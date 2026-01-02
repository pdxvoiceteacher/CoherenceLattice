from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterator, Tuple, Optional, Callable, List

import numpy as np


@dataclass
class BlockArray:
    """
    Sparse chunked 3D array for a large logical grid (e.g., 1000^3).
    Storage: dict[(bx,by,bz)] -> dense block (chunk^3) allocated on write.

    Notes:
    - Edge blocks are stored at full chunk size; out-of-range indices are prevented by bounds checks.
    - scan_bbox iterates only allocated blocks intersecting the bbox (sparse-friendly).
    """
    shape: Tuple[int, int, int] = (1000, 1000, 1000)
    chunk: int = 16
    dtype: np.dtype = np.float32

    def __post_init__(self) -> None:
        sx, sy, sz = self.shape
        if sx <= 0 or sy <= 0 or sz <= 0:
            raise ValueError("shape must be positive")
        if self.chunk <= 0:
            raise ValueError("chunk must be positive")
        self.blocks: Dict[Tuple[int, int, int], np.ndarray] = {}

    def _check_bounds(self, x: int, y: int, z: int) -> None:
        sx, sy, sz = self.shape
        if not (0 <= x < sx and 0 <= y < sy and 0 <= z < sz):
            raise IndexError(f"index out of bounds: {(x,y,z)} for shape {self.shape}")

    def _block_key(self, x: int, y: int, z: int) -> Tuple[Tuple[int,int,int], Tuple[int,int,int]]:
        bx, by, bz = x // self.chunk, y // self.chunk, z // self.chunk
        lx, ly, lz = x % self.chunk, y % self.chunk, z % self.chunk
        return (bx, by, bz), (lx, ly, lz)

    def _ensure_block(self, bkey: Tuple[int,int,int]) -> np.ndarray:
        blk = self.blocks.get(bkey)
        if blk is None:
            blk = np.zeros((self.chunk, self.chunk, self.chunk), dtype=self.dtype)
            self.blocks[bkey] = blk
        return blk

    def get(self, x: int, y: int, z: int) -> float:
        self._check_bounds(x, y, z)
        bkey, (lx, ly, lz) = self._block_key(x, y, z)
        blk = self.blocks.get(bkey)
        if blk is None:
            return 0.0
        return float(blk[lx, ly, lz])

    def set(self, x: int, y: int, z: int, v: float) -> None:
        self._check_bounds(x, y, z)
        bkey, (lx, ly, lz) = self._block_key(x, y, z)
        blk = self._ensure_block(bkey)
        blk[lx, ly, lz] = v

    def set_many(self, coords: np.ndarray, values: np.ndarray) -> None:
        """
        Batch set. coords shape (N,3), values shape (N,).
        Groups by block key for speed.
        """
        coords = np.asarray(coords, dtype=np.int64)
        values = np.asarray(values, dtype=self.dtype)
        if coords.ndim != 2 or coords.shape[1] != 3:
            raise ValueError("coords must be (N,3)")
        if values.ndim != 1 or values.shape[0] != coords.shape[0]:
            raise ValueError("values must be (N,) matching coords")

        # bounds check (vectorized)
        sx, sy, sz = self.shape
        if np.any(coords[:,0] < 0) or np.any(coords[:,0] >= sx) or np.any(coords[:,1] < 0) or np.any(coords[:,1] >= sy) or np.any(coords[:,2] < 0) or np.any(coords[:,2] >= sz):
            raise IndexError("coords contain out-of-bounds indices")

        # compute block keys and locals
        bxyz = coords // self.chunk
        lxyz = coords % self.chunk

        # group by block key via structured view
        keys = bxyz[:,0] * 10_000_000 + bxyz[:,1] * 10_000 + bxyz[:,2]
        order = np.argsort(keys)
        keys_s = keys[order]
        b_s = bxyz[order]
        l_s = lxyz[order]
        v_s = values[order]

        start = 0
        n = coords.shape[0]
        while start < n:
            k = keys_s[start]
            end = start + 1
            while end < n and keys_s[end] == k:
                end += 1
            bx, by, bz = map(int, b_s[start])
            blk = self._ensure_block((bx, by, bz))
            lx = l_s[start:end, 0]
            ly = l_s[start:end, 1]
            lz = l_s[start:end, 2]
            blk[lx, ly, lz] = v_s[start:end]
            start = end

    def estimate_bytes(self) -> int:
        """Rough memory estimate for allocated blocks (payload only)."""
        return len(self.blocks) * (self.chunk ** 3) * np.dtype(self.dtype).itemsize

    def scan_bbox(
        self,
        x0: int, x1: int,
        y0: int, y1: int,
        z0: int, z1: int,
        *,
        max_blocks: int = 10_000,
        max_hits: int = 1_000_000,
        predicate: Optional[Callable[[float], bool]] = None,
    ) -> Tuple[int, int, List[Tuple[int,int,int,float]]]:
        """
        Scan allocated blocks intersecting bbox [x0,x1),[y0,y1),[z0,z1).
        Returns (visited_blocks, hits, list_of_hits).
        Bounded by max_blocks and max_hits.
        """
        sx, sy, sz = self.shape
        x0 = max(0, min(sx, x0)); x1 = max(0, min(sx, x1))
        y0 = max(0, min(sy, y0)); y1 = max(0, min(sy, y1))
        z0 = max(0, min(sz, z0)); z1 = max(0, min(sz, z1))
        if x0 >= x1 or y0 >= y1 or z0 >= z1:
            return (0, 0, [])

        bx0, bx1 = x0 // self.chunk, (x1 - 1) // self.chunk
        by0, by1 = y0 // self.chunk, (y1 - 1) // self.chunk
        bz0, bz1 = z0 // self.chunk, (z1 - 1) // self.chunk

        pred = predicate or (lambda v: v != 0.0)

        hits: List[Tuple[int,int,int,float]] = []
        visited = 0

        for (bx, by, bz), blk in self.blocks.items():
            if visited >= max_blocks:
                break
            if bx0 <= bx <= bx1 and by0 <= by <= by1 and bz0 <= bz <= bz1:
                visited += 1

                # local bounds within block
                gx0 = x0 - bx * self.chunk; gx1 = x1 - bx * self.chunk
                gy0 = y0 - by * self.chunk; gy1 = y1 - by * self.chunk
                gz0 = z0 - bz * self.chunk; gz1 = z1 - bz * self.chunk
                lx0 = max(0, gx0); lx1 = min(self.chunk, gx1)
                ly0 = max(0, gy0); ly1 = min(self.chunk, gy1)
                lz0 = max(0, gz0); lz1 = min(self.chunk, gz1)

                sub = blk[lx0:lx1, ly0:ly1, lz0:lz1]
                # iterate hits (sparse-friendly)
                it = np.nditer(sub, flags=["multi_index"])
                for v in it:
                    fv = float(v)
                    if pred(fv):
                        mi = it.multi_index
                        x = bx * self.chunk + (lx0 + mi[0])
                        y = by * self.chunk + (ly0 + mi[1])
                        z = bz * self.chunk + (lz0 + mi[2])
                        hits.append((x, y, z, fv))
                        if len(hits) >= max_hits:
                            return (visited, len(hits), hits)

        return (visited, len(hits), hits)