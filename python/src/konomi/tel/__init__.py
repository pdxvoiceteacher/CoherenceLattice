from .tel_graph import TelGraph, TelNode, TelEdge, MemoryBand

 param($m) 
        $inner = $m.Groups[1].Value
        if ($inner -match "TelRecorder") { $m.Value } else { "__all__ = [" + $inner.Trim() + ', "TelRecorder"]' }
      
from .recorder import TelRecorder
