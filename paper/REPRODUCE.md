
Reproducibility / Peer Review Checklist
1) Build the project
From the repo root:

powershell
Copy code
lake exe cache get
lake build
Expected result: Build completed successfully (...) jobs.

2) Verify the paper-facing theorem names exist
Create a temporary check file (do not commit it):

powershell
Copy code
$s = @"
import CoherenceLattice

#check Coherence.PaperGloss.Lemma_DrivePositive
#check Coherence.PaperGloss.Lemma_BoundedDrift_stepET
#check Coherence.PaperGloss.Lemma_PsiNondecreasing_stepET
#check Coherence.PaperGloss.Theorem_NoTeleport
#check Coherence.PaperGloss.Theorem_DeltaSynPsiStep_Safe
#check Coherence.PaperGloss.Theorem_DeltaSynETStep_Safe
#check Coherence.PaperGloss.Corollary_TrajectoryET_ValidPath
"@

[System.IO.File]::WriteAllText((Join-Path $PWD "ReviewChecks.lean"), $s, [System.Text.UTF8Encoding]::new($false))
lake env lean .\ReviewChecks.lean
If Lean prints each #check signature with no errors, the theorem names are present.

3) Read the claim map
See: paper/theorem-map.md
