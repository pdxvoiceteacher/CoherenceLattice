import CoherenceLattice.Coherence.Dynamics

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.unusedSimpArgs false
noncomputable section

/-- Build a state trajectory of length n+1 by iterating a step function. -/
def traj (f : State → State) : Nat → State → List State
  | 0, s => [s]
  | Nat.succ n, s => s :: traj f n (f s)

/-- If each step is a validTransition, the whole trajectory is a valid state-path. -/
theorem statePathValid_traj {f : State → State}
    (hf : ∀ s, validTransition s (f s)) :
    ∀ n s, statePathValid (traj f n s) := by
  intro n s
  induction n generalizing s with
  | zero =>
      simp [traj, statePathValid]
  | succ n ih =>
      cases n with
      | zero =>
          -- traj f 1 s = [s, f s]
          simp [traj, statePathValid, hf]
      | succ n' =>
          -- traj f (n'+2) s = s :: traj f (n'+1) (f s)
          have ht : statePathValid (traj f (Nat.succ n') (f s)) := ih (s := f s)
          have hpair :
              validTransition s (f s) ∧ statePathValid (traj f (Nat.succ n') (f s)) :=
            ⟨hf s, ht⟩
          simpa [traj, statePathValid] using hpair

/-- Therefore the induced regime path is valid in the regime graph. -/
theorem validPath_regimePath_traj {f : State → State}
    (hf : ∀ s, validTransition s (f s)) :
    ∀ n s, Coherence.validPath (regimePath (traj f n s)) := by
  intro n s
  exact validPath_of_statePathValid (traj f n s) (statePathValid_traj (f := f) hf n s)

-- ===== Specialization: ΔSyn ψ-step =====

def trajPsi (η : ℝ) (p : Coherence.DeltaSynInput) : Nat → State → List State :=
  traj (stepPsi η p)

theorem validPath_trajPsi (η : ℝ) (p : Coherence.DeltaSynInput) :
    ∀ n s, Coherence.validPath (regimePath (trajPsi η p n s)) := by
  intro n s
  apply validPath_regimePath_traj (f := stepPsi η p)
  intro s0
  simpa using validTransition_stepPsi η p s0

end  -- noncomputable section

end Lattice
end Coherence
