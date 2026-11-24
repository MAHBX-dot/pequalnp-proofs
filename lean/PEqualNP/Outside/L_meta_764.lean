import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.ExactMaj3

namespace PEqualNP.Outside.L_meta_764

lemma maj3_nonne : ∃ y y' : Fin 3 → Bool, maj3 y ≠ maj3 y' := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  simp [maj3]

lemma F_eq :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
      = (fun x : Fin 5 → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || maj3 (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  simp [maj3, Bool.or_assoc]

end PEqualNP.Outside.L_meta_764

open PEqualNP.Outside.L_meta_764 in
theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  have hstep : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) (t + 2) ↔ 4 ≤ t := by
    intro t
    have h1 : HasCircuitSize 5 (fun x : Fin 5 → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || maj3 (fun j : Fin 3 => x (Fin.natAdd 2 j))) (t + 2) ↔
        HasCircuitSize 3 maj3 t := by
      simpa using (PEqualNP.MetaComplexity.L153 3 t maj3 maj3_nonne)
    have h2 : HasCircuitSize 3 maj3 t ↔ 4 ≤ t := PEqualNP.MetaComplexity.L100 t
    have h3 : HasCircuitSize 5 (fun x : Fin 5 → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || maj3 (fun j : Fin 3 => x (Fin.natAdd 2 j))) (t + 2) ↔ 4 ≤ t :=
      h1.trans h2
    rw [← F_eq] at h3
    exact h3
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hfalse : ¬ HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s := by
      intro h
      have h2 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) (0 + 2) :=
        hasCircuitSize_mono (by omega) h
      exact absurd ((hstep 0).mp h2) (by omega)
    constructor
    · intro h
      exact absurd h hfalse
    · intro h6
      omega
  · have hs2 : s = (s - 2) + 2 := by omega
    rw [hs2]
    have h4 : (4 ≤ s - 2) ↔ (6 ≤ (s - 2) + 2) := by
      constructor
      · intro h
        omega
      · intro h
        omega
    exact (hstep (s - 2)).trans h4
