import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_765

/-- The edge function of the 4-cycle on four inputs. -/
def g : (Fin 4 → Bool) → Bool :=
  fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)

lemma g_nonne : ∃ y y' : Fin 4 → Bool, g y ≠ g y' := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  simp [g]

lemma F_eq :
    (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
      = (fun x : Fin 6 → Bool =>
          (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
            g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  funext x
  simp [g, Bool.or_assoc]

lemma size_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, hFan, hsize, heval⟩ := h
  exact ⟨C, hFan, le_trans hsize hst, heval⟩

end PEqualNP.Outside.L_meta_765

open PEqualNP.Outside.L_meta_765 in
theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ,
      HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔
        5 ≤ s := by
  intro s
  have hstep :
      ∀ t : ℕ,
        HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) (t + 2) ↔
          3 ≤ t := by
    intro t
    have h1 :
        HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
              g (fun j : Fin 4 => x (Fin.natAdd 2 j))) (t + 2) ↔
          HasCircuitSize 4 g t := by
      simpa using (PEqualNP.MetaComplexity.L153 4 t g g_nonne)
    have h2 : HasCircuitSize 4 g t ↔ 3 ≤ t := PEqualNP.MetaComplexity.L112 t
    have h3 :
        HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
              g (fun j : Fin 4 => x (Fin.natAdd 2 j))) (t + 2) ↔
          3 ≤ t :=
      h1.trans h2
    rw [← F_eq] at h3
    exact h3
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hfalse :
        ¬ HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s := by
      intro h
      have h2 :
          HasCircuitSize 6
            (fun x : Fin 6 → Bool =>
              (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) (0 + 2) :=
        size_mono (by omega) h
      exact absurd ((hstep 0).mp h2) (by omega)
    constructor
    · intro h
      exact absurd h hfalse
    · intro h5
      omega
  · have hs2 : s = (s - 2) + 2 := by omega
    rw [hs2]
    have h4 : (3 ≤ s - 2) ↔ (5 ≤ (s - 2) + 2) := by omega
    exact (hstep (s - 2)).trans h4
