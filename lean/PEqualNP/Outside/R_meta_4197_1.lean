import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4197_1
    (h1 : ∀ (n : ℕ) (R : Fin n → Fin n → Prop) (_K : (Fin n → Bool) → Fin n → Bool),
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ (124 : ℕ) ∧
        (∀ (x4 x5 : Fin n), R x4 x5 →
          C.eval (List.ofFn fun (x7 : Fin (n + n)) =>
            Fin.addCases (fun (x8 : Fin n) => Decidable.decide (x8 = x4))
              (fun (x8 : Fin n) => Decidable.decide (x8 = x5)) x7) = Bool.true))
    (h2 : ∀ (n : ℕ) (R : Fin n → Fin n → Prop) (K : (Fin n → Bool) → Fin n → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ (124 : ℕ) →
        (∀ (x4 x5 : Fin n), R x4 x5 →
          C.eval (List.ofFn fun (x7 : Fin (n + n)) =>
            Fin.addCases (fun (x8 : Fin n) => Decidable.decide (x8 = x4))
              (fun (x8 : Fin n) => Decidable.decide (x8 = x5)) x7) = Bool.true) →
        ∀ (x4 : Fin n → Bool),
          (∀ (x5 : Fin n), x4 x5 = Bool.false → ∃ (x7 : Fin n), R x5 x7 ∧ K x4 x7 = Bool.true) →
            C.eval (List.ofFn fun (x6 : Fin (n + n)) => Fin.addCases x4 (K x4) x6) = Bool.false) :
    have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (124 : ℕ) ∧ (∀ (x4 x5 : Fin (21 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ ∀ (x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (21 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false := by
  obtain ⟨C, hC⟩ := h1 (21 : ℕ)
    (fun (a b : Fin (21 : ℕ)) => a = b ∨ a = b + (1 : Fin (21 : ℕ)) ∨ a = b + (4 : Fin (21 : ℕ)) ∨ a = b + (14 : Fin (21 : ℕ)) ∨ a = b + (16 : Fin (21 : ℕ)))
    (fun (a : Fin (21 : ℕ) → Bool) (b : Fin (21 : ℕ)) => !(a b || a (b + (1 : Fin (21 : ℕ))) || a (b + (4 : Fin (21 : ℕ))) || a (b + (14 : Fin (21 : ℕ))) || a (b + (16 : Fin (21 : ℕ)))))
  refine ⟨C, hC.1, hC.2.1, hC.2.2, ?_⟩
  exact h2 (21 : ℕ)
    (fun (a b : Fin (21 : ℕ)) => a = b ∨ a = b + (1 : Fin (21 : ℕ)) ∨ a = b + (4 : Fin (21 : ℕ)) ∨ a = b + (14 : Fin (21 : ℕ)) ∨ a = b + (16 : Fin (21 : ℕ)))
    (fun (a : Fin (21 : ℕ) → Bool) (b : Fin (21 : ℕ)) => !(a b || a (b + (1 : Fin (21 : ℕ))) || a (b + (4 : Fin (21 : ℕ))) || a (b + (14 : Fin (21 : ℕ))) || a (b + (16 : Fin (21 : ℕ)))))
    C hC.1 hC.2.1 hC.2.2
