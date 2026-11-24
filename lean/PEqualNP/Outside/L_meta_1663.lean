import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

lemma mem_unique {N : ℕ} {L : Fin N → Finset (Fin N)}
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    {i j : Fin N} (hij : i ≠ j) {a b : Fin N}
    (hai : a ∈ L i) (haj : a ∈ L j) (hbi : b ∈ L i) (hbj : b ∈ L j) : a = b := by
  have h1 : (L i ∩ L j).card = 1 := hinter i j hij
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
  have ha : a ∈ ({c} : Finset (Fin N)) := hc ▸ (Finset.mem_inter.mpr ⟨hai, haj⟩)
  have hb : b ∈ ({c} : Finset (Fin N)) := hc ▸ (Finset.mem_inter.mpr ⟨hbi, hbj⟩)
  rw [Finset.mem_singleton] at ha hb
  exact ha.trans hb.symm

end PEqualNP.Outside.L_meta_1663

open PEqualNP.Outside.L_meta_1663 in
theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N), 3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) → (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) → s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp → ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S → (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W, ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧ (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv, ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp hq hN hline hinter hnocol hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvs : v ≠ s := by
    rintro h
    exact hnocol Mv ⟨h ▸ hsMv, hsMv, hpMv⟩
  have hvp : v ≠ p := by
    rintro h
    exact hnocol Mp ⟨hvMp, hsMp, h ▸ hvMp⟩
  have hsp : s ≠ p := by
    rintro h
    exact hnocol Ms ⟨hvMs, h ▸ hpMs, hpMs⟩
  have hMsMv : Ms ≠ Mv := by
    rintro h
    exact hnocol Mv ⟨h ▸ hvMs, hsMv, hpMv⟩
  have hMpMv : Mp ≠ Mv := by
    rintro h
    exact hnocol Mv ⟨h ▸ hvMp, hsMv, hpMv⟩
  constructor
  · intro w W hwW P hPW hcon
    rcases hcon with ⟨hAB, hCD⟩
    rcases hwW with ⟨hws, hWM⟩ | ⟨hws, hWM⟩
    · have hPWM : P ∈ L Ms := hWM ▸ hPW
      have hAP : P ∈ L S := by
        rcases hAB with h | h
        · exact h
        · exact absurd (hws ▸ h.2.2.2) hsS
      rcases hCD with hC | hD
      · have hPp : P = p := mem_unique hinter hMsMv hPWM hC hpMs hpMv
        exact hpS (hPp ▸ hAP)
      · obtain ⟨hPv, -, -, -⟩ := hD
        have hSW : S = Ms := by
          by_contra hne
          exact hPv (mem_unique hinter hne hAP hPWM hvS hvMs)
        exact hpS (hSW ▸ hpMs)
    · have hPWM : P ∈ L Mp := hWM ▸ hPW
      have hAP : P ∈ L S := by
        rcases hAB with h | h
        · exact h
        · exact absurd (hws ▸ h.2.2.2) hpS
      rcases hCD with hC | hD
      · have hPs : P = s := mem_unique hinter hMpMv hPWM hC hsMp hsMv
        exact hsS (hPs ▸ hAP)
      · obtain ⟨hPv, -, -, -⟩ := hD
        have hSW : S = Mp := by
          by_contra hne
          exact hPv (mem_unique hinter hne hAP hPWM hvS hvMp)
        exact hsS (hSW ▸ hsMp)
  · intro w S1 hw hwS1 hS1only P hP hcon
    rcases hcon with ⟨hAB, hCD⟩
    have hD : ¬ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1) := by
      rintro ⟨-, -, -, hv1⟩
      have hvw : v = w := hS1only v (Or.inl rfl) hv1
      rcases hw with hws | hwp
      · exact hvs (hws ▸ hvw)
      · exact hvp (hwp ▸ hvw)
    have hC1 : P ∈ L S1 := by
      rcases hCD with h | h
      · exact h
      · exact absurd h hD
    rcases hw with hws | hwp
    · by_cases hPw : P = w
      · have hPs : P = s := hws ▸ hPw
        rcases hAB with h | h
        · exact hsS (hPs ▸ h)
        · exact absurd rfl (hPs ▸ h.2.1)
      · have hS1Mv : S1 = Mv := by
          by_contra hne
          exact hPw (mem_unique hinter hne hC1 hP hwS1 (hws ▸ hsMv))
        have hpS1 : p ∈ L S1 := hS1Mv ▸ hpMv
        have hps : p = s := hws ▸ (hS1only p (Or.inr (Or.inr rfl)) hpS1)
        exact hsp hps.symm
    · by_cases hPw : P = w
      · have hPp : P = p := hwp ▸ hPw
        rcases hAB with h | h
        · exact hpS (hPp ▸ h)
        · exact absurd rfl (hPp ▸ h.2.2.1)
      · have hS1Mv : S1 = Mv := by
          by_contra hne
          exact hPw (mem_unique hinter hne hC1 hP hwS1 (hwp ▸ hpMv))
        have hs1 : s ∈ L S1 := hS1Mv ▸ hsMv
        have hps : s = p := hwp ▸ (hS1only s (Or.inr (Or.inl rfl)) hs1)
        exact hsp hps
