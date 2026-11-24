import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328_aux

/-- `v` is the AND or the OR of two members of `s`. -/
def opDer (s : List ℕ) (v : ℕ) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, v = a &&& b ∨ v = a ||| b

/-- Every element of `t` is derived from `s` plus the elements listed before it. -/
def wireDer (s : List ℕ) (t : List ℕ) : Prop :=
  ∀ i : Fin t.length, opDer (s ++ t.take (i : ℕ)) (t.get i)

/-- Append `e` to `acc` unless the value is already present in `s` or in `acc`. -/
def push (s acc : List ℕ) (e : ℕ) : List ℕ :=
  if e ∈ s ∨ e ∈ acc then acc else acc ++ [e]

lemma push_of_mem (s acc : List ℕ) (e : ℕ) (hc : e ∈ s ∨ e ∈ acc) : push s acc e = acc := by
  unfold push
  rw [if_pos hc]

lemma push_of_notmem (s acc : List ℕ) (e : ℕ) (hc : ¬(e ∈ s ∨ e ∈ acc)) :
    push s acc e = acc ++ [e] := by
  unfold push
  rw [if_neg hc]

/-- Keep only values not already available, never repeating a value, order preserved. -/
def prune (s : List ℕ) : List ℕ → List ℕ → List ℕ
  | acc, [] => acc
  | acc, e :: rest => prune s (push s acc e) rest

lemma prune_self_subset (s : List ℕ) :
    ∀ (acc t : List ℕ), ∀ y ∈ acc, y ∈ prune s acc t := by
  intro acc t
  induction t generalizing acc with
  | nil => intro y hy; exact hy
  | cons z zs ih =>
    intro y hy
    apply ih
    by_cases hc : z ∈ s ∨ z ∈ acc
    · rw [push_of_mem s acc z hc]; exact hy
    · rw [push_of_notmem s acc z hc]; exact List.mem_append_left _ hy

lemma mem_push_of_notin (s acc : List ℕ) (e : ℕ) (h : e ∉ s) : e ∈ push s acc e := by
  by_cases hc : e ∈ s ∨ e ∈ acc
  · rw [push_of_mem s acc e hc]
    rcases hc with h1 | h1
    · exact absurd h1 h
    · exact h1
  · rw [push_of_notmem s acc e hc]
    simp

lemma mem_prune (s : List ℕ) :
    ∀ (acc t : List ℕ) (e : ℕ), e ∈ t → e ∉ s → e ∈ prune s acc t := by
  intro acc t
  induction t generalizing acc with
  | nil => intro e he; exact absurd he (by simp)
  | cons z zs ih =>
    intro e he hs
    rcases List.mem_cons.mp he with hhead | htail
    · subst e
      exact prune_self_subset s (push s acc z) zs z (mem_push_of_notin s acc z hs)
    · exact ih (push s acc z) e htail hs

lemma notin_prune (s : List ℕ) :
    ∀ (acc t : List ℕ), (∀ y ∈ acc, y ∉ s) → ∀ y ∈ prune s acc t, y ∉ s := by
  intro acc t
  induction t generalizing acc with
  | nil => intro h1 y hy; exact h1 y hy
  | cons z zs ih =>
    intro h1 y hy
    have hacc : ∀ w ∈ push s acc z, w ∉ s := by
      intro w hw
      by_cases hc : z ∈ s ∨ z ∈ acc
      · rw [push_of_mem s acc z hc] at hw
        exact h1 w hw
      · rw [push_of_notmem s acc z hc] at hw
        rcases List.mem_append.mp hw with h2 | h2
        · exact h1 w h2
        · simp only [List.mem_singleton] at h2
          rw [h2]
          exact fun hzs => hc (Or.inl hzs)
    exact ih (push s acc z) hacc y hy

/-- Adding one fresh value at the end keeps the list duplicate free. -/
lemma nodup_snoc {e : ℕ} :
    ∀ (acc : List ℕ), acc.Nodup → e ∉ acc → (acc ++ [e]).Nodup := by
  intro acc
  induction acc with
  | nil => intro h he; simp
  | cons x xs ih =>
    intro h he
    have hx : x ∉ xs := (List.nodup_cons.mp h).1
    have hnd : xs.Nodup := (List.nodup_cons.mp h).2
    have hxs : e ∉ xs := fun hm => he (List.mem_cons.mpr (Or.inr hm))
    have hxe : x ≠ e := by
      intro h1
      exact he (by rw [← h1]; exact List.mem_cons.mpr (Or.inl rfl))
    have hmem : x ∉ xs ++ [e] := by
      intro h1
      rcases List.mem_append.mp h1 with h2 | h2
      · exact hx h2
      · simp only [List.mem_singleton] at h2
        exact hxe h2
    exact List.nodup_cons.mpr ⟨hmem, ih hnd hxs⟩

/-- Pruning never introduces a repetition. -/
lemma nodup_prune (s : List ℕ) :
    ∀ (acc t : List ℕ), acc.Nodup → (prune s acc t).Nodup := by
  intro acc t
  induction t generalizing acc with
  | nil => intro h; exact h
  | cons z zs ih =>
    intro h
    apply ih
    by_cases hc : z ∈ s ∨ z ∈ acc
    · rw [push_of_mem s acc z hc]; exact h
    · rw [push_of_notmem s acc z hc]
      exact nodup_snoc acc h (fun hm => hc (Or.inr hm))

/-- `v` is derivable from a longer list of available values. -/
lemma opDer_mono {s s' : List ℕ} {v : ℕ} (h : opDer s v) (hsub : ∀ y ∈ s, y ∈ s') :
    opDer s' v := by
  obtain ⟨a, ha, b, hb, hv⟩ := h
  exact ⟨a, hsub a ha, b, hsub b hb, hv⟩

lemma wireDer_mono {s s' t : List ℕ} (h : wireDer s t) (hsub : ∀ y ∈ s, y ∈ s') :
    wireDer s' t := by
  intro i
  exact opDer_mono (h i) (by
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact List.mem_append_left _ (hsub y h1)
    · exact List.mem_append_right _ h1)

lemma wireDer_nil (s : List ℕ) : wireDer s [] := by
  intro i
  exact i.elim0

/-- A derivation whose head is already available is still a derivation of the tail. -/
lemma wireDer_cons_of_mem {X : List ℕ} {e : ℕ} {rest : List ℕ} (h : wireDer X (e :: rest))
    (he : e ∈ X) : wireDer X rest := by
  intro i
  have hh := h i.succ
  have htake : (e :: rest).take (i.succ : ℕ) = e :: rest.take (i : ℕ) := by simp
  have hget : (e :: rest).get i.succ = rest.get i := by simp
  rw [htake, hget] at hh
  obtain ⟨p, hp, q, hq, hv⟩ := hh
  have hmem : ∀ y ∈ X ++ e :: rest.take (i : ℕ), y ∈ X ∨ y ∈ rest.take (i : ℕ) := by
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    rcases hy with h1 | h2 | h2
    · exact Or.inl h1
    · exact Or.inl (h2 ▸ he)
    · exact Or.inr h2
  refine ⟨p, ?_, q, ?_, hv⟩
  · rcases hmem p hp with h1 | h1
    · exact List.mem_append.mpr (Or.inl h1)
    · exact List.mem_append.mpr (Or.inr h1)
  · rcases hmem q hq with h1 | h1
    · exact List.mem_append.mpr (Or.inl h1)
    · exact List.mem_append.mpr (Or.inr h1)

/-- Prepending a derivable value to a derivation gives a derivation. -/
lemma wireDer_cons {s : List ℕ} {a : ℕ} {t : List ℕ} (ha : opDer s a)
    (ht : wireDer (a :: s) t) : wireDer s (a :: t) := by
  intro i
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · have htake : (a :: t).take (i : ℕ) = [] := by rw [h0]; simp
    have hget : (a :: t).get i = a := by
      have hii : i = ⟨0, by simp⟩ := Fin.ext h0
      rw [hii]
      simp
    rw [htake, hget]
    simpa using ha
  · have hlt : (i : ℕ) < t.length + 1 := by
      have h := i.isLt
      simpa using h
    have hidx : (i : ℕ) - 1 < t.length := by omega
    obtain ⟨j, hj⟩ : ∃ j : Fin t.length, (i : ℕ) = (j : ℕ) + 1 := by
      refine ⟨⟨(i : ℕ) - 1, hidx⟩, ?_⟩
      simp only [Fin.val_mk]
      omega
    have htake : (a :: t).take (i : ℕ) = a :: t.take (j : ℕ) := by rw [hj]; simp
    have hget : (a :: t).get i = t.get j := by
      have hii : i = j.succ := Fin.ext hj
      rw [hii]
      simp
    rw [htake, hget]
    exact opDer_mono (ht j) (by
      intro y hy
      rcases List.mem_append.mp hy with h1 | h1
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        · exact List.mem_append.mpr (Or.inl h2)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1))))

lemma wireDer_snoc {s acc : List ℕ} {e : ℕ} (h : wireDer s acc) (he : opDer (s ++ acc) e) :
    wireDer s (acc ++ [e]) := by
  intro i
  by_cases hi : (i : ℕ) < acc.length
  · have h1 := h ⟨i, hi⟩
    have htake : (acc ++ [e]).take (i : ℕ) = acc.take (i : ℕ) := by
      rw [List.take_append]
      simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt hi)]
    have hget : (acc ++ [e]).get i = acc.get ⟨i, hi⟩ := by
      simp [List.getElem_append_left hi]
    rw [htake, hget]
    exact h1
  · have hlen : (i : ℕ) = acc.length := by
      have : (i : ℕ) < (acc ++ [e]).length := i.isLt
      simp at this
      omega
    have htake : (acc ++ [e]).take (i : ℕ) = acc := by
      rw [hlen, List.take_append]
      simp
    have hget : (acc ++ [e]).get i = e := by
      have hii : i = ⟨acc.length, by simp⟩ := Fin.ext hlen
      rw [hii]
      simp
    rw [htake, hget]
    exact he

lemma push_len (s acc : List ℕ) (e : ℕ) : (push s acc e).length ≤ acc.length + 1 := by
  by_cases hc : e ∈ s ∨ e ∈ acc
  · rw [push_of_mem s acc e hc]; simp
  · rw [push_of_notmem s acc e hc]; simp

lemma prune_len (s : List ℕ) :
    ∀ (acc u : List ℕ), (prune s acc u).length ≤ acc.length + u.length := by
  intro acc u
  induction u generalizing acc with
  | nil =>
    show (prune s acc []).length ≤ acc.length + [].length
    simp only [prune, List.length_nil, Nat.add_zero]
    exact Nat.le_refl _
  | cons z zs ih =>
    have h1 := ih (push s acc z)
    have h2 := push_len s acc z
    show (prune s (push s acc z) zs).length ≤ acc.length + (z :: zs).length
    simp only [List.length_cons]
    omega

/-- Pruning keeps derivability: the surviving values are derived from `s` alone. -/
lemma wireDer_prune (s : List ℕ) :
    ∀ (acc u : List ℕ), wireDer s acc → wireDer (s ++ acc) u → wireDer s (prune s acc u) := by
  intro acc u
  induction u generalizing acc with
  | nil => intro h1 h2; exact h1
  | cons z zs ih =>
    intro h1 h2
    by_cases hc : z ∈ s ∨ z ∈ acc
    · rw [show prune s acc (z :: zs) = prune s acc zs from by
        simp only [prune]
        rw [push_of_mem s acc z hc]]
      have hz : z ∈ s ++ acc := by
        rcases hc with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr h)
      exact ih acc h1 (wireDer_cons_of_mem h2 hz)
    · rw [show prune s acc (z :: zs) = prune s (acc ++ [z]) zs from by
        simp only [prune]
        rw [push_of_notmem s acc z hc]]
      have h0 : opDer (s ++ acc) z := by
        have h := h2 ⟨0, by simp⟩
        simpa using h
      have hacc' : wireDer s (acc ++ [z]) := wireDer_snoc h1 h0
      have h2' : wireDer (s ++ (acc ++ [z])) (z :: zs) := by
        have h3 : wireDer ((s ++ acc) ++ [z]) (z :: zs) :=
          wireDer_mono h2 (by
            intro y hy
            exact List.mem_append.mpr (Or.inl hy))
        rwa [List.append_assoc] at h3
      exact ih (acc ++ [z]) hacc' (wireDer_cons_of_mem h2' (by simp))

/-- The pruning lemma of the step, in unrolled form. -/
lemma main (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ) (h5 : x5 ∉ x3)
    (h4 : opDer x3 x4) (h6 : wireDer (x4 :: x3) x6) (h7 : opDer (x4 :: x3 ++ x6) x5) :
    ∃ x11 : List ℕ, x11.length ≤ x6.length + 2 ∧ x11.Nodup ∧ (∀ y ∈ x11, y ∉ x3) ∧
      x5 ∈ x11 ∧ wireDer x3 x11 := by
  have h7' : opDer ((x4 :: x3) ++ x6) x5 := by
    simpa [List.cons_append] using h7
  have hx6 : wireDer (x4 :: x3) (x6 ++ [x5]) := wireDer_snoc h6 h7'
  have hu : wireDer x3 (x4 :: (x6 ++ [x5])) := wireDer_cons h4 hx6
  refine ⟨prune x3 [] (x4 :: (x6 ++ [x5])), ?_, ?_, ?_, ?_, ?_⟩
  · have hlen : (x4 :: (x6 ++ [x5])).length = x6.length + 2 := by simp
    have h := prune_len x3 [] (x4 :: (x6 ++ [x5]))
    simp only [List.length_nil] at h
    omega
  · exact nodup_prune x3 [] _ (by simp)
  · intro y hy
    exact notin_prune x3 [] (x4 :: (x6 ++ [x5])) (by simp) y hy
  · exact mem_prune x3 [] (x4 :: (x6 ++ [x5])) x5 (by simp) h5
  · have hu' : wireDer (x3 ++ []) (x4 :: (x6 ++ [x5])) := by simpa using hu
    exact wireDer_prune x3 [] _ (wireDer_nil x3) hu'

end PEqualNP.Outside.L_meta_3328_aux

namespace PEqualNP.Outside

set_option maxHeartbeats 1000000

theorem L_meta_3328 :
  have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro _ _ x3 x4 x5 x6 h5 h4 h6 h7
  exact L_meta_3328_aux.main x3 x4 x5 x6 h5 h4 h6 h7

end PEqualNP.Outside
