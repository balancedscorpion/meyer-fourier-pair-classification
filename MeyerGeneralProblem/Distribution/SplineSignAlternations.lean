module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Sign alternations along a spline

Alternations are witnessed by ordered points with opposite nonzero signs.
A finite set of knots can be removed when choosing the derivative samples
in Rolle's argument. The final piecewise constant derivative charges a
different knot for every remaining alternation.
-/

namespace MeyerGeneralProblem

open Set

/-- A sequence of `n + 1` ordered samples witnessing `n` sign changes. -/
def HasSignAlternations (f : ℝ → ℝ) (U : Set ℝ) (n : ℕ) : Prop :=
  ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ U) ∧
    ∀ i : Fin n, f (x i.castSucc) * f (x i.succ) < 0

/-- If a continuous function increases in the direction of `c`, some
interior derivative has the same sign after discarding a finite set. -/
theorem exists_signed_derivative_off_finite (f g : ℝ → ℝ) (s : Finset ℝ)
    {a b c : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (g x) x)
    (hInc : 0 < (f b - f a) * c) :
    ∃ x ∈ Ioo a b, x ∉ s ∧ 0 < g x * c := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f g hab hf
      (fun x hx => hg x hx (Finset.notMem_empty x))
    refine ⟨x, hx, Finset.notMem_empty x, ?_⟩
    rw [he, div_mul_eq_mul_div]
    exact div_pos hInc (sub_pos.mpr hab)
  | insert z s hzs ih =>
    have hInsert {x : ℝ} (hx : x ≠ z) (hs : x ∉ s) : x ∉ insert z s :=
      fun hm => (Finset.mem_insert.mp hm).elim hx hs
    by_cases hz : z ∈ Ioo a b
    · have hSplit : (f z - f a) * c + (f b - f z) * c = (f b - f a) * c := by ring
      rcases lt_or_ge 0 ((f z - f a) * c) with hLeft | hLeft
      · have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc le_rfl hz.2.le
        have hDeriv : ∀ x ∈ Ioo a z, x ∉ s → HasDerivAt f (g x) x := by
          intro x hx hs
          exact hg x ⟨hx.1, hx.2.trans hz.2⟩ (hInsert hx.2.ne hs)
        obtain ⟨x, hx, hs, hg⟩ := ih hz.1 (hf.mono hsub) hDeriv hLeft
        exact ⟨x, ⟨hx.1, hx.2.trans hz.2⟩, hInsert hx.2.ne hs, hg⟩
      · have hRight : 0 < (f b - f z) * c := by linarith
        have hsub : Icc z b ⊆ Icc a b := Icc_subset_Icc hz.1.le le_rfl
        have hDeriv : ∀ x ∈ Ioo z b, x ∉ s → HasDerivAt f (g x) x := by
          intro x hx hs
          exact hg x ⟨hz.1.trans hx.1, hx.2⟩ (hInsert hx.1.ne' hs)
        obtain ⟨x, hx, hs, hg⟩ := ih hz.2 (hf.mono hsub) hDeriv hRight
        exact ⟨x, ⟨hz.1.trans hx.1, hx.2⟩, hInsert hx.1.ne' hs, hg⟩
    · have hne (x : ℝ) (hx : x ∈ Ioo a b) : x ≠ z := fun e => hz (e ▸ hx)
      obtain ⟨x, hx, hs, hp⟩ := ih hab hf
        (fun x hx hs => hg x hx (hInsert (hne x hx) hs)) hInc
      exact ⟨x, hx, hInsert (hne x hx) hs, hp⟩

/-- Restriction to a larger set preserves a witnessed alternation count. -/
theorem HasSignAlternations.mono {f : ℝ → ℝ} {U V : Set ℝ} {n : ℕ}
    (h : HasSignAlternations f U n) (hUV : U ⊆ V) : HasSignAlternations f V n := by
  obtain ⟨x, hx, hmem, halt⟩ := h
  exact ⟨x, hx, fun i => hUV (hmem i), halt⟩

/-- Repeated Rolle counting loses at most one sign change in one
derivative step. All new sampling points avoid the finite knot set. -/
theorem HasSignAlternations.derivative_off_knots {f g : ℝ → ℝ} {s : Finset ℝ}
    {a b : ℝ} {n : ℕ} (h : HasSignAlternations f (Icc a b) (n + 1))
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (g x) x) :
    HasSignAlternations g (Icc a b \ (s : Set ℝ)) n := by
  obtain ⟨x, hx, hmem, halt⟩ := h
  have hW (i : Fin (n + 1)) : ∃ t ∈ Ioo (x i.castSucc) (x i.succ),
      t ∉ s ∧ 0 < g t * f (x i.succ) := by
    have hi : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
    have hsub : Icc (x i.castSucc) (x i.succ) ⊆ Icc a b :=
      Icc_subset_Icc (hmem i.castSucc).1 (hmem i.succ).2
    apply exists_signed_derivative_off_finite f g s hi (hcont.mono hsub)
    · intro t ht hts
      exact hderiv t ⟨(hmem i.castSucc).1.trans_lt ht.1, ht.2.trans_le (hmem i.succ).2⟩ hts
    · rw [sub_mul]
      exact sub_pos.mpr ((halt i).trans_le (mul_self_nonneg _))
  choose t ht hts hSign using hW
  have hMid (i : Fin n) : x i.castSucc.succ = x i.succ.castSucc := congrArg x (Fin.ext rfl)
  refine ⟨t, Fin.strictMono_iff_lt_succ.mpr (fun i => (ht i.castSucc).2.trans
    ((hMid i).trans_lt (ht i.succ).1)), ?_, ?_⟩
  · intro i
    exact ⟨⟨(hmem i.castSucc).1.trans (ht i).1.le, (ht i).2.le.trans (hmem i.succ).2⟩, hts i⟩
  · intro i
    have hOpp : f (x i.castSucc.succ) * f (x i.succ.succ) < 0 := by
      rw [hMid]
      exact halt i.succ
    have hPos := mul_pos (hSign i.castSucc) (hSign i.succ)
    rw [mul_mul_mul_comm] at hPos
    exact (mul_pos_iff.mp hPos).resolve_left (fun ha => hOpp.not_gt ha.2) |>.1

/-- A change in a function constant between the knots must cross a knot.
Disjoint consecutive sample intervals therefore use distinct knots. -/
theorem HasSignAlternations.le_card_knots_of_piecewise_constant {g : ℝ → ℝ} {s : Finset ℝ}
    {a b : ℝ} {n : ℕ} (h : HasSignAlternations g (Icc a b \ (s : Set ℝ)) n)
    (hConst : ∀ u v : ℝ, u ∈ Icc a b \ (s : Set ℝ) → v ∈ Icc a b \ (s : Set ℝ) → u < v →
        (∀ k ∈ s, k ∉ Ioo u v) → g u = g v) : n ≤ s.card := by
  classical
  obtain ⟨x, hx, hmem, halt⟩ := h
  have hK (i : Fin n) : ∃ k ∈ s, k ∈ Ioo (x i.castSucc) (x i.succ) := by
    by_contra! hNo
    have he := hConst _ _ (hmem i.castSucc) (hmem i.succ) (hx Fin.castSucc_lt_succ) hNo
    exact (not_lt_of_ge (mul_self_nonneg _)) (he ▸ halt i)
  choose k hk hkt using hK
  have hkMono : StrictMono k := by
    intro i j hij
    have hIdx : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact (hkt i).2.trans_le (hx.monotone hIdx) |>.trans (hkt j).1
  have hc := Fintype.card_le_of_injective (fun i : Fin n => (⟨k i, hk i⟩ : s))
    (fun i j he => hkMono.injective (congrArg Subtype.val he))
  simpa using hc

private theorem le_card_add_order_of_off_knots_derivative_chain
    (s : Finset ℝ) {a b : ℝ} (m : ℕ) (f : ℕ → ℝ → ℝ) {n : ℕ}
    (hcont : ∀ k < m, ContinuousOn (f k) (Icc a b))
    (hderiv : ∀ k < m, ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt (f k) (f (k + 1) x) x)
    (hConst : ∀ u v : ℝ, u ∈ Icc a b \ (s : Set ℝ) → v ∈ Icc a b \ (s : Set ℝ) → u < v →
      (∀ k ∈ s, k ∉ Ioo u v) → f m u = f m v)
    (h : HasSignAlternations (f 0) (Icc a b \ (s : Set ℝ)) n) : n ≤ s.card + m := by
  induction m generalizing f n with
  | zero => simpa only [Nat.add_zero] using h.le_card_knots_of_piecewise_constant hConst
  | succ m ih =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      have h' := (h.mono sdiff_subset).derivative_off_knots (hcont 0 (Nat.succ_pos m))
        (hderiv 0 (Nat.succ_pos m))
      have hn : n ≤ s.card + m := ih (fun k => f (k + 1))
        (fun k hk => hcont (k + 1) (Nat.succ_lt_succ hk))
        (fun k hk => hderiv (k + 1) (Nat.succ_lt_succ hk)) hConst h'
      omega

/-- A continuous spline whose derivative chain has length `m + 1` and
ends in a function constant between its knots has at most `s.card + m + 1`
sign changes. The original samples may include endpoints and knots. -/
theorem spline_sign_alternations_le_card_knots_add_order
    (s : Finset ℝ) {a b : ℝ} (m : ℕ) (f : ℕ → ℝ → ℝ) {n : ℕ}
    (hcont : ∀ k ≤ m, ContinuousOn (f k) (Icc a b))
    (hderiv : ∀ k ≤ m, ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt (f k) (f (k + 1) x) x)
    (hConst : ∀ u v : ℝ, u ∈ Icc a b \ (s : Set ℝ) → v ∈ Icc a b \ (s : Set ℝ) → u < v →
      (∀ k ∈ s, k ∉ Ioo u v) → f (m + 1) u = f (m + 1) v)
    (h : HasSignAlternations (f 0) (Icc a b) n) : n ≤ s.card + m + 1 := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have h' := h.derivative_off_knots (hcont 0 (Nat.zero_le _)) (hderiv 0 (Nat.zero_le _))
    have hn : n ≤ s.card + m := le_card_add_order_of_off_knots_derivative_chain s m (fun k => f (k + 1))
      (fun k hk => hcont (k + 1) (Nat.succ_le_of_lt hk))
      (fun k hk => hderiv (k + 1) (Nat.succ_le_of_lt hk)) hConst h'
    omega

end MeyerGeneralProblem
