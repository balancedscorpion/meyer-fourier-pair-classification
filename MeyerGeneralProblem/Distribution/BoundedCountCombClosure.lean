module

public import MeyerGeneralProblem.Distribution.CenteredCountFiniteComb

@[expose] public section

/-! Finite comb form for both original records on two bounded-count carriers. -/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform

theorem UnitCellBound.centered_count_nat {A : LocallyFiniteCarrier} {K : ℕ}
    (h : UnitCellBound A K) (n : ℕ) :
    (A.carrier ∩ Icc (-(n : ℝ)) n).ncard ≤ (2 * n + 1) * K := by
  have hs : A.carrier ∩ Icc (-(n : ℝ)) n ⊆
      A.carrier ∩ Ico (-(n : ℝ)) (-(n : ℝ) + ((2 * n + 1 : ℕ) : ℝ)) := by
    rintro x ⟨hx, hlo, hhi⟩
    exact ⟨hx, hlo, by push_cast; linarith⟩
  have hle := ncard_le_ncard hs
    (A.finite_window (-(n : ℝ)) ((2 * n + 1 : ℕ) : ℝ))
  have hw : windowCount A (-(n : ℝ)) ((2 * n + 1 : ℕ) : ℝ) ≤ (2 * n + 1) * K := by
    simpa only [Int.cast_neg, Int.cast_natCast] using h.windowCount_nat (2 * n + 1) (-(n : ℤ))
  exact hle.trans hw

/-- Bounded local counts imply the required vanishing quadratic lower count,
using integer radii with both endpoints included. -/
theorem UnitCellBound.frequently_centered_count_lt_quadratic
    {A : LocallyFiniteCarrier} {K : ℕ} (h : UnitCellBound A K) (c : ℝ) (hc : 0 < c) :
    ∃ᶠ R : ℝ in atTop, ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2 := by
  apply frequently_atTop.mpr
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (max x (max 1 (3 * (K : ℝ) / c)))
  have hx : x < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt
    ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hk : 3 * (K : ℝ) < c * n := by
    have hn' := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
    linarith [(div_lt_iff₀ hc).mp hn']
  refine ⟨(n : ℝ), hx.le, ?_⟩
  calc
    _ ≤ (2 * (n : ℝ) + 1) * K := by exact_mod_cast h.centered_count_nat n
    _ ≤ (3 * (K : ℝ)) * n := by
      have hlin : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
      calc
        _ ≤ (3 * (n : ℝ)) * K := mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg _)
        _ = _ := by ring
    _ < c * (n : ℝ) ^ 2 := by
      have ht := mul_lt_mul_of_pos_right hk (show 0 < (n : ℝ) by linarith)
      linear_combination ht

/-- Every broad value-only pair on two relatively separated allowed
carriers is a finite sum of modulated combs on each original record. -/
theorem finiteModulatedDiracCombSum_pair_of_two_unitCellBounds
    (A B : LocallyFiniteCarrier) (K M : ℕ) (hA : UnitCellBound A K) (hB : UnitCellBound B M)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ DistributionalMeyerPairSpace A B) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  have hp := (mem_distributionalMeyerPairSpace_iff A B T).mp hT
  exact finiteModulatedDiracCombSum_pair_of_unitCellBound A B K hA T hp.1 hp.2
    hB.frequently_centered_count_lt_quadratic

end
end MeyerGeneralProblem
