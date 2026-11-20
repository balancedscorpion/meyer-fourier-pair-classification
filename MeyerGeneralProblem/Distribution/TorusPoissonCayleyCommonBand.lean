module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyMultistepTrace
public import MeyerGeneralProblem.Distribution.CovariantProjectionTrace

@[expose] public section

/-!
# Common frequency bands for Cayley powers

A vector in a frequency band and in the range of the transported lower
cutoff has a preimage whose intermediate powers stay in the same band.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive MeasureTheory Set UnitAddTorus
open scoped ENNReal InnerProductSpace

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- A coordinate that vanishes in the first q + 1 iterates also vanishes
in the q-th finite difference. -/
theorem lp_finiteDifference_apply_eq_zero_of_pow_apply_eq_zero
    {ι : Type*} (U : SeqL2(ι) ≃ₗᵢ[ℂ] SeqL2(ι)) (f : SeqL2(ι)) (i : ι)
    (q : ℕ) (h : ∀ j ≤ q, (U ^ j) f i = 0) :
    let C : SeqL2(ι) →L[ℂ] SeqL2(ι) := U
    ((C - 1) ^ q) f i = 0 := by
  intro C
  induction q generalizing f with
  | zero =>
    change f i = 0
    have h₀ := h 0 le_rfl
    rw [pow_zero] at h₀
    exact h₀
  | succ q ih =>
    have hStep (j : ℕ) (hj : j ≤ q) : (U ^ j) (U f - f) i = 0 := by
      have hNext : (U ^ j) (U f) = (U ^ (j + 1)) f := by
        rw [pow_succ, LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
      rw [map_sub, lp.coeFn_sub, Pi.sub_apply, hNext, h _ (Nat.succ_le_succ hj),
        h _ (hj.trans (Nat.le_succ q)), sub_zero]
    rw [pow_succ]
    change ((C - 1) ^ q) (U f - f) i = 0
    exact ih _ hStep

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- A nonzero band vector in the kernel of the q-step defect pulls back to a
nonzero vector with all q + 1 iterates in the same half-open frequency band. -/
theorem exists_torusPoissonCayleyCommonBand_of_cutoffDefect_eq_zero
    (t W : ℝ) (q : ℕ) (h : SeqL2(d → ℤ)) (h₀ : h ≠ 0)
    (hLow : lpUpperFrequencyProjection (torusDirectionalFrequency β) t h = h)
    (hHigh : lpUpperFrequencyProjection (torusDirectionalFrequency β) (t + W) h = 0)
    (hDefect : torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q h = 0) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    ∃ f : SeqL2(d → ℤ), f ≠ 0 ∧ (U ^ q) f = h ∧
      ∀ j : ℕ, j ≤ q → ∀ n : d → ℤ,
        torusDirectionalFrequency β n ∉ Ico t (t + W) → (U ^ j) f n = 0 := by
  intro U
  let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
  let Q := lpUpperFrequencyProjection (torusDirectionalFrequency β) (t + W)
  let f := (U ^ q).symm h
  have hfq : (U ^ q) f = h := (U ^ q).apply_symm_apply h
  have hf₀ : f ≠ 0 := by
    intro hf
    apply h₀
    rw [← hfq, hf, map_zero]
  let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := (U ^ q : _ ≃ₗᵢ[ℂ] _)
  change (P - V * P * V.adjoint) h = 0 at hDefect
  change P h - V (P (V.adjoint h)) = 0 at hDefect
  rw [hLow, (U ^ q).adjoint_eq_symm] at hDefect
  have hfP : P f = f := (U ^ q).injective ((sub_eq_zero.mp hDefect).symm.trans hfq.symm)
  refine ⟨f, hf₀, hfq, fun j hj n hn => ?_⟩
  let y := (U ^ j) f
  have hyP : P y = y := by
    have hp := lpUpperFrequencyProjection_torusPoissonCayleyConvolution_pow
      β S T hT hCont hCount hAdvance t j f
    change P ((U ^ j) (P f)) = (U ^ j) (P f) at hp
    rwa [hfP] at hp
  have hCompose : (U ^ (q - j)) y = h := by
    calc
      (U ^ (q - j)) y = (U ^ (q - j) * U ^ j) f := by
        rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
      _ = h := by rw [← pow_add, Nat.sub_add_cancel hj, hfq]
  have hQ : Q.adjoint = Q := adjoint_lpCoordinateProjection _
  have hUpper : Q ((U ^ (q - j)) (Q y)) = (U ^ (q - j)) (Q y) :=
    lpUpperFrequencyProjection_torusPoissonCayleyConvolution_pow
      β S T hT hCont hCount hAdvance (t + W) (q - j) y
  have hInner : ⟪y, Q y⟫_ℂ = 0 := by
    rw [← (U ^ (q - j)).inner_map_map, hCompose]
    nth_rw 1 [← hUpper]
    rw [← hQ, ContinuousLinearMap.adjoint_inner_right, hQ, hHigh, inner_zero_left]
  have hyQ : Q y = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      ⟪Q y, Q y⟫_ℂ = ⟪y, Q (Q y)⟫_ℂ := by
        rw [← Q.adjoint_inner_right, hQ]
      _ = 0 := by
        rw [show Q (Q y) = Q y from lpUpperFrequencyProjection_idempotent _ _ _]
        exact hInner
  change y n = 0
  by_cases htn : t ≤ torusDirectionalFrequency β n
  · have hWn : t + W ≤ torusDirectionalFrequency β n :=
      le_of_not_gt fun hlt => hn ⟨htn, hlt⟩
    have hnQ := congrArg (fun g : SeqL2(d → ℤ) => g n) hyQ
    change lpUpperFrequencyProjection (torusDirectionalFrequency β) (t + W) y n = 0 at hnQ
    simpa only [lpUpperFrequencyProjection_apply, ite_eq_left hWn] using hnQ
  · have hnP := congrArg (fun g : SeqL2(d → ℤ) => g n) hyP
    change lpUpperFrequencyProjection (torusDirectionalFrequency β) t y n = y n at hnP
    simpa only [lpUpperFrequencyProjection_apply, ite_eq_right htn] using hnP.symm

/-- A band wider than q times the directional energy contains every iterate
up to step q of a single nonzero vector. -/
theorem exists_torusPoissonCayleyCommonBand_of_mul_energy_lt
    (E W : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) (hWidth : (q : ℝ) * E < W) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    ∃ (t : ℝ) (f : SeqL2(d → ℤ)), f ≠ 0 ∧
      ∀ j : ℕ, j ≤ q → ∀ n : d → ℤ,
        torusDirectionalFrequency β n ∉ Ico t (t + W) → (U ^ j) f n = 0 := by
  classical
  intro U
  let b := torusDirectionalFrequency β
  let P (t : ℝ) := lpUpperFrequencyProjection b t
  let R (t : ℝ) := lpCoordinateProjection {n | b n ∈ Ico t (t + W)}
  let L (t : ℝ) := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q
  have hE₀ : 0 ≤ E := hE.nonneg fun n => by
    by_cases hn : b n < 0
    · rw [mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg
        β S T hT hCont hCount hAdvance n hn]
      simp
    · exact mul_nonneg (le_of_not_gt hn) (sq_nonneg _)
  have hW : 0 < W := (mul_nonneg (Nat.cast_nonneg q) hE₀).trans_lt hWidth
  have hBand (t : ℝ) : R t = P t - P (t + W) := by
    apply ContinuousLinearMap.ext
    intro f
    ext n
    change lpCoordinateProjection {n | b n ∈ Ico t (t + W)} f n =
      P t f n - P (t + W) f n
    rw [lpCoordinateProjection_apply]
    change Set.indicator {n | b n ∈ Ico t (t + W)} f n =
      lpUpperFrequencyProjection b t f n - lpUpperFrequencyProjection b (t + W) f n
    rw [lpUpperFrequencyProjection_apply, lpUpperFrequencyProjection_apply]
    by_cases hn : t ≤ b n
    · by_cases hUpper : t + W ≤ b n
      · simp [hn, hUpper, not_lt_of_ge hUpper]
      · simp [hn, hUpper, lt_of_not_ge hUpper]
    · have hUpper : ¬ t + W ≤ b n := fun ht => hn ((le_add_of_nonneg_right hW.le).trans ht)
      simp [hn, hUpper]
  have hPField (s : ℝ) : LpOperatorField b (fun t => P (t + s)) := by
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [P, lpUpperFrequencyProjection_apply]
      have h : Measurable (fun t : ℝ => t + s) := measurable_id.add_const s
      exact Measurable.ite (measurableSet_le h measurable_const) measurable_const measurable_const
    · intro t j f
      change P (t + b j + s) (lpFrequencyShift j f) =
        lpFrequencyShift j (P (t + s) f)
      rw [add_right_comm t (b j) s]
      exact lpUpperFrequencyProjection_lpFrequencyShift β j (t + s) f
  have hRField : LpOperatorField b R := by
    have h := (hPField 0).sub (hPField W)
    simpa only [add_zero, ← hBand] using h
  have hLField : LpOperatorField b L :=
    ⟨fun i _ => measurable_torusPoissonCayleyCutoffDefect_apply β S T hT hCont hCount hAdvance q _ i,
      fun t j f => torusPoissonCayleyCutoffDefect_lpFrequencyShift β S T hT hCont hCount hAdvance q j t f⟩
  have hRProj (t : ℝ) : IsStarProjection (R t) := by
    refine ⟨?_, adjoint_lpCoordinateProjection _⟩
    change lpCoordinateProjection _ ∘L lpCoordinateProjection _ = _
    simp only [R, lpCoordinateProjection_comp, inter_self]
  have hLProj (t : ℝ) : IsStarProjection (L t) := by
    obtain ⟨hAdj, hMul⟩ := torusPoissonCayleyCutoffDefect_is_projection
      β S T hT hCont hCount hAdvance t q
    exact ⟨hMul, hAdj⟩
  have hRTrace : lpIntegratedZeroDiagonal R = ENNReal.ofReal W := by
    simp_rw [lpIntegratedZeroDiagonal, hBand]
    exact lintegral_upperFrequencyBand_diag β W hW.le
  have hLTrace : lpIntegratedZeroDiagonal L = (q : ℝ≥0∞) * ENNReal.ofReal E :=
    lpIntegratedZeroDiagonal_torusPoissonCayleyCutoffDefect_eq_mul_energy
      β S T hT hCont hCount hAdvance E hE q
  have hLt : lpIntegratedZeroDiagonal L < lpIntegratedZeroDiagonal R := by
    rw [hLTrace, hRTrace, ← ENNReal.ofReal_natCast q, ← ENNReal.ofReal_mul (Nat.cast_nonneg q)]
    exact (ENNReal.ofReal_lt_ofReal_iff hW).mpr hWidth
  obtain ⟨t, x, hx, hxR, hxL⟩ :=
    exists_fixed_vector_in_kernel_of_lt_integrated_diagonal b R L hRField hLField hRProj hLProj hLt
  have hxZero (n : d → ℤ) (hn : b n ∉ Ico t (t + W)) : x n = 0 := by
    have h := congrArg (fun f : SeqL2(d → ℤ) => f n) hxR
    change lpCoordinateProjection {n | b n ∈ Ico t (t + W)} x n = x n at h
    have hn' : n ∉ {m : d → ℤ | b m ∈ Ico t (t + W)} := hn
    simpa only [lpCoordinateProjection_apply, Set.indicator_of_notMem hn'] using h.symm
  have hxLow : P t x = x := by
    ext n
    change lpUpperFrequencyProjection b t x n = x n
    rw [lpUpperFrequencyProjection_apply]
    by_cases hn : t ≤ b n
    · exact ite_eq_left hn
    · rw [ite_eq_right hn, hxZero n (fun hm => hn hm.1)]
  have hxHigh : P (t + W) x = 0 := by
    ext n
    change lpUpperFrequencyProjection b (t + W) x n = 0
    rw [lpUpperFrequencyProjection_apply]
    by_cases hn : t + W ≤ b n
    · rw [ite_eq_left hn, hxZero n (fun hm => (not_lt_of_ge hn) hm.2)]
    · exact ite_eq_right hn
  obtain ⟨f, hf, _, hfBand⟩ := exists_torusPoissonCayleyCommonBand_of_cutoffDefect_eq_zero
    β S T hT hCont hCount hAdvance t W q x hx hxLow hxHigh hxL
  exact ⟨t, f, hf, hfBand⟩

/-- Moving the band by a frequency from the original module puts all
iterates into a bounded nonnegative frequency interval. -/
theorem exists_torusPoissonCayleyCommonNonnegativeBand
    (E W : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) (hWidth : (q : ℝ) * E < W) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    ∃ (W₀ : ℝ) (f : SeqL2(d → ℤ)), 0 ≤ W₀ ∧ f ≠ 0 ∧
      ∀ j : ℕ, j ≤ q → ∀ n : d → ℤ,
        torusDirectionalFrequency β n ∉ Icc 0 W₀ → (U ^ j) f n = 0 := by
  intro U
  let b := torusDirectionalFrequency β
  obtain ⟨t, f, hf, hBand⟩ := exists_torusPoissonCayleyCommonBand_of_mul_energy_lt
    β S T hT hCont hCount hAdvance E W hE q hWidth
  by_cases hPos : ∃ k : d → ℤ, 0 < b k
  · obtain ⟨k, hk⟩ := hPos
    obtain ⟨N, hN⟩ := exists_nat_gt (-t / b k)
    let m := N • k
    have hm : b m = (N : ℝ) * b k := by
      change (∑ i, ((m i : ℤ) : ℝ) * β i) = (N : ℝ) * ∑ i, (k i : ℝ) * β i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change ((N • k i : ℤ) : ℝ) * β i = _
      simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
      ring
    have ht : 0 < t + b m := by
      rw [hm]
      have h := (div_lt_iff₀ hk).mp hN
      linarith
    let W₀ := max 0 (t + b m + W)
    refine ⟨W₀, lpFrequencyShift m f, le_max_left _ _, ?_, fun j hj n hn => ?_⟩
    · intro h
      exact hf ((lpFrequencyShift m).injective (h.trans (map_zero (lpFrequencyShift m)).symm))
    · have hShift := torusPoissonCayleyConvolution_pow_lpFrequencyShift
        β S T hT hCont hCount hAdvance j m f
      change (U ^ j) (lpFrequencyShift m f) = lpFrequencyShift m ((U ^ j) f) at hShift
      rw [hShift, lpFrequencyShift_apply]
      apply hBand j hj (n - m)
      intro hIn
      have hb : b (n - m) = b n - b m := by
        simp only [b, torusDirectionalFrequency, Pi.sub_apply, Int.cast_sub,
          sub_mul, Finset.sum_sub_distrib]
      change t ≤ b (n - m) ∧ b (n - m) < t + W at hIn
      rw [hb] at hIn
      apply hn
      refine ⟨by linarith [hIn.1], le_trans ?_ (le_max_right _ _)⟩
      linarith [hIn.2]
  · have hZero (n : d → ℤ) : b n = 0 := by
      have h₁ : b n ≤ 0 := le_of_not_gt fun h => hPos ⟨n, h⟩
      have h₂ : b (-n) ≤ 0 := le_of_not_gt fun h => hPos ⟨-n, h⟩
      have hNeg : b (-n) = -b n := by
        simp only [b, torusDirectionalFrequency, Pi.neg_apply, Int.cast_neg,
          neg_mul, Finset.sum_neg_distrib]
      rw [hNeg] at h₂
      linarith
    exact ⟨0, f, le_rfl, hf, fun j hj n hn =>
      (hn (by change 0 ≤ b n ∧ b n ≤ 0; rw [hZero]; exact ⟨le_rfl, le_rfl⟩)).elim⟩


/-- The q-th Cayley finite difference is nonzero and shares a bounded
nonnegative frequency band with all the preceding iterates of its input. -/
theorem exists_nonzero_torusPoissonCayleyFiniteDifference_in_band
    (E W : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) (hWidth : (q : ℝ) * E < W) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    let C : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := U
    ∃ (W₀ : ℝ) (f : SeqL2(d → ℤ)), 0 ≤ W₀ ∧ f ≠ 0 ∧ ((C - 1) ^ q) f ≠ 0 ∧
      ∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W₀ →
        ((C - 1) ^ q) f n = 0 ∧ ∀ j : ℕ, j ≤ q → (U ^ j) f n = 0 := by
  intro U C
  obtain ⟨W₀, f, hW₀, hf, hBand⟩ := exists_torusPoissonCayleyCommonNonnegativeBand
    β S T hT hCont hCount hAdvance E W hE q hWidth
  have hInj : Function.Injective (fun g : SeqL2(d → ℤ) => ((C - 1) ^ q) g) :=
    torusPoissonCayleyConvolution_sub_one_pow_injective β S T hT hCont hCount hAdvance q
  have hNe : ((C - 1) ^ q) f ≠ 0 := by
    intro h
    apply hf
    exact hInj (h.trans (map_zero ((C - 1) ^ q)).symm)
  refine ⟨W₀, f, hW₀, hf, hNe, fun n hn => ?_⟩
  have hZero (j : ℕ) (hj : j ≤ q) : (U ^ j) f n = 0 := hBand j hj n hn
  exact ⟨lp_finiteDifference_apply_eq_zero_of_pow_apply_eq_zero U f n q hZero, hZero⟩

end
end
end MeyerGeneralProblem
