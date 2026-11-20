module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyConvolution
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Physical-frequency cutoffs and their integrated diagonals

The Cayley unitary preserves every upper frequency cutoff. Its powers
give nested cutoff defects, and the original Fourier coefficients
compute the integrated one-step defect and band diagonals.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal InnerProductSpace NNReal Topology

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- The orthogonal coordinate cutoff on a square-summable sequence. -/
def lpCoordinateProjection {ι : Type*} (s : Set ι) : SeqL2(ι) →L[ℂ] SeqL2(ι) := by
  classical
  let P : SeqL2(ι) →ₗ[ℂ] SeqL2(ι) :=
    { toFun := fun f => ⟨s.indicator f, (lp.memℓp f).norm.mono fun i => by
        by_cases hi : i ∈ s
        · simp [hi]
        · simp [hi, norm_nonneg]⟩
      map_add' := by
        intro f g
        ext i
        change s.indicator (fun j => f j + g j) i =
          s.indicator f i + s.indicator g i
        by_cases hi : i ∈ s <;> simp [hi]
      map_smul' := by
        intro c f
        ext i
        by_cases hi : i ∈ s <;> simp [hi, lp.coeFn_smul] }
  refine P.mkContinuous 1 fun f => ?_
  rw [one_mul]
  apply lp.norm_mono (by norm_num)
  intro i
  change ‖s.indicator f i‖ ≤ ‖f i‖
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi, norm_nonneg]

/-- A cutoff retains precisely the coordinates in the selected set. -/
theorem lpCoordinateProjection_apply {ι : Type*} (s : Set ι) (f : SeqL2(ι)) (i : ι) :
    lpCoordinateProjection s f i = s.indicator f i := rfl

/-- Composing coordinate cutoffs intersects their coordinate sets. -/
theorem lpCoordinateProjection_comp {ι : Type*} (s t : Set ι) :
    lpCoordinateProjection s ∘L lpCoordinateProjection t = lpCoordinateProjection (s ∩ t) := by
  apply ContinuousLinearMap.ext
  intro f
  ext i
  change lpCoordinateProjection s (lpCoordinateProjection t f) i =
    lpCoordinateProjection (s ∩ t) f i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [lpCoordinateProjection_apply, hs, ht]

/-- The coordinate cutoff is self-adjoint. -/
theorem adjoint_lpCoordinateProjection {ι : Type*} (s : Set ι) :
    (lpCoordinateProjection s).adjoint = lpCoordinateProjection s := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [lpCoordinateProjection_apply, hi]

/-- The upper cutoff retains frequencies greater than or equal to its threshold. -/
def lpUpperFrequencyProjection {ι : Type*} (b : ι → ℝ) (t : ℝ) : SeqL2(ι) →L[ℂ] SeqL2(ι) :=
  lpCoordinateProjection {n | t ≤ b n}

/-- The upper half-line cut applied to a coordinate is an explicit step function. -/
theorem lpUpperFrequencyProjection_apply {ι : Type*} (b : ι → ℝ) (t : ℝ)
    (f : SeqL2(ι)) (i : ι) :
    lpUpperFrequencyProjection b t f i = if t ≤ b i then f i else 0 := by
  classical
  rw [lpUpperFrequencyProjection, lpCoordinateProjection_apply]
  by_cases hi : t ≤ b i <;> simp [hi]

private theorem torusDirectionalFrequency_sub {d : Type*} [Fintype d] (β : d → ℝ) (m n : d → ℤ) :
    torusDirectionalFrequency β (m - n) = torusDirectionalFrequency β m - torusDirectionalFrequency β n := by
  simp only [torusDirectionalFrequency, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

section CayleyCutoffs

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- Nonnegative physical shifts preserve every upper spectral cutoff. -/
theorem lpUpperFrequencyProjection_torusPoissonCayleyConvolution
    (t : ℝ) (f : SeqL2(d → ℤ)) :
    let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    P (U (P f)) = U (P f) := by
  classical
  intro P U
  ext n
  by_cases hn : t ≤ torusDirectionalFrequency β n
  · rw [lpUpperFrequencyProjection_apply, ite_eq_left hn]
  · rw [lpUpperFrequencyProjection_apply, ite_eq_right hn]
    symm
    have hSum := hasSum_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance (P f) n
    have hZero (m : d → ℤ) :
        mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) (n - m) *
          P f m = 0 := by
      rw [lpUpperFrequencyProjection_apply]
      by_cases hm : t ≤ torusDirectionalFrequency β m
      · rw [ite_eq_left hm]
        have hlt : torusDirectionalFrequency β (n - m) < 0 := by
          rw [torusDirectionalFrequency_sub]
          exact sub_neg.mpr ((lt_of_not_ge hn).trans_le hm)
        rw [mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance _ hlt,
          zero_mul]
      · rw [ite_eq_right hm, mul_zero]
    have hZ : HasSum (fun _ : d → ℤ => (0 : ℂ)) 0 := hasSum_zero
    exact hSum.unique (hZ.congr_fun fun m => hZero m)

/-- A reverse step from the output zero coordinate reads the conjugate of
the original boundary coefficient at the reversed index. -/
theorem torusPoissonCayleyConvolution_symm_single_zero (m : d → ℤ) :
    (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance).symm
      (lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)) m =
      star (mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) (-m)) := by
  classical
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let e (j : d → ℤ) := lp.single (E := fun _ : d → ℤ => ℂ) 2 j (1 : ℂ)
  have hAdj := (U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ)).adjoint_inner_right (e m) (e 0)
  rw [U.adjoint_eq_symm] at hAdj
  change ⟪e m, U.symm (e 0)⟫_ℂ = ⟪U (e m), e 0⟫_ℂ at hAdj
  rw [show e 0 = lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ) from rfl,
    show e m = lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ) from rfl,
    lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply', RCLike.inner_apply'] at hAdj
  simpa only [U, torusPoissonCayleyConvolution_single, zero_sub, mul_one,
    map_one, one_mul, Complex.star_def] using hAdj


/-- An upper half-line cutoff is idempotent. -/
theorem lpUpperFrequencyProjection_idempotent {ι : Type*} (b : ι → ℝ) (t : ℝ)
    (f : SeqL2(ι)) :
    lpUpperFrequencyProjection b t (lpUpperFrequencyProjection b t f) = lpUpperFrequencyProjection b t f := by
  ext i
  by_cases hi : t ≤ b i <;> simp [lpUpperFrequencyProjection_apply, hi]

/-- Every nonnegative power of the Cayley unitary preserves each upper cutoff. -/
theorem lpUpperFrequencyProjection_torusPoissonCayleyConvolution_pow
    (t : ℝ) (q : ℕ) (f : SeqL2(d → ℤ)) :
    let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    P ((U ^ q) (P f)) = (U ^ q) (P f) := by
  intro P U
  induction q with
  | zero =>
    rw [pow_zero]
    exact lpUpperFrequencyProjection_idempotent (torusDirectionalFrequency β) t f
  | succ q ih =>
    rw [pow_succ', LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply, ← ih]
    exact lpUpperFrequencyProjection_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
      t ((U ^ q) (P f))

/-- The defect after q applications is the original cutoff minus the
projection onto its image under the q-th power of the Cayley unitary. -/
def torusPoissonCayleyCutoffDefect (t : ℝ) (q : ℕ) :
    SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
  let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
  let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
    (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance ^ q : _ ≃ₗᵢ[ℂ] _)
  P - V * P * V.adjoint

/-- Each iterated Cayley cutoff defect is a self-adjoint idempotent,
the orthogonal projection onto the difference of the two nested ranges. -/
theorem torusPoissonCayleyCutoffDefect_is_projection (t : ℝ) (q : ℕ) :
    let K := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q
    K.adjoint = K ∧ K * K = K := by
  let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := (U ^ q : _ ≃ₗᵢ[ℂ] _)
  let Q := V * P * V.adjoint
  change (P - Q).adjoint = P - Q ∧ (P - Q) * (P - Q) = P - Q
  have hPAdj : P.adjoint = P := adjoint_lpCoordinateProjection _
  have hPP : P * P = P := by
    apply ContinuousLinearMap.ext
    exact lpUpperFrequencyProjection_idempotent (torusDirectionalFrequency β) t
  have hV : V.adjoint * V = 1 := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      V.isometry_iff_adjoint_comp_self.mp (U ^ q).isometry
  have hQAdj : Q.adjoint = Q := by
    simp only [Q, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hPAdj, ContinuousLinearMap.comp_assoc]
  have hQQ : Q * Q = Q := by
    calc
      _ = V * P * (V.adjoint * V) * P * V.adjoint := by simp only [Q, mul_assoc]
      _ = _ := by rw [hV, mul_one, mul_assoc V P P, hPP]
  have hPQ : P * Q = Q := by
    apply ContinuousLinearMap.ext
    intro f
    change P ((U ^ q) (P (V.adjoint f))) = (U ^ q) (P (V.adjoint f))
    exact lpUpperFrequencyProjection_torusPoissonCayleyConvolution_pow
      β S T hT hCont hCount hAdvance t q (V.adjoint f)
  have hQP : Q * P = Q := by
    have h := congrArg (fun L : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) => L.adjoint) hPQ
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hPAdj, hQAdj] using h
  refine ⟨?_, ?_⟩
  · exact (map_sub ContinuousLinearMap.adjoint P Q).trans (by rw [hPAdj, hQAdj])
  · rw [sub_mul, mul_sub, mul_sub, hPP, hPQ, hQP, hQQ, sub_self, sub_zero]


private theorem torusDirectionalFrequency_zero {d : Type*} [Fintype d] (β : d → ℝ) :
    torusDirectionalFrequency β 0 = 0 := by
  simp [torusDirectionalFrequency]

private theorem torusDirectionalFrequency_neg {d : Type*} [Fintype d] (β : d → ℝ) (n : d → ℤ) :
    torusDirectionalFrequency β (-n) = -torusDirectionalFrequency β n := by
  simpa only [zero_sub, torusDirectionalFrequency_zero] using
    torusDirectionalFrequency_sub β 0 n

include hAdvance in
/-- The output-zero diagonal of the one-step cutoff defect is the
boundary Fourier mass crossing that threshold. -/
theorem re_inner_torusPoissonCayleyCutoffDefect_one (t : ℝ) :
    let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
    let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
    (⟪e, torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 e⟫_ℂ).re =
      ∑' n : d → ℤ, if t ∈ Ioc (-torusDirectionalFrequency β n) 0 then ‖mFourierCoeff B n‖ ^ 2 else 0 := by
  classical
  let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
  let b := torusDirectionalFrequency β
  let P := lpUpperFrequencyProjection b t
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := U
  let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let g (n : d → ℤ) := ‖mFourierCoeff B n‖ ^ 2
  let H (n : d → ℤ) := if t ≤ -b n then g n else 0
  let R (n : d → ℤ) := if t ∈ Ioc (-b n) 0 then g n else 0
  change (⟪e, torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 e⟫_ℂ).re = ∑' n, R n
  have hK : torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 =
      P - V * P * V.adjoint := by
    unfold torusPoissonCayleyCutoffDefect
    rw [pow_one]
  rw [hK, sub_apply, inner_sub_right, Complex.sub_re]
  have hb₀ : b 0 = 0 := torusDirectionalFrequency_zero β
  have hP : (⟪e, P e⟫_ℂ).re = if t ≤ 0 then 1 else 0 := by
    change (⟪lp.single 2 0 (1 : ℂ), P e⟫_ℂ).re = _
    rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
    change (lpUpperFrequencyProjection b t e 0).re = _
    rw [lpUpperFrequencyProjection_apply, hb₀]
    by_cases ht : t ≤ 0 <;> simp [ht, e]
  have hPSelf : P.adjoint = P := adjoint_lpCoordinateProjection _
  have hPProd : P * P = P := by
    apply ContinuousLinearMap.ext
    exact lpUpperFrequencyProjection_idempotent b t
  let A := P * V.adjoint
  have hA : A.adjoint * A = V * P * V.adjoint := by
    have he : A.adjoint = V * P := by
      simp only [A, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, hPSelf]
    rw [he]
    change V * P * (P * V.adjoint) = _
    rw [← mul_assoc (V * P), mul_assoc V P P, hPProd]
  have hQ : (⟪e, (V * P * V.adjoint) e⟫_ℂ).re = ‖P (U.symm e)‖ ^ 2 := by
    have hA' := A.apply_norm_sq_eq_inner_adjoint_right e
    change ‖A e‖ ^ 2 = (⟪e, (A.adjoint * A) e⟫_ℂ).re at hA'
    have hE : A e = P (U.symm e) := by
      change P ((U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ)).adjoint e) = _
      rw [U.adjoint_eq_symm]
      rfl
    rw [← hE, hA', hA]
  have hHead : ‖P (U.symm e)‖ ^ 2 = ∑' n, H n := by
    have hNorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (P (U.symm e))
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at hNorm
    rw [Real.rpow_two] at hNorm
    rw [hNorm, ← (Equiv.neg (d → ℤ)).tsum_eq]
    apply tsum_congr
    intro n
    rw [show (Equiv.neg (d → ℤ)) n = -n by rfl]
    change ‖lpUpperFrequencyProjection b t (U.symm e) (-n)‖ ^ 2 = H n
    rw [lpUpperFrequencyProjection_apply, show b (-n) = -b n from
      torusDirectionalFrequency_neg β n]
    by_cases hn : t ≤ -b n
    · rw [ite_eq_left hn]
      change ‖(torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance).symm e (-n)‖ ^ 2 = _
      rw [torusPoissonCayleyConvolution_symm_single_zero]
      simp [H, g, B, hn]
    · simp [H, hn]
  rw [hP, hQ, hHead]
  by_cases ht : t ≤ 0
  · have hSum : HasSum g 1 := hasSum_sq_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
    have hHS : Summable H := hSum.summable.of_nonneg_of_le
      (fun n => by unfold H g; split_ifs <;> positivity)
      (fun n => by
        unfold H
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _)
    have hRS : Summable R := hSum.summable.of_nonneg_of_le
      (fun n => by unfold R g; split_ifs <;> positivity)
      (fun n => by
        unfold R
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _)
    have hPartition (n : d → ℤ) : H n + R n = g n := by
      by_cases hn : t ≤ -b n
      · simp [H, R, hn, not_lt_of_ge hn]
      · simp [H, R, hn, lt_of_not_ge hn, ht]
    have hAll : (∑' n, H n) + ∑' n, R n = 1 := by
      rw [← hHS.tsum_add hRS, tsum_congr hPartition, hSum.tsum_eq]
    rw [ite_eq_left ht]
    linarith only [hAll]
  · have hH0 (n : d → ℤ) : H n = 0 := by
      by_cases hn : t ≤ -b n
      · have hNeg : b n < 0 := by linarith only [lt_of_not_ge ht, hn]
        have hz : mFourierCoeff B n = 0 :=
          mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance n hNeg
        simp [H, g, hn, hz]
      · simp [H, hn]
    have hR0 (n : d → ℤ) : R n = 0 := by simp [R, ht]
    simp only [ite_eq_right ht, hH0, hR0, tsum_zero, sub_zero]


include hAdvance in
/-- The integrated output-zero diagonal of the one-step cutoff defect
is exactly the finite directional Fourier energy. -/
theorem lintegral_torusPoissonCayleyCutoffDefect_one_eq_energy (E : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E) :
    let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
    (∫⁻ t : ℝ, ENNReal.ofReal
      (⟪e, torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 e⟫_ℂ).re) =
      ENNReal.ofReal E := by
  classical
  let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
  let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let a (n : d → ℤ) := ‖mFourierCoeff B n‖ ^ 2
  let b := torusDirectionalFrequency β
  let w (n : d → ℤ) (t : ℝ) := (Ioc (-b n) 0).indicator (fun _ => ENNReal.ofReal (a n)) t
  have hA : Summable a := (hasSum_sq_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance).summable
  have hEq (t : ℝ) : ENNReal.ofReal
      (⟪e, torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 e⟫_ℂ).re =
        ∑' n, w n t := by
    rw [re_inner_torusPoissonCayleyCutoffDefect_one β S T hT hCont hCount hAdvance]
    let g (n : d → ℤ) := if t ∈ Ioc (-b n) 0 then a n else 0
    have hG0 (n : d → ℤ) : 0 ≤ g n := by unfold g a; split_ifs <;> positivity
    have hG_le (n : d → ℤ) : g n ≤ a n := by
      unfold g
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    change ENNReal.ofReal (∑' n, g n) = _
    rw [ENNReal.ofReal_tsum_of_nonneg hG0 (hA.of_nonneg_of_le hG0 hG_le)]
    apply tsum_congr
    intro n
    by_cases h : t ∈ Ioc (-b n) 0
    · simp only [g, w, ite_eq_left h, indicator_of_mem h]
    · simp only [g, w, ite_eq_right h, indicator_of_notMem h, ENNReal.ofReal_zero]
  have hW (n : d → ℤ) : Measurable (w n) :=
    measurable_const.indicator measurableSet_Ioc
  have hWint (n : d → ℤ) : (∫⁻ t, w n t) = ENNReal.ofReal (b n * a n) := by
    unfold w
    rw [lintegral_indicator measurableSet_Ioc, lintegral_const,
      Measure.restrict_apply_univ, Real.volume_Ioc, zero_sub, neg_neg,
      ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have hNonneg (n : d → ℤ) : 0 ≤ b n * a n := by
    by_cases hn : b n < 0
    · have hz : mFourierCoeff B n = 0 :=
        mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance n hn
      simp [a, hz]
    · exact mul_nonneg (le_of_not_gt hn) (sq_nonneg _)
  change (∫⁻ t : ℝ, ENNReal.ofReal
    (⟪e, torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t 1 e⟫_ℂ).re) = _
  calc
    _ = ∫⁻ t, ∑' n, w n t := lintegral_congr hEq
    _ = ∑' n, ∫⁻ t, w n t := lintegral_tsum fun n => (hW n).aemeasurable
    _ = ∑' n, ENNReal.ofReal (b n * a n) := tsum_congr hWint
    _ = _ := by
      have hSum : HasSum (fun n => b n * a n) E := hE
      rw [← ENNReal.ofReal_tsum_of_nonneg hNonneg hSum.summable, hSum.tsum_eq]

/-- The integrated output-zero diagonal of a band of width W is W. -/
theorem lintegral_upperFrequencyBand_diag (W : ℝ) (hW : 0 ≤ W) :
    let b := torusDirectionalFrequency β
    let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
    (∫⁻ t : ℝ, ENNReal.ofReal
      (⟪e, (lpUpperFrequencyProjection b t - lpUpperFrequencyProjection b (t + W)) e⟫_ℂ).re) =
      ENNReal.ofReal W := by
  classical
  let b := torusDirectionalFrequency β
  let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
  have hOne (t : ℝ) : (⟪e, lpUpperFrequencyProjection b t e⟫_ℂ).re = if t ≤ 0 then 1 else 0 := by
    change (⟪lp.single 2 0 (1 : ℂ), lpUpperFrequencyProjection b t e⟫_ℂ).re = _
    rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul,
      lpUpperFrequencyProjection_apply]
    rw [show b 0 = 0 from torusDirectionalFrequency_zero β]
    by_cases ht : t ≤ 0 <;> simp [ht, e]
  have hEq (t : ℝ) :
      ENNReal.ofReal
        (⟪e, (lpUpperFrequencyProjection b t - lpUpperFrequencyProjection b (t + W)) e⟫_ℂ).re =
      (Ioc (-W) 0).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    rw [sub_apply, inner_sub_right, Complex.sub_re, hOne, hOne]
    by_cases ht : t ≤ 0
    · by_cases hu : t + W ≤ 0
      · have hn : ¬-W < t := by linarith only [hu]
        simp [ht, hu, hn]
      · have hp : -W < t := by linarith only [lt_of_not_ge hu]
        simp [ht, hu, hp]
    · have hu : ¬t + W ≤ 0 := fun h => ht (by linarith only [h, hW])
      simp [ht, hu]
  change (∫⁻ t : ℝ, ENNReal.ofReal
    (⟪e, (lpUpperFrequencyProjection b t - lpUpperFrequencyProjection b (t + W)) e⟫_ℂ).re) = _
  rw [lintegral_congr hEq, lintegral_indicator measurableSet_Ioc, lintegral_const, one_mul,
    Measure.restrict_apply_univ, Real.volume_Ioc, zero_sub, neg_neg]

end CayleyCutoffs

end
end MeyerGeneralProblem
