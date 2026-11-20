module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCutoffTrace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Covariance and integrated trace symmetry

Module shifts translate the physical cutoff threshold and commute with
the Cayley unitary. The defect's entries are measurable and obey the
shifted transpose identity used in integrated trace symmetry.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal InnerProductSpace NNReal Topology

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- The integrated output-zero diagonal of a field of sequence-space operators. -/
def lpIntegratedZeroDiagonal {ι : Type*} [Zero ι] [DecidableEq ι]
    (V : ℝ → SeqL2(ι) →L[ℂ] SeqL2(ι)) : ℝ≥0∞ :=
  let e := lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ)
  ∫⁻ t : ℝ, ENNReal.ofReal (⟪e, V t e⟫_ℂ).re

/-- Tonelli and the shifted transpose of matrix coefficients give trace
symmetry for a covariant field, allowing infinite integrated diagonals. -/
theorem lpIntegratedZeroDiagonal_adjoint_mul_eq_mul_adjoint
    {ι : Type*} [AddGroup ι] [Countable ι] [DecidableEq ι]
    (b : ι → ℝ) (V : ℝ → SeqL2(ι) →L[ℂ] SeqL2(ι))
    (hMeas : ∀ i j : ι, Measurable (fun t => V t (lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ)) i))
    (hCov : ∀ (t : ℝ) (j : ι),
      V t (lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ)) j =
        V (t - b j) (lp.single (E := fun _ : ι => ℂ) 2 (-j) (1 : ℂ)) 0) :
    lpIntegratedZeroDiagonal (fun t => (V t).adjoint * V t) =
      lpIntegratedZeroDiagonal (fun t => V t * (V t).adjoint) := by
  let e (j : ι) := lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ)
  let f (j : ι) (t : ℝ) := ENNReal.ofReal (‖V t (e 0) j‖ ^ 2)
  let g (j : ι) (t : ℝ) := ENNReal.ofReal (‖V t (e j) 0‖ ^ 2)
  have hDiag (A : SeqL2(ι) →L[ℂ] SeqL2(ι)) :
      ENNReal.ofReal (⟪e 0, (A.adjoint * A) (e 0)⟫_ℂ).re =
        ∑' j : ι, ENNReal.ofReal (‖A (e 0) j‖ ^ 2) := by
    have h := A.apply_norm_sq_eq_inner_adjoint_right (e 0)
    change ‖A (e 0)‖ ^ 2 = (⟪e 0, (A.adjoint * A) (e 0)⟫_ℂ).re at h
    rw [← h]
    have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    have hNorm := lp.norm_rpow_eq_tsum hp (A (e 0))
    have hs := (lp.memℓp (A (e 0))).summable hp
    have hTwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [hTwo, Real.rpow_two] at hNorm hs
    rw [hNorm, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
  have hAdj (t : ℝ) (j : ι) : (V t).adjoint (e 0) j = conj (V t (e j) 0) := by
    have h := (V t).adjoint_inner_right (e j) (e 0)
    change ⟪lp.single 2 j (1 : ℂ), (V t).adjoint (e 0)⟫_ℂ =
      ⟪V t (e j), lp.single 2 0 (1 : ℂ)⟫_ℂ at h
    rw [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply', RCLike.inner_apply',
      map_one, one_mul, mul_one] at h
    exact h
  have hf (j : ι) : AEMeasurable (f j) volume :=
    (ENNReal.measurable_ofReal.comp ((hMeas j 0).norm.pow_const 2)).aemeasurable
  have hg (j : ι) : AEMeasurable (g j) volume :=
    (ENNReal.measurable_ofReal.comp ((hMeas 0 j).norm.pow_const 2)).aemeasurable
  have hRight (t : ℝ) : ENNReal.ofReal (⟪e 0, (V t * (V t).adjoint) (e 0)⟫_ℂ).re =
      ∑' j, g j t := by
    have h := hDiag (V t).adjoint
    rw [ContinuousLinearMap.adjoint_adjoint] at h
    rw [h]
    apply tsum_congr
    intro j
    rw [hAdj, Complex.norm_conj]
  have hShift (j : ι) : (∫⁻ t, f j t) = ∫⁻ t, g (-j) t := by
    calc
      _ = ∫⁻ t, g (-j) (t + -b j) := by
        apply lintegral_congr
        intro t
        dsimp only [f, g]
        rw [← sub_eq_add_neg, hCov]
      _ = _ := lintegral_add_right_eq_self _ _
  change (∫⁻ t : ℝ, ENNReal.ofReal (⟪e 0, ((V t).adjoint * V t) (e 0)⟫_ℂ).re) =
    ∫⁻ t : ℝ, ENNReal.ofReal (⟪e 0, (V t * (V t).adjoint) (e 0)⟫_ℂ).re
  rw [lintegral_congr (fun t => hDiag (V t)), lintegral_congr hRight,
    lintegral_tsum hf, lintegral_tsum hg, tsum_congr hShift]
  exact (Equiv.neg ι).tsum_eq (fun j => ∫⁻ t, g j t)

/-- Permuting the coordinates of a square-summable sequence is a linear isometry. -/
def lpCoordinateReindex {ι : Type*} (e : ι ≃ ι) : SeqL2(ι) ≃ₗᵢ[ℂ] SeqL2(ι) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  let R (σ : ι ≃ ι) (f : SeqL2(ι)) : SeqL2(ι) :=
    ⟨fun j => f (σ j), (memℓp_gen_iff hp).mpr (σ.summable_iff.mpr ((lp.memℓp f).summable hp))⟩
  refine {
    toLinearEquiv := {
      toFun := R e
      invFun := R e.symm
      left_inv := by
        intro f
        ext j
        change f (e (e.symm j)) = f j
        rw [e.apply_symm_apply]
      right_inv := by
        intro f
        ext j
        change f (e.symm (e j)) = f j
        rw [e.symm_apply_apply]
      map_add' := by
        intro f g
        ext j
        rfl
      map_smul' := by
        intro c f
        ext j
        rfl }
    norm_map' := fun f => ?_ }
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hR := lp.norm_rpow_eq_tsum hp (R e f)
  have hF := lp.norm_rpow_eq_tsum hp f
  have hp₂ : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [hp₂, Real.rpow_two] at hR hF
  change ‖R e f‖ ^ 2 = ‖f‖ ^ 2
  rw [hR, hF]
  exact e.tsum_eq (fun j => ‖f j‖ ^ 2)

/-- Reindexing precomposes the coefficient sequence with the coordinate bijection. -/
theorem lpCoordinateReindex_apply {ι : Type*} (e : ι ≃ ι) (f : SeqL2(ι)) (i : ι) :
    lpCoordinateReindex e f i = f (e i) := rfl

/-- The module shift by j moves a coordinate formerly at i to i + j. -/
def lpFrequencyShift {ι : Type*} [AddGroup ι] (j : ι) : SeqL2(ι) ≃ₗᵢ[ℂ] SeqL2(ι) :=
  lpCoordinateReindex (Equiv.subRight j)

/-- The coefficient at an output index is the input at that index minus the shift. -/
theorem lpFrequencyShift_apply {ι : Type*} [AddGroup ι] (j : ι) (f : SeqL2(ι)) (i : ι) :
    lpFrequencyShift j f i = f (i - j) := rfl

private theorem torusDirectionalFrequency_sub_for_shift {d : Type*} [Fintype d]
    (β : d → ℝ) (m n : d → ℤ) :
    torusDirectionalFrequency β (m - n) = torusDirectionalFrequency β m - torusDirectionalFrequency β n := by
  simp only [torusDirectionalFrequency, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

/-- Shifting the sequence by a module frequency shifts the cutoff
threshold by the corresponding physical frequency. -/
theorem lpUpperFrequencyProjection_lpFrequencyShift {d : Type*} [Fintype d] (β : d → ℝ)
    (j : d → ℤ) (t : ℝ) (f : SeqL2(d → ℤ)) :
    let b := torusDirectionalFrequency β
    lpUpperFrequencyProjection b (t + b j) (lpFrequencyShift j f) =
      lpFrequencyShift j (lpUpperFrequencyProjection b t f) := by
  intro b
  ext i
  rw [lpUpperFrequencyProjection_apply, lpFrequencyShift_apply, lpFrequencyShift_apply,
    lpUpperFrequencyProjection_apply]
  have h : t + b j ≤ b i ↔ t ≤ b (i - j) := by
    change t + torusDirectionalFrequency β j ≤ torusDirectionalFrequency β i ↔
      t ≤ torusDirectionalFrequency β (i - j)
    rw [torusDirectionalFrequency_sub_for_shift]
    exact le_sub_iff_add_le.symm
  simp only [h]


/-- Expand an output coordinate of a bounded operator in the standard basis. -/
theorem hasSum_lpOperator_matrix_apply {ι : Type*} [DecidableEq ι]
    (A : SeqL2(ι) →L[ℂ] SeqL2(ι)) (f : SeqL2(ι)) (i : ι) :
    HasSum (fun j : ι => A (lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ)) i * f j) (A f i) := by
  classical
  let L := (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).comp A
  have h : HasSum (fun j : ι => A (lp.single 2 j (f j)) i) (A f i) :=
    L.hasSum (lp.hasSum_single (by norm_num) f)
  refine h.congr_fun fun j => ?_
  have hSingle : lp.single 2 j (f j) = (f j) • lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : ι => ℂ) 2 j (f j) (1 : ℂ))
  rw [hSingle, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- After any fixed bounded linear map, the coordinates of a moving
upper cutoff are Borel measurable in its threshold. -/
theorem measurable_lpOperator_upperFrequencyProjection_apply {ι : Type*} [Countable ι]
    (A : SeqL2(ι) →L[ℂ] SeqL2(ι)) (b : ι → ℝ) (f : SeqL2(ι)) (i : ι) :
    Measurable (fun t => A (lpUpperFrequencyProjection b t f) i) := by
  classical
  let a (j : ι) := A (lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ)) i
  have hEq : (fun t => A (lpUpperFrequencyProjection b t f) i) =
      fun t : ℝ => ∑' j : ι, a j * (if t ≤ b j then f j else 0) := by
    funext t
    rw [← (hasSum_lpOperator_matrix_apply A (lpUpperFrequencyProjection b t f) i).tsum_eq]
    apply tsum_congr
    intro j
    rw [lpUpperFrequencyProjection_apply]
  rw [hEq]
  apply Measurable.tsum
  intro j
  exact measurable_const.mul
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const)

section ConvolutionCovariance

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- Reindexing the absolutely convergent coordinate convolution gives
the Cayley operator's commutation with every module shift. -/
theorem torusPoissonCayleyConvolution_lpFrequencyShift (j : d → ℤ) (f : SeqL2(d → ℤ)) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    U (lpFrequencyShift j f) = lpFrequencyShift j (U f) := by
  intro U
  ext i
  rw [lpFrequencyShift_apply]
  let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let a := mFourierCoeff B
  have hR : HasSum (fun m => a (i - j - m) * f m) (U f (i - j)) :=
    hasSum_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance f (i - j)
  have hL : HasSum (fun m => a (i - m) * lpFrequencyShift j f m) (U (lpFrequencyShift j f) i) :=
    hasSum_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance (lpFrequencyShift j f) i
  have hL' : HasSum (fun m => a (i - j - m) * f m) (U (lpFrequencyShift j f) i) := by
    have h := (Equiv.addRight j).hasSum_iff.mpr hL
    refine h.congr_fun fun m => ?_
    change a (i - j - m) * f m = a (i - (m + j)) * lpFrequencyShift j f (m + j)
    rw [lpFrequencyShift_apply, add_sub_cancel_right, sub_sub, add_comm j m]
  exact hL'.unique hR


/-- The powers used in the multistep trace commute with module shifts. -/
theorem torusPoissonCayleyConvolution_pow_lpFrequencyShift (q : ℕ) (j : d → ℤ) (f : SeqL2(d → ℤ)) :
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    (U ^ q) (lpFrequencyShift j f) = lpFrequencyShift j ((U ^ q) f) := by
  intro U
  induction q with
  | zero => rw [pow_zero]; rfl
  | succ q ih =>
    rw [pow_succ', LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.trans_apply, ih]
    exact torusPoissonCayleyConvolution_lpFrequencyShift β S T hT hCont hCount hAdvance j ((U ^ q) f)

/-- The multistep cutoff defects intertwine physical threshold translation
with the corresponding shift of the coefficient sequence. -/
theorem torusPoissonCayleyCutoffDefect_lpFrequencyShift (q : ℕ) (j : d → ℤ) (t : ℝ)
    (f : SeqL2(d → ℤ)) :
    let L := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance
    L (t + torusDirectionalFrequency β j) q (lpFrequencyShift j f) =
      lpFrequencyShift j (L t q f) := by
  intro L
  let b := torusDirectionalFrequency β
  let P (s : ℝ) := lpUpperFrequencyProjection b s
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let V := U ^ q
  let W := lpFrequencyShift j
  have hP (v : SeqL2(d → ℤ)) : P (t + b j) (W v) = W (P t v) :=
    lpUpperFrequencyProjection_lpFrequencyShift β j t v
  have hUV (v : SeqL2(d → ℤ)) : V (W v) = W (V v) :=
    torusPoissonCayleyConvolution_pow_lpFrequencyShift β S T hT hCont hCount hAdvance q j v
  have hUSymm (v : SeqL2(d → ℤ)) : V.symm (W v) = W (V.symm v) := by
    apply V.injective
    rw [V.apply_symm_apply, hUV, V.apply_symm_apply]
  let C : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := V
  have hL (s : ℝ) (v : SeqL2(d → ℤ)) : L s q v = P s v - V (P s (V.symm v)) := by
    change (P s - C * P s * C.adjoint) v = _
    rw [V.adjoint_eq_symm]
    rfl
  rw [hL, hL, map_sub, hP, hUSymm, hP, hUV]

/-- The zero column of the covariant defect is the translated reversed-index
row of the same defect, as required for integrated trace symmetry. -/
theorem torusPoissonCayleyCutoffDefect_matrix_covariance (q : ℕ) (t : ℝ) (j : d → ℤ) :
    let L := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance
    let e (i : d → ℤ) := lp.single (E := fun _ : d → ℤ => ℂ) 2 i (1 : ℂ)
    L t q (e 0) j = L (t - torusDirectionalFrequency β j) q (e (-j)) 0 := by
  classical
  intro L e
  have hE : lpFrequencyShift j (e (-j)) = e 0 := by
    ext i
    rw [lpFrequencyShift_apply]
    by_cases hi : i = 0
    · subst i
      simp [e]
    · have hj : i - j ≠ -j := by
        intro he
        exact hi (by simpa [sub_add_cancel] using congrArg (· + j) he)
      simp only [e, lp.coeFn_single, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hi]
  have h := torusPoissonCayleyCutoffDefect_lpFrequencyShift β S T hT hCont hCount hAdvance q j
    (t - torusDirectionalFrequency β j) (e (-j))
  change L (t - torusDirectionalFrequency β j + torusDirectionalFrequency β j) q
    (lpFrequencyShift j (e (-j))) = lpFrequencyShift j (L (t - torusDirectionalFrequency β j) q (e (-j))) at h
  rw [sub_add_cancel, hE] at h
  have hp := congrArg (fun f : SeqL2(d → ℤ) => f j) h
  simpa only [lpFrequencyShift_apply, sub_self] using hp


/-- Every output coordinate of a multistep defect applied to a fixed
input is Borel measurable in the cutoff threshold. -/
theorem measurable_torusPoissonCayleyCutoffDefect_apply (q : ℕ) (e : SeqL2(d → ℤ)) (i : d → ℤ) :
    Measurable (fun t => torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q e i) := by
  classical
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := (U ^ q : _ ≃ₗᵢ[ℂ] _)
  let b := torusDirectionalFrequency β
  let P (t : ℝ) := lpUpperFrequencyProjection b t
  have hp : Measurable (fun t => P t e i) :=
    measurable_lpOperator_upperFrequencyProjection_apply
      (ContinuousLinearMap.id ℂ (SeqL2(d → ℤ))) b e i
  have hq : Measurable (fun t => V (P t (V.adjoint e)) i) :=
    measurable_lpOperator_upperFrequencyProjection_apply V b (V.adjoint e) i
  have h : Measurable (fun t : ℝ => P t e i - V (P t (V.adjoint e)) i) := hp.sub hq
  simpa only [torusPoissonCayleyCutoffDefect, V, U, P, b, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, sub_apply, lp.coeFn_sub, Pi.sub_apply] using h

end ConvolutionCovariance

end
end MeyerGeneralProblem
