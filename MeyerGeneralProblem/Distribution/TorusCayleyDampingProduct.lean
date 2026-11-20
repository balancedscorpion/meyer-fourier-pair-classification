module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCutoffCovariance

@[expose] public section

/-!
# Damping of Cayley products

On nonnegative physical frequencies, the exponential weight of a term
in the convolution is the product of the weights of its two factors.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

section BoundedMultiplication

variable {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ}
variable {u : Θ → ℂ} (hu : AEStronglyMeasurable u μ) (hBound : ∀ᵐ θ ∂μ, ‖u θ‖ ≤ 1)

include hu hBound in
private theorem memLp_bounded_mul (f : Lp ℂ 2 μ) :
    MemLp (fun θ => u θ * f θ) 2 μ :=
  (Lp.memLp f).mono (hu.mul (Lp.aestronglyMeasurable f)) (by
    filter_upwards [hBound] with θ hθ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ)

private def l2BoundedMul (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_bounded_mul hu hBound f).toLp _

private theorem coeFn_l2BoundedMul (f : Lp ℂ 2 μ) :
    l2BoundedMul hu hBound f =ᵐ[μ] fun θ => u θ * f θ := MemLp.coeFn_toLp _

/-- Multiplication by a measurable function bounded by one is a contraction on (L^2). -/
def l2BoundedMultiplier : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := l2BoundedMul hu hBound
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [coeFn_l2BoundedMul hu hBound (f + g), coeFn_l2BoundedMul hu hBound f,
          coeFn_l2BoundedMul hu hBound g, Lp.coeFn_add f g,
          Lp.coeFn_add (l2BoundedMul hu hBound f) (l2BoundedMul hu hBound g)]
          with θ h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1, h5, h2, h3, h4, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [coeFn_l2BoundedMul hu hBound (c • f), coeFn_l2BoundedMul hu hBound f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (l2BoundedMul hu hBound f)]
          with θ h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
        rw [RingHom.id_apply, h1, h4, h2, h3]
        ring }
  refine L.mkContinuous 1 fun f => ?_
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_l2BoundedMul hu hBound f, hBound] with θ h1 h2
  change ‖l2BoundedMul hu hBound f θ‖ ≤ ‖f θ‖
  rw [h1, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) h2

/-- The contraction acts by pointwise multiplication almost everywhere. -/
theorem coeFn_l2BoundedMultiplier (f : Lp ℂ 2 μ) :
    l2BoundedMultiplier hu hBound f =ᵐ[μ] fun θ => u θ * f θ :=
  coeFn_l2BoundedMul hu hBound f

end BoundedMultiplication

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyDampingCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

section TorusMultiplication

variable {d : Type*} [Fintype d]
variable (u : TorusL2(d)) (hBound : ∀ᵐ θ ∂volume, ‖u θ‖ ≤ 1)

/-- Fourier coordinates of multiplication by a bounded torus function. -/
def torusBoundedConvolution : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
  let e := (mFourierBasis (d := d)).repr.toContinuousLinearEquiv
  e.toContinuousLinearMap ∘L l2BoundedMultiplier (Lp.aestronglyMeasurable u) hBound ∘L
    e.symm.toContinuousLinearMap

/-- The Fourier-coordinate matrix is given by the differences of indices. -/
theorem torusBoundedConvolution_single (m n : d → ℤ) :
    torusBoundedConvolution u hBound (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)) n =
      mFourierCoeff u (n - m) := by
  change (mFourierBasis (d := d)).repr
    (l2BoundedMultiplier (Lp.aestronglyMeasurable u) hBound
      ((mFourierBasis (d := d)).repr.symm (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)))) n = _
  rw [HilbertBasis.repr_symm_single, coe_mFourierBasis, mFourierBasis_repr]
  simp only [mFourierCoeff, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [coeFn_l2BoundedMultiplier (Lp.aestronglyMeasurable u) hBound (mFourierLp 2 m),
    coeFn_mFourierLp 2 m] with θ h1 h2
  rw [h1, h2]
  calc
    mFourier (-n) θ * (u θ * mFourier m θ) =
        (mFourier (-n) θ * mFourier m θ) * u θ := by ring
    _ = mFourier (-(n - m)) θ * u θ := by
        rw [← mFourier_add, neg_sub, sub_eq_add_neg, add_comm m (-n)]

/-- The bounded multiplier acts by a convergent convolution at every coordinate. -/
theorem hasSum_torusBoundedConvolution (f : SeqL2(d → ℤ)) (n : d → ℤ) :
    HasSum (fun m : d → ℤ => mFourierCoeff u (n - m) * f m)
      (torusBoundedConvolution u hBound f n) := by
  classical
  simpa only [torusBoundedConvolution_single] using
    hasSum_lpOperator_matrix_apply (torusBoundedConvolution u hBound) f n

/-- Powers of the convolution represent pointwise powers of its symbol. -/
theorem ae_repr_symm_torusBoundedConvolution_pow (q : ℕ) (f : SeqL2(d → ℤ)) :
    let e := (mFourierBasis (d := d)).repr
    e.symm ((torusBoundedConvolution u hBound ^ q) f) =ᵐ[volume]
      fun θ => (u θ) ^ q * e.symm f θ := by
  intro e
  let C := torusBoundedConvolution u hBound
  let L := l2BoundedMultiplier (Lp.aestronglyMeasurable u) hBound
  have he (g : SeqL2(d → ℤ)) : e.symm (C g) = L (e.symm g) := by
    change e.symm (e (L (e.symm g))) = _
    exact e.symm_apply_apply _
  induction q with
  | zero =>
    simpa only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, one_mul] using
      (Filter.EventuallyEq.rfl : ⇑(e.symm f) =ᵐ[volume] ⇑(e.symm f))
  | succ q ih =>
    change e.symm ((C ^ (q + 1)) f) =ᵐ[volume] _
    rw [pow_succ']
    change e.symm (C ((C ^ q) f)) =ᵐ[volume] _
    rw [he]
    filter_upwards [coeFn_l2BoundedMultiplier (Lp.aestronglyMeasurable u) hBound
      (e.symm ((C ^ q) f)), ih] with θ h1 h2
    rw [h1, h2, pow_succ', mul_assoc]

end TorusMultiplication

section CayleyProducts

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- Upper-half-plane Cayley symbols are bounded by one in their Haar (L^2) representatives. -/
theorem ae_norm_torusPoissonCayleyL2_le_one (z : ℂ) :
    ∀ᵐ θ ∂volume, ‖torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z θ‖ ≤ 1 := by
  filter_upwards [coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z,
    ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
    with θ hθ hField
  rw [hθ]
  exact hField.2 z

/-- Exponential damping on torus frequencies with the absolute physical rate. -/
def torusDirectionalDamping (y : ℝ) : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
  lpExponentialDamping (fun n => 2 * Real.pi * |torusDirectionalFrequency β n|)
    (fun _ => mul_nonneg Real.two_pi_pos.le (abs_nonneg _)) y

theorem torusDirectionalDamping_apply (y : ℝ) (hy : 0 ≤ y) (f : SeqL2(d → ℤ)) (n : d → ℤ) :
    torusDirectionalDamping β y f n =
      (Real.exp (-(2 * Real.pi * |torusDirectionalFrequency β n|) * y) : ℂ) * f n := by
  rw [torusDirectionalDamping, lpExponentialDamping_apply, max_eq_left hy]

/-- On a nonnegative-frequency input, multiplying by the upper
Cayley symbol after damping is the same as damping the boundary product. -/
theorem torusDirectionalDamping_cayleyConvolution
    (y : ℝ) (hy : 0 < y) (f : SeqL2(d → ℤ))
    (hf : ∀ n : d → ℤ, torusDirectionalFrequency β n < 0 → f n = 0) :
    let u := torusPoissonCayleyL2 β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I)
    let Cy := torusBoundedConvolution u
      (ae_norm_torusPoissonCayleyL2_le_one β S T hT hCont hCount hAdvance _)
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    torusDirectionalDamping β y (U f) = Cy (torusDirectionalDamping β y f) := by
  intro u Cy U
  let b := torusDirectionalFrequency β
  let a := mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance)
  let D := torusDirectionalDamping β y
  ext n
  have hB := hasSum_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance f n
  have hU := hasSum_torusBoundedConvolution u
    (ae_norm_torusPoissonCayleyL2_le_one β S T hT hCont hCount hAdvance _) (D f) n
  let w (j : d → ℤ) := (Real.exp (-(2 * Real.pi * |b j|) * y) : ℂ)
  let v (j : d → ℤ) := (Real.exp (-(2 * Real.pi * b j * y)) : ℂ)
  have hCoeff (j : d → ℤ) : mFourierCoeff u j = v j * a j :=
    torusPoissonCayleyCoeff_at_height β S T hT hCont hCount hAdvance j y hy
  have hD (g : SeqL2(d → ℤ)) (j : d → ℤ) : D g j = w j * g j :=
    torusDirectionalDamping_apply β y hy.le g j
  have hTerm (m : d → ℤ) :
      w n * (a (n - m) * f m) = mFourierCoeff u (n - m) * D f m := by
    rw [hCoeff, hD]
    by_cases hm : b m < 0
    · rw [hf m hm]
      simp
    by_cases hnm : b (n - m) < 0
    · have hz : a (n - m) = 0 :=
        mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance _ hnm
      rw [hz]
      simp
    have hbn : b n = b (n - m) + b m := by
      simp only [b, torusDirectionalFrequency, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    have hnon : 0 ≤ b n := by rw [hbn]; exact add_nonneg (le_of_not_gt hnm) (le_of_not_gt hm)
    have hw : w n = v (n - m) * w m := by
      simp only [w, v, abs_of_nonneg hnon, abs_of_nonneg (le_of_not_gt hm), ← Complex.ofReal_mul,
        ← Real.exp_add]
      congr 2
      rw [hbn]
      ring
    rw [hw]
    ring
  change D (U f) n = Cy (D f) n
  rw [hD]
  have hLeft : HasSum (fun m => w n * (a (n - m) * f m)) (w n * U f n) := hB.mul_left _
  exact (hLeft.congr_fun fun m => (hTerm m).symm).unique hU

/-- Damped iterates of the boundary operator are the iterated upper-field products. -/
theorem ae_torusDirectionalDamping_cayleyConvolution_pow
    (y : ℝ) (hy : 0 < y) (q : ℕ) (f : SeqL2(d → ℤ))
    (hf : ∀ n : d → ℤ, torusDirectionalFrequency β n < 0 → f n = 0) :
    let e := (mFourierBasis (d := d)).repr
    let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
    let D := torusDirectionalDamping β y
    e.symm (D ((U ^ q) f)) =ᵐ[volume] fun θ =>
      (torusPoissonCayleyField β S T hT hCont hCount ((y : ℂ) * Complex.I) θ) ^ q *
        e.symm (D f) θ := by
  intro e U D
  let u := torusPoissonCayleyL2 β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I)
  let hU := ae_norm_torusPoissonCayleyL2_le_one β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I)
  let C := torusBoundedConvolution u hU
  let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) 0
  have hP : P f = f := by
    ext n
    by_cases hn : 0 ≤ torusDirectionalFrequency β n
    · simp [P, lpUpperFrequencyProjection_apply, hn]
    · simp [P, lpUpperFrequencyProjection_apply, hn, hf n (lt_of_not_ge hn)]
  have hP_pow (j : ℕ) : P ((U ^ j) f) = (U ^ j) f := by
    have h := lpUpperFrequencyProjection_torusPoissonCayleyConvolution_pow
      β S T hT hCont hCount hAdvance 0 j f
    change P ((U ^ j) (P f)) = (U ^ j) (P f) at h
    rwa [hP] at h
  have hSupp (j : ℕ) (n : d → ℤ) (hn : torusDirectionalFrequency β n < 0) : (U ^ j) f n = 0 := by
    have h := congrArg (fun v : SeqL2(d → ℤ) => v n) (hP_pow j)
    change lpUpperFrequencyProjection (torusDirectionalFrequency β) 0 ((U ^ j) f) n = _ at h
    simpa only [lpUpperFrequencyProjection_apply, ite_eq_right (not_le.mpr hn)] using h.symm
  have hPow (j : ℕ) : D ((U ^ j) f) = (C ^ j) (D f) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ' U, pow_succ' C, LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
      change D (U ((U ^ j) f)) = C ((C ^ j) (D f))
      rw [← ih]
      exact torusDirectionalDamping_cayleyConvolution β S T hT hCont hCount hAdvance
        y hy ((U ^ j) f) (hSupp j)
  rw [hPow]
  have h := ae_repr_symm_torusBoundedConvolution_pow u hU q (D f)
  filter_upwards [h, coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I)]
    with θ h1 h2
  change e.symm ((C ^ q) (D f)) θ = (u θ) ^ q * e.symm (D f) θ at h1
  change u θ = _ at h2
  rw [h1, h2]

/-- Fourier synthesis of the q-th Cayley finite difference equals multiplication
by the q-th power of the boundary symbol minus one. -/
theorem ae_repr_symm_torusCayleyFiniteDifference (q : ℕ) (f : SeqL2(d → ℤ)) :
    let e := (mFourierBasis (d := d)).repr
    let U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance : _ ≃ₗᵢ[ℂ] _)
    let u := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
    e.symm (((U - 1) ^ q) f) =ᵐ[volume] fun θ => (u θ - 1) ^ q * e.symm f θ := by
  intro e U u
  let hBound : ∀ᵐ θ ∂volume, ‖u θ‖ ≤ 1 :=
    (ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance).mono fun _ h => h.le
  have hU : U = torusBoundedConvolution u hBound := by
    apply ContinuousLinearMap.ext
    intro g
    ext n
    exact (hasSum_torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance g n).unique
      (hasSum_torusBoundedConvolution u hBound g n)
  have hProduct (g : SeqL2(d → ℤ)) :
      e.symm (U g) =ᵐ[volume] fun θ => u θ * e.symm g θ := by
    rw [hU]
    have h := ae_repr_symm_torusBoundedConvolution_pow u hBound 1 g
    simpa only [pow_one] using h
  have hDiff (g : SeqL2(d → ℤ)) :
      e.symm ((U - 1) g) =ᵐ[volume] fun θ => (u θ - 1) * e.symm g θ := by
    change e.symm (U g - g) =ᵐ[volume] _
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (e.symm (U g)) (e.symm g), hProduct g] with θ h1 h2
    simp only [Pi.sub_apply] at h1
    rw [h1, h2, sub_mul, one_mul]
  induction q with
  | zero =>
    simpa only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, one_mul] using
      (Filter.EventuallyEq.rfl : ⇑(e.symm f) =ᵐ[volume] ⇑(e.symm f))
  | succ q ih =>
    rw [pow_succ']
    change e.symm ((U - 1) (((U - 1) ^ q) f)) =ᵐ[volume] _
    filter_upwards [hDiff (((U - 1) ^ q) f), ih] with θ h1 h2
    rw [h1, h2, pow_succ', mul_assoc]

end CayleyProducts
end
end MeyerGeneralProblem
