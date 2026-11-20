module

public import MeyerGeneralProblem.Distribution.TorusSchwartzOrbitConvolution
public import MeyerGeneralProblem.Distribution.BroadCauchySupportJets
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-!
# Bounded sampling along the real phase flow

A Schwartz time kernel regularizes a Haar square-integrable input on each
real orbit. Uniform Schwartz bounds on a weakly continuous distribution
family control the resulting pairing. A frequency cutoff recovers the
actual real orbit representative on a bounded band.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff ENNReal FourierTransform SchwartzMap Topology

/-- A quadratic derivative envelope for a smooth multiplier gives an
explicit bound on the seminorm of its product with a fixed Schwartz test. -/
private theorem schwartz_seminorm_smulLeftCLM_le_of_quadratic_derivatives
    (g : SchwartzMap ℝ ℂ) (k n : ℕ) (h : ℝ → ℂ) (hg : h.HasTemperateGrowth)
    (M : ℝ) (hM : 0 ≤ M)
    (hDeriv : ∀ j ≤ n, ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ M * (1 + x ^ 2)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ h g) ≤
      M * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (SchwartzMap.seminorm ℂ k (n - j) g + SchwartzMap.seminorm ℂ (k + 2) (n - j) g) := by
  let S := Finset.range (n + 1)
  let C (j : ℕ) := (n.choose j : ℝ) *
    (SchwartzMap.seminorm ℂ k (n - j) g + SchwartzMap.seminorm ℂ (k + 2) (n - j) g)
  have hC (j : ℕ) : 0 ≤ C j := by dsimp [C]; positivity
  change _ ≤ M * ∑ j ∈ S, C j
  refine SchwartzMap.seminorm_le_bound' ℂ k n _ (mul_nonneg hM (Finset.sum_nonneg fun j _ => hC j)) ?_
  intro x
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simp only [smul_eq_mul]
  rw [iteratedDeriv_fun_mul
    (hg.1.of_le (by simp)).contDiffAt
    (g.smooth n).contDiffAt]
  let D (j : ℕ) : ℂ := (n.choose j : ℂ) * iteratedDeriv j h x * iteratedDeriv (n - j) g x
  change |x| ^ k * ‖∑ j ∈ S, D j‖ ≤ M * ∑ j ∈ S, C j
  calc
    _ ≤ |x| ^ k * ∑ j ∈ S, ‖D j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ S, |x| ^ k * ‖D j‖ := Finset.mul_sum _ _ _
    _ ≤ M * ∑ j ∈ S, C j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hW :
          |x| ^ k * (1 + x ^ 2) * ‖iteratedDeriv (n - j) g x‖ ≤
            SchwartzMap.seminorm ℂ k (n - j) g + SchwartzMap.seminorm ℂ (k + 2) (n - j) g := by
        rw [← sq_abs x]
        rw [show |x| ^ k * (1 + |x| ^ 2) * ‖iteratedDeriv (n - j) g x‖ =
          |x| ^ k * ‖iteratedDeriv (n - j) g x‖ +
            (|x| ^ k * |x| ^ 2) * ‖iteratedDeriv (n - j) g x‖ by ring]
        exact add_le_add (SchwartzMap.le_seminorm' ℂ k (n - j) g x)
          (by simpa only [pow_add] using SchwartzMap.le_seminorm' ℂ (k + 2) (n - j) g x)
      simp only [D, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ |x| ^ k * ((n.choose j : ℝ) * (M * (1 + x ^ 2)) *
              ‖iteratedDeriv (n - j) g x‖) := by
          gcongr
          exact hDeriv j hjn x
        _ = (M * (n.choose j : ℝ)) *
              (|x| ^ k * (1 + x ^ 2) * ‖iteratedDeriv (n - j) g x‖) := by ring
        _ ≤ M * C j := by
          rw [show M * C j = _ from (mul_assoc _ _ _).symm]
          exact mul_le_mul_of_nonneg_left hW (by positivity)

/-- A common rectangular seminorm bound controls pairing after convolution
by the weighted absolute integral of the original orbit data. -/
theorem exists_norm_schwartzConvolution_pairing_le
    (k g : SchwartzMap ℝ ℂ) (weight order : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : TemperedDistribution ℝ ℂ) (D : ℝ), 0 ≤ D →
      (∀ f : SchwartzMap ℝ ℂ,
        ‖T f‖ ≤ D * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) →
      ∀ (F : ℝ → ℂ), Measurable F →
      (∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2)⁻¹) * ENNReal.ofReal (‖F t‖ ^ 2)) < ⊤ →
      let h (x : ℝ) := ∫ t : ℝ, k (x - t) * F t
      ‖T (SchwartzMap.smulLeftCLM ℂ h g)‖ ≤
        (D * C) * ∫ t : ℝ, (1 + t ^ 2)⁻¹ * ‖F t‖ := by
  let I : Finset (ℕ × ℕ) := Finset.Iic (weight, order)
  let A (j : ℕ) := 2 * (SchwartzMap.seminorm ℂ 0 j k + SchwartzMap.seminorm ℂ 2 j k)
  let B (i : ℕ × ℕ) := ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) *
    (SchwartzMap.seminorm ℂ i.1 (i.2 - j) g + SchwartzMap.seminorm ℂ (i.1 + 2) (i.2 - j) g)
  let C₁ := ∑ j ∈ Finset.range (order + 1), A j
  let C₂ := ∑ i ∈ I, B i
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  have hB (i : ℕ × ℕ) : 0 ≤ B i := by dsimp [B]; positivity
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg fun j _ => hA j
  have hC₂ : 0 ≤ C₂ := Finset.sum_nonneg fun i _ => hB i
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro T D hD hT F hF hSq h
  let L := ∫ t : ℝ, (1 + t ^ 2)⁻¹ * ‖F t‖
  have hL : 0 ≤ L := integral_nonneg (fun t => by positivity)
  have hM : 0 ≤ C₁ * L := mul_nonneg hC₁ hL
  have hEst := schwartz_convolution_estimates_of_weighted_sq k F hF hSq
  have hDeriv (j : ℕ) (hj : j ≤ order) (x : ℝ) :
      ‖iteratedDeriv j h x‖ ≤ (C₁ * L) * (1 + x ^ 2) := by
    have hle : A j ≤ C₁ := Finset.single_le_sum (fun j _ => hA j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact (hEst.2.2 j x).trans (by gcongr)
  have hSup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (SchwartzMap.smulLeftCLM ℂ h g) ≤
      (C₁ * L) * C₂ := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hM hC₂) (fun i hi => ?_)
    have hiOrder : i.2 ≤ order := (Finset.mem_Iic.mp hi).2
    exact (schwartz_seminorm_smulLeftCLM_le_of_quadratic_derivatives g i.1 i.2 h hEst.1
      (C₁ * L) hM (fun j hj => hDeriv j (hj.trans hiOrder))).trans
      (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hB i) hi) hM)
  calc
    _ ≤ D * ((I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (SchwartzMap.smulLeftCLM ℂ h g)) := hT _
    _ ≤ D * ((C₁ * L) * C₂) := mul_le_mul_of_nonneg_left hSup hD
    _ = _ := by change _ = (D * (C₁ * C₂)) * L; ring

/-- Use normalized Haar measure on each circle factor. -/
local instance orbitSamplingCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance orbitSamplingCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private def orbitWeight (t : ℝ) : ℝ := (1 + t ^ 2)⁻¹

private theorem orbitWeight_nonneg (t : ℝ) : 0 ≤ orbitWeight t := by
  unfold orbitWeight
  positivity

private theorem measurable_orbitWeight : Measurable orbitWeight :=
  (measurable_const.add (measurable_id.pow_const 2)).inv

private theorem lintegral_orbitWeight_lt_top :
    (∫⁻ t, ENNReal.ofReal (orbitWeight t)) < ⊤ := by
  have h := integrable_inv_one_add_sq.hasFiniteIntegral
  change HasFiniteIntegral orbitWeight volume at h
  rw [hasFiniteIntegral_iff_norm] at h
  simpa only [Real.norm_of_nonneg (orbitWeight_nonneg _)] using h

private theorem ofReal_weighted_integral_norm_sq_le
    (F : ℝ → ℂ) (hF : Measurable F)
    (hSq : (∫⁻ t : ℝ, ENNReal.ofReal (orbitWeight t) * ENNReal.ofReal (‖F t‖ ^ 2)) < ⊤) :
    ENNReal.ofReal ((∫ t : ℝ, orbitWeight t * ‖F t‖) ^ 2) ≤
      (∫⁻ t, ENNReal.ofReal (orbitWeight t)) *
        ∫⁻ t, ENNReal.ofReal (orbitWeight t) * ENNReal.ofReal (‖F t‖ ^ 2) := by
  let a (t : ℝ) := ENNReal.ofReal (orbitWeight t)
  let b (t : ℝ) := ENNReal.ofReal ‖F t‖
  have ha : Measurable a := ENNReal.measurable_ofReal.comp measurable_orbitWeight
  have hb : Measurable b := ENNReal.measurable_ofReal.comp hF.norm
  have hPos (t : ℝ) : 0 ≤ orbitWeight t * ‖F t‖ :=
    mul_nonneg (orbitWeight_nonneg t) (norm_nonneg _)
  have hInt : Integrable (fun t : ℝ => orbitWeight t * ‖F t‖) := by
    have hi := integrable_mul_of_le_inverse_quadratic_weight F (fun t => (orbitWeight t : ℂ))
      hF (Complex.continuous_ofReal.measurable.comp measurable_orbitWeight) 1 hSq (fun t => by
        rw [Complex.norm_real, Real.norm_of_nonneg (orbitWeight_nonneg t), one_mul]
        rfl)
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (orbitWeight_nonneg _)] using hi.norm
  have hIntNonneg : 0 ≤ ∫ t : ℝ, orbitWeight t * ‖F t‖ := integral_nonneg hPos
  rw [ENNReal.ofReal_pow hIntNonneg,
    ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hPos)]
  simp_rw [ENNReal.ofReal_mul (orbitWeight_nonneg _), ENNReal.ofReal_pow (norm_nonneg _) 2]
  change (∫⁻ t, a t * b t) ^ 2 ≤ (∫⁻ t, a t) * ∫⁻ t, a t * b t ^ 2
  have hSquare (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = z := by
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  have hSplit (t : ℝ) : a t ^ (1 / 2 : ℝ) * (a t * b t ^ 2) ^ (1 / 2 : ℝ) = a t * b t := by
    apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
    simp only [ENNReal.rpow_two, mul_pow]
    rw [hSquare (a t), hSquare (a t * b t ^ 2)]
    ring
  have hHolder := ENNReal.lintegral_mul_norm_pow_le (μ := (volume : Measure ℝ))
    ha.aemeasurable (ha.mul (hb.pow_const 2)).aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  change (∫⁻ t, a t ^ (1 / 2 : ℝ) * (a t * b t ^ 2) ^ (1 / 2 : ℝ)) ≤
    (∫⁻ t, a t) ^ (1 / 2 : ℝ) * (∫⁻ t, a t * b t ^ 2) ^ (1 / 2 : ℝ) at hHolder
  simp_rw [hSplit] at hHolder
  exact (pow_le_pow_left' hHolder 2).trans_eq (by rw [mul_pow, hSquare, hSquare])

private def torusOrbitWeightedNorm {d : Type*} [Fintype d] (β : d → ℝ)
    (F : UnitAddTorus d → ℂ) (θ : UnitAddTorus d) : ℝ :=
  ∫ t : ℝ, orbitWeight t * ‖F (unitAddTorusFlow β t θ)‖

private theorem torusOrbitWeightedNorm_nonneg {d : Type*} [Fintype d] (β : d → ℝ)
    (F : UnitAddTorus d → ℂ) (θ : UnitAddTorus d) :
    0 ≤ torusOrbitWeightedNorm β F θ :=
  integral_nonneg (fun t => mul_nonneg (orbitWeight_nonneg t) (norm_nonneg _))

private theorem measurable_torusOrbitWeightedNorm {d : Type*} [Fintype d] (β : d → ℝ)
    {F : UnitAddTorus d → ℂ} (hF : Measurable F) : Measurable (torusOrbitWeightedNorm β F) := by
  have h : Measurable (fun p : UnitAddTorus d × ℝ =>
      orbitWeight p.2 * ‖F (unitAddTorusFlow β p.2 p.1)‖) :=
    (measurable_orbitWeight.comp measurable_snd).mul
      (hF.norm.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The weighted absolute orbit integral has L² norm at most the weight
mass times the Haar L² norm of the input. -/
private theorem eLpNorm_torusOrbitWeightedNorm_le {d : Type*} [Fintype d] (β : d → ℝ)
    (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hLp : MemLp F 2 volume) :
    eLpNorm (torusOrbitWeightedNorm β F) 2 volume ≤
      (∫⁻ t, ENNReal.ofReal (orbitWeight t)) * eLpNorm F 2 volume := by
  let w (t : ℝ) := ENNReal.ofReal (orbitWeight t)
  let C := ∫⁻ t, w t
  let B (θ : UnitAddTorus d) := torusOrbitWeightedNorm β F θ
  have hw : Measurable w := ENNReal.measurable_ofReal.comp measurable_orbitWeight
  have hB (θ) : 0 ≤ B θ := torusOrbitWeightedNorm_nonneg β F θ
  have hAE : ∀ᵐ θ, ENNReal.ofReal (B θ ^ 2) ≤
      C * ∫⁻ t : ℝ, w t * ENNReal.ofReal (‖F (unitAddTorusFlow β t θ)‖ ^ 2) := by
    filter_upwards [ae_torusOrbit_weighted_norm_sq_lt_top β F hF hLp] with θ hθ
    exact ofReal_weighted_integral_norm_sq_le (fun t => F (unitAddTorusFlow β t θ))
      (hF.comp ((continuous_unitAddTorusFlow β).measurable.comp (measurable_id.prodMk measurable_const))) hθ
  have hM : Measurable (fun p : UnitAddTorus d × ℝ =>
      w p.2 * ENNReal.ofReal (‖F (unitAddTorusFlow β p.2 p.1)‖ ^ 2)) :=
    (hw.comp measurable_snd).mul ((ENNReal.measurable_ofReal.comp (hF.norm.pow_const 2)).comp
      ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  have hInt : (∫⁻ θ, ENNReal.ofReal (B θ ^ 2)) ≤
      C ^ 2 * ∫⁻ θ, ENNReal.ofReal (‖F θ‖ ^ 2) := by
    apply (lintegral_mono_ae hAE).trans_eq
    rw [lintegral_const_mul C hM.lintegral_prod_right', lintegral_weighted_torusOrbit_norm_sq β F hF w hw]
    change C * (C * _) = C ^ 2 * _
    rw [pow_two, mul_assoc]
  change eLpNorm B 2 volume ≤ C * eLpNorm F 2 volume
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := B) (by norm_num) (by norm_num)
    (measurable_torusOrbitWeightedNorm β hF).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  simp_rw [Real.enorm_eq_ofReal (hB _), ← ofReal_norm, ← ENNReal.ofReal_pow (hB _) 2,
    ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  have hPower := ENNReal.rpow_le_rpow hInt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast_mul, show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num,
    ENNReal.rpow_one] using hPower

section

variable {d : Type*} [Fintype d]

/-- Convolve the real orbit with the Schwartz kernel at each phase. -/
def torusSchwartzOrbitConvolution (β : d → ℝ) (k : SchwartzMap ℝ ℂ)
    (F : UnitAddTorus d → ℂ) (θ : UnitAddTorus d) (x : ℝ) : ℂ :=
  ∫ t : ℝ, k (x - t) * F (unitAddTorusFlow β t θ)

/-- Pair an original hull leaf with the convolved orbit times a Schwartz test. -/
def torusSchwartzOrbitPairing (β : d → ℝ) (k g : SchwartzMap ℝ ℂ)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ) (F : UnitAddTorus d → ℂ)
    (θ : UnitAddTorus d) : ℂ :=
  T θ (SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k F θ) g)

private theorem measurable_orbit (β : d → ℝ) (θ : UnitAddTorus d)
    {F : UnitAddTorus d → ℂ} (hF : Measurable F) :
    Measurable (fun t : ℝ => F (unitAddTorusFlow β t θ)) :=
  hF.comp ((continuous_unitAddTorusFlow β).measurable.comp (measurable_id.prodMk measurable_const))

private theorem integrable_translate_schwartz_mul_of_weighted_sq
    (k : SchwartzMap ℝ ℂ) (x : ℝ) (F : ℝ → ℂ) (hF : Measurable F)
    (hSq : (∫⁻ t : ℝ, ENNReal.ofReal (orbitWeight t) *
      ENNReal.ofReal (‖F t‖ ^ 2)) < ⊤) :
    Integrable (fun t : ℝ => k (x - t) * F t) := by
  let J := combSchwartzTranslation x k
  refine integrable_mul_of_le_inverse_quadratic_weight F (fun t => J (-t)) hF
    (J.continuous.comp continuous_neg).measurable
    (SchwartzMap.seminorm ℂ 0 0 J + SchwartzMap.seminorm ℂ 2 0 J) hSq ?_
  intro t
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h₀ := SchwartzMap.norm_le_seminorm ℂ J (-t)
  have h₂ := SchwartzMap.le_seminorm' ℂ 2 0 J (-t)
  simp only [iteratedDeriv_zero, abs_neg, sq_abs] at h₂
  rw [mul_add, mul_one, mul_comm ‖J (-t)‖]
  exact add_le_add h₀ h₂

private theorem ae_torusSchwartzOrbitPairing_sub
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (F G : UnitAddTorus d → ℂ) (hF : Measurable F) (hG : Measurable G)
    (hFLp : MemLp F 2 volume) (hGLp : MemLp G 2 volume) :
    torusSchwartzOrbitPairing β k g T (F - G) =ᵐ[volume]
      torusSchwartzOrbitPairing β k g T F - torusSchwartzOrbitPairing β k g T G := by
  filter_upwards [ae_torusOrbit_weighted_norm_sq_lt_top β F hF hFLp,
    ae_torusOrbit_weighted_norm_sq_lt_top β G hG hGLp,
    ae_torusOrbit_weighted_norm_sq_lt_top β (F - G) (hF.sub hG) (hFLp.sub hGLp)]
    with θ hθF hθG hθFG
  have hMa := measurable_orbit β θ hF
  have hMb := measurable_orbit β θ hG
  have hMc := measurable_orbit β θ (hF.sub hG)
  have hA := (schwartz_convolution_estimates_of_weighted_sq k _ hMa hθF).1
  have hB := (schwartz_convolution_estimates_of_weighted_sq k _ hMb hθG).1
  have hC := (schwartz_convolution_estimates_of_weighted_sq k _ hMc hθFG).1
  have hConv (x : ℝ) : torusSchwartzOrbitConvolution β k (F - G) θ x =
      torusSchwartzOrbitConvolution β k F θ x - torusSchwartzOrbitConvolution β k G θ x := by
    simp only [torusSchwartzOrbitConvolution, Pi.sub_apply, mul_sub]
    exact integral_sub (integrable_translate_schwartz_mul_of_weighted_sq k x _ hMa hθF)
      (integrable_translate_schwartz_mul_of_weighted_sq k x _ hMb hθG)
  change (torusSchwartzOrbitConvolution β k F θ).HasTemperateGrowth at hA
  change (torusSchwartzOrbitConvolution β k G θ).HasTemperateGrowth at hB
  change (torusSchwartzOrbitConvolution β k (F - G) θ).HasTemperateGrowth at hC
  have hTest : SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k (F - G) θ) g =
      SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k F θ) g -
      SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k G θ) g := by
    ext x
    simp only [sub_apply, SchwartzMap.smulLeftCLM_apply_apply hA,
      SchwartzMap.smulLeftCLM_apply_apply hB, SchwartzMap.smulLeftCLM_apply_apply hC, hConv, sub_smul]
  change T θ _ = T θ _ - T θ _
  rw [hTest, map_sub]

/-- The convolution eigenvalue of a torus character along the real flow. -/
def torusSchwartzKernelMultiplier (β : d → ℝ) (k : SchwartzMap ℝ ℂ) (n : d → ℤ) : ℂ :=
  ∫ t : ℝ, k (-t) * combModulationCharacter (torusDirectionalFrequency β n) t

/-- A finite Fourier polynomial pairs with the hull by its finite
Schwartz sum of modulated tests. -/
theorem torusSchwartzOrbitPairing_finite_sum
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (s : Finset (d → ℤ)) (a : (d → ℤ) → ℂ) (θ : UnitAddTorus d) :
    torusSchwartzOrbitPairing β k g T (fun φ => ∑ n ∈ s, a n * mFourier n φ) θ =
      ∑ n ∈ s, (a n * mFourier n θ * torusSchwartzKernelMultiplier β k n) *
        T θ (combSchwartzModulation (torusDirectionalFrequency β n) g) := by
  let P (φ : UnitAddTorus d) := ∑ n ∈ s, a n * mFourier n φ
  let K := ∑ n ∈ s, ‖a n‖
  have hUnit (n : d → ℤ) (φ : UnitAddTorus d) : ‖mFourier n φ‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  have hP : Continuous P :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous
  have hBound (φ : UnitAddTorus d) : ‖P φ‖ ≤ K := by
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, hUnit, mul_one, K])
  have hSq : (∫⁻ t : ℝ, ENNReal.ofReal (orbitWeight t) *
      ENNReal.ofReal (‖P (unitAddTorusFlow β t θ)‖ ^ 2)) < ⊤ := by
    calc
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (orbitWeight t) * ENNReal.ofReal (K ^ 2) := by
        apply lintegral_mono
        intro t
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (hBound _) 2))
      _ < ⊤ := by
        rw [lintegral_mul_const (f := fun t : ℝ => ENNReal.ofReal (orbitWeight t)) _
          (ENNReal.measurable_ofReal.comp measurable_orbitWeight)]
        exact ENNReal.mul_lt_top lintegral_orbitWeight_lt_top ENNReal.ofReal_lt_top
  have hGrowth : (torusSchwartzOrbitConvolution β k P θ).HasTemperateGrowth :=
    (schwartz_convolution_estimates_of_weighted_sq k _ (measurable_orbit β θ hP.measurable) hSq).1
  have hTerm (n : d → ℤ) (x : ℝ) :
      (∫ t : ℝ, k (x - t) * (a n * mFourier n (unitAddTorusFlow β t θ))) =
        (a n * mFourier n θ * torusSchwartzKernelMultiplier β k n) *
          combModulationCharacter (torusDirectionalFrequency β n) x := by
    let H (t : ℝ) := k (x - t) * (a n * mFourier n (unitAddTorusFlow β t θ))
    rw [show (∫ t, H t) = ∫ t, H (t + x) from (integral_add_right_eq_self H x).symm]
    have hChar (b t x : ℝ) :
        combModulationCharacter b (t + x) = combModulationCharacter b t * combModulationCharacter b x := by
      simp only [combModulationCharacter, mul_add, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
    have hH (t : ℝ) : H (t + x) = (a n * mFourier n θ *
        combModulationCharacter (torusDirectionalFrequency β n) x) *
        (k (-t) * combModulationCharacter (torusDirectionalFrequency β n) t) := by
      simp only [H, mFourier_unitAddTorusFlow, hChar, show x - (t + x) = -t by abel]
      ring
    simp_rw [hH, integral_const_mul]
    unfold torusSchwartzKernelMultiplier
    ring
  have hTest :
      SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k P θ) g =
      ∑ n ∈ s, (a n * mFourier n θ * torusSchwartzKernelMultiplier β k n) •
        combSchwartzModulation (torusDirectionalFrequency β n) g := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hGrowth]
    have hInt (n : d → ℤ) :
        Integrable (fun t => k (x - t) * (a n * mFourier n (unitAddTorusFlow β t θ))) := by
      let J := combSchwartzTranslation x k
      apply (J.integrable.comp_neg.norm.const_mul ‖a n‖).mono'
      · exact ((k.continuous.comp (continuous_const.sub continuous_id)).mul
          (continuous_const.mul ((mFourier n).continuous.comp
            ((continuous_unitAddTorusFlow β).comp (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
      · filter_upwards with t
        simp only [norm_mul, hUnit, mul_one, J, combSchwartzTranslation_apply, ← sub_eq_add_neg, mul_comm]
        exact le_rfl
    simp only [torusSchwartzOrbitConvolution, P, Finset.mul_sum, smul_eq_mul,
      sum_apply, smul_apply, combSchwartzModulation_apply]
    rw [integral_finsetSum _ (fun n _ => hInt n), Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [hTerm]; ring
  change T θ _ = _
  rw [hTest, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- On any weakly continuous family of tempered distributions with a
uniform rectangular Schwartz bound, the actual orbit convolution pairing
is measurable and bounded in Haar L². -/
theorem memLp_torusSchwartzOrbitPairing_of_schwartzSeminorm_bound
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (weight order : ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (T : UnitAddTorus d → TemperedDistribution ℝ ℂ),
      (∀ f : SchwartzMap ℝ ℂ, Continuous (fun θ => T θ f)) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ᵐ θ ∂volume, ∀ f : SchwartzMap ℝ ℂ, ‖T θ f‖ ≤
        D * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) →
      ∀ (F : UnitAddTorus d → ℂ), Measurable F → MemLp F 2 volume →
      MemLp (torusSchwartzOrbitPairing β k g T F) 2 volume ∧
        eLpNorm (torusSchwartzOrbitPairing β k g T F) 2 volume ≤
          (ENNReal.ofReal D * C) * eLpNorm F 2 volume := by
  classical
  obtain ⟨A, hA, hEstimate⟩ := exists_norm_schwartzConvolution_pairing_le k g weight order
  let M := ∫⁻ t : ℝ, ENNReal.ofReal (orbitWeight t)
  have hM : M < ⊤ := lintegral_orbitWeight_lt_top
  let C := ENNReal.ofReal A * M
  have hC : C < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM
  refine ⟨C, hC, ?_⟩
  intro T hCont D hD hT F hF hFLp
  let S := torusSchwartzOrbitPairing β k g T
  have hDA := mul_nonneg hD hA
  have hPointwise (Z : UnitAddTorus d → ℂ) (hZ : Measurable Z) (hZLp : MemLp Z 2 volume) :
      ∀ᵐ θ ∂volume, ‖S Z θ‖ ≤ (D * A) * torusOrbitWeightedNorm β Z θ := by
    filter_upwards [hT, ae_torusOrbit_weighted_norm_sq_lt_top β Z hZ hZLp] with θ hθT hθZ
    exact hEstimate (T θ) D hD hθT _ (measurable_orbit β θ hZ) hθZ
  let f := hFLp.toLp F
  have hFRep : F =ᵐ[volume] f := (MemLp.coeFn_toLp hFLp).symm
  let a := mFourierCoeff f
  let P (s : Finset (d → ℤ)) (θ : UnitAddTorus d) := ∑ n ∈ s, a n * mFourier n θ
  let p (s : Finset (d → ℤ)) : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
    ∑ n ∈ s, a n • mFourierLp 2 n
  have hP (s : Finset (d → ℤ)) : Continuous (P s) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous
  have hp (s : Finset (d → ℤ)) : P s =ᵐ[volume] p s := by
    have he (n : d → ℤ) : (fun θ => a n * mFourier n θ) =ᵐ[volume]
        (a n • mFourierLp 2 n : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :=
      ((Lp.coeFn_smul (a n) (mFourierLp 2 n)).trans
        ((coeFn_mFourierLp 2 n).fun_comp (fun z => a n * z))).symm
    have hPSum : P s = ∑ n ∈ s, fun θ => a n * mFourier n θ := by
      funext θ
      simp only [P, Finset.sum_apply]
    rw [hPSum]
    exact (eventuallyEq_sum fun n (_ : n ∈ s) => he n).trans (Lp.coeFn_finsetSum s _).symm
  have hPLp (s : Finset (d → ℤ)) : MemLp (P s) 2 volume :=
    (memLp_congr_ae (hp s)).mpr (Lp.memLp (p s))
  have hSC (s : Finset (d → ℤ)) : Continuous (S (P s)) := by
    rw [show S (P s) = fun θ => ∑ n ∈ s,
      (a n * mFourier n θ * torusSchwartzKernelMultiplier β k n) *
        T θ (combSchwartzModulation (torusDirectionalFrequency β n) g)
      from funext (torusSchwartzOrbitPairing_finite_sum β k g T s a)]
    exact continuous_finsetSum _ fun n _ =>
      ((continuous_const.mul (mFourier n).continuous).mul continuous_const).mul (hCont _)
  let G (s : Finset (d → ℤ)) := P s - F
  have hG (s : Finset (d → ℤ)) : Measurable (G s) := (hP s).measurable.sub hF
  have hGLp (s : Finset (d → ℤ)) : MemLp (G s) 2 volume := (hPLp s).sub hFLp
  have hELp : Tendsto (fun s => eLpNorm (G s) 2 volume) atTop (𝓝 0) := by
    have hTendsto : Tendsto p atTop (𝓝 f) := hasSum_mFourier_series_L2 f
    have he : (fun s => eLpNorm (G s) 2 volume) =
        (fun s => eLpNorm (⇑(p s) - ⇑f) 2 volume) :=
      funext fun s => eLpNorm_congr_ae ((hp s).sub hFRep)
    rw [he]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' p f).mp hTendsto
  let Q (s : Finset (d → ℤ)) := torusOrbitWeightedNorm β (G s)
  have hQ (s : Finset (d → ℤ)) : Measurable (Q s) := measurable_torusOrbitWeightedNorm β (hG s)
  have hQLim : Tendsto (fun s => eLpNorm (Q s) 2 volume) atTop (𝓝 0) := by
    have hUpper : Tendsto (fun s => M * eLpNorm (G s) 2 volume) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using
        ((ENNReal.continuous_const_mul hM.ne).continuousAt.tendsto.comp hELp)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun _ => zero_le) (fun s => eLpNorm_torusOrbitWeightedNorm_le β (G s) (hG s) (hGLp s))
  have hQM : TendstoInMeasure volume Q atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    simpa only [← Pi.zero_def, sub_zero] using hQLim
  obtain ⟨u, _, hq⟩ := hQM.exists_seq_tendsto_ae'
  have hErr (s : Finset (d → ℤ)) : ∀ᵐ θ ∂volume,
      ‖S (P s) θ - S F θ‖ ≤ (D * A) * Q s θ := by
    filter_upwards [hPointwise (G s) (hG s) (hGLp s),
      ae_torusSchwartzOrbitPairing_sub β k g T (P s) F (hP s).measurable hF (hPLp s) hFLp]
      with θ hθB hθS
    change S (G s) θ = S (P s) θ - S F θ at hθS
    rwa [hθS] at hθB
  have hSae : ∀ᵐ θ ∂volume, Tendsto (fun i : ℕ => S (P (u i)) θ) atTop (𝓝 (S F θ)) := by
    filter_upwards [hq, ae_all_iff.2 (fun i : ℕ => hErr (u i))] with θ hθq hθe
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_eq_norm]
    apply squeeze_zero (fun _ => norm_nonneg _) hθe
    simpa only [mul_zero] using hθq.const_mul (D * A)
  have hSM : AEStronglyMeasurable (S F) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun i => (hSC (u i)).aestronglyMeasurable) hSae
  have hNorm : eLpNorm (S F) 2 volume ≤ (ENNReal.ofReal D * C) * eLpNorm F 2 volume := by
    calc
      _ ≤ eLpNorm ((D * A) • torusOrbitWeightedNorm β F) 2 volume :=
        eLpNorm_mono_ae_real hSM (hPointwise F hF hFLp)
      _ = ENNReal.ofReal (D * A) * eLpNorm (torusOrbitWeightedNorm β F) 2 volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hDA]
      _ ≤ ENNReal.ofReal (D * A) * (M * eLpNorm F 2 volume) :=
        mul_le_mul' le_rfl (eLpNorm_torusOrbitWeightedNorm_le β F hF hFLp)
      _ = _ := by rw [ENNReal.ofReal_mul hD]; simp only [C, mul_assoc]
  exact ⟨hNorm.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC) hFLp), hNorm⟩

/-- If the kernel fixes every active frequency, convolution recovers the
real orbit almost everywhere along almost every phase. -/
theorem ae_torusSchwartzOrbitConvolution_eq_of_multiplier_one
    (β : d → ℝ) (k : SchwartzMap ℝ ℂ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hRep : F =ᵐ[volume] f)
    (hPass : ∀ n : d → ℤ, mFourierCoeff f n ≠ 0 → torusSchwartzKernelMultiplier β k n = 1) :
    ∀ᵐ θ ∂volume, torusSchwartzOrbitConvolution β k F θ =ᵐ[volume]
      fun x : ℝ => F (unitAddTorusFlow β x θ) := by
  let K (t : ℝ) := k (-t)
  let A := torusOrbitAverage β K F
  have hKm : Measurable K := (k.continuous.comp continuous_neg).measurable
  have hKi : Integrable K := k.integrable.comp_neg
  have hAm : Measurable A := measurable_torusOrbitAverage β hKm hF
  have hEq : A =ᵐ[volume] F :=
    ae_torusOrbitAverage_eq_of_multiplier_one β f hKm hKi hF hRep hPass
  have hConv (θ : UnitAddTorus d) (x : ℝ) :
      torusSchwartzOrbitConvolution β k F θ x = A (unitAddTorusFlow β x θ) := by
    let H (t : ℝ) := k (x - t) * F (unitAddTorusFlow β t θ)
    change (∫ t, H t) = _
    rw [show (∫ t, H t) = ∫ t, H (t + x) from (integral_add_right_eq_self H x).symm]
    apply integral_congr_ae
    filter_upwards with t
    simp only [H, K, unitAddTorusFlow_add_apply,
      show x - (t + x) = -t by abel]
  filter_upwards [ae_torusOrbit_congr β A F hAm hF hEq] with θ hθ
  exact hθ.mono (fun x hx => (hConv θ x).trans hx)

/-- The inverse Fourier cutoff kernel agrees pointwise with every
continuous representative of the same bounded-band orbit, for almost
every phase. -/
theorem ae_torusSchwartzOrbitConvolution_eq_bounded_band_representative
    (β : d → ℝ) (N : ℕ) (W : ℝ) (hW : W ≤ (N : ℝ) + 1)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hBand : ∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W → mFourierCoeff f n = 0)
    (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hRep : F =ᵐ[volume] f)
    (R : UnitAddTorus d → ℝ → ℂ)
    (hR : ∀ᵐ θ ∂volume, Continuous (R θ) ∧
      (R θ) =ᵐ[volume] fun x : ℝ => F (unitAddTorusFlow β x θ)) :
    ∀ᵐ θ ∂volume, torusSchwartzOrbitConvolution β (𝓕⁻ (scaledCompactSchwartzCutoff N)) F θ = R θ := by
  let k : SchwartzMap ℝ ℂ := 𝓕⁻ (scaledCompactSchwartzCutoff N)
  have hPass (n : d → ℤ) (hn : mFourierCoeff f n ≠ 0) :
      torusSchwartzKernelMultiplier β k n = 1 := by
    have hb : torusDirectionalFrequency β n ∈ Icc 0 W := by
      by_contra hc
      exact hn (hBand n hc)
    unfold torusSchwartzKernelMultiplier k
    rw [integral_neg_inverseFourier_mul_character]
    exact scaledCompactSchwartzCutoff_eq_one N (by rw [abs_of_nonneg hb.1]; exact hb.2.trans hW)
  have hMem : MemLp F 2 volume := (memLp_congr_ae hRep).mpr (Lp.memLp f)
  filter_upwards [hR, ae_torusSchwartzOrbitConvolution_eq_of_multiplier_one β k f F hF hRep hPass,
    ae_torusOrbit_weighted_norm_sq_lt_top β F hF hMem] with θ hθR hθC hθSq
  have hθGrow : (torusSchwartzOrbitConvolution β k F θ).HasTemperateGrowth :=
    (schwartz_convolution_estimates_of_weighted_sq k _ (measurable_orbit β θ hF) hθSq).1
  exact Measure.eq_of_ae_eq (hθC.trans hθR.2.symm) hθGrow.1.continuous hθR.1

private theorem ae_torusSchwartzOrbitPairing_congr
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (F G : UnitAddTorus d → ℂ) (hF : Measurable F) (hG : Measurable G)
    (he : F =ᵐ[volume] G) :
    torusSchwartzOrbitPairing β k g T F =ᵐ[volume] torusSchwartzOrbitPairing β k g T G := by
  filter_upwards [ae_torusOrbit_congr β F G hF hG he] with θ hθ
  have hConv : torusSchwartzOrbitConvolution β k F θ = torusSchwartzOrbitConvolution β k G θ := by
    funext x
    apply integral_congr_ae
    filter_upwards [hθ] with t ht
    rw [ht]
  simp only [torusSchwartzOrbitPairing, hConv]

private theorem ae_torusSchwartzOrbitPairing_add
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (F G : UnitAddTorus d → ℂ) (hF : Measurable F) (hG : Measurable G)
    (hFLp : MemLp F 2 volume) (hGLp : MemLp G 2 volume) :
    torusSchwartzOrbitPairing β k g T (F + G) =ᵐ[volume]
      torusSchwartzOrbitPairing β k g T F + torusSchwartzOrbitPairing β k g T G := by
  have h := ae_torusSchwartzOrbitPairing_sub β k g T (F + G) G
    (hF.add hG) hG (hFLp.add hGLp) hGLp
  rw [add_sub_cancel_right] at h
  exact h.mono (fun θ hθ => (eq_sub_iff_add_eq.mp hθ).symm)

private theorem ae_torusSchwartzOrbitPairing_smul
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (a : ℂ) (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hFLp : MemLp F 2 volume) :
    torusSchwartzOrbitPairing β k g T (a • F) =ᵐ[volume]
      a • torusSchwartzOrbitPairing β k g T F := by
  have hAF : Measurable (a • F) := measurable_const.smul hF
  filter_upwards [ae_torusOrbit_weighted_norm_sq_lt_top β F hF hFLp,
    ae_torusOrbit_weighted_norm_sq_lt_top β (a • F) hAF (hFLp.const_smul a)] with θ hθ hθA
  have hFgrow : (torusSchwartzOrbitConvolution β k F θ).HasTemperateGrowth :=
    (schwartz_convolution_estimates_of_weighted_sq k _ (measurable_orbit β θ hF) hθ).1
  have hAFgrow : (torusSchwartzOrbitConvolution β k (a • F) θ).HasTemperateGrowth :=
    (schwartz_convolution_estimates_of_weighted_sq k _ (measurable_orbit β θ hAF) hθA).1
  have hConv (x : ℝ) : torusSchwartzOrbitConvolution β k (a • F) θ x =
      a * torusSchwartzOrbitConvolution β k F θ x := by
    simp only [torusSchwartzOrbitConvolution, Pi.smul_apply, smul_eq_mul,
      mul_left_comm (k (x - _)) a, integral_const_mul]
  have hTest : SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k (a • F) θ) g =
      a • SchwartzMap.smulLeftCLM ℂ (torusSchwartzOrbitConvolution β k F θ) g := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply hAFgrow,
      SchwartzMap.smulLeftCLM_apply_apply hFgrow, smul_apply, hConv, mul_smul]
  change T θ _ = a • T θ _
  rw [hTest, map_smul]

/-- Orbit sampling is an actual continuous complex-linear map on Haar L².
For every measurable representative its value is the original
convolution pairing almost everywhere. -/
theorem exists_torusSchwartzOrbitSamplingCLM
    (β : d → ℝ) (k g : SchwartzMap ℝ ℂ) (weight order : ℕ)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hCont : ∀ f : SchwartzMap ℝ ℂ, Continuous (fun θ => T θ f))
    (D : ℝ) (hD : 0 ≤ D)
    (hT : ∀ᵐ θ ∂volume, ∀ f : SchwartzMap ℝ ℂ, ‖T θ f‖ ≤
      D * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) :
    let H := Lp ℂ 2 (volume : Measure (UnitAddTorus d))
    ∃ L : H →L[ℂ] H, ∀ (f : H) (F : UnitAddTorus d → ℂ), Measurable F →
      F =ᵐ[volume] f → ⇑(L f) =ᵐ[volume] torusSchwartzOrbitPairing β k g T F := by
  intro H
  let P (f : H) := (Lp.aestronglyMeasurable f).aemeasurable
  let R (f : H) := (P f).mk (⇑f)
  have hRm (f : H) : Measurable (R f) := (P f).measurable_mk
  have hRe (f : H) : R f =ᵐ[volume] f := (P f).ae_eq_mk.symm
  have hRp (f : H) : MemLp (R f) 2 volume := (memLp_congr_ae (hRe f)).mpr (Lp.memLp f)
  let S := torusSchwartzOrbitPairing β k g T
  obtain ⟨C, hC, hEstimate⟩ := memLp_torusSchwartzOrbitPairing_of_schwartzSeminorm_bound β k g weight order
  have hMem (f : H) : MemLp (S (R f)) 2 volume :=
    (hEstimate T hCont D hD hT _ (hRm f) (hRp f)).1
  let L (f : H) : H := (hMem f).toLp (S (R f))
  have hL (f : H) (F : UnitAddTorus d → ℂ) (hF : Measurable F) (he : F =ᵐ[volume] f) :
      ⇑(L f) =ᵐ[volume] S F :=
    (MemLp.coeFn_toLp (hMem f)).trans
      (ae_torusSchwartzOrbitPairing_congr β k g T _ _ (hRm f) hF ((hRe f).trans he.symm))
  let L₀ : H →ₗ[ℂ] H :=
    { toFun := L
      map_add' f z := by
        apply Lp.ext
        have hIn := ((hRe f).add (hRe z)).trans (Lp.coeFn_add f z).symm
        have hAdd := ae_torusSchwartzOrbitPairing_add β k g T _ _ (hRm f) (hRm z) (hRp f) (hRp z)
        have hOut := ((hL f _ (hRm f) (hRe f)).symm.add (hL z _ (hRm z) (hRe z)).symm).trans
          (Lp.coeFn_add (L f) (L z)).symm
        exact (hL (f + z) _ ((hRm f).add (hRm z)) hIn).trans (hAdd.trans hOut)
      map_smul' a f := by
        apply Lp.ext
        have hIn := ((hRe f).const_smul a).trans (Lp.coeFn_smul a f).symm
        have hSmul := ae_torusSchwartzOrbitPairing_smul β k g T a _ (hRm f) (hRp f)
        have hOut := ((hL f _ (hRm f) (hRe f)).symm.const_smul a).trans (Lp.coeFn_smul a (L f)).symm
        exact (hL (a • f) _ (measurable_const.smul (hRm f)) hIn).trans (hSmul.trans hOut) }
  let A := ENNReal.ofReal D * C
  have hA : A < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC
  have hNorm (f : H) : ‖L₀ f‖ ≤ A.toReal * ‖f‖ := by
    have h := (hEstimate T hCont D hD hT _ (hRm f) (hRp f)).2
    rw [eLpNorm_congr_ae (hRe f)] at h
    change ‖L f‖ ≤ A.toReal * ‖f‖
    calc
      ‖L f‖ = (eLpNorm (S (R f)) 2 volume).toReal := Lp.norm_toLp _ (hMem f)
      _ ≤ (A * eLpNorm f 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_lt_top hA (Lp.memLp f)).ne h
      _ = _ := by rw [ENNReal.toReal_mul, Lp.norm_def]
  exact ⟨L₀.mkContinuous A.toReal hNorm, hL⟩

/-- Lemma T's bounded band operator agrees with the actual Schwartz
pairing using any continuous representative of the real orbit. -/
theorem exists_torusBoundedBandSamplingCLM
    (β : d → ℝ) (W : ℝ) (g : SchwartzMap ℝ ℂ) (weight order : ℕ)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hCont : ∀ f : SchwartzMap ℝ ℂ, Continuous (fun θ => T θ f))
    (D : ℝ) (hD : 0 ≤ D)
    (hT : ∀ᵐ θ ∂volume, ∀ f : SchwartzMap ℝ ℂ, ‖T θ f‖ ≤
      D * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) :
    let H := Lp ℂ 2 (volume : Measure (UnitAddTorus d))
    ∃ (N : ℕ) (L : H →L[ℂ] H), W ≤ (N : ℝ) + 1 ∧
      (∀ (f : H) (F : UnitAddTorus d → ℂ), Measurable F → F =ᵐ[volume] f →
        ⇑(L f) =ᵐ[volume] torusSchwartzOrbitPairing β (𝓕⁻ (scaledCompactSchwartzCutoff N)) g T F) ∧
      ∀ (f : H), (∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W → mFourierCoeff f n = 0) →
      ∀ (F : UnitAddTorus d → ℂ), Measurable F → F =ᵐ[volume] f →
      ∀ (R : UnitAddTorus d → ℝ → ℂ),
      (∀ᵐ θ ∂volume, Continuous (R θ) ∧ (R θ) =ᵐ[volume] fun x : ℝ => F (unitAddTorusFlow β x θ)) →
      ⇑(L f) =ᵐ[volume] fun θ => T θ (SchwartzMap.smulLeftCLM ℂ (R θ) g) := by
  intro H
  obtain ⟨N, hN⟩ := exists_nat_gt W
  have hW : W ≤ (N : ℝ) + 1 := hN.le.trans (by linarith)
  let k := (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ)
  obtain ⟨L, hL⟩ := exists_torusSchwartzOrbitSamplingCLM β k g weight order T hCont D hD hT
  refine ⟨N, L, hW, hL, ?_⟩
  intro f hf F hF hRep R hR
  refine (hL f F hF hRep).trans ?_
  filter_upwards [ae_torusSchwartzOrbitConvolution_eq_bounded_band_representative
    β N W hW f hf F hF hRep R hR] with θ hθ
  simp only [torusSchwartzOrbitPairing, k, hθ]

end

end
end MeyerGeneralProblem
