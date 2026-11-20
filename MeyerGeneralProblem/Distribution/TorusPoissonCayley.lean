module

public import MeyerGeneralProblem.Distribution.TorusPoissonMeromorphicLeaf
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.MeasureTheory.Function.UniformIntegrable

@[expose] public section

/-!
# The Cayley field and its unit-modulus boundary

The scalar Cayley transform extends through every pole of the normalized
Poisson leaf. The resulting boundary values give a Haar `L²` limit as
height tends to zero through all positive real values.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory ProbabilityTheory Set UnitAddTorus
open scoped ENNReal NNReal Topology

/-- The Cayley transform used for the normalized positive Poisson leaf. -/
def supportPoissonCayley (w : ℂ) : ℂ :=
  (w + Complex.I - 1) / (w + Complex.I + 1)

/-- The Cayley denominator is nonzero on the closed right half-plane. -/
theorem supportPoissonCayley_denominator_ne_zero {w : ℂ} (hw : 0 ≤ w.re) :
    w + Complex.I + 1 ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  simp only [Complex.add_re, Complex.I_re, add_zero, Complex.one_re, Complex.zero_re] at hRe
  linarith

/-- The Cayley transform is bounded by one on the closed right half-plane. -/
theorem norm_supportPoissonCayley_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖supportPoissonCayley w‖ ≤ 1 := by
  rw [supportPoissonCayley, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr (supportPoissonCayley_denominator_ne_zero hw))).mpr
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    add_zero, sub_zero]
  nlinarith only [hw]

/-- Imaginary inputs have unit boundary modulus. -/
theorem norm_supportPoissonCayley_eq_one {w : ℂ} (hw : w.re = 0) :
    ‖supportPoissonCayley w‖ = 1 := by
  rw [supportPoissonCayley, norm_div]
  apply (div_eq_iff (norm_ne_zero_iff.mpr (supportPoissonCayley_denominator_ne_zero hw.ge))).mpr
  rw [one_mul]
  have hSq : ‖w + Complex.I - 1‖ ^ 2 = ‖w + Complex.I + 1‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      add_zero, sub_zero, hw]
    ring
  exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq.symm.le)

/-- At a simple pole the Cayley transform extends analytically with
value one and a simple zero of its difference from one. -/
theorem exists_analyticAt_supportPoissonCayley_at_simplePole
    {f g : ℂ → ℂ} {a c : ℂ} (hc : c ≠ 0) (hg : AnalyticAt ℂ g a)
    (hPole : f =ᶠ[𝓝[≠] a] fun w => c * (w - a)⁻¹ + g w) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ H a = 1 ∧
      (fun w => supportPoissonCayley (f w)) =ᶠ[𝓝[≠] a] H ∧
      meromorphicOrderAt (fun w => H w - 1) a = (1 : ℤ) := by
  let A (w : ℂ) := c + (w - a) * (g w + Complex.I + 1)
  let H (w : ℂ) := 1 - 2 * (w - a) / A w
  have hLin : AnalyticAt ℂ (fun w : ℂ => w - a) a := analyticAt_id.sub analyticAt_const
  have hA : AnalyticAt ℂ A a := analyticAt_const.add (hLin.mul ((hg.add analyticAt_const).add analyticAt_const))
  have hA0 : A a = c := by simp [A]
  have hAnz : A a ≠ 0 := by rwa [hA0]
  have hH : AnalyticAt ℂ H a := analyticAt_const.sub ((analyticAt_const.mul hLin).div hA hAnz)
  refine ⟨H, hH, by simp [H], ?_, ?_⟩
  · have hNear : ∀ᶠ w in 𝓝[≠] a, A w ≠ 0 :=
      (hA.continuousAt.eventually_ne hAnz).filter_mono nhdsWithin_le_nhds
    filter_upwards [hPole, hNear, self_mem_nhdsWithin] with w hw hAw hwa
    have hne : w - a ≠ 0 := sub_ne_zero.mpr hwa
    have hDen : f w + Complex.I + 1 = A w / (w - a) := by
      rw [hw]
      unfold A
      field_simp [hne]
      ring
    have hNum : f w + Complex.I - 1 = A w / (w - a) - 2 := by rw [← hDen]; ring
    rw [supportPoissonCayley, hDen, hNum]
    unfold H
    field_simp [hAw, hne]
  · have hHsub : AnalyticAt ℂ (fun w => H w - 1) a := hH.sub analyticAt_const
    have hM := hHsub.meromorphicAt
    let U (w : ℂ) := -(2 : ℂ) / A w
    have hU : AnalyticAt ℂ U a := analyticAt_const.div hA hAnz
    have hUnz : U a ≠ 0 := div_ne_zero (by norm_num) hAnz
    refine (meromorphicOrderAt_eq_int_iff hM).mpr ⟨U, hU, hUnz, ?_⟩
    apply Eventually.of_forall
    intro w
    simp only [H, U, zpow_one, smul_eq_mul, div_eq_mul_inv]
    ring

/-- Use normalized Haar measure on each circle factor of the phase torus. -/
local instance poissonCayleyCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance poissonCayleyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

section PhaseBoundary

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)

/-- The scalar boundary value at the origin of each normalized leaf.
The removable Cayley value is used when that origin is a pole. -/
def torusPoissonCayleyBoundary (θ : UnitAddTorus d) : ℂ := by
  classical
  exact if 0 ∈ Distribution.dsupport (T θ) then 1
    else supportPoissonCayley (torusPositivePoissonLeaf β S T hT hCont hCount θ 0)

/-- Almost every leaf has the actual pointwise vertical boundary limit
at the origin, and that limit has modulus one. -/
theorem ae_tendsto_torusPoissonCayleyBoundary
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume,
      ‖torusPoissonCayleyBoundary β S T hT hCont hCount θ‖ = 1 ∧
      Tendsto (fun y : ℝ => supportPoissonCayley
        (torusPositivePoissonLeaf β S T hT hCont hCount θ ((y : ℂ) * Complex.I)))
        (𝓝[>] 0) (𝓝 (torusPoissonCayleyBoundary β S T hT hCont hCount θ)) := by
  classical
  let line (y : ℝ) := (y : ℂ) * Complex.I
  have hLine : Tendsto line (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have h : Continuous line := Complex.continuous_ofReal.mul continuous_const
    have h0 : line 0 = 0 := by simp [line]
    simpa only [h0] using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hLineNE : Tendsto line (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_inf.mpr ⟨hLine, tendsto_principal.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)) Complex.I_ne_zero
  filter_upwards [ae_re_torusPositivePoissonLeaf_real_of_notMem_dsupport
    β S T hT hCont hCount hAdvance] with θ hθ
  let L := torusPositivePoissonLeaf β S T hT hCont hCount θ
  by_cases hp : 0 ∈ Distribution.dsupport (T θ)
  · obtain ⟨F, hF, hEq⟩ := exists_supportCauchy_analytic_remainder_at_site
      (S θ) (T θ) (hT θ) (hCount θ) hp
    let c := torusPositivePoissonField β S T hT hCont hCount Complex.I θ
    let G (w : ℂ) := c + F w
    have hG' : AnalyticAt ℂ G ((0 : ℝ) : ℂ) := analyticAt_const.add hF
    have hG : AnalyticAt ℂ G 0 := by simpa only [Complex.ofReal_zero] using hG'
    have hC : -supportCauchyConstant ≠ 0 := by
      rw [neg_supportCauchyConstant_eq_residue]
      apply div_ne_zero Complex.I_ne_zero
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hPole : L =ᶠ[𝓝[≠] (0 : ℂ)] fun w => -supportCauchyConstant * (w - 0)⁻¹ + G w := by
      have hEq' := hEq.filter_mono (show 𝓝[≠] ((0 : ℝ) : ℂ) ≤ 𝓝 ((0 : ℝ) : ℂ) from nhdsWithin_le_nhds)
      rw [Complex.ofReal_zero] at hEq'
      filter_upwards [hEq'] with w hw
      change c + (∫ x, supportCauchyKernel w x ∂discreteSupportCount (T θ)) = _
      rw [hw]
      unfold G
      abel
    obtain ⟨H, hH, hH0, hCayley, _⟩ := exists_analyticAt_supportPoissonCayley_at_simplePole hC hG hPole
    have hLim := (hH.continuousAt.tendsto.comp hLine).congr' (hCayley.comp_tendsto hLineNE).symm
    exact ⟨by simp [torusPoissonCayleyBoundary, hp],
      by simpa only [line, L, Function.comp_def, hH0, torusPoissonCayleyBoundary, ite_eq_left hp] using hLim⟩
  · have hNo : (0 : ℂ) ∉ Complex.ofReal '' Distribution.dsupport (T θ) := by
      rintro ⟨a, ha, hzero⟩
      exact hp ((Complex.ofReal_eq_zero.mp hzero) ▸ ha)
    have hL : AnalyticAt ℂ L 0 :=
      (torusPositivePoissonLeaf_poles_and_residues β S T hT hCont hCount θ).1 0 hNo
    have hRe : (L 0).re = 0 := by simpa only [Complex.ofReal_zero] using hθ 0 hp
    have hCayley : ContinuousAt supportPoissonCayley (L 0) := by
      unfold supportPoissonCayley
      exact ((continuousAt_id.add continuousAt_const).sub continuousAt_const).div
        ((continuousAt_id.add continuousAt_const).add continuousAt_const)
        (supportPoissonCayley_denominator_ne_zero hRe.ge)
    have hLim := hCayley.tendsto.comp (hL.continuousAt.tendsto.comp hLine)
    exact ⟨by simpa only [torusPoissonCayleyBoundary, ite_eq_right hp] using norm_supportPoissonCayley_eq_one hRe,
      by simpa only [line, L, Function.comp_def, torusPoissonCayleyBoundary, ite_eq_right hp] using hLim⟩

/-- Almost every scalar leaf gives a holomorphic Cayley field bounded
by one on the whole upper half-plane. -/
theorem ae_analyticOnNhd_norm_supportPoissonCayley_leaf
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume,
      AnalyticOnNhd ℂ (fun z => supportPoissonCayley (torusPositivePoissonLeaf β S T hT hCont hCount θ z))
        {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im →
        ‖supportPoissonCayley (torusPositivePoissonLeaf β S T hT hCont hCount θ z)‖ ≤ 1 := by
  filter_upwards [ae_forall_re_torusPositivePoissonLeaf β S T hT hCont hCount hAdvance] with θ hθ
  let L := torusPositivePoissonLeaf β S T hT hCont hCount θ
  have hRe (z : ℂ) (hz : 0 < z.im) : 0 ≤ (L z).re := by
    change 0 ≤ (torusPositivePoissonLeaf β S T hT hCont hCount θ z).re
    rw [hθ z hz]
    refine div_nonneg (integral_nonneg (fun t => ?_)) (by norm_num)
    exact (cauchyPDF_pos _ (Real.toNNReal_pos.mpr hz).ne' t).le
  refine ⟨?_, fun z hz => norm_supportPoissonCayley_le_one (hRe z hz)⟩
  intro z hz
  have hL : AnalyticAt ℂ L z := analyticOnNhd_torusPositivePoissonLeaf β S T hT hCont hCount θ z hz
  change AnalyticAt ℂ (fun w => supportPoissonCayley (L w)) z
  unfold supportPoissonCayley
  exact ((hL.add analyticAt_const).sub analyticAt_const).div
    ((hL.add analyticAt_const).add analyticAt_const) (supportPoissonCayley_denominator_ne_zero (hRe z hz))

/-- The bounded Cayley field at each positive imaginary part, with zero
values outside the upper half-plane for the ambient function. -/
def torusPoissonCayleyField (z : ℂ) (θ : UnitAddTorus d) : ℂ :=
  if 0 < z.im then supportPoissonCayley
    (torusPositivePoissonLeaf β S T hT hCont hCount θ z) else 0

/-- For each argument the Cayley field is measurable up to Haar null sets. -/
theorem aemeasurable_torusPoissonCayleyField
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) :
    AEMeasurable (torusPoissonCayleyField β S T hT hCont hCount z) volume := by
  by_cases hz : 0 < z.im
  · have hEq := ae_eq_torusPositivePoissonLeaf_field β S T hT hCont hCount hAdvance z hz
    have hM := (Lp.aestronglyMeasurable _).aemeasurable.congr hEq.symm
    have hC : Measurable supportPoissonCayley := by unfold supportPoissonCayley; fun_prop
    have hF : torusPoissonCayleyField β S T hT hCont hCount z =
        fun θ => supportPoissonCayley (torusPositivePoissonLeaf β S T hT hCont hCount θ z) := by
      funext θ
      simp [torusPoissonCayleyField, hz]
    rw [hF]
    exact hC.comp_aemeasurable hM
  · have hF : torusPoissonCayleyField β S T hT hCont hCount z = 0 := by
      funext θ
      simp [torusPoissonCayleyField, hz]
    rw [hF]
    exact aemeasurable_const

/-- On one full-measure set the scalar Cayley field is holomorphic on the
upper half-plane and bounded by one at every complex argument. -/
theorem ae_analyticOnNhd_norm_torusPoissonCayleyField
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume,
      AnalyticOnNhd ℂ (fun z => torusPoissonCayleyField β S T hT hCont hCount z θ)
        {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, ‖torusPoissonCayleyField β S T hT hCont hCount z θ‖ ≤ 1 := by
  filter_upwards [ae_analyticOnNhd_norm_supportPoissonCayley_leaf β S T hT hCont hCount hAdvance]
    with θ hθ
  refine ⟨?_, fun z => ?_⟩
  · intro z hz
    have hPos : 0 < z.im := hz
    apply (hθ.1 z hz).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hPos] with w hw
    simp [torusPoissonCayleyField, show 0 < w.im from hw]
  · by_cases hz : 0 < z.im
    · simpa only [torusPoissonCayleyField, ite_eq_left hz] using hθ.2 z hz
    · simp [torusPoissonCayleyField, hz]

private theorem ae_tendsto_torusPoissonCayleyField
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume,
      ‖torusPoissonCayleyBoundary β S T hT hCont hCount θ‖ = 1 ∧
      Tendsto (fun y : ℝ => torusPoissonCayleyField β S T hT hCont hCount ((y : ℂ) * Complex.I) θ)
        (𝓝[>] 0) (𝓝 (torusPoissonCayleyBoundary β S T hT hCont hCount θ)) := by
  filter_upwards [ae_tendsto_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance] with θ hθ
  refine ⟨hθ.1, hθ.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < y := hy
  simp [torusPoissonCayleyField, Complex.mul_im, hy']

/-- The pointwise scalar boundary limit is measurable up to Haar null sets. -/
theorem aemeasurable_torusPoissonCayleyBoundary
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    AEMeasurable (torusPoissonCayleyBoundary β S T hT hCont hCount) volume :=
  aemeasurable_of_tendsto_metrizable_ae (𝓝[>] (0 : ℝ))
    (fun y => aemeasurable_torusPoissonCayleyField β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I))
    ((ae_tendsto_torusPoissonCayleyField β S T hT hCont hCount hAdvance).mono fun _ h => h.2)

private theorem memLp_torusPoissonCayleyField
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) :
    MemLp (torusPoissonCayleyField β S T hT hCont hCount z) 2 volume :=
  MemLp.of_bound (aemeasurable_torusPoissonCayleyField β S T hT hCont hCount hAdvance z).aestronglyMeasurable
    1 ((ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance).mono fun _ h => h.2 z)

private theorem memLp_torusPoissonCayleyBoundary
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    MemLp (torusPoissonCayleyBoundary β S T hT hCont hCount) 2 volume :=
  MemLp.of_bound (aemeasurable_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance).aestronglyMeasurable
    1 ((ae_tendsto_torusPoissonCayleyField β S T hT hCont hCount hAdvance).mono fun _ h => h.1.le)

/-- The bounded Cayley field represented in normalized Haar `L²`. -/
def torusPoissonCayleyL2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) : TorusL2(d) :=
  (memLp_torusPoissonCayleyField β S T hT hCont hCount hAdvance z).toLp _

/-- The `L²` Cayley field has its explicit scalar representative almost everywhere. -/
theorem coeFn_torusPoissonCayleyL2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) :
    torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z =ᵐ[volume]
      torusPoissonCayleyField β S T hT hCont hCount z :=
  MemLp.coeFn_toLp _

/-- The unit-modulus Cayley boundary represented in normalized Haar `L²`. -/
def torusPoissonCayleyBoundaryL2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    TorusL2(d) :=
  (memLp_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance).toLp _

/-- The Haar `L²` boundary has pointwise modulus one almost everywhere. -/
theorem ae_norm_torusPoissonCayleyBoundaryL2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume, ‖torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance θ‖ = 1 := by
  filter_upwards [(memLp_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance).coeFn_toLp,
    ae_tendsto_torusPoissonCayleyField β S T hT hCont hCount hAdvance] with θ h1 h2
  exact (congrArg norm h1).trans h2.1

/-- The bounded Cayley fields converge in Haar `L²` to the unit-modulus
boundary as height tends to zero through all positive real values. -/
theorem tendsto_torusPoissonCayleyBoundary_L2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    Tendsto (fun y : ℝ => torusPoissonCayleyL2 β S T hT hCont hCount hAdvance ((y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance)) := by
  let M : Measure (UnitAddTorus d) := volume
  let F (y : ℝ) := torusPoissonCayleyField β S T hT hCont hCount ((y : ℂ) * Complex.I)
  let g := torusPoissonCayleyBoundary β S T hT hCont hCount
  have hLp (y : ℝ) : MemLp (F y) 2 M :=
    memLp_torusPoissonCayleyField β S T hT hCont hCount hAdvance _
  have hg : MemLp g 2 M := memLp_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hLp g hg).mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  let q (n : ℕ) := F (u n)
  have hQ (n : ℕ) : AEStronglyMeasurable (q n) M := (hLp (u n)).aestronglyMeasurable
  have hUI : UnifIntegrable q 2 M := by
    refine unifIntegrable_of (by norm_num) (by norm_num) hQ fun ε hε => ⟨2, fun n => ?_⟩
    have hZero : ({x | (2 : ℝ≥0) ≤ ‖q n x‖₊}.indicator (q n)) =ᵐ[M] 0 := by
      filter_upwards [ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
        with x hx
      apply indicator_of_notMem
      intro hx'
      have hTwo : (2 : ℝ) ≤ ‖q n x‖ := by exact_mod_cast hx'
      have hOne : ‖q n x‖ ≤ 1 := hx.2 _
      linarith only [hTwo, hOne]
    rw [eLpNorm_congr_ae hZero, eLpNorm_zero]
    exact bot_le
  have hLim : ∀ᵐ θ ∂M, Tendsto (fun n => q n θ) atTop (𝓝 (g θ)) :=
    (ae_tendsto_torusPoissonCayleyField β S T hT hCont hCount hAdvance).mono fun _ h => h.2.comp hu
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hQ hg hUI hLim

end PhaseBoundary

end
end MeyerGeneralProblem
