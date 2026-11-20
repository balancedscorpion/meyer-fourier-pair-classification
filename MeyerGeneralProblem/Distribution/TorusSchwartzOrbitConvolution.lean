module

public import MeyerGeneralProblem.Distribution.TorusBandRepresentative
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Schwartz convolution of weighted orbit data

The real convolution has polynomial bounds for every derivative.
Continuity and the real restriction identity transfer these bounds to
the bounded-band representatives used on the hull.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff ENNReal Topology FourierTransform SchwartzMap

/-- Convolution by a Schwartz function gives a smooth, temperate
representative for measurable data of finite inverse-quadratic weighted
square integral. Each derivative is the convolution with the corresponding
kernel derivative and has a quadratic envelope controlled by the
weighted absolute integral. -/
theorem schwartz_convolution_estimates_of_weighted_sq
    (k : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (hg : Measurable g)
    (hSq : (∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2)⁻¹) *
      ENNReal.ofReal (‖g t‖ ^ 2)) < (⊤ : ℝ≥0∞)) :
    let A (x : ℝ) := ∫ t : ℝ, k (x - t) * g t
    A.HasTemperateGrowth ∧
      (∀ (j : ℕ) (x : ℝ), iteratedDeriv j A x =
        ∫ t : ℝ, iteratedDeriv j (k : ℝ → ℂ) (x - t) * g t) ∧
      ∀ (j : ℕ) (x : ℝ), ‖iteratedDeriv j A x‖ ≤
        (2 * (SchwartzMap.seminorm ℂ 0 j k + SchwartzMap.seminorm ℂ 2 j k) *
          (∫ t : ℝ, (1 + t ^ 2)⁻¹ * ‖g t‖)) * (1 + x ^ 2) := by
  intro A
  let a (t : ℝ) := (1 + t ^ 2)⁻¹
  let M (j : ℕ) := SchwartzMap.seminorm ℂ 0 j k + SchwartzMap.seminorm ℂ 2 j k
  let D (j : ℕ) (x t : ℝ) := iteratedDeriv j (k : ℝ → ℂ) (x - t) * g t
  let H (j : ℕ) (x : ℝ) := ∫ t : ℝ, D j x t
  let v (t : ℝ) := a t * ‖g t‖
  have ha (t : ℝ) : 0 ≤ a t := by dsimp [a]; positivity
  have hM (j : ℕ) : 0 ≤ M j := by dsimp [M]; positivity
  have hAMeas : Measurable a := (measurable_const.add (measurable_id.pow_const 2)).inv
  have hVInt : Integrable v := by
    have hi := integrable_mul_of_le_inverse_quadratic_weight g (fun t : ℝ => (a t : ℂ)) hg
      (Complex.continuous_ofReal.measurable.comp hAMeas) 1 hSq (fun t => by
        rw [Complex.norm_real, Real.norm_of_nonneg (ha t), one_mul])
    have he : (fun t : ℝ => ‖(a t : ℂ) * g t‖) = v := by
      funext t
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha t)]
    exact he ▸ hi.norm
  have hv (t : ℝ) : 0 ≤ v t := mul_nonneg (ha t) (norm_nonneg _)
  have hKernel (j : ℕ) (s : ℝ) :
      (1 + s ^ 2) * ‖iteratedDeriv j (k : ℝ → ℂ) s‖ ≤ M j := by
    have h0 := SchwartzMap.le_seminorm ℂ 0 j k s
    have h2 := SchwartzMap.le_seminorm ℂ 2 j k s
    rw [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h0
    rw [Real.norm_eq_abs, sq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h2
    rw [add_mul, one_mul]
    exact add_le_add h0 h2
  have hBound (j : ℕ) (x t : ℝ) :
      ‖D j x t‖ ≤ 2 * (1 + x ^ 2) * M j * v t := by
    let s := x - t
    have hGeom : 1 + t ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + s ^ 2) := by
      dsimp [s]
      nlinarith [sq_nonneg (x + (x - t)), mul_nonneg (sq_nonneg x) (sq_nonneg (x - t))]
    have hK : ‖iteratedDeriv j (k : ℝ → ℂ) s‖ ≤ 2 * (1 + x ^ 2) * M j * a t := by
      change _ ≤ _ * (1 + t ^ 2)⁻¹
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (by positivity)).mpr
      calc
        _ ≤ ‖iteratedDeriv j (k : ℝ → ℂ) s‖ * (2 * (1 + x ^ 2) * (1 + s ^ 2)) :=
          mul_le_mul_of_nonneg_left hGeom (norm_nonneg _)
        _ = 2 * (1 + x ^ 2) * ((1 + s ^ 2) * ‖iteratedDeriv j (k : ℝ → ℂ) s‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hKernel j s) (by positivity)
    rw [show D j x t = iteratedDeriv j (k : ℝ → ℂ) s * g t from rfl, norm_mul]
    calc
      _ ≤ (2 * (1 + x ^ 2) * M j * a t) * ‖g t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ = _ := by dsimp [v]; ring
  have hDSmooth (j : ℕ) : Differentiable ℝ (iteratedDeriv j (k : ℝ → ℂ)) :=
    ContDiff.differentiable_iteratedDeriv' j (k.smooth _)
  have hMeas (j : ℕ) (x : ℝ) : Measurable (D j x) :=
    ((hDSmooth j).continuous.comp (continuous_const.sub continuous_id)).measurable.mul hg
  have hDeriv (j : ℕ) (x₀ : ℝ) : HasDerivAt (H j) (H (j + 1) x₀) x₀ := by
    let C := 2 * (1 + (|x₀| + 1) ^ 2) * M (j + 1)
    have hInt : Integrable (D j x₀) := (hVInt.const_mul (2 * (1 + x₀ ^ 2) * M j)).mono'
      (hMeas j x₀).aestronglyMeasurable (Eventually.of_forall (hBound j x₀))
    have hDominant : ∀ᵐ t ∂volume, ∀ x ∈ Metric.ball x₀ 1, ‖D (j + 1) x t‖ ≤ C * v t :=
      Eventually.of_forall fun t x hx => by
        have hx' : |x| ≤ |x₀| + 1 := by
          have hΔ : |x - x₀| < 1 := by
            simpa only [Metric.mem_ball, Real.dist_eq] using hx
          calc
            |x| = |x - x₀ + x₀| := by rw [sub_add_cancel]
            _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
            _ ≤ _ := by linarith
        have hSq' : x ^ 2 ≤ (|x₀| + 1) ^ 2 := by
          rw [← sq_abs x]
          exact pow_le_pow_left₀ (abs_nonneg x) hx' 2
        refine (hBound (j + 1) x t).trans ?_
        dsimp [C]
        gcongr
    have hDiff (t : ℝ) (x : ℝ) : HasDerivAt (fun y => D j y t) (D (j + 1) x t) x := by
      have h := (((hDSmooth j) (x - t)).hasDerivAt.scomp x ((hasDerivAt_id x).sub_const t)).mul_const (g t)
      simpa only [D, Function.comp_apply, iteratedDeriv_succ, id_eq, one_smul] using h
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds x₀ one_pos) (Eventually.of_forall fun x => (hMeas j x).aestronglyMeasurable)
      hInt (hMeas (j + 1) x₀).aestronglyMeasurable hDominant (hVInt.const_mul C)
      (Eventually.of_forall fun t x _ => hDiff t x)).2
  have hEq (j : ℕ) : iteratedDeriv j A = H j := by
    induction j with
    | zero => rw [iteratedDeriv_zero]; rfl
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hDeriv j x).deriv
  have hIntegralBound (j : ℕ) (x : ℝ) :
      ‖iteratedDeriv j A x‖ ≤ (2 * M j * (∫ t, v t)) * (1 + x ^ 2) := by
    rw [hEq]
    have hDom := norm_integral_le_of_norm_le
      (hVInt.const_mul (2 * (1 + x ^ 2) * M j)) (Eventually.of_forall (hBound j x))
    calc
      ‖H j x‖ ≤ ∫ t, 2 * (1 + x ^ 2) * M j * v t := hDom
      _ = (2 * M j * (∫ t, v t)) * (1 + x ^ 2) := by rw [integral_const_mul]; ring
  refine ⟨⟨contDiff_of_differentiable_iteratedDeriv (fun j _ => by
    rw [hEq]
    exact fun x => (hDeriv j x).differentiableAt), ?_⟩, fun j x => congrFun (hEq j) x, hIntegralBound⟩
  intro j
  refine ⟨2, 2 * M j * (∫ t, v t), fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hx : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
    rw [Real.norm_eq_abs, ← sq_abs x]
    nlinarith [abs_nonneg x]
  exact (hIntegralBound j x).trans (mul_le_mul_of_nonneg_left hx
    (mul_nonneg (mul_nonneg (by norm_num) (hM j)) (integral_nonneg hv)))

/-- Convolution of weighted square-integrable data has temperate growth,
with derivatives obtained by differentiating the Schwartz kernel. -/
theorem schwartz_convolution_hasTemperateGrowth_of_weighted_sq
    (k : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (hg : Measurable g)
    (hSq : (∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2)⁻¹) *
      ENNReal.ofReal (‖g t‖ ^ 2)) < (⊤ : ℝ≥0∞)) :
    let A (x : ℝ) := ∫ t : ℝ, k (x - t) * g t
    A.HasTemperateGrowth ∧
      ∀ (j : ℕ) (x : ℝ), iteratedDeriv j A x =
        ∫ t : ℝ, iteratedDeriv j (k : ℝ → ℂ) (x - t) * g t := by
  obtain ⟨hgrowth, hderiv, _⟩ := schwartz_convolution_estimates_of_weighted_sq k g hg hSq
  exact ⟨hgrowth, hderiv⟩

/-- Use normalized Haar measure on each circle factor. -/
local instance schwartzOrbitCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- Any continuous real representative of a bounded-band torus orbit
has temperate growth on almost every phase leaf. -/
theorem ae_hasTemperateGrowth_of_continuous_torusOrbit_representative {d : Type*} [Fintype d]
    (β : d → ℝ) (W : ℝ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hBand : ∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W → mFourierCoeff f n = 0)
    (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hFRep : F =ᵐ[volume] f)
    (A : UnitAddTorus d → ℝ → ℂ)
    (hA : ∀ᵐ θ ∂volume, Continuous (A θ) ∧
      (A θ) =ᵐ[volume] fun t => F (unitAddTorusFlow β t θ)) :
    ∀ᵐ θ ∂volume, (A θ).HasTemperateGrowth := by
  obtain ⟨N, k, G, _, _, hk, hG, hGRep, hGOrbit⟩ :=
    exists_entire_torusOrbit_representative_of_bounded_band β W f hBand
  let K : SchwartzMap ℝ ℂ := 𝓕⁻ (scaledCompactSchwartzCutoff N)
  let B (θ : UnitAddTorus d) (x : ℝ) :=
    ∫ t : ℝ, K (x - t) * G (unitAddTorusFlow β t θ)
  have hGMem : MemLp G 2 volume := (memLp_congr_ae hGRep).mpr (Lp.memLp f)
  have hGWeight := ae_torusOrbit_weighted_norm_sq_lt_top β G hG hGMem
  have hEqOrbit := ae_torusOrbit_congr β F G hF hG (hFRep.trans hGRep.symm)
  filter_upwards [hA, hGOrbit, hGWeight, hEqOrbit] with θ hAθ hGθ hWθ hEqθ
  have hM : Measurable (fun t : ℝ => G (unitAddTorusFlow β t θ)) :=
    hG.comp ((continuous_unitAddTorusFlow β).measurable.comp (measurable_id.prodMk measurable_const))
  have hB : (B θ).HasTemperateGrowth :=
    (schwartz_convolution_hasTemperateGrowth_of_weighted_sq K _ hM hWθ).1
  have hReal : ∀ x : ℝ, (∫ t : ℝ, k ((x : ℂ) - (t : ℂ)) * G (unitAddTorusFlow β t θ)) = B θ x := by
    intro x
    unfold B
    apply integral_congr_ae
    filter_upwards with t
    rw [← Complex.ofReal_sub, hk]
  have hBG : B θ =ᵐ[volume] fun t => G (unitAddTorusFlow β t θ) := by
    filter_upwards [hGθ.2] with x hx
    rw [← hReal x]
    exact hx
  have hFG : (fun t : ℝ => F (unitAddTorusFlow β t θ)) =ᵐ[volume]
      fun t : ℝ => G (unitAddTorusFlow β t θ) := hEqθ
  have hAB : A θ = B θ :=
    Measure.eq_of_ae_eq (hAθ.2.trans (hFG.trans hBG.symm)) hAθ.1 hB.1.continuous
  rwa [hAB]

end
end MeyerGeneralProblem
