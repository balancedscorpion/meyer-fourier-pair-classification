module

public import MeyerGeneralProblem.Distribution.BlaschkeBoundaryLog

@[expose] public section

/-!
# Integrable local bounds for the Blaschke logarithm

Radial contraction can reduce the distance to a point of the unit
circle by at most a factor of two. This bounds the logarithmic defect
uniformly by an integrable function of the boundary angle.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

private theorem norm_boundary_sub_le_two_mul_radial {w ζ : ℂ} (hw : ‖w‖ = 1) (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖w - ζ‖ ≤ 2 * ‖(r : ℂ) * w - ζ‖ := by
  have hRadial : ‖(r : ℂ) * w‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hw, mul_one]
  have hLower := norm_sub_norm_le ζ ((r : ℂ) * w)
  rw [hζ, hRadial, norm_sub_rev] at hLower
  have hDist : ‖w - (r : ℂ) * w‖ = 1 - r := by
    rw [show w - (r : ℂ) * w = ((1 - r : ℝ) : ℂ) * w by
      simp [sub_mul], norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hr₁),
      hw, mul_one]
  calc
    ‖w - ζ‖ ≤ ‖w - (r : ℂ) * w‖ + ‖(r : ℂ) * w - ζ‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ 2 * ‖(r : ℂ) * w - ζ‖ := by linarith only [hDist, hLower]

/-- A finite Cayley boundary point admits a radial bound on the
logarithmic defect by a constant and the absolute logarithm of the
boundary chord. The bound holds up to the real zeros. -/
theorem exists_local_blaschkeBoundaryLog_radial_bound {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ₁ : ζ ≠ 1) (A : ℝ) :
    ∃ (δ : ℝ) (_ : 0 < δ) (n : ℕ) (D : ℝ),
      ∀ {w : ℂ} (_ : ‖w‖ = 1) (_ : w ≠ ζ) {r : ℝ} (_ : 0 ≤ r) (_ : r < 1),
        (r : ℂ) * w ∈ ball ζ δ →
        A - (L (cayleyToUpperHalfPlane ((r : ℂ) * w))).re ≤ D + (n : ℝ) * |Real.log ‖w - ζ‖| := by
  obtain ⟨n, R, hR, hInside, _⟩ := exists_local_blaschkeBoundaryLog_model ha hFin hSum hH hFactor hζ hζ₁
  have hRlow : ∀ᶠ u in 𝓝 ζ, R ζ - 1 < R u :=
    hR.tendsto.eventually (Ioi_mem_nhds (sub_lt_self _ zero_lt_one))
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp ((eventually_nhdsWithin_iff.mp hInside).and hRlow)
  refine ⟨δ, hδ, n, A - R ζ + 1 + (n : ℝ) * Real.log 2, ?_⟩
  intro w hw hwζ r hr hr₁ hNear
  let u := (r : ℂ) * w
  have hu : u ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hw, mul_one]
    exact hr₁
  obtain ⟨hLog, hRem⟩ := hBall hNear
  have hDist := norm_boundary_sub_le_two_mul_radial hw hζ hr hr₁.le
  have hChord : 0 < ‖w - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwζ)
  have hHalf : ‖w - ζ‖ / 2 ≤ ‖u - ζ‖ := (div_le_iff₀ (by norm_num)).mpr (by linarith only [hDist])
  have hl : Real.log ‖w - ζ‖ - Real.log 2 ≤ Real.log ‖u - ζ‖ := by
    rw [← Real.log_div hChord.ne' two_ne_zero]
    exact Real.log_le_log (half_pos hChord) hHalf
  have hn := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) n)
  have habs := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log ‖w - ζ‖)) (Nat.cast_nonneg (α := ℝ) n)
  rw [hLog hu]
  linarith only [hRem, hn, habs]

/-- The absolute logarithm of a boundary chord is integrable in the
angular measure. -/
theorem integrable_diskAngleMeasure_abs_log_chord (ζ : ℂ) :
    Integrable (fun θ : ℝ => |Real.log ‖circleMap 0 1 θ - ζ‖|) diskAngleMeasure := by
  have hM : MeromorphicOn (fun z : ℂ => z - ζ) (sphere (0 : ℂ) |(1 : ℝ)|) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  have hI := hM.circleIntegrable_log_norm
  change IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - ζ‖) volume 0 (2 * Real.pi) at hI
  have hIoc := hI.abs.1
  exact hIoc.mono_set Ioo_subset_Ioc_self

/-- The radial defect admits one integrable majorant on any compact
set of finite Cayley boundary points, uniformly as the radius tends
to one from below. -/
theorem exists_integrable_blaschkeBoundaryLog_radial_bound_on_compact
    {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ sphere (0 : ℂ) 1 \ {1}) (A : ℝ) :
    ∃ M : ℝ → ℝ, Integrable M diskAngleMeasure ∧ 0 ≤ M ∧
      ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), ∀ᵐ θ ∂diskAngleMeasure, circleMap 0 1 θ ∈ K →
        A - (L (cayleyToUpperHalfPlane (circleMap 0 r θ))).re ≤ M θ := by
  classical
  let _ : IsFiniteMeasure diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  let _ : NullSingletonClass diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  have hPoint (v : K) : ‖(v : ℂ)‖ = 1 ∧ (v : ℂ) ≠ 1 := by
    simpa only [Set.mem_sdiff, mem_sphere, dist_zero_right, mem_singleton_iff] using hKsub v.property
  choose δ hδ n D hBound using fun v : K =>
    exists_local_blaschkeBoundaryLog_radial_bound ha hFin hSum hH hFactor
      (hPoint v).1 (hPoint v).2 A
  let U (v : K) := ball (v : ℂ) (δ v / 2)
  have hCover : K ⊆ ⋃ v, U v := fun v hv =>
    mem_iUnion.mpr ⟨⟨v, hv⟩, mem_ball_self (half_pos (hδ ⟨v, hv⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hCover
  let m (v : K) (θ : ℝ) := max (D v) 0 + (n v : ℝ) * |Real.log ‖circleMap 0 1 θ - (v : ℂ)‖|
  have hm (v : K) (θ : ℝ) : 0 ≤ m v θ :=
    add_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  let M (θ : ℝ) := ∑ v ∈ s, m v θ
  have hInt : Integrable M diskAngleMeasure := integrable_finsetSum s fun v _ =>
    (integrable_const _).add ((integrable_diskAngleMeasure_abs_log_chord v).const_mul _)
  have hM : 0 ≤ M := fun θ => Finset.sum_nonneg fun v _ => hm v θ
  have hAvoid : ∀ᵐ θ ∂diskAngleMeasure, ∀ v ∈ s, circleMap 0 1 θ ≠ (v : ℂ) := by
    rw [Finset.eventually_all]
    intro v _
    simp only [ae_iff, not_not]
    change diskAngleMeasure (circleMap 0 1 ⁻¹' {(v : ℂ)}) = 0
    exact ((countable_singleton (v : ℂ)).preimage_circleMap (0 : ℂ) one_ne_zero).measure_zero diskAngleMeasure
  have hTime : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), ∀ v ∈ s, 1 - r < δ v / 2 := by
    rw [Finset.eventually_all]
    intro v _
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (sub_lt_self (1 : ℝ) (half_pos (hδ v))))] with r hr
    linarith only [show 1 - δ v / 2 < r from hr]
  refine ⟨M, hInt, hM, ?_⟩
  filter_upwards [hTime, self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)]
    with r hrδ (hr₁ : r < 1) (hr : 0 < r)
  filter_upwards [hAvoid] with θ hθ hθK
  let w := circleMap 0 1 θ
  obtain ⟨v, hv⟩ := mem_iUnion.mp (hs hθK)
  obtain ⟨hvs, hvw⟩ := mem_iUnion.mp hv
  have hw : ‖w‖ = 1 := by simp [w, norm_circleMap_zero]
  have hScaled : circleMap 0 r θ = (r : ℂ) * w := by
    simp only [w, circleMap_zero, Complex.ofReal_one, one_mul]
  have hDist : dist ((r : ℂ) * w) w = 1 - r := by
    rw [dist_eq_norm, show (r : ℂ) * w - w = ((r - 1 : ℝ) : ℂ) * w by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul],
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one,
      abs_of_nonpos (sub_nonpos.mpr hr₁.le), neg_sub]
  have hNear : (r : ℂ) * w ∈ ball (v : ℂ) (δ v) := by
    apply mem_ball.mpr ((dist_triangle _ w _).trans_lt ?_)
    linarith only [hDist, hrδ v hvs, show dist w v < δ v / 2 from hvw]
  rw [hScaled]
  calc
    _ ≤ D v + (n v : ℝ) * |Real.log ‖w - (v : ℂ)‖| := hBound v hw (hθ v hvs) hr.le hr₁ hNear
    _ ≤ m v θ := add_le_add (le_max_left _ _) le_rfl
    _ ≤ M θ := Finset.single_le_sum (fun u _ => hm u θ) hvs

end
end MeyerGeneralProblem
