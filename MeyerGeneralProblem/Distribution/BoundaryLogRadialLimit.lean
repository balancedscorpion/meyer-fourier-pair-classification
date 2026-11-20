module

public import MeyerGeneralProblem.Distribution.BoundaryLogArgument
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Radial limits of the conjugate Herglotz integral

At a real boundary point with a local first-order bound on the datum,
subtracting its value cancels the pole of the conjugate kernel. The
one integrable function bounds the compensated integrands up to the boundary.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem norm_sub_le_twice_norm_sub_radial {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ‖a - b‖ ≤ 2 * ‖a - (s : ℂ) * b‖ := by
  let w := (s : ℂ) * b
  have hw : ‖w‖ = s := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, hb, mul_one, Real.norm_of_nonneg hs₀]
  have hShift : ‖w - b‖ = 1 - s := by
    have he : w - b = ((s - 1 : ℝ) : ℂ) * b := by
      simp [w, Complex.ofReal_sub, sub_mul]
    rw [he, norm_mul, Complex.norm_real, hb, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hs₁)]
    ring
  have hTri := norm_add_le (a - w) (w - b)
  rw [sub_add_sub_cancel, hShift] at hTri
  have hRev := norm_sub_norm_le a w
  rw [ha, hw] at hRev
  change ‖a - b‖ ≤ 2 * ‖a - w‖
  linarith only [hTri, hRev]

private theorem norm_ofReal_add_I_pos (t : ℝ) : 0 < ‖(t : ℂ) + Complex.I‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hi := congrArg Complex.im h
  simp at hi

private theorem norm_cayleyBoundaryPoint_sub_mul (t x : ℝ) :
    ‖cayleyBoundaryPoint t - cayleyBoundaryPoint x‖ *
        (‖(t : ℂ) + Complex.I‖ * ‖(x : ℂ) + Complex.I‖) = 2 * |t - x| := by
  have hProd : ‖(t : ℂ) + Complex.I‖ * ‖(x : ℂ) + Complex.I‖ ≠ 0 :=
    (mul_pos (norm_ofReal_add_I_pos t) (norm_ofReal_add_I_pos x)).ne'
  simp only [cayleyBoundaryPoint_sub, norm_div, norm_mul, div_mul_cancel₀ _ hProd,
    Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  norm_num

private theorem norm_ofReal_add_I_le (t x : ℝ) :
    ‖(t : ℂ) + Complex.I‖ ≤ |t - x| + ‖(x : ℂ) + Complex.I‖ := by
  calc
    _ = ‖((t - x : ℝ) : ℂ) + ((x : ℂ) + Complex.I)‖ := by
      rw [Complex.ofReal_sub, ← add_assoc, sub_add_cancel]
    _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le ((t - x : ℝ) : ℂ) ((x : ℂ) + Complex.I)

private theorem norm_radial_herglotzRieszKernel_mul_abs_sub_le {t x s : ℝ} (htx : t ≠ x)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ‖herglotzRieszKernel 0 ((s : ℂ) * cayleyBoundaryPoint x) (cayleyBoundaryPoint t)‖ * |t - x| ≤
      2 * ‖(x : ℂ) + Complex.I‖ * (|t - x| + ‖(x : ℂ) + Complex.I‖) := by
  let a := cayleyBoundaryPoint t
  let b := cayleyBoundaryPoint x
  let w := (s : ℂ) * b
  let X := ‖(x : ℂ) + Complex.I‖
  let T := ‖(t : ℂ) + Complex.I‖
  have ha : ‖a‖ = 1 := norm_cayleyBoundaryPoint t
  have hb : ‖b‖ = 1 := norm_cayleyBoundaryPoint x
  have hMain := mul_le_mul_of_nonneg_right (norm_sub_le_twice_norm_sub_radial ha hb hs₀ hs₁)
    (show 0 ≤ T * X by positivity)
  change ‖cayleyBoundaryPoint t - cayleyBoundaryPoint x‖ * _ ≤ _ at hMain
  rw [norm_cayleyBoundaryPoint_sub_mul] at hMain
  have hDen : 0 < ‖a - w‖ := by
    apply norm_pos_iff.mpr
    intro he
    change 2 * |t - x| ≤ 2 * ‖a - w‖ * (T * X) at hMain
    rw [he, norm_zero, mul_zero, zero_mul] at hMain
    exact (not_le_of_gt (mul_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr htx)))) hMain
  have hNum : ‖a + w‖ ≤ 2 := by
    have hTri := norm_add_le a w
    have hw : ‖w‖ = s := by
      dsimp only [w]
      rw [norm_mul, Complex.norm_real, hb, mul_one, Real.norm_of_nonneg hs₀]
    rw [ha, hw] at hTri
    linarith only [hs₁, hTri]
  change ‖herglotzRieszKernel 0 w a‖ * |t - x| ≤ 2 * X * (|t - x| + X)
  rw [herglotzRieszKernel_def, sub_zero, sub_zero, norm_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hDen).2
  calc
    _ ≤ 2 * |t - x| := mul_le_mul_of_nonneg_right hNum (abs_nonneg _)
    _ ≤ 2 * ‖a - w‖ * (T * X) := hMain
    _ ≤ 2 * ‖a - w‖ * ((|t - x| + X) * X) := by
      gcongr
      exact norm_ofReal_add_I_le t x
    _ = _ := by ring

/-- The boundary conjugate of a weighted datum has its compensated
radial limit wherever the datum has a local first-order bound. -/
theorem tendsto_im_weightedDiskHerglotzIntegral_radial_of_local_bound
    {u : ℝ → ℝ} (hu : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    (x : ℝ) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hLocal : ∀ t : ℝ, |t - x| < δ → |u t - u x| ≤ C * |t - x|) :
    Tendsto (fun s : ℝ => (weightedDiskHerglotzIntegral u ((s : ℂ) * cayleyBoundaryPoint x)).im)
      (𝓝[<] (1 : ℝ))
      (𝓝 (weightedDiskHerglotzIntegral (fun t => u t - u x) (cayleyBoundaryPoint x)).im) := by
  let w (s : ℝ) := (s : ℂ) * cayleyBoundaryPoint x
  let k (s t : ℝ) := herglotzRieszKernel 0 (w s) (cayleyBoundaryPoint t)
  let g (t : ℝ) := Real.pi⁻¹ * ((u t - u x) / (1 + t ^ 2))
  let K (s t : ℝ) := k s t * (g t : ℂ)
  let X := ‖(x : ℂ) + Complex.I‖
  let A := Real.pi⁻¹ * C * (2 * X * (δ + X))
  let B := 2 * X * (1 + X / δ)
  let W (t : ℝ) := A * (1 + t ^ 2)⁻¹ + B * ‖g t‖
  have hConst : Integrable (fun t : ℝ => u x / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (u x)
  have hg : Integrable g := by
    have hU : Integrable (fun t : ℝ => (u t - u x) / (1 + t ^ 2)) := by
      convert hu.sub hConst using 1
      funext t
      exact sub_div _ _ _
    exact hU.const_mul _
  have hW : Integrable W := (integrable_inv_one_add_sq.const_mul A).add (hg.norm.const_mul B)
  have hs : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ s ∧ s < 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin (s := Iio (1 : ℝ))] with s hs₀ hs₁
    exact ⟨hs₀.le, hs₁⟩
  have hMeas (s : ℝ) : AEStronglyMeasurable (K s) := by
    have hK : Measurable (k s) := by
      simp only [k, herglotzRieszKernel_def, sub_zero]
      exact (continuous_cayleyBoundaryPoint.measurable.add measurable_const).div
        (continuous_cayleyBoundaryPoint.measurable.sub measurable_const)
    exact hK.aestronglyMeasurable.mul (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  have hMajor (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (t : ℝ) : ‖K s t‖ ≤ W t := by
    by_cases htx : t = x
    · subst t
      have hNonneg : 0 ≤ W x := by dsimp [W, A, B]; positivity
      simpa [K, g] using hNonneg
    have hRad : ‖k s t‖ * |t - x| ≤ 2 * X * (|t - x| + X) :=
      norm_radial_herglotzRieszKernel_mul_abs_sub_le htx hs₀ hs₁
    have hNorm : ‖K s t‖ = ‖k s t‖ * ‖g t‖ := by
      simp only [K, norm_mul, Complex.norm_real]
    rw [hNorm]
    by_cases ht : |t - x| < δ
    · let p := (1 + t ^ 2)⁻¹
      have hp : 0 ≤ p := by dsimp [p]; positivity
      have hData : ‖g t‖ ≤ Real.pi⁻¹ * p * (C * |t - x|) := by
        calc
          _ = Real.pi⁻¹ * p * |u t - u x| := by
            dsimp only [g, p]
            rw [div_eq_mul_inv, norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr Real.pi_pos.le),
              Real.norm_of_nonneg hp, Real.norm_eq_abs]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hLocal t ht) (by positivity)
      calc
        _ ≤ ‖k s t‖ * (Real.pi⁻¹ * p * (C * |t - x|)) :=
          mul_le_mul_of_nonneg_left hData (norm_nonneg _)
        _ = (Real.pi⁻¹ * p * C) * (‖k s t‖ * |t - x|) := by ring
        _ ≤ (Real.pi⁻¹ * p * C) * (2 * X * (δ + X)) :=
          mul_le_mul_of_nonneg_left (hRad.trans (by gcongr)) (by positivity)
        _ = A * p := by dsimp [A]; ring
        _ ≤ W t := le_add_of_nonneg_right (by dsimp [B]; positivity)
    · have htFar : δ ≤ |t - x| := le_of_not_gt ht
      have hX : X ≤ (X / δ) * |t - x| := by
        calc
          X = (X / δ) * δ := (div_mul_cancel₀ X hδ.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left htFar (by positivity)
      have hBound : ‖k s t‖ ≤ B := by
        apply (mul_le_mul_iff_of_pos_right (hδ.trans_le htFar)).mp
        calc
          _ ≤ 2 * X * (|t - x| + X) := hRad
          _ ≤ 2 * X * (|t - x| + (X / δ) * |t - x|) := by gcongr
          _ = _ := by dsimp [B]; ring
      exact (mul_le_mul_of_nonneg_right hBound (norm_nonneg _)).trans
        (le_add_of_nonneg_left (by dsimp [A]; positivity))
  have hAt (t : ℝ) : Tendsto (fun s : ℝ => K s t) (𝓝[<] (1 : ℝ)) (𝓝 (K 1 t)) := by
    by_cases ht : t = x
    · subst t
      simp [K, g]
    have hwc : Continuous w := Complex.continuous_ofReal.mul continuous_const
    have hDen : cayleyBoundaryPoint t - w 1 ≠ 0 := by
      simpa only [w, Complex.ofReal_one, one_mul] using sub_ne_zero.mpr (cayleyBoundaryPoint_injective.ne ht)
    have hk : ContinuousAt (fun s : ℝ => k s t) 1 := by
      simp only [k, herglotzRieszKernel_def, sub_zero]
      exact (continuousAt_const.add hwc.continuousAt).div
        (continuousAt_const.sub hwc.continuousAt) hDen
    exact (hk.mul continuousAt_const).continuousWithinAt
  have hComp : Tendsto (fun s : ℝ => weightedDiskHerglotzIntegral
      (fun t => u t - u x) (w s)) (𝓝[<] (1 : ℝ))
      (𝓝 (weightedDiskHerglotzIntegral (fun t => u t - u x) (w 1))) :=
    tendsto_integral_filter_of_dominated_convergence W (Eventually.of_forall hMeas)
      (hs.mono fun s h => ae_of_all _ (hMajor s h.1 h.2.le)) hW (ae_of_all _ hAt)
  have hIm := Complex.continuous_im.continuousAt.tendsto.comp hComp
  rw [show w 1 = cayleyBoundaryPoint x by simp [w]] at hIm
  apply hIm.congr'
  filter_upwards [hs] with s hs'
  have hInside : ‖w s‖ < 1 := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, norm_cayleyBoundaryPoint, mul_one,
      Real.norm_of_nonneg hs'.1]
    exact hs'.2
  change (weightedDiskHerglotzIntegral (fun t => u t - u x) (w s)).im =
    (weightedDiskHerglotzIntegral u (w s)).im
  rw [weightedDiskHerglotzIntegral_sub hu hConst hInside, weightedDiskHerglotzIntegral_const hInside,
    Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- The compensated boundary value of the conjugate integral. -/
def weightedDiskHerglotzBoundaryConjugate (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (weightedDiskHerglotzIntegral (fun t => u t - u x) (cayleyBoundaryPoint x)).im

/-- A differentiable real datum has the compensated conjugate limit at
the point of differentiability. -/
theorem tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt
    {u : ℝ → ℝ} (hu : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    {x : ℝ} (hx : DifferentiableAt ℝ u x) :
    Tendsto (fun s : ℝ => (weightedDiskHerglotzIntegral u ((s : ℂ) * cayleyBoundaryPoint x)).im)
      (𝓝[<] (1 : ℝ)) (𝓝 (weightedDiskHerglotzBoundaryConjugate u x)) := by
  obtain ⟨C, hC, hO⟩ := hx.isBigO_sub.exists_nonneg
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff.mp hO.bound
  refine tendsto_im_weightedDiskHerglotzIntegral_radial_of_local_bound hu x hδ hC ?_
  intro t ht
  have hDist : dist t x < δ := by simpa only [Real.dist_eq] using ht
  simpa only [Real.norm_eq_abs] using hB hDist

/-- The compensated conjugate is a measurable function of the real
boundary point for every measurable datum. -/
theorem measurable_weightedDiskHerglotzBoundaryConjugate {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (weightedDiskHerglotzBoundaryConjugate u) := by
  let K (p : ℝ × ℝ) := herglotzRieszKernel 0 (cayleyBoundaryPoint p.1) (cayleyBoundaryPoint p.2)
  let g (p : ℝ × ℝ) := Real.pi⁻¹ * ((u p.2 - u p.1) / (1 + p.2 ^ 2))
  have hFst : Measurable (fun p : ℝ × ℝ => cayleyBoundaryPoint p.1) :=
    continuous_cayleyBoundaryPoint.measurable.comp measurable_fst
  have hSnd : Measurable (fun p : ℝ × ℝ => cayleyBoundaryPoint p.2) :=
    continuous_cayleyBoundaryPoint.measurable.comp measurable_snd
  have hK : Measurable K := by
    simp only [K, herglotzRieszKernel_def, sub_zero]
    exact (hSnd.add hFst).div (hSnd.sub hFst)
  have hg : Measurable g := by
    dsimp only [g]
    exact measurable_const.mul (((hu.comp measurable_snd).sub (hu.comp measurable_fst)).div
      (measurable_const.add (measurable_snd.pow_const _)))
  have hMeas : Measurable (fun p : ℝ × ℝ => K p * (g p : ℂ)) :=
    hK.mul (Complex.continuous_ofReal.measurable.comp hg)
  exact Complex.continuous_im.measurable.comp
    (hMeas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

private def cayleyRealBoundaryCoordinate (θ : ℝ) : ℝ :=
  Real.tan ((θ - Real.pi) / 2)

private theorem measurable_cayleyRealBoundaryCoordinate :
    Measurable cayleyRealBoundaryCoordinate := by
  have h : Measurable (fun θ : ℝ => (θ - Real.pi) / 2) :=
    (measurable_id.sub_const _).div_const _
  have he : cayleyRealBoundaryCoordinate =
      (fun θ : ℝ => Real.sin ((θ - Real.pi) / 2) / Real.cos ((θ - Real.pi) / 2)) := by
    funext θ
    exact Real.tan_eq_sin_div_cos ((θ - Real.pi) / 2)
  rw [he]
  exact (Real.continuous_sin.measurable.comp h).div (Real.continuous_cos.measurable.comp h)

private theorem cayleyBoundaryAngle_cayleyRealBoundaryCoordinate {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    cayleyBoundaryAngle (cayleyRealBoundaryCoordinate θ) = θ := by
  have hLow : -(Real.pi / 2) < (θ - Real.pi) / 2 := by linarith only [hθ.1]
  have hHigh : (θ - Real.pi) / 2 < Real.pi / 2 := by linarith only [hθ.2]
  rw [cayleyBoundaryAngle, cayleyRealBoundaryCoordinate, Real.arctan_tan hLow hHigh]
  ring

private theorem circleMap_eq_mul_cayleyBoundaryPoint (s x : ℝ) :
    circleMap 0 s (cayleyBoundaryAngle x) = (s : ℂ) * cayleyBoundaryPoint x := by
  simp only [cayleyBoundaryPoint, circleMap_zero, Complex.ofReal_one, one_mul]

/-- For a measurable weighted datum differentiable off a countable set,
its compensated conjugate supplies a measurable angular radial limit. -/
theorem exists_angular_weightedDiskHerglotz_radial_limit
    {u : ℝ → ℝ} (hu : Measurable u)
    (huInt : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    {E : Set ℝ} (hE : E.Countable)
    (hDiff : ∀ x ∉ E, DifferentiableAt ℝ u x)
    (ρ : ℕ → ℝ) (hρ₁ : ∀ n, ρ n < 1) (hρ : Tendsto ρ atTop (𝓝 1)) :
    ∃ v : ℝ → ℝ, Measurable v ∧
      (∀ x, v (cayleyBoundaryAngle x) = weightedDiskHerglotzBoundaryConjugate u x) ∧
      ∀ᵐ θ ∂diskAngleMeasure, Tendsto
        (fun n : ℕ => (weightedDiskHerglotzIntegral u (circleMap 0 (ρ n) θ)).im)
        atTop (𝓝 (v θ)) := by
  let v := weightedDiskHerglotzBoundaryConjugate u ∘ cayleyRealBoundaryCoordinate
  refine ⟨v, (measurable_weightedDiskHerglotzBoundaryConjugate hu).comp
    measurable_cayleyRealBoundaryCoordinate, ?_, ?_⟩
  · intro x
    have he : (cayleyBoundaryAngle x - Real.pi) / 2 = Real.arctan x := by
      unfold cayleyBoundaryAngle
      ring
    simp only [v, Function.comp_apply, cayleyRealBoundaryCoordinate, he, Real.tan_arctan]
  have hAngle : ∀ᵐ θ ∂diskAngleMeasure, θ ∈ Ioo 0 (2 * Real.pi) :=
    ae_restrict_mem measurableSet_Ioo
  have hNot : ∀ᵐ θ ∂diskAngleMeasure, θ ∉ cayleyBoundaryAngle '' E := by
    rw [ae_iff]
    simp only [not_not, diskAngleMeasure]
    exact (hE.image cayleyBoundaryAngle).measure_zero _
  have hAlong : Tendsto ρ atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ρ hρ (Eventually.of_forall hρ₁)
  filter_upwards [hAngle, hNot] with θ hθ hθE
  let x := cayleyRealBoundaryCoordinate θ
  have hxθ : cayleyBoundaryAngle x = θ := cayleyBoundaryAngle_cayleyRealBoundaryCoordinate hθ
  have hxE : x ∉ E := fun hx => hθE ⟨x, hx, hxθ⟩
  have ht := (tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt huInt
    (hDiff x hxE)).comp hAlong
  have hEqual (n : ℕ) : circleMap 0 (ρ n) θ = (ρ n : ℂ) * cayleyBoundaryPoint x := by
    exact (congrArg (circleMap 0 (ρ n)) hxθ.symm).trans
      (circleMap_eq_mul_cayleyBoundaryPoint (ρ n) x)
  simpa only [hEqual, Function.comp_def, v, x] using ht

/-- The weighted logarithmic tail of a nonzero entire function has a
measurable angular conjugate boundary value. Its only exceptional real
points are contained in the real zero set and the two cutoff sites. -/
theorem exists_angular_weightedDiskHerglotz_log_tail_radial_limit
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF₀ : ∃ z, F z ≠ 0)
    (hInt : Integrable (fun x : ℝ => |Real.log ‖F (x : ℂ)‖| / (1 + x ^ 2)))
    (R : ℝ) (ρ : ℕ → ℝ) (hρ₁ : ∀ n, ρ n < 1) (hρ : Tendsto ρ atTop (𝓝 1)) :
    let u := {x : ℝ | R ≤ |x|}.indicator (fun x => Real.log ‖F (x : ℂ)‖)
    Integrable (fun x : ℝ => u x / (1 + x ^ 2)) ∧
    (∫ x : ℝ, ‖u x / (1 + x ^ 2)‖) =
      (∫ x in {x : ℝ | R ≤ |x|}, |Real.log ‖F (x : ℂ)‖| / (1 + x ^ 2)) ∧
    ∃ v : ℝ → ℝ, Measurable v ∧
      (∀ x, v (cayleyBoundaryAngle x) = weightedDiskHerglotzBoundaryConjugate u x) ∧
      ∀ᵐ θ ∂diskAngleMeasure, Tendsto
        (fun n : ℕ => (weightedDiskHerglotzIntegral u (circleMap 0 (ρ n) θ)).im)
        atTop (𝓝 (v θ)) := by
  let S := {x : ℝ | R ≤ |x|}
  let U (x : ℝ) := Real.log ‖F (x : ℂ)‖
  let u := S.indicator U
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hUmeas : Measurable U := Real.measurable_log.comp
    (hF.continuous.comp Complex.continuous_ofReal).norm.measurable
  have hu : Measurable u := hUmeas.indicator hS
  have hU : Integrable (fun x : ℝ => U x / (1 + x ^ 2)) := by
    refine hInt.mono' (hUmeas.div (measurable_const.add (measurable_id.pow_const _))).aestronglyMeasurable ?_
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
  have huInt : Integrable (fun x : ℝ => u x / (1 + x ^ 2)) := by
    have he : (fun x : ℝ => u x / (1 + x ^ 2)) =
        S.indicator (fun x : ℝ => U x / (1 + x ^ 2)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [u, hx]
    rw [he]
    exact hU.indicator hS
  have hMass : (∫ x : ℝ, ‖u x / (1 + x ^ 2)‖) = ∫ x in S, |U x| / (1 + x ^ 2) := by
    have he : (fun x : ℝ => ‖u x / (1 + x ^ 2)‖) =
        S.indicator (fun x : ℝ => |U x| / (1 + x ^ 2)) := by
      funext x
      by_cases hx : x ∈ S
      · simp only [u, indicator_of_mem hx, Real.norm_eq_abs, abs_div,
          abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
      · simp [u, hx]
    rw [he, integral_indicator hS]
  refine ⟨huInt, hMass, ?_⟩
  have hAnalytic : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z, hz⟩ := hF₀
  have hCodisc : (F ⁻¹' {(0 : ℂ)})ᶜ ∈ codiscrete ℂ := by
    rw [← preimage_compl]
    exact hAnalytic.preimage_zero_mem_codiscrete hz
  have hCount : (F ⁻¹' {(0 : ℂ)}).Countable := by
    have : DiscreteTopology (F ⁻¹' {(0 : ℂ)} : Set ℂ) :=
      isDiscrete_iff_discreteTopology.mp (compl_mem_codiscrete_iff.mp hCodisc).2
    exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hZeros : {x : ℝ | F (x : ℂ) = 0}.Countable :=
    hCount.preimage Complex.ofReal_injective
  have hCut : {x : ℝ | |x| = R}.Countable := by
    refine ((countable_singleton (-R)).insert R).mono ?_
    intro x hx
    change |x| = R at hx
    rcases abs_choice x with h | h
    · exact Or.inl (h.symm.trans hx)
    · exact Or.inr (show x = -R by linarith)
  refine exists_angular_weightedDiskHerglotz_radial_limit hu huInt
    (hZeros.union hCut) ?_ ρ hρ₁ hρ
  intro x hx
  have hzₓ : F (x : ℂ) ≠ 0 := fun h => hx (Or.inl h)
  have hCutₓ : |x| ≠ R := fun h => hx (Or.inr h)
  rcases lt_or_gt_of_ne hCutₓ with hSmall | hLarge
  · have hEq : u =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [continuous_abs.continuousAt.eventually_lt (continuousAt_const (y := R)) hSmall]
        with y hy
      exact indicator_of_notMem (show y ∉ S from not_le_of_gt hy) U
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hEq
  · have hEq : u =ᶠ[𝓝 x] U := by
      filter_upwards [(continuousAt_const (y := R)).eventually_lt continuous_abs.continuousAt hLarge]
        with y hy
      exact indicator_of_mem (show y ∈ S from le_of_lt hy) U
    have hFreal : DifferentiableAt ℝ (fun y : ℝ => F (y : ℂ)) x :=
      ((hF (x : ℂ)).restrictScalars ℝ).comp x Complex.ofRealCLM.differentiableAt
    exact ((hFreal.norm ℂ hzₓ).log (norm_ne_zero_iff.mpr hzₓ)).congr_of_eventuallyEq hEq

end
end MeyerGeneralProblem
