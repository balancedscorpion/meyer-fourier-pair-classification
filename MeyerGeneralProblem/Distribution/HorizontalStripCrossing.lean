module

public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Homotopy
public import TauCeti.Analysis.Contour.Winding.Number.Reparam
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-!
# Crossing paths in a horizontal strip

The normalized difference along the parameter square would connect
opposite semicircles by a homotopy avoiding zero if the vertical paths
were disjoint and reversed their horizontal endpoint order.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set TauCeti.Contour
open scoped unitInterval

private def semicircleAngle (positive : Bool) : ℝ :=
  if positive then Real.pi else -Real.pi

private def signedUnitSemicircle (positive : Bool) : Path (1 : ℂ) (-1) where
  toFun t := circleMap 0 1 (semicircleAngle positive * (t : ℝ))
  continuous_toFun := (continuous_circleMap 0 1).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [circleMap]
  target' := by
    cases positive <;> simp [semicircleAngle, circleMap, Complex.exp_neg, Complex.exp_pi_mul_I, neg_mul]

private theorem semicircle_im_sign (positive : Bool) (t : I) (h₀ : t ≠ 0) (h₁ : t ≠ 1) :
    0 < (if positive then (1 : ℝ) else -1) * (signedUnitSemicircle positive t).im := by
  have ht₀ : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1 (fun h => h₀ (Subtype.ext h.symm))
  have ht₁ : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2 (fun h => h₁ (Subtype.ext h))
  have hangle : 0 < Real.pi * (t : ℝ) := mul_pos Real.pi_pos ht₀
  have hlt : Real.pi * (t : ℝ) < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht₁ Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hangle hlt
  cases positive <;>
    simpa [signedUnitSemicircle, semicircleAngle, circleMap, Complex.exp_im, Real.sin_neg, neg_mul]
      using hs

private theorem signedUnitSemicircle_piecewise (positive : Bool) :
    IsPiecewiseC1On (signedUnitSemicircle positive).extend 0 1 := by
  let γ (t : ℝ) := circleMap 0 1 (semicircleAngle positive * t)
  have hγ : ContDiff ℝ 1 γ :=
    (contDiff_circleMap 0 1).comp (show ContDiff ℝ 1 (fun t : ℝ => semicircleAngle positive * t) by fun_prop)
  apply IsPiecewiseC1On.of_contDiffOn
  apply hγ.contDiffOn.congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  rw [Path.extend_apply _ ht]
  rfl

private theorem windingNumber_signedUnitSemicircle (positive : Bool) :
    windingNumber (signedUnitSemicircle positive).extend 0 1 0 =
      (semicircleAngle positive : ℂ) / (2 * (Real.pi : ℂ)) := by
  let γ (t : ℝ) := circleMap 0 1 (semicircleAngle positive * t)
  have hAgree : EqOn (signedUnitSemicircle positive).extend γ (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [Path.extend_apply _ ht]
    rfl
  have hMove := windingNumber_comp_mul_add (γ := circleMap 0 1) (a := (0 : ℝ)) (b := 1)
    (r := semicircleAngle positive) (s := 0) (z₀ := (0 : ℂ))
    (fun θ _ => (hasDerivAt_circleMap 0 1 θ).differentiableAt)
    (by
      have h : Continuous (fun θ : ℝ => deriv (circleMap 0 1) θ) := by
        simp only [deriv_circleMap]
        exact (continuous_circleMap 0 1).mul continuous_const
      exact h.continuousOn)
    (fun θ _ => circleMap_ne_center one_ne_zero)
  have hMove' : windingNumber γ 0 1 0 = windingNumber (circleMap 0 1) 0 (semicircleAngle positive) 0 := by
    simpa only [γ, Function.comp_def, mul_zero, zero_add, mul_one, add_zero] using hMove
  have hSub : uIoo (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIoo_of_le zero_le_one, uIcc_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  rw [windingNumber_congr_curve (hAgree.mono hSub),
    hMove', windingNumber_circleMap_center one_ne_zero, sub_zero]

private theorem no_avoiding_homotopy_signedUnitSemicircles
    (H : (signedUnitSemicircle true).Homotopy (signedUnitSemicircle false))
    (hAvoid : ∀ z : I × I, H z ≠ 0) : False := by
  have hw := windingNumber_eq_of_pathHomotopy H
    (signedUnitSemicircle_piecewise true) (signedUnitSemicircle_piecewise false) hAvoid
  rw [windingNumber_signedUnitSemicircle, windingNumber_signedUnitSemicircle] at hw
  have hden : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have ht := congrArg (fun z : ℂ => z * (2 * (Real.pi : ℂ))) hw
  simp only [div_mul_cancel₀ _ hden] at ht
  have hre := congrArg Complex.re ht
  simp [semicircleAngle] at hre
  linarith [Real.pi_pos]

private def halfPlanePathHomotopy {a b : ℂ} (p q : Path a b) : p.Homotopy q where
  toFun z := ((1 - (z.1 : ℝ) : ℝ) : ℂ) * p z.2 + ((z.1 : ℝ) : ℂ) * q z.2
  continuous_toFun := by fun_prop
  map_zero_left := by intro s; simp
  map_one_left := by intro s; simp
  prop' r s hs := by
    rcases (show s = 0 ∨ s = 1 by simpa only [mem_insert_iff, mem_singleton_iff] using hs) with rfl | rfl
    · change ((1 - (r : ℝ) : ℝ) : ℂ) * p 0 + ((r : ℝ) : ℂ) * q 0 = p 0
      simp only [Path.source, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · change ((1 - (r : ℝ) : ℝ) : ℂ) * p 1 + ((r : ℝ) : ℂ) * q 1 = p 1
      simp only [Path.target, Complex.ofReal_sub, Complex.ofReal_one]
      ring

private theorem halfPlanePathHomotopy_avoids_zero {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) {p q : Path a b} {sign : ℝ}
    (hp : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < sign * (p s).im)
    (hq : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < sign * (q s).im) :
    ∀ z : I × I, halfPlanePathHomotopy p q z ≠ 0 := by
  rintro ⟨r, s⟩
  by_cases hs₀ : s = 0
  · subst s
    have he : halfPlanePathHomotopy p q (r, 0) = a := by
      change ((1 - (r : ℝ) : ℝ) : ℂ) * p 0 + ((r : ℝ) : ℂ) * q 0 = a
      simp only [Path.source, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rwa [he]
  by_cases hs₁ : s = 1
  · subst s
    have he : halfPlanePathHomotopy p q (r, 1) = b := by
      change ((1 - (r : ℝ) : ℝ) : ℂ) * p 1 + ((r : ℝ) : ℂ) * q 1 = b
      simp only [Path.target, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rwa [he]
  have hp' := hp s hs₀ hs₁
  have hq' := hq s hs₀ hs₁
  have hSign : 0 < sign * (halfPlanePathHomotopy p q (r, s)).im := by
    change 0 < sign * (((1 - (r : ℝ) : ℝ) : ℂ) * p s + ((r : ℝ) : ℂ) * q s).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [show sign * ((1 - (r : ℝ)) * (p s).im + (r : ℝ) * (q s).im) =
      (1 - (r : ℝ)) * (sign * (p s).im) + (r : ℝ) * (sign * (q s).im) by ring]
    by_cases hr : (r : ℝ) = 0
    · simpa only [hr, sub_zero, one_mul, zero_mul, add_zero] using hp'
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr r.property.2) hp'.le)
        (mul_pos (lt_of_le_of_ne r.property.1 (fun he => hr he.symm)) hq')
  intro hZero
  simp only [hZero, Complex.zero_im, mul_zero, lt_irrefl] at hSign

private theorem pathHomotopy_trans_avoids_zero {a b : ℂ} {p q r : Path a b}
    (H₁ : p.Homotopy q) (H₂ : q.Homotopy r)
    (h₁ : ∀ z : I × I, H₁ z ≠ 0) (h₂ : ∀ z : I × I, H₂ z ≠ 0) :
    ∀ z : I × I, H₁.trans H₂ z ≠ 0 := by
  intro z
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact h₁ _
  · exact h₂ _

private def squareParameterUp (s : I) : I :=
  ⟨min 1 (2 * (s : ℝ)), le_min zero_le_one (by have := s.property.1; positivity), min_le_left _ _⟩

private def squareParameterDown (s : I) : I :=
  ⟨max 0 (2 * (s : ℝ) - 1), le_max_left _ _,
    max_le zero_le_one (by linarith [s.property.2])⟩

private def squareUpperPath : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) where
  toFun s := (squareParameterUp s, squareParameterDown s)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_const.min (continuous_const.mul continuous_subtype_val)).subtype_mk _
    · exact (continuous_const.max ((continuous_const.mul continuous_subtype_val).sub
        continuous_const)).subtype_mk _
  source' := by
    apply Prod.ext <;> apply Subtype.ext <;> norm_num [squareParameterUp, squareParameterDown]
  target' := by
    apply Prod.ext <;> apply Subtype.ext <;> norm_num [squareParameterUp, squareParameterDown]

private def squareLowerPath : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) :=
  squareUpperPath.map continuous_swap

private theorem upper_difference_im_pos {p q : I → ℂ} {T : ℝ}
    (hp : (p 1).im = T) (hq : (q 0).im = 0)
    (hpAbove : ∀ u : I, u ≠ 0 → 0 < (p u).im)
    (hqBelow : ∀ u : I, u ≠ 1 → (q u).im < T)
    (s : I) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    0 < (p (squareParameterUp s) - q (squareParameterDown s)).im := by
  have hsLo : 0 < (s : ℝ) :=
    lt_of_le_of_ne s.property.1 (fun he => hs₀ (Subtype.ext he.symm))
  have hsHi : (s : ℝ) < 1 :=
    lt_of_le_of_ne s.property.2 (fun he => hs₁ (Subtype.ext he))
  rw [Complex.sub_im]
  by_cases hMid : (s : ℝ) ≤ 1 / 2
  · have hd : squareParameterDown s = 0 := by
      apply Subtype.ext
      change max 0 (2 * (s : ℝ) - 1) = 0
      exact max_eq_left (by linarith)
    have hUp : 0 < (squareParameterUp s : ℝ) := lt_min zero_lt_one (by positivity)
    have hu : squareParameterUp s ≠ 0 := fun he => hUp.ne' (congrArg Subtype.val he)
    rw [hd, hq, sub_zero]
    exact hpAbove _ hu
  · have hu : squareParameterUp s = 1 := by
      apply Subtype.ext
      change min 1 (2 * (s : ℝ)) = 1
      exact min_eq_left (by linarith [lt_of_not_ge hMid])
    have hDown : (squareParameterDown s : ℝ) < 1 := max_lt zero_lt_one (by linarith)
    have hd : squareParameterDown s ≠ 1 := fun he => hDown.ne (congrArg Subtype.val he)
    rw [hu, hp]
    exact sub_pos.mpr (hqBelow _ hd)

private def normalizedComplexDirection (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

private theorem normalizedComplexDirection_nonzero {z : ℂ} (hz : z ≠ 0) :
    normalizedComplexDirection z ≠ 0 :=
  div_ne_zero hz (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

private theorem normalizedComplexDirection_eq_one {z : ℂ}
    (hz : z.im = 0) (hpos : 0 < z.re) : normalizedComplexDirection z = 1 := by
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hz)
  unfold normalizedComplexDirection
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact div_self (Complex.ofReal_ne_zero.mpr hpos.ne')

private theorem normalizedComplexDirection_eq_neg_one {z : ℂ}
    (hz : z.im = 0) (hneg : z.re < 0) : normalizedComplexDirection z = -1 := by
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hz)
  unfold normalizedComplexDirection
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg, Complex.ofReal_neg, div_neg,
    div_self (Complex.ofReal_ne_zero.mpr hneg.ne)]

private theorem normalizedComplexDirection_im_sign {z : ℂ} {sign : ℝ}
    (hSign : 0 < sign * z.im) : 0 < sign * (normalizedComplexDirection z).im := by
  have hz : z ≠ 0 := by
    intro he
    simp [he] at hSign
  rw [normalizedComplexDirection, Complex.div_ofReal_im, ← mul_div_assoc]
  exact div_pos hSign (norm_pos_iff.mpr hz)

/-- Two continuous paths in the open horizontal strip between their
endpoints intersect when their bottom endpoint order reverses at the
top. The argument applies even when the paths revisit interior points. -/
theorem exists_eq_of_reversed_paths_across_horizontal_strip
    (p q : I → ℂ) (hp : Continuous p) (hq : Continuous q) {T : ℝ} (hT : 0 < T)
    (hp₀ : (p 0).im = 0) (hq₀ : (q 0).im = 0)
    (hp₁ : (p 1).im = T) (hq₁ : (q 1).im = T)
    (hpInside : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < (p s).im ∧ (p s).im < T)
    (hqInside : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < (q s).im ∧ (q s).im < T)
    (hStart : (q 0).re < (p 0).re) (hEnd : (p 1).re < (q 1).re) :
    ∃ s t : I, p s = q t := by
  by_contra! hDisjoint
  let F (z : I × I) := p z.1 - q z.2
  have hF : Continuous F := (hp.comp continuous_fst).sub (hq.comp continuous_snd)
  have hFN (z : I × I) : F z ≠ 0 := sub_ne_zero.mpr (hDisjoint z.1 z.2)
  let N : C(I × I, ℂ) :=
    ⟨fun z => normalizedComplexDirection (F z),
      hF.div (Complex.continuous_ofReal.comp hF.norm) fun z =>
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hFN z))⟩
  have hN (z : I × I) : N z ≠ 0 := normalizedComplexDirection_nonzero (hFN z)
  have hStartN : N (0, 0) = 1 :=
    normalizedComplexDirection_eq_one (by simp [F, Complex.sub_im, hp₀, hq₀]) (sub_pos.mpr hStart)
  have hEndN : N (1, 1) = -1 :=
    normalizedComplexDirection_eq_neg_one (by simp [F, Complex.sub_im, hp₁, hq₁]) (sub_neg.mpr hEnd)
  let P : Path (1 : ℂ) (-1) := (squareUpperPath.map N.continuous).cast hStartN.symm hEndN.symm
  let Q : Path (1 : ℂ) (-1) := (squareLowerPath.map N.continuous).cast hStartN.symm hEndN.symm
  have hAbove {u : I → ℂ} (h₁ : (u 1).im = T)
      (h : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < (u s).im ∧ (u s).im < T)
      (s : I) (hs : s ≠ 0) : 0 < (u s).im := by
    by_cases he : s = 1
    · exact he ▸ h₁ ▸ hT
    · exact (h s hs he).1
  have hBelow {u : I → ℂ} (h₀ : (u 0).im = 0)
      (h : ∀ s : I, s ≠ 0 → s ≠ 1 → 0 < (u s).im ∧ (u s).im < T)
      (s : I) (hs : s ≠ 1) : (u s).im < T := by
    by_cases he : s = 0
    · exact he ▸ h₀ ▸ hT
    · exact (h s he hs).2
  have hP (s : I) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : 0 < (1 : ℝ) * (P s).im := by
    apply normalizedComplexDirection_im_sign
    simp only [one_mul]
    exact upper_difference_im_pos hp₁ hq₀ (hAbove hp₁ hpInside) (hBelow hq₀ hqInside) s hs₀ hs₁
  have hQ (s : I) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : 0 < (-1 : ℝ) * (Q s).im := by
    apply normalizedComplexDirection_im_sign
    change 0 < (-1 : ℝ) * (p (squareParameterDown s) - q (squareParameterUp s)).im
    simp only [neg_one_mul, Complex.sub_im, neg_sub]
    simpa only [Complex.sub_im] using
      upper_difference_im_pos hq₁ hp₀ (hAbove hq₁ hqInside) (hBelow hp₀ hpInside) s hs₀ hs₁
  let _ : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_le_one⟩
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic squareUpperPath squareLowerPath
  let Hmid : P.Homotopy Q := (H.map N).pathCast hStartN.symm hEndN.symm
  have hMid : ∀ z : I × I, Hmid z ≠ 0 := fun z => hN (H z)
  let H₁ := halfPlanePathHomotopy (signedUnitSemicircle true) P
  let H₃ := halfPlanePathHomotopy Q (signedUnitSemicircle false)
  have h₁ : ∀ z : I × I, H₁ z ≠ 0 :=
    halfPlanePathHomotopy_avoids_zero one_ne_zero (by norm_num)
      (by simpa using semicircle_im_sign true) hP
  have h₃ : ∀ z : I × I, H₃ z ≠ 0 :=
    halfPlanePathHomotopy_avoids_zero one_ne_zero (by norm_num)
      hQ (by simpa using semicircle_im_sign false)
  exact no_avoiding_homotopy_signedUnitSemicircles ((H₁.trans Hmid).trans H₃)
    (pathHomotopy_trans_avoids_zero _ _ (pathHomotopy_trans_avoids_zero _ _ h₁ hMid) h₃)

end
end MeyerGeneralProblem
