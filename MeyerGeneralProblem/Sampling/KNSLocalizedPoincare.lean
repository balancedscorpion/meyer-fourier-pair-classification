module

public import MeyerGeneralProblem.Sampling.KNSLocalizerRegularity
public import MeyerGeneralProblem.Sampling.ConvexFourierPoincare

@[expose] public section

/-!
# Actual KNS localization on reciprocal tail gaps

The entire real line is covered by the genuine consecutive intervals of a
two-sided carrier. Only intervals on which the actual localized function is
nonzero need a gap bound. The support calculation makes every other central
interval inactive, including gaps and nodes affected by finite exceptions.
The inverse L2 Fourier convention and weighted integrability are explicit.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped ContDiff FourierTransform

/-- A nonzero localized value lies strictly beyond the inner radial edge
of its actual translated support, on either ray. -/
theorem knsLocalizedFunction_innerRadius_lt_abs {n : ℕ} (hn : 1 ≤ n)
    {u v x : ℝ} (hu : 0 < u) {f : ℝ → ℂ}
    (hx : knsLocalizedFunction n u v f x ≠ 0) : |v|-3*u/2 < |x| := by
  have hF : knsMomentLocalizer n u (x-v) ≠ 0 := by
    intro hz
    exact hx (by simp [knsLocalizedFunction, hz])
  have hdist : |x-v| < 3*u/2 :=
    abs_lt.mpr (support_knsMomentLocalizer_subset_open hn hu.le hF)
  have htri := abs_sub_abs_le_abs_sub v x
  rw [abs_sub_comm v x] at htri
  linarith

/-- Original zeros are only needed outside the central radius: every
remaining node value is killed by the actual support of the localizer. -/
theorem knsLocalizedFunction_zero_on_tailZeroCarrier
    (Λ : TwoSidedCarrier) {n : ℕ} (hn : 1 ≤ n) {u v X0 : ℝ} (hu : 0 < u)
    (hcenter : X0 ≤ |v|-3*u/2) {f : ℝ → ℂ}
    (hzero : ∀ j : ℤ, X0 ≤ |Λ j| → f (Λ j) = 0) :
    ∀ j : ℤ, knsLocalizedFunction n u v f (Λ j) = 0 := by
  intro j
  by_contra hj
  have hx := knsLocalizedFunction_innerRadius_lt_abs hn hu hj
  exact hj (knsLocalizedFunction_eq_zero_of_zero n u v (hzero j (by linarith)))

/-- The genuine source-shaped reciprocal gap bound gives the precise
uniform length bound on every active localized interval. -/
theorem knsLocalizedFunction_active_gap_le
    (Λ : TwoSidedCarrier) {n : ℕ} (hn : 1 ≤ n) {u v X0 σ : ℝ}
    (hu : 0 < u) (hσ : 0 < σ) (hinner : 0 < |v|-3*u/2)
    (hcenter : X0 ≤ |v|-3*u/2)
    (hgap : ∀ (j : ℤ) (x : ℝ), x ∈ Ioc (Λ j) (Λ (j+1)) → X0 ≤ |x| →
      Λ (j+1)-Λ j ≤ (2*σ*|x|)⁻¹) (f : ℝ → ℂ) :
    ∀ j : ℤ, (∃ x ∈ Ioc (Λ j) (Λ (j+1)), knsLocalizedFunction n u v f x ≠ 0) →
      Λ (j+1)-Λ j ≤ (2*(σ*(|v|-3*u/2)))⁻¹ := by
  intro j hj
  obtain ⟨x,hx,hf⟩ := hj
  have hrad := knsLocalizedFunction_innerRadius_lt_abs hn hu hf
  have hg := hgap j x hx (by linarith)
  apply hg.trans
  apply inv_anti₀ (by positivity)
  nlinarith

/-- Actual reciprocal-tail localization of the sharp convex Poincare
inequality, at exactly t = sigma times the inner support radius. The only
Fourier-weight hypothesis is integrability of the actual displayed moment. -/
theorem convex_poincare_knsLocalizedFunction
    (Λ : TwoSidedCarrier) {n : ℕ} (hn : 2 ≤ n) {u v X0 σ : ℝ}
    (hu : 0 < u) (hσ : 0 < σ) (hinner : 0 < |v|-3*u/2)
    (hcenter : X0 ≤ |v|-3*u/2)
    (hgap : ∀ (j : ℤ) (x : ℝ), x ∈ Ioc (Λ j) (Λ (j+1)) → X0 ≤ |x| →
      Λ (j+1)-Λ j ≤ (2*σ*|x|)⁻¹)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hzero : ∀ j : ℤ, X0 ≤ |Λ j| → f (Λ j) = 0)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0))
    (hd : DifferentiableAt ℝ Φ ((σ*(|v|-3*u/2))^2)) :
    let hF := (memLp_knsLocalizedFunction_and_deriv hn hu v hf).1
    Integrable (fun ξ => Φ (ξ^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) ξ‖^2) →
      Φ ((σ*(|v|-3*u/2))^2)*(∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
        ∫ ξ, Φ (ξ^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) ξ‖^2 := by
  intro hF hΦi
  exact convex_poincare_of_active_twoSided_zeros Λ (mul_pos hσ hinner)
    (knsLocalizedFunction n u v f) (contDiff_one_knsLocalizedFunction hn hu v hf)
    (knsLocalizedFunction_zero_on_tailZeroCarrier Λ (by omega) hu hcenter hzero)
    (knsLocalizedFunction_active_gap_le Λ (by omega) hu hσ hinner hcenter hgap f)
    hF (memLp_knsLocalizedFunction_and_deriv hn hu v hf).2 Φ hΦ hmono hd hΦi

/-- A radius constructed from finite sums strictly contains all deleted
nodes and both endpoints of every exceptional consecutive gap. -/
theorem TwoSidedCarrier.exists_radius_finite_nodes_and_gaps
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) :
    ∃ R > 0, (∀ j ∈ F, |Λ j| < R) ∧
      ∀ j ∈ J, max |Λ j| |Λ (j+1)| < R := by
  let A : ℝ := ∑ j ∈ F, |Λ j|
  let B : ℝ := ∑ j ∈ J, max |Λ j| |Λ (j+1)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => abs_nonneg (Λ j))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ =>
    (abs_nonneg (Λ j)).trans (le_max_left _ _))
  refine ⟨1+A+B, by positivity, ?_, ?_⟩
  · intro j hj
    have hs : |Λ j| ≤ A := Finset.single_le_sum (fun i _ => abs_nonneg (Λ i)) hj
    linarith
  · intro j hj
    have hs : max |Λ j| |Λ (j+1)| ≤ B := Finset.single_le_sum
      (f := fun i : ℤ => max |Λ i| |Λ (i+1)|)
      (fun i _ => (abs_nonneg (Λ i)).trans (le_max_left _ _)) hj
    linarith

/-- A larger-endpoint weighted gap bound outside finitely many indices
implies the actual reciprocal bound at every tail point of every gap.
The exceptional gaps are inactive once their two endpoints lie inside R. -/
theorem TwoSidedCarrier.reciprocalTailGap_of_weightedGap
    (Λ : TwoSidedCarrier) (J : Finset ℤ) {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    (hJ : ∀ j ∈ J, max |Λ j| |Λ (j+1)| < R)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∀ (j : ℤ) (x : ℝ), x ∈ Ioc (Λ j) (Λ (j+1)) → R ≤ |x| →
      Λ (j+1)-Λ j ≤ (2*σ*|x|)⁻¹ := by
  intro j x hx hRx
  have hxpos : 0 < |x| := hR.trans_le hRx
  have hmax : |x| ≤ max |Λ j| |Λ (j+1)| := abs_le_max_abs_abs hx.1.le hx.2
  have hj : j ∉ J := by
    intro hj
    have hh := hJ j hj
    linarith
  have hδ : 0 ≤ Λ (j+1)-Λ j := sub_nonneg.mpr (Λ.strictMono (by omega)).le
  have hw : (2*σ)*(max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j)) ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*σ)).mp
      (show max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ 1/(2*σ) by
        simpa only [one_div] using hgap j hj)
    nlinarith
  rw [← one_div]
  apply (le_div_iff₀ (by positivity : 0 < 2*σ*|x|)).mpr
  calc
    (Λ (j+1)-Λ j)*(2*σ*|x|) = (2*σ)*(|x| * (Λ (j+1)-Λ j)) := by ring
    _ ≤ (2*σ)*(max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hδ) (by positivity)
    _ ≤ 1 := hw

/-- Both tail hypotheses are genuine conclusions after enlarging one
radius around independent finite sets of deleted nodes and bad gaps. -/
theorem TwoSidedCarrier.exists_radius_tailZeros_and_reciprocalGap
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ R > 0,
      (∀ (f : ℝ → ℂ), (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
        ∀ j : ℤ, R ≤ |Λ j| → f (Λ j) = 0) ∧
      ∀ (j : ℤ) (x : ℝ), x ∈ Ioc (Λ j) (Λ (j+1)) → R ≤ |x| →
        Λ (j+1)-Λ j ≤ (2*σ*|x|)⁻¹ := by
  obtain ⟨R,hR,hF,hJ⟩ := Λ.exists_radius_finite_nodes_and_gaps F J
  refine ⟨R,hR,?_,Λ.reciprocalTailGap_of_weightedGap J hσ hR hJ hgap⟩
  intro f hf j hj
  apply hf j
  intro hmem
  have h := hF j hmem
  linarith

/-- The actual convex localized estimate survives arbitrary finite
deletions. Its positive radius is chosen before the cutoff order, width,
translation, unknown function, and convex weight. The original carrier,
not a possibly empty list of consecutive zero pairs, supplies coverage. -/
theorem exists_radius_convex_poincare_knsLocalizedFunction_of_finite_exceptions
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (n : ℕ) (hn : 2 ≤ n) (u : ℝ) (hu : 0 < u) (v : ℝ),
      X0 ≤ |v|-3*u/2 →
      ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f), (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (Φ : ℝ → ℝ), ConvexOn ℝ (Ici 0) Φ → MonotoneOn Φ (Ici 0) →
      DifferentiableAt ℝ Φ ((σ*(|v|-3*u/2))^2) →
      let hF := (memLp_knsLocalizedFunction_and_deriv hn hu v hf).1
      Integrable (fun ξ => Φ (ξ^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) ξ‖^2) →
        Φ ((σ*(|v|-3*u/2))^2)*(∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
          ∫ ξ, Φ (ξ^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) ξ‖^2 := by
  obtain ⟨R,hR,hzeros,hgaps⟩ := Λ.exists_radius_tailZeros_and_reciprocalGap F J hσ hgap
  refine ⟨R,hR,?_⟩
  intro n hn u hu v hv f hf hz Φ hΦ hm hd
  exact convex_poincare_knsLocalizedFunction Λ hn hu hσ (hR.trans_le hv)
    hv hgaps f hf (hzeros f hz) Φ hΦ hm hd

/-- The same exact localized convex estimate for the genuine classical
negative-phase Fourier integral, with all unweighted domain properties
proved from the actual compact C1 localizer. -/
theorem convex_classicalFourier_poincare_knsLocalizedFunction
    (Λ : TwoSidedCarrier) {n : ℕ} (hn : 2 ≤ n) {u v X0 σ : ℝ}
    (hu : 0 < u) (hσ : 0 < σ) (hinner : 0 < |v|-3*u/2)
    (hcenter : X0 ≤ |v|-3*u/2)
    (hgap : ∀ (j : ℤ) (x : ℝ), x ∈ Ioc (Λ j) (Λ (j+1)) → X0 ≤ |x| →
      Λ (j+1)-Λ j ≤ (2*σ*|x|)⁻¹)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hzero : ∀ j : ℤ, X0 ≤ |Λ j| → f (Λ j) = 0)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0))
    (hd : DifferentiableAt ℝ Φ ((σ*(|v|-3*u/2))^2))
    (hΦi : Integrable (fun ξ => Φ (ξ^2)*‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2)) :
    Φ ((σ*(|v|-3*u/2))^2)*(∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
      ∫ ξ, Φ (ξ^2)*‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2 := by
  obtain ⟨hF,hD⟩ := memLp_knsLocalizedFunction_and_deriv hn hu v hf
  obtain ⟨hL1,hD1⟩ := integrable_knsLocalizedFunction_and_deriv hn hu v hf
  exact convex_classicalFourier_poincare_of_active_twoSided_zeros Λ (mul_pos hσ hinner)
    (knsLocalizedFunction n u v f) (contDiff_one_knsLocalizedFunction hn hu v hf)
    (knsLocalizedFunction_zero_on_tailZeroCarrier Λ (by omega) hu hcenter hzero)
    (knsLocalizedFunction_active_gap_le Λ (by omega) hu hσ hinner hcenter hgap f)
    hF hD hL1 hD1 Φ hΦ hmono hd hΦi

/-- Finite deletions and exceptional weighted gaps yield the actual
classical-Fourier localized bound at every sufficiently exterior translation.
The radius is geometric and is fixed before all function and weight data. -/
theorem exists_radius_classicalFourier_poincare_knsLocalizedFunction_of_finite_exceptions
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (n : ℕ) (hn : 2 ≤ n) (u : ℝ) (hu : 0 < u) (v : ℝ),
      X0 ≤ |v|-3*u/2 →
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (Φ : ℝ → ℝ), ConvexOn ℝ (Ici 0) Φ → MonotoneOn Φ (Ici 0) →
      DifferentiableAt ℝ Φ ((σ*(|v|-3*u/2))^2) →
      Integrable (fun ξ => Φ (ξ^2)*‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2) →
        Φ ((σ*(|v|-3*u/2))^2)*(∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
          ∫ ξ, Φ (ξ^2)*‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2 := by
  obtain ⟨R,hR,hzeros,hgaps⟩ := Λ.exists_radius_tailZeros_and_reciprocalGap F J hσ hgap
  refine ⟨R,hR,?_⟩
  intro n hn u hu v hv f hf hz Φ hΦ hm hd hΦi
  exact convex_classicalFourier_poincare_knsLocalizedFunction Λ hn hu hσ (hR.trans_le hv)
    hv hgaps f hf (hzeros f hz) Φ hΦ hm hd hΦi

end

end MeyerGeneralProblem
