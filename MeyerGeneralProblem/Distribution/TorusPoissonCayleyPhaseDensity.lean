module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayley
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The real-analytic Cayley boundary and its phase density

The removable values at actual support points give one scalar function
which is analytic through the entire real line on almost every phase.
The boundary speed has a translation-covariant continuous density,
with interval mass bounded by the number of support points plus one.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric Set UnitAddTorus
open scoped NNReal Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyRealLeafCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The scalar Cayley leaf with its removable values filled in
at all real points of intrinsic support. -/
def torusPoissonCayleyExtendedLeaf (θ : UnitAddTorus d) (z : ℂ) : ℂ := by
  classical
  exact if z.im = 0 ∧ z.re ∈ Distribution.dsupport (T θ) then 1
    else supportPoissonCayley (torusPositivePoissonLeaf β S T hT hCont hCount θ z)

/-- The actual extension restricts at the origin to the coherent boundary. -/
theorem torusPoissonCayleyExtendedLeaf_zero (θ : UnitAddTorus d) :
    torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ 0 =
      torusPoissonCayleyBoundary β S T hT hCont hCount θ := by
  classical
  simp [torusPoissonCayleyExtendedLeaf, torusPoissonCayleyBoundary]

/-- The extended leaf agrees with the scalar upper-half-plane field. -/
theorem torusPoissonCayleyExtendedLeaf_eq_field (θ : UnitAddTorus d) {z : ℂ} (hz : 0 < z.im) :
    torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ z =
      torusPoissonCayleyField β S T hT hCont hCount z θ := by
  classical
  simp [torusPoissonCayleyExtendedLeaf, torusPoissonCayleyField, hz, hz.ne']

private theorem analyticAt_cayley_of_re_eq_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hRe : (f a).re = 0) :
    AnalyticAt ℂ (supportPoissonCayley ∘ f) a := by
  unfold supportPoissonCayley
  exact ((hf.add analyticAt_const).sub analyticAt_const).div
    ((hf.add analyticAt_const).add analyticAt_const)
    (supportPoissonCayley_denominator_ne_zero hRe.ge)

include hAdvance in
/-- On a common full-measure set the patched Cayley function is analytic
at every real point and has unit modulus there. -/
theorem ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf :
    ∀ᵐ θ ∂volume, ∀ a : ℝ,
      AnalyticAt ℂ (torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ) (a : ℂ) ∧
      ‖torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (a : ℂ)‖ = 1 := by
  classical
  filter_upwards [ae_re_torusPositivePoissonLeaf_real_of_notMem_dsupport
    β S T hT hCont hCount hAdvance] with θ hθ a
  let L := torusPositivePoissonLeaf β S T hT hCont hCount θ
  let U := Distribution.dsupport (T θ)
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ
  change AnalyticAt ℂ F (a : ℂ) ∧ ‖F (a : ℂ)‖ = 1
  by_cases ha : a ∈ U
  · obtain ⟨G, hG, hEq⟩ := exists_supportCauchy_analytic_remainder_at_site
      (S θ) (T θ) (hT θ) (hCount θ) ha
    let c := torusPositivePoissonField β S T hT hCont hCount Complex.I θ
    have hResidue : -supportCauchyConstant ≠ 0 := by
      rw [neg_supportCauchyConstant_eq_residue]
      exact div_ne_zero Complex.I_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hPole : L =ᶠ[𝓝[≠] (a : ℂ)] fun w => -supportCauchyConstant * (w - (a : ℂ))⁻¹ + (c + G w) := by
      filter_upwards [hEq.filter_mono nhdsWithin_le_nhds] with w hw
      change c + (∫ x, supportCauchyKernel w x ∂discreteSupportCount (T θ)) = _
      rw [hw]
      abel
    obtain ⟨H, hH, hH0, hCayley, _⟩ :=
      exists_analyticAt_supportPoissonCayley_at_simplePole hResidue (analyticAt_const.add hG) hPole
    let j : (S θ).subtype := ⟨a, dsupport_subset_of_discrete_support (S θ) (T θ) (hT θ) ha⟩
    have hNear : ∀ᶠ w : ℂ in 𝓝 (a : ℂ), w.re ∈ ball (j : ℝ) ((S θ).isolationRadius j) := by
      apply Complex.continuous_re.continuousAt
      exact ball_mem_nhds _ ((S θ).isolationRadius_pos j)
    have hPuncture : F =ᶠ[𝓝[≠] (a : ℂ)] H := by
      filter_upwards [hCayley, hNear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with w hw hNearW hwne
      have hOff : ¬(w.im = 0 ∧ w.re ∈ U) := by
        rintro ⟨hi, hs⟩
        have hm : w.re ∈ ball (j : ℝ) ((S θ).isolationRadius j) ∩ (S θ).carrier :=
          ⟨hNearW, dsupport_subset_of_discrete_support (S θ) (T θ) (hT θ) hs⟩
        rw [(S θ).ball_isolationRadius_inter j] at hm
        have hre : w.re = a := hm
        apply hwne
        apply Complex.ext
        · simpa using hre
        · simpa using hi
      change (if w.im = 0 ∧ w.re ∈ U then 1 else supportPoissonCayley (L w)) = H w
      rw [ite_eq_right hOff]
      exact hw
    have hAt : F (a : ℂ) = 1 := by simp [F, torusPoissonCayleyExtendedLeaf, U, ha]
    have hFull : F =ᶠ[𝓝 (a : ℂ)] H := by
      filter_upwards [eventually_nhdsWithin_iff.mp hPuncture] with w hw
      by_cases he : w = (a : ℂ)
      · rw [he, hAt, hH0]
      · exact hw he
    exact ⟨hH.congr hFull.symm, by simp [hAt]⟩
  · have hNo : (a : ℂ) ∉ Complex.ofReal '' U := by
      rintro ⟨x, hx, hxa⟩
      exact ha (Complex.ofReal_injective hxa ▸ hx)
    have hL : AnalyticAt ℂ L (a : ℂ) :=
      (torusPositivePoissonLeaf_poles_and_residues β S T hT hCont hCount θ).1 _ hNo
    have hRe := hθ a ha
    have hNear : ∀ᶠ w : ℂ in 𝓝 (a : ℂ), w.re ∈ Uᶜ := by
      apply Complex.continuous_re.continuousAt
      apply Distribution.isClosed_dsupport.isOpen_compl.mem_nhds
      simpa only [Complex.ofReal_re, mem_compl_iff] using ha
    have hEq : F =ᶠ[𝓝 (a : ℂ)] (supportPoissonCayley ∘ L) := by
      filter_upwards [hNear] with w hw
      change (if w.im = 0 ∧ w.re ∈ U then 1 else supportPoissonCayley (L w)) = _
      rw [ite_eq_right fun h => hw h.2]
      rfl
    refine ⟨(analyticAt_cayley_of_re_eq_zero hL hRe).congr hEq.symm, ?_⟩
    rw [hEq.eq_of_nhds]
    exact norm_supportPoissonCayley_eq_one hRe

end

private theorem intervalIntegral_le_one_of_gapPrimitive {f g : ℝ → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (f x) x)
    (hg : ∀ x ∈ Ioo a b, g x ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, f x) ≤ 1 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let P (t : ℝ) := ∫ x in a..t, f x
  have hP : Continuous P :=
    intervalIntegral.continuous_primitive (fun l r => hf.intervalIntegrable l r) a
  have hClosed : IsClosed {q : ℝ × ℝ | P q.2 - P q.1 ≤ 1} :=
    isClosed_le ((hP.comp continuous_snd).sub (hP.comp continuous_fst)) continuous_const
  have hSub : Ioo a b ×ˢ Ioo a b ⊆ {q : ℝ × ℝ | P q.2 - P q.1 ≤ 1} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hEq : P v - P u = ∫ x in u..v, f x := by
      dsimp only [P]
      linarith only [intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (μ := volume) a u) (hf.intervalIntegrable u v)]
    change P v - P u ≤ 1
    rw [hEq]
    by_cases huv : u ≤ v
    · have ht : ∀ x ∈ uIcc u v, HasDerivAt g (f x) x := by
        rw [uIcc_of_le huv]
        intro x hx
        exact hd x ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt ht (hf.intervalIntegrable u v)]
      linarith only [(hg u hu).1, (hg v hv).2]
    · rw [intervalIntegral.integral_symm v u]
      linarith only [intervalIntegral.integral_nonneg_of_forall (le_of_not_ge huv) h0
        (μ := (volume : Measure ℝ))]
  have hPair : (a, b) ∈ closure (Ioo a b ×ˢ Ioo a b) := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨⟨le_rfl, hab.le⟩, ⟨hab.le, le_rfl⟩⟩
  have h := closure_minimal hSub hClosed hPair
  change P b - P a ≤ 1 at h
  simpa only [P, intervalIntegral.integral_same, sub_zero] using h

/-- A bounded primitive off a finite exceptional set controls the total
mass of a nonnegative continuous density by the number of intervening gaps. -/
private theorem intervalIntegral_le_card_add_one_of_gapPrimitive {f g : ℝ → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (s : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ x ∈ s, x ∈ Ioo a b)
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt g (f x) x)
    (hg : ∀ x ∈ Ioo a b, x ∉ s → g x ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, f x) ≤ (s.card : ℝ) + 1 := by
  classical
  induction s using Finset.strongInductionOn generalizing a b
  rename_i s ih
  by_cases he : s = ∅
  · subst s
    simpa using intervalIntegral_le_one_of_gapPrimitive hf h0 hab
      (fun x hx => hd x hx (Finset.notMem_empty x))
      (fun x hx => hg x hx (Finset.notMem_empty x))
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hac := (hs c hc).1
  have hcb := (hs c hc).2
  let l := s.filter (· < c)
  let r := s.filter (c < ·)
  have hl : l ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, fun eq =>
      lt_irrefl c (Finset.mem_filter.mp (show c ∈ l from eq.symm ▸ hc)).2⟩
  have hr : r ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, fun eq =>
      lt_irrefl c (Finset.mem_filter.mp (show c ∈ r from eq.symm ▸ hc)).2⟩
  have hL := ih l hl hac.le
    (fun x hx => ⟨(hs x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩)
    (fun x hx h => hd x ⟨hx.1, hx.2.trans hcb⟩
      (fun hm => h (Finset.mem_filter.mpr ⟨hm, hx.2⟩)))
    (fun x hx h => hg x ⟨hx.1, hx.2.trans hcb⟩
      (fun hm => h (Finset.mem_filter.mpr ⟨hm, hx.2⟩)))
  have hR := ih r hr hcb.le
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hs x (Finset.mem_filter.mp hx).1).2⟩)
    (fun x hx h => hd x ⟨hac.trans hx.1, hx.2⟩
      (fun hm => h (Finset.mem_filter.mpr ⟨hm, hx.1⟩)))
    (fun x hx h => hg x ⟨hac.trans hx.1, hx.2⟩
      (fun hm => h (Finset.mem_filter.mpr ⟨hm, hx.1⟩)))
  have hDis : Disjoint l r := Finset.disjoint_left.mpr fun x hx hy =>
    lt_asymm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hSub : l ∪ r ⊆ s.erase c := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hx).1⟩
    · exact Finset.mem_erase.mpr ⟨ne_of_gt (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hx).1⟩
  have hCard : l.card + r.card + 1 ≤ s.card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hDis, Finset.card_erase_of_mem hc] at h
    have : 0 < s.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  have hCardReal : (l.card : ℝ) + r.card + 1 ≤ s.card := by exact_mod_cast hCard
  have hSplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) a c) (hf.intervalIntegrable c b)
  linarith only [hL, hR, hCardReal, hSplit]

section BoundaryPhaseMass

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The positive boundary phase density is the speed of the unit-modulus
Cayley path divided by one full turn. -/
def torusPoissonCayleyPhaseDensity (θ : UnitAddTorus d) (x : ℝ) : ℝ :=
  ‖deriv (fun t : ℝ => torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (t : ℂ)) x‖ /
    (2 * Real.pi)

private theorem norm_one_add_imaginary_sq (u : ℝ) :
    ‖(u : ℂ) * Complex.I + 1‖ ^ 2 = 1 + u ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem hasDerivAt_cayley_imaginary {u : ℝ → ℝ} {a v : ℝ} (hu : HasDerivAt u v a) :
    HasDerivAt (fun x => supportPoissonCayley ((u x : ℂ) * Complex.I))
      (2 * ((v : ℂ) * Complex.I) / (((u a + 1 : ℝ) : ℂ) * Complex.I + 1) ^ 2) a := by
  let D (x : ℝ) := ((u x + 1 : ℝ) : ℂ) * Complex.I + 1
  have hD : HasDerivAt D ((v : ℂ) * Complex.I) a :=
    (((hu.add_const 1).ofReal_comp).mul_const Complex.I).add_const 1
  have hDne (x : ℝ) : D x ≠ 0 := by
    intro h
    have hz := congrArg Complex.re h
    simp [D, Complex.mul_re] at hz
  have hC (x : ℝ) :
      supportPoissonCayley ((u x : ℂ) * Complex.I) = 1 - 2 * (D x)⁻¹ := by
    have hDen : (u x : ℂ) * Complex.I + Complex.I + 1 = D x := by
      simp only [D, Complex.ofReal_add, Complex.ofReal_one]
      ring
    have hNum : (u x : ℂ) * Complex.I + Complex.I - 1 = D x - 2 := by rw [← hDen]; ring
    rw [supportPoissonCayley, hDen, hNum, sub_div, div_self (hDne x), div_eq_mul_inv]
  simp only [hC]
  have h := ((hD.inv (hDne a)).const_mul (2 : ℂ)).const_sub (1 : ℂ)
  simpa only [Pi.inv_apply, D, neg_div, mul_neg, neg_neg, mul_div_assoc] using h

private theorem hasDerivAt_cayleyPhasePrimitive_of_notMem
    (θ : UnitAddTorus d) {x : ℝ} (hx : x ∉ Distribution.dsupport (T θ))
    (hRe : ∀ a : ℝ, a ∉ Distribution.dsupport (T θ) →
      (torusPositivePoissonLeaf β S T hT hCont hCount θ (a : ℂ)).re = 0) :
    HasDerivAt (fun a : ℝ => 1 / 2 - Real.arctan
      ((torusPositivePoissonLeaf β S T hT hCont hCount θ (a : ℂ)).im + 1) / Real.pi)
      (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x) x := by
  classical
  let L := torusPositivePoissonLeaf β S T hT hCont hCount θ
  let U := Distribution.dsupport (T θ)
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ
  let u (a : ℝ) := (L (a : ℂ)).im
  let v := deriv u x
  have hv := (hasDerivAt_im_torusPositivePoissonLeaf_of_notMem_dsupport β S T hT hCont hCount θ hx)
  have hu : HasDerivAt u v x := hv.differentiableAt.hasDerivAt
  have hv0 : v ≤ 0 := deriv_im_torusPositivePoissonLeaf_nonpos β S T hT hCont hCount θ hx
  have hEq : (fun a : ℝ => supportPoissonCayley ((u a : ℂ) * Complex.I)) =ᶠ[𝓝 x]
      (fun a : ℝ => F (a : ℂ)) := by
    have hNear : ∀ᶠ a : ℝ in 𝓝 x, a ∈ Uᶜ :=
      Distribution.isClosed_dsupport.isOpen_compl.mem_nhds hx
    filter_upwards [hNear] with a ha
    have hL : (u a : ℂ) * Complex.I = L (a : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, zero_mul, sub_zero] using (hRe a ha).symm
      · simp [Complex.mul_im, u]
    change supportPoissonCayley ((u a : ℂ) * Complex.I) =
      (if (a : ℂ).im = 0 ∧ (a : ℂ).re ∈ U then 1 else supportPoissonCayley (L (a : ℂ)))
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, ite_eq_right ha, hL]
  have hD := (hasDerivAt_cayley_imaginary hu).congr_of_eventuallyEq hEq.symm
  have hVal : torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x =
      (-v) / ((1 + (u x + 1) ^ 2) * Real.pi) := by
    change ‖deriv (fun a : ℝ => F (a : ℂ)) x‖ / (2 * Real.pi) = _
    rw [hD.deriv, norm_div, norm_mul, norm_mul, norm_pow, norm_one_add_imaginary_sq,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonpos hv0]
    have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hTwo]
    have hDen : 1 + (u x + 1) ^ 2 ≠ 0 := by positivity
    field_simp [hDen, Real.pi_ne_zero]
  rw [hVal]
  have hA := (Real.hasDerivAt_arctan (u x + 1)).comp x (hu.add_const 1)
  have hP := (hA.div_const Real.pi).const_sub (1 / 2 : ℝ)
  change HasDerivAt (fun a : ℝ => 1 / 2 - Real.arctan (u a + 1) / Real.pi)
    ((-v) / ((1 + (u x + 1) ^ 2) * Real.pi)) x
  have hEq : -((1 / (1 + (u x + 1) ^ 2) * v) / Real.pi) =
      (-v) / ((1 + (u x + 1) ^ 2) * Real.pi) := by
    have hDen : 1 + (u x + 1) ^ 2 ≠ 0 := by positivity
    field_simp [hDen, Real.pi_ne_zero]
  rw [← hEq]
  exact hP

include hAdvance in
/-- The mass on a compact real interval is at most the number of actual
support points in that interval's interior plus one. -/
theorem ae_intervalIntegral_torusPoissonCayleyPhaseDensity_le :
    ∀ᵐ θ ∂volume, ∀ a b : ℝ, a ≤ b →
      (∫ x in a..b, torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x) ≤
        ((Distribution.dsupport (T θ) ∩ Ioo a b).ncard : ℝ) + 1 := by
  classical
  filter_upwards [ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance,
    ae_re_torusPositivePoissonLeaf_real_of_notMem_dsupport β S T hT hCont hCount hAdvance]
    with θ hAnalytic hRe a b hab
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ
  let f := torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ
  let L := torusPositivePoissonLeaf β S T hT hCont hCount θ
  let g (t : ℝ) := 1 / 2 - Real.arctan ((L (t : ℂ)).im + 1) / Real.pi
  have hDer : (fun t : ℝ => deriv (fun x : ℝ => F (x : ℂ)) t) =
      fun t : ℝ => deriv F (t : ℂ) := by
    funext t
    exact (((hAnalytic t).1.differentiableAt.hasDerivAt).comp_ofReal).deriv
  have hContDer : Continuous (fun t : ℝ => deriv F (t : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (hAnalytic t).1.deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hf : Continuous f := by
    change Continuous (fun t : ℝ => ‖deriv (fun x : ℝ => F (x : ℂ)) t‖ / (2 * Real.pi))
    simp only [hDer]
    exact hContDer.norm.div_const _
  have hf0 (t : ℝ) : 0 ≤ f t := div_nonneg (norm_nonneg _) Real.two_pi_pos.le
  have hFin : (Distribution.dsupport (T θ) ∩ Ioo a b).Finite :=
    ((S θ).finite_inter_Ioo a b).subset fun _ h =>
      ⟨dsupport_subset_of_discrete_support (S θ) (T θ) (hT θ) h.1, h.2⟩
  let s := hFin.toFinset
  have hS (t : ℝ) : t ∈ s ↔ t ∈ Distribution.dsupport (T θ) ∧ t ∈ Ioo a b :=
    hFin.mem_toFinset
  have he := intervalIntegral_le_card_add_one_of_gapPrimitive (g := g) hf hf0 s hab
    (fun t ht => ((hS t).mp ht).2)
    (fun t ht hs => hasDerivAt_cayleyPhasePrimitive_of_notMem β S T hT hCont hCount θ
      (fun h => hs ((hS t).mpr ⟨h, ht⟩)) hRe)
    (fun t _ _ => by
      obtain ⟨hl, hu⟩ := Real.arctan_mem_Ioo ((L (t : ℂ)).im + 1)
      change 0 ≤ g t ∧ g t ≤ 1
      constructor
      · apply sub_nonneg.mpr
        apply (div_le_iff₀ Real.pi_pos).mpr
        linarith only [hu]
      · have hLow : -(1 / 2 : ℝ) ≤ Real.arctan ((L (t : ℂ)).im + 1) / Real.pi :=
          (le_div_iff₀ Real.pi_pos).mpr (by linarith only [hl])
        dsimp only [g]
        linarith only [hLow])
  simpa only [s, ← Set.ncard_eq_toFinset_card _ hFin] using he


include hAdvance in
/-- Covariance holds at every real boundary point for almost every phase,
for each fixed translation of the flow. -/
theorem ae_torusPoissonCayleyExtendedLeaf_real_phaseAdvance (s : ℝ) :
    ∀ᵐ θ ∂volume, ∀ x : ℝ,
      torusPoissonCayleyExtendedLeaf β S T hT hCont hCount (unitAddTorusFlow β s θ) (x : ℂ) =
        torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ ((x + s : ℝ) : ℂ) := by
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount
  let flow := unitAddTorusFlow β s
  let row (x y : ℝ) := (x : ℂ) + (y : ℂ) * Complex.I
  have hRow (x : ℝ) : Tendsto (row x) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hc : Continuous (row x) := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h := (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [row] using h
  have hGood := ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance
  have hPres := measurePreserving_unitAddTorusFlow β s
  filter_upwards [hGood, hPres.quasiMeasurePreserving.ae hGood,
    ae_forall_torusPositivePoissonLeaf_phaseAdvance β S T hT hCont hCount hAdvance s]
    with θ hθ hFlow hCov x
  change F (flow θ) (x : ℂ) = F θ ((x + s : ℝ) : ℂ)
  have hEq : (fun y : ℝ => F (flow θ) (row x y)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun y => F θ (row (x + s) y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hY : 0 < (row x y).im := by simpa [row, Complex.mul_im] using hy
    have hY' : 0 < (row (x + s) y).im := by simpa [row, Complex.mul_im] using hy
    have hShift : row x y + (s : ℂ) = row (x + s) y := by
      simp only [row, Complex.ofReal_add]
      abel
    have h := hCov (row x y) hY
    rw [hShift] at h
    change torusPoissonCayleyExtendedLeaf β S T hT hCont hCount (flow θ) (row x y) =
      torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (row (x + s) y)
    rw [torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount _ hY,
      torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount _ hY']
    simpa only [torusPoissonCayleyField, ite_eq_left hY, ite_eq_left hY', flow] using
      congrArg supportPoissonCayley h
  have hLim := ((hFlow x).1.continuousAt.tendsto.comp (hRow x)).congr' hEq
  exact tendsto_nhds_unique hLim ((hθ (x + s)).1.continuousAt.tendsto.comp (hRow (x + s)))

include hAdvance in
/-- The positive real phase density is covariant under each fixed translation
on a full-measure set common to all real points of the leaf. -/
theorem ae_torusPoissonCayleyPhaseDensity_phaseAdvance (s : ℝ) :
    ∀ᵐ θ ∂volume, ∀ x : ℝ,
      torusPoissonCayleyPhaseDensity β S T hT hCont hCount (unitAddTorusFlow β s θ) x =
        torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ (x + s) := by
  filter_upwards [ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance,
    ae_torusPoissonCayleyExtendedLeaf_real_phaseAdvance β S T hT hCont hCount hAdvance s]
    with θ hθ hCov x
  let F (φ : UnitAddTorus d) (t : ℝ) :=
    torusPoissonCayleyExtendedLeaf β S T hT hCont hCount φ (t : ℂ)
  have hEq : F (unitAddTorusFlow β s θ) = fun t => F θ (t + s) := funext hCov
  have hD : DifferentiableAt ℝ (F θ) (x + s) :=
    ((hθ (x + s)).1.differentiableAt.hasDerivAt.comp_ofReal).differentiableAt
  have hInner : HasDerivAt (fun t : ℝ => t + s) 1 x := (hasDerivAt_id x).add_const s
  have h := hD.hasDerivAt.scomp x hInner
  have hShift : HasDerivAt (fun t : ℝ => F θ (t + s)) (deriv (F θ) (x + s)) x := by
    simpa only [Function.comp_def, one_smul] using h
  change ‖deriv (F (unitAddTorusFlow β s θ)) x‖ / (2 * Real.pi) =
    ‖deriv (F θ) (x + s)‖ / (2 * Real.pi)
  rw [hEq, hShift.deriv]

end BoundaryPhaseMass

end
end MeyerGeneralProblem
