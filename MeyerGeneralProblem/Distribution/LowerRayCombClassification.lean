module

public import MeyerGeneralProblem.Distribution.FiniteModulationMenu
public import MeyerGeneralProblem.Distribution.CenteredCountFiniteComb
public import MeyerGeneralProblem.Distribution.SplineSignAlternations
public import MeyerGeneralProblem.Distribution.AtomicPrimitiveSpline

@[expose] public section

/-!
# One lower ray count and the comb classification

A ray lower-density bound for a value-only atomic source with a Fourier
gap gives the fixed detector needed by the finite-prefix modulation
matrix. The detector and the established comb extraction use the full
original source and both original coefficient records.
-/

namespace MeyerGeneralProblem

open Filter MeasureTheory Set UniformDiscrete
open scoped FourierTransform

/-- The closed origin-based window on the positive or negative real ray. -/
def originalRayWindow (positive : Bool) (r : ℝ) : Set ℝ :=
  if positive then Icc 0 r else Icc (-r) 0

/-- The original point count on the chosen ray through radius `r`. -/
noncomputable def originalRayCount (A : LocallyFiniteCarrier) (positive : Bool) (r : ℝ) : ℕ :=
  (A.carrier ∩ originalRayWindow positive r).ncard

private theorem signAlternations_le_original_count_add_order
    (A : LocallyFiniteCarrier) {a b : ℝ} (m : ℕ) (f : ℕ → ℝ → ℝ) {n : ℕ}
    (hCont : ∀ k ≤ m, Continuous (f k))
    (hDeriv : ∀ k ≤ m, ∀ x ∉ A.carrier, HasDerivAt (f k) (f (k + 1) x) x)
    (hConst : ∀ u v : ℝ, u ∉ A.carrier → v ∉ A.carrier → u < v →
      (∀ x ∈ A.carrier, x ∉ Ioo u v) → f (m + 1) u = f (m + 1) v)
    (hAlt : HasSignAlternations (f 0) (Icc a b) n) :
    n ≤ (A.carrier ∩ Icc a b).ncard + m + 1 := by
  classical
  let hFinite := A.finite_inter_Icc a b
  let knots := hFinite.toFinset
  have hOff {x : ℝ} (hx : x ∈ Icc a b) (hk : x ∉ knots) : x ∉ A.carrier :=
    fun hA => hk (hFinite.mem_toFinset.mpr ⟨hA, hx⟩)
  rw [Set.ncard_eq_toFinset_card _ hFinite]
  refine spline_sign_alternations_le_card_knots_add_order knots m f
    (fun k hk => (hCont k hk).continuousOn)
    (fun k hk x hx hKnots => hDeriv k hk x (hOff (Ioo_subset_Icc_self hx) hKnots)) ?_ hAlt
  intro u v hu hv huv hKnots
  refine hConst u v (hOff hu.1 hu.2) (hOff hv.1 hv.2) huv (fun x hx hInterval => ?_)
  exact hKnots x (hFinite.mem_toFinset.mpr
    ⟨hx, hu.1.1.trans hInterval.1.le, hInterval.2.le.trans hv.1.2⟩) hInterval

/-- A strict asymptotic lower bound on spline sign changes transfers to
the point count on either ray. The fixed derivative order contributes
only an additive constant to the finite-window bound. -/
theorem eventually_originalRayCount_lower_bound_of_spline
    (A : LocallyFiniteCarrier) (positive : Bool) (m : ℕ) (f : ℕ → ℝ → ℝ) (L : ℝ)
    (hCont : ∀ k ≤ m, Continuous (f k))
    (hDeriv : ∀ k ≤ m, ∀ x ∉ A.carrier, HasDerivAt (f k) (f (k + 1) x) x)
    (hConst : ∀ u v : ℝ, u ∉ A.carrier → v ∉ A.carrier → u < v →
      (∀ x ∈ A.carrier, x ∉ Ioo u v) → f (m + 1) u = f (m + 1) v)
    (hOsc : ∀ d < L, ∀ᶠ r in atTop, ∃ n : ℕ,
      d * r ≤ (n : ℝ) ∧ HasSignAlternations (f 0) (originalRayWindow positive r) n)
    (c : ℝ) (hc : c < L) :
    ∀ᶠ r in atTop, c * r ≤ (originalRayCount A positive r : ℝ) := by
  obtain ⟨d, hcd, hdL⟩ := exists_between hc
  have hMargin : 0 < d - c := sub_pos.mpr hcd
  filter_upwards [hOsc d hdL, eventually_ge_atTop (((m : ℝ) + 1) / (d - c))]
    with r hOscR hRadius
  obtain ⟨n, hSlope, hAlt⟩ := hOscR
  have hCount : n ≤ originalRayCount A positive r + m + 1 := by
    cases positive <;> exact signAlternations_le_original_count_add_order A m f hCont hDeriv hConst hAlt
  have hCountReal : (n : ℝ) ≤ (originalRayCount A positive r : ℝ) + (m : ℝ) + 1 := by
    exact_mod_cast hCount
  have hAbsorb := (div_le_iff₀ hMargin).mp hRadius
  nlinarith only [hSlope, hCountReal, hAbsorb]

/-- Finite lower linear density on the chosen ray, expressed by a bound
on arbitrarily large radii. -/
def HasFiniteLowerRayCount (A : LocallyFiniteCarrier) (positive : Bool) : Prop :=
  ∃ C : ℝ, ∃ᶠ r : ℝ in atTop, (originalRayCount A positive r : ℝ) ≤ C * r

/-- The one-record Fourier-gap density theorem needed for the lower-ray
classification. Every slope strictly below the full gap length bounds
both ray counts from below at sufficiently large radii. -/
def AtomicFourierGapRayLowerBound : Prop :=
  ∀ (A : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ) (R : ℝ),
    0 < R → U ≠ 0 → AtomicOnCarrier A U → VanishesOnInterval (𝓕 U) R →
    ∀ (positive : Bool) (c : ℝ), c < 2 * R →
      ∀ᶠ r : ℝ in atTop, c * r ≤ (originalRayCount A positive r : ℝ)

/-- The Eremenko–Novikov sign-change bound restricted to the real continuous
polynomial-growth Fourier inverse transforms used in the spline proof. -/
def PolynomialGrowthFourierGapSignAlternations : Prop :=
  ∀ (V : TemperedDistribution ℝ ℂ) (f : ℝ → ℝ) (q : ℕ) (R : ℝ),
    0 < R → Continuous f → f ≠ 0 →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ q) →
    (∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ)) →
    VanishesOnInterval (𝓕 V) R →
    ∀ (positive : Bool) (c : ℝ), c < 2 * R →
      ∀ᶠ r : ℝ in atTop, ∃ n : ℕ,
        c * r ≤ (n : ℝ) ∧ HasSignAlternations f (originalRayWindow positive r) n

/-- The real-function oscillation bound implies the value-only atomic
ray-density theorem through the exact real spline primitive. -/
theorem atomicFourierGapRayLowerBound_of_polynomialGrowth_signAlternations
    (hOsc : PolynomialGrowthFourierGapSignAlternations) : AtomicFourierGapRayLowerBound := by
  intro S T R hR hNonzero hAtomic hGap positive c hc
  obtain ⟨a, _, _, hU, _, hFixed, q, hPrimitive⟩ :=
    exists_real_atomic_polynomialGrowth_primitive_with_centered_gap S T hNonzero hAtomic R hR hGap
  obtain ⟨V, f, hD, hVGap, hf, hfNonzero, hGrowth, hRep⟩ := hPrimitive (q + 2) le_rfl
  obtain ⟨hCont, hDeriv, hConst⟩ :=
    real_atomic_primitive_spline_derivative_chain S (realPartTemperedDistribution (a • T))
      V f hf q hU hFixed hD hRep
  apply eventually_originalRayCount_lower_bound_of_spline S positive q
    (fun j => iteratedDeriv j f) (2 * R) hCont hDeriv hConst _ c hc
  intro d hd
  simpa only [iteratedDeriv_zero] using hOsc V f q R hR hf hfNonzero hGrowth hRep hVGap positive d hd

/-- Finite lower linear density on either ray supplies one fixed gap
detector for the whole carrier, with no uniform onset required. -/
theorem exists_spectralGapUniqueness_of_finite_lower_ray_count
    (hGap : AtomicFourierGapRayLowerBound) (A : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) :
    ∃ R : ℝ, 0 < R ∧ SpectralGapUniqueness A R := by
  obtain ⟨C, hC⟩ := hCount
  let R := max C 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right C 0]
  have hSlope : C + 1 < 2 * R := by dsimp [R]; linarith [le_max_left C 0, le_max_right C 0]
  refine ⟨R, hR, fun U hU hV => ?_⟩
  by_contra hUne
  have hLower := hGap A U R hR hUne
    ((atomicOnCarrier_iff_hasLocallyAtomicAction A U).mpr hU) hV positive (C + 1) hSlope
  obtain ⟨r, ⟨hSmall, hBig⟩, hr⟩ :=
    ((hC.and_eventually hLower).and_eventually (eventually_gt_atTop (0 : ℝ))).exists
  nlinarith

/-- A single finite lower ray count yields a genuine finite exponential
annihilator of the whole source, from the Fourier-gap density theorem. -/
theorem exists_finiteExponentialAnnihilator_of_lower_ray_count
    (hGap : AtomicFourierGapRayLowerBound) (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (inst : Fintype ι), letI := inst
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨R, _, hR⟩ := exists_spectralGapUniqueness_of_finite_lower_ray_count hGap A positive hCount
  exact exists_finiteExponentialAnnihilator_of_spectralGapUniqueness A B U hA hB R hR

/-- One finite lower ray count and vanishing opposite quadratic lower
count imply finite modulated comb sums on both original records. -/
theorem finiteModulatedDiracCombSum_pair_of_lower_ray_count
    (hGap : AtomicFourierGapRayLowerBound) (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hQuadratic : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((B.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  obtain ⟨ι, inst, a, c, ha, hNonzero, hz⟩ :=
    exists_finiteExponentialAnnihilator_of_lower_ray_count hGap A B positive hCount T hA hB
  let _ := inst
  exact finiteModulatedDiracCombSum_pair_of_annihilator A B T hA hB hActual a c ha hNonzero hz hQuadratic

private theorem tendsto_rayCount_div_of_no_finite_lower_ray_count (A : LocallyFiniteCarrier)
    (positive : Bool) (h : ¬ HasFiniteLowerRayCount A positive) :
    Tendsto (fun r : ℝ => (originalRayCount A positive r : ℝ) / r) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have he : ∀ᶠ r : ℝ in atTop, ¬ (originalRayCount A positive r : ℝ) ≤ C * r :=
    not_frequently.mp fun hf => h ⟨C, hf⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), he] with r hr hC
  exact ((lt_div_iff₀ hr).mpr (lt_of_not_ge hC)).le

/-- When the two centered counts each have vanishing quadratic lower
count, any noncomb pair must have divergent linear counts on all four
rays. In particular the conclusion applies under joint subquadratic growth. -/
theorem tendsto_four_ray_counts_of_noncomb_pair
    (hGap : AtomicFourierGapRayLowerBound) (A B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActualA : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hActualB : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hNotComb : ¬ IsFiniteModulatedDiracCombSum T)
    (hQuadraticA : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((A.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2)
    (hQuadraticB : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((B.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount A positive r : ℝ) / r) atTop atTop) ∧
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount B positive r : ℝ) / r) atTop atTop) := by
  refine ⟨fun positive => tendsto_rayCount_div_of_no_finite_lower_ray_count A positive ?_,
    fun positive => tendsto_rayCount_div_of_no_finite_lower_ray_count B positive ?_⟩
  · intro hCount
    exact hNotComb (finiteModulatedDiracCombSum_pair_of_lower_ray_count
      hGap A B positive hCount T hA hB hActualA hQuadraticB).1
  · intro hCount
    have hFFT : AtomicOnCarrier A.reflect (𝓕 (𝓕 T)) := by
      rw [fourier_fourier_eq_originalDistributionReflection]
      exact atomicOnCarrier_originalDistributionReflection A T hA
    have hComb := finiteModulatedDiracCombSum_pair_of_lower_ray_count
      hGap B A.reflect positive hCount (𝓕 T) hB hFFT hActualB
      (by simpa only [centeredCount_reflect] using hQuadraticA)
    exact hNotComb hComb.1.of_fourier

/-- Joint subquadratic centered counts give the quadratic lower-count
hypotheses on both records of the four-ray theorem. -/
theorem tendsto_four_ray_counts_of_joint_subquadratic_noncomb_pair
    (hGap : AtomicFourierGapRayLowerBound) (A B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActualA : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hActualB : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hNotComb : ¬ IsFiniteModulatedDiracCombSum T)
    (hJoint : Asymptotics.IsLittleO atTop
      (fun r : ℝ => ((A.carrier ∩ Icc (-r) r).ncard : ℝ) + ((B.carrier ∩ Icc (-r) r).ncard : ℝ))
      (fun r : ℝ => r ^ 2)) :
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount A positive r : ℝ) / r) atTop atTop) ∧
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount B positive r : ℝ) / r) atTop atTop) := by
  have hSmall (c : ℝ) (hc : 0 < c) : ∀ᶠ r : ℝ in atTop,
      ((A.carrier ∩ Icc (-r) r).ncard : ℝ) + ((B.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2 := by
    filter_upwards [hJoint.bound (half_pos hc), eventually_gt_atTop (0 : ℝ)] with r hBound hr
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (sq_nonneg r)] at hBound
    exact hBound.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hc) (sq_pos_of_pos hr))
  apply tendsto_four_ray_counts_of_noncomb_pair hGap A B T hA hB hActualA hActualB hNotComb
  · intro c hc
    exact ((hSmall c hc).mono fun r h => (le_add_of_nonneg_right (by positivity)).trans_lt h).frequently
  · intro c hc
    exact ((hSmall c hc).mono fun r h => (le_add_of_nonneg_left (by positivity)).trans_lt h).frequently

end MeyerGeneralProblem
