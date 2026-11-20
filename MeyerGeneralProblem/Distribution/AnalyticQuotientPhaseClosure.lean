module

public import MeyerGeneralProblem.Distribution.AtomicLaplaceQuotient
public import MeyerGeneralProblem.Distribution.FrequencyTorusNonvanishing
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

/-!
# Phase closure for pole-free quotients

A small sphere with nonvanishing limiting denominator gives a uniform
boundary bound for nearby analytic extensions. The maximum modulus
principle preserves cancellation at the limiting phase.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set
open scoped Topology

/-- Local meromorphic cancellation gives a common analytic extension,
with the literal quotient value wherever the denominator is nonzero. -/
theorem exists_analytic_quotient_extension
    (f p : ℂ → ℂ) (Ω : Set ℂ)
    (hf : AnalyticOnNhd ℂ f Ω) (hp : AnalyticOnNhd ℂ p Ω)
    (hlocal : ∀ z ∈ Ω, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (fun u => f u / p u) =ᶠ[𝓝[≠] z] g) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧ ∀ z ∈ Ω, p z ≠ 0 → H z = f z / p z := by
  let F (z : ℂ) := f z / p z
  have hF : MeromorphicOn F Ω := fun z hz => (hf z hz).meromorphicAt.div (hp z hz).meromorphicAt
  let H := toMeromorphicNFOn F Ω
  refine ⟨H, ?_, ?_⟩
  · intro z hz
    have hm := (meromorphicNFOn_toMeromorphicNFOn F Ω) hz
    apply hm.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hF hz]
    exact (hF z hz).meromorphicOrderAt_nonneg_iff.mpr (hlocal z hz)
  · intro z hz hne
    have hA : AnalyticAt ℂ F z := (hf z hz).div (hp z hz) hne
    change toMeromorphicNFOn F Ω z = F z
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hF hz, toMeromorphicNFAt_eq_self.mpr hA.meromorphicNFAt]

/-- A nonzero entire denominator and local cancellation give exact
analytic multiplication on the original open region, including its zeros. -/
theorem exists_analytic_factorization_of_local_quotients
    (f p : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hf : AnalyticOnNhd ℂ f univ) (hp : AnalyticOnNhd ℂ p univ)
    (hp₀ : ∃ z, p z ≠ 0)
    (hlocal : ∀ z ∈ Ω, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (fun u => f u / p u) =ᶠ[𝓝[≠] z] g) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧ ∀ z ∈ Ω, f z = p z * H z := by
  obtain ⟨H, hH, hv⟩ := exists_analytic_quotient_extension f p Ω
    (hf.mono (subset_univ _)) (hp.mono (subset_univ _)) hlocal
  refine ⟨H, hH, fun z hz => ?_⟩
  have hpz := hp z (mem_univ z)
  have hno := entire_analyticOrderAt_ne_top_of_exists_ne_zero p hp hp₀ z
  have hne := hpz.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun he => hno (analyticOrderAt_eq_top.mpr he))
  have hΩnear : ∀ᶠ u in 𝓝[≠] z, u ∈ Ω := mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hz)
  have hnear : f =ᶠ[𝓝[≠] z] fun u => p u * H u := by
    filter_upwards [hne, hΩnear] with u hu huΩ
    rw [hv u huΩ hu, mul_comm, div_mul_cancel₀ _ hu]
  exact (((hf z (mem_univ z)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hpz.mul (hH z hz)).continuousAt).mp hnear).eq_of_nhds

/-- If entire numerators and denominators vary jointly continuously,
having no poles on an open region is preserved on the closure of the
parameters with analytic extensions. -/
theorem quotient_no_poles_of_dense_analytic_extensions
    {X : Type*} [TopologicalSpace X] (D : Set X) (hD : Dense D)
    (f p : X → ℂ → ℂ)
    (hf : Continuous (fun v : X × ℂ => f v.1 v.2))
    (hp : Continuous (fun v : X × ℂ => p v.1 v.2))
    (hf_entire : ∀ θ, AnalyticOnNhd ℂ (f θ) univ)
    (hp_entire : ∀ θ, AnalyticOnNhd ℂ (p θ) univ)
    (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hext : ∀ θ ∈ D, ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H Ω ∧
      ∀ z ∈ Ω, p θ z ≠ 0 → H z = f θ z / p θ z)
    (θ₀ : X) (hp₀ : ∃ z, p θ₀ z ≠ 0) (c : ℂ) (hc : c ∈ Ω) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      (fun z => f θ₀ z / p θ₀ z) =ᶠ[𝓝[≠] c] g := by
  have hno := entire_analyticOrderAt_ne_top_of_exists_ne_zero _ (hp_entire θ₀) hp₀ c
  have hloc := ((hp_entire θ₀ c (mem_univ c)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
    (fun h => hno (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hloc
  obtain ⟨δ, hδ, hlocal⟩ := hloc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hc)
  let r := min δ ε / 2
  have hr : 0 < r := div_pos (lt_min hδ hε) (by norm_num)
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ ε]
  have hrε : r < ε := by dsimp [r]; linarith [min_le_right δ ε]
  have hsub : closedBall c r ⊆ Ω := by
    intro z hz
    exact hball (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrε))
  have hboundary (z : ℂ) (hz : z ∈ sphere c r) : p θ₀ z ≠ 0 := by
    have hd := mem_sphere.mp hz
    have hzc : z ≠ c := by intro h; subst z; rw [dist_self] at hd; exact hr.ne' hd.symm
    exact hlocal (hd.trans_lt hrδ) (by simpa using hzc)
  have hSphere : (sphere c r).Nonempty := by
    refine ⟨c + (r : ℂ), ?_⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hSphere
    (((hp_entire θ₀).continuousOn.mono (subset_univ _)).norm)
  obtain ⟨z₂, _, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn hSphere
    (((hf_entire θ₀).continuousOn.mono (subset_univ _)).norm)
  let κ := ‖p θ₀ z₁‖ / 2
  let B := ‖f θ₀ z₂‖ + 1
  have hκ : 0 < κ := div_pos (norm_pos_iff.mpr (hboundary _ hz₁)) (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  let V := {v : X × ℂ | κ < ‖p v.1 v.2‖ ∧ ‖f v.1 v.2‖ < B}
  have hV : IsOpen V := (isOpen_lt continuous_const hp.norm).inter (isOpen_lt hf.norm continuous_const)
  have hprod : ({θ₀} : Set X) ×ˢ sphere c r ⊆ V := by
    rintro ⟨θ, z⟩ ⟨hθ, hz⟩
    change θ = θ₀ at hθ
    subst θ
    exact ⟨(by dsimp [κ] at *; linarith : κ < ‖p θ₀ z₁‖).trans_le (hmin hz),
      (hmax hz).trans_lt (by dsimp [B]; linarith)⟩
  obtain ⟨W, Y, hW, _, hθW, hY, hWY⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hV hprod
  have hW₀ : θ₀ ∈ W := hθW (mem_singleton θ₀)
  let M := B / κ
  have hM : 0 ≤ M := (div_pos hB hκ).le
  have hbounded (θ : X) (hθW : θ ∈ W) (hθD : θ ∈ D) (z : ℂ) (hz : z ∈ ball c r) :
      ‖f θ z / p θ z‖ ≤ M := by
    by_cases hne : p θ z = 0
    · simp [hne, hM]
    obtain ⟨F, hF, hFval⟩ := hext θ hθD
    have hd : DiffContOnCl ℂ F (ball c r) :=
      DifferentiableOn.diffContOnCl ((hF.mono hsub).differentiableOn.mono closure_ball_subset_closedBall)
    rw [← hFval z (hsub (ball_subset_closedBall hz)) hne]
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd _ (subset_closure hz)
    intro w hw
    have hs : w ∈ sphere c r := frontier_ball_subset_sphere hw
    have h := hWY (show (θ, w) ∈ W ×ˢ Y from ⟨hθW, hY hs⟩)
    change κ < ‖p θ w‖ ∧ ‖f θ w‖ < B at h
    have hpw : p θ w ≠ 0 := norm_pos_iff.mp (hκ.trans h.1)
    rw [hFval w (hsub (sphere_subset_closedBall hs)) hpw, norm_div]
    dsimp [M]
    gcongr <;> first | exact h.1.le | exact h.2.le
  apply analytic_extension_of_eventually_norm_le _ c
    ((hf_entire θ₀ c (mem_univ c)).meromorphicAt.div
      (hp_entire θ₀ c (mem_univ c)).meromorphicAt)
  refine ⟨M, hM, ?_⟩
  filter_upwards [ball_mem_nhds c hr] with z hz
  by_cases hne : p θ₀ z = 0
  · simp [hne, hM]
  let Q := W ∩ {θ : X | p θ z ≠ 0}
  have hfp : Continuous (fun θ => p θ z) := hp.comp (continuous_id.prodMk continuous_const)
  have hff : Continuous (fun θ => f θ z) := hf.comp (continuous_id.prodMk continuous_const)
  have hQ : IsOpen Q := hW.inter ((isOpen_ne : IsOpen {w : ℂ | w ≠ 0}).preimage hfp)
  have hQ₀ : θ₀ ∈ Q := ⟨hW₀, hne⟩
  let H := {θ : X | ‖f θ z‖ ≤ M * ‖p θ z‖}
  have hH : IsClosed H := isClosed_le hff.norm (continuous_const.mul hfp.norm)
  have hinc : Q ∩ D ⊆ H := fun θ hθ =>
    (div_le_iff₀ (norm_pos_iff.mpr hθ.1.2)).mp (by
      rw [← norm_div]
      exact hbounded θ hθ.1.1 hθ.2 z hz)
  have hout : θ₀ ∈ H := (closure_minimal hinc hH) (hD.open_subset_closure_inter hQ hQ₀)
  change ‖f θ₀ z / p θ₀ z‖ ≤ M
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hne)).mpr hout

open Adaptive
open scoped FourierTransform

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

/-- The original exponential polynomial with the phases of a full
spectral-module torus point. -/
def basisTorusExponentialSum (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (p : G →₀ ℂ) (θ : UnitAddTorus ι) : ℂ → ℂ :=
  finiteEntireExponentialSum (fun m : p.support => L m) (fun m => p m * basisTorusCharacter b m θ)

private theorem basisTorusExponentialSum_continuous (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (p : G →₀ ℂ) :
    Continuous (fun v : UnitAddTorus ι × ℂ => basisTorusExponentialSum b L p v.1 v.2) := by
  unfold basisTorusExponentialSum finiteEntireExponentialSum
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.mul ((basisTorusCharacter b j).continuous.comp continuous_fst)).mul
    (Complex.continuous_exp.comp (continuous_const.mul continuous_snd))

private theorem basisTorusExponentialSum_shift (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (p : G →₀ ℂ) (x : ℝ) (z : ℂ) :
    basisTorusExponentialSum b L p (torusLinearFlow (fun i => L (b i)) x) z =
      complexExponentialSum L p ((x : ℂ) + z) := by
  simp only [basisTorusExponentialSum, basisTorusCharacter_flow, finiteEntireExponentialSum_shift_real,
    finiteEntireExponentialSum_original_support]

/-- Nonzero original coefficients stay nontrivial at every torus phase. -/
theorem basisTorusExponentialSum_ne_zero_somewhere (b : Module.Basis ι ℤ G)
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0)
    (θ : UnitAddTorus ι) : ∃ z, basisTorusExponentialSum b L p θ z ≠ 0 := by
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hp
  apply finiteEntireExponentialSum_ne_zero_somewhere _ (hL.comp Subtype.coe_injective)
  refine ⟨⟨m, hm⟩, mul_ne_zero (Finsupp.mem_support_iff.mp hm) ?_⟩
  apply norm_ne_zero_iff.mp
  simp only [basisTorusCharacter, UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]
  exact one_ne_zero

/-- The numerator quotient of the original pair has removable off-real
singularities at every phase of the full original torus. -/
theorem originalPair_basisTorusQuotient_no_nonreal_poles
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L) (p R : G →₀ ℂ)
    (hp : p ≠ 0) (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U)
    (hFU : AtomicOnCarrier B (𝓕 U))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p s (originalFourierArray L B U) = (fun n => R n))
    (θ : UnitAddTorus ι) (c : ℂ) (hc : c.im ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      (fun z => basisTorusExponentialSum b L R θ z / basisTorusExponentialSum b L p θ z)
        =ᶠ[𝓝[≠] c] g := by
  let Ω := {z : ℂ | z.im ≠ 0}
  let orbit := torusLinearFlow (fun i => L (b i))
  have hΩ : IsOpen Ω := (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage Complex.continuous_im
  obtain ⟨H, hH, hval⟩ := exists_analytic_quotient_extension
    (complexExponentialSum L R) (complexExponentialSum L p) Ω
    ((complexExponentialSum_entire L R).mono (subset_univ _))
    ((complexExponentialSum_entire L p).mono (subset_univ _))
    (fun z hz => originalPair_quotient_no_nonreal_poles L hL p R A B hB U hU hFU hA s hR z hz)
  apply quotient_no_poles_of_dense_analytic_extensions (range orbit) (basis_frequencyFlow_denseRange b L hL)
    (basisTorusExponentialSum b L R) (basisTorusExponentialSum b L p)
    (basisTorusExponentialSum_continuous b L R) (basisTorusExponentialSum_continuous b L p)
    (fun _ => finiteEntireExponentialSum_entire _ _) (fun _ => finiteEntireExponentialSum_entire _ _)
    Ω hΩ _ θ _ c hc
  · rintro _ ⟨x, rfl⟩
    have hshift (z : ℂ) (hz : z ∈ Ω) : (x : ℂ) + z ∈ Ω := by
      simpa only [Ω, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, zero_add] using hz
    refine ⟨fun z => H ((x : ℂ) + z), ?_, ?_⟩
    · intro z hz
      exact (hH _ (hshift z hz)).comp (by fun_prop)
    · intro z hz hne
      simp only [orbit, basisTorusExponentialSum_shift] at hne ⊢
      exact hval _ (hshift z hz) hne
  · exact basisTorusExponentialSum_ne_zero_somewhere b L hL p hp θ

/-- At every full-torus phase of a broad pair, the original numerator is
the denominator times an analytic function on the two open half-planes. -/
theorem originalPair_basisTorus_analytic_factorization
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L) (p R : G →₀ ℂ)
    (hp : p ≠ 0) (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U)
    (hFU : AtomicOnCarrier B (𝓕 U))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p s (originalFourierArray L B U) = (fun n => R n))
    (θ : UnitAddTorus ι) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {z : ℂ | z.im ≠ 0} ∧
      ∀ z : ℂ, z.im ≠ 0 →
        basisTorusExponentialSum b L R θ z = basisTorusExponentialSum b L p θ z * H z := by
  exact exists_analytic_factorization_of_local_quotients _ _ _
    ((isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage Complex.continuous_im)
    (finiteEntireExponentialSum_entire _ _) (finiteEntireExponentialSum_entire _ _)
    (basisTorusExponentialSum_ne_zero_somewhere b L hL p hp θ)
    (originalPair_basisTorusQuotient_no_nonreal_poles b L hL p R hp A B hB U hU hFU hA s hR θ)

end

end MeyerGeneralProblem
