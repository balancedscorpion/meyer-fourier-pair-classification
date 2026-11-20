module

public import MeyerGeneralProblem.Gram.CanonicalGroupedGram
public import MeyerGeneralProblem.Sampling.CanonicalGroupedFinsupp

@[expose] public section

/-!+# Genuine spectral-window lower bounds for grouped universal atoms

The actual universal `L²` synthesis has density-weighted grouped exponential
energy. The canonical finite-window Riesz theorem therefore gives a positive
universal Gram floor without a gap-dependent change of coordinates.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Finset

/-- The full-line `L²` norm is its ordinary real energy integral. -/
theorem groupedFullLineL2_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖^2 = ∫ t : ℝ, ‖f t‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re (L2.integrable_inner f f)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (norm_sq_eq_re_inner (𝕜 := ℂ) (f t)).symm))

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- The actual grouped universal atom has exactly the square-root-density
times grouped exponential representative, almost everywhere. -/
theorem universalAtom_coeFn (m : ℕ) (hm : 1 ≤ m) (x : G.Index) :
    (G.universalAtom m hm x : ℝ → ℂ) =ᵐ[volume] fun t =>
      (Real.sqrt (gramDensity m t) : ℂ)*groupedExponentialInitial (G.realNodes x.1) x.2 t := by
  have hterms (a : Fin (G.size x.1)) :
      (groupedNewtonWeight (G.nodes x.1) x.2 a • universalGramAtom m hm (G.realNodes x.1 a) :
        Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] fun t =>
        groupedNewtonWeight (G.nodes x.1) x.2 a * universalGramAtomFun m (G.realNodes x.1 a) t := by
    filter_upwards [Lp.coeFn_smul (groupedNewtonWeight (G.nodes x.1) x.2 a)
      (universalGramAtom m hm (G.realNodes x.1 a)),
      (memLp_universalGramAtomFun hm (G.realNodes x.1 a)).coeFn_toLp] with t ht hv
    simp only [ht,Pi.smul_apply,smul_eq_mul]
    exact congrArg (groupedNewtonWeight (G.nodes x.1) x.2 a * ·) hv
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun a => groupedNewtonWeight (G.nodes x.1) x.2 a • universalGramAtom m hm (G.realNodes x.1 a)),
      Filter.eventually_all.2 hterms] with t ht hall
  change (∑ a, groupedNewtonWeight (G.nodes x.1) x.2 a • universalGramAtom m hm (G.realNodes x.1 a) :
    Lp ℂ 2 (volume : Measure ℝ)) t = _
  rw [ht]
  simp only [Finset.sum_apply,hall,universalGramAtomFun]
  have hDD := groupedRealDividedDifference_eq_analytic (G.realNodes x.1) (G.realNodes_injective x.1) x.2
    (fun s => gramPhase s t)
  change groupedRealDividedDifference (G.realNodes x.1) x.2 (fun s => gramPhase s t) =
    groupedExponentialInitial (G.realNodes x.1) x.2 t at hDD
  rw [← hDD,groupedRealDividedDifference,mul_sum]
  apply sum_congr rfl
  intro a _
  have hw := groupedNewtonWeight_ofReal (G.realNodes x.1) x.2 a
  change groupedNewtonWeight (G.nodes x.1) x.2 a = _ at hw
  rw [hw]
  ring

/-- Exact density-weighted pointwise energy of a finite synthesis of actual
universal grouped atoms, before any operator extension. -/
theorem universalAtom_finiteSynthesis_energy_ae {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 1 ≤ m) (x : ι → G.Index) (c : ι → ℂ) :
    (fun t => ‖(∑ i, c i • G.universalAtom m hm (x i) : Lp ℂ 2 (volume : Measure ℝ)) t‖^2) =ᵐ[volume]
      fun t => gramDensity m t * ‖∑ i, c i*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t‖^2 := by
  have hterms (i : ι) :
      (c i • G.universalAtom m hm (x i) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] fun t =>
        c i*((Real.sqrt (gramDensity m t) : ℂ)*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t) := by
    filter_upwards [Lp.coeFn_smul (c i) (G.universalAtom m hm (x i)),G.universalAtom_coeFn m hm (x i)] with t ht hx
    simp only [ht,Pi.smul_apply,smul_eq_mul,hx]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => c i • G.universalAtom m hm (x i)),
    Filter.eventually_all.2 hterms] with t ht hi
  simp only [ht,Finset.sum_apply,hi]
  have he : (∑ i, c i*((Real.sqrt (gramDensity m t) : ℂ)*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t)) =
      (Real.sqrt (gramDensity m t) : ℂ)*(∑ i, c i*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (gramDensity_nonneg hm t)]

/-- The density-weighted finite grouped synthesis energy is integrable. -/
theorem integrable_universalAtom_finiteSynthesis_energy {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 1 ≤ m) (x : ι → G.Index) (c : ι → ℂ) :
    Integrable (fun t => gramDensity m t *
      ‖∑ i, c i*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t‖^2) := by
  have h := (Lp.memLp (∑ i, c i • G.universalAtom m hm (x i))).norm.integrable_sq
  exact h.congr (G.universalAtom_finiteSynthesis_energy_ae m hm x c)

/-- The exact universal spectral density transfers finite window energy
to the actual grouped `L²` synthesis norm. -/
theorem universalAtom_finiteSynthesis_ge_window {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 1 ≤ m) (x : ι → G.Index) (c : ι → ℂ) (W : ℝ) :
    (2*gramNormalization m*(1+4*W^2)⁻¹^(2*m)) *
      (∫ t : ℝ in Set.Icc (-W) W,
        ‖∑ i, c i*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t‖^2) ≤
      ‖∑ i, c i • G.universalAtom m hm (x i)‖^2 := by
  let energy := fun t => ‖∑ i, c i*groupedExponentialInitial (G.realNodes (x i).1) (x i).2 t‖^2
  let density := 2*gramNormalization m*(1+4*W^2)⁻¹^(2*m)
  have henergy : Continuous energy := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (continuous_groupedExponentialInitial _ _)
  have hint := G.integrable_universalAtom_finiteSynthesis_energy m hm x c
  have hlocal : IntegrableOn energy (Set.Icc (-W) W) := henergy.continuousOn.integrableOn_compact isCompact_Icc
  have hwindow : density*(∫ t : ℝ in Set.Icc (-W) W, energy t) ≤
      ∫ t : ℝ in Set.Icc (-W) W, gramDensity m t*energy t := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hlocal.const_mul density) hint.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right (gramDensity_lower_bound_on_Icc hm ht) (sq_nonneg _)
  have hfull : (∫ t : ℝ in Set.Icc (-W) W, gramDensity m t*energy t) ≤
      ∫ t : ℝ, gramDensity m t*energy t :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun t => mul_nonneg (gramDensity_nonneg hm t) (sq_nonneg _))) hint
  rw [groupedFullLineL2_norm_sq,integral_congr_ae (G.universalAtom_finiteSynthesis_energy_ae m hm x c)]
  exact hwindow.trans hfull

/-- The spectral-window transfer applies to arbitrary finitely supported
grouped coordinates, without requiring support to be a union of groups. -/
theorem universalAtom_finsupp_ge_window (m : ℕ) (hm : 1 ≤ m)
    (c : G.Index →₀ ℂ) (W : ℝ) :
    (2*gramNormalization m*(1+4*W^2)⁻¹^(2*m)) *
      (∫ t : ℝ in Set.Icc (-W) W,
        ‖c.sum (fun x z => z*groupedExponentialInitial (G.realNodes x.1) x.2 t)‖^2) ≤
      ‖Finsupp.linearCombination ℂ (G.universalAtom m hm) c‖^2 := by
  classical
  have h := G.universalAtom_finiteSynthesis_ge_window m hm (fun x : c.support => x.val)
    (fun x : c.support => c x.val) W
  have hsum := Finset.sum_coe_sort c.support (fun x => c x • G.universalAtom m hm x)
  have hpoly (t : ℝ) := Finset.sum_coe_sort c.support
    (fun x => c x*groupedExponentialInitial (G.realNodes x.1) x.2 t)
  rw [hsum] at h
  simp_rw [hpoly] at h
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using h

end OrderedCarrierGrouping

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- A genuine positive finite-synthesis floor for the actual canonical
universal grouped atoms, transferred from exact upper-density Riesz theory. -/
theorem exists_universalGrouped_finsupp_lower (hd : 0 < d) (m : ℕ) (hm : 1 ≤ m)
    {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : horder.signedGrouping.Index →₀ ℂ,
      a*(c.sum fun _ z => ‖z‖^2) ≤
        ‖Finsupp.linearCombination ℂ (horder.signedGrouping.universalAtom m hm) c‖^2 := by
  obtain ⟨A,hA,hbound⟩ := canonicalGrouping_groupedExponential_finsupp_lower S.signedSquareImage horder hd hW hS
  let b := 2*gramNormalization m*(1+4*W^2)⁻¹^(2*m)
  have hb : 0 < b := by dsimp [b]; exact mul_pos (mul_pos two_pos (gramNormalization_pos hm)) (by positivity)
  refine ⟨b*A,mul_pos hb hA,?_⟩
  intro c
  have hnodes (C : CanonicalClusterIndex S.signedSquareImage d) :
      horder.signedGrouping.realNodes C=horder.realClusterNode C := funext (horder.signedGrouping_realNodes C)
  have hwindow := horder.signedGrouping.universalAtom_finsupp_ge_window m hm c W
  simp_rw [hnodes] at hwindow
  calc
    (b*A)*(c.sum fun _ z => ‖z‖^2) = b*(A*(c.sum fun _ z => ‖z‖^2)) := by ring
    _ ≤ b*(∫ t : ℝ in Set.Icc (-W) W,
        ‖c.sum (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t)‖^2) :=
      mul_le_mul_of_nonneg_left (hbound c) hb.le
    _ ≤ _ := hwindow

/-- The actual universal grouped synthesis has a uniform Hilbert lower
floor on the entire coefficient space, not only on finite test vectors. -/
theorem exists_universalGrouped_synthesis_lower (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : CoefficientSpace horder.signedGrouping.Index,
      a*‖c‖^2 ≤ ‖(horder.universalGroupedBesselAnalysis hd m hm).synthesis c‖^2 := by
  classical
  obtain ⟨a,ha,hbound⟩ := horder.exists_universalGrouped_finsupp_lower hd m
    (by have := (le_max_left _ _).trans hm; omega) hW hS
  refine ⟨a,ha,?_⟩
  apply (horder.universalGroupedBesselAnalysis hd m hm).synthesis_norm_sq_lower_of_finsuppGram
  intro c
  simpa only [BesselAnalysis.norm_sq_finsupp_linearCombination_eq_gramForm_re] using hbound c

/-- The actual canonical universal grouped Gram has a strictly positive
Loewner floor, derived from the genuine density condition. -/
theorem exists_universalGroupedGramOperator_lowerBound (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ a : ℝ, 0 < a ∧ a • (1 : CoefficientSpace horder.signedGrouping.Index →L[ℂ]
      CoefficientSpace horder.signedGrouping.Index) ≤ horder.universalGroupedGramOperator hd m hm := by
  obtain ⟨a,ha,hlower⟩ := horder.exists_universalGrouped_synthesis_lower hd m hm hW hS
  refine ⟨a,ha,?_⟩
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · apply IsSelfAdjoint.sub
    · exact (ContinuousLinearMap.isPositive_adjoint_comp_self
        (horder.universalGroupedBesselAnalysis hd m hm).synthesis).isSelfAdjoint
    · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      intro u v
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      have hreal (c : ℝ) (w : CoefficientSpace horder.signedGrouping.Index) : c • w = (c : ℂ) • w := by
        ext i
        simp only [lp.coeFn_smul, Pi.smul_apply]
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) c (w i)
      rw [hreal, hreal]
      exact (inner_smul_real_left (𝕜 := ℂ) u v _).trans
        (inner_smul_real_right (𝕜 := ℂ) u v _).symm
  · intro c
    change 0 ≤ RCLike.re (inner ℂ ((horder.universalGroupedGramOperator hd m hm-a • 1) c) c)
    rw [sub_apply,inner_sub_left,map_sub]
    simp only [universalGroupedGramOperator,coefficientGram,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left,one_apply_eq_self,smul_apply]
    rw [← norm_sq_eq_re_inner,RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_real_left,RCLike.smul_re,
      ← norm_sq_eq_re_inner]
    linarith [hlower c]

end BoundedClusterOrder

end

end MeyerGeneralProblem
