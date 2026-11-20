module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

/-!
# Counting the actual support of discrete distributions

A weakly continuous family of distributions can lose sites when
atoms collide. Open sets detect the actual distributional support by
compact Schwartz tests. Counting distinct sites then gives a
measurable family of locally finite positive measures.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Metric Set
open scoped ENNReal Topology

private theorem eventually_zero_of_outside_tsupport (f : SchwartzMap ℝ ℂ) {x : ℝ}
    (hx : x ∉ tsupport f) : (f : ℝ → ℂ) =ᶠ[𝓝 x] 0 := by
  filter_upwards [(isClosed_tsupport (f : ℝ → ℂ)).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

/-- The intrinsic distributional support is contained in any locally
finite carrier supporting the original compact-test action. -/
theorem dsupport_subset_of_discrete_support (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T) :
    dsupport T ⊆ S.carrier := by
  intro x hx
  by_contra hxS
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp S.carrier_isClosed.isOpen_compl x hxS
  obtain ⟨f, hf, hnz⟩ :=
    (mem_dsupport_iff_forall_exists_ne x).mp hx (ball x r) (mem_ball_self hr) isOpen_ball
  apply hnz
  apply hT f ((isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
    (hf.trans ball_subset_closedBall))
  intro a ha
  apply eventually_zero_of_outside_tsupport f
  exact fun hm => hb (hf hm) ha

private theorem compactTest_eq_zero_of_supportedAt_of_vanishing
    {T : TemperedDistribution ℝ ℂ} {x : ℝ} (hT : DistributionSupportedAt x T)
    {O : Set ℝ} (hO : O ∈ 𝓝 x) (hV : IsVanishingOn T O)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) : T f = 0 := by
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hO
  let b : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let g : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hg : g.HasTemperateGrowth :=
    (b.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let f₀ := SchwartzMap.smulLeftCLM ℂ g f
  have hSup := SchwartzMap.tsupport_smulLeftCLM_subset g f
  have hO₀ : tsupport f₀ ⊆ O := by
    refine hSup.trans (inter_subset_right.trans ((tsupport_comp_subset rfl _).trans ?_))
    rwa [b.tsupport_eq]
  have hf₀ : HasCompactSupport (f₀ : ℝ → ℂ) :=
    hf.of_isClosed_subset (isClosed_tsupport _) (hSup.trans inter_subset_left)
  have hfg : ((f - f₀ : SchwartzMap ℝ ℂ) : ℝ → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [b.eventuallyEq_one] with y hy
    have hby : b y = 1 := hy
    change f y - f₀ y = 0
    simp [f₀, g, SchwartzMap.smulLeftCLM_apply_apply hg, hby]
  have h := hT (f - f₀) (hf.sub hf₀) hfg
  rw [map_sub, sub_eq_zero, hV f₀ hO₀] at h
  exact h

/-- For a locally finite original carrier, the intrinsic support alone
still supports every compact test. This also applies to point jets. -/
theorem distributionSupportedOn_dsupport_of_discrete_support (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T) :
    DistributionSupportedOn (dsupport T) T := by
  intro f hf hAway
  classical
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball 0).mp hf.isBounded
  let E : Set S.subtype := Subtype.val ⁻¹' (S.carrier ∩ Icc (-R) R)
  have hE : E.Finite :=
    (S.finite_inter_Icc (-R) R).preimage (Set.injOn_of_injective Subtype.val_injective)
  rw [supportedOn_finite_localization S T hT f hf hE.toFinset (fun a ha => by
    apply eventually_zero_of_outside_tsupport f
    intro hm
    have hr : |(a : ℝ)| < R := by simpa [Real.dist_eq] using hR hm
    exact ha (hE.mem_toFinset.mpr ⟨a.property, (abs_lt.mp hr).1.le, (abs_lt.mp hr).2.le⟩))]
  apply Finset.sum_eq_zero
  intro a _
  let T₀ := TemperedDistribution.smulLeftCLM ℂ (S.isolationSchwartz a) T
  have ha : DistributionSupportedAt (a : ℝ) T₀ := supportedOn_isolation_supportedAt S T hT a
  change T₀ f = 0
  by_cases hIn : (a : ℝ) ∈ dsupport T
  · exact ha f hf (hAway a hIn)
  · obtain ⟨O, hO, hOpen, haO⟩ := (notMem_dsupport_iff (a : ℝ)).mp hIn
    exact compactTest_eq_zero_of_supportedAt_of_vanishing ha (hOpen.mem_nhds haO)
      (Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hO
        (S.isolationSchwartz a).hasTemperateGrowth) f hf

/-- For a distribution supported on a locally finite carrier, an open
set hits the intrinsic support exactly when a compact test there has
nonzero action. -/
theorem nonempty_dsupport_inter_iff_exists_compactTest (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    {O : Set ℝ} (hO : IsOpen O) :
    (dsupport T ∩ O).Nonempty ↔ ∃ f : SchwartzMap ℝ ℂ,
      HasCompactSupport (f : ℝ → ℂ) ∧ tsupport f ⊆ O ∧ T f ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hxO⟩
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hO x hxO
    obtain ⟨f, hfs, hfn⟩ :=
      (mem_dsupport_iff_forall_exists_ne x).mp hx (ball x r) (mem_ball_self hr) isOpen_ball
    exact ⟨f, (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
      (hfs.trans ball_subset_closedBall), hfs.trans hb, hfn⟩
  · rintro ⟨f, hf, hs, hn⟩
    by_contra hMiss
    apply hn
    apply distributionSupportedOn_dsupport_of_discrete_support S T hT f hf
    intro x hx
    apply eventually_zero_of_outside_tsupport f
    exact fun hxs => hMiss ⟨x, hx, hs hxs⟩

section WeakFamily

variable {Θ : Type*} [TopologicalSpace Θ]

/-- Meeting an open set is an open condition on the parameter of a
weakly continuous family of discrete distributions. -/
theorem isOpen_dsupport_hit (S : Θ → LocallyFiniteCarrier)
    (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {O : Set ℝ} (hO : IsOpen O) :
    IsOpen {θ | (dsupport (T θ) ∩ O).Nonempty} := by
  let F := {f : SchwartzMap ℝ ℂ // HasCompactSupport (f : ℝ → ℂ) ∧ tsupport f ⊆ O}
  have hEq : {θ | (dsupport (T θ) ∩ O).Nonempty} = ⋃ f : F, {θ | T θ f ≠ 0} := by
    ext θ
    rw [mem_iUnion]
    exact (nonempty_dsupport_inter_iff_exists_compactTest _ _ (hT θ) hO).trans
      ⟨fun ⟨f, hfc, hfs, hfn⟩ => ⟨⟨f, hfc, hfs⟩, hfn⟩,
       fun ⟨f, hfn⟩ => ⟨f, f.property.1, f.property.2, hfn⟩⟩
  rw [hEq]
  exact isOpen_iUnion fun f => isClosed_singleton.isOpen_compl.preimage (hCont f f.property.1)

/-- At least `k` actual sites in a bounded open set is an open
condition. Disjoint local tests detect distinct sites even at collisions. -/
theorem isOpen_le_ncard_dsupport_inter (S : Θ → LocallyFiniteCarrier)
    (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {O : Set ℝ} (hO : IsOpen O) {a b : ℝ} (hBound : O ⊆ Icc a b) (k : ℕ) :
    IsOpen {θ | k ≤ (dsupport (T θ) ∩ O).ncard} := by
  classical
  have hFin (θ : Θ) : (dsupport (T θ) ∩ O).Finite :=
    ((S θ).finite_inter_Icc a b).subset
      (inter_subset_inter (dsupport_subset_of_discrete_support _ _ (hT θ)) hBound)
  apply isOpen_iff_forall_mem_open.mpr
  intro θ hθ
  have hCard : k ≤ (hFin θ).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ (hFin θ)]
    exact hθ
  obtain ⟨t, ht, htCard⟩ := Finset.le_card_iff_exists_subset_card.mp hCard
  obtain ⟨W, hW, hDis⟩ := t.finite_toSet.t2_separation
  let V (x : ℝ) := {η | (dsupport (T η) ∩ (W x ∩ O)).Nonempty}
  refine ⟨⋂ x ∈ t, V x, ?_, isOpen_biInter_finset (fun x _ =>
    isOpen_dsupport_hit S T hT hCont ((hW x).2.inter hO)), ?_⟩
  · intro η hη
    have hExists (x : (t : Set ℝ)) : ∃ y : ↥(dsupport (T η) ∩ O), (y : ℝ) ∈ W x := by
      obtain ⟨y, hyT, hyW, hyO⟩ := mem_iInter₂.mp hη x (Finset.mem_coe.mp x.property)
      exact ⟨⟨y, hyT, hyO⟩, hyW⟩
    choose y hy using hExists
    have hInj : Function.Injective y := by
      intro x x' he
      by_contra hne
      have hv : (x : ℝ) ≠ (x' : ℝ) := fun he' => hne (Subtype.ext he')
      exact (Set.disjoint_left.mp (hDis x.property x'.property hv)) (hy x) (he ▸ hy x')
    have hLe := Function.Embedding.encard_le (⟨y, hInj⟩ : (t : Set ℝ) ↪ ↥(dsupport (T η) ∩ O))
    rw [encard_coe_eq_coe_finsetCard, htCard, ← (hFin η).cast_ncard_eq] at hLe
    exact_mod_cast hLe
  · refine mem_iInter₂.mpr fun x hx => ?_
    have hxT := (hFin θ).mem_toFinset.mp (ht hx)
    exact ⟨x, hxT.1, (hW x).1, hxT.2⟩

end WeakFamily

/-- The positive measure assigning mass one to each actual support site. -/
def discreteSupportCount (T : TemperedDistribution ℝ ℂ) : Measure ℝ :=
  Measure.count.restrict (dsupport T)

theorem discreteSupportCount_apply_of_finite (T : TemperedDistribution ℝ ℂ)
    {B : Set ℝ} (hB : MeasurableSet B) (hF : (dsupport T ∩ B).Finite) :
    discreteSupportCount T B = ((dsupport T ∩ B).ncard : ℝ≥0∞) := by
  rw [discreteSupportCount, Measure.restrict_apply hB, inter_comm,
    Measure.count_apply_finite _ hF, Set.ncard_eq_toFinset_card _ hF]

/-- The counting detector has finite mass on some neighborhood of
each point. No global uniform count is required for local finiteness. -/
theorem isLocallyFiniteMeasure_discreteSupportCount (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T) :
    IsLocallyFiniteMeasure (discreteSupportCount T) := by
  refine ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  rw [discreteSupportCount_apply_of_finite T measurableSet_Ioo
    ((S.finite_inter_Ioo (x - 1) (x + 1)).subset
      (inter_subset_inter_left _ (dsupport_subset_of_discrete_support S T hT)))]
  exact ENNReal.natCast_lt_top _

private theorem measurable_discreteSupportCount_apply_open {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {O : Set ℝ} (hO : IsOpen O) {a b : ℝ} (hBound : O ⊆ Icc a b) :
    Measurable (fun θ => discreteSupportCount (T θ) O) := by
  have hCount : Measurable (fun θ => (dsupport (T θ) ∩ O).ncard) := by
    apply measurable_of_Ioi
    intro k
    simpa only [preimage, mem_Ioi, Nat.succ_le_iff] using
      (isOpen_le_ncard_dsupport_inter S T hT hCont hO hBound (k + 1)).measurableSet
  have hEq (θ : Θ) : discreteSupportCount (T θ) O = ((dsupport (T θ) ∩ O).ncard : ℝ≥0∞) :=
    discreteSupportCount_apply_of_finite _ hO.measurableSet
      (((S θ).finite_inter_Icc a b).subset
        (inter_subset_inter (dsupport_subset_of_discrete_support _ _ (hT θ)) hBound))
  simp only [hEq]
  change Measurable ((fun k : ℕ => (k : ℝ≥0∞)) ∘ (fun θ => (dsupport (T θ) ∩ O).ncard))
  exact (measurable_of_countable _).comp hCount

/-- The unit counting measure of the actual distributional support is
a measurable family. Its evaluations on arbitrary Borel sets are
obtained from bounded open evaluations by finite restriction. -/
theorem measurable_discreteSupportCount {Θ : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f)) :
    Measurable (fun θ => discreteSupportCount (T θ)) := by
  let I (n : ℕ) : Set ℝ := Ioo (-(n : ℝ)) n
  let μ (n : ℕ) (θ : Θ) := (discreteSupportCount (T θ)).restrict (I n)
  have hI (n : ℕ) : IsOpen (I n) := isOpen_Ioo
  have hFinite (n : ℕ) (θ : Θ) : μ n θ univ < ⊤ := by
    change (discreteSupportCount (T θ)).restrict (I n) univ < ⊤
    rw [Measure.restrict_apply_univ, discreteSupportCount_apply_of_finite _
      (hI n).measurableSet (((S θ).finite_inter_Ioo (-(n : ℝ)) n).subset
        (fun x hx => ⟨dsupport_subset_of_discrete_support _ _ (hT θ) hx.1, hx.2⟩))]
    exact ENNReal.natCast_lt_top _
  have hOpen (n : ℕ) {O : Set ℝ} (hO : IsOpen O) : Measurable (fun θ => μ n θ O) := by
    simpa only [μ, Measure.restrict_apply hO.measurableSet] using
      measurable_discreteSupportCount_apply_open S T hT hCont (hO.inter (hI n))
        (inter_subset_right.trans Ioo_subset_Icc_self)
  have hBounded (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
      Measurable (fun θ => μ n θ B) := by
    have hGen : (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom {O : Set ℝ | IsOpen O} := BorelSpace.measurable_eq
    have hPi : IsPiSystem {O : Set ℝ | IsOpen O} := by
      intro O hO P hP _
      change IsOpen O at hO
      change IsOpen P at hP
      exact hO.inter hP
    induction B, hB using MeasurableSpace.induction_on_inter hGen hPi with
    | empty => simp
    | basic O hO => exact hOpen n hO
    | compl O hO ih =>
      have hEq (θ : Θ) : μ n θ Oᶜ = μ n θ univ - μ n θ O :=
        measure_compl hO ((measure_mono (subset_univ O)).trans_lt (hFinite n θ)).ne
      rw [show (fun θ => μ n θ Oᶜ) = (fun θ => μ n θ univ) - (fun θ => μ n θ O) from funext hEq]
      exact (hOpen n isOpen_univ).sub ih
    | iUnion B hDis hMeas ih =>
      simp only [measure_iUnion hDis hMeas]
      exact Measurable.tsum ih
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have hUnion : (⋃ n : ℕ, B ∩ I n) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      exact hx.1
    · intro hx
      obtain ⟨n : ℕ, hn⟩ := exists_nat_gt |x|
      exact mem_iUnion.mpr ⟨n, hx, abs_lt.mp hn⟩
  have hMono : Monotone (fun n : ℕ => B ∩ I n) := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact inter_subset_inter_right _ (Ioo_subset_Ioo (neg_le_neg hab') hab')
  have hEq (θ : Θ) : discreteSupportCount (T θ) B = ⨆ n : ℕ, μ n θ B := by
    simp only [μ, Measure.restrict_apply hB, ← hMono.measure_iUnion, hUnion]
  simp only [hEq]
  exact Measurable.iSup (fun n => hBounded n hB)

/-- Integrating any nonnegative Borel function against the detector is
measurable in the weak-family parameter. -/
theorem measurable_lintegral_discreteSupportCount {Θ : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun θ => ∫⁻ x, f x ∂discreteSupportCount (T θ)) :=
  (Measure.measurable_lintegral hf).comp (measurable_discreteSupportCount S T hT hCont)

end
end MeyerGeneralProblem
