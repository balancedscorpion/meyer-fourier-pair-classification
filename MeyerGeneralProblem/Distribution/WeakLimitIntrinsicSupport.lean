module

public import MeyerGeneralProblem.Distribution.DiscreteSupportCounting
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Intrinsic support and locally finite weak limits

A finite smooth partition localizes each compact Schwartz test to the
complement of the intrinsic support. A common bound on translated unit
windows also controls each weak limit, since distinct limiting points
can be detected by disjoint compact tests that persist under convergence.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter Metric Set
open scoped ContDiff Manifold Topology

/-- The intrinsic distributional support controls all compact Schwartz tests,
by a finite smooth partition subordinate to local vanishing neighborhoods. -/
theorem distributionSupportedOn_intrinsic_dsupport (U : TemperedDistribution ℝ ℂ) :
    DistributionSupportedOn (dsupport U) U := by
  intro f hf hAway
  classical
  let K := tsupport (f : ℝ → ℂ)
  have hOut (x : K) : (x : ℝ) ∉ dsupport U := by
    intro hx
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hAway x hx)) x.property
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball 0).mp hf.isBounded
  have hOpenCover (x : K) : ∃ V : Set ℝ, IsOpen V ∧ (x : ℝ) ∈ V ∧
      V ⊆ ball 0 R ∧ IsVanishingOn U V := by
    obtain ⟨O, hO, hOpen, hx⟩ := (notMem_dsupport_iff (x : ℝ)).mp (hOut x)
    exact ⟨O ∩ ball 0 R, hOpen.inter isOpen_ball, ⟨hx, hR x.property⟩,
      inter_subset_right, fun g hg => hO g (hg.trans inter_subset_left)⟩
  choose V hV using hOpenCover
  have hCover : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩
  obtain ⟨E, hE⟩ := hf.elim_finite_subcover V (fun x => (hV x).1) hCover
  let O (i : ↥(E : Set K)) := V i
  have hCover' : K ⊆ ⋃ i, O i := by
    intro x hx
    obtain ⟨i, hi, hxO⟩ := mem_iUnion₂.mp (hE hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxO⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ)) (isClosed_tsupport _) O (fun i => (hV i).1) hCover'
  let ψ (i : ↥(E : Set K)) : ℝ → ℂ := Complex.ofRealCLM ∘ ρ i
  have hSupport (i : ↥(E : Set K)) : tsupport (ψ i) ⊆ O i :=
    (tsupport_comp_subset Complex.ofRealCLM.map_zero _).trans (hρ i)
  have hGrowth (i : ↥(E : Set K)) : (ψ i).HasTemperateGrowth := by
    have hC : HasCompactSupport (ψ i) := (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset
      (isClosed_tsupport _) ((hSupport i).trans ((hV i).2.2.1.trans ball_subset_closedBall))
    have hSmooth : ContDiff ℝ ∞ (ρ i : ℝ → ℝ) :=
      contMDiff_iff_contDiff.mp (ρ i).contMDiff
    exact hC.hasTemperateGrowth (Complex.ofRealCLM.contDiff.comp hSmooth)
  let g (i : ↥(E : Set K)) : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (ψ i) f
  have hLocal (i : ↥(E : Set K)) : U (g i) = 0 :=
    (hV i).2.2.2 (g i)
      ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ i) f).trans (inter_subset_right.trans (hSupport i)))
  have hSum : ∑ i, g i = f := by
    ext x
    simp only [_root_.sum_apply, g, SchwartzMap.smulLeftCLM_apply_apply (hGrowth _), smul_eq_mul,
      ψ, Function.comp_apply, Complex.ofRealCLM_apply, ← Finset.sum_mul, ← Complex.ofReal_sum]
    by_cases hx : x ∈ K
    · have hOne := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at hOne
      rw [hOne, Complex.ofReal_one, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [← hSum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hLocal i

private theorem card_finset_in_weakLimit_support_le_of_window_count {ι : Type*}
    {p : Filter ι} [p.NeBot] (S : ι → LocallyFiniteCarrier)
    (T : ι → TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
    (hT : ∀ j, DistributionSupportedOn (S j).carrier (T j))
    (hWeak : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Tendsto (fun j => T j f) p (𝓝 (U f)))
    (L : ℝ) {K : ℕ} (hCount : ∀ j r, ((S j).carrier ∩ Ico r (r + L)).ncard ≤ K)
    (r : ℝ) (E : Finset ℝ) (hE : (E : Set ℝ) ⊆ dsupport U ∩ Ico r (r + L)) :
    E.card ≤ K := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hNE
  · simp
  let M := E.max' hNE
  have hM : M < r + L := (hE (E.max'_mem hNE)).2.2
  let δ := (r + L - M) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hM)
  let a := r - δ
  let O := Ioo a (a + L)
  have hOpen : IsOpen O := isOpen_Ioo
  have hO (x : ↥(E : Set ℝ)) : (x : ℝ) ∈ O := by
    have hLeft : r ≤ (x : ℝ) := (hE x.property).2.1
    have hRight : (x : ℝ) ≤ M := E.le_max' x x.property
    exact ⟨by dsimp [a]; linarith only [hLeft, hδ],
      by dsimp [a, δ]; linarith only [hRight, hM]⟩
  obtain ⟨W, hW, hDis⟩ := E.finite_toSet.t2_separation
  have hTest (x : ↥(E : Set ℝ)) : ∃ f : SchwartzMap ℝ ℂ,
      HasCompactSupport (f : ℝ → ℂ) ∧ tsupport f ⊆ W x ∩ O ∧ U f ≠ 0 := by
    obtain ⟨f, hf, hNZ⟩ := (mem_dsupport_iff_forall_exists_ne (x : ℝ)).mp (hE x.property).1
      (W x ∩ O) ⟨(hW x).1, hO x⟩ ((hW x).2.inter hOpen)
    have hCompact : HasCompactSupport (f : ℝ → ℂ) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        (hf.trans (inter_subset_right.trans Ioo_subset_Icc_self))
    exact ⟨f, hCompact, hf, hNZ⟩
  choose f hf using hTest
  have hEventually : ∀ᶠ j in p, ∀ x, T j (f x) ≠ 0 :=
    eventually_all.mpr fun x => (hWeak (f x) (hf x).1).eventually_ne (hf x).2.2
  obtain ⟨j, hj⟩ := hEventually.exists
  let A := (S j).carrier ∩ Ico a (a + L)
  have hFind (x : ↥(E : Set ℝ)) : ∃ y : A, (y : ℝ) ∈ W x := by
    obtain ⟨y, hyT, hyW, hyO⟩ :=
      (nonempty_dsupport_inter_iff_exists_compactTest (S j) (T j) (hT j)
        ((hW x).2.inter hOpen)).mpr ⟨f x, (hf x).1, (hf x).2.1, hj x⟩
    exact ⟨⟨y, dsupport_subset_of_discrete_support _ _ (hT j) hyT,
      hyO.1.le, hyO.2⟩, hyW⟩
  choose y hy using hFind
  have hInj : Function.Injective y := by
    intro x x' he
    by_contra hne
    have hv : (x : ℝ) ≠ (x' : ℝ) := fun hx => hne (Subtype.ext hx)
    exact (Set.disjoint_left.mp (hDis x.property x'.property hv)) (hy x) (he ▸ hy x')
  have hA : A.Finite := ((S j).finite_inter_Icc a (a + L)).subset
    (inter_subset_inter_right _ Ico_subset_Icc_self)
  have hLe := Function.Embedding.encard_le (⟨y, hInj⟩ : (E : Set ℝ) ↪ A)
  rw [encard_coe_eq_coe_finsetCard, ← hA.cast_ncard_eq] at hLe
  exact (by exact_mod_cast hLe : E.card ≤ A.ncard).trans (hCount j a)

/-- The intrinsic support of a weak distributional limit inherits a common
distinct-site bound in every half-open interval of a fixed length. -/
theorem finite_and_ncard_weakLimit_support_window {ι : Type*} {p : Filter ι} [p.NeBot]
    (S : ι → LocallyFiniteCarrier)
    (T : ι → TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
    (hT : ∀ j, DistributionSupportedOn (S j).carrier (T j))
    (hWeak : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Tendsto (fun j => T j f) p (𝓝 (U f)))
    (L : ℝ) {K : ℕ} (hCount : ∀ j r, ((S j).carrier ∩ Ico r (r + L)).ncard ≤ K) (r : ℝ) :
    (dsupport U ∩ Ico r (r + L)).Finite ∧ (dsupport U ∩ Ico r (r + L)).ncard ≤ K := by
  have hSmall (E : Finset ℝ) (hE : (E : Set ℝ) ⊆ dsupport U ∩ Ico r (r + L)) :=
    card_finset_in_weakLimit_support_le_of_window_count S T U hT hWeak L hCount r E hE
  have hFin : (dsupport U ∩ Ico r (r + L)).Finite := by
    by_contra h
    obtain ⟨E, hE, hCard⟩ :=
      (show (dsupport U ∩ Ico r (r + L)).Infinite from h).exists_subset_card_eq (K + 1)
    have h := hSmall E hE
    omega
  refine ⟨hFin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hFin]
  exact hSmall hFin.toFinset fun x hx => hFin.mem_toFinset.mp hx

/-- The intrinsic support of a weak distributional limit inherits a common
distinct-site bound in every half-open unit interval. -/
theorem finite_and_ncard_weakLimit_support_unitWindow {ι : Type*} {p : Filter ι} [p.NeBot]
    (S : ι → LocallyFiniteCarrier)
    (T : ι → TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
    (hT : ∀ j, DistributionSupportedOn (S j).carrier (T j))
    (hWeak : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Tendsto (fun j => T j f) p (𝓝 (U f)))
    {K : ℕ} (hCount : ∀ j r, ((S j).carrier ∩ Ico r (r + 1)).ncard ≤ K) (r : ℝ) :
    (dsupport U ∩ Ico r (r + 1)).Finite ∧ (dsupport U ∩ Ico r (r + 1)).ncard ≤ K := by
  exact finite_and_ncard_weakLimit_support_window S T U hT hWeak 1 hCount r

/-- Weak limits under the common unit count have locally finite intrinsic
support and inherit the same bound. -/
theorem exists_locallyFiniteCarrier_weakLimit_support {ι : Type*} {p : Filter ι} [p.NeBot]
    (S : ι → LocallyFiniteCarrier)
    (T : ι → TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
    (hT : ∀ j, DistributionSupportedOn (S j).carrier (T j))
    (hWeak : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Tendsto (fun j => T j f) p (𝓝 (U f)))
    {K : ℕ} (hCount : ∀ j r, ((S j).carrier ∩ Ico r (r + 1)).ncard ≤ K) :
    ∃ A : LocallyFiniteCarrier, A.carrier = dsupport U ∧
      ∀ r, (A.carrier ∩ Ico r (r + 1)).ncard ≤ K := by
  have hWin := finite_and_ncard_weakLimit_support_unitWindow S T U hT hWeak hCount
  refine ⟨⟨dsupport U, ?_⟩, rfl, fun r => (hWin r).2⟩
  intro a b
  obtain ⟨N, hN⟩ := exists_nat_gt (b - a)
  refine ((Finset.range N).finite_toSet.biUnion
    (t := fun k : ℕ => dsupport U ∩ Ico (a + k) (a + k + 1))
    (fun k _ => (hWin (a + k)).1)).subset ?_
  intro x hx
  let k := Nat.floor (x - a)
  have hNonneg : 0 ≤ x - a := sub_nonneg.mpr hx.2.1
  have hk : k < N := (Nat.floor_lt hNonneg).mpr ((sub_le_sub_right hx.2.2 a).trans_lt hN)
  exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk, hx.1,
    by
      have hl : (k : ℝ) ≤ x - a := Nat.floor_le hNonneg
      linarith only [hl],
    by
      have hr : x - a < (k : ℝ) + 1 := Nat.lt_floor_add_one (x - a)
      linarith only [hr]⟩

end
end MeyerGeneralProblem
