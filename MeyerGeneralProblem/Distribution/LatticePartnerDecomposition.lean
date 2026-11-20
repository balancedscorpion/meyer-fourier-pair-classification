module

public import MeyerGeneralProblem.Distribution.LechFieldEmbedding
public import MeyerGeneralProblem.Distribution.LatticeClassNormalForm

@[expose] public section

/-!
# Directional support of finite comb components

Between distinct rational lattice directions all crossings are finite.
A directional comb may therefore have only finitely many coefficients
outside its own class in the allowed carrier. Its exact cofinite lattice
cover upgrades this to support containment in that class.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators FourierTransform SchwartzMap

/-- The cosets in a finite lattice presentation having one direction. -/
def latticeDirectionClass (E : Finset (ℝ × ℝ)) (D : Submodule ℚ ℝ) :
    Finset (ℝ × ℝ) := by
  classical
  exact E.filter fun v => rationalLineDirection v.2 = D

theorem mem_latticeDirectionClass (E : Finset (ℝ × ℝ)) (D : Submodule ℚ ℝ)
    (v : ℝ × ℝ) : v ∈ latticeDirectionClass E D ↔
      v ∈ E ∧ rationalLineDirection v.2 = D := by
  classical
  exact Finset.mem_filter

private theorem directionLatticeCover_mono {E F : Finset (ℝ × ℝ)} (h : E ⊆ F) :
    (affineLatticeUnionCarrier E).carrier ⊆ (affineLatticeUnionCarrier F).carrier := by
  intro x hx
  obtain ⟨v, hv, hline⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
  exact (mem_affineLatticeUnionCarrier F x).mpr ⟨v, h hv, hline⟩

/-- Each comb component of an exact directional sum is supported on
the cosets of its direction in the allowed carrier. -/
theorem atomicOnCarrier_latticeDirectionClass_of_sum
    {ι : Type*} [Fintype ι] (D : ι → Submodule ℚ ℝ) (hD : Function.Injective D)
    (T : ι → TemperedDistribution ℝ ℂ)
    (G : ι → Finset (ℝ × ℝ)) (hG : ∀ i v, v ∈ G i → rationalLineDirection v.2 = D i)
    (hTG : ∀ i, AtomicOnCarrier (affineLatticeUnionCarrier (G i)) (T i))
    (hcomb : ∀ i, IsFiniteModulatedDiracCombSum (T i))
    (E : Finset (ℝ × ℝ)) (hE : ∀ v ∈ E, 0 < v.2)
    (hT : AtomicOnCarrier (affineLatticeUnionCarrier E) (∑ i, T i)) (i : ι) :
    AtomicOnCarrier (affineLatticeUnionCarrier (latticeDirectionClass E (D i))) (T i) := by
  classical
  let U := affineLatticeUnionCarrier (E ∪ Finset.univ.biUnion G)
  let L := affineLatticeUnionCarrier (latticeDirectionClass E (D i))
  let J := E.filter fun v => rationalLineDirection v.2 ≠ D i
  have hEU : (affineLatticeUnionCarrier E).carrier ⊆ U.carrier :=
    directionLatticeCover_mono Finset.subset_union_left
  have hGU (j : ι) : (affineLatticeUnionCarrier (G j)).carrier ⊆ U.carrier :=
    directionLatticeCover_mono (fun p hp => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩))
  have hcoeffG (j : ι) (x : ℝ) := extendedAtomicCoefficient_on_larger_carrier _ _
    (hGU j) _ (hTG j) x
  have hcoeffE (x : ℝ) := extendedAtomicCoefficient_on_larger_carrier _ _
    hEU _ hT x
  have hSuppG (j : ι) : actualAtomicSupport U (T j) ⊆ (affineLatticeUnionCarrier (G j)).carrier := by
    intro x hx
    apply actualAtomicSupport_subset _ (T j)
    change extendedAtomicCoefficient _ _ x ≠ 0
    rw [← hcoeffG j x]
    exact hx
  have hSuppE : actualAtomicSupport U (∑ j, T j) ⊆ (affineLatticeUnionCarrier E).carrier := by
    intro x hx
    apply actualAtomicSupport_subset _ (∑ j, T j)
    change extendedAtomicCoefficient _ _ x ≠ 0
    rw [← hcoeffE x]
    exact hx
  have hX : ((affineLatticeUnionCarrier (G i)).carrier ∩
      (affineLatticeUnionCarrier J).carrier).Finite := by
    apply finite_latticeUnion_inter_of_different_directions
    intro p hp q hq
    rw [hG i p hp]
    exact Ne.symm (Finset.mem_filter.mp hq).2
  have hY (j : {j : ι // j ≠ i}) : ((affineLatticeUnionCarrier (G i)).carrier ∩
      (affineLatticeUnionCarrier (G j)).carrier).Finite := by
    apply finite_latticeUnion_inter_of_different_directions
    intro p hp q hq
    rw [hG i p hp, hG j q hq]
    exact fun he => j.property (hD he).symm
  have hfin : (actualAtomicSupport U (T i) \ L.carrier).Finite := by
    apply (hX.union (Set.finite_iUnion hY)).subset
    intro x hx
    have hxG := hSuppG i hx.1
    by_cases hxE : x ∈ (affineLatticeUnionCarrier E).carrier
    · obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hxE
      have hpD : rationalLineDirection p.2 ≠ D i := by
        intro he
        apply hx.2
        exact (mem_affineLatticeUnionCarrier _ x).mpr
          ⟨p, (mem_latticeDirectionClass _ _ _).mpr ⟨hp, he⟩, hxp⟩
      exact Or.inl ⟨hxG, (mem_affineLatticeUnionCarrier J x).mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, hpD⟩, hxp⟩⟩
    · right
      by_contra hnot
      have hz (j : ι) (hj : j ≠ i) : extendedAtomicCoefficient U (T j) x = 0 := by
        by_contra hne
        exact hnot (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxG, hSuppG j hne⟩)
      apply hxE
      apply hSuppE
      change extendedAtomicCoefficient U (∑ j, T j) x ≠ 0
      rw [extendedAtomicCoefficient_finset_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
        (fun j _ hj => hz j hj)]
      exact hx.1
  have hscalar := bilateralPowerSumCofiniteSupport_of_oneSidedEventuallyPeriodicZeros
    complexPowerSum_eventuallyPeriodicZeros
  obtain ⟨F, hF, hsub, hFfin⟩ := (hcomb i).hasCofiniteLatticeCover_actualAtomicSupport
    hscalar U (T i) ((hTG i).mono (hGU i))
  have hFL : (affineLatticeUnionCarrier F).carrier ⊆ L.carrier := by
    apply affineLatticeUnion_subset_of_finite_sdiff F (latticeDirectionClass E (D i)) hF
      (fun v hv => hE v ((mem_latticeDirectionClass _ _ _).mp hv).1)
    exact (hFfin.union hfin).subset fun x hx => by
      by_cases h : x ∈ actualAtomicSupport U (T i)
      · exact Or.inr ⟨h, hx.2⟩
      · exact Or.inl ⟨hx.1, h⟩
  exact atomicOnCarrier_of_actualAtomicSupport_subset U L (T i)
    ((hTG i).mono (hGU i)) (hsub.trans hFL)

/-- Inversion preserves and reflects equality of nonzero rational
lattice directions. -/
theorem rationalLineDirection_inv_eq_iff {a b : ℝ} (ha : a ≠ 0) :
    rationalLineDirection a⁻¹ = rationalLineDirection b⁻¹ ↔
      rationalLineDirection a = rationalLineDirection b := by
  have forward {x y : ℝ} (hx : x ≠ 0)
      (h : rationalLineDirection x = rationalLineDirection y) :
      rationalLineDirection x⁻¹ = rationalLineDirection y⁻¹ := by
    have hm : x ∈ rationalLineDirection y := h ▸ Submodule.mem_span_singleton_self x
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
    have he := congrArg Inv.inv (show (r : ℝ) * y = x by simpa only [Rat.smul_def] using hr)
    apply rationalLineDirection_eq_of_mem_ne_zero _ _ (inv_ne_zero hx)
    exact Submodule.mem_span_singleton.mpr ⟨r⁻¹, by
      simpa only [Rat.smul_def, Rat.cast_inv, mul_inv] using he⟩
  exact ⟨fun h => by simpa only [inv_inv] using forward (inv_ne_zero ha) h, forward ha⟩

/-- Physical and reciprocal spectral direction carriers for one partner. -/
abbrev latticePartnerPairSpace (E F : Finset (ℝ × ℝ)) (w : ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  DistributionalMeyerPairSpace
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    (affineLatticeUnionCarrier (latticeDirectionClass F (rationalLineDirection w⁻¹)))

/-- Each ordered partner is a subspace of the full original pair space. -/
theorem latticePartnerPairSpace_le (E F : Finset (ℝ × ℝ)) (w : ℝ) :
    latticePartnerPairSpace E F w ≤
      DistributionalMeyerPairSpace (affineLatticeUnionCarrier E) (affineLatticeUnionCarrier F) := by
  intro T hT
  obtain ⟨hA, hB⟩ := (mem_distributionalMeyerPairSpace_iff _ _ _).mp hT
  exact (mem_distributionalMeyerPairSpace_iff _ _ _).mpr
    ⟨hA.mono (directionLatticeCover_mono (fun _ h => (mem_latticeDirectionClass _ _ _).mp h |>.1)),
      hB.mono (directionLatticeCover_mono (fun _ h => (mem_latticeDirectionClass _ _ _).mp h |>.1))⟩

private theorem atomicOnCarrier_sum_affineCombTerm {ι : Type*} [Fintype ι]
    (q : ι → AffineCombTerm) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    AtomicOnCarrier (affineLatticeUnionCarrier (Finset.univ.image fun i => ((q i).origin, w i)))
      (∑ i, (q i).distribution (w i) (hw i)) := by
  intro f hf
  rw [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (q i).coefficient • modulatedAffineDiracComb (w i) (hw i) (q i).origin (q i).frequency f = 0
  rw [modulatedAffineDiracComb_apply]
  have hz (k : ℤ) : f ((q i).origin + (k : ℝ) * w i) = 0 :=
    hf _ ((mem_affineLatticeUnionCarrier _ _).mpr
      ⟨((q i).origin, w i), Finset.mem_image_of_mem _ (Finset.mem_univ i), k, rfl⟩)
  simp only [hz, mul_zero, tsum_zero, smul_zero]

/-- Every original pair on finite lattice unions is a finite sum of
components in their ordered partner spaces. The components have
distinct physical directions. -/
theorem exists_latticePartnerPairSpace_decomposition
    (E F : Finset (ℝ × ℝ)) (hE : ∀ v ∈ E, 0 < v.2) (hF : ∀ v ∈ F, 0 < v.2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ DistributionalMeyerPairSpace (affineLatticeUnionCarrier E) (affineLatticeUnionCarrier F)) :
    ∃ (κ : Type) (f : Fintype κ), letI := f
      ∃ (s : κ → ℝ) (U : κ → TemperedDistribution ℝ ℂ),
        (∀ i, 0 < s i) ∧ Function.Injective (fun i => rationalLineDirection (s i)) ∧
        T = ∑ i, U i ∧ ∀ i, U i ∈ latticePartnerPairSpace E F (s i) := by
  classical
  let A := affineLatticeUnionCarrier E
  let B := affineLatticeUnionCarrier F
  have hcomb := (finiteModulatedDiracCombSum_pair_of_two_unitCellBounds A B _ _
    (unitCellBound_affineLatticeUnionCarrier E hE) (unitCellBound_affineLatticeUnionCarrier F hF)
    T hT).1
  obtain ⟨ι, fi, q, w, hw, hsum⟩ := hcomb
  let _ := fi
  let dirs := Finset.univ.image fun i => rationalLineDirection (w i)
  have hrep (c : dirs) : ∃ i : ι, rationalLineDirection (w i) = c.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp c.property
    exact ⟨i, hi⟩
  choose rep hrep using hrep
  let s (c : dirs) := w (rep c)
  have hs (c : dirs) : 0 < s c := hw (rep c)
  have hd : Function.Injective (fun c => rationalLineDirection (s c)) := by
    intro c d he
    exact Subtype.ext ((hrep c).symm.trans (he.trans (hrep d)))
  have hd' : Function.Injective (fun c => rationalLineDirection (s c)⁻¹) := by
    intro c d he
    exact hd ((rationalLineDirection_inv_eq_iff (hs c).ne').mp he)
  let cls (i : ι) : dirs :=
    ⟨rationalLineDirection (w i), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let I (c : dirs) := {i : ι // cls i = c}
  let U (c : dirs) := ∑ i : I c, (q i.val).distribution (w i.val) (hw i.val)
  let G (c : dirs) := Finset.univ.image fun i : I c => ((q i.val).origin, w i.val)
  let H (c : dirs) := Finset.univ.image fun i : I c =>
    (((q i.val).fourierTerm (w i.val)).origin, (w i.val)⁻¹)
  have hDirection (c : dirs) (i : I c) :
      rationalLineDirection (w i.val) = rationalLineDirection (s c) :=
    (congrArg Subtype.val i.property).trans (hrep c).symm
  have hG (c : dirs) (a : ℝ × ℝ) (ha : a ∈ G c) :
      rationalLineDirection a.2 = rationalLineDirection (s c) := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hDirection c i
  have hH (c : dirs) (a : ℝ × ℝ) (ha : a ∈ H c) :
      rationalLineDirection a.2 = rationalLineDirection (s c)⁻¹ := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (rationalLineDirection_inv_eq_iff (hw i.val).ne').mpr (hDirection c i)
  have hReconstruct : T = ∑ c, U c := by
    rw [hsum, ← Finset.sum_fiberwise Finset.univ cls (fun i => (q i).distribution (w i) (hw i))]
    apply Finset.sum_congr rfl
    intro c _
    exact Finset.sum_subtype (p := fun i => cls i = c) _ (by simp)
      (fun i => (q i).distribution (w i) (hw i))
  have hU (c : dirs) : IsFiniteModulatedDiracCombSum (U c) :=
    ⟨I c, inferInstance, fun i => q i.val, fun i => w i.val, fun i => hw i.val, rfl⟩
  have hAtom (c : dirs) : AtomicOnCarrier (affineLatticeUnionCarrier (G c)) (U c) :=
    atomicOnCarrier_sum_affineCombTerm (fun i : I c => q i.val) (fun i => w i.val) (fun i => hw i.val)
  have hAtomF (c : dirs) : AtomicOnCarrier (affineLatticeUnionCarrier (H c)) (𝓕 (U c)) := by
    change AtomicOnCarrier (affineLatticeUnionCarrier (H c))
      (temperedFourierLinearMap (∑ i : I c, (q i.val).distribution (w i.val) (hw i.val)))
    rw [map_sum]
    simp only [temperedFourierLinearMap_apply, fourier_affineCombTerm]
    exact atomicOnCarrier_sum_affineCombTerm (fun i : I c => (q i.val).fourierTerm (w i.val))
      (fun i => (w i.val)⁻¹) (fun i => inv_pos.mpr (hw i.val))
  have hp := (mem_distributionalMeyerPairSpace_iff A B T).mp hT
  have hPf : AtomicOnCarrier B (∑ c, 𝓕 (U c)) := by
    rw [hReconstruct, ← temperedFourierLinearMap_apply, map_sum] at hp
    exact hp.2
  refine ⟨dirs, inferInstance, s, U, hs, hd, hReconstruct, fun c => ?_⟩
  exact (mem_distributionalMeyerPairSpace_iff _ _ _).mpr
    ⟨atomicOnCarrier_latticeDirectionClass_of_sum _ hd U G hG hAtom hU E hE
        (hReconstruct ▸ hp.1) c,
      atomicOnCarrier_latticeDirectionClass_of_sum _ hd' (fun c => 𝓕 (U c))
        H hH hAtomF (fun c => (hU c).fourier) F hF hPf c⟩

/-- Addition identifies the finite product of the ordered partner
spaces with the whole original pair space on the two lattice unions.
An absent spectral partner contributes the zero space. -/
theorem exists_latticePartnerPairSpace_equiv
    {ι : Type*} [Fintype ι]
    (E F : Finset (ℝ × ℝ)) (hE : ∀ v ∈ E, 0 < v.2) (hF : ∀ v ∈ F, 0 < v.2)
    (step : ι → ℝ)
    (hD : Function.Injective (fun i => rationalLineDirection (step i)))
    (hcover : ∀ v ∈ E, ∃ i, rationalLineDirection v.2 = rationalLineDirection (step i)) :
    ∃ e : ((i : ι) → latticePartnerPairSpace E F (step i)) ≃ₗ[ℂ]
        DistributionalMeyerPairSpace (affineLatticeUnionCarrier E) (affineLatticeUnionCarrier F),
      ∀ u, (e u : TemperedDistribution ℝ ℂ) = ∑ i, (u i : TemperedDistribution ℝ ℂ) := by
  classical
  let V := DistributionalMeyerPairSpace (affineLatticeUnionCarrier E) (affineLatticeUnionCarrier F)
  let W (i : ι) := latticePartnerPairSpace E F (step i)
  let l : ((i : ι) → W i) →ₗ[ℂ] V :=
    { toFun u := ⟨∑ i, (u i : TemperedDistribution ℝ ℂ),
        V.sum_mem (fun i _ => latticePartnerPairSpace_le E F (step i) (u i).property)⟩
      map_add' u v := by
        apply Subtype.ext
        change (∑ i, ((u i + v i : W i) : TemperedDistribution ℝ ℂ)) =
          (∑ i, (u i : TemperedDistribution ℝ ℂ)) + ∑ i, (v i : TemperedDistribution ℝ ℂ)
        simp only [Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' a u := by
        apply Subtype.ext
        change (∑ i, ((a • u i : W i) : TemperedDistribution ℝ ℂ)) =
          a • ∑ i, (u i : TemperedDistribution ℝ ℂ)
        simp only [Submodule.coe_smul, Finset.smul_sum] }
  have hInjective : Function.Injective l := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro u hu
    let U (i : ι) := (u i : TemperedDistribution ℝ ℂ)
    let G (i : ι) := latticeDirectionClass E (rationalLineDirection (step i))
    let H (i : ι) := latticeDirectionClass F (rationalLineDirection (step i)⁻¹)
    have hG (i : ι) (p : ℝ × ℝ) (hp : p ∈ G i) :
        rationalLineDirection p.2 = rationalLineDirection (step i) :=
      ((mem_latticeDirectionClass _ _ _).mp hp).2
    have hPositiveG (i : ι) (p : ℝ × ℝ) (hp : p ∈ G i) : 0 < p.2 :=
      hE p ((mem_latticeDirectionClass _ _ _).mp hp).1
    have hPositiveH (i : ι) (p : ℝ × ℝ) (hp : p ∈ H i) : 0 < p.2 :=
      hF p ((mem_latticeDirectionClass _ _ _).mp hp).1
    have hPair (i : ι) :
        U i ∈ DistributionalMeyerPairSpace (affineLatticeUnionCarrier (G i))
          (affineLatticeUnionCarrier (H i)) := (u i).property
    have hAtom (i : ι) : AtomicOnCarrier (affineLatticeUnionCarrier (G i)) (U i) :=
      ((mem_distributionalMeyerPairSpace_iff _ _ _).mp (hPair i)).1
    have hComb (i : ι) : IsFiniteModulatedDiracCombSum (U i) :=
      (finiteModulatedDiracCombSum_pair_of_two_unitCellBounds _ _ _ _
        (unitCellBound_affineLatticeUnionCarrier (G i) (hPositiveG i))
        (unitCellBound_affineLatticeUnionCarrier (H i) (hPositiveH i)) (U i) (hPair i)).1
    have hz : (∑ i, U i) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hu)
    have hEmpty : AtomicOnCarrier (affineLatticeUnionCarrier ∅) (∑ i, U i) := by
      rw [hz]
      intro f _
      simp
    funext i
    apply Subtype.ext
    change U i = 0
    have hAt := atomicOnCarrier_latticeDirectionClass_of_sum _ hD U G hG hAtom hComb ∅ (by simp)
      hEmpty i
    apply atomicOnCarrier_eq_zero_of_empty _ hAt
    ext x
    simp [mem_affineLatticeUnionCarrier, latticeDirectionClass]
  have hSingle (i : ι) (v : W i) : (l (Pi.single i v) : TemperedDistribution ℝ ℂ) = v := by
    change (∑ j, ((Pi.single i v : (i : ι) → W i) j : TemperedDistribution ℝ ℂ)) = v
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => by
      rw [Pi.single_eq_of_ne hj]
      rfl)]
    rw [Pi.single_eq_same]
  have hSurjective : Function.Surjective l := by
    intro T
    obtain ⟨κ, f, s, U, hs, _, hsum, hU⟩ :=
      exists_latticePartnerPairSpace_decomposition E F hE hF T T.property
    let _ := f
    let v (j : κ) : V := ⟨U j, latticePartnerPairSpace_le E F (s j) (hU j)⟩
    have hLift (j : κ) : ∃ u, l u = v j := by
      by_cases h : ∃ i, rationalLineDirection (s j) = rationalLineDirection (step i)
      · obtain ⟨i, hi⟩ := h
        have hj := (rationalLineDirection_inv_eq_iff (hs j).ne').mpr hi
        have hu : U j ∈ W i := by
          change U j ∈ latticePartnerPairSpace E F (step i)
          simpa only [latticePartnerPairSpace, hi, hj] using hU j
        exact ⟨Pi.single i ⟨U j, hu⟩, Subtype.ext (hSingle i ⟨U j, hu⟩)⟩
      · have hpart : latticeDirectionClass E (rationalLineDirection (s j)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          obtain ⟨hp, he⟩ := (mem_latticeDirectionClass _ _ _).mp hp
          obtain ⟨i, hi⟩ := hcover p hp
          exact h ⟨i, he.symm.trans hi⟩
        have hU0 : U j = 0 := by
          have hAt := ((mem_distributionalMeyerPairSpace_iff _ _ _).mp (hU j)).1
          rw [hpart] at hAt
          apply atomicOnCarrier_eq_zero_of_empty _ hAt
          ext x
          simp [mem_affineLatticeUnionCarrier]
        exact ⟨0, by rw [map_zero]; exact Subtype.ext hU0.symm⟩
    choose u hLift using hLift
    refine ⟨∑ j, u j, ?_⟩
    rw [map_sum]
    simp only [hLift]
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using hsum.symm
  exact ⟨LinearEquiv.ofBijective l ⟨hInjective, hSurjective⟩, fun _ => rfl⟩

/-- A missing reciprocal direction gives no contribution. -/
theorem latticePartnerPairSpace_eq_bot_of_empty_spectral_class
    (E F : Finset (ℝ × ℝ)) (w : ℝ)
    (hF : latticeDirectionClass F (rationalLineDirection w⁻¹) = ∅) :
    latticePartnerPairSpace E F w = ⊥ := by
  apply bot_unique
  intro T hT
  rw [Submodule.mem_bot]
  have hFourier := ((mem_distributionalMeyerPairSpace_iff _ _ _).mp hT).2
  rw [hF] at hFourier
  have hEmpty : (affineLatticeUnionCarrier ∅).carrier = ∅ := by
    ext x
    simp [mem_affineLatticeUnionCarrier]
  have hz := atomicOnCarrier_eq_zero_of_empty hEmpty hFourier
  have hRef : originalDistributionReflection T = 0 := by
    rw [← fourier_fourier_eq_originalDistributionReflection, hz,
      ← temperedFourierLinearMap_apply, map_zero]
  calc
    T = originalDistributionReflection (originalDistributionReflection T) :=
      (originalDistributionReflection_involutive T).symm
    _ = 0 := by rw [hRef, map_zero]

/-- The whole envelope has ordered partner coordinates. Both original
hole evaluations add the coordinate contributions, and the rank in
these coordinates gives the exact embedded nullity. -/
theorem FiniteHoleEnvelope.exists_latticePartnerHoleCoordinates
    {S : LocallyFiniteCarrier} (E : FiniteHoleEnvelope S) :
    let dirs := E.val.image fun v => rationalLineDirection v.2
    ∃ step : dirs → ℝ, (∀ i, 0 < step i ∧ rationalLineDirection (step i) = i.val) ∧
      ∃ e : ((i : dirs) → latticePartnerPairSpace E.val E.val (step i)) ≃ₗ[ℂ]
          DistributionalMeyerPairSpace E.carrier E.carrier,
        (∀ u, (e u : TemperedDistribution ℝ ℂ) = ∑ i, (u i : TemperedDistribution ℝ ℂ)) ∧
        (∀ u h, commonCarrierHoleRows E.carrier S (e u) h =
          (∑ i, (u i : TemperedDistribution ℝ ℂ) (E.carrier.isolationSchwartz h.val),
           ∑ i, (𝓕 (u i : TemperedDistribution ℝ ℂ)) (E.carrier.isolationSchwartz h.val))) ∧
        E.nullity = (∑ i, Module.finrank ℂ (latticePartnerPairSpace E.val E.val (step i))) -
          Module.finrank ℂ (LinearMap.range ((commonCarrierHoleRows E.carrier S).comp e.toLinearMap)) := by
  classical
  let dirs := E.val.image fun v => rationalLineDirection v.2
  obtain ⟨step, _, hDir, _, _⟩ := exists_exact_lattice_direction_refinements E.val E.property.1
  have hSteps (i : dirs) : 0 < step i ∧ rationalLineDirection (step i) = i.val :=
    ⟨(hDir i).1, (hDir i).2.1⟩
  have hinj : Function.Injective (fun i => rationalLineDirection (step i)) := by
    intro i j hij
    exact Subtype.ext ((hSteps i).2.symm.trans (hij.trans (hSteps j).2))
  have hc (v : ℝ × ℝ) (hv : v ∈ E.val) :
      ∃ i, rationalLineDirection v.2 = rationalLineDirection (step i) :=
    ⟨⟨_, Finset.mem_image_of_mem _ hv⟩, (hSteps ⟨_, Finset.mem_image_of_mem _ hv⟩).2.symm⟩
  obtain ⟨e, he⟩ := exists_latticePartnerPairSpace_equiv E.val E.val E.property.1 E.property.1
    step hinj hc
  refine ⟨step, hSteps, e, he, ?_, ?_⟩
  · intro u h
    change ((e u : TemperedDistribution ℝ ℂ) (E.carrier.isolationSchwartz h.val),
      (𝓕 (e u : TemperedDistribution ℝ ℂ)) (E.carrier.isolationSchwartz h.val)) = _
    rw [he, ← temperedFourierLinearMap_apply, map_sum]
    simp only [_root_.sum_apply, temperedFourierLinearMap_apply]
  · let : FiniteDimensional ℂ (DistributionalMeyerPairSpace
        (affineLatticeUnionCarrier E.val) (affineLatticeUnionCarrier E.val)) :=
      finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound
        E.carrier E.carrier _ (unitCellBound_affineLatticeUnionCarrier E.val E.property.1)
    have (i : dirs) : FiniteDimensional ℂ (latticePartnerPairSpace E.val E.val (step i)) :=
      FiniteDimensional.of_injective (Submodule.inclusion
        (latticePartnerPairSpace_le E.val E.val (step i))) (Submodule.inclusion_injective _)
    have hRank := congrArg
      (fun R : Submodule ℂ (CommonCarrierHole E.carrier S → ℂ × ℂ) => Module.finrank ℂ R)
      (e.range_comp (commonCarrierHoleRows E.carrier S))
    have hDim := e.finrank_eq
    rw [Module.finrank_pi_fintype] at hDim
    exact congrArg₂ Nat.sub hDim.symm hRank.symm

end
end MeyerGeneralProblem
