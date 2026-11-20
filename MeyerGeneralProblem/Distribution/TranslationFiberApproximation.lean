module

public import MeyerGeneralProblem.Distribution.TranslationFiberSupport

@[expose] public section

/-!
# Recovering whole bilateral solutions on finite families of fibers

A separate solution at each end of a line need not have a common
bilateral extension. We descend a stronger property through the
transverse product: agreement with a whole parallel-kernel solution
outside finitely many sites on a quotient fiber.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- Agreement with a submodule element up to finitely many sites on
one specified quotient fiber. -/
def approximatedOnTranslationFiber {G Q : Type*} (π : G → Q)
    (V : Submodule ℂ (G → ℂ)) (f : G → ℂ) (z : Q) : Prop :=
  ∃ u ∈ V, (Function.support (f - u) ∩ π ⁻¹' {z}).Finite

private theorem approximatedOnTranslationFiber_of_step
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (V : Submodule ℂ (G → ℂ))
    (hshift : ∀ a u, u ∈ V → (fun x => u (x - a)) ∈ V)
    (a : G) (ω : ℂ) (hω : ω ≠ 0) (f : G → ℂ) (z : Q)
    (hnext : approximatedOnTranslationFiber π V f (z - π a))
    (hD : approximatedOnTranslationFiber π V (translationDifference a ω f) z) :
    approximatedOnTranslationFiber π V f z := by
  obtain ⟨v,hV,hv⟩ := hnext
  obtain ⟨u,hU,hu⟩ := hD
  let g : G → ℂ := ω⁻¹ • ((fun x => v (x - a)) - u)
  refine ⟨g, V.smul_mem _ (V.sub_mem (hshift a v hV) hU), ?_⟩
  refine ((hv.image (fun x => x + a)).union hu).subset ?_
  rintro x ⟨hx,hz⟩
  change π x = z at hz
  by_cases hvx : f (x - a) = v (x - a)
  · by_cases hux : translationDifference a ω f x = u x
    · exfalso
      apply hx
      change f x - ω⁻¹ * (v (x - a) - u x) = 0
      rw [← hvx, ← hux, translationDifference, sub_sub_cancel, ← mul_assoc,
        inv_mul_cancel₀ hω, one_mul, sub_self]
    · exact Or.inr ⟨sub_ne_zero.mpr hux,hz⟩
  · refine Or.inl ⟨x - a,⟨sub_ne_zero.mpr hvx, ?_⟩,sub_add_cancel _ _⟩
    change π (x - a) = z - π a
    rw [map_sub, hz]

private theorem all_fibers_approximated_of_transverse_factor
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (V : Submodule ℂ (G → ℂ))
    (hshift : ∀ a u, u ∈ V → (fun x => u (x - a)) ∈ V)
    (a : G) (ω : ℂ) (hω : ω ≠ 0) (hinj : Function.Injective (fun n : ℕ => n • π a))
    (f : G → ℂ) (hf : (π '' Function.support f).Finite)
    (hD : ∀ z, approximatedOnTranslationFiber π V (translationDifference a ω f) z) :
    ∀ z, approximatedOnTranslationFiber π V f z := by
  intro z
  by_contra hbad
  let orbit (n : ℕ) := z - n • π a
  have hbadOrbit (n : ℕ) : ¬ approximatedOnTranslationFiber π V f (orbit n) := by
    induction n with
    | zero => simpa [orbit] using hbad
    | succ n ih =>
        intro hp
        apply ih
        apply approximatedOnTranslationFiber_of_step π V hshift a ω hω f (orbit n) _ (hD _)
        simpa only [orbit, succ_nsmul, sub_sub] using hp
  have hsub : Set.range orbit ⊆ π '' Function.support f := by
    rintro _ ⟨n,rfl⟩
    by_contra h
    apply hbadOrbit n
    refine ⟨0,V.zero_mem,?_⟩
    rw [sub_zero]
    refine Set.finite_empty.subset ?_
    rintro x ⟨hx,hxπ⟩
    exact (h ⟨x,hx,hxπ⟩).elim
  have hOrbitInj : Function.Injective orbit := by
    intro m n he
    apply hinj
    have h := congrArg (fun y => z - y) he
    simpa only [orbit, sub_sub_cancel] using h
  exact (Set.infinite_range_of_injective hOrbitInj).not_finite (hf.subset hsub)

theorem all_fibers_approximated_of_transverse_product
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (V : Submodule ℂ (G → ℂ))
    (hshift : ∀ a u, u ∈ V → (fun x => u (x - a)) ∈ V)
    (factors : List (G × ℂ))
    (hFactors : ∀ p ∈ factors, p.2 ≠ 0 ∧ Function.Injective (fun n : ℕ => n • π p.1))
    (f : G → ℂ) (hf : (π '' Function.support f).Finite)
    (hD : ∀ z, approximatedOnTranslationFiber π V (translationDifferenceProduct factors f) z) :
    ∀ z, approximatedOnTranslationFiber π V f z := by
  induction factors generalizing f with
  | nil => exact hD
  | cons p factors ih =>
      have hp := hFactors p List.mem_cons_self
      obtain ⟨a,ω⟩ := p
      exact all_fibers_approximated_of_transverse_factor π V hshift a ω hp.1 hp.2 f hf
        (ih (fun q hq => hFactors q (List.mem_cons_of_mem _ hq)) _
          (finite_image_support_translationDifferenceProduct π [(a,ω)] f hf) hD)

/-- The linear map belonging to an individual bilateral factor. -/
def translationDifferenceLinearMap {G : Type*} [AddCommGroup G] (a : G) (ω : ℂ) :
    Module.End ℂ (G → ℂ) where
  toFun := translationDifference a ω
  map_add' f g := by
    funext x
    simp only [translationDifference, Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [translationDifference, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The linear interpretation of the same literal factor list. -/
def translationDifferenceProductLinearMap {G : Type*} [AddCommGroup G] :
    List (G × ℂ) → Module.End ℂ (G → ℂ)
  | [] => LinearMap.id
  | (a,ω) :: factors =>
      (translationDifferenceProductLinearMap factors).comp (translationDifferenceLinearMap a ω)

@[simp]
theorem translationDifferenceProductLinearMap_apply {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) (f : G → ℂ) :
    translationDifferenceProductLinearMap factors f = translationDifferenceProduct factors f := by
  induction factors generalizing f with
  | nil => rfl
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      exact ih (translationDifference a ω f)

theorem translationDifferenceProduct_translate {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) (a : G) (f : G → ℂ) :
    translationDifferenceProduct factors (fun x => f (x - a)) =
      fun x => translationDifferenceProduct factors f (x - a) := by
  induction factors generalizing f with
  | nil => rfl
  | cons p factors ih =>
      obtain ⟨b,ξ⟩ := p
      have h : translationDifference b ξ (fun x => f (x - a)) =
          fun x => translationDifference b ξ f (x - a) := by
        funext x
        simp only [translationDifference]
        have hshift : x - b - a = x - a - b := by abel
        rw [hshift]
      change translationDifferenceProduct factors
        (translationDifference b ξ (fun x => f (x - a))) =
          fun x => translationDifferenceProduct factors (translationDifference b ξ f) (x - a)
      rw [h]
      exact ih _

/-- Restriction to an invariant set preserves the exact parallel
equation, including zero coefficients off that set. -/
theorem translationDifferenceProduct_indicator {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) (A : Set G)
    (hA : ∀ p ∈ factors, ∀ x, x - p.1 ∈ A ↔ x ∈ A) (f : G → ℂ) :
    translationDifferenceProduct factors (A.indicator f) =
      A.indicator (translationDifferenceProduct factors f) := by
  classical
  induction factors generalizing f with
  | nil => rfl
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      have h : translationDifference a ω (A.indicator f) =
          A.indicator (translationDifference a ω f) := by
        funext x
        by_cases hx : x ∈ A
        · have hax := (hA (a,ω) List.mem_cons_self x).mpr hx
          simp only [translationDifference, Set.indicator_of_mem hx, Set.indicator_of_mem hax]
        · have hax := fun h => hx ((hA (a,ω) List.mem_cons_self x).mp h)
          simp only [translationDifference, Set.indicator_of_notMem hx, Set.indicator_of_notMem hax,
            mul_zero, sub_self]
      change translationDifferenceProduct factors (translationDifference a ω (A.indicator f)) =
        A.indicator (translationDifferenceProduct factors (translationDifference a ω f))
      rw [h]
      exact ih (fun q hq => hA q (List.mem_cons_of_mem _ hq)) _

private theorem exists_parallel_kernel_approximation_of_fibers
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (parallel : List (G × ℂ)) (hπ : ∀ p ∈ parallel, π p.1 = 0)
    (g : G → ℂ) (hg : (π '' Function.support g).Finite)
    (happrox : ∀ z, approximatedOnTranslationFiber π
      (translationDifferenceProductLinearMap parallel).ker g z) :
    ∃ u : G → ℂ, translationDifferenceProduct parallel u = 0 ∧
      (Function.support (g - u)).Finite := by
  classical
  choose v hV hFin using happrox
  let F := hg.toFinset
  let term (z : Q) := (π ⁻¹' {z}).indicator (v z)
  let u := ∑ z ∈ F, term z
  have hvzero (z : Q) : translationDifferenceProduct parallel (v z) = 0 := by
    simpa only [LinearMap.mem_ker, translationDifferenceProductLinearMap_apply] using hV z
  have hterm (z : Q) : translationDifferenceProduct parallel (term z) = 0 := by
    change translationDifferenceProduct parallel ((π ⁻¹' {z}).indicator (v z)) = 0
    have hInv (p : G × ℂ) (hp : p ∈ parallel) (x : G) :
        x - p.1 ∈ π ⁻¹' {z} ↔ x ∈ π ⁻¹' {z} := by
      change π (x - p.1) = z ↔ π x = z
      rw [map_sub, hπ p hp, sub_zero]
    rw [translationDifferenceProduct_indicator _ _ hInv, hvzero z]
    funext x
    by_cases hx : π x = z
    · exact Set.indicator_of_mem (show x ∈ π ⁻¹' {z} from hx) (0 : G → ℂ)
    · exact Set.indicator_of_notMem (show x ∉ π ⁻¹' {z} from hx) (0 : G → ℂ)
  refine ⟨u, ?_, ?_⟩
  · rw [← translationDifferenceProductLinearMap_apply]
    change translationDifferenceProductLinearMap parallel (∑ z ∈ F, term z) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro z _
    simpa only [translationDifferenceProductLinearMap_apply] using hterm z
  · have hU := F.finite_toSet.biUnion (fun z _ => hFin z)
    apply hU.subset
    intro x hx
    change g x - u x ≠ 0 at hx
    have hEval : u x = ∑ z ∈ F, term z x := by simp only [u, Finset.sum_apply]
    by_cases hxF : π x ∈ F
    · have hux : u x = v (π x) x := by
        rw [hEval, Finset.sum_eq_single_of_mem (π x) hxF]
        · exact Set.indicator_of_mem (show x ∈ π ⁻¹' {π x} from rfl) _
        · intro z _ hn
          exact Set.indicator_of_notMem (show x ∉ π ⁻¹' {z} from fun he => hn he.symm) _
      rw [hux] at hx
      exact Set.mem_iUnion.mpr ⟨π x, Set.mem_iUnion.mpr ⟨hxF,hx,rfl⟩⟩
    · have hu0 : u x = 0 := by
        rw [hEval]
        apply Finset.sum_eq_zero
        intro z hz
        exact Set.indicator_of_notMem (show x ∉ π ⁻¹' {z} from fun he => hxF (he.symm ▸ hz)) _
      have hg0 : g x = 0 := by
        by_contra hn
        exact hxF (hg.mem_toFinset.mpr ⟨x,hn,rfl⟩)
      exact (hx (by rw [hu0,hg0,sub_zero])).elim

/-- A finitely supported crossing error does permit one whole bilateral
parallel solution on each fiber when the full original recurrence holds.
The patched function agrees with the selected component off a finite set. -/
theorem exists_parallel_kernel_approximation_of_original_product
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (parallel transverse : List (G × ℂ)) (hπ : ∀ p ∈ parallel, π p.1 = 0)
    (htrans : ∀ p ∈ transverse, p.2 ≠ 0 ∧ Function.Injective (fun n : ℕ => n • π p.1))
    (f g : G → ℂ) (hg : (π '' Function.support g).Finite)
    (hc : ∀ z, (Function.support (f - g) ∩ π ⁻¹' {z}).Finite)
    (hz : translationDifferenceProduct (parallel ++ transverse) f = 0) :
    ∃ u : G → ℂ, translationDifferenceProduct parallel u = 0 ∧
      (Function.support (g - u)).Finite := by
  let V := (translationDifferenceProductLinearMap parallel).ker
  have hzQ : translationDifferenceProduct parallel (translationDifferenceProduct transverse f) = 0 := by
    rw [← translationDifferenceProduct_append]
    exact (translationDifferenceProduct_eq_of_perm List.perm_append_comm f).trans hz
  have hshift (a : G) (u : G → ℂ) (hu : u ∈ V) : (fun x => u (x - a)) ∈ V := by
    have he : translationDifferenceProduct parallel u = 0 := by
      simpa only [V, LinearMap.mem_ker, translationDifferenceProductLinearMap_apply] using hu
    change translationDifferenceProductLinearMap parallel (fun x => u (x - a)) = 0
    rw [translationDifferenceProductLinearMap_apply, translationDifferenceProduct_translate, he]
    rfl
  have hGood (z : Q) :
      approximatedOnTranslationFiber π V (translationDifferenceProduct transverse g) z := by
    refine ⟨translationDifferenceProduct transverse f, ?_, ?_⟩
    · simpa only [V, LinearMap.mem_ker, translationDifferenceProductLinearMap_apply] using hzQ
    · apply (finite_support_inter_fiber_translationDifferenceProduct π transverse (f - g) hc z).subset
      rintro x ⟨hx,hxπ⟩
      refine ⟨?_,hxπ⟩
      change translationDifferenceProduct transverse g x -
        translationDifferenceProduct transverse f x ≠ 0 at hx
      rw [translationDifferenceProduct_sub]
      exact sub_ne_zero.mpr (sub_ne_zero.mp hx).symm
  exact exists_parallel_kernel_approximation_of_fibers π parallel hπ g hg
    (all_fibers_approximated_of_transverse_product π V hshift transverse htrans g hg hGood)

/-- The whole bilateral approximation may be carried by any invariant
set containing the function being approximated. -/
theorem exists_supported_translationKernel_approximation
    {G : Type*} [AddCommGroup G] (factors : List (G × ℂ)) (A : Set G)
    (hA : ∀ p ∈ factors, ∀ x, x - p.1 ∈ A ↔ x ∈ A) (f u : G → ℂ)
    (hf : Function.support f ⊆ A)
    (hu : translationDifferenceProduct factors u = 0)
    (hfinite : (Function.support (f - u)).Finite) :
    ∃ v : G → ℂ, Function.support v ⊆ A ∧ translationDifferenceProduct factors v = 0 ∧
      (Function.support (f - v)).Finite := by
  classical
  refine ⟨A.indicator u, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hn
    exact hx (Set.indicator_of_notMem hn u)
  · rw [translationDifferenceProduct_indicator factors A hA, hu]
    funext x
    by_cases hx : x ∈ A
    · exact Set.indicator_of_mem hx (0 : G → ℂ)
    · exact Set.indicator_of_notMem hx (0 : G → ℂ)
  · apply hfinite.subset
    intro x hx
    have hxA : x ∈ A := by
      by_contra hn
      have hfx : f x = 0 := by
        by_contra he
        exact hn (hf he)
      exact hx (by simp only [Pi.sub_apply, Set.indicator_of_notMem hn, hfx, sub_zero])
    change f x - u x ≠ 0
    simpa only [Function.mem_support, Pi.sub_apply, Set.indicator_of_mem hxA] using hx

end
end MeyerGeneralProblem
