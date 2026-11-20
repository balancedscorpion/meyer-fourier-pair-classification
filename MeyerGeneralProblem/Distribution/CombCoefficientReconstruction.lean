module

public import MeyerGeneralProblem.Distribution.BilateralCharacterModes
public import MeyerGeneralProblem.Distribution.QuadrantResidueCharacters

@[expose] public section

/-!
# Reconstruction from exact bilateral coefficients

The character-mode solution on each full coset is realized by its
actual modulated Dirac comb. Equal cosets are counted just once.
Isolation on any larger carrier recovers the same whole coefficient
function, including its zero extension.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators SchwartzMap

/-- The literal mass function of an affine modulated comb. -/
def AffineCombTerm.coefficientFunction (q : AffineCombTerm) (w : ℝ) : ℝ → ℂ :=
  (affineLatticeLine q.origin w).indicator
    (fun x => q.coefficient * combModulationCharacter q.frequency x)

theorem affineDiracCombCarrier_eq_affineLatticeLine (w : ℝ) (hw : 0 < w) (y : ℝ) :
    (affineDiracCombCarrier w hw y).carrier = affineLatticeLine y w := by
  ext x
  rw [mem_affineDiracCombCarrier]
  change (∃ k : ℤ, x = y + (k : ℝ) * w) ↔ ∃ k : ℤ, y + (k : ℝ) * w = x
  simp only [eq_comm]

/-- Exact all-point coefficient recovery for one original comb term. -/
theorem extendedAtomicCoefficient_affineCombTerm
    (q : AffineCombTerm) (w : ℝ) (hw : 0 < w) (A : LocallyFiniteCarrier)
    (hsub : affineLatticeLine q.origin w ⊆ A.carrier) (x : ℝ) :
    extendedAtomicCoefficient A (q.distribution w hw) x = q.coefficientFunction w x := by
  classical
  by_cases hx : x ∈ A.carrier
  · let x₀ : A.subtype := ⟨x,hx⟩
    let site (n : ℤ) := q.origin + (n : ℝ) * w
    let phase (n : ℤ) := combModulationCharacter q.frequency (site n)
    have hsite (n : ℤ) : site n ∈ A.carrier := hsub ⟨n,rfl⟩
    have hinj : Function.Injective site := by
      intro m n he
      exact_mod_cast mul_right_cancel₀ hw.ne' (add_left_cancel he)
    rw [extendedAtomicCoefficient, dite_eq_left hx]
    change q.distribution w hw (A.isolationSchwartz x₀) = _
    rw [AffineCombTerm.distribution, smul_apply, smul_eq_mul, modulatedAffineDiracComb_apply]
    change q.coefficient * (∑' n, phase n * A.isolationSchwartz x₀ (site n)) = _
    by_cases hm : x ∈ affineLatticeLine q.origin w
    · obtain ⟨k,hk⟩ := hm
      rw [tsum_isolationSchwartz_indexed_eq_of_injective A x₀ site hsite hinj phase k hk]
      change q.coefficient * combModulationCharacter q.frequency (site k) =
        (affineLatticeLine q.origin w).indicator _ x
      have hm : x ∈ affineLatticeLine q.origin w := ⟨k,hk⟩
      rw [Set.indicator_of_mem hm, show site k = x from hk]
    · rw [tsum_isolationSchwartz_indexed_eq_zero_off_image A x₀ site hsite phase
        (fun j h => hm ⟨j,h⟩)]
      simp only [mul_zero, AffineCombTerm.coefficientFunction, Set.indicator_of_notMem hm]
  · have hm : x ∉ affineLatticeLine q.origin w := fun h => hx (hsub h)
    simp only [extendedAtomicCoefficient, dite_eq_right hx, AffineCombTerm.coefficientFunction,
      Set.indicator_of_notMem hm]

/-- Recenter an affine lattice at any point it contains. -/
theorem affineLatticeLine_eq_of_mem (x y w : ℝ) (h : x ∈ affineLatticeLine y w) :
    affineLatticeLine x w = affineLatticeLine y w := by
  obtain ⟨n,rfl⟩ := h
  ext a
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨n + k,by push_cast; ring⟩
  · rintro ⟨k,rfl⟩
    exact ⟨k - n,by push_cast; ring⟩

private theorem affineCombTermSumCarrier_subset_of_each
    (w : ℝ) (hw : 0 < w) (terms : List AffineCombTerm) (A : LocallyFiniteCarrier)
    (h : ∀ q ∈ terms, affineLatticeLine q.origin w ⊆ A.carrier) :
    (affineCombTermSumCarrier w hw terms).carrier ⊆ A.carrier := by
  induction terms with
  | nil => exact Set.empty_subset _
  | cons q qs ih =>
      intro x hx
      rcases hx with hx | hx
      · rw [affineDiracCombCarrier_eq_affineLatticeLine] at hx
        exact h q List.mem_cons_self hx
      · exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) hx

/-- A whole exact parallel solution on a finite union of period cosets
is the actual coefficient record of a finite same-class comb sum. -/
theorem exists_affineCombTermSum_of_exact_coefficient_recurrence
    (E : Finset (ℝ × ℝ)) (w : ℝ) (hw : 0 < w) (hE : ∀ p ∈ E, p.2 = w)
    (modes : List ℝ)
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (u : ℝ → ℂ) (hu : Function.support u ⊆ (affineLatticeUnionCarrier E).carrier)
    (hz : translationDifferenceProduct (modes.map fun s => (w,combModulationCharacter (-w) s)) u = 0) :
    ∃ terms : List AffineCombTerm,
      (∀ q ∈ terms, q.frequency ∈ modes) ∧
      (affineCombTermSumCarrier w hw terms).carrier ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ∀ x, extendedAtomicCoefficient (affineLatticeUnionCarrier E) (affineCombTermSum w hw terms) x = u x := by
  classical
  let A := affineLatticeUnionCarrier E
  let L := E.image fun p => affineLatticeLine p.1 w
  have hrep (b : L) : ∃ p ∈ E, affineLatticeLine p.1 w = b.val := Finset.mem_image.mp b.property
  choose rep hrepE hrepLine using hrep
  have hline (b : L) : affineLatticeLine (rep b).1 w ⊆ A.carrier := by
    intro x hx
    exact (mem_affineLatticeUnionCarrier E x).mpr
      ⟨rep b,hrepE b,by rwa [hE (rep b) (hrepE b)]⟩
  have hModes (b : L) := exists_character_modes_on_affine_line w modes hdistinct u hz (rep b).1
  choose coeff hFormula using hModes
  let I := L × Fin modes.length
  let q (j : I) : AffineCombTerm := ⟨modes.get j.2,(rep j.1).1,coeff j.1 j.2⟩
  let indices : Finset I := Finset.univ
  let terms := indices.toList.map q
  have hSum : affineCombTermSum w hw terms = ∑ j : I, (q j).distribution w hw := by
    simp only [terms, affineCombTermSum, List.map_map]
    let source (j : I) := (q j).distribution w hw
    change (indices.val.toList.map source).sum = (indices.val.map source).sum
    have he := congrArg (fun m : Multiset I => (m.map source).sum) (Multiset.coe_toList indices.val)
    simpa only [Multiset.map_coe, Multiset.sum_coe] using he
  refine ⟨terms, ?_, affineCombTermSumCarrier_subset_of_each w hw terms A ?_, ?_⟩
  · intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact List.get_mem _ _
  · intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact hline j.1
  · intro x
    change extendedAtomicCoefficient A (affineCombTermSum w hw terms) x = _
    rw [hSum, extendedAtomicCoefficient_finset_sum, Fintype.sum_prod_type]
    have he (b : L) (i : Fin modes.length) :
        extendedAtomicCoefficient A ((q (b,i)).distribution w hw) x =
          (q (b,i)).coefficientFunction w x :=
      extendedAtomicCoefficient_affineCombTerm (q (b,i)) w hw A (hline b) x
    simp_rw [he]
    by_cases hx : x ∈ A.carrier
    · obtain ⟨p,hp,hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
      let b₀ : L := ⟨affineLatticeLine p.1 w, Finset.mem_image_of_mem _ hp⟩
      have hx₀ : x ∈ affineLatticeLine (rep b₀).1 w := by
        rw [hrepLine b₀]
        simpa only [b₀,hE p hp] using hxp
      have hno (b : L) (hb : b ≠ b₀) : x ∉ affineLatticeLine (rep b).1 w := by
        intro he
        apply hb
        apply Subtype.ext
        rw [← hrepLine b, ← hrepLine b₀]
        exact (affineLatticeLine_eq_of_mem _ _ _ he).symm.trans
          (affineLatticeLine_eq_of_mem _ _ _ hx₀)
      rw [Finset.sum_eq_single_of_mem b₀ (Finset.mem_univ _) (fun b _ hb => by
        simp only [q, AffineCombTerm.coefficientFunction, Set.indicator_of_notMem (hno b hb),
          Finset.sum_const_zero])]
      simp only [q, AffineCombTerm.coefficientFunction, Set.indicator_of_mem hx₀]
      obtain ⟨k,hk⟩ := hx₀
      rw [← hk]
      exact (hFormula b₀ k).symm
    · have hu0 : u x = 0 := by
        by_contra h
        exact hx (hu h)
      have hno (b : L) : x ∉ affineLatticeLine (rep b).1 w := fun he => hx (hline b he)
      simp only [q, AffineCombTerm.coefficientFunction, Set.indicator_of_notMem (hno _),
        Finset.sum_const_zero, hu0]

end
end MeyerGeneralProblem
