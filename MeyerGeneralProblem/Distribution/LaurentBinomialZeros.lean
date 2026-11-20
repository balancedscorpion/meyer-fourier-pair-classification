module

public import MeyerGeneralProblem.Distribution.LaurentPrimeTrimming
public import MeyerGeneralProblem.Distribution.RealRootedLaurentSlices
public import MeyerGeneralProblem.Distribution.CommonRealRootedPresentation
public import MeyerGeneralProblem.Distribution.OriginalAnnihilatorRelativeSeparation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Full real lattice cosets from the trimmed binomial product

Every real zero set of a literal Laurent binomial is empty or a full
affine lattice. The zeros of the trimmed product give a finite union
of these lattices on the physical record of the original pair.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform Topology

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

private theorem annihilatorExponentialSymbol_binomial
    (L : G →+ ℝ) (d : G) (c : ℂ) (x : ℝ) :
    annihilatorExponentialSymbol L (laurentBinomial d c).coeff x =
      combModulationCharacter (L d) x - c := by
  classical
  change ((Finsupp.single d (1 : ℂ) - Finsupp.single 0 c).sum
    (fun n a => a * combModulationCharacter (L n) x)) = _
  rw [Finsupp.sum_sub_index (fun _ a b => sub_mul a b _)]
  simp [Finsupp.sum_single_index, combModulationCharacter_zero_left]

private theorem annihilatorExponentialSymbol_one (L : G →+ ℝ) (x : ℝ) :
    annihilatorExponentialSymbol L (1 : AddMonoidAlgebra ℂ G).coeff x = 1 := by
  change (Finsupp.single 0 (1 : ℂ)).sum (fun n a => a * combModulationCharacter (L n) x) = 1
  simp [Finsupp.sum_single_index, combModulationCharacter_zero_left]

/-- The zeros of a binomial product are exactly the union of its
individual real zero sets. -/
theorem annihilatorExponentialSymbol_binomialProduct_eq_zero_iff
    (L : G →+ ℝ) (l : List (G × ℂ)) (x : ℝ) :
    annihilatorExponentialSymbol L ((l.map (fun p => laurentBinomial p.1 p.2)).prod).coeff x = 0 ↔
      ∃ p ∈ l, combModulationCharacter (L p.1) x = p.2 := by
  induction l with
  | nil => simp [annihilatorExponentialSymbol_one]
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, ← complexExponentialSum_ofReal,
      complexExponentialSum_laurent_mul]
    simp only [complexExponentialSum_ofReal, mul_eq_zero,
      annihilatorExponentialSymbol_binomial, sub_eq_zero, ih, List.mem_cons,
      exists_eq_or_imp]

theorem realCharacter_eq_iff_periodic
    (w : ℝ) (hw : w ≠ 0) (x₀ x : ℝ) :
    combModulationCharacter w x = combModulationCharacter w x₀ ↔
      ∃ k : ℤ, x = x₀ + (k : ℝ) / w := by
  rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp,
    Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    have hi := congrArg Complex.im hk
    simp [Complex.mul_im] at hi
    have hh : w * x = w * x₀ + (k : ℝ) := by
      apply mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
      linear_combination hi
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hw
    rw [mul_add, mul_div_cancel₀ _ hw]
    exact hh
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    field_simp [show (w : ℂ) ≠ 0 by exact_mod_cast hw]

/-- Starting from one real zero, the whole binomial zero set is a
single full lattice with positive period. -/
theorem exists_positive_period_of_realCharacter_zero
    (w : ℝ) (hw : w ≠ 0) (c : ℂ) (x₀ : ℝ) (hx₀ : combModulationCharacter w x₀ = c) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, combModulationCharacter w x = c ↔
      ∃ k : ℤ, x = x₀ + (k : ℝ) * a := by
  refine ⟨|w|⁻¹, inv_pos.mpr (abs_pos.mpr hw), fun x => ?_⟩
  rw [← hx₀, realCharacter_eq_iff_periodic w hw x₀ x]
  rcases lt_or_gt_of_ne hw with hn | hp
  · rw [abs_of_neg hn]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨-k, by simpa [div_eq_mul_inv] using hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨-k, by simpa [div_eq_mul_inv] using hk⟩
  · simp [abs_of_pos hp, div_eq_mul_inv]

/-- The real zeros of the whole binomial product form a finite union
of full affine lattices. -/
theorem exists_binomialProduct_latticeZeros (L : G →+ ℝ) (hL : Function.Injective L)
    (l : List (G × ℂ)) (hl : ∀ p ∈ l, p.1 ≠ 0) :
    ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧ ∀ x : ℝ,
      annihilatorExponentialSymbol L ((l.map (fun p => laurentBinomial p.1 p.2)).prod).coeff x = 0 ↔
        ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2 := by
  classical
  have haux : ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧ ∀ x : ℝ,
      (∃ p ∈ l, combModulationCharacter (L p.1) x = p.2) ↔
        ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2 := by
    induction l with
    | nil => exact ⟨[], by simp⟩
    | cons p l ih =>
      obtain ⟨E, hE, hEq⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      by_cases hp : ∃ x, combModulationCharacter (L p.1) x = p.2
      · obtain ⟨x, hx⟩ := hp
        have hω : L p.1 ≠ 0 := fun h => hl p (by simp) (hL (h.trans (map_zero L).symm))
        obtain ⟨a, ha, haEq⟩ := exists_positive_period_of_realCharacter_zero (L p.1) hω p.2 x hx
        refine ⟨(x, a) :: E, ?_, fun y => ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ha
          · exact hE z hz
        · simpa only [List.mem_cons, exists_eq_or_imp, exists_prop, and_comm, exists_or] using
            (or_congr (haEq y) (hEq y))
      · refine ⟨E, hE, fun x => ?_⟩
        have hx : combModulationCharacter (L p.1) x ≠ p.2 := fun h => hp ⟨x, h⟩
        simpa only [List.mem_cons, exists_eq_or_imp, exists_prop, and_comm, exists_or, hx,
          false_or] using hEq x
  obtain ⟨E, hE, hEq⟩ := haux
  exact ⟨E, hE, fun x => (annihilatorExponentialSymbol_binomialProduct_eq_zero_iff L l x).trans (hEq x)⟩

/-- After exhaustive Laurent cancellation, intersecting the physical
carrier with a finite union of full lattices preserves the complete
original pair space. -/
theorem exists_originalPairSpace_lattice_intersection_of_vanishingQuadraticLowerCount
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (P : AddMonoidAlgebra ℂ G) (hP : P ≠ 0)
    (A B : LocallyFiniteCarrier) (hmodule : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L P.coeff x = 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      ∃ A₀ : LocallyFiniteCarrier,
        A₀.carrier = A.carrier ∩ {x | ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2} ∧
        DistributionalMeyerPairSpace A B = DistributionalMeyerPairSpace A₀ B := by
  obtain ⟨l, hl, _, hEq⟩ :=
    exists_originalPairSpace_binomial_annihilator_of_vanishingQuadraticLowerCount
      b L hL P hP A B hmodule hA hcount
  obtain ⟨E, hE, hzero⟩ := exists_binomialProduct_latticeZeros L hL l (fun p hp => (hl p hp).1)
  let Q := (l.map (fun p => laurentBinomial p.1 p.2)).prod
  let A₀ := annihilatorZeroSubcarrier L Q.coeff A
  refine ⟨E, hE, A₀, ?_, hEq⟩
  ext x
  exact and_congr_right fun _ => hzero x

/-- Bounded local counts on the physical carrier give the original
spectral module internally. Under vanishing opposite quadratic lower
count, a finite-lattice intersection preserves the complete space. -/
theorem exists_originalPairSpace_lattice_intersection_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      ∃ A₀ : LocallyFiniteCarrier,
        A₀.carrier = A.carrier ∩ {x | ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2} ∧
        DistributionalMeyerPairSpace A B = DistributionalMeyerPairSpace A₀ B := by
  let Γ := pairSpectralModule A B
  let L := Γ.subtype
  let B₁ := pairSpectralCore A B
  obtain ⟨hΓ, _, _, P, _, _, hP, _, _, hV⟩ :=
    exists_common_realRooted_core_of_unitCellBound A B K hK
  let A₁ := annihilatorZeroSubcarrier L P.coeff A
  have hB₁ : B₁.carrier ⊆ B.carrier := fun _ hx => hx.1
  have hmodule : B₁.carrier ⊆ range L := fun x hx => ⟨⟨x, hx.2⟩, rfl⟩
  have hcount₁ (c : ℝ) (hc : 0 < c) :
      ∃ᶠ R : ℝ in atTop, ((B₁.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2 := by
    refine (hcount c hc).mono fun R hR => lt_of_le_of_lt ?_ hR
    have hsub : B₁.carrier ∩ Icc (-R) R ⊆ B.carrier ∩ Icc (-R) R :=
      inter_subset_inter_left _ hB₁
    exact_mod_cast Set.ncard_le_ncard hsub (B.finite_inter_Icc _ _)
  let _ : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr
    ((AddGroup.fg_iff_addSubgroup_fg Γ).mpr hΓ)
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Γ)
  obtain ⟨E, hE, A₂, hA₂, heq⟩ :=
    exists_originalPairSpace_lattice_intersection_of_vanishingQuadraticLowerCount
      b L Subtype.val_injective P hP A₁ B₁ hmodule (fun _ hx => hx.2) hcount₁
  let Z := {x : ℝ | ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2}
  let A₀ := A.restrict (A.carrier ∩ Z) inter_subset_left
  refine ⟨E, hE, A₀, rfl, ?_⟩
  have hA₂sub : A₂.carrier ⊆ A₀.carrier := by
    intro x hx
    rw [hA₂] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hA₀ : A₀.carrier ⊆ A.carrier := inter_subset_left
  ext T
  constructor
  · intro hT
    rw [hV, heq] at hT
    obtain ⟨ha, hb⟩ := (mem_distributionalMeyerPairSpace_iff _ _ _).mp hT
    exact (mem_distributionalMeyerPairSpace_iff _ _ _).mpr ⟨ha.mono hA₂sub, hb.mono hB₁⟩
  · intro hT
    obtain ⟨ha, hb⟩ := (mem_distributionalMeyerPairSpace_iff _ _ _).mp hT
    exact (mem_distributionalMeyerPairSpace_iff _ _ _).mpr ⟨ha.mono hA₀, hb⟩

/-- An original broad pair with upper linear centered count on its
actual physical record and vanishing opposite quadratic lower count
has a physical carrier reduced to finitely many full affine lattices. -/
theorem exists_lattice_intersection_of_centered_count_of_atomic_pair
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hactual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      ∃ A₀ : LocallyFiniteCarrier,
        A₀.carrier = A.carrier ∩ {x | ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2} ∧
        AtomicOnCarrier A₀ T := by
  obtain ⟨K, hK⟩ := exists_unitCellBound_of_centered_count_of_atomic_pair
    A B hb T hT hFT hactual
  obtain ⟨E, hE, A₀, hA₀, heq⟩ :=
    exists_originalPairSpace_lattice_intersection_of_unitCellBound A B K hK hcount
  have hp : T ∈ DistributionalMeyerPairSpace A B :=
    (mem_distributionalMeyerPairSpace_iff _ _ _).mpr ⟨hT, hFT⟩
  rw [heq] at hp
  exact ⟨E, hE, A₀, hA₀, ((mem_distributionalMeyerPairSpace_iff _ _ _).mp hp).1⟩

/-- The Fourier exchange of the original pair has its original
spectral record on a finite union of full lattices. Its physical
record is the original opposite record with the given count bound. -/
theorem exists_reflected_lattice_spectralCarrier_of_centered_count
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hactual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∃ E : List (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      ∃ C : LocallyFiniteCarrier, AtomicOnCarrier C (𝓕 (𝓕 T)) ∧
        ∀ x ∈ C.carrier, ∃ p ∈ E, ∃ k : ℤ, x = p.1 + (k : ℝ) * p.2 := by
  obtain ⟨E, hE, A₀, hA₀, hT₀⟩ :=
    exists_lattice_intersection_of_centered_count_of_atomic_pair A B hb T hT hFT hactual hcount
  let reflect (p : ℝ × ℝ) := (-p.1, p.2)
  refine ⟨E.map reflect, ?_, A₀.reflect, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hE q hq
  · rw [fourier_fourier_eq_originalDistributionReflection]
    exact atomicOnCarrier_originalDistributionReflection A₀ T hT₀
  · rintro _ ⟨x, hx, rfl⟩
    rw [hA₀] at hx
    obtain ⟨p, hp, k, hk⟩ := hx.2
    refine ⟨reflect p, List.mem_map.mpr ⟨p, hp, rfl⟩, -k, ?_⟩
    simp [reflect, hk, add_comm]

end

end MeyerGeneralProblem
