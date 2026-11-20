module

public import MeyerGeneralProblem.Distribution.QuadrantResidueCharacters
public import MeyerGeneralProblem.Distribution.TranslationFactorsCount

@[expose] public section

/-!
# Coefficientwise recurrence of the original atomic record

Translation products on distributions act on the true zero-extended
coefficients, at every physical point. The Fourier phase cover supplies
the zero product for any finite list of spectral classes.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform

/-- The scalar translation factor with the positive physical pushforward
convention. It applies to all indices of an additive group. -/
def translationDifference {G : Type*} [AddGroup G] (a : G) (ω : ℂ) (f : G → ℂ) (x : G) : ℂ :=
  f (x - a) - ω * f x

/-- Factors act in the listed order on a bilateral coefficient function. -/
def translationDifferenceProduct {G : Type*} [AddGroup G] :
    List (G × ℂ) → (G → ℂ) → (G → ℂ)
  | [], f => f
  | (a,ω) :: factors, f => translationDifferenceProduct factors (translationDifference a ω f)

theorem translationDifferenceProduct_append {G : Type*} [AddGroup G]
    (P Q : List (G × ℂ)) (f : G → ℂ) :
    translationDifferenceProduct (P ++ Q) f =
      translationDifferenceProduct Q (translationDifferenceProduct P f) := by
  induction P generalizing f with
  | nil => rfl
  | cons p P ih =>
      rcases p with ⟨a,ω⟩
      exact ih (translationDifference a ω f)

/-- Pull back one physical factor to an affine orbit of the shift group. -/
theorem translationDifference_comp_affine {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (y : ℝ) (a : G) (ω : ℂ) (f : ℝ → ℂ) (x : G) :
    translationDifference a ω (fun g => f (y + L g)) x =
      translationDifference (L a) ω f (y + L x) := by
  rw [translationDifference, translationDifference, map_sub, add_sub_assoc]

/-- The entire bilateral product pulls back to an affine orbit when
each physical step is the image of a shift in the orbit's group. -/
theorem translationDifferenceProduct_comp_affine {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (y : ℝ) (factors : List (G × ℂ)) (f : ℝ → ℂ) (x : G) :
    translationDifferenceProduct factors (fun g => f (y + L g)) x =
      translationDifferenceProduct (factors.map fun p => (L p.1, p.2)) f (y + L x) := by
  induction factors generalizing f with
  | nil => rfl
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      have he : translationDifference a ω (fun g => f (y + L g)) =
          fun g => translationDifference (L a) ω f (y + L g) :=
        funext (translationDifference_comp_affine L y a ω f)
      change translationDifferenceProduct factors
        (translationDifference a ω (fun g => f (y + L g))) x =
          translationDifferenceProduct (factors.map fun p => (L p.1,p.2))
            (translationDifference (L a) ω f) (y + L x)
      rw [he]
      exact ih _

private theorem extendedAtomicCoefficient_sub (U : LocallyFiniteCarrier) (x : ℝ)
    (V T : TemperedDistribution ℝ ℂ) :
    extendedAtomicCoefficient U (V - T) x =
      extendedAtomicCoefficient U V x - extendedAtomicCoefficient U T x := by
  classical
  by_cases hx : x ∈ U.carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hx, sub_apply]
  · simp only [extendedAtomicCoefficient, dite_eq_right hx, sub_self]

/-- The exact intrinsic coefficient of one factor. Translated collisions
are combined on the common locally finite carrier. -/
theorem extendedAtomicCoefficient_combTranslationFactor (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (w s x : ℝ) :
    extendedAtomicCoefficient ((A.translate w).union A) (combTranslationFactor w s T) x =
      translationDifference w (combModulationCharacter (-w) s)
        (extendedAtomicCoefficient A T) x := by
  let U := (A.translate w).union A
  have hTranslate := extendedAtomicCoefficient_translation A T hT w (x - w)
  have he : w + (x - w) = x := by ring
  rw [he] at hTranslate
  change extendedAtomicCoefficient U (combTranslationFactor w s T) x = _
  rw [combTranslationFactor_apply, extendedAtomicCoefficient_sub, extendedAtomicCoefficient_smul,
    extendedAtomicCoefficient_on_larger_carrier (A.translate w) U Set.subset_union_left _
      (atomicOnCarrier_combDistributionTranslation A T hT w),
    extendedAtomicCoefficient_on_larger_carrier A U Set.subset_union_right T hT, hTranslate]
  rfl

/-- Coefficient transport for all phases of one class, at every site. -/
theorem extendedAtomicCoefficient_combTranslationFactors (w : ℝ) (modes : List ℝ)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (x : ℝ) :
    extendedAtomicCoefficient (combTranslationFactorsPhysicalCarrier w modes A)
        (combTranslationFactors w modes T) x =
      translationDifferenceProduct (modes.map fun s => (w, combModulationCharacter (-w) s))
        (extendedAtomicCoefficient A T) x := by
  induction modes generalizing A T with
  | nil => rfl
  | cons s modes ih =>
      change extendedAtomicCoefficient (combTranslationFactorsPhysicalCarrier w modes
        ((A.translate w).union A)) (combTranslationFactors w modes (combTranslationFactor w s T)) x =
        translationDifferenceProduct _ (translationDifference w (combModulationCharacter (-w) s)
          (extendedAtomicCoefficient A T)) x
      rw [ih _ _ (atomicOnCarrier_combTranslationFactor A T hT w s)]
      congr 1
      funext y
      exact extendedAtomicCoefficient_combTranslationFactor A T hT w s y

/-- The product of the translation factors from all spectral classes. -/
def combTranslationFactorsByClass :
    List (ℝ × List ℝ) → Module.End ℂ (TemperedDistribution ℝ ℂ)
  | [] => LinearMap.id
  | (w,modes) :: classes => (combTranslationFactorsByClass classes).comp
      (combTranslationFactors w modes)

/-- The genuine locally finite physical container for the whole product. -/
def combTranslationPhysicalCarrierByClass :
    List (ℝ × List ℝ) → LocallyFiniteCarrier → LocallyFiniteCarrier
  | [], A => A
  | (w,modes) :: classes, A => combTranslationPhysicalCarrierByClass classes
      (combTranslationFactorsPhysicalCarrier w modes A)

/-- The steps and phases in the literal order of the distributional product. -/
def combTranslationWeightsByClass (classes : List (ℝ × List ℝ)) : List (ℝ × ℂ) :=
  classes.flatMap fun p => p.2.map fun s => (p.1, combModulationCharacter (-p.1) s)

theorem extendedAtomicCoefficient_combTranslationFactorsByClass
    (classes : List (ℝ × List ℝ)) (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (x : ℝ) :
    extendedAtomicCoefficient (combTranslationPhysicalCarrierByClass classes A)
        (combTranslationFactorsByClass classes T) x =
      translationDifferenceProduct (combTranslationWeightsByClass classes)
        (extendedAtomicCoefficient A T) x := by
  induction classes generalizing A T with
  | nil => rfl
  | cons p classes ih =>
      obtain ⟨w,modes⟩ := p
      change extendedAtomicCoefficient (combTranslationPhysicalCarrierByClass classes
        (combTranslationFactorsPhysicalCarrier w modes A)) (combTranslationFactorsByClass classes
        (combTranslationFactors w modes T)) x = _
      rw [ih _ _ (atomicOnCarrier_combTranslationFactors w modes A T hT)]
      change _ = translationDifferenceProduct
        ((modes.map fun s => (w, combModulationCharacter (-w) s)) ++
          combTranslationWeightsByClass classes) (extendedAtomicCoefficient A T) x
      rw [translationDifferenceProduct_append]
      congr 1
      funext y
      exact extendedAtomicCoefficient_combTranslationFactors w modes A T hT y

/-- Every covered Fourier atom is removed by the corresponding phase
factor, and therefore the full product kills the original distribution. -/
theorem combTranslationFactorsByClass_eq_zero_of_phase_cover
    (classes : List (ℝ × List ℝ)) (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier B (𝓕 T))
    (hcover : ∀ x ∈ B.carrier, ∃ p ∈ classes, ∃ s ∈ p.2,
      combModulationCharacter (-p.1) x = combModulationCharacter (-p.1) s) :
    combTranslationFactorsByClass classes T = 0 := by
  induction classes generalizing B T with
  | nil =>
      apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
      change 𝓕 T = 𝓕 (0 : TemperedDistribution ℝ ℂ)
      rw [FourierTransform.fourier_zero]
      ext f
      exact hFT f fun x hx => by simpa using hcover x hx
  | cons p classes ih =>
      obtain ⟨w,modes⟩ := p
      change combTranslationFactorsByClass classes (combTranslationFactors w modes T) = 0
      apply ih _ _ (atomicOnCarrier_fourier_combTranslationFactors B w modes T hFT)
      intro x hx
      obtain ⟨p,hp,s,hs,he⟩ := hcover x hx.1
      rcases List.mem_cons.mp hp with h | hp
      · subst p
        exact (hx.2 s hs he).elim
      · exact ⟨p,hp,s,hs,he⟩

/-- The original bilateral coefficient recurrence for a spectrum covered
by finitely many prescribed translated reciprocal lattices. -/
theorem translationDifferenceProduct_extendedAtomicCoefficient_eq_zero_of_spectral_cover
    (classes : List (ℝ × List ℝ)) (hpos : ∀ p ∈ classes, 0 < p.1)
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (hcover : ∀ x ∈ B.carrier, ∃ p ∈ classes, ∃ s ∈ p.2,
      ∃ k : ℤ, x = s + (k : ℝ) * p.1⁻¹) :
    translationDifferenceProduct (combTranslationWeightsByClass classes)
      (extendedAtomicCoefficient A T) = 0 := by
  have hPhase (x : ℝ) (hx : x ∈ B.carrier) : ∃ p ∈ classes, ∃ s ∈ p.2,
      combModulationCharacter (-p.1) x = combModulationCharacter (-p.1) s := by
    obtain ⟨p,hp,s,hs,k,rfl⟩ := hcover x hx
    exact ⟨p,hp,s,hs,combModulationCharacter_eq_on_reciprocal_coset p.1 s (hpos p hp) k⟩
  have hzero := combTranslationFactorsByClass_eq_zero_of_phase_cover classes B T hFT hPhase
  funext x
  rw [← extendedAtomicCoefficient_combTranslationFactorsByClass classes A T hT x, hzero]
  classical
  by_cases hx : x ∈ (combTranslationPhysicalCarrierByClass classes A).carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hx, zero_apply, Pi.zero_apply]
  · simp only [extendedAtomicCoefficient, dite_eq_right hx, Pi.zero_apply]

/-- One factor can use a site in the original support or one of its
physical translates. This bound allows every cancellation. -/
theorem support_translationDifference_subset {G : Type*} [AddCommGroup G]
    (a : G) (ω : ℂ) (f : G → ℂ) :
    Function.support (translationDifference a ω f) ⊆
      Function.support f ∪ (fun y => y + a) '' Function.support f := by
  intro x hx
  by_cases h : f x = 0
  · refine Or.inr ⟨x - a, ?_, sub_add_cancel _ _⟩
    intro hzero
    exact hx (by simp [translationDifference, h, hzero])
  · exact Or.inl h

/-- A translation factor preserves finite support on the bilateral
coefficient group. -/
theorem finite_support_translationDifference {G : Type*} [AddCommGroup G]
    (a : G) (ω : ℂ) (f : G → ℂ) (hf : (Function.support f).Finite) :
    (Function.support (translationDifference a ω f)).Finite :=
  (hf.union (hf.image (fun y => y + a))).subset (support_translationDifference_subset a ω f)

/-- A single nonzero translate-minus-phase has zero kernel on finite
support, by propagation along the infinite orbit of one nonzero site. -/
theorem eq_zero_of_translationDifference_of_finite_support {G : Type*} [AddCommGroup G]
    (a : G) (ω : ℂ) (hω : ω ≠ 0) (hinj : Function.Injective (fun n : ℕ => n • a))
    (f : G → ℂ) (hf : (Function.support f).Finite) (hz : translationDifference a ω f = 0) :
    f = 0 := by
  funext x
  by_contra hx
  have hnon (n : ℕ) : f (x - n • a) ≠ 0 := by
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        have h := sub_eq_zero.mp (congrFun hz (x - n • a))
        change f (x - n • a - a) = ω * f (x - n • a) at h
        rw [succ_nsmul, ← sub_sub, h]
        exact mul_ne_zero hω ih
  let orbit (n : ℕ) := x - n • a
  have horbit : Function.Injective orbit := by
    intro n m he
    apply hinj
    have he' := congrArg (fun y => x - y) he
    simpa only [orbit, sub_sub_cancel] using he'
  have hsub : Set.range orbit ⊆ Function.support f := by
    rintro _ ⟨n, rfl⟩
    exact hnon n
  exact (Set.infinite_range_of_injective horbit).not_finite (hf.subset hsub)

/-- Finite crossing defects cannot survive the whole translation product. -/
theorem eq_zero_of_translationDifferenceProduct_of_finite_support {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ))
    (hFactors : ∀ p ∈ factors, p.2 ≠ 0 ∧ Function.Injective (fun n : ℕ => n • p.1))
    (f : G → ℂ) (hf : (Function.support f).Finite)
    (hz : translationDifferenceProduct factors f = 0) : f = 0 := by
  induction factors generalizing f with
  | nil => exact hz
  | cons p factors ih =>
      have hp := hFactors p List.mem_cons_self
      obtain ⟨a,ω⟩ := p
      exact eq_zero_of_translationDifference_of_finite_support a ω hp.1 hp.2 f hf
        (ih (fun q hq => hFactors q (List.mem_cons_of_mem _ hq))
          (translationDifference a ω f) (finite_support_translationDifference a ω f hf) hz)

end
end MeyerGeneralProblem
