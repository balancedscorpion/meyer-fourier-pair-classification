module

public import MeyerGeneralProblem.Distribution.OriginalTranslationRecurrence

@[expose] public section

/-!
# Translation products and finite support on quotient fibers

Translation factors commute. They preserve a finite image of the
support in the quotient, and preserve finite support on each quotient
fiber. These facts control the crossing terms of the original record.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

theorem translationDifference_sub {G : Type*} [AddCommGroup G] (a : G) (ω : ℂ)
    (f g : G → ℂ) :
    translationDifference a ω (f - g) =
      translationDifference a ω f - translationDifference a ω g := by
  funext x
  simp only [translationDifference, Pi.sub_apply]
  ring

theorem translationDifferenceProduct_sub {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) (f g : G → ℂ) :
    translationDifferenceProduct factors (f - g) =
      translationDifferenceProduct factors f - translationDifferenceProduct factors g := by
  induction factors generalizing f g with
  | nil => rfl
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      change translationDifferenceProduct factors (translationDifference a ω (f - g)) =
        translationDifferenceProduct factors (translationDifference a ω f) -
          translationDifferenceProduct factors (translationDifference a ω g)
      rw [translationDifference_sub, ih]

theorem translationDifference_commute {G : Type*} [AddCommGroup G] (a b : G) (ω ξ : ℂ)
    (f : G → ℂ) :
    translationDifference a ω (translationDifference b ξ f) =
      translationDifference b ξ (translationDifference a ω f) := by
  funext x
  simp only [translationDifference]
  have he : x - a - b = x - b - a := by abel
  rw [he]
  ring

theorem translationDifferenceProduct_eq_of_perm {G : Type*} [AddCommGroup G]
    {factors more : List (G × ℂ)} (h : factors.Perm more) (f : G → ℂ) :
    translationDifferenceProduct factors f = translationDifferenceProduct more f := by
  induction h generalizing f with
  | nil => rfl
  | cons p _ ih =>
      obtain ⟨a,ω⟩ := p
      exact ih (translationDifference a ω f)
  | swap p q factors =>
      obtain ⟨a,ω⟩ := p
      obtain ⟨b,ξ⟩ := q
      change translationDifferenceProduct factors (translationDifference a ω (translationDifference b ξ f)) =
        translationDifferenceProduct factors (translationDifference b ξ (translationDifference a ω f))
      rw [translationDifference_commute a b ω ξ f]
  | trans _ _ ih₁ ih₂ => exact (ih₁ _).trans (ih₂ _)

private theorem support_translationDifference_inter_fiber_subset
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (a : G) (ω : ℂ) (f : G → ℂ) (z : Q) :
    Function.support (translationDifference a ω f) ∩ π ⁻¹' {z} ⊆
      (Function.support f ∩ π ⁻¹' {z}) ∪
        (fun y => y + a) '' (Function.support f ∩ π ⁻¹' {z - π a}) := by
  rintro x ⟨hx,hz⟩
  change π x = z at hz
  rcases support_translationDifference_subset a ω f hx with h | ⟨y,hy,rfl⟩
  · exact Or.inl ⟨h,hz⟩
  · apply Or.inr
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    change π y = z - π a
    rw [map_add] at hz
    rw [← hz, add_sub_cancel_right]

private theorem finite_image_support_translationDifference
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (a : G) (ω : ℂ) (f : G → ℂ) (hf : (π '' Function.support f).Finite) :
    (π '' Function.support (translationDifference a ω f)).Finite := by
  refine (hf.union (hf.image (fun z => z + π a))).subset ?_
  rintro _ ⟨x,hx,rfl⟩
  rcases support_translationDifference_subset a ω f hx with h | ⟨y,hy,rfl⟩
  · exact Or.inl ⟨x,h,rfl⟩
  · exact Or.inr ⟨π y,⟨y,hy,rfl⟩,(map_add π y a).symm⟩

theorem finite_image_support_translationDifferenceProduct
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (factors : List (G × ℂ)) (f : G → ℂ) (hf : (π '' Function.support f).Finite) :
    (π '' Function.support (translationDifferenceProduct factors f)).Finite := by
  induction factors generalizing f with
  | nil => exact hf
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      exact ih _ (finite_image_support_translationDifference π a ω f hf)

theorem finite_support_inter_fiber_translationDifferenceProduct
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (π : G →+ Q)
    (factors : List (G × ℂ)) (f : G → ℂ)
    (hf : ∀ z, (Function.support f ∩ π ⁻¹' {z}).Finite) :
    ∀ z, (Function.support (translationDifferenceProduct factors f) ∩ π ⁻¹' {z}).Finite := by
  induction factors generalizing f with
  | nil => exact hf
  | cons p factors ih =>
      obtain ⟨a,ω⟩ := p
      apply ih
      intro z
      exact ((hf z).union ((hf (z - π a)).image (fun y => y + a))).subset
        (support_translationDifference_inter_fiber_subset π a ω f z)

end
end MeyerGeneralProblem
