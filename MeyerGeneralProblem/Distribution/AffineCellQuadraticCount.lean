module

public import MeyerGeneralProblem.Distribution.CharacterSumBlocks
public import MeyerGeneralProblem.Distribution.IntegerAffineCells
public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients

@[expose] public section

/-!
# A quadratic count obstruction from an occupied integer affine cell

Disjoint blocks select distinct physical sites of the total character
sum. A locally finite exceptional set with linear count absorbs only
linearly many of those sites. The resulting quadratic lower bound holds
at every sufficiently large radius.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped BigOperators

private theorem centered_count_add_ge_block_card {κ : Type*} [Fintype κ]
    (F : ℤ × ℤ → ℂ) (M : ℕ) (hM : 0 < M)
    (hblock : ∀ o : ℤ × ℤ, ∃ m n : Fin M, F (o.1 + (m : ℕ), o.2 + (n : ℕ)) ≠ 0)
    (u : κ → ℤ × ℤ) (c : κ → ℤ) (d : ℤ × ℤ) (hd : ∀ i, 0 < integerPlaneForm (u i) d)
    (L : ℤ × ℤ →+ ℝ) (hL : Function.Injective L) (y : ℝ) (A X : LocallyFiniteCarrier)
    (hsite : ∀ k ∈ integerAffineCell u c, F k ≠ 0 →
      y + L k ∉ X.carrier → y + L k ∈ A.carrier) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (R : ℝ), 0 < N → C * (N : ℝ) ≤ R →
      (N : ℝ) ^ 2 ≤ ((A.carrier ∩ Icc (-R) R).ncard : ℝ) +
        ((X.carrier ∩ Icc (-R) R).ncard : ℝ) := by
  obtain ⟨B, hB, hbox⟩ := exists_integer_square_in_affineCell u c d hd L y
  refine ⟨B * M, by positivity, ?_⟩
  intro N R hN hR
  obtain ⟨o, ho⟩ := hbox (M * N) (Nat.mul_pos hM hN)
  obtain ⟨f, hf, hfne⟩ := exists_injective_nonzero_block_sites F M N hM hblock o
  let P (i : Fin N × Fin N) : ℤ × ℤ := (o.1 + (f i).1.val, o.2 + (f i).2.val)
  let g (i : Fin N × Fin N) := y + L (P i)
  have hg : Function.Injective g := by
    intro i j he
    apply hf
    have heq : P i = P j := hL (add_left_cancel he)
    apply Prod.ext
    · exact Fin.ext (Int.ofNat_inj.mp (add_left_cancel (congrArg Prod.fst heq)))
    · exact Fin.ext (Int.ofNat_inj.mp (add_left_cancel (congrArg Prod.snd heq)))
  let W := Icc (-R) R
  let A₀ := A.carrier ∩ W
  let X₀ := X.carrier ∩ W
  have hsubset : Set.range g ⊆ A₀ ∪ X₀ := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨hcell, hbound⟩ := ho (f i).1 (f i).2
    have hw : g i ∈ W := abs_le.mp (hbound.trans (by push_cast; linarith only [hR]))
    by_cases hx : g i ∈ X.carrier
    · exact Or.inr ⟨hx, hw⟩
    · exact Or.inl ⟨hsite (P i) hcell (hfne i) hx, hw⟩
  have hcard : N ^ 2 ≤ A₀.ncard + X₀.ncard := calc
    _ = (Set.range g).ncard := by rw [Set.ncard_range_of_injective hg]; simp [pow_two]
    _ ≤ (A₀ ∪ X₀).ncard := Set.ncard_le_ncard hsubset
      ((A.finite_inter_Icc (-R) R).union (X.finite_inter_Icc (-R) R))
    _ ≤ _ := Set.ncard_union_le _ _
  exact_mod_cast hcard

/-- A nonzero aggregate character sum on a cell admitting a strict
integer direction forces an eventual positive quadratic count. The
exceptional sites may include crossings and the same-class combs. -/
theorem exists_eventually_quadratic_count_of_planarCharacterSum_on_affineCell
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (coeff z w : ι → ℂ) (hz : ∀ j, z j ≠ 0) (hw : ∀ j, w j ≠ 0)
    (hne : ∃ k, planarCharacterSum coeff z w k ≠ 0)
    (u : κ → ℤ × ℤ) (c : κ → ℤ) (d : ℤ × ℤ) (hd : ∀ i, 0 < integerPlaneForm (u i) d)
    (L : ℤ × ℤ →+ ℝ) (hL : Function.Injective L) (y : ℝ) (A X : LocallyFiniteCarrier)
    (hsite : ∀ k ∈ integerAffineCell u c, planarCharacterSum coeff z w k ≠ 0 →
      y + L k ∉ X.carrier → y + L k ∈ A.carrier)
    (hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
      ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ R : ℝ in atTop,
      e * R ^ 2 ≤ ((A.carrier ∩ Icc (-R) R).ncard : ℝ) := by
  let M := Fintype.card ι + 1
  have hM : 0 < M := Nat.succ_pos _
  obtain ⟨C, hC, hcount⟩ := centered_count_add_ge_block_card
    (planarCharacterSum coeff z w) M hM
    (exists_planarCharacterSum_ne_zero_in_block coeff z w hz hw hne)
    u c d hd L hL y A X hsite
  obtain ⟨b, hb, hX⟩ := hX
  let e : ℝ := (8 * C ^ 2)⁻¹
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨e, he, ?_⟩
  filter_upwards [hX, eventually_ge_atTop (2 * C), eventually_ge_atTop (b / e)] with R hX hR hbR
  let N := ⌊R / C⌋₊
  have hR₀ : 0 ≤ R := by linarith
  have hN₁ : 1 ≤ N := (Nat.one_le_floor_iff (R / C)).mpr
    ((le_div_iff₀ hC).mpr (by linarith))
  have hNpos : 0 < N := hN₁
  have hNhi : C * (N : ℝ) ≤ R := by
    rw [mul_comm]
    exact (le_div_iff₀ hC).mp (Nat.floor_le (div_nonneg hR₀ hC.le))
  have hNlo : R / (2 * C) ≤ (N : ℝ) := by
    have hlo : 2 ≤ R / C := (le_div_iff₀ hC).mpr hR
    have hhi : R / C < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have half : R / C / 2 ≤ (N : ℝ) := by linarith
    simpa only [div_div, mul_comm C 2] using half
  have hquad : 2 * e * R ^ 2 ≤ (N : ℝ) ^ 2 := calc
    _ = (R / (2 * C)) ^ 2 := by dsimp [e]; field_simp; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hNlo 2
  have hlinear : b * R ≤ e * R ^ 2 := by
    have hb₁ : b ≤ R * e := (div_le_iff₀ he).mp hbR
    have hm := mul_le_mul_of_nonneg_right hb₁ hR₀
    nlinarith
  linarith [hcount N R hNpos hNhi]

/-- Exact agreement with the total original coefficient outside a
linearly counted set forces the character sum to vanish on a cell with
a strict direction when the original carrier has quadratic liminf zero. -/
theorem planarCharacterSum_eq_zero_of_vanishingQuadraticLowerCount_on_affineCell
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (coeff z w : ι → ℂ) (hz : ∀ j, z j ≠ 0) (hw : ∀ j, w j ≠ 0)
    (u : κ → ℤ × ℤ) (c : κ → ℤ) (d : ℤ × ℤ) (hd : ∀ i, 0 < integerPlaneForm (u i) d)
    (L : ℤ × ℤ →+ ℝ) (hL : Function.Injective L) (y : ℝ) (A X : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ)
    (hcoeff : ∀ k ∈ integerAffineCell u c, y + L k ∉ X.carrier →
      extendedAtomicCoefficient A T (y + L k) = planarCharacterSum coeff z w k)
    (hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
      ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∀ k, planarCharacterSum coeff z w k = 0 := by
  by_contra! hne
  have hsite (k : ℤ × ℤ) (hk : k ∈ integerAffineCell u c)
      (hne : planarCharacterSum coeff z w k ≠ 0) (hx : y + L k ∉ X.carrier) :
      y + L k ∈ A.carrier := by
    by_contra ha
    have he := hcoeff k hk hx
    classical
    rw [extendedAtomicCoefficient, dite_eq_right ha] at he
    exact hne he.symm
  obtain ⟨e, he, hlower⟩ := exists_eventually_quadratic_count_of_planarCharacterSum_on_affineCell
    coeff z w hz hw hne u c d hd L hL y A X hsite hX
  obtain ⟨R, hR, hsmall⟩ := (hcount e he).and_eventually hlower |>.exists
  exact (not_lt_of_ge hsmall) hR

/-- On a single residue cell with the exact aggregate coefficient, all
surviving sites outside the exceptional set lie on finitely many affine
cyclic lines. The line directions are images of the original integer
coordinate lattice. -/
theorem exists_finite_affine_lattice_cover_on_affineCell_of_vanishingQuadraticLowerCount
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (coeff z w : ι → ℂ) (hz : ∀ j, z j ≠ 0) (hw : ∀ j, w j ≠ 0)
    (u : κ → ℤ × ℤ) (c : κ → ℤ) (hu : ∀ i, u i ≠ 0)
    (L : ℤ × ℤ →+ ℝ) (hL : Function.Injective L) (y : ℝ) (A X : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ)
    (hcoeff : ∀ k ∈ integerAffineCell u c, y + L k ∉ X.carrier →
      extendedAtomicCoefficient A T (y + L k) = planarCharacterSum coeff z w k)
    (hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
      ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ E : Finset (ℝ × ℝ),
      (∀ p ∈ E, p.1 ∈ Set.range (fun k => y + L k) ∧ p.2 ∈ Set.range L) ∧
      ∀ k ∈ integerAffineCell u c, y + L k ∉ X.carrier →
        extendedAtomicCoefficient A T (y + L k) ≠ 0 →
        ∃ p ∈ E, ∃ t : ℤ, y + L k = p.1 + (t : ℝ) * p.2 := by
  classical
  by_cases h : ∃ d, ∀ i, 0 < integerPlaneForm (u i) d
  · obtain ⟨d, hd⟩ := h
    have hzero := planarCharacterSum_eq_zero_of_vanishingQuadraticLowerCount_on_affineCell
      coeff z w hz hw u c d hd L hL y A X T hcoeff hX hcount
    exact ⟨∅, by simp, fun k hk hx hne => (hne ((hcoeff k hk hx).trans (hzero k))).elim⟩
  · obtain ⟨E, hE⟩ := exists_finite_affineCyclic_cover_of_no_strict_direction u c hu h
    refine ⟨E.image (fun p => (y + L p.1, L p.2)), ?_, ?_⟩
    · intro p hp
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨⟨r.1, rfl⟩, ⟨r.2, rfl⟩⟩
    · intro k hk _ _
      obtain ⟨p, hp, t, rfl⟩ := hE k hk
      exact ⟨(y + L p.1, L p.2), Finset.mem_image_of_mem _ hp, t, by
        rw [map_add, map_zsmul, zsmul_eq_mul, add_assoc]⟩

/-- Constant inequalities generated during residue refinement can be
removed, or force the whole cell to be empty. -/
theorem exists_finite_affine_lattice_cover_on_affineCell_with_constant_constraints
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (coeff z w : ι → ℂ) (hz : ∀ j, z j ≠ 0) (hw : ∀ j, w j ≠ 0)
    (u : κ → ℤ × ℤ) (c : κ → ℤ)
    (L : ℤ × ℤ →+ ℝ) (hL : Function.Injective L) (y : ℝ) (A X : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ)
    (hcoeff : ∀ k ∈ integerAffineCell u c, y + L k ∉ X.carrier →
      extendedAtomicCoefficient A T (y + L k) = planarCharacterSum coeff z w k)
    (hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
      ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ E : Finset (ℝ × ℝ),
      (∀ p ∈ E, p.1 ∈ Set.range (fun k => y + L k) ∧ p.2 ∈ Set.range L) ∧
      ∀ k ∈ integerAffineCell u c, y + L k ∉ X.carrier →
        extendedAtomicCoefficient A T (y + L k) ≠ 0 →
        ∃ p ∈ E, ∃ t : ℤ, y + L k = p.1 + (t : ℝ) * p.2 := by
  classical
  have hzform (k : ℤ × ℤ) : integerPlaneForm 0 k = 0 := by simp [integerPlaneForm]
  by_cases hbad : ∃ i, u i = 0 ∧ 0 < c i
  · obtain ⟨i, hi, hp⟩ := hbad
    refine ⟨∅, by simp, fun k hk _ _ => ?_⟩
    have he : c i ≤ integerPlaneForm (u i) k := hk i
    rw [hi, hzform] at he
    exact (not_lt_of_ge he hp).elim
  · let I := {i // u i ≠ 0}
    have hcell : integerAffineCell (fun i : I => u i) (fun i : I => c i) =
        integerAffineCell u c := by
      ext k
      constructor
      · intro hk i
        by_cases hi : u i = 0
        · have hn : c i ≤ 0 := le_of_not_gt fun hp => hbad ⟨i, hi, hp⟩
          simpa only [hi, hzform] using hn
        · exact hk ⟨i, hi⟩
      · exact fun hk i => hk i
    obtain ⟨E, hE, hcover⟩ :=
      exists_finite_affine_lattice_cover_on_affineCell_of_vanishingQuadraticLowerCount
        coeff z w hz hw (fun i : I => u i) (fun i : I => c i) (fun i => i.property)
        L hL y A X T (fun k hk => hcoeff k (hcell ▸ hk)) hX hcount
    exact ⟨E, hE, fun k hk => hcover k (hcell.symm ▸ hk)⟩

end
end MeyerGeneralProblem
