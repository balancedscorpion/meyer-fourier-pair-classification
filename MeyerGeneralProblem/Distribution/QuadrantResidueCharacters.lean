module

public import MeyerGeneralProblem.Distribution.EscapingQuadrantIndexWeights

@[expose] public section

/-!
# Character weights and sign inequalities on a residue plane

The affine pullback of one outgoing quadrantal weight has a fixed
coefficient and two nonzero character values. A sign pattern of the
original index forms is a cell of integer affine inequalities.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators SchwartzMap

/-- An additive map on the integer plane is determined by the images
of its two standard coordinate vectors. -/
theorem map_integerPlane_basis {G : Type*} [AddCommGroup G] (L : ℤ × ℤ →+ G)
    (k : ℤ × ℤ) : L k = k.1 • L (1, 0) + k.2 • L (0, 1) := by
  have he : k = k.1 • ((1, 0) : ℤ × ℤ) + k.2 • ((0, 1) : ℤ × ℤ) := by
    apply Prod.ext
    · change k.1 = k.1 * 1 + k.2 * 0
      ring
    · change k.2 = k.1 * 0 + k.2 * 1
      ring
  conv_lhs => rw [he, map_add, map_zsmul, map_zsmul]

private theorem combModulationCharacter_ne_zero_for_residue (s x : ℝ) :
    combModulationCharacter s x ≠ 0 :=
  norm_pos_iff.mp (by rw [norm_combModulationCharacter]; norm_num)

/-- Pulling back the character part of the actual outgoing coefficient
through any affine integer index map gives an actual two-variable
character. The sign is handled by the index inequalities. -/
theorem exists_character_of_escapingCombWeight_affine_pullback
    (q : AffineCombTerm) (a w s : ℝ) (p₀ : ℤ × ℤ) (L : ℤ × ℤ →+ ℤ × ℤ) :
    ∃ coeff α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧ ∀ k : ℤ × ℤ,
      q.weight a (p₀ + L k).1 * combModulationCharacter (-w) s ^ (-(p₀ + L k).2 - 1) =
        coeff * α ^ k.1 * β ^ k.2 := by
  let firstPhase := combModulationCharacter q.frequency a
  let secondPhase := combModulationCharacter (-w) s
  have h₁ := combModulationCharacter_ne_zero_for_residue q.frequency a
  have h₂ := combModulationCharacter_ne_zero_for_residue (-w) s
  let u := L (1, 0)
  let v := L (0, 1)
  refine ⟨q.weight a p₀.1 * secondPhase ^ (-p₀.2 - 1),
    firstPhase ^ u.1 * secondPhase ^ (-u.2), firstPhase ^ v.1 * secondPhase ^ (-v.2),
    mul_ne_zero (zpow_ne_zero _ h₁) (zpow_ne_zero _ h₂),
    mul_ne_zero (zpow_ne_zero _ h₁) (zpow_ne_zero _ h₂), ?_⟩
  intro k
  have hL₁ : (L k).1 = u.1 * k.1 + v.1 * k.2 := by
    have he := congrArg Prod.fst (map_integerPlane_basis L k)
    change (L k).1 = k.1 * u.1 + k.2 * v.1 at he
    simpa only [mul_comm] using he
  have hL₂ : -(L k).2 = (-u.2) * k.1 + (-v.2) * k.2 := by
    have he := congrArg Prod.snd (map_integerPlane_basis L k)
    change (L k).2 = k.1 * u.2 + k.2 * v.2 at he
    linarith
  have hexp : -(p₀ + L k).2 - 1 = (-p₀.2 - 1) + (-(L k).2) := by
    rw [Prod.snd_add]
    ring
  change q.weight a (p₀ + L k).1 * secondPhase ^ (-(p₀ + L k).2 - 1) = _
  simp only [AffineCombTerm.weight_eq_zpow, Prod.fst_add, hexp, hL₁, hL₂,
    zpow_add₀ (show firstPhase ≠ 0 from h₁), zpow_add₀ (show secondPhase ≠ 0 from h₂),
    zpow_mul, mul_zpow, firstPhase, secondPhase]
  ring

/-- The sign pattern of finitely many affine integer index functions is
exactly one cell as used by the quadratic count theorem. -/
theorem exists_integerAffineCell_for_sign_pattern {ι : Type*}
    (L : ι → (ℤ × ℤ →+ ℤ)) (offset : ι → ℤ) (sign : ι → Bool) :
    ∃ u : ι → ℤ × ℤ, ∃ c : ι → ℤ, ∀ k,
      k ∈ integerAffineCell u c ↔ ∀ i, (0 ≤ offset i + L i k ↔ sign i = true) := by
  let row (i : ι) := (L i (1, 0), L i (0, 1))
  let u (i : ι) := if sign i then row i else -row i
  let c (i : ι) := if sign i then -offset i else offset i + 1
  have hrow (i : ι) (k : ℤ × ℤ) : integerPlaneForm (row i) k = L i k := by
    change L i (1, 0) * k.1 + L i (0, 1) * k.2 = L i k
    have he := map_integerPlane_basis (L i) k
    change L i k = k.1 * L i (1, 0) + k.2 * L i (0, 1) at he
    simpa only [mul_comm] using he.symm
  have hneg (i : ι) (k : ℤ × ℤ) : integerPlaneForm (-row i) k = -L i k := by
    have h := hrow i k
    change (row i).1 * k.1 + (row i).2 * k.2 = L i k at h
    change (-(row i).1) * k.1 + (-(row i).2) * k.2 = -L i k
    linarith
  refine ⟨u, c, fun k => ?_⟩
  change (∀ i, c i ≤ integerPlaneForm (u i) k) ↔ _
  apply forall_congr'
  intro i
  cases hsign : sign i <;> simp [u, c, hsign, hrow, hneg] <;> omega

/-- On one residue region where the actual source's two index signs
are fixed, a single outgoing integral has one exact planar character
coefficient. An absent source contributes the zero coefficient. -/
theorem exists_character_of_escapingCombIntegral_on_residue
    {ι : Type*} {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w)
    (i : ι) (q : AffineCombTerm) (ha : 0 < a i) (hw : 0 < w) (s x : ℝ)
    (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin (a i) w ha hw).carrier ⊆ U.carrier)
    (D : Set (ℤ × ℤ)) (sign : ℂ)
    (hSign : ∀ p, q.origin + integerPlaneMap (a i) w p = x →
      ∀ k ∈ D, escapingQuadrantSign (p + C.lift i k) = sign) :
    ∃ coeff α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧ ∀ k ∈ D,
      extendedAtomicCoefficient U (escapingCombIntegral q (a i) w ha hw s)
        (x + C.residueDirection k) = coeff * α ^ k.1 * β ^ k.2 := by
  by_cases h : ∃ p, q.origin + integerPlaneMap (a i) w p = x
  · obtain ⟨p, hp⟩ := h
    obtain ⟨coeff, α, β, ha₀, hb₀, he⟩ :=
      exists_character_of_escapingCombWeight_affine_pullback q (a i) w s p (C.lift i)
    refine ⟨sign * coeff, α, β, ha₀, hb₀, ?_⟩
    intro k hk
    rw [← (C.index_eq_add_lift i q.origin x p _ k hp).mpr rfl,
      escapingCombIntegral_extendedCoefficient_at_index q (a i) w ha hw s U hsub
        (C.location_injective i), hSign p hp k hk, he]
    ring
  · refine ⟨0, 1, 1, one_ne_zero, one_ne_zero, ?_⟩
    intro k _
    rw [escapingCombIntegral_extendedCoefficient_off_lattice q (a i) w ha hw s U hsub
      _ (fun hk => h ((C.exists_index_iff_at_origin i q.origin x k).mp hk))]
    simp

theorem extendedAtomicCoefficient_finset_sum {τ : Type*}
    (U : LocallyFiniteCarrier) (y : ℝ) (E : Finset τ) (P : τ → TemperedDistribution ℝ ℂ) :
    extendedAtomicCoefficient U (∑ j ∈ E, P j) y =
      ∑ j ∈ E, extendedAtomicCoefficient U (P j) y := by
  classical
  by_cases hm : y ∈ U.carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hm, _root_.sum_apply]
  · simp only [extendedAtomicCoefficient, dite_eq_right hm, Finset.sum_const_zero]

theorem extendedAtomicCoefficient_smul (U : LocallyFiniteCarrier) (y : ℝ)
    (c : ℂ) (V : TemperedDistribution ℝ ℂ) :
    extendedAtomicCoefficient U (c • V) y = c * extendedAtomicCoefficient U V y := by
  classical
  by_cases hm : y ∈ U.carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hm, smul_apply, smul_eq_mul]
  · simp only [extendedAtomicCoefficient, dite_eq_right hm, mul_zero]

/-- Finite addition of genuine records commutes with the original
isolation coefficient, including its zero extension. -/
theorem extendedAtomicCoefficient_add (U : LocallyFiniteCarrier) (y : ℝ)
    (T V : TemperedDistribution ℝ ℂ) :
    extendedAtomicCoefficient U (T + V) y =
      extendedAtomicCoefficient U T y + extendedAtomicCoefficient U V y := by
  classical
  by_cases hm : y ∈ U.carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hm, add_apply]
  · simp only [extendedAtomicCoefficient, dite_eq_right hm, add_zero]

/-- A source outside its full affine lattice contributes zero at the
original coefficient for the complete Lagrange integral. -/
theorem escapingCombProductIntegral_extendedCoefficient_off_lattice
    (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) (modes : List ℝ)
    (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (x : ℝ) (hx : ¬ ∃ p, q.origin + integerPlaneMap a w p = x) :
    extendedAtomicCoefficient U (escapingCombProductIntegral q a w ha hw modes) x = 0 := by
  classical
  rw [escapingCombProductIntegral, extendedAtomicCoefficient_finset_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [extendedAtomicCoefficient_smul,
    escapingCombIntegral_extendedCoefficient_off_lattice q a w ha hw s U hsub x hx,
    mul_zero]

/-- The sum of all same-span quadrant sources on a fixed residue sign
region has the exact finite planar character expression, retaining
every source and translation phase before cancellation. -/
theorem exists_planarCharacterSum_of_escapingCombProductIntegrals_on_residue
    {ι : Type*} [Fintype ι] {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w)
    (q : ι → AffineCombTerm) (ha : ∀ i, 0 < a i) (hw : 0 < w) (modes : List ℝ)
    (U : LocallyFiniteCarrier)
    (hsub : ∀ i, (escapingCombIntegralCarrier (q i).origin (a i) w (ha i) hw).carrier ⊆ U.carrier)
    (x : ℝ) (D : Set (ℤ × ℤ)) (sign : ι → ℂ)
    (hSign : ∀ i p, (q i).origin + integerPlaneMap (a i) w p = x →
      ∀ k ∈ D, escapingQuadrantSign (p + C.lift i k) = sign i) :
    ∃ coeff α β : ι × (↑modes.toFinset : Type) → ℂ, (∀ j, α j ≠ 0) ∧ (∀ j, β j ≠ 0) ∧
      ∀ k ∈ D, extendedAtomicCoefficient U
        (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes)
        (x + C.residueDirection k) = ∑ j, coeff j * α j ^ k.1 * β j ^ k.2 := by
  classical
  choose coeff α β hα hβ he using fun (j : ι × (↑modes.toFinset : Type)) =>
    exists_character_of_escapingCombIntegral_on_residue C j.1 (q j.1) (ha j.1) hw j.2 x U
      (hsub j.1) D (sign j.1) (hSign j.1)
  let weight (j : ι × (↑modes.toFinset : Type)) :=
    Lagrange.nodalWeight modes.toFinset (combModulationCharacter (-w)) j.2
  refine ⟨fun j => weight j * coeff j, α, β, hα, hβ, ?_⟩
  intro k hk
  let y := x + C.residueDirection k
  change extendedAtomicCoefficient U
    (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes) y = _
  rw [extendedAtomicCoefficient_finset_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [escapingCombProductIntegral, extendedAtomicCoefficient_finset_sum, ← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro s _
  rw [extendedAtomicCoefficient_smul, show extendedAtomicCoefficient U
    (escapingCombIntegral (q i) (a i) w (ha i) hw s) y =
      coeff (i,s) * α (i,s) ^ k.1 * β (i,s) ^ k.2 from he (i,s) k hk]
  change weight (i,s) * _ = _
  ring

/-- The actual same-span quadrant sum has a finite affine-cell cover on
every residue. The affine inequalities and the aggregate character
formula are derived from the original outgoing coordinates. -/
theorem exists_affineCells_escapingCombProductIntegrals_on_residue
    {ι : Type*} [Fintype ι] {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w)
    (q : ι → AffineCombTerm) (ha : ∀ i, 0 < a i) (hw : 0 < w) (modes : List ℝ)
    (U : LocallyFiniteCarrier)
    (hsub : ∀ i, (escapingCombIntegralCarrier (q i).origin (a i) w (ha i) hw).carrier ⊆ U.carrier)
    (x : ℝ) :
    ∃ (u : (ι × Bool → Bool) → ι × Bool → ℤ × ℤ)
      (c : (ι × Bool → Bool) → ι × Bool → ℤ),
      (∀ k, ∃ bits, k ∈ integerAffineCell (u bits) (c bits)) ∧
      ∀ bits, ∃ coeff α β : ι × (↑modes.toFinset : Type) → ℂ,
        (∀ j, α j ≠ 0) ∧ (∀ j, β j ≠ 0) ∧
        ∀ k ∈ integerAffineCell (u bits) (c bits),
          extendedAtomicCoefficient U
            (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes)
            (x + C.residueDirection k) = ∑ j, coeff j * α j ^ k.1 * β j ^ k.2 := by
  classical
  let p₀ (i : ι) : ℤ × ℤ :=
    if h : ∃ p, (q i).origin + integerPlaneMap (a i) w p = x then Classical.choose h else 0
  have hp₀ (i : ι) (p : ℤ × ℤ) (hp : (q i).origin + integerPlaneMap (a i) w p = x) :
      p = p₀ i := by
    have h : ∃ p, (q i).origin + integerPlaneMap (a i) w p = x := ⟨p, hp⟩
    dsimp only [p₀]
    rw [dite_eq_left h]
    exact C.location_injective i (add_left_cancel (hp.trans (Classical.choose_spec h).symm))
  let coordinate (b : Bool) : ℤ × ℤ →+ ℤ :=
    if b then AddMonoidHom.fst ℤ ℤ else AddMonoidHom.snd ℤ ℤ
  let F (j : ι × Bool) := (coordinate j.2).comp (C.lift j.1)
  let offset (j : ι × Bool) := coordinate j.2 (p₀ j.1)
  have hcoordinate (j : ι × Bool) (k : ℤ × ℤ) :
      offset j + F j k = coordinate j.2 (p₀ j.1 + C.lift j.1 k) :=
    ((coordinate j.2).map_add (p₀ j.1) (C.lift j.1 k)).symm
  choose u c hc using fun bits : ι × Bool → Bool =>
    exists_integerAffineCell_for_sign_pattern F offset bits
  refine ⟨u, c, ?_, ?_⟩
  · intro k
    refine ⟨fun j => decide (0 ≤ offset j + F j k), ?_⟩
    exact (hc _ k).mpr (fun j => by simp)
  · intro bits
    let sign (i : ι) : ℂ :=
      if bits (i, true) = true ∧ bits (i, false) = true then -1
      else if (¬ bits (i, true) = true) ∧ (¬ bits (i, false) = true) then 1 else 0
    apply exists_planarCharacterSum_of_escapingCombProductIntegrals_on_residue
      C q ha hw modes U hsub x (integerAffineCell (u bits) (c bits)) sign
    intro i p hp k hk
    rw [hp₀ i p hp]
    have hfirst : 0 ≤ (p₀ i + C.lift i k).1 ↔ bits (i, true) = true := by
      have h := (hc bits k).mp hk (i, true)
      rw [hcoordinate] at h
      exact h
    have hsecond : 0 ≤ (p₀ i + C.lift i k).2 ↔ bits (i, false) = true := by
      have h := (hc bits k).mp hk (i, false)
      rw [hcoordinate] at h
      exact h
    have hn₁ : (p₀ i + C.lift i k).1 < 0 ↔ ¬ bits (i, true) = true :=
      not_le.symm.trans (not_congr hfirst)
    have hn₂ : (p₀ i + C.lift i k).2 < 0 ↔ ¬ bits (i, false) = true :=
      not_le.symm.trans (not_congr hsecond)
    simp only [escapingQuadrantSign, hfirst, hsecond, hn₁, hn₂, sign]

end
end MeyerGeneralProblem
