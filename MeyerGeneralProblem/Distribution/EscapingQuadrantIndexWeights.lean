module

public import MeyerGeneralProblem.Distribution.EscapingQuadrantCoefficients
public import MeyerGeneralProblem.Distribution.QuadrantResidueCoordinates

@[expose] public section

/-!
# Escaping coefficients in the original integer coordinates

Injectivity within a source resolves both outgoing quadrants at every
site of its affine lattice, including the index axes. The two sign
conditions are the only piecewise part of its original coefficient.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap

private def forwardIndices (n : ℕ × ℕ) : ℤ × ℤ :=
  ((n.1 : ℤ), (n.2 : ℤ))

private def backwardIndices (n : ℕ × ℕ) : ℤ × ℤ :=
  (Int.negSucc n.1, Int.negSucc n.2)

private theorem forwardIndices_injective : Function.Injective forwardIndices := by
  intro p q h
  apply Prod.ext
  · exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  · exact Int.ofNat_inj.mp (congrArg Prod.snd h)

private theorem backwardIndices_injective : Function.Injective backwardIndices := by
  intro p q h
  apply Prod.ext
  · have h₁ : Int.negSucc p.1 = Int.negSucc q.1 := congrArg Prod.fst h
    exact Int.negSucc.inj h₁
  · have h₂ : Int.negSucc p.2 = Int.negSucc q.2 := congrArg Prod.snd h
    exact Int.negSucc.inj h₂

private theorem forwardNode_eq (y a w : ℝ) (n : ℕ × ℕ) :
    y + quadrantNode 1 a w n = y + integerPlaneMap a w (forwardIndices n) := by
  simp only [quadrantNode, forwardIndices, integerPlaneMap_real_apply, Int.cast_natCast,
    one_mul]
  ring

private theorem backwardNode_eq (y a w : ℝ) (n : ℕ × ℕ) :
    y - a - w + quadrantNode (-1) a w n =
      y + integerPlaneMap a w (backwardIndices n) := by
  simp only [quadrantNode, backwardIndices, integerPlaneMap_real_apply,
    Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
  ring

private theorem exists_negSucc_of_negative (k : ℤ) (hk : k < 0) :
    ∃ n : ℕ, Int.negSucc n = k := by
  cases k with
  | ofNat n => exact ((not_lt_of_ge (Int.natCast_nonneg n)) hk).elim
  | negSucc n => exact ⟨n, rfl⟩

/-- The sign of the original outgoing integral at an index. Both axes
belong to the closed forward quadrant only when both coordinates are
nonnegative. The backward quadrant is strict in both coordinates. -/
def escapingQuadrantSign (p : ℤ × ℤ) : ℂ :=
  if 0 ≤ p.1 ∧ 0 ≤ p.2 then -1 else if p.1 < 0 ∧ p.2 < 0 then 1 else 0

/-- Explicit original coefficient at any index of an injective source
lattice. Inactive quadrants and every boundary sign are accounted for. -/
theorem escapingCombIntegral_isolation_at_index (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (hinj : Function.Injective (integerPlaneMap a w))
    (x : U.subtype) (p : ℤ × ℤ) (hx : q.origin + integerPlaneMap a w p = (x : ℝ)) :
    escapingCombIntegral q a w ha hw s (U.isolationSchwartz x) =
      escapingQuadrantSign p * (q.weight a p.1 * combModulationCharacter (-w) s ^ (-p.2 - 1)) := by
  classical
  let ω := combModulationCharacter (-w) s
  let forward (n : ℕ × ℕ) := q.origin + quadrantNode 1 a w n
  let backward (n : ℕ × ℕ) := q.origin - a - w + quadrantNode (-1) a w n
  let forwardWeight (n : ℕ × ℕ) := q.weight a (Int.ofNat n.1) * (ω⁻¹) ^ n.2
  let backwardWeight (n : ℕ × ℕ) := q.weight a (Int.negSucc n.1) * ω ^ n.2
  have hmem_forward (n) : forward n ∈ U.carrier := hsub (Or.inl ⟨_, ⟨n, rfl⟩, rfl⟩)
  have hmem_backward (n) : backward n ∈ U.carrier := hsub (Or.inr ⟨_, ⟨n, rfl⟩, rfl⟩)
  have hf (n) : forward n = (x : ℝ) ↔ forwardIndices n = p := by
    change q.origin + quadrantNode 1 a w n = (x : ℝ) ↔ _
    rw [forwardNode_eq, ← hx]
    exact ⟨fun he => hinj (add_left_cancel he), fun he => by rw [he]⟩
  have hb (n) : backward n = (x : ℝ) ↔ backwardIndices n = p := by
    change q.origin - a - w + quadrantNode (-1) a w n = (x : ℝ) ↔ _
    rw [backwardNode_eq, ← hx]
    exact ⟨fun he => hinj (add_left_cancel he), fun he => by rw [he]⟩
  have hinj_forward : Function.Injective forward := by
    intro i j he
    apply forwardIndices_injective
    apply hinj
    have hi : q.origin + integerPlaneMap a w (forwardIndices i) =
        q.origin + integerPlaneMap a w (forwardIndices j) := by
      rw [← forwardNode_eq, ← forwardNode_eq]
      exact he
    exact add_left_cancel hi
  have hinj_backward : Function.Injective backward := by
    intro i j he
    apply backwardIndices_injective
    apply hinj
    have hi : q.origin + integerPlaneMap a w (backwardIndices i) =
        q.origin + integerPlaneMap a w (backwardIndices j) := by
      rw [← backwardNode_eq, ← backwardNode_eq]
      exact he
    exact add_left_cancel hi
  have forward_zero (h : ¬ (0 ≤ p.1 ∧ 0 ≤ p.2)) :
      (∑' n, forwardWeight n * U.isolationSchwartz x (forward n)) = 0 := by
    apply tsum_isolationSchwartz_indexed_eq_zero_off_image U x forward hmem_forward forwardWeight
    intro n he
    have hi := (hf n).mp he
    apply h
    rw [← hi]
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  have backward_zero (h : ¬ (p.1 < 0 ∧ p.2 < 0)) :
      (∑' n, backwardWeight n * U.isolationSchwartz x (backward n)) = 0 := by
    apply tsum_isolationSchwartz_indexed_eq_zero_off_image U x backward hmem_backward backwardWeight
    intro n he
    have hi := (hb n).mp he
    apply h
    rw [← hi]
    simp [backwardIndices]
  rw [escapingCombIntegral_apply]
  change (-ω⁻¹) * (∑' n, forwardWeight n * U.isolationSchwartz x (forward n)) +
    (∑' n, backwardWeight n * U.isolationSchwartz x (backward n)) =
      escapingQuadrantSign p * (q.weight a p.1 * ω ^ (-p.2 - 1))
  by_cases hp : 0 ≤ p.1 ∧ 0 ≤ p.2
  · have hn : ¬ (p.1 < 0 ∧ p.2 < 0) := fun h => (not_lt_of_ge hp.1) h.1
    let n : ℕ × ℕ := (p.1.toNat, p.2.toNat)
    have hidx : forwardIndices n = p :=
      Prod.ext (Int.toNat_of_nonneg hp.1) (Int.toNat_of_nonneg hp.2)
    rw [tsum_isolationSchwartz_indexed_eq_of_injective U x forward hmem_forward hinj_forward forwardWeight n ((hf n).mpr hidx),
      backward_zero hn, add_zero, escapingQuadrantSign, ite_eq_left hp]
    have hm : (n.2 : ℤ) = p.2 := congrArg Prod.snd hidx
    have hn₁ : Int.ofNat n.1 = p.1 := congrArg Prod.fst hidx
    have hpow : ω ^ (-p.2 - 1) = (ω⁻¹) ^ n.2 * ω⁻¹ := by
      rw [show -p.2 - 1 = -((n.2 + 1 : ℕ) : ℤ) by push_cast; omega,
        zpow_neg, zpow_natCast, ← inv_pow, pow_succ]
    simp only [forwardWeight, hn₁, hpow]
    ring
  · rw [forward_zero hp, mul_zero, zero_add, escapingQuadrantSign, ite_eq_right hp]
    by_cases hn : p.1 < 0 ∧ p.2 < 0
    · obtain ⟨j, hj⟩ := exists_negSucc_of_negative p.1 hn.1
      obtain ⟨k, hk⟩ := exists_negSucc_of_negative p.2 hn.2
      have hidx : backwardIndices (j, k) = p := Prod.ext hj hk
      rw [tsum_isolationSchwartz_indexed_eq_of_injective U x backward hmem_backward hinj_backward backwardWeight
        (j, k) ((hb (j, k)).mpr hidx), ite_eq_left hn, one_mul]
      have hpow : -p.2 - 1 = (k : ℤ) := by omega
      simp only [backwardWeight, hj, hpow, zpow_natCast]
    · rw [backward_zero hn, ite_eq_right hn, zero_mul]

/-- At a site outside this source's whole affine lattice the exact local
coefficient vanishes, regardless of the other sources on the carrier. -/
theorem escapingCombIntegral_isolation_off_lattice (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (x : U.subtype) (hx : ¬ ∃ p, q.origin + integerPlaneMap a w p = (x : ℝ)) :
    escapingCombIntegral q a w ha hw s (U.isolationSchwartz x) = 0 := by
  apply escapingCombIntegral_atomicOnCarrier
  intro y hy
  apply U.isolationSchwartz_of_mem_of_ne x (hsub hy)
  intro h
  subst y
  rcases hy with ⟨_, ⟨n, rfl⟩, hn⟩ | ⟨_, ⟨n, rfl⟩, hn⟩
  · exact hx ⟨forwardIndices n, (forwardNode_eq q.origin a w n).symm.trans hn⟩
  · exact hx ⟨backwardIndices n, (backwardNode_eq q.origin a w n).symm.trans hn⟩

/-- The actual modulation weight splits into its original phase at the
origin and the integer power of the character at the step. -/
theorem AffineCombTerm.weight_eq_zpow (q : AffineCombTerm) (a : ℝ) (k : ℤ) :
    q.weight a k = q.coefficient * combModulationCharacter q.frequency q.origin *
      combModulationCharacter q.frequency a ^ k := by
  rw [AffineCombTerm.weight, mul_assoc]
  congr 1
  rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp,
    combModulationCharacter_eq_exp, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The signed index law holds at every point of the affine lattice,
including the zero-extended coefficient outside the common carrier. -/
theorem escapingCombIntegral_extendedCoefficient_at_index (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (hinj : Function.Injective (integerPlaneMap a w)) (p : ℤ × ℤ) :
    extendedAtomicCoefficient U (escapingCombIntegral q a w ha hw s)
        (q.origin + integerPlaneMap a w p) =
      escapingQuadrantSign p * (q.weight a p.1 * combModulationCharacter (-w) s ^ (-p.2 - 1)) := by
  classical
  by_cases hx : q.origin + integerPlaneMap a w p ∈ U.carrier
  · rw [extendedAtomicCoefficient, dite_eq_left hx]
    exact escapingCombIntegral_isolation_at_index q a w ha hw s U hsub hinj ⟨_, hx⟩ p rfl
  · rw [extendedAtomicCoefficient, dite_eq_right hx]
    have hpos : ¬ (0 ≤ p.1 ∧ 0 ≤ p.2) := by
      intro hp
      let n : ℕ × ℕ := (p.1.toNat, p.2.toNat)
      have he : forwardIndices n = p :=
        Prod.ext (Int.toNat_of_nonneg hp.1) (Int.toNat_of_nonneg hp.2)
      apply hx
      apply hsub
      rw [← he, ← forwardNode_eq]
      exact Or.inl ⟨_, ⟨n, rfl⟩, rfl⟩
    have hneg : ¬ (p.1 < 0 ∧ p.2 < 0) := by
      intro hp
      obtain ⟨i, hi⟩ := exists_negSucc_of_negative p.1 hp.1
      obtain ⟨j, hj⟩ := exists_negSucc_of_negative p.2 hp.2
      have he : backwardIndices (i, j) = p := Prod.ext hi hj
      apply hx
      apply hsub
      rw [← he, ← backwardNode_eq]
      exact Or.inr ⟨_, ⟨(i,j), rfl⟩, rfl⟩
    simp only [escapingQuadrantSign, ite_eq_right hpos, ite_eq_right hneg, zero_mul]

/-- The zero-extended coefficient is zero off the whole affine lattice. -/
theorem escapingCombIntegral_extendedCoefficient_off_lattice (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (x : ℝ) (hx : ¬ ∃ p, q.origin + integerPlaneMap a w p = x) :
    extendedAtomicCoefficient U (escapingCombIntegral q a w ha hw s) x = 0 := by
  classical
  by_cases hm : x ∈ U.carrier
  · rw [extendedAtomicCoefficient, dite_eq_left hm]
    exact escapingCombIntegral_isolation_off_lattice q a w ha hw s U hsub ⟨x, hm⟩ hx
  · rw [extendedAtomicCoefficient, dite_eq_right hm]

end
end MeyerGeneralProblem
