module

public import MeyerGeneralProblem.Distribution.EscapingCombProduct

@[expose] public section

/-!
# Actual isolation coefficients of the escaping integral

An isolation test on any common locally finite carrier keeps precisely
the indices landing on the chosen physical atom. This transports the
genuine distributions to the coefficient calculation on residue cells.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap BigOperators

private theorem isolationSchwartz_eq_indicator (U : LocallyFiniteCarrier) (x : U.subtype)
    (y : ℝ) (hy : y ∈ U.carrier) :
    U.isolationSchwartz x y = (if y = (x : ℝ) then 1 else 0) := by
  by_cases h : y = (x : ℝ)
  · rw [h, LocallyFiniteCarrier.isolationSchwartz_self, ite_eq_left rfl]
  · rw [U.isolationSchwartz_of_mem_of_ne x hy h, ite_eq_right h]

/-- The actual isolation coefficient is the sum of all outgoing indices
at the chosen point, with the original phase and sign of each index. -/
theorem escapingCombIntegral_isolation_apply (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) (U : LocallyFiniteCarrier)
    (hsub : (escapingCombIntegralCarrier q.origin a w ha hw).carrier ⊆ U.carrier)
    (x : U.subtype) :
    let ω := combModulationCharacter (-w) s
    escapingCombIntegral q a w ha hw s (U.isolationSchwartz x) =
      (-ω⁻¹) * (∑' p : ℕ × ℕ, if q.origin + quadrantNode 1 a w p = (x : ℝ)
        then q.weight a (Int.ofNat p.1) * (ω⁻¹) ^ p.2 else 0) +
      (∑' p : ℕ × ℕ, if q.origin - a - w + quadrantNode (-1) a w p = (x : ℝ)
        then q.weight a (Int.negSucc p.1) * ω ^ p.2 else 0) := by
  have hp (p : ℕ × ℕ) : q.origin + quadrantNode 1 a w p ∈ U.carrier :=
    hsub (Or.inl ⟨_, ⟨p, rfl⟩, rfl⟩)
  have hn (p : ℕ × ℕ) : q.origin - a - w + quadrantNode (-1) a w p ∈ U.carrier :=
    hsub (Or.inr ⟨_, ⟨p, rfl⟩, rfl⟩)
  dsimp only
  rw [escapingCombIntegral_apply]
  simp_rw [isolationSchwartz_eq_indicator U x _ (hp _), isolationSchwartz_eq_indicator U x _ (hn _),
    mul_ite, mul_one, mul_zero]

/-- A single coordinate image in an injective quadrant contributes its
actual weight to the common isolation test. Off the quadrant every
summand of this isolation test is zero. -/
theorem tsum_isolationSchwartz_indexed_eq_of_injective {ι : Type*}
    (U : LocallyFiniteCarrier) (x : U.subtype) (y : ι → ℝ)
    (hy : ∀ i, y i ∈ U.carrier) (hinj : Function.Injective y) (b : ι → ℂ) (i : ι)
    (hi : y i = (x : ℝ)) :
    (∑' j, b j * U.isolationSchwartz x (y j)) = b i := by
  rw [tsum_eq_single i]
  · rw [hi, LocallyFiniteCarrier.isolationSchwartz_self, mul_one]
  · intro j hj
    have hne : y j ≠ (x : ℝ) := fun h => hj (hinj (h.trans hi.symm))
    rw [U.isolationSchwartz_of_mem_of_ne x (hy j) hne, mul_zero]

theorem tsum_isolationSchwartz_indexed_eq_zero_off_image {ι : Type*}
    (U : LocallyFiniteCarrier) (x : U.subtype) (y : ι → ℝ)
    (hy : ∀ i, y i ∈ U.carrier) (b : ι → ℂ)
    (hx : ∀ i, y i ≠ (x : ℝ)) :
    (∑' j, b j * U.isolationSchwartz x (y j)) = 0 := by
  have h (j : ι) : U.isolationSchwartz x (y j) = 0 :=
    U.isolationSchwartz_of_mem_of_ne x (hy j) (hx j)
  simp only [h, mul_zero, tsum_zero]

end
end MeyerGeneralProblem
