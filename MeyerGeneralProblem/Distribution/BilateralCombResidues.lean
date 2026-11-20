module

public import MeyerGeneralProblem.Distribution.BilateralCharacterModes

@[expose] public section

/-!
# Integer power sums on a full affine coset

A forward zero progression of a bilateral power sum is zero on the
whole progression. An eventual periodic support decomposition can then
be transported to the original real coset with its exact finite holes.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- The bilateral exponential sequence with its literal complex phases. -/
def integerPowerSum {ι : Type*} [Fintype ι] (c z : ι → ℂ) (n : ℤ) : ℂ :=
  ∑ i, c i * z i ^ n

/-- The number of phases bounds the required consecutive samples. -/
theorem integerPowerSum_eq_zero_of_backward_samples {ι : Type*} [Fintype ι]
    (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (hs : ∀ n : Fin (Fintype.card ι), integerPowerSum c z (-(n.val : ℤ)) = 0) :
    integerPowerSum c z = 0 := by
  classical
  let phase : List ℂ := (Finset.univ : Finset ι).toList.map (fun i => (z i)⁻¹)
  have hphase : ∀ ξ ∈ phase, ξ ≠ 0 := by
    intro ξ hξ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hξ
    exact inv_ne_zero (hz i)
  let g (i : ι) (n : ℤ) := c i * z i ^ n
  have hsum : integerPowerSum c z = ∑ i, g i := by
    funext n
    rw [Finset.sum_apply]
    rfl
  have hterm (i : ι) : translationDifferenceProduct (phase.map fun ξ => (1, ξ)) (g i) = 0 := by
    apply translationDifferenceProduct_eq_zero_of_factor _ 1 (z i)⁻¹
    · apply List.mem_map.mpr
      refine ⟨(z i)⁻¹, List.mem_map.mpr ⟨i, ?_, rfl⟩, rfl⟩
      simp
    · funext n
      change c i * z i ^ (n - 1) - (z i)⁻¹ * (c i * z i ^ n) = 0
      rw [show n - 1 = n + (-1) by ring, zpow_add₀ (hz i), zpow_neg_one]
      ring
  apply int_function_eq_zero_of_translation_product_and_samples phase hphase
  · rw [hsum, ← translationDifferenceProductLinearMap_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [translationDifferenceProductLinearMap_apply, hterm i]
  · intro n
    exact hs ⟨n.val, by simpa [phase] using n.isLt⟩

theorem integerPowerSum_eq_zero_of_nonpos {ι : Type*} [Fintype ι]
    (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (hs : ∀ n : ℕ, integerPowerSum c z (-(n : ℤ)) = 0) :
    integerPowerSum c z = 0 :=
  integerPowerSum_eq_zero_of_backward_samples c z hz (fun n => hs n.val)

theorem integerPowerSum_affine {ι : Type*} [Fintype ι]
    (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0) (a m k : ℤ) :
    integerPowerSum c z (a + m * k) =
      integerPowerSum (fun i => c i * z i ^ a) (fun i => z i ^ m) k := by
  unfold integerPowerSum
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_add₀ (hz i), zpow_mul, mul_assoc]

/-- For nonzero phases, vanishing on a full forward progression forces
vanishing on the corresponding bilateral progression. -/
theorem integerPowerSum_eq_zero_of_forward_progression {ι : Type*} [Fintype ι]
    (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0) (a m : ℤ)
    (h : ∀ n : ℕ, integerPowerSum c z (a + m * (n : ℤ)) = 0) :
    ∀ k : ℤ, integerPowerSum c z (a + m * k) = 0 := by
  let c' i := c i * z i ^ a
  let z' i := z i ^ (-m)
  have hz' (i : ι) : z' i ≠ 0 := zpow_ne_zero _ (hz i)
  have hs (n : ℕ) : integerPowerSum c' z' (-(n : ℤ)) = 0 := by
    have he := integerPowerSum_affine c z hz a (-m) (-(n : ℤ))
    rw [neg_mul_neg] at he
    exact he.symm.trans (h n)
  have hzero := integerPowerSum_eq_zero_of_nonpos c' z' hz' hs
  intro k
  have he := integerPowerSum_affine c z hz a (-m) (-k)
  rw [neg_mul_neg] at he
  exact he.trans (congrFun hzero (-k))

/-- Full residue progressions at a single positive step, with a chosen
common origin in the integer parameter. -/
def integerResidueUnion (a : ℤ) (q : ℕ) (R : Finset (Fin q)) : Set ℤ :=
  ⋃ r : R, range (fun k : ℤ => a + (r.val.val : ℤ) + k * (q : ℤ))

theorem mem_integerResidueUnion (a : ℤ) (q : ℕ) (R : Finset (Fin q)) (n : ℤ) :
    n ∈ integerResidueUnion a q R ↔
      ∃ r ∈ R, ∃ k : ℤ, a + (r.val : ℤ) + k * (q : ℤ) = n := by
  constructor
  · intro hn
    obtain ⟨r, k, hk⟩ := mem_iUnion.mp hn
    exact ⟨r.val, r.property, k, hk⟩
  · rintro ⟨r, hr, k, hk⟩
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, k, hk⟩

/-- The scalar periodic-support consequence of characteristic-zero
Skolem–Mahler–Lech for bilateral power sums with nonzero phases. -/
def BilateralPowerSumCofiniteSupport : Prop :=
  ∀ (ι : Type) [Fintype ι] (c z : ι → ℂ), (∀ i, z i ≠ 0) →
    ∃ (a : ℤ) (q : ℕ) (R : Finset (Fin q)), 0 < q ∧
      Function.support (integerPowerSum c z) ⊆ integerResidueUnion a q R ∧
      (integerResidueUnion a q R \ Function.support (integerPowerSum c z)).Finite

/-- Send a cofinite set of integer residue progressions to the actual
affine lattice, retaining the rational direction of every full coset. -/
theorem exists_lattice_cover_of_integer_residue_support
    (u : ℤ → ℂ) (a : ℤ) (q : ℕ) (R : Finset (Fin q)) (hq : 0 < q)
    (hs : Function.support u ⊆ integerResidueUnion a q R)
    (hf : (integerResidueUnion a q R \ Function.support u).Finite)
    (y d : ℝ) (hd : 0 < d) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2 ∧ rationalLineDirection p.2 = rationalLineDirection d) ∧
      (fun n : ℤ => y + (n : ℝ) * d) '' Function.support u ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ (fun n : ℤ => y + (n : ℝ) * d) '' Function.support u).Finite := by
  classical
  let point (n : ℤ) := y + (n : ℝ) * d
  let p (r : Fin q) := (point (a + (r.val : ℤ)), (q : ℝ) * d)
  let E := R.image p
  have hp : ∀ v ∈ E, 0 < v.2 ∧ rationalLineDirection v.2 = rationalLineDirection d := by
    intro v hv
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
    have hpos : 0 < (q : ℝ) * d := mul_pos (by exact_mod_cast hq) hd
    exact ⟨hpos, rationalLineDirection_eq_of_mem_ne_zero _ _ hpos.ne'
      (Submodule.mem_span_singleton.mpr ⟨(q : ℚ), by simp [p, Rat.smul_def]⟩)⟩
  have hcover : (affineLatticeUnionCarrier E).carrier = point '' integerResidueUnion a q R := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, k, hk⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨a + (r.val : ℤ) + k * (q : ℤ),
        (mem_integerResidueUnion a q R _).mpr ⟨r, hr, k, rfl⟩, ?_⟩
      rw [← hk]
      simp only [point, p]
      push_cast
      ring
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨r, hr, k, rfl⟩ := (mem_integerResidueUnion a q R n).mp hn
      refine (mem_affineLatticeUnionCarrier E _).mpr
        ⟨p r, Finset.mem_image_of_mem p hr, k, ?_⟩
      simp only [point, p]
      push_cast
      ring
  refine ⟨E, hp, ?_, ?_⟩
  · rw [hcover]
    exact Set.image_mono hs
  · rw [hcover]
    apply (hf.image point).subset
    rintro x ⟨⟨n, hn, rfl⟩, hnot⟩
    exact ⟨n, ⟨hn, fun hu => hnot ⟨n, hu, rfl⟩⟩, rfl⟩

end
end MeyerGeneralProblem
