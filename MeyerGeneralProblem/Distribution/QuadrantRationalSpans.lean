module

public import MeyerGeneralProblem.Distribution.QuadrantResidueCoordinates
public import MeyerGeneralProblem.Distribution.AffineLineCenteredCount
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Rat

@[expose] public section

/-!
# Rational spans and exceptional crossings

All escaping sources share the same outer period. A source whose other
step is outside a selected rational span can meet the selected affine
grid only on one full line with that common period.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

/-- The rational span of the two actual real steps. -/
def quadrantRationalSpan (a w : ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ ({a, w} : Set ℝ)

theorem quadrantRationalSpan_left (a w : ℝ) : a ∈ quadrantRationalSpan a w :=
  Submodule.subset_span (by simp)

theorem quadrantRationalSpan_right (a w : ℝ) : w ∈ quadrantRationalSpan a w :=
  Submodule.subset_span (by simp)

private theorem rat_smul_real (r : ℚ) (x : ℝ) : r • x = (r : ℝ) * x :=
  Rat.smul_def r x

theorem mem_quadrantRationalSpan_iff (a w x : ℝ) :
    x ∈ quadrantRationalSpan a w ↔ ∃ r t : ℚ, x = (r : ℝ) * a + (t : ℝ) * w := by
  unfold quadrantRationalSpan
  rw [Submodule.mem_span_pair]
  simp only [rat_smul_real, eq_comm]

private theorem integerPlaneMap_rat_apply (a w : ℝ) (p : ℤ × ℤ) :
    integerPlaneMap a w p = (p.1 : ℚ) • a + (p.2 : ℚ) • w := by
  simp only [integerPlaneMap_real_apply, rat_smul_real, Rat.cast_intCast]

private theorem not_rat_multiple_of_integerPlaneMap_injective (a w : ℝ)
    (h : Function.Injective (integerPlaneMap a w)) (t : ℚ) :
    a ≠ (t : ℝ) * w := by
  intro he
  let p : ℤ × ℤ := ((t.den : ℤ), -t.num)
  have hd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
  have hp : integerPlaneMap a w p = 0 := by
    rw [integerPlaneMap_real_apply, he, Rat.cast_def]
    dsimp only [p]
    push_cast
    field_simp
    ring
  have hg : p = 0 := h (hp.trans (map_zero _).symm)
  have hzero : (t.den : ℤ) = 0 := congrArg Prod.fst hg
  exact t.den_nz (by exact_mod_cast hzero)

/-- Membership of an independent second source step gives an actual
nonzero rational coordinate along the first step of the reference. -/
theorem exists_nonzero_rat_coordinate_of_quadrantRationalSpan (a b w : ℝ)
    (hainj : Function.Injective (integerPlaneMap a w)) (ha : a ∈ quadrantRationalSpan b w) :
    ∃ r t : ℚ, r ≠ 0 ∧ a = (r : ℝ) * b + (t : ℝ) * w := by
  obtain ⟨r, t, he⟩ := (mem_quadrantRationalSpan_iff b w a).mp ha
  refine ⟨r, t, ?_, he⟩
  intro hr
  exact not_rat_multiple_of_integerPlaneMap_injective a w hainj t
    (by simpa only [hr, Rat.cast_zero, zero_mul, zero_add] using he)

theorem quadrantRationalSpan_eq_of_mem (a b w : ℝ)
    (hainj : Function.Injective (integerPlaneMap a w)) (ha : a ∈ quadrantRationalSpan b w) :
    quadrantRationalSpan a w = quadrantRationalSpan b w := by
  have h₁ : quadrantRationalSpan a w ≤ quadrantRationalSpan b w := by
    apply Submodule.span_le.mpr
    exact Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr (quadrantRationalSpan_right b w)⟩
  obtain ⟨r, t, hr, he⟩ := exists_nonzero_rat_coordinate_of_quadrantRationalSpan a b w hainj ha
  let V := quadrantRationalSpan a w
  have hw : w ∈ V := quadrantRationalSpan_right a w
  have hrb : r • b ∈ V := by
    have hs := V.sub_mem (quadrantRationalSpan_left a w) (V.smul_mem t hw)
    have heq : a - t • w = r • b := by
      simp only [rat_smul_real]
      linarith
    rwa [heq] at hs
  have hb : b ∈ V := by
    have h := V.smul_mem r⁻¹ hrb
    rwa [inv_smul_smul₀ hr] at h
  exact le_antisymm h₁ (Submodule.span_le.mpr
    (Set.insert_subset_iff.mpr ⟨hb, Set.singleton_subset_iff.mpr hw⟩))

/-- Translating an additive real projection gives an affine plane
lattice, possibly dense in the real line. -/
def affineLatticePlane (y : ℝ) (L : ℤ × ℤ →+ ℝ) : Set ℝ :=
  Set.range (fun p => y + L p)

/-- The overlap between an affine grid in a selected rational span and
an outside source lies on one lattice line with the common period. -/
theorem exists_affineLatticeLine_cover_cross_span
    (V : Submodule ℚ ℝ) (L : ℤ × ℤ →+ ℝ) (hL : ∀ p, L p ∈ V)
    (y z a w : ℝ) (hw : w ∈ V) (ha : a ∉ V) :
    ∃ b : ℝ, affineLatticePlane y L ∩ affineLatticePlane z (integerPlaneMap a w) ⊆
      affineLatticeLine b w := by
  let S := affineLatticePlane y L ∩ affineLatticePlane z (integerPlaneMap a w)
  by_cases hS : S.Nonempty
  · obtain ⟨x₀, ⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩ := hS
    refine ⟨x₀, ?_⟩
    rintro x ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    have hxV : x - x₀ ∈ V := by
      have h : x - x₀ = L (p - p₀) := by rw [map_sub, ← hp, ← hp₀]; ring
      rw [h]
      exact hL _
    have he : x - x₀ = integerPlaneMap a w (q - q₀) := by
      rw [map_sub, ← hq, ← hq₀]
      ring
    let d := q - q₀
    have hdV : integerPlaneMap a w d ∈ V := he ▸ hxV
    have hd₁ : d.1 = 0 := by
      by_contra hn
      have hnq : (d.1 : ℚ) ≠ 0 := by exact_mod_cast hn
      rw [integerPlaneMap_rat_apply] at hdV
      have h := V.sub_mem hdV (V.smul_mem (d.2 : ℚ) hw)
      rw [add_sub_cancel_right] at h
      have ht := V.smul_mem ((d.1 : ℚ)⁻¹) h
      rw [inv_smul_smul₀ hnq] at ht
      exact ha ht
    refine ⟨d.2, ?_⟩
    change x - x₀ = integerPlaneMap a w d at he
    rw [integerPlaneMap_real_apply, hd₁, Int.cast_zero, zero_mul, zero_add] at he
    linarith
  · exact ⟨0, fun x hx => (hS ⟨x, hx⟩).elim⟩

end
end MeyerGeneralProblem
