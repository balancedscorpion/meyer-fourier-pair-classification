module

public import MeyerGeneralProblem.Distribution.LaurentEulerRecurrence
public import MeyerGeneralProblem.Distribution.LaurentRecurrenceWidth
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Sym.Card

@[expose] public section

/-!
# Counts from independent Euler twists of an original array

The degree-bounded multiset of Euler coordinates, with an identity
coordinate for padding, has the exact stars-and-bars dimension.
Its common powered recurrence yields a bound on the occupied sites
in every half-open window of the corresponding width.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

variable {G : Type*} [AddCommGroup G]

/-- An Euler monomial weights the original coefficient by the product of
its selected additive coordinates. The extra coordinate contributes one. -/
def laurentEulerMonomial {ι : Type*} {k : ℕ} (e : ι → G →+ ℂ)
    (t : Sym (Option ι) k) (u : G → ℂ) (n : G) : ℂ :=
  ((t.val.map fun o => o.elim 1 (fun i => e i n)).prod) * u n

/-- The product of the coefficient weights equals the ordered Euler action
on the array after dropping identity letters. -/
theorem laurentEulerMonomial_eq_foldr {ι : Type*} {k : ℕ} (e : ι → G →+ ℂ)
    (t : Sym (Option ι) k) (u : G → ℂ) :
    laurentEulerMonomial e t u =
      (t.val.toList.filterMap (Option.map e)).foldr laurentEulerArray u := by
  ext n
  have h (l : List (Option ι)) :
      (l.filterMap (Option.map e)).foldr laurentEulerArray u n =
        (l.map (fun o => o.elim 1 (fun i => e i n))).prod * u n := by
    induction l with
    | nil => simp
    | cons o l ih =>
      cases o <;> simp [laurentEulerArray, ih, mul_assoc]
  rw [h]
  have ht := congrArg (fun m : Multiset (Option ι) =>
    (m.map fun o => o.elim 1 (fun i => e i n)).prod) (Multiset.coe_toList t.val)
  simp only [Multiset.map_coe, Multiset.prod_coe] at ht
  rw [ht]
  rfl

/-- A list of at most k Euler operators satisfies the (k+1)-st power of
the recurrence, including when no operators are applied. -/
theorem annihilatorArrayConvolution_pow_eulers_eq_zero_of_le
    (p : AddMonoidAlgebra ℂ G) (es : List (G →+ ℂ)) (k : ℕ) (hk : es.length ≤ k)
    (u : G → ℂ) (h : annihilatorArrayConvolution p.coeff u = 0) (n : G) :
    annihilatorArrayConvolution (p ^ (k + 1)).coeff
      (es.foldr laurentEulerArray u) n = 0 := by
  rw [show k + 1 = k - es.length + (es.length + 1) by omega, pow_add,
    annihilatorArrayConvolution_mul, annihilatorArrayConvolution_pow_eulers_eq_zero p es u h,
    annihilatorArrayConvolution_zero]

/-- An independent family of all degree-at-most-k Euler monomials forces
the exact binomial count on each window of width (k+1) times the original
recurrence width. -/
theorem choose_le_occupied_eulerWindow_of_independent
    (L : G →+ ℝ) (hL : Function.Injective L) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ m ∈ p.coeff.support, L lo ≤ L m)
    (hmax : ∀ m ∈ p.coeff.support, L m ≤ L hi)
    (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : annihilatorArrayConvolution p.coeff u = 0)
    {ι : Type*} [Fintype ι] (e : ι → G →+ ℂ) (k : ℕ) (s : ℝ)
    (hind : LinearIndependent ℂ (fun t : Sym (Option ι) k => laurentEulerMonomial e t u)) :
    (Fintype.card ι + k).choose k ≤
      {n : G | u n ≠ 0 ∧ L n ∈ Ico s (s + (k + 1 : ℕ) * (L hi - L lo))}.ncard := by
  classical
  obtain ⟨hil, hle⟩ := laurentPower_lowerExtreme L hL p lo hlo hmin (k + 1)
  obtain ⟨hir, hge⟩ := laurentPower_upperExtreme L hL p hi hhi hmax (k + 1)
  have hstrictlo (n : G) (hn : n ∈ (p ^ (k + 1)).coeff.support)
      (hne : n ≠ (k + 1) • lo) : L ((k + 1) • lo) < L n :=
    lt_of_le_of_ne (hle n hn) (fun h => hne (hL h).symm)
  have hstricthi (n : G) (hn : n ∈ (p ^ (k + 1)).coeff.support)
      (hne : n ≠ (k + 1) • hi) : L n < L ((k + 1) • hi) :=
    lt_of_le_of_ne (hge n hn) (fun h => hne (hL h))
  have hcount := card_le_occupied_recurrenceWindow_of_linearIndependent
    L (p ^ (k + 1)) ((k + 1) • lo) ((k + 1) • hi)
    (hil.trans_ne (pow_ne_zero _ hlo)) (hir.trans_ne (pow_ne_zero _ hhi))
    hstrictlo hstricthi s u hu (fun t : Sym (Option ι) k => laurentEulerMonomial e t u)
    hind (by intro t n hz; simp [laurentEulerMonomial, hz]) ?_
  · have hw : L ((k + 1) • hi) - L ((k + 1) • lo) =
        (k + 1 : ℕ) * (L hi - L lo) := by
      rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_sub]
    simpa only [Sym.card_sym_eq_choose, Fintype.card_option, show
      Fintype.card ι + 1 + k - 1 = Fintype.card ι + k by omega, hw] using hcount
  · intro t n
    rw [laurentEulerMonomial_eq_foldr]
    apply annihilatorArrayConvolution_pow_eulers_eq_zero_of_le _ _ _ ?_ _ hconv
    have hl : t.val.toList.length = k := by rw [Multiset.length_toList, t.property]
    exact (List.length_filterMap_le (f := Option.map e) (l := t.val.toList)).trans_eq hl

/-- A sharp eventual quadratic lower bound follows from exact binomial
window counts in dimension at least two. The formulation allows a
quadratic liminf of positive infinity. -/
theorem eventually_quadratic_le_occupied_centeredCount
    (L : G →+ ℝ) (u : G → ℂ) (D : ℝ) (hD : 0 < D) (d : ℕ) (hd : 2 ≤ d)
    (hwindow : ∀ (k : ℕ) (s : ℝ), (d + k).choose k ≤
      {n : G | u n ≠ 0 ∧ L n ∈ Ico s (s + (k + 1 : ℕ) * D)}.ncard)
    (hu : FrequencyLocallyFinite L u) (c : ℝ) (hc : c < 2 / D ^ 2) :
    ∀ᶠ R : ℝ in atTop, c * R ^ 2 ≤
      ({n : G | u n ≠ 0 ∧ L n ∈ Icc (-R) R}.ncard : ℝ) := by
  let b := (max c 0 + 2 / D ^ 2) / 2
  have hb0 : 0 < b := by
    dsimp [b]
    have hb1 : 0 < 2 / D ^ 2 := by positivity
    linarith [le_max_right c (0 : ℝ)]
  have hcb : c ≤ b := by
    dsimp [b]
    linarith [le_max_left c (0 : ℝ), max_lt hc (show 0 < 2 / D ^ 2 by positivity)]
  have hb : b < 2 / D ^ 2 := by
    dsimp [b]
    linarith [max_lt hc (show 0 < 2 / D ^ 2 by positivity)]
  let a := Real.sqrt (2 * b)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha₂ : a ^ 2 = 2 * b := Real.sq_sqrt (by positivity)
  have hasmall : a < 2 / D := by
    have hD₂ : D ^ 2 ≠ 0 := pow_ne_zero _ hD.ne'
    have he : (2 / D) ^ 2 = 2 * (2 / D ^ 2) := by field_simp
    nlinarith [sq_nonneg (a - 2 / D), show 0 < 2 / D by positivity]
  filter_upwards [eventually_ge_atTop (max (2 / (2 / D - a)) 1)] with R hR
  have hR₁ : 1 ≤ R := (le_max_right _ _).trans hR
  have hR₀ : 0 ≤ R := by linarith
  have hlarge : 2 ≤ R * (2 / D - a) :=
    (div_le_iff₀ (sub_pos.mpr hasmall)).mp ((le_max_left _ _).trans hR)
  let M := ⌊2 * R / D⌋₊
  have hMlo : 2 * R / D < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMhi : (M : ℝ) ≤ 2 * R / D := Nat.floor_le (by positivity)
  have hm : a * R + 1 < (M : ℝ) := by
    have he : R * (2 / D - a) = 2 * R / D - a * R := by ring
    rw [he] at hlarge
    linarith
  have hM : 1 ≤ M := by
    have hpos : (0 : ℝ) < M := by linarith [mul_nonneg ha.le hR₀]
    exact_mod_cast (show 0 < (M : ℝ) from hpos)
  let k := M - 1
  have hk : k + 1 = M := Nat.sub_add_cancel hM
  have hwidth : (k + 1 : ℕ) * D ≤ 2 * R := by
    rw [hk]
    exact (le_div_iff₀ hD).mp hMhi
  have hsub : {n : G | u n ≠ 0 ∧ L n ∈ Ico (-R) (-R + (k + 1 : ℕ) * D)}
      ⊆ {n : G | u n ≠ 0 ∧ L n ∈ Icc (-R) R} := by
    intro n hn
    exact ⟨hn.1, hn.2.1, by linarith [hn.2.2]⟩
  have hw := (hwindow k (-R)).trans (Set.ncard_le_ncard hsub (hu (-R) R))
  have hcomb : (k + 2).choose 2 ≤ (d + k).choose k := by
    rw [← Nat.choose_symm_add (a := k) (b := 2)]
    exact Nat.choose_le_choose k (by omega)
  have hcN : ((k + 2).choose 2 : ℝ) ≤
      ({n : G | u n ≠ 0 ∧ L n ∈ Icc (-R) R}.ncard : ℝ) := by exact_mod_cast hcomb.trans hw
  rw [Nat.cast_choose_two] at hcN
  have he : ((k + 2 : ℕ) : ℝ) = (M : ℝ) + 1 := by exact_mod_cast (by omega : k + 2 = M + 1)
  rw [he] at hcN
  have hsq : (a * R) ^ 2 ≤ (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha.le hR₀) (by linarith) 2
  calc
    c * R ^ 2 ≤ b * R ^ 2 := mul_le_mul_of_nonneg_right hcb (sq_nonneg _)
    _ = (a * R) ^ 2 / 2 := by rw [mul_pow, ha₂]; ring
    _ ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1 - 1) / 2 := by
      nlinarith [show 0 ≤ (M : ℝ) by positivity]
    _ ≤ _ := hcN

end

end MeyerGeneralProblem
