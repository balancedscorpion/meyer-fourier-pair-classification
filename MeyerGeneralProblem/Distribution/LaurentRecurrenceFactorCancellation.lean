module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator
public import MeyerGeneralProblem.Cardinal.Strong.LaurentArrayAlgebraAction

@[expose] public section

/-!
# Cancelling a common factor in the two half-line recurrences

For a locally finite array each half-line recurrence can be cancelled
using extremal uniqueness. The two cuts then give the reduced
homogeneous recurrence on the complete array.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G : Type*} [AddCommGroup G]

private theorem FrequencyLocallyFinite.laurentConvolution {L : G →+ ℝ} {u : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (p : G →₀ ℂ) :
    FrequencyLocallyFinite L (annihilatorArrayConvolution p u) := by
  intro a b
  apply (p.support.finite_toSet.biUnion (fun m _ =>
    (hu (a - L m) (b - L m)).image (fun k => k + m))).subset
  intro n hn
  obtain ⟨m, hm, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn.1
  refine mem_biUnion hm ⟨n - m, ⟨(mul_ne_zero_iff.mp hx).2, ?_⟩, sub_add_cancel n m⟩
  simpa only [map_sub, mem_Icc, sub_le_sub_iff_right] using hn.2

private theorem FrequencyLocallyFinite.laurentCoefficients (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G) :
    FrequencyLocallyFinite L p.coeff := by
  intro a b
  exact p.coeff.support.finite_toSet.subset fun x hx => Finsupp.mem_support_iff.mpr hx.1

private theorem laurentConvolution_bounded_below
    (L : G →+ ℝ) (p : G →₀ ℂ) (u : G → ℂ) (a b : ℝ)
    (hp : ∀ m ∈ p.support, a ≤ L m) (hu : ∀ n, u n ≠ 0 → b ≤ L n) :
    ∀ n, annihilatorArrayConvolution p u n ≠ 0 → a + b ≤ L n := by
  intro n hn
  obtain ⟨m, hm, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have h := add_le_add (hp m hm) (hu (n - m) (mul_ne_zero_iff.mp hx).2)
  rwa [map_sub, add_sub_cancel] at h

private theorem laurentConvolution_bounded_above
    (L : G →+ ℝ) (p : G →₀ ℂ) (u : G → ℂ) (a b : ℝ)
    (hp : ∀ m ∈ p.support, L m ≤ a) (hu : ∀ n, u n ≠ 0 → L n ≤ b) :
    ∀ n, annihilatorArrayConvolution p u n ≠ 0 → L n ≤ a + b := by
  intro n hn
  obtain ⟨m, hm, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have h := add_le_add (hp m hm) (hu (n - m) (mul_ne_zero_iff.mp hx).2)
  rwa [map_sub, add_sub_cancel] at h

private theorem laurentCoefficients_bounded (L : G →+ ℝ) (p : G →₀ ℂ) :
    ∃ a b : ℝ, ∀ m, p m ≠ 0 → a ≤ L m ∧ L m ≤ b := by
  have hf : (L '' (p.support : Set G)).Finite := p.support.finite_toSet.image L
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  exact ⟨a, b, fun m hm =>
    ⟨ha ⟨m, Finsupp.mem_support_iff.mpr hm, rfl⟩, hb ⟨m, Finsupp.mem_support_iff.mpr hm, rfl⟩⟩⟩

/-- When the same Laurent factor divides the denominator and the actual
cut numerator, cancellation preserves the homogeneous recurrence and
identifies the actual reduced cut numerator coefficientwise. -/
theorem laurentRecurrence_cancel_common_factor
    (L : G →+ ℝ) (hL : Function.Injective L) (d g Q : AddMonoidAlgebra ℂ G)
    (hd : d.coeff ≠ 0) (u : G → ℂ) (hu : FrequencyLocallyFinite L u) (s : ℝ)
    (hrec : ∀ n, annihilatorArrayConvolution (d * g).coeff u n = 0)
    (hcut : cutArrayNumerator L (d * g).coeff s u = (fun n => (d * Q).coeff n)) :
    (∀ n, annihilatorArrayConvolution g.coeff u n = 0) ∧
      cutArrayNumerator L g.coeff s u = (fun n => Q.coeff n) := by
  obtain ⟨lo, hi, hlo, hhi, _, hmin, hmax⟩ := finiteAnnihilator_extrema L hL d.coeff hd
  obtain ⟨a, b, hab⟩ := laurentCoefficients_bounded L g.coeff
  obtain ⟨c, e, hce⟩ := laurentCoefficients_bounded L Q.coeff
  let up := arrayPositiveCut L s u
  let un := arrayNegativeCut L s u
  let gp := annihilatorArrayConvolution g.coeff up
  let gn := annihilatorArrayConvolution g.coeff un
  let q := (fun n => Q.coeff n)
  have hgpfin : FrequencyLocallyFinite L gp := (hu.positiveCut s).laurentConvolution _
  have hgnfin : FrequencyLocallyFinite L gn := (hu.negativeCut s).laurentConvolution _
  have hqfin : FrequencyLocallyFinite L q := FrequencyLocallyFinite.laurentCoefficients L Q
  have hnegqfin : FrequencyLocallyFinite L (-q) := by
    intro x y
    simpa only [Pi.neg_apply, neg_ne_zero] using hqfin x y
  have hgpbound : ∀ n, gp n ≠ 0 → a + s ≤ L n := by
    apply laurentConvolution_bounded_below L g.coeff up a s
      (fun m hm => (hab m (Finsupp.mem_support_iff.mp hm)).1)
    intro n hn
    by_contra hh
    exact hn (ite_eq_right hh)
  have hgnbound : ∀ n, gn n ≠ 0 → L n ≤ b + s := by
    apply laurentConvolution_bounded_above L g.coeff un b s
      (fun m hm => (hab m (Finsupp.mem_support_iff.mp hm)).2)
    intro n hn
    by_contra hh
    exact hn (ite_eq_right (fun h => hh h.le))
  have hpos : gp = q := by
    apply annihilatorArray_solution_unique_below L d.coeff lo hlo hmin gp q hgpfin hqfin
    · refine ⟨min (a + s) c, fun n hn => ?_⟩
      by_cases hg : gp n = 0
      · have hq : q n ≠ 0 := fun h => hn (by simp [Pi.sub_apply, hg, h])
        exact (min_le_right _ _).trans (hce n hq).1
      · exact (min_le_left _ _).trans (hgpbound n hg)
    · intro n
      change annihilatorArrayConvolution d.coeff (annihilatorArrayConvolution g.coeff up) n =
        annihilatorArrayConvolution d.coeff (fun k => Q.coeff k) n
      rw [← annihilatorArrayConvolution_mul d g up n,
        annihilatorArrayConvolution_finite d Q n]
      exact congrFun hcut n
  have hneg : gn = -q := by
    apply sub_eq_zero.mp
    apply annihilatorArray_eq_zero_of_bounded_above L d.coeff hi hhi hmax
      (gn - -q) (hgnfin.sub hnegqfin)
    · refine ⟨max (b + s) e, fun n hn => ?_⟩
      by_cases hg : gn n = 0
      · have hq : q n ≠ 0 := fun h => hn (by simp [Pi.sub_apply, hg, h])
        exact (hce n hq).2.trans (le_max_right _ _)
      · exact (hgnbound n hg).trans (le_max_left _ _)
    · intro n
      have hh := congrFun hcut n
      rw [cutArrayNumerator_eq_negative L (d * g).coeff s u hrec] at hh
      have hnegq : annihilatorArrayConvolution d.coeff (-q) n = -(d * Q).coeff n := by
        rw [← annihilatorArrayConvolution_finite d Q n]
        simp only [annihilatorArrayConvolution, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, q]
      rw [annihilatorArrayConvolution_sub, hnegq]
      change annihilatorArrayConvolution d.coeff (annihilatorArrayConvolution g.coeff un) n -
        -(d * Q).coeff n = 0
      rw [← annihilatorArrayConvolution_mul d g un n]
      exact sub_eq_zero.mpr (neg_eq_iff_eq_neg.mp hh)
  refine ⟨fun n => ?_, hpos⟩
  rw [← arrayCuts_add L s u, annihilatorArrayConvolution_add]
  change gp n + gn n = 0
  rw [hpos, hneg, Pi.neg_apply, add_neg_cancel]

end

end MeyerGeneralProblem
