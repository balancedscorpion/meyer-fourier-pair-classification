module

public import MeyerGeneralProblem.Carrier.EventualGapCounts
public import MeyerGeneralProblem.Sampling.BernsteinZeroDensity

@[expose] public section

/-!
# Actual moving open-window counts from eventual gaps

A single finite selection contains exactly the eventual sequence nodes in the
outer open window, with the center erased. The endpoint loss and the possible
center loss are absorbed by a fixed strict density slack. Neither the initial
sequence segment nor the eventual-gap index changes that density.
-/

noncomputable section

open Set Filter
open scoped BigOperators

namespace MeyerGeneralProblem

/-- Eventual adjacent gap bounds construct the actual finite moving selection.
The fixed inner cutoff absorbs both the open-endpoint and center-erasure losses.
The outer radius is explicitly at least that cutoff, so the count interval is
nonempty. No radial-count or finite-selection certificate is assumed. -/
theorem exists_movingOpenZeroFinset_count_ge_of_eventual_gap
    {z : ℕ → ℝ} (hzmono : StrictMono z) (hztop : Tendsto z atTop atTop)
    {ell d s : ℝ} (hell : 0 < ell) (hd0 : 0 < d) (hdell : d < ell⁻¹)
    (hs0 : 0 < s) (hs1 : s < 1) (N₀ : ℕ)
    (hgap : ∀ n ≥ N₀, z (n + 1) - z n ≤ ell) :
    ∃ X₀ > 0, ∀ x ≥ X₀, ∃ Z : Finset ℝ,
      (ell⁻¹ - d)⁻¹ ≤ s * x ∧
      (∀ y, y ∈ Z ↔ ∃ n ≥ N₀,
        y = z n ∧ |y - x| < s * x ∧ y ≠ x) ∧
      ∀ t ∈ Icc ((ell⁻¹ - d)⁻¹) (s * x),
        2 * d * t ≤ ∑ y ∈ Z, if |y - x| < t then (1 : ℝ) else 0 := by
  classical
  let r₀ : ℝ := (ell⁻¹ - d)⁻¹
  have hδ : 0 < ell⁻¹ - d := sub_pos.mpr hdell
  have hr₀ : 0 < r₀ := inv_pos.mpr hδ
  let X₀ : ℝ := max 1 (max (r₀ / s) ((z N₀ + 1) / (1 - s)))
  have hX₀ : 0 < X₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx
  have hxr : r₀ / s ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxz : (z N₀ + 1) / (1 - s) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hrR : r₀ ≤ s * x := by
    have := (div_le_iff₀ hs0).mp hxr
    nlinarith
  have hstart : z N₀ < x - s * x := by
    have := (div_le_iff₀ (sub_pos.mpr hs1)).mp hxz
    nlinarith
  let I : ℝ → Finset ℕ := fun t =>
    (finite_indices_in_Ioo_of_strictMono_tendsto hzmono hztop (x - t) (x + t)).toFinset
  have hI (t : ℝ) (n : ℕ) : n ∈ I t ↔ |z n - x| < t := by
    simp only [I, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, abs_lt]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  let Z : Finset ℝ := ((I (s * x)).image z).erase x
  have hZ (y : ℝ) : y ∈ Z ↔
      ∃ n ≥ N₀, y = z n ∧ |y - x| < s * x ∧ y ≠ x := by
    constructor
    · intro hy
      rcases Finset.mem_erase.mp hy with ⟨hne, hy⟩
      rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
      have hinner := (hI _ _).mp hn
      have hzn : z N₀ < z n := by
        have := (abs_lt.mp hinner).1
        linarith
      exact ⟨n, (hzmono.lt_iff_lt.mp hzn).le, rfl, hinner, hne⟩
    · rintro ⟨n, _, rfl, hn, hne⟩
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image.mpr ⟨n, (hI _ _).mpr hn, rfl⟩⟩
  refine ⟨Z, hrR, hZ, ?_⟩
  intro t ht
  have htpos : 0 < t := hr₀.trans_le ht.1
  have hfilter : Z.filter (fun y => |y - x| < t) = ((I t).image z).erase x := by
    ext y
    simp only [Z, Finset.mem_filter, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨⟨hne, n, hn, rfl⟩, hyt⟩
      exact ⟨hne, n, (hI _ _).mpr hyt, rfl⟩
    · rintro ⟨hne, n, hn, rfl⟩
      have hyt := (hI _ _).mp hn
      exact ⟨⟨hne, n, (hI _ _).mpr (hyt.trans_le ht.2), rfl⟩, hyt⟩
  have hsum : (∑ y ∈ Z, if |y - x| < t then (1 : ℝ) else 0) =
      ((((I t).image z).erase x).card : ℝ) := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hcard : (I t).card ≤ (((I t).image z).erase x).card + 1 := by
    have hi : ((I t).image z).card = (I t).card :=
      Finset.card_image_of_injective _ hzmono.injective
    have he := Finset.pred_card_le_card_erase (s := (I t).image z) (a := x)
    omega
  have hcardR : ((I t).card : ℝ) ≤ ((((I t).image z).erase x).card : ℝ) + 1 := by
    exact_mod_cast hcard
  have hinterval := openInterval_count_ge_of_eventual_gap hzmono hztop hell N₀ hgap
    (show z N₀ ≤ x - t by linarith [ht.2])
    (show x - t < x + t by linarith)
  have hncard : {n : ℕ | x - t < z n ∧ z n < x + t}.ncard = (I t).card := by
    exact Set.ncard_eq_toFinset_card _
      (finite_indices_in_Ioo_of_strictMono_tendsto hzmono hztop (x - t) (x + t))
  rw [hncard] at hinterval
  have hlength : 2 * t ≤ ell * (((((I t).image z).erase x).card : ℝ) + 2) := by
    nlinarith
  have hinv : ell * ell⁻¹ = 1 := mul_inv_cancel₀ hell.ne'
  have hdivide := mul_le_mul_of_nonneg_left hlength (hd0.trans hdell).le
  have hslack : 1 ≤ (ell⁻¹ - d) * t := by
    exact (inv_le_iff_one_le_mul₀' hδ).mp ht.1
  rw [hsum]
  nlinarith

/-- Direct application of the existing finite radial-count integral to the
actual eventual-gap selection. Center erasure proves the zero-multiplicity
condition after translation. This is only a logarithmic-sum bound, not a sector
growth, product-decay, or uniqueness theorem. -/
theorem exists_movingOpenZeroFinset_log_sum_ge_of_eventual_gap
    {z : ℕ → ℝ} (hzmono : StrictMono z) (hztop : Tendsto z atTop atTop)
    {ell d s : ℝ} (hell : 0 < ell) (hd0 : 0 < d) (hdell : d < ell⁻¹)
    (hs0 : 0 < s) (hs1 : s < 1) (N₀ : ℕ)
    (hgap : ∀ n ≥ N₀, z (n + 1) - z n ≤ ell) :
    ∃ X₀ > 0, ∀ x ≥ X₀, ∃ Z : Finset ℝ,
      (ell⁻¹ - d)⁻¹ ≤ s * x ∧
      (∀ y, y ∈ Z ↔ ∃ n ≥ N₀,
        y = z n ∧ |y - x| < s * x ∧ y ≠ x) ∧
      2 * d * (s * x - (ell⁻¹ - d)⁻¹) ≤
        ∑ y ∈ Z, Real.log (s * x / |y - x|) := by
  classical
  obtain ⟨X₀, hX₀, hselect⟩ :=
    exists_movingOpenZeroFinset_count_ge_of_eventual_gap hzmono hztop
      hell hd0 hdell hs0 hs1 N₀ hgap
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx
  obtain ⟨Z, hrR, hZ, hcounts⟩ := hselect x hx
  let translate : ℝ → ℂ := fun y => ((y - x : ℝ) : ℂ)
  have hinj : Function.Injective translate := by
    intro y w h
    have : y - x = w - x := Complex.ofReal_injective h
    linarith
  let Zc := Z.image translate
  have hnodes : ∀ w ∈ Zc, ‖w‖ ≤ s * x := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨n, hn, heq, hinner, hne⟩ := (hZ y).mp hy
    simpa only [translate, Complex.norm_real, Real.norm_eq_abs] using hinner.le
  have hzero : ∀ w ∈ Zc, w = 0 → (1 : ℕ) = 0 := by
    intro w hw hw0
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hne := (hZ y).mp hy
    obtain ⟨n, hn, heq, hinner, hne⟩ := hne
    have hyx : y = x := by
      have : y - x = 0 := Complex.ofReal_eq_zero.mp hw0
      linarith
    exact (hne hyx).elim
  have hcountsC : ∀ t ∈ Icc ((ell⁻¹ - d)⁻¹) (s * x),
      2 * d * t ≤ ∑ w ∈ Zc, if ‖w‖ < t then ((1 : ℕ) : ℝ) else 0 := by
    intro t ht
    rw [Finset.sum_image hinj.injOn]
    simpa only [translate, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one]
      using hcounts t ht
  have hlog := finite_log_sum_ge_of_weighted_radial_counts Zc (fun _ => 1)
    (inv_pos.mpr (sub_pos.mpr hdell)) hrR hnodes hzero hcountsC
  refine ⟨Z, hrR, hZ, ?_⟩
  rw [Finset.sum_image hinj.injOn] at hlog
  simpa only [translate, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one,
    one_mul, div_eq_mul_inv] using hlog

end MeyerGeneralProblem
