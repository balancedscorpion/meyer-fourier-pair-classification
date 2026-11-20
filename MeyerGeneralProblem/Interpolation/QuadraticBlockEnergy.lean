module

public import MeyerGeneralProblem.Interpolation.QuadraticDerivativeBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Physical energy of an exterior quadratic block

The actual support of `ψ_b(x²) h(x²)` has physical length of order
`B / sqrt(bB)` on the two rays together. Combining this geometric fact
with the genuine quadratic derivative bounds gives a uniform local energy
estimate. No global data summability or interpolation property is assumed.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

/-- The two-ray physical enclosure of one enlarged positive square block. -/
def quadraticBlockDomain (B : ℝ) (b : ℕ) : Set ℝ :=
  (fun x : ℝ => x ^ 2) ⁻¹'
    Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8)

/-- On every exterior block the square coordinate lies between one and
twice its block base. These bounds include both physical ray signs. -/
theorem quadraticBlockDomain_bounds {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b)
    {x : ℝ} (hx : x ∈ quadraticBlockDomain B b) :
    1 ≤ |x| ∧ x ^ 2 ≤ 2 * ((b : ℝ) * B) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have ht : 2 * B ≤ (b : ℝ) * B := mul_le_mul_of_nonneg_right hb' (by linarith)
  change (b : ℝ) * B - B / 8 ≤ x ^ 2 ∧ x ^ 2 ≤ ((b : ℝ) + 1) * B + B / 8 at hx
  constructor
  · have hs : 1 ≤ x ^ 2 := by nlinarith
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]
  · nlinarith [hx.2]

/-- Exact two-interval description of the physical support enclosure. -/
theorem quadraticBlockDomain_eq_intervals {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b) :
    quadraticBlockDomain B b =
      Icc (-Real.sqrt (((b : ℝ) + 1) * B + B / 8))
          (-Real.sqrt ((b : ℝ) * B - B / 8)) ∪
      Icc (Real.sqrt ((b : ℝ) * B - B / 8))
          (Real.sqrt (((b : ℝ) + 1) * B + B / 8)) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have ht : 2 * B ≤ (b : ℝ) * B := mul_le_mul_of_nonneg_right hb' (by linarith)
  have hL : 0 ≤ (b : ℝ) * B - B / 8 := by nlinarith
  have hU : 0 ≤ ((b : ℝ) + 1) * B + B / 8 := by positivity
  have hLs := Real.sq_sqrt hL
  have hUs := Real.sq_sqrt hU
  have hLn := Real.sqrt_nonneg ((b : ℝ) * B - B / 8)
  have hUn := Real.sqrt_nonneg (((b : ℝ) + 1) * B + B / 8)
  ext x
  simp only [quadraticBlockDomain, mem_preimage, mem_Icc, mem_union]
  constructor
  · intro hx
    by_cases hxsign : 0 ≤ x
    · right
      constructor <;> nlinarith
    · left
      constructor <;> nlinarith
  · rintro (hx | hx) <;> constructor <;> nlinarith

/-- The physical block enclosure is compact, independently of the function. -/
theorem isCompact_quadraticBlockDomain {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b) :
    IsCompact (quadraticBlockDomain B b) := by
  rw [quadraticBlockDomain_eq_intervals hB hb]
  exact isCompact_Icc.union isCompact_Icc

/-- The total physical length of the enlarged block on both rays is at
most `3B / sqrt(bB)`. The factor two for the two rays is included. -/
theorem volume_real_quadraticBlockDomain_le {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b) :
    volume.real (quadraticBlockDomain B b) ≤ 3 * B / Real.sqrt ((b : ℝ) * B) := by
  let L : ℝ := (b : ℝ) * B - B / 8
  let U : ℝ := ((b : ℝ) + 1) * B + B / 8
  let t : ℝ := (b : ℝ) * B
  have hBpos : 0 < B := by linarith
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have ht : 0 < t := by dsimp [t]; positivity
  have hL : 0 ≤ L := by
    have h := mul_le_mul_of_nonneg_right hb' hBpos.le
    dsimp [L]
    nlinarith
  have hLU : L ≤ U := by dsimp [L, U]; nlinarith
  have htU : t ≤ U := by dsimp [t, U]; nlinarith
  have hU : 0 ≤ U := hL.trans hLU
  have hdiff : 0 ≤ Real.sqrt U - Real.sqrt L := sub_nonneg.mpr (Real.sqrt_le_sqrt hLU)
  have hden : Real.sqrt t ≤ Real.sqrt U + Real.sqrt L :=
    (Real.sqrt_le_sqrt htU).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hprod : (Real.sqrt U - Real.sqrt L) * (Real.sqrt U + Real.sqrt L) = U - L := by
    nlinarith [Real.sq_sqrt hU, Real.sq_sqrt hL]
  have hlength : 2 * (Real.sqrt U - Real.sqrt L) ≤ 3 * B / Real.sqrt t := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr ht)).mpr
    have h := mul_le_mul_of_nonneg_left hden hdiff
    rw [hprod] at h
    dsimp [U, L] at h
    nlinarith
  rw [quadraticBlockDomain_eq_intervals hB hb]
  calc
    _ ≤ volume.real (Icc (-Real.sqrt U) (-Real.sqrt L)) +
        volume.real (Icc (Real.sqrt L) (Real.sqrt U)) := measureReal_union_le _ _
    _ = 2 * (Real.sqrt U - Real.sqrt L) := by
      rw [Real.volume_real_Icc, Real.volume_real_Icc]
      have heq : -Real.sqrt L - -Real.sqrt U = Real.sqrt U - Real.sqrt L := by ring
      rw [heq, max_eq_left hdiff]
      ring
    _ ≤ _ := hlength

/-- The weight on the actual physical support is bounded by the block
base to the same order, with a constant depending only on the order. -/
theorem pow_abs_le_quadraticBlock_weight {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b)
    {x : ℝ} (hx : x ∈ quadraticBlockDomain B b) (k : ℕ) :
    |x| ^ (2 * k) ≤ (2 : ℝ) ^ k * ((b : ℝ) * B) ^ k := by
  rw [pow_mul, sq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (sq_nonneg x) (quadraticBlockDomain_bounds hB hb hx).2 k

/-- Every actual derivative of an exterior physical block piece has
compact support, even before any local derivative bound is imposed. -/
theorem hasCompactSupport_iteratedDeriv_quadraticBlockPiece
    {B : ℝ} (hB : 1 ≤ B) {b : ℕ} (hb : 2 ≤ b) (p : ℝ → ℂ) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j (quadraticBlockPiece B b p)) := by
  apply HasCompactSupport.intro (isCompact_quadraticBlockDomain hB hb)
  intro x hx
  by_contra h
  exact hx (tsupport_iteratedDeriv_quadraticBlockPiece_subset (by linarith) b j p (subset_closure h))

/-- Actual local physical weighted and derivative energies have the
retained block scaling `B * (bB)^(k-1/2)`. The constant depends only on k,
is chosen before B, b and the local function, and includes both ray signs.
Only the local function's genuine derivatives on the cutoff enclosure are
bounded; no polynomial coefficient or intragroup-gap estimate is assumed. -/
theorem exists_uniform_quadraticBlock_energy_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ), 2 ≤ b →
      ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ (M : ℝ), 0 ≤ M →
      (∀ s ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
        ∀ i ≤ k, ‖iteratedDeriv i h s‖ ≤ M) →
      let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
      Integrable (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
      Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
      (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤
          C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) * M ^ 2 := by
  obtain ⟨D, hD, hderiv⟩ := exists_uniform_quadraticCutoff_derivative_bound k
  let C₀ : ℝ := (1 + D ^ 2) * (2 : ℝ) ^ k
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro B hB b hb h hh M hM hbound
  let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
  have hsmooth : ContDiff ℝ ∞ f := contDiff_quadraticBlockPiece B b (hh.comp (by fun_prop))
  have hcompact := isCompact_quadraticBlockDomain hB hb
  have hzero (j : ℕ) (x : ℝ) (hx : x ∉ quadraticBlockDomain B b) : iteratedDeriv j f x = 0 := by
    by_contra hnot
    exact hx (tsupport_iteratedDeriv_quadraticBlockPiece_subset (by linarith) b j _
      (subset_closure hnot))
  have hvint : Integrable (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) := by
    apply ((continuous_abs.pow (2*k)).mul (hsmooth.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hcompact
    intro x hx
    have hz := hzero 0 x hx
    simp only [iteratedDeriv_zero] at hz
    simp [hz]
  have hdint : Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) := by
    apply ((((hsmooth.of_le (by simp)).continuous_iteratedDeriv' k).norm).pow 2).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hcompact
    intro x hx
    simp [hzero k x hx]
  refine ⟨hvint, hdint, ?_⟩
  have hpoint (x : ℝ) (hx : x ∈ quadraticBlockDomain B b) :
      |x| ^ (2*k) * ‖f x‖ ^ 2 + ‖iteratedDeriv k f x‖ ^ 2 ≤
        C₀ * ((b : ℝ) * B) ^ k * M ^ 2 := by
    have hv : ‖f x‖ ≤ M := by
      change ‖blockCutoff B b (x ^ 2) • h (x ^ 2)‖ ≤ M
      rw [norm_smul, Real.norm_of_nonneg (blockCutoff_mem_Icc B b _).1]
      calc
        _ ≤ 1 * M := mul_le_mul (blockCutoff_mem_Icc B b _).2
          (by simpa only [iteratedDeriv_zero] using hbound (x^2) hx 0 (Nat.zero_le k))
          (norm_nonneg _) zero_le_one
        _ = M := one_mul _
    have hd : ‖iteratedDeriv k f x‖ ≤ D * |x| ^ k * M :=
      hderiv B hB b h hh x M (quadraticBlockDomain_bounds hB hb hx).1 hM
        (hbound (x^2) hx)
    have hvsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hdsq : ‖iteratedDeriv k f x‖ ^ 2 ≤ D ^ 2 * |x| ^ (2*k) * M ^ 2 := by
      have hd' := pow_le_pow_left₀ (norm_nonneg _) hd 2
      simpa only [mul_pow, ← pow_mul, mul_comm k 2] using hd'
    calc
      _ ≤ |x| ^ (2*k) * M ^ 2 + D ^ 2 * |x| ^ (2*k) * M ^ 2 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hvsq (by positivity)) hdsq
      _ = (1 + D ^ 2) * |x| ^ (2*k) * M ^ 2 := by ring
      _ ≤ (1 + D ^ 2) * ((2 : ℝ) ^ k * ((b : ℝ) * B) ^ k) * M ^ 2 := by
        gcongr
        exact pow_abs_le_quadraticBlock_weight hB hb hx k
      _ = _ := by dsimp [C₀]; ring
  let Q : ℝ := C₀ * ((b : ℝ) * B) ^ k * M ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hind : Integrable ((quadraticBlockDomain B b).indicator (fun _ : ℝ => Q)) :=
    (integrable_indicator_iff hcompact.measurableSet).mpr
      (integrableOn_const hcompact.measure_lt_top.ne)
  have hmajor : (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2 + ‖iteratedDeriv k f x‖ ^ 2) ≤
      volume.real (quadraticBlockDomain B b) * Q := by
    have heq : (∫ x : ℝ, (quadraticBlockDomain B b).indicator (fun _ : ℝ => Q) x) =
        volume.real (quadraticBlockDomain B b) * Q := by
      simpa only [smul_eq_mul] using integral_indicator_const Q hcompact.measurableSet
    rw [← heq]
    apply integral_mono (hvint.add hdint) hind
    intro x
    by_cases hx : x ∈ quadraticBlockDomain B b
    · simpa only [indicator_of_mem hx, Pi.add_apply, Q] using hpoint x hx
    · have hz := hzero 0 x hx
      simp only [iteratedDeriv_zero] at hz
      simp [indicator_of_notMem hx, hz, hzero k x hx]
  have ht : 0 < (b : ℝ) * B := by
    have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  rw [← integral_add hvint hdint]
  apply hmajor.trans
  calc
    _ ≤ (3 * B / Real.sqrt ((b : ℝ) * B)) * Q :=
      mul_le_mul_of_nonneg_right (volume_real_quadraticBlockDomain_le hB hb) hQ
    _ = _ := by
      rw [Real.rpow_sub ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      dsimp [Q]
      ring

/-- Extended-valued local energy form for direct use with the actual
overlap/Tonelli theorem. Finiteness is a conclusion of the local derivative
bounds, with the same physical block exponent and both rays included. -/
theorem exists_uniform_quadraticBlock_lintegral_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ), 2 ≤ b →
      ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ (M : ℝ), 0 ≤ M →
      (∀ s ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
        ∀ i ≤ k, ‖iteratedDeriv i h s‖ ≤ M) →
      let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
      (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*k)) * ENNReal.ofReal (‖f x‖ ^ 2)) +
        (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k f x‖ ^ 2)) ≤
          ENNReal.ofReal (C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) * M ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_quadraticBlock_energy_bound k
  refine ⟨C, hC, ?_⟩
  intro B hB b hb h hh M hM hlocal
  obtain ⟨hvint, hdint, henergy⟩ := hbound B hB b hb h hh M hM hlocal
  let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
  have hvnonneg (x : ℝ) : 0 ≤ |x| ^ (2*k) * ‖f x‖ ^ 2 := by positivity
  have hdnonneg (x : ℝ) : 0 ≤ ‖iteratedDeriv k f x‖ ^ 2 := sq_nonneg _
  have heqv := ofReal_integral_eq_lintegral_ofReal hvint (Filter.Eventually.of_forall hvnonneg)
  have heqd := ofReal_integral_eq_lintegral_ofReal hdint (Filter.Eventually.of_forall hdnonneg)
  have heqmul : (fun x : ℝ => ENNReal.ofReal (|x| ^ (2*k)) * ENNReal.ofReal (‖f x‖ ^ 2)) =
      fun x => ENNReal.ofReal (|x| ^ (2*k) * ‖f x‖ ^ 2) := by
    funext x
    exact (ENNReal.ofReal_mul (by positivity : 0 ≤ |x| ^ (2*k))).symm
  change (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*k)) * ENNReal.ofReal (‖f x‖ ^ 2)) +
    (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k f x‖ ^ 2)) ≤ _
  rw [heqmul, ← heqv, ← heqd,
    ← ENNReal.ofReal_add (integral_nonneg hvnonneg) (integral_nonneg hdnonneg)]
  exact ENNReal.ofReal_le_ofReal henergy

end

end MeyerGeneralProblem
