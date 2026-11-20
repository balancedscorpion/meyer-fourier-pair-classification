module

public import MeyerGeneralProblem.Sampling.KNSSectorLogGeometry
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# Boundary-ray propagation in a Cartesian sector

Independent holomorphic exponential twists reduce the upper and lower
half-sectors to the horizontal-strip Phragmén–Lindelöf theorem. The actual
global exponential bound supplies its double-exponential growth hypothesis.
No symmetry between the values in the two half-sectors is required.
-/

open Set Function Filter Asymptotics Complex
open scoped Topology

namespace MeyerGeneralProblem

/-- The signed holomorphic twist after the exponential change of variable. -/
private noncomputable def sectorStripTwist (t : ℝ) (H : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I * Complex.exp ζ) * H (Complex.exp ζ)

/-- Exact norm of the signed twist, with no sign restriction on the height. -/
private theorem sectorStripTwist_norm (t : ℝ) (H : ℂ → ℂ) (ζ : ℂ) :
    ‖sectorStripTwist t H ζ‖ =
      Real.exp (-t * (Complex.exp ζ).im) * ‖H (Complex.exp ζ)‖ := by
  simp [sectorStripTwist, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The twist is bounded by the boundary constant exactly when the original
function satisfies the corresponding signed exponential estimate. -/
private theorem sectorStripTwist_norm_le_iff (t M : ℝ) (H : ℂ → ℂ) (ζ : ℂ) :
    ‖sectorStripTwist t H ζ‖ ≤ M ↔
      ‖H (Complex.exp ζ)‖ ≤ M * Real.exp (t * (Complex.exp ζ).im) := by
  rw [sectorStripTwist_norm, mul_comm (Real.exp _) _, ← le_div_iff₀ (Real.exp_pos _)]
  simp only [neg_mul, Real.exp_neg, div_inv_eq_mul]

/-- The exponential change of variable converts a genuine linear norm bound
into the double-exponential bound required on a horizontal strip. -/
private theorem sectorStripTwist_growth {H : ℂ → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlinear : ∀ w, ‖H w‖ ≤ A * Real.exp (B * ‖w‖)) (t : ℝ) (ζ : ℂ) :
    ‖sectorStripTwist t H ζ‖ ≤
      A * Real.exp ((B + |t|) * Real.exp |ζ.re|) := by
  have he : -t * (Complex.exp ζ).im ≤ |t| * ‖Complex.exp ζ‖ := by
    calc
      -t * (Complex.exp ζ).im = -(t * (Complex.exp ζ).im) := by ring
      _ ≤ |t * (Complex.exp ζ).im| := neg_le_abs _
      _ = |t| * |(Complex.exp ζ).im| := abs_mul _ _
      _ ≤ |t| * ‖Complex.exp ζ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg _)
  rw [sectorStripTwist_norm]
  calc
    Real.exp (-t * (Complex.exp ζ).im) * ‖H (Complex.exp ζ)‖ ≤
        Real.exp (|t| * ‖Complex.exp ζ‖) *
          (A * Real.exp (B * ‖Complex.exp ζ‖)) := by
      exact mul_le_mul (Real.exp_le_exp.mpr he) (hlinear _)
        (norm_nonneg _) (by positivity)
    _ = A * Real.exp ((B + |t|) * ‖Complex.exp ζ‖) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ A * Real.exp ((B + |t|) * Real.exp |ζ.re|) := by
      rw [Complex.norm_exp]
      gcongr
      exact le_abs_self _

/-- Strip propagation for either signed twist. The exponential image must
actually lie in the right half-plane on the open strip. -/
private theorem sectorStrip_bound {H : ℂ → ℂ} {l u A B M : ℝ}
    (hwidth : 0 < u - l) (hwidthπ : u - l < Real.pi)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hH : DiffContOnCl ℂ H {w : ℂ | 0 < w.re})
    (hlinear : ∀ w, ‖H w‖ ≤ A * Real.exp (B * ‖w‖))
    (hmap : ∀ ζ : ℂ, ζ.im ∈ Ioo l u → 0 < (Complex.exp ζ).re)
    (t : ℝ)
    (hl : ∀ ζ : ℂ, ζ.im = l →
      ‖H (Complex.exp ζ)‖ ≤ M * Real.exp (t * (Complex.exp ζ).im))
    (hu : ∀ ζ : ℂ, ζ.im = u →
      ‖H (Complex.exp ζ)‖ ≤ M * Real.exp (t * (Complex.exp ζ).im))
    {ζ : ℂ} (hζl : l ≤ ζ.im) (hζu : ζ.im ≤ u) :
    ‖H (Complex.exp ζ)‖ ≤ M * Real.exp (t * (Complex.exp ζ).im) := by
  apply (sectorStripTwist_norm_le_iff t M H ζ).mp
  apply PhragmenLindelof.horizontal_strip (a := l) (b := u)
  · have hd : Differentiable ℂ
        (fun ζ : ℂ => Complex.exp ((t : ℂ) * Complex.I * Complex.exp ζ)) :=
      (Complex.differentiable_exp.const_mul _).cexp
    exact hd.diffContOnCl.smul
      (hH.comp Complex.differentiable_exp.diffContOnCl hmap)
  · refine ⟨1, (lt_div_iff₀ hwidth).mpr (by simpa using hwidthπ), B + |t|, ?_⟩
    apply Asymptotics.IsBigO.of_bound A
    exact Filter.Eventually.of_forall fun z => by
      simpa only [one_mul, Real.norm_eq_abs, Real.abs_exp] using
        sectorStripTwist_growth hA hB hlinear t z
  · intro z hz
    exact (sectorStripTwist_norm_le_iff t M H z).mpr (hl z hz)
  · intro z hz
    exact (sectorStripTwist_norm_le_iff t M H z).mpr (hu z hz)
  · exact hζl
  · exact hζu

/-- A horizontal line exponentiates to its actual polar ray. -/
private theorem sectorStrip_exp_on_horizontal {ζ : ℂ} {θ : ℝ} (hζ : ζ.im = θ) :
    Complex.exp ζ = (Real.exp ζ.re : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  calc
    Complex.exp ζ = Complex.exp ((ζ.re : ℂ) + (θ : ℂ) * Complex.I) := by
      rw [← hζ, Complex.re_add_im]
    _ = (Real.exp ζ.re : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_add, Complex.ofReal_exp]

/-- The middle horizontal boundary uses precisely the nonnegative real-axis
estimate, independently of the sign of the twist. -/
private theorem sectorStrip_real_boundary {H : ℂ → ℂ} {M : ℝ}
    (hreal : ∀ r : ℝ, 0 ≤ r → ‖H (r : ℂ)‖ ≤ M) (t : ℝ)
    (ζ : ℂ) (hζ : ζ.im = 0) :
    ‖H (Complex.exp ζ)‖ ≤ M * Real.exp (t * (Complex.exp ζ).im) := by
  have he : Complex.exp ζ = (Real.exp ζ.re : ℂ) := by
    simpa using sectorStrip_exp_on_horizontal hζ
  simpa only [he, Complex.ofReal_im, mul_zero, Real.exp_zero, mul_one] using
    hreal (Real.exp ζ.re) (Real.exp_pos _).le

/-- Actual boundary-ray estimates propagate to the whole strict Cartesian
sector. Separate signed holomorphic twists on the upper and lower logarithmic
strips prove the estimate; no parity, conjugation symmetry, or sector-growth
conclusion is assumed. The global linear bound supplies strip growth with
exponent `1 < π / α`. The requested nonnegativity of `a` and lower bound on
`M` are retained in the interface; propagation itself does not need them. -/
theorem norm_le_on_knsOpenSector_of_boundaryRays {H : ℂ → ℂ} {α a M A B : ℝ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (_ha : 0 ≤ a) (_hM : 1 ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hH : DiffContOnCl ℂ H {w : ℂ | 0 < w.re})
    (hlinear : ∀ w, ‖H w‖ ≤ A * Real.exp (B * ‖w‖))
    (hreal : ∀ r : ℝ, 0 ≤ r → ‖H (r : ℂ)‖ ≤ M)
    (hupper : ∀ r : ℝ, 0 ≤ r →
      ‖H ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))‖ ≤
        M * Real.exp (a * Real.pi * r * Real.sin α))
    (hlower : ∀ r : ℝ, 0 ≤ r →
      ‖H ((r : ℂ) * Complex.exp ((-α : ℂ) * Complex.I))‖ ≤
        M * Real.exp (a * Real.pi * r * Real.sin α)) :
    ∀ w ∈ knsOpenSector α, ‖H w‖ ≤ M * Real.exp (a * Real.pi * |w.im|) := by
  intro w hw
  have hlog := log_im_mem_Ioo_of_mem_knsOpenSector hα0 hαhalf hw
  have he : Complex.exp (Complex.log w) = w :=
    Complex.exp_log (ne_zero_of_mem_knsOpenSector hα0 hαhalf hw)
  have hαπ : α < Real.pi := by linarith [Real.pi_pos]
  by_cases him : 0 ≤ w.im
  · have hnonneg : 0 ≤ (Complex.log w).im := by
      rw [Complex.log_im]
      exact Complex.arg_nonneg_iff.mpr him
    have hb := sectorStrip_bound (l := 0) (u := α) (by simpa using hα0)
      (by simpa using hαπ) hA hB hH hlinear
      (fun z hz => exp_re_pos_of_im_mem_Icc_symmetric hαhalf
        ⟨by linarith [hz.1], hz.2.le⟩) (a * Real.pi)
      (sectorStrip_real_boundary hreal (a * Real.pi))
      (fun z hz => ?_) hnonneg hlog.2.le
    · simpa only [he, abs_of_nonneg him] using hb
    · calc
        ‖H (Complex.exp z)‖ =
            ‖H ((Real.exp z.re : ℂ) * Complex.exp ((α : ℂ) * Complex.I))‖ := by
          rw [sectorStrip_exp_on_horizontal hz]
        _ ≤ M * Real.exp (a * Real.pi * Real.exp z.re * Real.sin α) :=
          hupper (Real.exp z.re) (Real.exp_pos _).le
        _ = M * Real.exp ((a * Real.pi) * (Complex.exp z).im) := by
          rw [Complex.exp_im, hz]
          congr 2
          ring
  · have hnonpos : (Complex.log w).im ≤ 0 := by
      rw [Complex.log_im]
      exact (lt_of_not_ge ((Complex.arg_nonneg_iff).not.mpr him)).le
    have hb := sectorStrip_bound (l := -α) (u := 0) (by simpa using hα0)
      (by simpa using hαπ) hA hB hH hlinear
      (fun z hz => exp_re_pos_of_im_mem_Icc_symmetric hαhalf
        ⟨hz.1.le, by linarith [hz.2]⟩) (-(a * Real.pi))
      (fun z hz => ?_) (sectorStrip_real_boundary hreal (-(a * Real.pi)))
      hlog.1.le hnonpos
    · simpa only [he, abs_of_neg (lt_of_not_ge him), mul_neg, neg_mul] using hb
    · calc
        ‖H (Complex.exp z)‖ =
            ‖H ((Real.exp z.re : ℂ) * Complex.exp ((-α : ℂ) * Complex.I))‖ := by
          rw [sectorStrip_exp_on_horizontal hz, Complex.ofReal_neg]
        _ ≤ M * Real.exp (a * Real.pi * Real.exp z.re * Real.sin α) :=
          hlower (Real.exp z.re) (Real.exp_pos _).le
        _ = M * Real.exp (-(a * Real.pi) * (Complex.exp z).im) := by
          rw [Complex.exp_im, hz, Real.sin_neg]
          congr 2
          ring

end MeyerGeneralProblem
