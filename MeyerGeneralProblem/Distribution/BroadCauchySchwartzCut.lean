module

public import MeyerGeneralProblem.Distribution.BroadCauchyCompactTest

@[expose] public section

/-!
# Actual compact Schwartz cutoffs of the broad Cauchy kernel

At a prescribed finite seminorm order the cutoff differences tend to
zero. The decay bound applies to the original test variable and is
uniform for poles in any bounded region off the real line.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- The actual compact test used in the definition of the broad Cauchy pairing. -/
def broadCauchySchwartzCut (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (N : ℕ) : SchwartzMap ℝ ℂ := by
  let f : ℝ → ℂ := (scaledCompactSchwartzCutoff N : ℝ → ℂ) * broadCauchyKernel m z
  have hC : HasCompactSupport f := (scaledCompactSchwartzCutoff_hasCompactSupport N).mul_right
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    ((scaledCompactSchwartzCutoff N).smooth ⊤).mul (contDiff_broadCauchyKernel_test m z hz ⊤)
  exact hC.toSchwartzMap hD

theorem broadCauchySchwartzCut_apply (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (N : ℕ) (x : ℝ) :
    broadCauchySchwartzCut m z hz N x = scaledCompactSchwartzCutoff N x * broadCauchyKernel m z x :=
  rfl

private theorem norm_cutoff_derivative_le (N i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (scaledCompactSchwartzCutoff N) x‖ ≤
      SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff :=
  (norm_iteratedDeriv_scaledCompactSchwartzCutoff_le N i x).trans
    (mul_le_of_le_one_left (apply_nonneg _ _)
      (pow_le_one₀ (compactSchwartzCutoffScale_pos N).le (compactSchwartzCutoffScale_le_one N)))

private theorem norm_iteratedDeriv_cutoff_difference_le (N M i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i ((scaledCompactSchwartzCutoff N : ℝ → ℂ) -
      (scaledCompactSchwartzCutoff M : ℝ → ℂ)) x‖ ≤ 2 * SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff := by
  rw [iteratedDeriv_sub ((scaledCompactSchwartzCutoff N).smooth i).contDiffAt
    ((scaledCompactSchwartzCutoff M).smooth i).contDiffAt]
  calc
    _ ≤ ‖iteratedDeriv i (scaledCompactSchwartzCutoff N) x‖ +
        ‖iteratedDeriv i (scaledCompactSchwartzCutoff M) x‖ := norm_sub_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add (norm_cutoff_derivative_le N i x) (norm_cutoff_derivative_le M i x)

private theorem norm_weighted_kernel_tail_le (m i k : ℕ) (hk : k < m)
    (z : ℂ) (x B : ℝ) (hB : 1 ≤ B) (hx : B ≤ |x|) (hfar : 2 * ‖z‖ ≤ B) :
    |x| ^ k * ‖iteratedDeriv i (broadCauchyKernel m z) x‖ ≤
      ((m.ascFactorial i : ℝ) * 2 ^ (m + i)) * B⁻¹ := by
  have hpos : 0 < |x| := zero_lt_one.trans_le (hB.trans hx)
  have hratio : |x| ^ k / |x| ^ (m + i) ≤ B⁻¹ := by
    rw [← one_div B]
    apply (div_le_div_iff₀ (pow_pos hpos _) (zero_lt_one.trans_le hB)).mpr
    rw [one_mul]
    calc
      _ ≤ |x| ^ k * |x| := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = |x| ^ (k + 1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (hB.trans hx) (by omega)
  calc
    _ ≤ |x| ^ k * ((m.ascFactorial i : ℝ) * 2 ^ (m + i) / |x| ^ (m + i)) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_broadCauchyKernel_test_tail_of_far m i z x hpos (hfar.trans hx)) (by positivity)
    _ = ((m.ascFactorial i : ℝ) * 2 ^ (m + i)) * (|x| ^ k / |x| ^ (m + i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

/-- Difference of two expanding cutoffs, supported beyond their common inner interval. -/
def annularSchwartzCutoff (N M : ℕ) : SchwartzMap ℝ ℂ :=
  scaledCompactSchwartzCutoff N - scaledCompactSchwartzCutoff M

theorem annularSchwartzCutoff_hasCompactSupport (N M : ℕ) :
    HasCompactSupport (annularSchwartzCutoff N M : ℝ → ℂ) :=
  (scaledCompactSchwartzCutoff_hasCompactSupport N).sub (scaledCompactSchwartzCutoff_hasCompactSupport M)

private theorem le_abs_of_mem_tsupport_annularSchwartzCutoff {K N M : ℕ}
    (hN : K ≤ N) (hM : K ≤ M) {x : ℝ}
    (hx : x ∈ tsupport (annularSchwartzCutoff N M : ℝ → ℂ)) : (K : ℝ) + 1 ≤ |x| := by
  have hs : tsupport (annularSchwartzCutoff N M : ℝ → ℂ) ⊆ {x : ℝ | (K : ℝ) + 1 ≤ |x|} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_abs)
    intro x hx
    change (K : ℝ) + 1 ≤ |x|
    by_contra! h
    have hN' : (K : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hN
    have hM' : (K : ℝ) + 1 ≤ (M : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hM
    exact hx (by
      change scaledCompactSchwartzCutoff N x - scaledCompactSchwartzCutoff M x = 0
      rw [scaledCompactSchwartzCutoff_eq_one N (h.le.trans hN'),
        scaledCompactSchwartzCutoff_eq_one M (h.le.trans hM'), sub_self])
  exact hs hx

theorem mem_compactCauchyPoleDomain_annularSchwartzCutoff {K N M : ℕ}
    (hN : K ≤ N) (hM : K ≤ M) {z : ℂ} (hz : ‖z‖ < (K : ℝ) + 1) :
    z ∈ compactCauchyPoleDomain (annularSchwartzCutoff N M) := by
  rintro ⟨x, hx, rfl⟩
  rw [Complex.norm_real, Real.norm_eq_abs] at hz
  exact (not_lt_of_ge (le_abs_of_mem_tsupport_annularSchwartzCutoff hN hM hx)) hz

/-- A compact Cauchy test on the difference of the two expanding cutoffs. -/
def broadCauchyAnnularCut (m : ℕ) (z : ℂ) (N M : ℕ) : SchwartzMap ℝ ℂ :=
  compactCauchySchwartzTest (annularSchwartzCutoff N M) (annularSchwartzCutoff_hasCompactSupport N M) m z

private theorem broadCauchyAnnularCut_apply (m : ℕ) (z : ℂ) (N M : ℕ)
    (hz : z ∈ compactCauchyPoleDomain (annularSchwartzCutoff N M)) (x : ℝ) :
    broadCauchyAnnularCut m z N M x =
      (scaledCompactSchwartzCutoff N x - scaledCompactSchwartzCutoff M x) * broadCauchyKernel m z x :=
  compactCauchySchwartzTest_apply _ _ hz x

/-- The annular tail estimate includes real poles in the inner disk. -/
theorem broadCauchyAnnularCut_seminorm_le (m k j : ℕ) (hk : k < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (K N M : ℕ),
      2 * ‖z‖ ≤ (K : ℝ) + 1 → K ≤ N → K ≤ M →
      SchwartzMap.seminorm ℂ k j (broadCauchyAnnularCut m z N M) ≤ C * compactSchwartzCutoffScale K := by
  let B (i : ℕ) : ℝ := (j.choose i : ℝ) * (2 * SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff) *
    ((m.ascFactorial (j - i) : ℝ) * 2 ^ (m + (j - i)))
  have hB (i : ℕ) : 0 ≤ B i := by dsimp only [B]; positivity
  let C := ∑ i ∈ Finset.range (j + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hB i
  refine ⟨C, hC, fun z K N M hfar hN hM => ?_⟩
  have hK : (1 : ℝ) ≤ (K : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg K)
  have hdom := mem_compactCauchyPoleDomain_annularSchwartzCutoff hN hM (by linarith)
  refine SchwartzMap.seminorm_le_bound' ℂ k j _
    (mul_nonneg hC (compactSchwartzCutoffScale_pos K).le) fun x => ?_
  let χ := annularSchwartzCutoff N M
  change |x| ^ k * ‖iteratedDeriv j (compactCauchySchwartzTest χ
    (annularSchwartzCutoff_hasCompactSupport N M) m z) x‖ ≤ _
  by_cases hx : x ∈ tsupport (χ : ℝ → ℂ)
  · have hout := le_abs_of_mem_tsupport_annularSchwartzCutoff hN hM hx
    have hne : (x : ℂ) - z ≠ 0 := fun he => hdom ⟨x, hx, sub_eq_zero.mp he⟩
    rw [iteratedDeriv_compactCauchySchwartzTest _ m j hdom hx]
    simp only [← iteratedDeriv_broadCauchyKernel_test_of_sub_ne_zero _ _ _ _ hne]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, show C = ∑ i ∈ Finset.range (j + 1), B i from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := norm_iteratedDeriv_cutoff_difference_le N M i x
    have ht := norm_weighted_kernel_tail_le m (j - i) k hk z x ((K : ℝ) + 1) hK hout hfar
    simp only [norm_mul, norm_natCast]
    calc
      _ = (j.choose i : ℝ) * ‖iteratedDeriv i χ x‖ *
          (|x| ^ k * ‖iteratedDeriv (j - i) (broadCauchyKernel m z) x‖) := by ring
      _ ≤ ((j.choose i : ℝ) * (2 * SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff)) *
          (((m.ascFactorial (j - i) : ℝ) * 2 ^ (m + (j - i))) * ((K : ℝ) + 1)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)) ht (by positivity) (by positivity)
      _ = _ := by dsimp only [B, compactSchwartzCutoffScale]; ring
  · rw [iteratedDeriv_compactCauchySchwartzTest_eq_zero _ m j hdom hx, norm_zero, mul_zero]
    exact mul_nonneg hC (compactSchwartzCutoffScale_pos K).le

theorem broadCauchyAnnularCut_sub (m : ℕ) (z : ℂ) (K N M L : ℕ)
    (hz : ‖z‖ < (K : ℝ) + 1) (hN : K ≤ N) (hM : K ≤ M) (hL : K ≤ L) :
    broadCauchyAnnularCut m z N L - broadCauchyAnnularCut m z M L =
      broadCauchyAnnularCut m z N M := by
  ext x
  change broadCauchyAnnularCut m z N L x - broadCauchyAnnularCut m z M L x =
    broadCauchyAnnularCut m z N M x
  rw [broadCauchyAnnularCut_apply _ _ _ _ (mem_compactCauchyPoleDomain_annularSchwartzCutoff hN hL hz),
    broadCauchyAnnularCut_apply _ _ _ _ (mem_compactCauchyPoleDomain_annularSchwartzCutoff hM hL hz),
    broadCauchyAnnularCut_apply _ _ _ _ (mem_compactCauchyPoleDomain_annularSchwartzCutoff hN hM hz)]
  ring

theorem broadCauchyAnnularCut_eq_sub_offReal (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (N M : ℕ) :
    broadCauchyAnnularCut m z N M = broadCauchySchwartzCut m z hz N - broadCauchySchwartzCut m z hz M := by
  have hd : z ∈ compactCauchyPoleDomain (annularSchwartzCutoff N M) := by
    rintro ⟨x, _, rfl⟩
    exact hz (Complex.ofReal_im x)
  ext x
  change broadCauchyAnnularCut m z N M x = broadCauchySchwartzCut m z hz N x - broadCauchySchwartzCut m z hz M x
  rw [broadCauchyAnnularCut_apply m z N M hd, broadCauchySchwartzCut_apply,
    broadCauchySchwartzCut_apply, sub_mul]

/-- At every derivative order and every weight below the pole order,
the difference of the two actual off-real Schwartz cutoffs has a uniform tail bound. -/
theorem broadCauchySchwartzCut_seminorm_sub_le (m k j : ℕ) (hk : k < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hz : z.im ≠ 0) (K N M : ℕ),
      2 * ‖z‖ ≤ (K : ℝ) + 1 → K ≤ N → K ≤ M →
      SchwartzMap.seminorm ℂ k j
        (broadCauchySchwartzCut m z hz N - broadCauchySchwartzCut m z hz M) ≤
          C * compactSchwartzCutoffScale K := by
  obtain ⟨C, hC, hbound⟩ := broadCauchyAnnularCut_seminorm_le m k j hk
  refine ⟨C, hC, fun z hz K N M hfar hN hM => ?_⟩
  rw [← broadCauchyAnnularCut_eq_sub_offReal m z hz N M]
  exact hbound z K N M hfar hN hM

/-- Every actual cutoff has the same global finite-order bound,
uniformly in its radius. -/
theorem broadCauchySchwartzCut_seminorm_le (m k j : ℕ) (hk : k ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hz : z.im ≠ 0) (N : ℕ),
      SchwartzMap.seminorm ℂ k j (broadCauchySchwartzCut m z hz N) ≤
        C * (1 + ‖z‖) ^ k * (max 1 (|z.im|)⁻¹) ^ (m + j) := by
  let B (i : ℕ) : ℝ := (j.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff *
    (m.ascFactorial (j - i) : ℝ)
  have hB (i : ℕ) : 0 ≤ B i := by dsimp only [B]; positivity
  let C := ∑ i ∈ Finset.range (j + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hB i
  refine ⟨C, hC, fun z hz N => ?_⟩
  let a := 1 + ‖z‖
  let b := max 1 (|z.im|)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 1 ≤ b := le_max_left _ _
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  apply SchwartzMap.seminorm_le_bound' ℂ k j _
    (show 0 ≤ C * a ^ k * b ^ (m + j) by positivity)
  intro x
  have hfun : (broadCauchySchwartzCut m z hz N : ℝ → ℂ) =
      (scaledCompactSchwartzCutoff N : ℝ → ℂ) * broadCauchyKernel m z := rfl
  rw [hfun, iteratedDeriv_mul ((scaledCompactSchwartzCutoff N).smooth j).contDiffAt
    (contDiff_broadCauchyKernel_test m z hz j).contDiffAt]
  change |x| ^ k * ‖∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℂ) * iteratedDeriv i (scaledCompactSchwartzCutoff N) x *
      iteratedDeriv (j - i) (broadCauchyKernel m z) x‖ ≤ C * a ^ k * b ^ (m + j)
  calc
    _ ≤ |x| ^ k * ∑ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i (scaledCompactSchwartzCutoff N) x *
          iteratedDeriv (j - i) (broadCauchyKernel m z) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ _ := by
      rw [Finset.mul_sum, show C = ∑ i ∈ Finset.range (j + 1), B i from rfl,
        Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_cutoff_derivative_le N i x
      have hk' : k ≤ m + (j - i) := hk.trans (Nat.le_add_right _ _)
      have ht := norm_weighted_iteratedDeriv_broadCauchyKernel_test_le m k (j - i) hk' z hz x
      simp only [norm_mul, norm_natCast]
      calc
        _ = (j.choose i : ℝ) * ‖iteratedDeriv i (scaledCompactSchwartzCutoff N) x‖ *
            (|x| ^ k * ‖iteratedDeriv (j - i) (broadCauchyKernel m z) x‖) := by ring
        _ ≤ ((j.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff) *
            ((m.ascFactorial (j - i) : ℝ) * a ^ k * b ^ (m + (j - i))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)) ht
            (by positivity) (by positivity)
        _ = B i * a ^ k * b ^ (m + (j - i)) := by dsimp only [B]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hb (Nat.add_le_add_left (Nat.sub_le j i) m)) (by positivity)

end

end MeyerGeneralProblem
