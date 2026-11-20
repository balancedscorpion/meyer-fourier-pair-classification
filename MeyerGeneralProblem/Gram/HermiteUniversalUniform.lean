module

public import MeyerGeneralProblem.Gram.UniversalLimitIntegral

@[expose] public section

/-!
# Uniform bounded-band Hermite-to-universal comparison

This module upgrades the exact sequence limit to uniform convergence on every
bounded signed-square band.  The natural pair and diagonal scales are used
throughout; their normalization ratio tends to one because the two magnitudes
become asymptotic on a bounded signed-square band.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

/-- Natural Mehler scale for a pair of nonzero spatial nodes. -/
def hermitePairScale (x y : ℝ) : ℝ :=
  1 / (|x| + |y|) ^ 2

/-- Natural Mehler pair scale specialized to a diagonal spatial node. -/
def hermiteNaturalDiagonalScale (x : ℝ) : ℝ :=
  1 / (|x| + |x|) ^ 2

theorem hermitePairScale_pos {x y : ℝ} (hx : x ≠ 0) :
    0 < hermitePairScale x y := by
  unfold hermitePairScale
  positivity

theorem hermiteNaturalDiagonalScale_pos {x : ℝ} (hx : x ≠ 0) :
    0 < hermiteNaturalDiagonalScale x := by
  unfold hermiteNaturalDiagonalScale
  positivity

@[simp]
theorem hermitePairScale_mul_abs_add_sq {x y : ℝ} (hx : x ≠ 0) :
    hermitePairScale x y * (|x| + |y|) ^ 2 = 1 := by
  unfold hermitePairScale
  field_simp

@[simp]
theorem hermiteNaturalDiagonalScale_mul_abs_add_sq {x : ℝ} (hx : x ≠ 0) :
    hermiteNaturalDiagonalScale x * (|x| + |x|) ^ 2 = 1 := by
  unfold hermiteNaturalDiagonalScale
  field_simp

/-- The resolvent scale is multiplicative on positive arguments. -/
theorem hermiteResolventScale_mul
    (m : ℕ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    hermiteResolventScale m (q * r) =
      hermiteResolventScale m q * hermiteResolventScale m r := by
  unfold hermiteResolventScale
  rw [mul_pow, Real.sqrt_mul hq.le]
  field_simp [Real.sqrt_ne_zero'.mpr hq, Real.sqrt_ne_zero'.mpr hr]

/-- Multiplicativity cancels the common vanishing pair scale from the
normalization ratio. -/
theorem hermiteResolventScale_ratio_mul
    (m : ℕ) {q r s : ℝ} (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    hermiteResolventScale m q /
        Real.sqrt (hermiteResolventScale m (q * r) *
          hermiteResolventScale m (q * s)) =
      1 / Real.sqrt (hermiteResolventScale m r *
        hermiteResolventScale m s) := by
  rw [hermiteResolventScale_mul m hq hr,
    hermiteResolventScale_mul m hq hs]
  let A := hermiteResolventScale m q
  let R := hermiteResolventScale m r
  let S := hermiteResolventScale m s
  have hA : 0 < A := hermiteResolventScale_pos m hq
  have hRS : 0 < R * S := mul_pos
    (hermiteResolventScale_pos m hr) (hermiteResolventScale_pos m hs)
  change A / Real.sqrt ((A * R) * (A * S)) =
    1 / Real.sqrt (R * S)
  rw [show (A * R) * (A * S) = A ^ 2 * (R * S) by ring,
    Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_pos hA]
  field_simp [Real.sqrt_ne_zero'.mpr hRS]

/-- The scale-normalization ratio tends to one when both diagonal-to-pair
scale ratios tend to one. -/
theorem tendsto_hermiteResolventScale_ratio_of_mul
    (m : ℕ) {q r s : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hr : ∀ n, 0 < r n) (hs : ∀ n, 0 < s n)
    (hr1 : Tendsto r atTop (nhds 1))
    (hs1 : Tendsto s atTop (nhds 1)) :
    Tendsto
      (fun n => hermiteResolventScale m (q n) /
        Real.sqrt (hermiteResolventScale m (q n * r n) *
          hermiteResolventScale m (q n * s n)))
      atTop (nhds 1) := by
  have hscale : ContinuousAt (hermiteResolventScale m) 1 := by
    unfold hermiteResolventScale
    exact (continuousAt_id.pow (2 * m)).div
      Real.continuous_sqrt.continuousAt (by norm_num)
  have hscaleOne : hermiteResolventScale m 1 = 1 := by
    simp [hermiteResolventScale]
  have hrScale : Tendsto (fun n => hermiteResolventScale m (r n))
      atTop (nhds 1) := by
    have hraw := hscale.tendsto.comp hr1
    rw [hscaleOne] at hraw
    apply hraw.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hsScale : Tendsto (fun n => hermiteResolventScale m (s n))
      atTop (nhds 1) := by
    have hraw := hscale.tendsto.comp hs1
    rw [hscaleOne] at hraw
    apply hraw.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hsqrt : Tendsto
      (fun n => Real.sqrt (hermiteResolventScale m (r n) *
        hermiteResolventScale m (s n))) atTop (nhds 1) := by
    have hprod : Tendsto
        (fun n => hermiteResolventScale m (r n) *
          hermiteResolventScale m (s n)) atTop (nhds 1) := by
      simpa only [one_mul] using hrScale.mul hsScale
    have hraw := (Real.continuous_sqrt.tendsto 1).comp hprod
    rw [Real.sqrt_one] at hraw
    apply hraw.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hratio : Tendsto
      (fun n => 1 / Real.sqrt (hermiteResolventScale m (r n) *
        hermiteResolventScale m (s n))) atTop (nhds 1) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hraw := hone.div hsqrt (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at hraw
    apply hraw.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  apply hratio.congr'
  filter_upwards with n
  exact (hermiteResolventScale_ratio_mul m (hq n) (hr n) (hs n)).symm

/-- On a same-ray pair, the absolute signed-square displacement factors into
the magnitude gap and magnitude sum. -/
theorem abs_signedSquare_sub_eq_abs_abs_sub_mul_abs_add
    {x y : ℝ} (hxy : 0 ≤ x * y) :
    |signedSquare y - signedSquare x| =
      |(|y| - |x|)| * (|x| + |y|) := by
  rcases mul_nonneg_iff.mp hxy with hsign | hsign
  · rw [signedSquare_of_nonneg hsign.1, signedSquare_of_nonneg hsign.2,
      abs_of_nonneg hsign.1, abs_of_nonneg hsign.2]
    rw [show y ^ 2 - x ^ 2 = (y - x) * (x + y) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hsign.1 hsign.2)]
  · rw [signedSquare_of_nonpos hsign.1, signedSquare_of_nonpos hsign.2,
      abs_of_nonpos hsign.1, abs_of_nonpos hsign.2]
    rw [show -(y ^ 2) - -(x ^ 2) = (x - y) * (x + y) by ring,
      abs_mul, abs_of_nonpos (add_nonpos hsign.1 hsign.2)]
    ring_nf

/-- Diagonal-to-pair scale ratio written in terms of the ratio of spatial
magnitudes. -/
theorem hermiteNaturalDiagonalScale_div_pairScale_left
    {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    hermiteNaturalDiagonalScale x / hermitePairScale x y =
      ((1 + |y| / |x|) / 2) ^ 2 := by
  unfold hermiteNaturalDiagonalScale hermitePairScale
  field_simp [abs_ne_zero.mpr hx, abs_ne_zero.mpr hy]
  ring

theorem hermiteNaturalDiagonalScale_div_pairScale_right
    {x y : ℝ} (_hx : x ≠ 0) (hy : y ≠ 0) :
    hermiteNaturalDiagonalScale y / hermitePairScale x y =
      ((1 + |x| / |y|) / 2) ^ 2 := by
  unfold hermiteNaturalDiagonalScale hermitePairScale
  field_simp [abs_ne_zero.mpr _hx, abs_ne_zero.mpr hy]
  ring

theorem hermitePairScale_mul_diagonal_div_pair_left
    {x y : ℝ} (hx : x ≠ 0) :
    hermitePairScale x y *
        (hermiteNaturalDiagonalScale x / hermitePairScale x y) =
      hermiteNaturalDiagonalScale x := by
  field_simp [ne_of_gt (hermitePairScale_pos (y := y) hx)]

theorem hermitePairScale_mul_diagonal_div_pair_right
    {x y : ℝ} (hx : x ≠ 0) :
    hermitePairScale x y *
        (hermiteNaturalDiagonalScale y / hermitePairScale x y) =
      hermiteNaturalDiagonalScale y := by
  field_simp [ne_of_gt (hermitePairScale_pos (y := y) hx)]

/-- Along any same-ray sequence escaping in a bounded signed-square band, the
normalized Hermite kernel converges to the exact universal kernel. -/
theorem tendsto_normalizedHermiteGramKernel_of_escape_bounded_band
    (m : ℕ) (hm : 1 ≤ m)
    {x y : ℕ → ℝ} {L δ₀ : ℝ}
    (_hL : 0 ≤ L)
    (hxne : ∀ n, x n ≠ 0)
    (hyne : ∀ n, y n ≠ 0)
    (hsame : ∀ n, 0 ≤ x n * y n)
    (hxEscape : Tendsto (fun n => |signedSquare (x n)|) atTop atTop)
    (hyEscape : Tendsto (fun n => |signedSquare (y n)|) atTop atTop)
    (hband : ∀ n, |signedSquare (y n) - signedSquare (x n)| ≤ L)
    (hδ : Tendsto (fun n => signedSquare (y n) - signedSquare (x n))
      atTop (nhds δ₀)) :
    Tendsto (fun n => normalizedHermiteGramKernel m hm (x n) (y n))
      atTop (nhds (universalGramKernel m δ₀)) := by
  have hxAbs : Tendsto (fun n => |x n|) atTop atTop := by
    have hraw := Real.tendsto_sqrt_atTop.comp hxEscape
    apply hraw.congr'
    filter_upwards with n
    change Real.sqrt |signedSquare (x n)| = |x n|
    rw [abs_signedSquare, Real.sqrt_sq_eq_abs, abs_abs]
  have hyAbs : Tendsto (fun n => |y n|) atTop atTop := by
    have hraw := Real.tendsto_sqrt_atTop.comp hyEscape
    apply hraw.congr'
    filter_upwards with n
    change Real.sqrt |signedSquare (y n)| = |y n|
    rw [abs_signedSquare, Real.sqrt_sq_eq_abs, abs_abs]
  have hsum : Tendsto (fun n => |x n| + |y n|) atTop atTop :=
    tendsto_atTop_mono
      (fun n => le_add_of_nonneg_right (abs_nonneg (y n))) hxAbs
  have hdiffAbs : Tendsto (fun n => |(|y n| - |x n|)|)
      atTop (nhds 0) := by
    have hupper : Tendsto
        (fun n => L * (|x n| + |y n|)⁻¹) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp hsum)
    apply squeeze_zero (fun n => abs_nonneg _)
      (fun n => ?_) hupper
    have hsumPos : 0 < |x n| + |y n| :=
      add_pos (abs_pos.mpr (hxne n)) (abs_pos.mpr (hyne n))
    have hfactor := abs_signedSquare_sub_eq_abs_abs_sub_mul_abs_add
      (hsame n)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hsumPos).2
    rw [← hfactor]
    exact hband n
  have hdiff : Tendsto (fun n => |y n| - |x n|) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using hdiffAbs
  have hyDivX : Tendsto (fun n => |y n| / |x n|) atTop (nhds 1) := by
    have hsmall : Tendsto
        (fun n => (|y n| - |x n|) * (|x n|)⁻¹)
        atTop (nhds 0) := by
      simpa using hdiff.mul (tendsto_inv_atTop_zero.comp hxAbs)
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hraw := hone.add hsmall
    have hraw' : Tendsto
        (fun n => 1 + (|y n| - |x n|) * (|x n|)⁻¹)
        atTop (nhds 1) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards with n
    field_simp [abs_ne_zero.mpr (hxne n)]
    ring
  have hxDivY : Tendsto (fun n => |x n| / |y n|) atTop (nhds 1) := by
    have hdiff' : Tendsto (fun n => |x n| - |y n|) atTop (nhds 0) := by
      simpa [neg_sub] using hdiff.neg
    have hsmall : Tendsto
        (fun n => (|x n| - |y n|) * (|y n|)⁻¹)
        atTop (nhds 0) := by
      simpa using hdiff'.mul (tendsto_inv_atTop_zero.comp hyAbs)
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hraw := hone.add hsmall
    have hraw' : Tendsto
        (fun n => 1 + (|x n| - |y n|) * (|y n|)⁻¹)
        atTop (nhds 1) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards with n
    field_simp [abs_ne_zero.mpr (hyne n)]
    ring
  let qxy : ℕ → ℝ := fun n => hermitePairScale (x n) (y n)
  let qxx : ℕ → ℝ := fun n => hermiteNaturalDiagonalScale (x n)
  let qyy : ℕ → ℝ := fun n => hermiteNaturalDiagonalScale (y n)
  let rxx : ℕ → ℝ := fun n => qxx n / qxy n
  let ryy : ℕ → ℝ := fun n => qyy n / qxy n
  have hrxx1 : Tendsto rxx atTop (nhds 1) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hhalf : Tendsto (fun n => (1 + |y n| / |x n|) / 2)
        atTop (nhds 1) := by
      convert (hone.add hyDivX).div_const 2 using 1 <;> norm_num
    have hp : Tendsto (fun n => ((1 + |y n| / |x n|) / 2) ^ 2)
        atTop (nhds 1) := by simpa using hhalf.pow 2
    apply hp.congr'
    filter_upwards with n
    simpa only [rxx, qxx, qxy] using
      (hermiteNaturalDiagonalScale_div_pairScale_left
        (hxne n) (hyne n)).symm
  have hryy1 : Tendsto ryy atTop (nhds 1) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hhalf : Tendsto (fun n => (1 + |x n| / |y n|) / 2)
        atTop (nhds 1) := by
      convert (hone.add hxDivY).div_const 2 using 1 <;> norm_num
    have hp : Tendsto (fun n => ((1 + |x n| / |y n|) / 2) ^ 2)
        atTop (nhds 1) := by simpa using hhalf.pow 2
    apply hp.congr'
    filter_upwards with n
    simpa only [ryy, qyy, qxy] using
      (hermiteNaturalDiagonalScale_div_pairScale_right
        (hxne n) (hyne n)).symm
  have hqxyPos : ∀ n, 0 < qxy n := fun n =>
    hermitePairScale_pos (y := y n) (hxne n)
  have hqxxPos : ∀ n, 0 < qxx n := fun n =>
    hermiteNaturalDiagonalScale_pos (hxne n)
  have hqyyPos : ∀ n, 0 < qyy n := fun n =>
    hermiteNaturalDiagonalScale_pos (hyne n)
  have hrxxPos : ∀ n, 0 < rxx n := fun n => by
    dsimp only [rxx]
    exact div_pos (hqxxPos n) (hqxyPos n)
  have hryyPos : ∀ n, 0 < ryy n := fun n => by
    dsimp only [ryy]
    exact div_pos (hqyyPos n) (hqxyPos n)
  have hqxyNhd : Tendsto qxy atTop (nhds 0) := by
    have hden : Tendsto (fun n => (|x n| + |y n|) ^ 2) atTop atTop := by
      apply tendsto_atTop_mono' atTop ?_ hsum
      filter_upwards [tendsto_atTop.1 hsum 1] with n hn
      nlinarith
    have hinv := tendsto_inv_atTop_zero.comp hden
    apply hinv.congr'
    filter_upwards with n
    change ((|x n| + |y n|) ^ 2)⁻¹ = qxy n
    simp only [qxy, hermitePairScale, one_div]
  have hqxxNhd : Tendsto qxx atTop (nhds 0) := by
    have htwice : Tendsto (fun n => |x n| + |x n|) atTop atTop :=
      tendsto_atTop_mono (fun n => le_add_of_nonneg_right (abs_nonneg (x n))) hxAbs
    have hden : Tendsto (fun n => (|x n| + |x n|) ^ 2) atTop atTop := by
      apply tendsto_atTop_mono' atTop ?_ htwice
      filter_upwards [tendsto_atTop.1 htwice 1] with n hn
      nlinarith
    have hinv := tendsto_inv_atTop_zero.comp hden
    apply hinv.congr'
    filter_upwards with n
    change ((|x n| + |x n|) ^ 2)⁻¹ = qxx n
    simp only [qxx, hermiteNaturalDiagonalScale, one_div]
  have hqyyNhd : Tendsto qyy atTop (nhds 0) := by
    have htwice : Tendsto (fun n => |y n| + |y n|) atTop atTop :=
      tendsto_atTop_mono (fun n => le_add_of_nonneg_right (abs_nonneg (y n))) hyAbs
    have hden : Tendsto (fun n => (|y n| + |y n|) ^ 2) atTop atTop := by
      apply tendsto_atTop_mono' atTop ?_ htwice
      filter_upwards [tendsto_atTop.1 htwice 1] with n hn
      nlinarith
    have hinv := tendsto_inv_atTop_zero.comp hden
    apply hinv.congr'
    filter_upwards with n
    change ((|y n| + |y n|) ^ 2)⁻¹ = qyy n
    simp only [qyy, hermiteNaturalDiagonalScale, one_div]
  have hqxyLim : Tendsto qxy atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hqxyNhd, Filter.Eventually.of_forall hqxyPos⟩
  have hqxxLim : Tendsto qxx atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hqxxNhd, Filter.Eventually.of_forall hqxxPos⟩
  have hqyyLim : Tendsto qyy atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hqyyNhd, Filter.Eventually.of_forall hqyyPos⟩
  have hqxyOne : ∀ᶠ n in atTop, qxy n ≤ 1 :=
    (hqxyNhd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn => hn.le)
  have hqxxOne : ∀ᶠ n in atTop, qxx n ≤ 1 :=
    (hqxxNhd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn => hn.le)
  have hqyyOne : ∀ᶠ n in atTop, qyy n ≤ 1 :=
    (hqyyNhd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn => hn.le)
  have hscaleRatio : Tendsto
      (fun n => hermiteResolventScale m (qxy n) /
        Real.sqrt (hermiteResolventScale m (qxx n) *
          hermiteResolventScale m (qyy n)))
      atTop (nhds 1) := by
    have hraw := tendsto_hermiteResolventScale_ratio_of_mul
      m hqxyPos hrxxPos hryyPos hrxx1 hryy1
    apply hraw.congr'
    filter_upwards with n
    rw [hermitePairScale_mul_diagonal_div_pair_left (hxne n),
      hermitePairScale_mul_diagonal_div_pair_right (hxne n)]
  exact tendsto_normalizedHermiteGramKernel_of_scaled_sequences_to_universal
    m hm hqxyPos hqxxPos hqyyPos hqxyOne hqxxOne hqyyOne hsame
      (fun n => hermitePairScale_mul_abs_add_sq (hxne n))
      (fun n => hermiteNaturalDiagonalScale_mul_abs_add_sq (hxne n))
      (fun n => hermiteNaturalDiagonalScale_mul_abs_add_sq (hyne n))
      hqxyLim hqxxLim hqyyLim hδ hscaleRatio

/-- Exact local analytic statement needed for the same-side compact
comparison: on every bounded signed-square metric band, the normalized
Hermite kernel converges uniformly to the universal kernel as both nodes
escape. -/
def HermiteUniversalUniformOnBand (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∀ L ≥ 0, ∀ ε > 0, ∃ T ≥ 0, ∀ x y : ℝ,
    T ≤ |signedSquare x| →
    T ≤ |signedSquare y| →
    |signedSquare y - signedSquare x| ≤ L →
    ‖normalizedHermiteGramKernel m hm x y -
      universalGramKernel m (signedSquare y - signedSquare x)‖ ≤ ε

/-- The bounded-band comparison holds unconditionally.  Failure would give a
bad escaping sequence; compactness of `[-L,L]` supplies a convergent
displacement subsequence, contradicting the exact sequence limit above. -/
theorem hermiteUniversalUniformOnBand
    (m : ℕ) (hm : 1 ≤ m) :
    HermiteUniversalUniformOnBand m hm := by
  intro L hL ε hε
  by_contra hfail
  push Not at hfail
  let T₀ : ℝ := L / 2 + 1
  have hT₀ : 0 < T₀ := by dsimp only [T₀]; linarith
  have hchoice : ∀ n : ℕ, ∃ x y : ℝ,
      (n : ℝ) + T₀ ≤ |signedSquare x| ∧
      (n : ℝ) + T₀ ≤ |signedSquare y| ∧
      |signedSquare y - signedSquare x| ≤ L ∧
      ε < ‖normalizedHermiteGramKernel m hm x y -
        universalGramKernel m (signedSquare y - signedSquare x)‖ := by
    intro n
    exact hfail ((n : ℝ) + T₀) (by positivity)
  choose x y hxLarge hyLarge hband hbad using hchoice
  have hsame : ∀ n, 0 ≤ x n * y n := by
    intro n
    have hsign := sameSign_of_signedSquare_large_of_difference_le
      (T := (n : ℝ) + T₀) (L := L)
      (by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        dsimp only [T₀]
        linarith)
      (hxLarge n) (hyLarge n) (hband n)
    rcases hsign with hpos | hneg
    · exact mul_nonneg hpos.1 hpos.2
    · exact mul_nonneg_of_nonpos_of_nonpos hneg.1 hneg.2
  have hxne : ∀ n, x n ≠ 0 := by
    intro n hzero
    have h := hxLarge n
    rw [hzero, signedSquare_zero, abs_zero] at h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp only [T₀] at h
    linarith
  have hyne : ∀ n, y n ≠ 0 := by
    intro n hzero
    have h := hyLarge n
    rw [hzero, signedSquare_zero, abs_zero] at h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp only [T₀] at h
    linarith
  let d : ℕ → ℝ := fun n => signedSquare (y n) - signedSquare (x n)
  have hdMem : ∀ n, d n ∈ Set.Icc (-L) L := by
    intro n
    exact (abs_le.mp (hband n))
  rcases isCompact_Icc.tendsto_subseq hdMem with
    ⟨δ₀, hδ₀, φ, hφ, hδ⟩
  let xs : ℕ → ℝ := x ∘ φ
  let ys : ℕ → ℝ := y ∘ φ
  have hxEscape : Tendsto (fun n => |signedSquare (xs n)|) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + T₀) atTop atTop :=
      tendsto_atTop_add_const_right atTop T₀ tendsto_natCast_atTop_atTop
    apply tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards with n
    calc
      (n : ℝ) + T₀ ≤ (φ n : ℝ) + T₀ := by
        have hnφ : (n : ℝ) ≤ (φ n : ℝ) := by
          exact_mod_cast (hφ.id_le n)
        linarith
      _ ≤ |signedSquare (xs n)| := by
        exact hxLarge (φ n)
  have hyEscape : Tendsto (fun n => |signedSquare (ys n)|) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + T₀) atTop atTop :=
      tendsto_atTop_add_const_right atTop T₀ tendsto_natCast_atTop_atTop
    apply tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards with n
    calc
      (n : ℝ) + T₀ ≤ (φ n : ℝ) + T₀ := by
        have hnφ : (n : ℝ) ≤ (φ n : ℝ) := by
          exact_mod_cast (hφ.id_le n)
        linarith
      _ ≤ |signedSquare (ys n)| := by
        exact hyLarge (φ n)
  have hδ' : Tendsto
      (fun n => signedSquare (ys n) - signedSquare (xs n))
      atTop (nhds δ₀) := by
    apply hδ.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hkernel := tendsto_normalizedHermiteGramKernel_of_escape_bounded_band
    m hm hL (fun n => hxne (φ n)) (fun n => hyne (φ n))
      (fun n => hsame (φ n)) hxEscape hyEscape (fun n => hband (φ n)) hδ'
  have huniversal : Tendsto
      (fun n => universalGramKernel m
        (signedSquare (ys n) - signedSquare (xs n)))
      atTop (nhds (universalGramKernel m δ₀)) :=
    (continuous_universalGramKernel hm).continuousAt.tendsto.comp hδ'
  have hdifference : Tendsto
      (fun n => normalizedHermiteGramKernel m hm (xs n) (ys n) -
        universalGramKernel m
          (signedSquare (ys n) - signedSquare (xs n)))
      atTop (nhds 0) := by
    simpa only [xs, ys, Function.comp_apply, sub_self] using
      hkernel.sub huniversal
  have hnorm : Tendsto
      (fun n => ‖normalizedHermiteGramKernel m hm (xs n) (ys n) -
        universalGramKernel m
          (signedSquare (ys n) - signedSquare (xs n))‖)
      atTop (nhds 0) := by
    simpa using hdifference.norm
  have hsmall := hnorm.eventually (Iio_mem_nhds hε)
  rcases hsmall.exists with ⟨n, hn⟩
  have hbadn := hbad (φ n)
  change ε < ‖normalizedHermiteGramKernel m hm (xs n) (ys n) -
    universalGramKernel m
      (signedSquare (ys n) - signedSquare (xs n))‖ at hbadn
  linarith

end

end MeyerGeneralProblem
