module

public import MeyerGeneralProblem.Interpolation.QuadraticBlockEnergy

@[expose] public section

/-!
# Smooth ray restriction of actual exterior blocks

The fixed smooth step is constant on every exterior block's two rays.
It therefore selects one ray without altering any derivative there and
without introducing an artificial nonsmooth point at the origin.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- The actual block piece restricted smoothly to the ray of sign ε. -/
def rayQuadraticBlockPiece (B : ℝ) (b : ℕ) (ε : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  unitBlockTransition (ε*x) • quadraticBlockPiece B b (fun y => h (y^2)) x

/-- Ray selection preserves genuine smoothness, including at the origin. -/
theorem contDiff_rayQuadraticBlockPiece (B : ℝ) (b : ℕ) (ε : ℝ)
    {h : ℝ → ℂ} {n : ℕ∞} (hh : ContDiff ℝ n h) :
    ContDiff ℝ n (rayQuadraticBlockPiece B b ε h) :=
  (contDiff_unitBlockTransition.comp (by fun_prop)).smul
    (contDiff_quadraticBlockPiece B b (hh.comp (by fun_prop)))

/-- Every derivative of the selected piece has the original physical
block support enclosure; the ray selector creates no new support. -/
theorem tsupport_iteratedDeriv_rayQuadraticBlockPiece_subset {B : ℝ} (hB : 0 < B)
    (b j : ℕ) (ε : ℝ) (h : ℝ → ℂ) :
    tsupport (iteratedDeriv j (rayQuadraticBlockPiece B b ε h)) ⊆
      quadraticBlockDomain B b := by
  apply (tsupport_iteratedDeriv_subset_original j).trans
  exact (tsupport_smul_subset_right _ _).trans
    (tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b 0 _)

/-- On the selected exterior ray every actual derivative is unchanged;
on the other ray every actual derivative vanishes. -/
theorem iteratedDeriv_rayQuadraticBlockPiece {B : ℝ} (hB : 1 ≤ B)
    {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : ε^2=1) (h : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (rayQuadraticBlockPiece B b ε h) x =
      if 0 < ε*x then iteratedDeriv j (quadraticBlockPiece B b (fun y => h (y^2))) x
      else 0 := by
  have hB0 : 0 < B := by linarith
  by_cases hx : x ∈ quadraticBlockDomain B b
  · have habs : |ε*x| = |x| := by
      rw [abs_mul]
      have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
      rw [heps, one_mul]
    have hsize : 1 ≤ |ε*x| := by rw [habs]; exact (quadraticBlockDomain_bounds hB hb hx).1
    by_cases hpos : 0 < ε*x
    · simp only [hpos, ite_true]
      have hnear : {y : ℝ | (1/8 : ℝ) < ε*y} ∈ 𝓝 x :=
        (isOpen_lt continuous_const (continuous_const.mul continuous_id)).mem_nhds
          (by change (1/8 : ℝ) < ε*x; rw [abs_of_pos hpos] at hsize; linarith)
      have heq : rayQuadraticBlockPiece B b ε h =ᶠ[𝓝 x]
          quadraticBlockPiece B b (fun y => h (y^2)) := by
        filter_upwards [hnear] with y hy
        simp only [rayQuadraticBlockPiece, unitBlockTransition_one hy.le, one_smul]
      exact heq.iteratedDeriv_eq j
    · simp only [hpos, ite_false]
      have hneg : ε*x ≤ -1 := by
        rw [abs_of_nonpos (le_of_not_gt hpos)] at hsize
        linarith
      have hnear : {y : ℝ | ε*y < -(1/8 : ℝ)} ∈ 𝓝 x :=
        (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds
          (by change ε*x < -(1/8 : ℝ); linarith)
      have heq : rayQuadraticBlockPiece B b ε h =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [hnear] with y hy
        simp only [rayQuadraticBlockPiece, unitBlockTransition_zero hy.le, zero_smul]
      rw [heq.iteratedDeriv_eq j]
      simp
  · have hzray : iteratedDeriv j (rayQuadraticBlockPiece B b ε h) x = 0 := by
      by_contra hz
      exact hx (tsupport_iteratedDeriv_rayQuadraticBlockPiece_subset hB0 b j ε h (subset_closure hz))
    have hzbase : iteratedDeriv j (quadraticBlockPiece B b (fun y => h (y^2))) x = 0 := by
      by_contra hz
      exact hx (tsupport_iteratedDeriv_quadraticBlockPiece_subset hB0 b j _ (subset_closure hz))
    simp only [hzray, hzbase, ite_self]

/-- Ray restriction cannot increase the norm of any actual derivative. -/
theorem norm_iteratedDeriv_rayQuadraticBlockPiece_le {B : ℝ} (hB : 1 ≤ B)
    {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : ε^2=1) (h : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (rayQuadraticBlockPiece B b ε h) x‖ ≤
      ‖iteratedDeriv j (quadraticBlockPiece B b (fun y => h (y^2))) x‖ := by
  rw [iteratedDeriv_rayQuadraticBlockPiece hB hb hε]
  split_ifs <;> simp

/-- Every actual selected-ray derivative has compact support. -/
theorem hasCompactSupport_iteratedDeriv_rayQuadraticBlockPiece {B : ℝ} (hB : 1 ≤ B)
    {b : ℕ} (hb : 2 ≤ b) (ε : ℝ) (h : ℝ → ℂ) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j (rayQuadraticBlockPiece B b ε h)) := by
  apply HasCompactSupport.intro (isCompact_quadraticBlockDomain hB hb)
  intro x hx
  by_contra hz
  exact hx (tsupport_iteratedDeriv_rayQuadraticBlockPiece_subset (by linarith) b j ε h
    (subset_closure hz))

/-- The genuine one-ray energy has the same local constant as the proved
two-ray bound. Constants precede the sign, block, function and data bound. -/
theorem exists_uniform_rayQuadraticBlock_lintegral_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ), 2 ≤ b →
      ∀ (ε : ℝ), ε^2=1 → ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h →
      ∀ (M : ℝ), 0 ≤ M →
      (∀ s ∈ Icc ((b : ℝ)*B-B/8) (((b : ℝ)+1)*B+B/8),
        ∀ i ≤ k, ‖iteratedDeriv i h s‖ ≤ M) →
      (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*k)) *
        ENNReal.ofReal (‖rayQuadraticBlockPiece B b ε h x‖^2)) +
      (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k (rayQuadraticBlockPiece B b ε h) x‖^2)) ≤
        ENNReal.ofReal (C*B*((b : ℝ)*B)^((k : ℝ)-1/2)*M^2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_quadraticBlock_lintegral_bound k
  refine ⟨C, hC, ?_⟩
  intro B hB b hb ε hε h hh M hM hlocal
  apply le_trans _ (hbound B hB b hb h hh M hM hlocal)
  apply add_le_add
  · apply lintegral_mono
    intro x
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_rayQuadraticBlockPiece_le hB hb hε h 0 x
  · apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (norm_iteratedDeriv_rayQuadraticBlockPiece_le hB hb hε h k x) 2)

/-- The genuine smooth local factor for the exterior sum. The first
three blocks are reserved for a separate physical central interpolant. -/
def exteriorRayBlockFactor (b : ℕ) (ε : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 3 ≤ b then unitBlockTransition (ε*x) • h (x^2) else 0

/-- The actual locally finite exterior interpolating sum on one ray. -/
def exteriorRayBlockSum (B ε : ℝ) (h : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' b : ℕ, quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) x

/-- Every factor in the actual exterior sum is smooth. -/
theorem contDiff_exteriorRayBlockFactor (b : ℕ) (ε : ℝ) {h : ℝ → ℂ}
    {n : ℕ∞} (hh : ContDiff ℝ n h) : ContDiff ℝ n (exteriorRayBlockFactor b ε h) := by
  unfold exteriorRayBlockFactor
  split_ifs
  · exact (contDiff_unitBlockTransition.comp (by fun_prop)).smul (hh.comp (by fun_prop))
  · exact contDiff_const

/-- The cutoff factorization agrees exactly with the selected exterior
ray piece, with the finite central indices identically zero. -/
theorem quadraticBlockPiece_exteriorRayBlockFactor (B ε : ℝ) (b : ℕ) (h : ℝ → ℂ) :
    quadraticBlockPiece B b (exteriorRayBlockFactor b ε h) =
      if 3 ≤ b then rayQuadraticBlockPiece B b ε h else (fun _ => 0) := by
  funext x
  unfold exteriorRayBlockFactor
  split_ifs <;> simp [quadraticBlockPiece, rayQuadraticBlockPiece, mul_comm, mul_assoc]

/-- The actual exterior sum is smooth by local finiteness on physical
space, without any global growth bound on the chosen polynomials. -/
theorem contDiff_exteriorRayBlockSum {B : ℝ} (hB : 0 < B) (ε : ℝ)
    (h : ℕ → ℝ → ℂ) {n : ℕ∞} (hh : ∀ b, ContDiff ℝ n (h b)) :
    ContDiff ℝ n (exteriorRayBlockSum B ε h) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let I : ℕ → Set ℝ := fun b => quadraticBlockDomain B b
  have hloc : LocallyFinite I :=
    (locallyFinite_blockCutoff_intervals hB).preimage_continuous (by fun_prop)
  let S : Finset ℕ := (hloc.point_finite x).toFinset
  have hnear := hloc.eventually_subset (fun _ => isClosed_Icc.preimage (by fun_prop)) x
  have heq : exteriorRayBlockSum B ε h =ᶠ[𝓝 x]
      (fun y => ∑ b ∈ S, quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) y) := by
    filter_upwards [hnear] with y hy
    apply tsum_eq_sum
    intro b hb
    by_contra hz
    have hI : y ∈ I b := tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b 0 _
      (subset_closure (by simpa only [iteratedDeriv_zero, Function.mem_support] using hz))
    exact hb (by simpa only [S, Set.Finite.mem_toFinset] using hy hI)
  exact (ContDiffAt.sum (fun b _ =>
    (contDiff_quadraticBlockPiece B b (contDiff_exteriorRayBlockFactor b ε (hh b))).contDiffAt)).congr_of_eventuallyEq heq

/-- The exterior cutoffs sum to exactly the third block transition. -/
theorem hasSum_exteriorBlockCutoff (B s : ℝ) :
    HasSum (fun b : ℕ => if 3 ≤ b then blockCutoff B b s else 0) (blockTransition B 3 s) := by
  let g : ℕ → ℝ := fun b => if 3 ≤ b then blockCutoff B b s else 0
  have hf : Summable (fun b => blockCutoff B b s) := by
    simpa only [Nat.zero_add] using (hasSum_blockCutoff B 0 s).summable
  have hg : Summable g := hf.of_nonneg_of_le
    (fun b => by dsimp only [g]; split_ifs; exact (blockCutoff_mem_Icc B b s).1; exact le_rfl)
    (fun b => by dsimp only [g]; split_ifs; exact le_rfl; exact (blockCutoff_mem_Icc B b s).1)
  have hzero : ∑ b ∈ Finset.range 3, g b = 0 := by norm_num [g, Finset.sum_range_succ]
  have htail : (fun n : ℕ => g (n+3)) = fun n => blockCutoff B (3+n) s := by
    funext n
    simp [g, Nat.add_comm]
  have heq : ∑' b : ℕ, g b = blockTransition B 3 s := by
    rw [← hg.sum_add_tsum_nat_add 3, hzero, zero_add, htail, (hasSum_blockCutoff B 3 s).tsum_eq]
  exact heq ▸ hg.hasSum

/-- The actual exterior sum retains a prescribed value whenever every
active local polynomial has that value. Both the ray and central transition
factors remain explicit until the corresponding regions are selected. -/
theorem exteriorRayBlockSum_eq_of_active_values (B ε : ℝ) (h : ℕ → ℝ → ℂ)
    (x : ℝ) (v : ℂ)
    (hactive : ∀ b, 3 ≤ b → blockCutoff B b (x^2) ≠ 0 → h b (x^2) = v) :
    exteriorRayBlockSum B ε h x =
      unitBlockTransition (ε*x) • (blockTransition B 3 (x^2) • v) := by
  have heq (b : ℕ) : quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) x =
      (if 3 ≤ b then blockCutoff B b (x^2) else 0) • (unitBlockTransition (ε*x) • v) := by
    by_cases hb : 3 ≤ b
    · by_cases hz : blockCutoff B b (x^2)=0
      · simp [quadraticBlockPiece, exteriorRayBlockFactor, hb, hz]
      · simp [quadraticBlockPiece, exteriorRayBlockFactor, hb, hactive b hb hz]
    · simp [quadraticBlockPiece, exteriorRayBlockFactor, hb]
  simp only [exteriorRayBlockSum, heq,
    ((hasSum_exteriorBlockCutoff B (x^2)).smul_const (unitBlockTransition (ε*x) • v)).tsum_eq]
  simp only [smul_smul, mul_comm]

/-- Actual derivatives commute with the locally finite exterior sum.
No summability of a formal derivative series is an input. -/
theorem iteratedDeriv_exteriorRayBlockSum {B : ℝ} (hB : 0 < B)
    (ε : ℝ) (h : ℕ → ℝ → ℂ) (j : ℕ) (hh : ∀ b, ContDiff ℝ j (h b)) (x : ℝ) :
    iteratedDeriv j (exteriorRayBlockSum B ε h) x =
      ∑' b : ℕ, iteratedDeriv j
        (quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b))) x :=
  iteratedDeriv_tsum_quadraticBlockPiece hB _ j
    (fun b => contDiff_exteriorRayBlockFactor b ε (hh b)) x

/-- The actual weighted value and derivative energy of the exterior sum
is bounded by three times the sum of its local energies, even when the
right-hand side is infinite. -/
theorem lintegral_exteriorRayBlockSum_le {B : ℝ} (hB : 0 < B)
    (ε : ℝ) (h : ℕ → ℝ → ℂ) (k : ℕ) (hh : ∀ b, ContDiff ℝ k (h b)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*k)) * ENNReal.ofReal (‖exteriorRayBlockSum B ε h x‖^2)) +
      (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k (exteriorRayBlockSum B ε h) x‖^2)) ≤
      3 * ∑' b : ℕ,
        ((∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*k)) * ENNReal.ofReal
          (‖quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) x‖^2)) +
         (∫⁻ x : ℝ, ENNReal.ofReal
          (‖iteratedDeriv k (quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b))) x‖^2))) := by
  have hv := lintegral_iteratedDeriv_tsum_quadraticBlockPiece_le hB
    (fun b => exteriorRayBlockFactor b ε (h b)) 0
    (fun b => (contDiff_exteriorRayBlockFactor b ε (hh b)).of_le (by simp))
    (fun x => ENNReal.ofReal (|x|^(2*k))) (by fun_prop)
  have hd := lintegral_iteratedDeriv_tsum_quadraticBlockPiece_le hB
    (fun b => exteriorRayBlockFactor b ε (h b)) k
    (fun b => contDiff_exteriorRayBlockFactor b ε (hh b))
    (fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [iteratedDeriv_zero, one_mul] at hv hd
  apply (add_le_add hv hd).trans_eq
  rw [← mul_add, ENNReal.tsum_add]

/-- Genuine local derivative estimates give the global exterior energy
bound with no additional power of the block scale. Summability of the
explicit nonnegative data energy is not assumed in the theorem. -/
theorem exists_uniform_exteriorRayBlockSum_lintegral_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (ε : ℝ), ε^2=1 →
      ∀ (h : ℕ → ℝ → ℂ), (∀ b, ContDiff ℝ ∞ (h b)) →
      ∀ M : ℕ → ℝ, (∀ b, 0 ≤ M b) →
      (∀ b : ℕ, 3 ≤ b → ∀ s ∈ Icc ((b : ℝ)*B-B/8) (((b : ℝ)+1)*B+B/8),
        ∀ i ≤ k, ‖iteratedDeriv i (h b) s‖ ≤ M b) →
      (∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*k)) * ENNReal.ofReal (‖exteriorRayBlockSum B ε h x‖^2)) +
      (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k (exteriorRayBlockSum B ε h) x‖^2)) ≤
        ENNReal.ofReal (3*C*B) * ∑' b : ℕ,
          if 3 ≤ b then ENNReal.ofReal (((b : ℝ)*B)^((k : ℝ)-1/2)*(M b)^2) else 0 := by
  obtain ⟨C, hC, hlocal⟩ := exists_uniform_rayQuadraticBlock_lintegral_bound k
  refine ⟨C, hC, ?_⟩
  intro B hB ε hε h hh M hM hbound
  apply (lintegral_exteriorRayBlockSum_le (by linarith) ε h k
    (fun b => (hh b).of_le (by simp))).trans
  have hp (b : ℕ) :
      ((∫⁻ x : ℝ, ENNReal.ofReal (|x|^(2*k)) * ENNReal.ofReal
        (‖quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) x‖^2)) +
       (∫⁻ x : ℝ, ENNReal.ofReal
        (‖iteratedDeriv k (quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b))) x‖^2))) ≤
      ENNReal.ofReal (C*B) *
        (if 3 ≤ b then ENNReal.ofReal (((b : ℝ)*B)^((k : ℝ)-1/2)*(M b)^2) else 0) := by
    rw [quadraticBlockPiece_exteriorRayBlockFactor]
    split_ifs with hb
    · apply (hlocal B hB b (by omega) ε hε (h b) (hh b) (M b) (hM b) (hbound b hb)).trans_eq
      rw [← ENNReal.ofReal_mul (mul_nonneg hC.le (by linarith))]
      congr 1
      ring
    · simp
  calc
    _ ≤ 3 * ∑' b : ℕ, ENNReal.ofReal (C*B) *
        (if 3 ≤ b then ENNReal.ofReal (((b : ℝ)*B)^((k : ℝ)-1/2)*(M b)^2) else 0) :=
      mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hp)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ← mul_assoc, ← ENNReal.ofReal_ofNat 3,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 2
      ring

end

end MeyerGeneralProblem
