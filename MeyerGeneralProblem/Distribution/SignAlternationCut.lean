module

public import MeyerGeneralProblem.Distribution.SplineSignAlternations
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# The first sign change of a real function

When the number of sign alternations is finite and positive, a linear
factor with its root at the end of the first sign interval removes one
alternation. The argument uses ordered samples and allows zero intervals
and sign jumps.
-/

namespace MeyerGeneralProblem

open Filter Set
open scoped Topology

private theorem alternating_cons {f : ℝ → ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {a : ℝ}
    (hMono : StrictMono x) (hAlt : ∀ i : Fin n, f (x i.castSucc) * f (x i.succ) < 0)
    (hBefore : a < x 0) (hSign : f a * f (x 0) < 0) :
    StrictMono (Fin.cons a x : Fin (n + 2) → ℝ) ∧
      ∀ i : Fin (n + 1), f ((Fin.cons a x : Fin (n + 2) → ℝ) i.castSucc) *
        f ((Fin.cons a x : Fin (n + 2) → ℝ) i.succ) < 0 := by
  refine ⟨Fin.strictMono_cons.mpr ⟨fun i => hBefore.trans_le (hMono.monotone (Fin.zero_le i)), hMono⟩, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hSign
  · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hAlt j

/-- A nonempty sampling set witnesses zero sign alternations. -/
theorem hasSignAlternations_zero_of_nonempty {f : ℝ → ℝ} {U : Set ℝ} (h : U.Nonempty) :
    HasSignAlternations f U 0 := by
  obtain ⟨x, hx⟩ := h
  let X : Fin 1 → ℝ := fun _ => x
  have hX : StrictMono X := fun i j hij => False.elim ((ne_of_lt hij) (Subsingleton.elim i j))
  exact ⟨X, hX, fun _ => hx, fun i => Fin.elim0 i⟩

/-- Discarding the first sample preserves the remaining alternations. -/
theorem HasSignAlternations.drop_first {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}
    (h : HasSignAlternations f U (n + 1)) : HasSignAlternations f U n := by
  obtain ⟨x, hx, hMem, hAlt⟩ := h
  refine ⟨fun i => x i.succ, hx.comp (fun _ _ hij => Nat.succ_lt_succ hij), fun i => hMem i.succ, fun i => ?_⟩
  simpa only [Fin.castSucc_succ] using hAlt i.succ

/-- Multiplication by a strictly positive function preserves sign alternations. -/
theorem hasSignAlternations_pos_mul_iff {f w : ℝ → ℝ} {U : Set ℝ} {n : ℕ}
    (hw : ∀ x ∈ U, 0 < w x) :
    HasSignAlternations (fun x => w x * f x) U n ↔ HasSignAlternations f U n := by
  constructor <;> rintro ⟨x, hMono, hMem, hAlt⟩
  · refine ⟨x, hMono, hMem, fun i => ?_⟩
    have h := hAlt i
    rw [mul_mul_mul_comm] at h
    exact (mul_neg_iff.mp h).resolve_right
      (fun h' => (not_lt_of_ge (mul_nonneg (hw _ (hMem _)).le (hw _ (hMem _)).le)) h'.1) |>.2
  · refine ⟨x, hMono, hMem, fun i => ?_⟩
    rw [mul_mul_mul_comm]
    exact mul_neg_of_pos_of_neg (mul_pos (hw _ (hMem _)) (hw _ (hMem _))) (hAlt i)

/-- Reversing every sign preserves sign alternations. -/
theorem hasSignAlternations_neg_iff {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} :
    HasSignAlternations (fun x => -f x) U n ↔ HasSignAlternations f U n := by
  constructor <;> rintro ⟨x, hMono, hMem, hAlt⟩ <;>
    exact ⟨x, hMono, hMem, fun i => by simpa only [neg_mul_neg] using hAlt i⟩

private theorem hasSignAlternations_one_of_opposite_pair {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hs : f a * f b < 0) : HasSignAlternations f univ 1 := by
  let x : Fin 1 → ℝ := fun _ => b
  have hx : StrictMono x := fun i j h => False.elim ((ne_of_lt h) (Subsingleton.elim i j))
  have hAlt := alternating_cons hx (fun i : Fin 0 => Fin.elim0 i) (show a < x 0 from hab)
    (show f a * f (x 0) < 0 from hs)
  exact ⟨_, hAlt.1, fun _ => mem_univ _, hAlt.2⟩

/-- A function with no sign alternation on the real line has constant weak sign. -/
theorem forall_nonneg_or_forall_nonpos_of_no_signAlternations {f : ℝ → ℝ}
    (h : ¬ HasSignAlternations f univ 1) : (∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0) := by
  by_cases hPos : ∃ x, 0 < f x
  · obtain ⟨a, ha⟩ := hPos
    left
    intro b
    by_contra! hb
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact h (hasSignAlternations_one_of_opposite_pair hab (mul_neg_of_pos_of_neg ha hb))
    · exact (not_lt_of_ge ha.le) hb
    · exact h (hasSignAlternations_one_of_opposite_pair hba (mul_neg_of_neg_of_pos hb ha))
  · exact Or.inr fun x => le_of_not_gt (fun hx => hPos ⟨x, hx⟩)

private theorem exists_sub_mul_removes_first_sign_change_of_positive
    (f : ℝ → ℝ) (n : ℕ) (x : Fin (n + 2) → ℝ) (hx : StrictMono x)
    (hAlt : ∀ i : Fin (n + 1), f (x i.castSucc) * f (x i.succ) < 0)
    (hFirst : 0 < f (x 0)) (hBound : ¬ HasSignAlternations f univ (n + 2)) :
    ∃ a : ℝ, ¬ HasSignAlternations (fun t => (t - a) * f t) univ (n + 1) := by
  have h01 : (0 : Fin (n + 2)) < 1 := Fin.castSucc_lt_succ (i := (0 : Fin (n + 1)))
  let b := x 1
  have hb : f b < 0 := by
    have h := hAlt 0
    change f (x 0) * f b < 0 at h
    exact ((mul_neg_iff.mp h).resolve_right (fun hs => (not_lt_of_ge hFirst.le) hs.1)).2
  let P := {t : ℝ | t < b ∧ 0 < f t}
  have hP : P.Nonempty := ⟨x 0, hx h01, hFirst⟩
  have hPB : BddAbove P := ⟨b, fun _ ht => ht.1.le⟩
  let a := sSup P
  have hAb : a ≤ b := csSup_le hP (fun _ ht => ht.1.le)
  have hBefore : x 0 ≤ a := le_csSup hPB ⟨hx h01, hFirst⟩
  have hBelow (t : ℝ) (ht : t < a) : 0 ≤ f t := by
    by_contra! hNeg
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hPB hP).mp ht
    let X : Fin (n + 1) → ℝ := fun i => x i.succ
    have hX : StrictMono X := hx.comp (fun _ _ hij => Nat.succ_lt_succ hij)
    have hXS (i : Fin n) : f (X i.castSucc) * f (X i.succ) < 0 := by
      simpa only [X, Fin.castSucc_succ] using hAlt i.succ
    have hSX : s < X 0 := hs.1
    have hS := alternating_cons hX hXS hSX (mul_neg_of_pos_of_neg hs.2 hb)
    have hT := alternating_cons (a := t) hS.1 hS.2
      (by simpa only [Fin.cons_zero] using hts)
      (by simpa only [Fin.cons_zero] using mul_neg_of_neg_of_pos hNeg hs.2)
    exact hBound ⟨_, hT.1, fun _ => mem_univ _, hT.2⟩
  let g (t : ℝ) := (t - a) * f t
  have hNonpos (t : ℝ) (ht : t ≤ b) : g t ≤ 0 := by
    rcases lt_trichotomy t a with hf | rfl | hf
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hf.le) (hBelow t hf)
    · simp [g]
    · have hfn : f t ≤ 0 := by
        rcases lt_or_eq_of_le ht with ht' | rfl
        · by_contra! hp
          exact (not_lt_of_ge (le_csSup hPB ⟨ht', hp⟩)) hf
        · exact hb.le
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hf.le) hfn
  have hSignAbove {u v : ℝ} (hu : a < u) (hv : a < v) (h : g u * g v < 0) :
      f u * f v < 0 := by
    change ((u - a) * f u) * ((v - a) * f v) < 0 at h
    rw [mul_mul_mul_comm] at h
    exact ((mul_neg_iff.mp h).resolve_right fun hs =>
      (not_lt_of_ge (mul_nonneg (sub_nonneg.mpr hu.le) (sub_nonneg.mpr hv.le))) hs.1).2
  have hPosAbove {u : ℝ} (hu : a < u) (h : 0 < g u) : 0 < f u :=
    ((mul_pos_iff.mp h).resolve_right fun hs => (not_lt_of_ge (sub_nonneg.mpr hu.le)) hs.1).2
  have hNegAbove {u : ℝ} (hu : a < u) (h : g u < 0) : f u < 0 :=
    ((mul_neg_iff.mp h).resolve_right fun hs => (not_lt_of_ge (sub_nonneg.mpr hu.le)) hs.1).2
  refine ⟨a, ?_⟩
  rintro ⟨y, hy, _, hYAlt⟩
  have hY01 : y 0 < y 1 := hy h01
  have hFirstY := hYAlt 0
  change g (y 0) * g (y 1) < 0 at hFirstY
  have hY1 : b < y 1 := by
    by_contra! hle
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos
      (hNonpos _ (hY01.le.trans hle)) (hNonpos _ hle))) hFirstY
  have hYsigns (hY0 : a < y 0) (i : Fin (n + 1)) : f (y i.castSucc) * f (y i.succ) < 0 :=
    hSignAbove (hY0.trans_le (hy.monotone (Fin.zero_le _)))
      (hY0.trans_le (hy.monotone (Fin.zero_le _))) (hYAlt i)
  rcases mul_neg_iff.mp hFirstY with ⟨hPositive, hNegative⟩ | ⟨hNegative, hPositive⟩
  · have hBy : b < y 0 := by
      by_contra! hle
      exact (not_lt_of_ge (hNonpos _ hle)) hPositive
    have hAbove := hAb.trans_lt hBy
    have h := alternating_cons hy (hYsigns hAbove) hBy (mul_neg_of_neg_of_pos hb (hPosAbove hAbove hPositive))
    exact hBound ⟨_, h.1, fun _ => mem_univ _, h.2⟩
  · rcases lt_or_ge a (y 0) with hAbove | hLe
    · have h := alternating_cons hy (hYsigns hAbove) (hBefore.trans_lt hAbove)
        (mul_neg_of_pos_of_neg hFirst (hNegAbove hAbove hNegative))
      exact hBound ⟨_, h.1, fun _ => mem_univ _, h.2⟩
    · let Y : Fin (n + 1) → ℝ := fun i => y i.succ
      have hY : StrictMono Y := hy.comp (fun _ _ hij => Nat.succ_lt_succ hij)
      have hAbove : a < Y 0 := hAb.trans_lt hY1
      have hYS (i : Fin n) : f (Y i.castSucc) * f (Y i.succ) < 0 := by
        apply hSignAbove (hAbove.trans_le (hY.monotone (Fin.zero_le _)))
          (hAbove.trans_le (hY.monotone (Fin.zero_le _)))
        simpa only [Y, Fin.castSucc_succ] using hYAlt i.succ
      have hB := alternating_cons hY hYS (show b < Y 0 from hY1)
        (mul_neg_of_neg_of_pos hb (hPosAbove hAbove hPositive))
      have hX := alternating_cons (a := x 0) hB.1 hB.2
        (by simpa only [Fin.cons_zero] using hx h01)
        (by simpa only [Fin.cons_zero] using mul_neg_of_pos_of_neg hFirst hb)
      exact hBound ⟨_, hX.1, fun _ => mem_univ _, hX.2⟩

/-- If there are exactly `n + 1` sign alternations, multiplication by a
linear function can reduce the count to at most `n`. -/
theorem exists_sub_mul_removes_first_sign_change (f : ℝ → ℝ) (n : ℕ)
    (hExists : HasSignAlternations f univ (n + 1))
    (hBound : ¬ HasSignAlternations f univ (n + 2)) :
    ∃ a : ℝ, ¬ HasSignAlternations (fun t => (t - a) * f t) univ (n + 1) := by
  obtain ⟨x, hx, _, hAlt⟩ := hExists
  have h := hAlt 0
  change f (x 0) * f (x 1) < 0 at h
  rcases mul_neg_iff.mp h with ⟨hPos, _⟩ | ⟨hNeg, _⟩
  · exact exists_sub_mul_removes_first_sign_change_of_positive f n x hx hAlt hPos hBound
  · have hBound' : ¬ HasSignAlternations (fun t => -f t) univ (n + 2) :=
      fun h' => hBound (hasSignAlternations_neg_iff.mp h')
    obtain ⟨a, ha⟩ := exists_sub_mul_removes_first_sign_change_of_positive
      (fun t => -f t) n x hx (fun i => by simpa only [neg_mul_neg] using hAlt i)
      (neg_pos.mpr hNeg) hBound'
    refine ⟨a, fun h' => ha ?_⟩
    simpa only [mul_neg] using hasSignAlternations_neg_iff.mpr h'

/-- A finite sequence of strict sign alternations persists eventually
under pointwise convergence on its sampling set. -/
theorem HasSignAlternations.eventually_of_pointwise_tendsto
    {ι : Type*} {l : Filter ι} {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {U : Set ℝ} {n : ℕ} (h : HasSignAlternations g U n)
    (hlim : ∀ x ∈ U, Tendsto (fun t => f t x) l (𝓝 (g x))) :
    ∀ᶠ t in l, HasSignAlternations (f t) U n := by
  obtain ⟨x, hx, hMem, hAlt⟩ := h
  have hStrict (i : Fin n) : ∀ᶠ t in l, f t (x i.castSucc) * f t (x i.succ) < 0 :=
    ((hlim _ (hMem i.castSucc)).mul (hlim _ (hMem i.succ))).eventually
      (Iio_mem_nhds (hAlt i))
  filter_upwards [Filter.eventually_all.mpr hStrict] with t hSigns
  exact ⟨x, hx, hMem, hSigns⟩

end MeyerGeneralProblem
