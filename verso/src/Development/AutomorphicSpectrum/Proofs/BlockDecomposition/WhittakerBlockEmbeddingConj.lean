import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Conj

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[dif_pos h]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_` and prove the remaining obligations.

Introduce `a ha`. Establish `ha' : ¬ (a : ℕ) < j` using `fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩`. Establish `hne : i ≠ a` using `fun e => ha' (e ▸ h)`. Simplify using `[blkEmb, ha', hne]`. Introduce `k`.

Simplify using `[blkEmb, h]`. Rewrite using `[dif_neg h, Finset.sum_eq_single i]`. Simplify using `[blkEmb, h]`. Introduce `a _ ha`. Simplify using `[blkEmb, h, Ne.symm ha]`.

Simplify using the standard rewrite rules.
-/
theorem blkEmb_mul_apply {d j : ℕ} (hj : j ≤ d) (A : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (blkEmb K d j A * M) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : i ≠ a := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single i]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, Ne.symm ha]
    · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `h : (l : ℕ) < j`. Rewrite using `[dif_pos h]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_` and prove the remaining obligations.

Introduce `a ha`. Establish `ha' : ¬ (a : ℕ) < j` using `fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩`. Establish `hne : a ≠ l` using `fun e => ha' (e ▸ h)`. Simplify using `[blkEmb, ha', hne]`. Introduce `k`.

Simplify using `[blkEmb, h]`. Rewrite using `[dif_neg h, Finset.sum_eq_single l]`. Simplify using `[blkEmb, h]`. Introduce `a _ ha`. Simplify using `[blkEmb, h, ha]`.

Simplify using the standard rewrite rules.
-/
theorem mul_blkEmb_apply {d j : ℕ} (hj : j ≤ d) (B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (M * blkEmb K d j B) i l =
      if h : (l : ℕ) < j then ∑ k : Fin j, M i (Fin.castLE hj k) * B k ⟨l, h⟩ else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (l : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : a ≠ l := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single l]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, ha]
    · simp

/- English proof (translation)
Rewrite using `[mul_blkEmb_apply hj, dif_neg (not_lt.2 hl), blkEmb_mul_apply hj]`.
-/
theorem conj_apply_ge {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) (hl : j ≤ (l : ℕ)) :
    (blkEmb K d j A * M * blkEmb K d j B) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [mul_blkEmb_apply hj, dif_neg (not_lt.2 hl), blkEmb_mul_apply hj]

/- English proof (translation)
Rewrite using `[mul_blkEmb_apply hj, dif_pos hl]`. Repeatedly rewrite using `[blkEmb_mul_apply hj]`. Distinguish the cases in `h : (i : ℕ) < j`. Simplify using `only [dif_pos h]`. Establish `inner : ∀ k : Fin j, ∑ m : Fin j, A ⟨i, h⟩ m * M (Fin.castLE hj m) (Fin.castLE hj k) = A ⟨i, h⟩ k`.

Introduce `k`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[hM _ _ (by simp)]`. Simplify using the standard rewrite rules. Introduce `m _ hm`.

Rewrite using `[hM _ _ (by simp), if_neg (fun e => hm (Fin.castLE_injective hj e))]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Repeatedly rewrite using `[inner]`. Use `congrFun (congrFun hAB ⟨i, h⟩) ⟨l, hl⟩` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this, Matrix.one_apply]`. Distinguish the cases in `e : i = l`. Simplify using `[e]`. Establish `e' : ¬ ((⟨i, h⟩ : Fin j) = ⟨l, hl⟩)` using `fun q => e (Fin.ext (by simpa using q))`.

Simplify using `[e, e']`. Simplify using `only [dif_neg h]`. Establish `hne : i ≠ l` using `fun e => h (e ▸ hl)`. Rewrite using `[if_neg hne]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Establish `hk : i ≠ Fin.castLE hj k` using `fun e => h (by rw [e]; simp)`. Rewrite using `[hM _ _ (by simp), if_neg hk]`. Simplify using the standard rewrite rules.
-/
theorem conj_apply_lt {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) (hAB : A * B = 1)
    (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ i l : Fin d, (l : ℕ) < j → M i l = if i = l then 1 else 0)
    (i l : Fin d) (hl : (l : ℕ) < j) :
    (blkEmb K d j A * M * blkEmb K d j B) i l = if i = l then 1 else 0 := by
  rw [mul_blkEmb_apply hj, dif_pos hl]
  simp_rw [blkEmb_mul_apply hj]
  by_cases h : (i : ℕ) < j
  · simp only [dif_pos h]
    have inner : ∀ k : Fin j, ∑ m : Fin j, A ⟨i, h⟩ m * M (Fin.castLE hj m) (Fin.castLE hj k)
        = A ⟨i, h⟩ k := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [hM _ _ (by simp)]
        simp
      · intro m _ hm
        rw [hM _ _ (by simp), if_neg (fun e => hm (Fin.castLE_injective hj e))]
        simp
      · simp
    simp_rw [inner]
    have := congrFun (congrFun hAB ⟨i, h⟩) ⟨l, hl⟩
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
    by_cases e : i = l
    · simp [e]
    · have e' : ¬ ((⟨i, h⟩ : Fin j) = ⟨l, hl⟩) := fun q => e (Fin.ext (by simpa using q))
      simp [e, e']
  · simp only [dif_neg h]
    have hne : i ≠ l := fun e => h (e ▸ hl)
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : i ≠ Fin.castLE hj k := fun e => h (by rw [e]; simp)
    rw [hM _ _ (by simp), if_neg hk]
    simp

/- English proof (translation)
Distinguish the cases in `e : i = l`. Rewrite using `[if_pos e]`. Conclude with `(hu i l).1 e`. Rewrite using `[if_neg e]`. Conclude with `(hu i l).2 e (fun c => absurd c.2 (not_le.2 hl))`.
-/
theorem col_lt {d j : ℕ} {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) (i l : Fin d)
    (hl : (l : ℕ) < j) : (u : Matrix (Fin d) (Fin d) K) i l = if i = l then 1 else 0 := by
  by_cases e : i = l
  · rw [if_pos e]
    exact (hu i l).1 e
  · rw [if_neg e]
    exact (hu i l).2 e (fun c => absurd c.2 (not_le.2 hl))

/- English proof (translation)
Establish `hgg : (g : Matrix (Fin j) (Fin j) K) * ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) * blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K)`. Rewrite using `[Units.val_mul, Units.val_mul, h1, h2]`. Introduce `i l`.

Rewrite using `[key]`. Distinguish the cases in `hl : (l : ℕ) < j`. Rewrite using `[conj_apply_lt hj _ _ hgg _ (fun a b hb => col_lt hu a b hb) i l hl]`. Conclude with `⟨fun e => if_pos e, fun e _ => if_neg e⟩`. Establish `hl' : j ≤ (l : ℕ)` using `not_lt.1 hl`.

Rewrite using `[conj_apply_ge hj _ _ _ i l hl']`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `hi : ¬ (i : ℕ) < j` using `by rw [e]; exact hl`. Rewrite using `[dif_neg hi]`.

Conclude with `(hu i l).1 e`. Introduce `e hc`. Establish `hlt : ¬ i < l` using `fun q => hc ⟨q, hl'⟩`. Establish `hi : ¬ (i : ℕ) < j` using `fun q => hlt (by`. Rewrite using `[Fin.lt_def]`.

Use the proof step `omega)`. Rewrite using `[dif_neg hi]`. Conclude with `(hu i l).2 e (fun c => hlt c.1)`.
-/
theorem conj_mem {d j : ℕ} (hj : j ≤ d) (g : GL (Fin j) K) (h : GL (Fin d) K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) :
    h * u * h⁻¹ ∈ patSet K (colGe d j) := by
  have hgg : (g : Matrix (Fin j) (Fin j) K) * ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
    rw [Units.val_mul, Units.val_mul, h1, h2]
  intro i l
  rw [key]
  by_cases hl : (l : ℕ) < j
  · rw [conj_apply_lt hj _ _ hgg _ (fun a b hb => col_lt hu a b hb) i l hl]
    exact ⟨fun e => if_pos e, fun e _ => if_neg e⟩
  · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
    rw [conj_apply_ge hj _ _ _ i l hl']
    constructor
    · intro e
      have hi : ¬ (i : ℕ) < j := by rw [e]; exact hl
      rw [dif_neg hi]
      exact (hu i l).1 e
    · intro e hc
      have hlt : ¬ i < l := fun q => hc ⟨q, hl'⟩
      have hi : ¬ (i : ℕ) < j := fun q => hlt (by
        rw [Fin.lt_def]; omega)
      rw [dif_neg hi]
      exact (hu i l).2 e (fun c => hlt c.1)

/- English proof (translation)
Simplify using `only [colGeR, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hj.le) (Fin.castLE_injective hj.le) _ _ ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Establish `ha' : ¬ (a : ℕ) < j` using `fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Simplify using `[ha']`. Introduce `k`. Rewrite using `[Finset.sum_eq_single (⟨j, hj⟩ : Fin d)]`.

Simplify using the standard rewrite rules. Introduce `l _ hl`. Establish `: ¬ (l : ℕ) = j` using `fun e => hl (Fin.ext e)`. Simplify using `[this]`. Simplify using the standard rewrite rules.
-/
theorem sum_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i, ∑ l, colGeR K d j r i l * M i l =
      ∑ i, ∑ l, colGeE K d (j + 1) i l * M i l +
        ∑ k : Fin j, r k * M (Fin.castLE hj.le k) ⟨j, hj⟩ := by
  simp only [colGeR, add_mul, Finset.sum_add_distrib]
  congr 1
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj.le) (Fin.castLE_injective hj.le) _ _ ?_ ?_
  · intro a ha
    have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [ha']
  · intro k
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin d)]
    · simp
    · intro l _ hl
      have : ¬ (l : ℕ) = j := fun e => hl (Fin.ext e)
      simp [this]
    · simp

/- English proof (translation)
Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `c : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)`. Rewrite using `[hXU i l (by omega) (by omega)]`. Establish `e : colGeE K d (j + 1) i l = 0` using `if_neg c`. Rewrite using `[e, zero_mul, zero_mul]`.
-/
theorem sum_colGeE_congr {d j : ℕ} (X U : Matrix (Fin d) (Fin d) K)
    (hXU : ∀ i l : Fin d, j ≤ (i : ℕ) → j ≤ (l : ℕ) → X i l = U i l) :
    ∑ i, ∑ l, colGeE K d (j + 1) i l * X i l = ∑ i, ∑ l, colGeE K d (j + 1) i l * U i l := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases c : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)
  · rw [hXU i l (by omega) (by omega)]
  · have e : colGeE K d (j + 1) i l = 0 := if_neg c
    rw [e, zero_mul, zero_mul]

/- English proof (translation)
Establish `key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) * blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K)`. Rewrite using `[Units.val_mul, Units.val_mul, h1, h2]`. Unfold `patChar`. Use `congr 1`. Rewrite using `[sum_colGeR hj, sum_colGeR hj, key]`.

Use `congr 1`. Use `sum_colGeE_congr _ _ fun i l hi hl => ?_` and prove the remaining obligations. Rewrite using `[conj_apply_ge hj.le _ _ _ i l hl, dif_neg (not_lt.2 hi)]`. Establish `: ∀ k : Fin j, (blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) * blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K)) (Fin.castLE hj.le k) ⟨j, hj⟩ = ∑ m : Fin j, (g : Matrix (Fin j) (Fin j) K) k m * (u : Matrix (Fin d) (Fin d) K) (Fin.cast …`. Introduce `k`.

Rewrite using `[conj_apply_ge hj.le _ _ _ _ _ (le_refl j), dif_pos (by simp)]`. Both sides reduce to the same expression. Repeatedly rewrite using `[this, Finset.mul_sum, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem patChar_conj {d j : ℕ} (hj : j < d) (ψ₀ : AddChar K ℂ) (g : GL (Fin j) K)
    (h : GL (Fin d) K) (r : Fin j → K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ (h * u * h⁻¹) =
      patChar (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ u := by
  have key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
    rw [Units.val_mul, Units.val_mul, h1, h2]
  unfold patChar
  congr 1
  rw [sum_colGeR hj, sum_colGeR hj, key]
  congr 1
  · refine sum_colGeE_congr _ _ fun i l hi hl => ?_
    rw [conj_apply_ge hj.le _ _ _ i l hl, dif_neg (not_lt.2 hi)]
  · have : ∀ k : Fin j, (blkEmb K d j (g : Matrix (Fin j) (Fin j) K) *
        (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K)) (Fin.castLE hj.le k) ⟨j, hj⟩
        = ∑ m : Fin j, (g : Matrix (Fin j) (Fin j) K) k m *
          (u : Matrix (Fin d) (Fin d) K) (Fin.castLE hj.le m) ⟨j, hj⟩ := by
      intro k
      rw [conj_apply_ge hj.le _ _ _ _ _ (le_refl j), dif_pos (by simp)]
      rfl
    simp_rw [this, Finset.mul_sum, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring

/- English proof (translation)
Introduce `K _ _ _ d j ψ₀ χ g h r hj hχ h1 h2`. Establish `hN : ∀ u : GL (Fin d) K, h * u * h⁻¹ ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j)`. Introduce `u`. Use `⟨fun hu => ?_, conj_mem hj.le g h h1 h2⟩` and prove the remaining obligations. Use `conj_mem hj.le g⁻¹ h⁻¹ h2 (by rw [inv_inv, inv_inv]; exact h1) hu` as an intermediate fact.

Establish `e : h⁻¹ * (h * u * h⁻¹) * (h⁻¹)⁻¹ = u` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Unfold `wh`. Use `congr 1`. Rewrite using `[← Equiv.sum_comp (MulAut.conj h).toEquiv]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Establish `e : (MulAut.conj h).toEquiv u = h * u * h⁻¹` using `rfl`. Rewrite using `[e]`. Distinguish the cases in `hu : u ∈ patSet K (colGe d j)`. Rewrite using `[if_pos ((hN u).2 hu), if_pos hu, patChar_conj hj ψ₀ g h r h1 h2 u, hχ]`.

Rewrite using `[if_neg (fun q => hu ((hN u).1 q)), if_neg hu]`.
-/
theorem wh_colGeR_conj : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  intro K _ _ _ d j ψ₀ χ g h r hj hχ h1 h2
  have hN : ∀ u : GL (Fin d) K, h * u * h⁻¹ ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j) := by
    intro u
    refine ⟨fun hu => ?_, conj_mem hj.le g h h1 h2⟩
    have := conj_mem hj.le g⁻¹ h⁻¹ h2 (by rw [inv_inv, inv_inv]; exact h1) hu
    have e : h⁻¹ * (h * u * h⁻¹) * (h⁻¹)⁻¹ = u := by group
    rwa [e] at this
  unfold wh
  congr 1
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e : (MulAut.conj h).toEquiv u = h * u * h⁻¹ := rfl
  rw [e]
  by_cases hu : u ∈ patSet K (colGe d j)
  · rw [if_pos ((hN u).2 hu), if_pos hu, patChar_conj hj ψ₀ g h r h1 h2 u, hχ]
  · rw [if_neg (fun q => hu ((hN u).1 q)), if_neg hu]

end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
