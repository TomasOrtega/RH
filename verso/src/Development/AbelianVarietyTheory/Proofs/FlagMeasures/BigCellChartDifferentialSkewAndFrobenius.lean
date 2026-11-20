import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterizationStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.DNorm

def sw (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

variable {k r : ℕ}

/- English proof (translation)
Unfold `sw`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma sw_val (i : Fin (2 * r + k + 1)) :
    (sw k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sw
  split_ifs <;> rfl

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `hi` using `i.isLt`. Rewrite using `[sw_val, sw_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
lemma sw_sw (i : Fin (2 * r + k + 1)) : sw k r (sw k r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  rw [sw_val, sw_val]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Unfold `sg`. Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> first | rfl | omega`.
-/
lemma sg_sw (i : Fin (2 * r + k + 1)) : sg k r (sw k r i) = sg k r i := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold sg
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Unfold `lev`. Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> omega`.
-/
lemma lev_sw (i : Fin (2 * r + k + 1)) : lev k r (sw k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold lev
  split_ifs at hs <;> split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Unfold `Hpk sg`. Simplify using `only [Fin.ext_iff]`.

Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> first | rfl | omega`.
-/
lemma hpk_apply (i j : Fin (2 * r + k + 1)) : Hpk k r i j = if j = sw k r i then sg k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold Hpk sg
  simp only [Fin.ext_iff]
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Unfold `wC bigCell`. Simplify using `only [esI, Matrix.one_apply, Fin.ext_iff, star_one, inv_one]`.

Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> first | rfl | omega`.
-/
lemma wC_apply (i j : Fin (2 * r + k + 1)) : wC k r i j = if j = sw k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold wC bigCell
  simp only [esI, Matrix.one_apply, Fin.ext_iff, star_one, inv_one]
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `[Matrix.mul_apply, wC_apply]`.
-/
private lemma wC_mul_apply (N : Mat k r) (i j : Fin (2 * r + k + 1)) : (wC k r * N) i j = N (sw k r i) j := by
  simp [Matrix.mul_apply, wC_apply]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]`. Rewrite using `[wC_apply, if_pos (sw_sw j).symm, mul_one]`. Introduce `l _ hl`. Rewrite using `[wC_apply, if_neg, mul_zero]`. Introduce `h`.

Conclude with `hl (by rw [h, sw_sw])`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma mul_wC_apply (N : Mat k r) (i j : Fin (2 * r + k + 1)) : (N * wC k r) i j = N i (sw k r j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]
  · rw [wC_apply, if_pos (sw_sw j).symm, mul_one]
  · intro l _ hl
    rw [wC_apply, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, sw_sw])
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[mul_wC_apply, wC_mul_apply]`.
-/
lemma conj_apply (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sw k r i) (sw k r j) := by
  rw [mul_wC_apply, wC_mul_apply]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]`. Rewrite using `[hpk_apply, if_pos (sw_sw j).symm, sg_sw]`. Introduce `l _ hl`. Rewrite using `[hpk_apply, if_neg, mul_zero]`. Introduce `h`.

Conclude with `hl (by rw [h, sw_sw])`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma mul_Hpk_apply' (N : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (N * Hpk k r) i j = N i (sw k r j) * sg k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]
  · rw [hpk_apply, if_pos (sw_sw j).symm, sg_sw]
  · intro l _ hl
    rw [hpk_apply, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, sw_sw])
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `[Matrix.mul_apply, hpk_apply]`.
-/
private lemma Hpk_mul_apply' (N : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * N) i j = sg k r i * N (sw k r i) j := by
  simp [Matrix.mul_apply, hpk_apply]

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Simplify using `only [Matrix.add_apply, Matrix.zero_apply, mul_Hpk_apply', Hpk_mul_apply', Matrix.conjTranspose_apply]`.
-/
lemma skew_iff (M : Mat k r) : Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
    ∀ i j, star (M (sw k r j) i) * sg k r j + sg k r i * M (sw k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_Hpk_apply', Hpk_mul_apply', Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite `h`, the goal using `[skew_iff]`. Introduce `i j`. Establish `hij` using `h (sw k r i) (sw k r j)`. Simplify using `only [conj_apply, sw_sw, sg_sw] at hij ⊢`. Conclude with `hij`.
-/
lemma skew_conj {M : Mat k r} (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    (wC k r * M * wC k r)ᴴ * Hpk k r + Hpk k r * (wC k r * M * wC k r) = 0 := by
  rw [skew_iff] at h ⊢
  intro i j
  have hij := h (sw k r i) (sw k r j)
  simp only [conj_apply, sw_sw, sg_sw] at hij ⊢
  exact hij

/- English proof (translation)
Unfold `torD`. Conclude with `Matrix.diagonal_apply_ne _ h`.
-/
private lemma torD_apply_of_ne (x : Fin r → ℂ) {i j : Fin (2 * r + k + 1)} (h : i ≠ j) : torD k r x i j = 0 := by
  unfold torD
  exact Matrix.diagonal_apply_ne _ h

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Establish `e2 : 2 * r + k - (2 * r + k - i.val) = i.val` using `by omega`. Unfold `torD`. Simplify using `only [Matrix.diagonal_apply_eq]`.

Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> (try simp only [hs, e2]) <;> (try simp only [star_neg, star_star, neg_neg, star_zero, neg_zero]) <;> first | rfl | omega`.
-/
private lemma torD_sw_sw_eq_neg_star (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) :
    torD k r x (sw k r i) (sw k r i) = -star (torD k r x i i) := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  have e2 : 2 * r + k - (2 * r + k - i.val) = i.val := by omega
  unfold torD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs at hs <;> split_ifs <;> (try simp only [hs, e2]) <;> (try simp only [star_neg, star_star, neg_neg, star_zero, neg_zero]) <;>
    first | rfl | omega

/- English proof (translation)
Rewrite using `[skew_iff]`. Introduce `i j`. Distinguish the cases in `h : j = sw k r i`. Substitute `h` using the available equality. Rewrite using `[sw_sw, sg_sw, torD_sw_sw_eq_neg_star]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h' : sw k r j ≠ i` using `fun e => h (by rw [← e, sw_sw])`. Establish `h'' : sw k r i ≠ j` using `fun e => h e.symm`. Rewrite using `[torD_apply_of_ne x h', torD_apply_of_ne x h'']`. Simplify using the standard rewrite rules.
-/
lemma skew_torD (x : Fin r → ℂ) : (torD k r x)ᴴ * Hpk k r + Hpk k r * torD k r x = 0 := by
  rw [skew_iff]
  intro i j
  by_cases h : j = sw k r i
  · subst h
    rw [sw_sw, sg_sw, torD_sw_sw_eq_neg_star]
    ring
  · have h' : sw k r j ≠ i := fun e => h (by rw [← e, sw_sw])
    have h'' : sw k r i ≠ j := fun e => h e.symm
    rw [torD_apply_of_ne x h', torD_apply_of_ne x h'']
    simp

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]`.

Simplify using `only [unrealify, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

/- English proof (translation)
The claim follows from `norm_unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))`.
-/
lemma norm_um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) :
    ∑ i, ∑ j, ‖um X i j‖ ^ 2 = ‖X‖ ^ 2 :=
  norm_unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hs` using `sw_val (k := k) (r := r) i`. Unfold `torD`. Rewrite using `[Matrix.diagonal_apply_eq]`. Apply the tactic sequence `split_ifs at hs <;> split_ifs <;> (try simp only [hs]) <;> (try simp only [norm_neg, norm_star, norm_zero, add_zero, zero_add]) <;> first | rfl | omega | norm_num`.
-/
private lemma norm_sq_torD_diag_eq (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) :
    ‖torD k r x i i‖ ^ 2 = (if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0) +
      (if h : (sw k r i).val < r then ‖x ⟨(sw k r i).val, h⟩‖ ^ 2 else 0) := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold torD
  rw [Matrix.diagonal_apply_eq]
  split_ifs at hs <;> split_ifs <;> (try simp only [hs]) <;> (try simp only [norm_neg, norm_star, norm_zero, add_zero, zero_add]) <;>
    first | rfl | omega | norm_num

/- English proof (translation)
Establish `hoff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0` using `fun i j h => by`. Unfold `torD`. Conclude with `Matrix.diagonal_apply_ne _ h`. Establish `h1 : ∀ i, ∑ j, ‖torD k r x i j‖ ^ 2 = ‖torD k r x i i‖ ^ 2` using `fun i => by`. Rewrite using `[Finset.sum_eq_single i]`.

Introduce `j _ hj`. Rewrite using `[hoff i j (Ne.symm hj), norm_zero]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Simplify using `only [h1, norm_sq_torD_diag_eq, Finset.sum_add_distrib]`. Establish `hsw : (∑ i : Fin (2 * r + k + 1), if h : (sw k r i).val < r then ‖x ⟨(sw k r i).val, h⟩‖ ^ 2 else 0) = ∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0` using `Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun i => sw_sw i)) (fun i : Fin (2 * r + k + 1) => if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0)`. Establish `hG : (∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0) = ∑ a, ‖x a‖ ^ 2`. Use `(Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) _).trans ?_` and prove the remaining obligations. Rewrite using `[show 2 * r + k + 1 = r + (r + k + 1) by ring, Finset.sum_range_add]`.

Rewrite using `[Finset.sum_eq_zero (s := Finset.range (r + k + 1)) (fun n _ => dif_neg (by omega)), add_zero]`. Use `(Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) r).symm.trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun a _ => dif_pos a.isLt`. Rewrite using `[hsw, hG]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_torD (x : Fin r → ℂ) : ∑ i, ∑ j, ‖torD k r x i j‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  have hoff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0 := fun i j h => by
    unfold torD
    exact Matrix.diagonal_apply_ne _ h
  have h1 : ∀ i, ∑ j, ‖torD k r x i j‖ ^ 2 = ‖torD k r x i i‖ ^ 2 := fun i => by
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hoff i j (Ne.symm hj), norm_zero]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [h1, norm_sq_torD_diag_eq, Finset.sum_add_distrib]
  have hsw : (∑ i : Fin (2 * r + k + 1), if h : (sw k r i).val < r then ‖x ⟨(sw k r i).val, h⟩‖ ^ 2 else 0) =
      ∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0 :=
    Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun i => sw_sw i))
      (fun i : Fin (2 * r + k + 1) => if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0)
  have hG : (∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0) =
      ∑ a, ‖x a‖ ^ 2 := by
    refine (Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) _).trans ?_
    rw [show 2 * r + k + 1 = r + (r + k + 1) by ring, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := Finset.range (r + k + 1)) (fun n _ => dif_neg (by omega)), add_zero]
    refine (Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) r).symm.trans ?_
    exact Finset.sum_congr rfl fun a _ => dif_pos a.isLt
  rw [hsw, hG]
  ring

/- English proof (translation)
Introduce `k r v`. Take `⟨⟨X, X'⟩, ⟨x, Y⟩⟩` from `v`. Establish `hX` using `(GlobalTheory.CellDens.LieN.lieE_Nset k r (X : EuclideanSpace ℝ _)).1.1 X.2`. Establish `hX'` using `(GlobalTheory.CellDens.LieN.lieE_Nset k r (X' : EuclideanSpace ℝ _)).1.1 X'.2`. Establish `hY` using `(GlobalTheory.CellLieAlg.lie_entries k r (Y : EuclideanSpace ℝ _)).2.1.1 Y.2`.

Express the relevant statement in the definitionally equal form `(um X)ᴴ * Hpk k r + Hpk k r * um X = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X i j = 0 at hX`. Express the relevant statement in the definitionally equal form `(um X')ᴴ * Hpk k r + Hpk k r * um X' = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X' i j = 0 at hX'`. Express the relevant statement in the definitionally equal form `(um Y)ᴴ * Hpk k r + Hpk k r * um Y = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → um Y i j = 0 at hY`. Use `show (-(wC k r * um X * wC k r) + torD k r x + um Y + um X')ᴴ * Hpk k r + Hpk k r * (-(wC k r * um X * wC k r) + torD k r x + um Y + um X') = 0 ∧ (∑ i, ∑ j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2) = ‖X‖ ^ 2 + ‖X'‖ ^ 2 + 2 * (∑ a, ‖x a‖ ^ 2) + ‖Y‖ ^ 2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `e : ∀ A T B C : Mat k r, (-A + T + B + C)ᴴ * Hpk k r + Hpk k r * (-A + T + B + C) = -(Aᴴ * Hpk k r + Hpk k r * A) + (Tᴴ * Hpk k r + Hpk k r * T) + (Bᴴ * Hpk k r + Hpk k r * B) + (Cᴴ * Hpk k r + Hpk k r * C)`. Introduce `A T B C`. Simplify using `only [conjTranspose_add, conjTranspose_neg, add_mul, mul_add, neg_mul, mul_neg]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, skew_conj hX.1, skew_torD x, hY.1, hX'.1]`.

Simplify using the standard rewrite rules. Establish `hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → lev k r i = r` using `fun i h => by`. Unfold `lev`. Rewrite using `[if_neg (by omega), if_pos h.2]`. Establish `hToff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0` using `fun i j h => by`.

Unfold `torD`. Conclude with `Matrix.diagonal_apply_ne _ h`. Establish `hTmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → torD k r x i i = 0` using `fun i h => by`. Unfold `torD`. Rewrite using `[Matrix.diagonal_apply_eq, dif_neg (by omega), dif_neg (by omega)]`.

Apply the tactic sequence `have hentry : ∀ i j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2 = ‖um X (sw k r i) (sw k r j)‖ ^ 2 + ‖um X' i j‖ ^ 2 + ‖torD k r x i j‖ ^ 2 + ‖um Y i j‖ ^ 2 := by`. Introduce `i j`. Simplify using `only [Matrix.add_apply, Matrix.neg_apply, conj_apply]`. Establish `li` using `lev_sw (k := k) (r := r) i`. Establish `lj` using `lev_sw (k := k) (r := r) j`.

Break down `lt_trichotomy (lev k r j) (lev k r i) with h | h | h` into its components or cases. Establish `h1 : um X' i j = 0` using `hX'.2 i j h.le`. Establish `h2 : torD k r x i j = 0` using `hToff i j (by rintro rfl; omega)`. Establish `h3 : um Y i j = 0` using `hY.2 i j (by`. Introduce and unpack `⟨hi, hj⟩`.

Rewrite `h` using `[hmid i hi, hmid j hj]`. Use the proof step `omega)`. Rewrite using `[h1, h2, h3]`. Simplify using the standard rewrite rules. Establish `h0 : um X (sw k r i) (sw k r j) = 0` using `hX.2 _ _ (by omega)`.

Establish `h1 : um X' i j = 0` using `hX'.2 i j h.le`. Rewrite using `[h0, h1]`. Distinguish the cases in `hm : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`. Establish `h2 : torD k r x i j = 0`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Conclude with `hTmid i hm.1`. Conclude with `hToff i j e`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.

Rewrite using `[hY.2 i j hm]`. Simplify using the standard rewrite rules. Establish `h0 : um X (sw k r i) (sw k r j) = 0` using `hX.2 _ _ (by omega)`. Establish `h2 : torD k r x i j = 0` using `hToff i j (by rintro rfl; omega)`. Establish `h3 : um Y i j = 0` using `hY.2 i j (by`.

Introduce and unpack `⟨hi, hj⟩`. Rewrite `h` using `[hmid i hi, hmid j hj]`. Use the proof step `omega)`. Rewrite using `[h0, h2, h3]`. Simplify using the standard rewrite rules.

Establish `hswX : ∑ i, ∑ j, ‖um X (sw k r i) (sw k r j)‖ ^ 2 = ∑ i, ∑ j, ‖um X i j‖ ^ 2`. Establish `h1 : ∀ i, ∑ j, ‖um X i (sw k r j)‖ ^ 2 = ∑ j, ‖um X i j‖ ^ 2` using `fun i => Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j)) (fun j => ‖um X i j‖ ^ 2)`. Simplify using `only [h1]`. Conclude with `Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j)) (fun i => ∑ j, ‖um X i j‖ ^ 2)`. Simplify using `only [hentry, Finset.sum_add_distrib]`.

Rewrite using `[hswX, norm_um, norm_um, norm_torD, norm_um]`.
-/
theorem dchart_skew_norm : ∀ (k r : ℕ) (v : EE k r),
    ((dchart k r v)ᴴ * Hpk k r + Hpk k r * dchart k r v = 0) ∧
    (∑ i, ∑ j, ‖dchart k r v i j‖ ^ 2) =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  intro k r v
  obtain ⟨⟨X, X'⟩, ⟨x, Y⟩⟩ := v
  have hX := (GlobalTheory.CellDens.LieN.lieE_Nset k r (X : EuclideanSpace ℝ _)).1.1 X.2
  have hX' := (GlobalTheory.CellDens.LieN.lieE_Nset k r (X' : EuclideanSpace ℝ _)).1.1 X'.2
  have hY := (GlobalTheory.CellLieAlg.lie_entries k r (Y : EuclideanSpace ℝ _)).2.1.1 Y.2
  change (um X)ᴴ * Hpk k r + Hpk k r * um X = 0 ∧
    ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X i j = 0 at hX
  change (um X')ᴴ * Hpk k r + Hpk k r * um X' = 0 ∧
    ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X' i j = 0 at hX'
  change (um Y)ᴴ * Hpk k r + Hpk k r * um Y = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
    ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → um Y i j = 0 at hY
  show (-(wC k r * um X * wC k r) + torD k r x + um Y + um X')ᴴ * Hpk k r +
      Hpk k r * (-(wC k r * um X * wC k r) + torD k r x + um Y + um X') = 0 ∧
    (∑ i, ∑ j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2) =
      ‖X‖ ^ 2 + ‖X'‖ ^ 2 + 2 * (∑ a, ‖x a‖ ^ 2) + ‖Y‖ ^ 2
  refine ⟨?_, ?_⟩
  · have e : ∀ A T B C : Mat k r, (-A + T + B + C)ᴴ * Hpk k r + Hpk k r * (-A + T + B + C) =
        -(Aᴴ * Hpk k r + Hpk k r * A) + (Tᴴ * Hpk k r + Hpk k r * T) + (Bᴴ * Hpk k r + Hpk k r * B) +
          (Cᴴ * Hpk k r + Hpk k r * C) := by
      intro A T B C
      simp only [conjTranspose_add, conjTranspose_neg, add_mul, mul_add, neg_mul, mul_neg]
      abel
    rw [e, skew_conj hX.1, skew_torD x, hY.1, hX'.1]
    simp
  · have hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → lev k r i = r := fun i h => by
      unfold lev
      rw [if_neg (by omega), if_pos h.2]
    have hToff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0 := fun i j h => by
      unfold torD
      exact Matrix.diagonal_apply_ne _ h
    have hTmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → torD k r x i i = 0 := fun i h => by
      unfold torD
      rw [Matrix.diagonal_apply_eq, dif_neg (by omega), dif_neg (by omega)]
    have hentry : ∀ i j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2 =
        ‖um X (sw k r i) (sw k r j)‖ ^ 2 + ‖um X' i j‖ ^ 2 + ‖torD k r x i j‖ ^ 2 + ‖um Y i j‖ ^ 2 := by
      intro i j
      simp only [Matrix.add_apply, Matrix.neg_apply, conj_apply]
      have li := lev_sw (k := k) (r := r) i
      have lj := lev_sw (k := k) (r := r) j
      rcases lt_trichotomy (lev k r j) (lev k r i) with h | h | h
      · have h1 : um X' i j = 0 := hX'.2 i j h.le
        have h2 : torD k r x i j = 0 := hToff i j (by rintro rfl; omega)
        have h3 : um Y i j = 0 := hY.2 i j (by
          rintro ⟨hi, hj⟩
          rw [hmid i hi, hmid j hj] at h
          omega)
        rw [h1, h2, h3]
        simp
      · have h0 : um X (sw k r i) (sw k r j) = 0 := hX.2 _ _ (by omega)
        have h1 : um X' i j = 0 := hX'.2 i j h.le
        rw [h0, h1]
        by_cases hm : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
        · have h2 : torD k r x i j = 0 := by
            by_cases e : i = j
            · subst e
              exact hTmid i hm.1
            · exact hToff i j e
          rw [h2]
          simp
        · rw [hY.2 i j hm]
          simp
      · have h0 : um X (sw k r i) (sw k r j) = 0 := hX.2 _ _ (by omega)
        have h2 : torD k r x i j = 0 := hToff i j (by rintro rfl; omega)
        have h3 : um Y i j = 0 := hY.2 i j (by
          rintro ⟨hi, hj⟩
          rw [hmid i hi, hmid j hj] at h
          omega)
        rw [h0, h2, h3]
        simp
    have hswX : ∑ i, ∑ j, ‖um X (sw k r i) (sw k r j)‖ ^ 2 = ∑ i, ∑ j, ‖um X i j‖ ^ 2 := by
      have h1 : ∀ i, ∑ j, ‖um X i (sw k r j)‖ ^ 2 = ∑ j, ‖um X i j‖ ^ 2 := fun i =>
        Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j)) (fun j => ‖um X i j‖ ^ 2)
      simp only [h1]
      exact Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j))
        (fun i => ∑ j, ‖um X i j‖ ^ 2)
    simp only [hentry, Finset.sum_add_distrib]
    rw [hswX, norm_um, norm_um, norm_torD, norm_um]

end GlobalTheory.CellDens.DNorm
