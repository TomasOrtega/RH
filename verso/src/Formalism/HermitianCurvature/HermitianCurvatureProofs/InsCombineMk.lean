import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwist

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

/- English proof (translation)
Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Simplify using `only [eU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Rewrite using `[if_pos rfl]`.

Generalize the expression as in `x a = v`. Apply the tactic sequence `fin_cases v <;> simp`. Rewrite using `[if_neg hxy]`. Establish `h : ∀ i : Fin 2, ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b)`. Introduce and unpack `i ⟨h1, h2, h3⟩`.

Apply `hxy` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Rewrite using `[h1, h2]`.

Conclude with `h3 b hb`. Rewrite using `[if_neg (h 0), if_neg (h 1), add_zero]`.
-/
private theorem eU_zero_zero_add_eU_one_one (a : S) : (eU a 0 0 : SlopeTestRemainingChoices S A) + eU a 1 1 = 1 := by
  refine Matrix.ext fun x y => ?_
  simp only [eU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    generalize x a = v
    fin_cases v <;> simp
  · rw [if_neg hxy]
    have h : ∀ i : Fin 2, ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro i ⟨h1, h2, h3⟩
      apply hxy
      funext b
      by_cases hb : b = a
      · subst hb; rw [h1, h2]
      · exact h3 b hb
    rw [if_neg (h 0), if_neg (h 1), add_zero]

/- English proof (translation)
Use `show (io g : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io g`. Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Simplify using `only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, eU, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem commute_io_eU (g : A) (a : S) (i j : Fin 2) : Commute (io g : SlopeTestRemainingChoices S A) (eU a i j) := by
  show (io g : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io g
  refine Matrix.ext fun x y => ?_
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, eU, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `ins`. Conclude with `Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (commute_io_eU g a i j).mul_right (h i j)`.
-/
private theorem commute_io_ins_of_commute_entries (g : A) (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (h : ∀ i j, Commute (io g : SlopeTestRemainingChoices S A) (M i j)) :
    Commute (io g : SlopeTestRemainingChoices S A) (ins a M) := by
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (commute_io_eU g a i j).mul_right (h i j)

/- English proof (translation)
Establish `hff : (io f : SlopeTestRemainingChoices S A) * io fi = 1`. Unfold `io`. Rewrite using `[← map_mul (Matrix.scalar (Ix S)), h1, map_one]`. Unfold `cj`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hff, mul_one]`. Simplify using `only [mul_assoc]`. Use `_ = io fi * x * io f * (io fi * y * io f) := by simp only [mul_assoc]`.
-/
private theorem cj_mul_of_mul_inv_eq_one {f fi : A} (h1 : f * fi = 1) (x y : SlopeTestRemainingChoices S A) :
    cj f fi (x * y) = cj f fi x * cj f fi y := by
  have hff : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := by
    unfold io; rw [← map_mul (Matrix.scalar (Ix S)), h1, map_one]
  unfold cj
  calc io fi * (x * y) * io f = io fi * x * (io f * io fi) * y * io f := by
        rw [hff, mul_one]; simp only [mul_assoc]
    _ = io fi * x * io f * (io fi * y * io f) := by simp only [mul_assoc]

/- English proof (translation)
Establish `hfi : (io fi : SlopeTestRemainingChoices S A) * io f = 1`. Unfold `io`. Rewrite using `[← map_mul (Matrix.scalar (Ix S)), h2, map_one]`. Unfold `cj`. Rewrite using `[mul_assoc, ← hx.eq, ← mul_assoc, hfi, one_mul]`.
-/
private theorem cj_eq_self_of_commute {f fi : A} (h2 : fi * f = 1) (x : SlopeTestRemainingChoices S A) (hx : Commute (io f : SlopeTestRemainingChoices S A) x) :
    cj f fi x = x := by
  have hfi : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    unfold io; rw [← map_mul (Matrix.scalar (Ix S)), h2, map_one]
  unfold cj
  rw [mul_assoc, ← hx.eq, ← mul_assoc, hfi, one_mul]

/- English proof (translation)
Unfold `cj`. Rewrite using `[mul_smul_comm, smul_mul_assoc]`.
-/
private theorem cj_smul' (f fi : A) (c : ℂ) (x : SlopeTestRemainingChoices S A) : cj f fi (c • x) = c • cj f fi x := by
  unfold cj; rw [mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Unfold `cj`. Rewrite using `[mul_sub, sub_mul]`.
-/
private theorem cj_sub' (f fi : A) (x y : SlopeTestRemainingChoices S A) : cj f fi (x - y) = cj f fi x - cj f fi y := by
  unfold cj; rw [mul_sub, sub_mul]

/- English proof (translation)
Unfold `cj`. Rewrite using `[mul_add, add_mul]`.
-/
private theorem cj_add' (f fi : A) (x y : SlopeTestRemainingChoices S A) : cj f fi (x + y) = cj f fi x + cj f fi y := by
  unfold cj; rw [mul_add, add_mul]

/- English proof (translation)
Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Rewrite using `[Matrix.star_apply]`. Simplify using `only [eU, Matrix.of_apply]`. Establish `hiff : (y a = i ∧ x a = j ∧ ∀ b, b ≠ a → y b = x b) ↔ (x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨h2, h1, fun b hb => (h3 b hb).symm⟩`. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨h2, h1, fun b hb => (h3 b hb).symm⟩`. Distinguish the cases in `h : x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b`.

Rewrite using `[if_pos (hiff.2 h), if_pos h, star_one]`. Rewrite using `[if_neg (mt hiff.1 h), if_neg h, star_zero]`.
-/
private theorem star_eU_apply_swap (a : S) (i j : Fin 2) : star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.star_apply]
  simp only [eU, Matrix.of_apply]
  have hiff : (y a = i ∧ x a = j ∧ ∀ b, b ≠ a → y b = x b) ↔ (x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
  by_cases h : x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b
  · rw [if_pos (hiff.2 h), if_pos h, star_one]
  · rw [if_neg (mt hiff.1 h), if_neg h, star_zero]

/- English proof (translation)
Establish `hc : ∀ i j, eU a i j * k = k * eU a i j` using `fun i j => (hk i j).eq`. Establish `hp : p = eU a 0 0 * p + eU a 1 1 * p` using `by rw [← add_mul, eU_zero_zero_add_eU_one_one, one_mul]`. Unfold `ins`. Simplify using `[Fin.sum_univ_two, mul_add, ← mul_assoc, hc]`. Use `conv_lhs => rw [hp]`.

Normalize the expressions using the abelian group laws.
-/
theorem ins_combine (a : S) (p k : SlopeTestRemainingChoices S A) (hk : FreeOf a k) (M : M2 (SlopeTestRemainingChoices S A)) :
    p + k * ins a M = ins a !![p + k * M 0 0, k * M 0 1; k * M 1 0, p + k * M 1 1] := by
  have hc : ∀ i j, eU a i j * k = k * eU a i j := fun i j => (hk i j).eq
  have hp : p = eU a 0 0 * p + eU a 1 1 * p := by rw [← add_mul, eU_zero_zero_add_eU_one_one, one_mul]
  unfold ins
  simp [Fin.sum_univ_two, mul_add, ← mul_assoc, hc]
  conv_lhs => rw [hp]
  abel

/- English proof (translation)
Conclude with `ins_combine a p k hk !![x, y; z, w]`.
-/
theorem ins_combine_mk (a : S) (p k : SlopeTestRemainingChoices S A) (hk : FreeOf a k) (x y z w : SlopeTestRemainingChoices S A) :
    p + k * ins a !![x, y; z, w] = ins a !![p + k * x, k * y; k * z, p + k * w] := by
  exact ins_combine a p k hk !![x, y; z, w]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

/- English proof (translation)
Establish `hx' : cj f fi x = x - t • (1 : SlopeTestRemainingChoices S A)` using `hx`. Establish `hw' : cj f fi w = w - t • (1 : SlopeTestRemainingChoices S A)` using `hw`. Establish `key : cj f fi (ins a !![x, y; z, w]) = ins a !![cj f fi x, cj f fi y; cj f fi z, cj f fi w]`. Unfold `ins cj`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, (commute_io_eU fi a i j).eq, mul_assoc (eU a i j), mul_assoc (eU a i j)]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> rfl`. Use `show cj f fi (ins a !![x, y; z, w]) = ins a !![x, y; z, w] - t • (1 : SlopeTestRemainingChoices S A)`. Rewrite using `[key, hx', hw', hy, hz]`.

Use `conv_rhs => rw [← eU_zero_zero_add_eU_one_one (A := A) a]`. Unfold `ins`. Apply the tactic sequence `simp [Fin.sum_univ_two, mul_sub, smul_add, mul_smul_comm] <;> abel`.
-/
theorem tw_ins_mk (a : S) (t : ℂ) (x y z w : SlopeTestRemainingChoices S A) (hx : Tw f fi t x) (hw : Tw f fi t w)
    (hy : cj f fi y = y) (hz : cj f fi z = z) : Tw f fi t (ins a !![x, y; z, w]) := by
  have hx' : cj f fi x = x - t • (1 : SlopeTestRemainingChoices S A) := hx
  have hw' : cj f fi w = w - t • (1 : SlopeTestRemainingChoices S A) := hw
  have key : cj f fi (ins a !![x, y; z, w]) = ins a !![cj f fi x, cj f fi y; cj f fi z, cj f fi w] := by
    unfold ins cj
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, (commute_io_eU fi a i j).eq, mul_assoc (eU a i j), mul_assoc (eU a i j)]
    fin_cases i <;> fin_cases j <;> rfl
  show cj f fi (ins a !![x, y; z, w]) = ins a !![x, y; z, w] - t • (1 : SlopeTestRemainingChoices S A)
  rw [key, hx', hw', hy, hz]
  conv_rhs => rw [← eU_zero_zero_add_eU_one_one (A := A) a]
  unfold ins
  simp [Fin.sum_univ_two, mul_sub, smul_add, mul_smul_comm] <;> abel

section Older

variable (hW : WaveHyp L st f fi s) (fw : Fr.FrameData S A) (hF : Fr.IsFrame L fw)
  (ihx : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y)) (ihl : ∀ Y ∈ fw.inv, Tw f fi s (fw.l L Y))
include hW hF ihx ihl

/- English proof (translation)
Introduce `Y hY`. Take `⟨h1, h2⟩` from `hF.x_xi Y hY`. Establish `hx` using `ihx Y`. Use `show (io f : SlopeTestRemainingChoices S A) * fw.xi Y = fw.xi Y * io f`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem io_commute_xi : ∀ Y ∈ fw.inv, Commute (io f : SlopeTestRemainingChoices S A) (fw.xi Y) := by
  intro Y hY
  obtain ⟨h1, h2⟩ := hF.x_xi Y hY
  have hx := ihx Y
  show (io f : SlopeTestRemainingChoices S A) * fw.xi Y = fw.xi Y * io f
  calc (io f : SlopeTestRemainingChoices S A) * fw.xi Y = fw.xi Y * fw.x Y * io f * fw.xi Y := by rw [h2, one_mul]
    _ = fw.xi Y * (io f * fw.x Y) * fw.xi Y := by rw [hx.eq]; simp only [mul_assoc]
    _ = fw.xi Y * io f := by rw [mul_assoc, mul_assoc, h1, mul_one]

/- English proof (translation)
Introduce `Y hY Y' hY'`. Establish `hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A)` using `ihl Y hY`. Establish `hl' : cj f fi (fw.l L Y') = fw.l L Y' - s • (1 : SlopeTestRemainingChoices S A)` using `ihl Y' hY'`. Establish `hio : (io (L.l0 Y - L.l0 Y') : SlopeTestRemainingChoices S A) = io (L.l0 Y) - io (L.l0 Y')` using `map_sub (Matrix.scalar (Ix S)) _ _`. Establish `e : Fr.kapL L * fw.DD Y Y' = (Y - Y')⁻¹ • (fw.l L Y - fw.l L Y' - io (L.l0 Y - L.l0 Y'))`.

Unfold `Formalism.FourierDecayAlt.Fr.FrameData.DD Formalism.FourierDecayAlt.Fr.FrameData.l`. Rewrite using `[mul_smul_comm, mul_sub, hio]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `hc : Commute (io f : SlopeTestRemainingChoices S A) (io (L.l0 Y - L.l0 Y'))` using `(hW.lowering_constant_sub Y Y').map (Matrix.scalar (Ix S))`.

Rewrite using `[e, cj_smul', cj_sub', cj_sub', hl, hl', cj_eq_self_of_commute hW.fi_f _ hc]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem cj_kapL_DD : ∀ Y ∈ fw.inv, ∀ Y' ∈ fw.inv,
    cj f fi (Fr.kapL L * fw.DD Y Y') = Fr.kapL L * fw.DD Y Y' := by
  intro Y hY Y' hY'
  have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY
  have hl' : cj f fi (fw.l L Y') = fw.l L Y' - s • (1 : SlopeTestRemainingChoices S A) := ihl Y' hY'
  have hio : (io (L.l0 Y - L.l0 Y') : SlopeTestRemainingChoices S A) = io (L.l0 Y) - io (L.l0 Y') := map_sub (Matrix.scalar (Ix S)) _ _
  have e : Fr.kapL L * fw.DD Y Y' = (Y - Y')⁻¹ • (fw.l L Y - fw.l L Y' - io (L.l0 Y - L.l0 Y')) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.DD Formalism.FourierDecayAlt.Fr.FrameData.l
    rw [mul_smul_comm, mul_sub, hio]
    congr 1
    abel
  have hc : Commute (io f : SlopeTestRemainingChoices S A) (io (L.l0 Y - L.l0 Y')) := (hW.lowering_constant_sub Y Y').map (Matrix.scalar (Ix S))
  rw [e, cj_smul', cj_sub', cj_sub', hl, hl', cj_eq_self_of_commute hW.fi_f _ hc]
  congr 1
  abel

/- English proof (translation)
Introduce `Y hY Ya hYa`. Establish `hxi` using `io_commute_xi hW fw hF ihx ihl Ya hYa`. Take `⟨h1, h2⟩` from `hF.x_xi Ya hYa`. Establish `hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A)` using `ihl Y hY`. Use `show cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A)`.

Rewrite using `[cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hxi, cj_eq_self_of_commute hW.fi_f _ (ihx Ya), hl, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, h2]`.
-/
theorem tw_xi_l_x : ∀ Y ∈ fw.inv, ∀ Ya ∈ fw.inv, Tw f fi s (fw.xi Ya * fw.l L Y * fw.x Ya) := by
  intro Y hY Ya hYa
  have hxi := io_commute_xi hW fw hF ihx ihl Ya hYa
  obtain ⟨h1, h2⟩ := hF.x_xi Ya hYa
  have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY
  show cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A)
  rw [cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hxi, cj_eq_self_of_commute hW.fi_f _ (ihx Ya), hl,
    mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, h2]

omit ihx ihl in
/- English proof (translation)
Introduce `Y Ya hYa`. Take `⟨h1, h2⟩` from `hF.x_xi Ya hYa`. Establish `hz` using `mem_zfns L`. Establish `hl0 : Commute (fw.x Ya) (io (L.l0 Y))`. Rewrite using `[embed_lowering_constant]`.

Conclude with `(hF.x_nab Ya).neg_right.sub_right (((Commute.one_right _).smul_right _).mul_right ((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)))`. Establish `hk : Commute (fw.x Ya) (Fr.kapL L)`. Unfold `Fr.kapL io`. Rewrite using `[map_mul, map_mul]`. Conclude with `((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.1)).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)`.

Establish `e1 : fw.xi Ya * io (L.l0 Y) * fw.x Ya = io (L.l0 Y)`. Rewrite using `[mul_assoc, ← hl0.eq, ← mul_assoc, h2, one_mul]`. Establish `e2 : fw.xi Ya * Fr.kapL L = Fr.kapL L * fw.xi Ya`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_assoc, h1, mul_one]`.

Use `_ = fw.xi Ya * fw.x Ya * Fr.kapL L * fw.xi Ya := by rw [← hk.eq]; simp only [mul_assoc]`. Use `_ = Fr.kapL L * fw.xi Ya := by rw [h2, one_mul]`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.l`. Rewrite using `[mul_add, add_mul, e1]`. Use `congr 1`.

Rewrite using `[← mul_assoc (fw.xi Ya) (Fr.kapL L) (fw.ee Y), e2]`. Simplify using `only [mul_assoc]`.
-/
theorem io_l0_add_kapL_eq : ∀ Y, ∀ Ya ∈ fw.inv, io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya) =
    fw.xi Ya * fw.l L Y * fw.x Ya := by
  intro Y Ya hYa
  obtain ⟨h1, h2⟩ := hF.x_xi Ya hYa
  have hz := mem_zfns L
  have hl0 : Commute (fw.x Ya) (io (L.l0 Y)) := by
    rw [embed_lowering_constant]
    exact (hF.x_nab Ya).neg_right.sub_right (((Commute.one_right _).smul_right _).mul_right
      ((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)))
  have hk : Commute (fw.x Ya) (Fr.kapL L) := by
    unfold Fr.kapL io
    rw [map_mul, map_mul]
    exact ((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.1)).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)
  have e1 : fw.xi Ya * io (L.l0 Y) * fw.x Ya = io (L.l0 Y) := by
    rw [mul_assoc, ← hl0.eq, ← mul_assoc, h2, one_mul]
  have e2 : fw.xi Ya * Fr.kapL L = Fr.kapL L * fw.xi Ya := by
    calc fw.xi Ya * Fr.kapL L = fw.xi Ya * (Fr.kapL L * fw.x Ya) * fw.xi Ya := by
          rw [mul_assoc, mul_assoc, h1, mul_one]
      _ = fw.xi Ya * fw.x Ya * Fr.kapL L * fw.xi Ya := by rw [← hk.eq]; simp only [mul_assoc]
      _ = Fr.kapL L * fw.xi Ya := by rw [h2, one_mul]
  unfold Formalism.FourierDecayAlt.Fr.FrameData.l
  rw [mul_add, add_mul, e1]
  congr 1
  rw [← mul_assoc (fw.xi Ya) (Fr.kapL L) (fw.ee Y), e2]
  simp only [mul_assoc]

end Older

section Letters

variable (hW : WaveHyp L st f fi s) (fw : Fr.FrameData S A) (hF : Fr.IsFrame L fw) (a : S)
  (Ya : ℂ) (m0 : Ya ∈ fw.inv)
  (ihx : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y))
  (ihl : ∀ Y ∈ fw.inv, Tw f fi s (fw.l L Y))
include hW hF m0 ihx ihl

omit m0 ihl in
/- English proof (translation)
Introduce `Y`. Use `show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • 1, 0; 0, 1])`. Use `(ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Use `show Commute (io f : SlopeTestRemainingChoices S A) (((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A))`. Conclude with `(Commute.one_right _).smul_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 0`. Conclude with `Commute.zero_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 0`.

Conclude with `Commute.zero_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 1`. Conclude with `Commute.one_right _`.
-/
theorem commute_io_plus_x : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((fw.plus L a Ya).x Y) := by
  intro Y
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • 1, 0; 0, 1])
  refine (ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  fin_cases i <;> fin_cases j
  · show Commute (io f : SlopeTestRemainingChoices S A) (((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A))
    exact (Commute.one_right _).smul_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 1
    exact Commute.one_right _

omit m0 in
/- English proof (translation)
Use `show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q Ya • fw.xi (Ya + 1), 0; 0, fw.x Ya])`. Use `ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)` and prove the remaining obligations. Introduce `i j`. Establish `h1` using `(io_commute_xi hW fw hF ihx ihl (Ya + 1) m1).smul_right (fw.q Ya)`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Conclude with `h1`. Conclude with `Commute.zero_right _`. Conclude with `Commute.zero_right _`. Conclude with `ihx Ya`.
-/
theorem plus_c (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (m1 : Ya + 1 ∈ fw.inv) : Commute (io f : SlopeTestRemainingChoices S A) (fw.plus L a Ya).c := by
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q Ya • fw.xi (Ya + 1), 0; 0, fw.x Ya])
  refine ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  have h1 := (io_commute_xi hW fw hF ihx ihl (Ya + 1) m1).smul_right (fw.q Ya)
  fin_cases i <;> fin_cases j
  · exact h1
  · exact Commute.zero_right _
  · exact Commute.zero_right _
  · exact ihx Ya

/- English proof (translation)
Introduce `Y hY`. Establish `hY0 : Y ∈ fw.inv` using `hY.1`. Establish `hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A)` using `fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm`. Use `show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoices S A)); 0, fw.xi Ya * fw.ee Y * fw.x Ya]) = io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoic …`. Rewrite using `[ins_combine_mk a _ _ hkap]`.

Use `tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Establish `e : io (L.l0 Y) + Fr.kapL L * (fw.ee Y - fw.DD Y Ya + Fr.tz L) = fw.l L Y - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.l`. Rewrite using `[mul_add, mul_sub]`. Normalize the expressions using the abelian group laws.

Establish `hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A)` using `ihl Y hY0`. Use `show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)`. Rewrite using `[e, cj_add', cj_sub', hl, cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0, cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]`. Normalize the expressions using the abelian group laws. Use `show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)`.

Rewrite using `[io_l0_add_kapL_eq hW fw hF Y Ya m0]`. Conclude with `tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0`. Conclude with `cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((Commute.one_right _).smul_right _).neg_right)`. Conclude with `cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))`.
-/
theorem plus_l : ∀ Y ∈ (fw.plus L a Ya).inv, Tw f fi s ((fw.plus L a Ya).l L Y) := by
  intro Y hY
  have hY0 : Y ∈ fw.inv := hY.1
  have hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A) := fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm
  show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoices S A));
      0, fw.xi Ya * fw.ee Y * fw.x Ya]) =
    io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoices S A));
      0, fw.xi Ya * fw.ee Y * fw.x Ya] - s • (1 : SlopeTestRemainingChoices S A)
  rw [ins_combine_mk a _ _ hkap]
  refine tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_
  · have e : io (L.l0 Y) + Fr.kapL L * (fw.ee Y - fw.DD Y Ya + Fr.tz L) =
        fw.l L Y - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L := by
      unfold Formalism.FourierDecayAlt.Fr.FrameData.l
      rw [mul_add, mul_sub]
      abel
    have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY0
    show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [e, cj_add', cj_sub', hl, cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0,
      cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]
    abel
  · show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [io_l0_add_kapL_eq hW fw hF Y Ya m0]
    exact tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((Commute.one_right _).smul_right _).neg_right)
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))

/- English proof (translation)
Establish `hfl : FreeOf a (fw.l L Ya)` using `fun i j => by`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL`. Conclude with `((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 Ya i j))`. Establish `hD : FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * fw.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A))`. Rewrite using `[Matrix.mul_fin_two]`.

Introduce `p q i j`. Establish `hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A)` using `fun g => (commute_io_eU g a i j).symm`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Conclude with `((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfl i j)))`. Conclude with `((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))`.

Conclude with `((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfl i j)))`. Conclude with `((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))`. Establish `hz` using `mem_zfns L`. Establish `hE` using `block_twist hW.f_fi hW.fi_f s (io L.ζi) (io L.ζbi) (io L.GG) (fw.l L Ya) (hW.io_fn hz.2.1) (hW.io_fn hz.2.2.2.1) (hW.io_fn hz.2.2.2.2.1) (ihl Ya m0)`. Conclude with `frame_step hW.f_fi a s _ fw.F UU hD hfree.2.2.1 ihF hE`.
-/
theorem plus_F (hfree : fw.Free a) (UU : SlopeTestRemainingChoices S A) (ihF : fw.F * (io f * UU) = io f * fw.F) :
    (fw.plus L a Ya).F * (io f * (ins a (lift0 (Uinv (A := A) s)) * UU)) = io f * (fw.plus L a Ya).F := by
  have hfl : FreeOf a (fw.l L Ya) := fun i j => by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL
    exact ((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 Ya i j))
  have hD : FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * fw.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) := by
    rw [Matrix.mul_fin_two]
    intro p q i j
    have hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A) := fun g => (commute_io_eU g a i j).symm
    fin_cases p <;> fin_cases q
    · exact ((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfl i j)))
    · exact ((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))
    · exact ((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfl i j)))
    · exact ((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))
  have hz := mem_zfns L
  have hE := block_twist hW.f_fi hW.fi_f s (io L.ζi) (io L.ζbi) (io L.GG) (fw.l L Ya) (hW.io_fn hz.2.1)
    (hW.io_fn hz.2.2.2.1) (hW.io_fn hz.2.2.2.2.1) (ihl Ya m0)
  exact frame_step hW.f_fi a s _ fw.F UU hD hfree.2.2.1 ihF hE

omit m0 ihl in
/- English proof (translation)
Introduce `Y`. Use `show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Ya - Y) / (Ya - Y - 1)) • 1, 0; 0, 1])`. Use `(ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Use `show Commute (io f : SlopeTestRemainingChoices S A) (((Ya - Y) / (Ya - Y - 1)) • (1 : SlopeTestRemainingChoices S A))`. Conclude with `(Commute.one_right _).smul_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 0`. Conclude with `Commute.zero_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 0`.

Conclude with `Commute.zero_right _`. Use `show Commute (io f : SlopeTestRemainingChoices S A) 1`. Conclude with `Commute.one_right _`.
-/
theorem commute_io_minus_x : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((fw.minus L a Ya).x Y) := by
  intro Y
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Ya - Y) / (Ya - Y - 1)) • 1, 0; 0, 1])
  refine (ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  fin_cases i <;> fin_cases j
  · show Commute (io f : SlopeTestRemainingChoices S A) (((Ya - Y) / (Ya - Y - 1)) • (1 : SlopeTestRemainingChoices S A))
    exact (Commute.one_right _).smul_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 1
    exact Commute.one_right _

omit m0 in
/- English proof (translation)
Use `show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q (Ya - 1) • fw.xi (Ya - 1), 0; 0, fw.x Ya])`. Use `ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)` and prove the remaining obligations. Introduce `i j`. Establish `h1` using `(io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1).smul_right (fw.q (Ya - 1))`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Conclude with `h1`. Conclude with `Commute.zero_right _`. Conclude with `Commute.zero_right _`. Conclude with `ihx Ya`.
-/
theorem minus_c (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) : Commute (io f : SlopeTestRemainingChoices S A) (fw.minus L a Ya).c := by
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q (Ya - 1) • fw.xi (Ya - 1), 0; 0, fw.x Ya])
  refine ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  have h1 := (io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1).smul_right (fw.q (Ya - 1))
  fin_cases i <;> fin_cases j
  · exact h1
  · exact Commute.zero_right _
  · exact Commute.zero_right _
  · exact ihx Ya

/- English proof (translation)
Introduce `Y hY`. Establish `hY0 : Y ∈ fw.inv` using `hY.1`. Establish `hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A)` using `fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm`. Use `show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0; -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.xi (Ya - 1))), fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L]) = io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0; -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.x …`. Rewrite using `[ins_combine_mk a _ _ hkap]`.

Use `tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `ihl Y hY0`. Establish `e : io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L) = (io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya)) - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L`. Rewrite using `[mul_add, mul_sub]`. Normalize the expressions using the abelian group laws.

Establish `hl' : cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A)` using `tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0`. Use `show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)`. Rewrite using `[e, io_l0_add_kapL_eq hW fw hF Y Ya m0, cj_add', cj_sub', hl', cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0, cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]`. Normalize the expressions using the abelian group laws. Conclude with `cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))`.

Establish `h1` using `io_commute_xi hW fw hF ihx ihl Ya m0`. Establish `h2` using `io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1`. Conclude with `cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((h1.mul_right h2).smul_right _).neg_right)`.
-/
theorem minus_l (mm1 : Ya - 1 ∈ fw.inv) : ∀ Y ∈ (fw.minus L a Ya).inv, Tw f fi s ((fw.minus L a Ya).l L Y) := by
  intro Y hY
  have hY0 : Y ∈ fw.inv := hY.1
  have hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A) := fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm
  show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0;
      -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.xi (Ya - 1))), fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L]) =
    io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0;
      -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.xi (Ya - 1))), fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L] -
      s • (1 : SlopeTestRemainingChoices S A)
  rw [ins_combine_mk a _ _ hkap]
  refine tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_
  · exact ihl Y hY0
  · have e : io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L) =
        (io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya)) - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L := by
      rw [mul_add, mul_sub]
      abel
    have hl' : cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A) :=
      tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0
    show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [e, io_l0_add_kapL_eq hW fw hF Y Ya m0, cj_add', cj_sub', hl', cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0,
      cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]
    abel
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))
  · have h1 := io_commute_xi hW fw hF ihx ihl Ya m0
    have h2 := io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1
    exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((h1.mul_right h2).smul_right _).neg_right)

omit m0 in

/- English proof (translation)
Take `⟨hcc, hcc'⟩` from `hF.c_ci`. Establish `hci : Commute (io f : SlopeTestRemainingChoices S A) fw.ci` using `by show (io f : SlopeTestRemainingChoices S A) * fw.ci = fw.ci * io f`. Combine the equalities or inequalities in the displayed calculation. Establish `hdi : Commute (io f : SlopeTestRemainingChoices S A) (fw.di L)`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.di`.

Conclude with `hci.mul_right ((WaveHyp.wti (S := S) hW).pow_right _)`. Establish `hd : Commute (io f : SlopeTestRemainingChoices S A) (fw.d L)`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.d`. Conclude with `((WaveHyp.wt (S := S) hW).pow_right _).mul_right ihc`. Establish `hstar : ∀ x : A, star (io x : SlopeTestRemainingChoices S A) = io (star x)`.

Introduce `x`. Use `first`. Consider the case `(unfold io`. Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use the proof step `rfl)`.

Consider the case `(refine Matrix.ext fun i j => ?_`. Simplify using `[io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.star_apply]`. Apply the tactic sequence `split_ifs <;> simp_all)`. Establish `hsf : star fi = f` using `by rw [← hW.star_f, star_star]`. Establish `cjs : ∀ z : SlopeTestRemainingChoices S A, cj f fi (star z) = star (cj f fi z)`.

Introduce `z`. Unfold `cj`. Rewrite using `[star_mul, star_mul, hstar, hstar, hW.star_f, hsf, mul_assoc]`. Establish `hl : cj f fi (fw.l L (Ya - 1)) = fw.l L (Ya - 1) - s • (1 : SlopeTestRemainingChoices S A)` using `ihl (Ya - 1) mm1`. Use `show cj f fi (fw.di L * star (fw.l L (Ya - 1)) * fw.d L) = fw.di L * star (fw.l L (Ya - 1)) * fw.d L - star s • (1 : SlopeTestRemainingChoices S A)`.

Rewrite using `[cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hdi, cj_eq_self_of_commute hW.fi_f _ hd, cjs, hl, star_sub, star_smul, star_one, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, di_d L fw hcc']`.
-/
theorem minus_m (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) : Tw f fi (star s) (fw.m L Ya) := by
  obtain ⟨hcc, hcc'⟩ := hF.c_ci
  have hci : Commute (io f : SlopeTestRemainingChoices S A) fw.ci := by
    show (io f : SlopeTestRemainingChoices S A) * fw.ci = fw.ci * io f
    calc (io f : SlopeTestRemainingChoices S A) * fw.ci = fw.ci * fw.c * io f * fw.ci := by rw [hcc', one_mul]
      _ = fw.ci * (io f * fw.c) * fw.ci := by rw [ihc.eq]; simp only [mul_assoc]
      _ = fw.ci * io f := by rw [mul_assoc, mul_assoc, hcc, mul_one]
  have hdi : Commute (io f : SlopeTestRemainingChoices S A) (fw.di L) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.di
    exact hci.mul_right ((WaveHyp.wti (S := S) hW).pow_right _)
  have hd : Commute (io f : SlopeTestRemainingChoices S A) (fw.d L) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.d
    exact ((WaveHyp.wt (S := S) hW).pow_right _).mul_right ihc
  have hstar : ∀ x : A, star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
    intro x
    first
      | (unfold io
         rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
         rfl)
      | (refine Matrix.ext fun i j => ?_
         simp [io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.star_apply]
         split_ifs <;> simp_all)
  have hsf : star fi = f := by rw [← hW.star_f, star_star]
  have cjs : ∀ z : SlopeTestRemainingChoices S A, cj f fi (star z) = star (cj f fi z) := by
    intro z
    unfold cj
    rw [star_mul, star_mul, hstar, hstar, hW.star_f, hsf, mul_assoc]
  have hl : cj f fi (fw.l L (Ya - 1)) = fw.l L (Ya - 1) - s • (1 : SlopeTestRemainingChoices S A) := ihl (Ya - 1) mm1
  show cj f fi (fw.di L * star (fw.l L (Ya - 1)) * fw.d L) =
    fw.di L * star (fw.l L (Ya - 1)) * fw.d L - star s • (1 : SlopeTestRemainingChoices S A)
  rw [cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hdi, cj_eq_self_of_commute hW.fi_f _ hd, cjs, hl,
    star_sub, star_smul, star_one, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, di_d L fw hcc']

omit m0 in
/- English proof (translation)
Establish `hfl : FreeOf a (fw.l L (Ya - 1))` using `fun i j => by`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL`. Conclude with `((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 (Ya - 1) i j))`. Establish `hfm : FreeOf a (fw.m L Ya)` using `fun i j => by`. Establish `hs : Commute (eU a i j) (star (fw.l L (Ya - 1)))`.

Establish `h` using `(hfl j i).star_star`. Rewrite `h` using `[star_eU_apply_swap]`. Then use the resulting hypothesis. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.m Formalism.FourierDecayAlt.Fr.FrameData.di Formalism.FourierDecayAlt.Fr.FrameData.d Fr.wti Fr.wt`. Conclude with `(((hfree.2.2.2.2.2.2.2.1 i j).mul_right ((commute_io_eU _ a i j).symm.pow_right _)).mul_right hs).mul_right (((commute_io_eU _ a i j).symm.pow_right _).mul_right (hfree.2.2.2.2.2.2.1 i j))`. Establish `hD : FreeOf2 a (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * fw.m L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A))`.

Rewrite using `[Matrix.mul_fin_two]`. Introduce `p q i j`. Establish `hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A)` using `fun g => (commute_io_eU g a i j).symm`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Conclude with `((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfm i j)))`.

Conclude with `((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))`. Conclude with `((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfm i j)))`. Conclude with `((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))`. Establish `hz` using `mem_zfns L`. Establish `hE` using `block_twist hW.f_fi hW.fi_f (star s) (io L.ζbi) (io L.ζi) (io L.GG) (fw.m L Ya) (hW.io_fn hz.2.2.2.1) (hW.io_fn hz.2.1) (hW.io_fn hz.2.2.2.2.1) (minus_m (hW := hW) (fw := fw) (hF := hF) (Ya := Ya) (ihx := ihx) (ihl := ihl) (ihc := ihc) (mm1 := mm1))`.

Conclude with `frame_step hW.f_fi a (star s) _ fw.F UU hD hfree.2.2.1 ihF hE`.
-/
theorem minus_F (hfree : fw.Free a) (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) (UU : SlopeTestRemainingChoices S A) (ihF : fw.F * (io f * UU) = io f * fw.F) :
    (fw.minus L a Ya).F * (io f * (ins a (lift0 (Uinv (A := A) (star s))) * UU)) =
      io f * (fw.minus L a Ya).F := by
  have hfl : FreeOf a (fw.l L (Ya - 1)) := fun i j => by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL
    exact ((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 (Ya - 1) i j))
  have hfm : FreeOf a (fw.m L Ya) := fun i j => by
    have hs : Commute (eU a i j) (star (fw.l L (Ya - 1))) := by
      have h := (hfl j i).star_star
      rwa [star_eU_apply_swap] at h
    unfold Formalism.FourierDecayAlt.Fr.FrameData.m Formalism.FourierDecayAlt.Fr.FrameData.di Formalism.FourierDecayAlt.Fr.FrameData.d Fr.wti Fr.wt
    exact (((hfree.2.2.2.2.2.2.2.1 i j).mul_right ((commute_io_eU _ a i j).symm.pow_right _)).mul_right hs).mul_right
      (((commute_io_eU _ a i j).symm.pow_right _).mul_right (hfree.2.2.2.2.2.2.1 i j))
  have hD : FreeOf2 a (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * fw.m L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) := by
    rw [Matrix.mul_fin_two]
    intro p q i j
    have hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A) := fun g => (commute_io_eU g a i j).symm
    fin_cases p <;> fin_cases q
    · exact ((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfm i j)))
    · exact ((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))
    · exact ((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfm i j)))
    · exact ((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))
  have hz := mem_zfns L
  have hE := block_twist hW.f_fi hW.fi_f (star s) (io L.ζbi) (io L.ζi) (io L.GG) (fw.m L Ya) (hW.io_fn hz.2.2.2.1)
    (hW.io_fn hz.2.1) (hW.io_fn hz.2.2.2.2.1)
    (minus_m (hW := hW) (fw := fw) (hF := hF) (Ya := Ya) (ihx := ihx) (ihl := ihl) (ihc := ihc) (mm1 := mm1))
  exact frame_step hW.f_fi a (star s) _ fw.F UU hD hfree.2.2.1 ihF hE

end Letters

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_`. Use `⟨fun Y => commute_io_io (hW.x Y), Commute.one_right _, fun Y hY => ?_, ?_⟩` and prove the remaining obligations.

Use `show Tw f fi s (io (L.l0 Y) + Fr.kapL L * io (st.ee Y))`. Establish `e : (io (L.l0 Y) + Fr.kapL L * io (st.ee Y) : SlopeTestRemainingChoices S A) = io (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)`. Simplify using `only [Fr.kapL, io_add', io_mul']`. Rewrite using `[e]`. Unfold `Tw`.

Rewrite using `[cj_io, hW.l Y hY, io_sub', io_algebraMap]`. Use `show (1 : SlopeTestRemainingChoices S A) * (io f * 1) = io f * 1`. Simplify using the standard rewrite rules. Consider the case `cons l w ih`. Introduce `hA`.

Take `⟨hnd, hre, hpt, hpw⟩` from `hA`. Establish `hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup` using `List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)`. Establish `hpw'` using `List.pairwise_cons.mp hpw`. Establish `hAw : Fr.admitted st w` using `⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩`. Take `⟨ihx, ihc, ihl, ihF⟩` from `ih hAw`.

Establish `hF` using `Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL hst hAw`. Establish `hfree` using `Formalism.FourierDecayAlt.P.frame_free_of_new_position A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1`. Take `⟨p0, p1, pm1, -, -⟩` from `hpt l (by simp)`. Establish `hd` using `hpw'.1`. Establish `m0 : l.pt ∈ (Fr.ofWord L st w).inv` using `Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combin …`.

Establish `m1 : l.pt + 1 ∈ (Fr.ofWord L st w).inv` using `Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' => ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_com …`. Establish `mm1 : l.pt - 1 ∈ (Fr.ofWord L st w).inv` using `Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' => ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combinat …`. Distinguish the cases in `hp : l.plus`. Establish `e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt` using `by simp [Fr.ofWord, hp]`. Establish `eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) = io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A` using `A) s)) * UUiw s w) := by`.

Simplify using `[Vw, UUiw, hp]`. Rewrite using `[e, eV]`. Conclude with `⟨commute_io_plus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, plus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc m1, plus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl, plus_F hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx …`. Establish `e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt` using `by simp [Fr.ofWord, hp]`. Establish `eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) = io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A` using `A) (star s))) * UUiw s w) := by`.

Simplify using `[Vw, UUiw, hp]`. Rewrite using `[e, eV]`. Conclude with `⟨commute_io_minus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, minus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc mm1, minus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl mm1, minus_F hW _ hF l.intersection_update_fsHerm_neg_one l.p …`.
-/
theorem frame_twist (hL : Fr.IsStarLevel L) (hst : Fr.IsLevelStart L st) (hW : WaveHyp L st f fi s) :
    ∀ w : List (Letter ℂ S), Fr.admitted st w →
      (∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((Fr.ofWord L st w).x Y)) ∧
      Commute (io f : SlopeTestRemainingChoices S A) (Fr.ofWord L st w).c ∧
      (∀ Y ∈ (Fr.ofWord L st w).inv, Tw f fi s ((Fr.ofWord L st w).l L Y)) ∧
      (Fr.ofWord L st w).F * Vw f s w = io f * (Fr.ofWord L st w).F := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨fun Y => commute_io_io (hW.x Y), Commute.one_right _, fun Y hY => ?_, ?_⟩
    · show Tw f fi s (io (L.l0 Y) + Fr.kapL L * io (st.ee Y))
      have e : (io (L.l0 Y) + Fr.kapL L * io (st.ee Y) : SlopeTestRemainingChoices S A) =
          io (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) := by
        simp only [Fr.kapL, io_add', io_mul']
      rw [e]
      unfold Tw
      rw [cj_io, hW.l Y hY, io_sub', io_algebraMap]
    · show (1 : SlopeTestRemainingChoices S A) * (io f * 1) = io f * 1
      simp
  | cons l w ih =>
    intro hA
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : Fr.admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨ihx, ihc, ihl, ihF⟩ := ih hAw
    have hF := Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL hst hAw
    have hfree := Formalism.FourierDecayAlt.P.frame_free_of_new_position A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
    obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · have e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [Fr.ofWord, hp]
      have eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) = io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) s)) * UUiw s w) := by
        simp [Vw, UUiw, hp]
      rw [e, eV]
      exact ⟨commute_io_plus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, plus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc m1,
        plus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl, plus_F hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl hfree _ ihF⟩
    · have e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [Fr.ofWord, hp]
      have eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) =
          io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (star s))) * UUiw s w) := by
        simp [Vw, UUiw, hp]
      rw [e, eV]
      exact ⟨commute_io_minus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, minus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc mm1,
        minus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl mm1, minus_F hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl hfree ihc mm1 _ ihF⟩

/- English proof (translation)
Take `⟨-, hc, -, hF⟩` from `frame_twist hL hst hW w hw`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.d`. Conclude with `((WaveHyp.wt (S := S) hW).pow_right _).mul_right hc`.
-/
theorem frame_twist_F (hL : Fr.IsStarLevel L) (hst : Fr.IsLevelStart L st) (hW : WaveHyp L st f fi s)
    (w : List (Letter ℂ S)) (hw : Fr.admitted st w) :
    (Fr.ofWord L st w).F * Vw f s w = io f * (Fr.ofWord L st w).F ∧
      Commute (io f : SlopeTestRemainingChoices S A) ((Fr.ofWord L st w).d L) := by
  obtain ⟨-, hc, -, hF⟩ := frame_twist hL hst hW w hw
  refine ⟨hF, ?_⟩
  unfold Formalism.FourierDecayAlt.Fr.FrameData.d
  exact ((WaveHyp.wt (S := S) hW).pow_right _).mul_right hc

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
