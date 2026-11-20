import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftOfSmoothComm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator

namespace GlobalTheory.HatNF.CellRules

open Matrix Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

/- English proof (translation)
Rewrite using `[PI.QnWCellW.wCell_last, PI.QnWCellW.Wm_mul_apply]`.
-/
theorem cell_apply (c : Fin r → ℂ) (g : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p q = PI.QnWCellW.cf k r c p * g (PI.QnWCellW.swp k r p) q := by
  rw [PI.QnWCellW.wCell_last, PI.QnWCellW.Wm_mul_apply]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[PI.QnWCellW.swp_val, if_neg (by rw [eI_val]; omega), eI_val, esI_val]`.
-/
theorem swp_e (a : Fin r) : PI.QnWCellW.swp k r (eI k r a) = esI k r a := by
  have := a.isLt
  apply Fin.ext
  rw [PI.QnWCellW.swp_val, if_neg (by rw [eI_val]; omega), eI_val, esI_val]

/- English proof (translation)
Rewrite using `[← swp_e, PI.QnWCellW.swp_swp]`.
-/
theorem swp_es (a : Fin r) : PI.QnWCellW.swp k r (esI k r a) = eI k r a := by
  rw [← swp_e, PI.QnWCellW.swp_swp]

/- English proof (translation)
Simplify using `[PI.QnWCellW.cf, eI]`.
-/
theorem cf_e (c : Fin r → ℂ) (a : Fin r) : PI.QnWCellW.cf k r c (eI k r a) = (star (c a))⁻¹ := by
  simp [PI.QnWCellW.cf, eI]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `PI.QnWCellW.cf`. Rewrite using `[if_neg (by rw [esI_val]; omega), if_neg (by rw [esI_val]; omega), esI_val, show 2 * r + k - (2 * r + k - a.val) = a.val by omega, PI.QnWCellW.cN_val]`.
-/
theorem cf_es (c : Fin r → ℂ) (a : Fin r) : PI.QnWCellW.cf k r c (esI k r a) = c a := by
  have := a.isLt
  unfold PI.QnWCellW.cf
  rw [if_neg (by rw [esI_val]; omega), if_neg (by rw [esI_val]; omega), esI_val, show 2 * r + k - (2 * r + k - a.val) = a.val by omega,
    PI.QnWCellW.cN_val]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite using `[PI.QnWCellW.swp_swp]`. Introduce and unpack `rfl`. Rewrite using `[PI.QnWCellW.swp_swp]`.
-/
theorem swp_eq_iff (p q : Fin (2 * r + k + 1)) : PI.QnWCellW.swp k r p = q ↔ p = PI.QnWCellW.swp k r q := by
  constructor
  · rintro rfl; rw [PI.QnWCellW.swp_swp]
  · rintro rfl; rw [PI.QnWCellW.swp_swp]

variable {g : Mx k r}

/- English proof (translation)
Rewrite using `[cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1]`. Simplify using `only [swp_eq_iff, swp_e]`. Use `split_ifs with h`. Rewrite using `[h, cf_es, mul_one]`. Rewrite using `[mul_zero]`.
-/
theorem col_e (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p (eI k r a) = if p = esI k r a then c a else 0 := by
  rw [cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1]
  simp only [swp_eq_iff, swp_e]
  split_ifs with h
  · rw [h, cf_es, mul_one]
  · rw [mul_zero]

/- English proof (translation)
Rewrite using `[cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2]`. Simplify using `only [swp_eq_iff, swp_es]`. Use `split_ifs with h`. Rewrite using `[h, cf_e, mul_one]`. Rewrite using `[mul_zero]`.
-/
theorem col_es (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p (esI k r a) = if p = eI k r a then (star (c a))⁻¹ else 0 := by
  rw [cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2]
  simp only [swp_eq_iff, swp_es]
  split_ifs with h
  · rw [h, cf_e, mul_one]
  · rw [mul_zero]

/- English proof (translation)
Use `WeylGroupFacts.row_of_fixed_col hg.1 (eI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1)` as an intermediate fact. Rewrite `this` using `[Qx3.tau_e]`. Rewrite using `[cell_apply, swp_e, cf_e, this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem row_e (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) (eI k r a) q = if esI k r a = q then (star (c a))⁻¹ else 0 := by
  have := WeylGroupFacts.row_of_fixed_col hg.1 (eI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1)
  rw [Qx3.tau_e] at this
  rw [cell_apply, swp_e, cf_e, this]
  split_ifs <;> simp

/- English proof (translation)
Use `WeylGroupFacts.row_of_fixed_col hg.1 (esI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2)` as an intermediate fact. Rewrite `this` using `[Qx3.tau_es]`. Rewrite using `[cell_apply, swp_es, cf_es, this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem row_es (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) (esI k r a) q = if eI k r a = q then c a else 0 := by
  have := WeylGroupFacts.row_of_fixed_col hg.1 (esI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2)
  rw [Qx3.tau_es] at this
  rw [cell_apply, swp_es, cf_es, this]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `Qx3.glev_mul (Qx3.wlist_glev hc _) (Qx3.glev_mono (Fin.zero_le _) hg)`.
-/
theorem cell_mem (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    wCell k r (Fin.last r) c * g ∈ Glev k r 0 :=
  Qx3.glev_mul (Qx3.wlist_glev hc _) (Qx3.glev_mono (Fin.zero_le _) hg)

def hX (k : ℕ) {r : ℕ} (a b : Fin r) (s : ℂ) : Mx k r :=
  s • Matrix.single (eI k r a) (eI k r b) (1 : ℂ) - star s • Matrix.single (esI k r b) (esI k r a) (1 : ℂ)

/- English proof (translation)
Unfold `hpart1 hX`. Rewrite using `[Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI, smul_sub]`. Establish `h2 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[h2]`.
-/
theorem hpart1_eq (a b : Fin r) :
    hpart1 (Hpk k r) (Matrix.single (eI k r a) (eI k r b) (1 : ℂ)) = hX k a b (1 / 2) := by
  unfold hpart1 hX
  rw [Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI, smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]

/- English proof (translation)
Unfold `hpart2 hX`. Rewrite using `[Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI, smul_add, CutHL.half_I]`. Establish `h2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2)`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`. Rewrite using `[h2, neg_smul, sub_neg_eq_add]`.
-/
theorem hpart2_eq (a b : Fin r) :
    hpart2 (Hpk k r) (Matrix.single (eI k r a) (eI k r b) (1 : ℂ)) = hX k a b (-Complex.I / 2) := by
  unfold hpart2 hX
  rw [Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI,
    smul_add, CutHL.half_I]
  have h2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h2, neg_smul, sub_neg_eq_add]

/- English proof (translation)
Unfold `QRR.dag hX`. Rewrite using `[Qx2.hpk_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT, SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_m …`.
-/
theorem dag_hX (a b : Fin r) (s : ℂ) : QRR.dag k r (hX k a b s) = -hX k a b s := by
  unfold QRR.dag hX
  rw [Qx2.hpk_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    SingleEntryHermitianProducts.single_conjT, SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI, LevelPointCoordinates.single_mul_hpk_eI, LevelPointCoordinates.single_mul_hpk_esI, neg_sub]

/- English proof (translation)
Establish `ha` using `hc a`. Establish `hb` using `hc b`. Establish `ha' : star (c a) ≠ 0` using `star_ne_zero.2 ha`. Establish `hb' : star (c b) ≠ 0` using `star_ne_zero.2 hb`. Use `set x := wCell k r (Fin.last r) c * g with hx`.

Establish `e1 : x * Matrix.single (eI k r a) (eI k r b) (1 : ℂ) = (c a / c b) • (Matrix.single (esI k r a) (esI k r b) (1 : ℂ) * x)`. Use extensionality with `p q`. Distinguish the cases in `hq : q = eI k r b`. Substitute `hq` using the available equality. Rewrite using `[Matrix.mul_single_apply_same, hx, col_e hg, Matrix.smul_apply]`.

Distinguish the cases in `hp : p = esI k r a`. Substitute `hp` using the available equality. Rewrite using `[Matrix.single_mul_apply_same, row_es hg]`. Simplify using `[hb]`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]`.

Simplify using `[hp]`. Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]`. Distinguish the cases in `hp : p = esI k r a`. Substitute `hp` using the available equality. Rewrite using `[Matrix.single_mul_apply_same, hx, row_es hg]`.

Simplify using `[Ne.symm hq]`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]`. Simplify using the standard rewrite rules. Establish `e2 : x * Matrix.single (esI k r b) (esI k r a) (1 : ℂ) = star (c a / c b) • (Matrix.single (eI k r b) (eI k r a) (1 : ℂ) * x)`. Use extensionality with `p q`.

Distinguish the cases in `hq : q = esI k r a`. Substitute `hq` using the available equality. Rewrite using `[Matrix.mul_single_apply_same, hx, col_es hg, Matrix.smul_apply]`. Distinguish the cases in `hp : p = eI k r b`. Substitute `hp` using the available equality.

Rewrite using `[Matrix.single_mul_apply_same, row_e hg, star_div₀]`. Simplify using `only [if_true, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]`. Simplify using `[hp]`.

Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]`. Distinguish the cases in `hp : p = eI k r b`. Substitute `hp` using the available equality. Rewrite using `[Matrix.single_mul_apply_same, hx, row_e hg]`. Simplify using `[Ne.symm hq]`.

Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]`. Simplify using the standard rewrite rules. Unfold `hX`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e1, e2, smul_smul, smul_smul, star_neg, star_star, star_mul', neg_smul, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem cell_mul_hX (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (a b : Fin r) (s : ℂ) :
    wCell k r (Fin.last r) c * g * hX k a b s =
      hX k b a (-star (s * (c a / c b))) * (wCell k r (Fin.last r) c * g) := by
  have ha := hc a
  have hb := hc b
  have ha' : star (c a) ≠ 0 := star_ne_zero.2 ha
  have hb' : star (c b) ≠ 0 := star_ne_zero.2 hb
  set x := wCell k r (Fin.last r) c * g with hx
  have e1 : x * Matrix.single (eI k r a) (eI k r b) (1 : ℂ) =
      (c a / c b) • (Matrix.single (esI k r a) (esI k r b) (1 : ℂ) * x) := by
    ext p q
    by_cases hq : q = eI k r b
    · subst hq
      rw [Matrix.mul_single_apply_same, hx, col_e hg, Matrix.smul_apply]
      by_cases hp : p = esI k r a
      · subst hp
        rw [Matrix.single_mul_apply_same, row_es hg]; simp [hb]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp [hp]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]
      by_cases hp : p = esI k r a
      · subst hp
        rw [Matrix.single_mul_apply_same, hx, row_es hg]; simp [Ne.symm hq]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp
  have e2 : x * Matrix.single (esI k r b) (esI k r a) (1 : ℂ) =
      star (c a / c b) • (Matrix.single (eI k r b) (eI k r a) (1 : ℂ) * x) := by
    ext p q
    by_cases hq : q = esI k r a
    · subst hq
      rw [Matrix.mul_single_apply_same, hx, col_es hg, Matrix.smul_apply]
      by_cases hp : p = eI k r b
      · subst hp
        rw [Matrix.single_mul_apply_same, row_e hg, star_div₀]
        simp only [if_true, smul_eq_mul]
        field_simp
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp [hp]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]
      by_cases hp : p = eI k r b
      · subst hp
        rw [Matrix.single_mul_apply_same, hx, row_e hg]; simp [Ne.symm hq]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp
  unfold hX
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e1, e2,
    smul_smul, smul_smul, star_neg, star_star, star_mul', neg_smul, neg_smul]
  abel

/- English proof (translation)
Introduce `i j hij`. Establish `ha` using `a.isLt`. Distinguish the cases in `h1 : eI k r b = i ∧ eI k r a = j`. Take `⟨rfl, rfl⟩` from `h1 left`. Rewrite using `[eI_val, eI_val]`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h2 : esI k r a = i ∧ esI k r b = j`. Take `⟨rfl, rfl⟩` from `h2 right`. Rewrite using `[esI_val, esI_val]`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Apply `hij` to reduce the goal to its premises. Simplify using `[hX, Matrix.single_apply, h1, h2]`.
-/
theorem pat_hX {a b : Fin r} (hab : b.val < a.val) (s : ℂ) : QRR.Pat k r b (hX k b a s) := by
  intro i j hij
  have ha := a.isLt
  by_cases h1 : eI k r b = i ∧ eI k r a = j
  · obtain ⟨rfl, rfl⟩ := h1
    left; rw [eI_val, eI_val]; omega
  by_cases h2 : esI k r a = i ∧ esI k r b = j
  · obtain ⟨rfl, rfl⟩ := h2
    right; rw [esI_val, esI_val]; omega
  exfalso; apply hij
  simp [hX, Matrix.single_apply, h1, h2]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hrow : ∀ (l : Fin r) q, hX k b a s (eI k r l) q = if l = b ∧ eI k r a = q then s else 0`. Introduce `l q`. Establish `h1 : esI k r a ≠ eI k r l`. Use `l.isLt` as an intermediate fact.

Simplify using `only [eI, esI, ne_eq, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (eI k r b = eI k r l) ↔ l = b`. Simplify using `only [eI, Fin.ext_iff]`. Conclude with `eq_comm`.

Simplify using `[hX, Matrix.single_apply, h1, h2]`. Unfold `ell`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[dif_pos (by omega), hrow]`. Simplify using `[eI, Fin.ext_iff]`.

Introduce `l _ hl split_ifs with h`. Rewrite using `[hrow, if_neg (fun h => hl h.1)]`. Simplify using `only [Matrix.mulVec, dotProduct, hrow]`. Simplify using `[hl]`. Simplify using the standard rewrite rules.
-/
theorem ell_hX {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {a b : Fin r} (hab : b.val < a.val) (s : ℂ) :
    ell k r z (hX k b a s) = if a.val = b.val + 1 then s else 0 := by
  have ha := a.isLt
  have hrow : ∀ (l : Fin r) q, hX k b a s (eI k r l) q = if l = b ∧ eI k r a = q then s else 0 := by
    intro l q
    have h1 : esI k r a ≠ eI k r l := by
      have := l.isLt
      simp only [eI, esI, ne_eq, Fin.ext_iff]; omega
    have h2 : (eI k r b = eI k r l) ↔ l = b := by
      simp only [eI, Fin.ext_iff]; exact eq_comm
    simp [hX, Matrix.single_apply, h1, h2]
  unfold ell
  rw [Finset.sum_eq_single b]
  · rw [dif_pos (by omega), hrow]
    simp [eI, Fin.ext_iff]
  · intro l _ hl
    split_ifs with h
    · rw [hrow, if_neg (fun h => hl h.1)]
    · simp only [Matrix.mulVec, dotProduct, hrow]
      simp [hl]
  · simp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hxG` using `cell_mem hg hc`. Establish `hconj` using `cell_mul_hX hg hc a b s`. Use `set x := wCell k r (Fin.last r) c * g with hx`. Establish `hdet : IsUnit x.det` using `WeylGroupFacts.isUnit_of_uh hxG.1`. Establish `hu : IsUnit x` using `(Matrix.isUnit_iff_isUnit_det x).2 hdet`.

Establish `h1` using `HeadLetterLemmas.rdV_of_eq z hz (fun y => Ψ (y * x)) 1 (fun n hn => by simpa using hΨ n hn) b _ (pat_hX hab (-star (s * (c a / c b)))) (dag_hX _ _ _)`. Establish `h2 : RdV (hX k a b s) Ψ x = RdV (hX k b a (-star (s * (c a / c b)))) (fun y => Ψ (y * x)) 1`. Unfold `RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Use `congr 1`. Establish `e : (t : ℂ) • hX k b a (-star (s * (c a / c b))) = x * ((t : ℂ) • hX k a b s) * x⁻¹`. Rewrite using `[Matrix.mul_smul, hconj, Matrix.smul_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]`. Rewrite using `[e, Matrix.exp_conj _ _ hu, Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hdet]`. Rewrite using `[h2, h1, ell_hX hz hab, Matrix.one_mul]`.

Use `congr 1`. Use `split_ifs`. Rewrite using `[star_neg, star_star]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem rdV_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) (Ψ : Mx k r → E)
    (hΨ : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, Ψ (n * (wCell k r (Fin.last r) c * g)) =
      psi k r z cStd n • Ψ (wCell k r (Fin.last r) c * g))
    {a b : Fin r} (hab : b.val < a.val) (s : ℂ) :
    RdV (hX k a b s) Ψ (wCell k r (Fin.last r) c * g) =
      (if a.val = b.val + 1 then s * (c a / c b) - star (s * (c a / c b)) else 0) •
        Ψ (wCell k r (Fin.last r) c * g) := by
  have hxG := cell_mem hg hc
  have hconj := cell_mul_hX hg hc a b s
  set x := wCell k r (Fin.last r) c * g with hx
  have hdet : IsUnit x.det := WeylGroupFacts.isUnit_of_uh hxG.1
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hdet
  have h1 := HeadLetterLemmas.rdV_of_eq z hz (fun y => Ψ (y * x)) 1 (fun n hn => by simpa using hΨ n hn) b _
    (pat_hX hab (-star (s * (c a / c b)))) (dag_hX _ _ _)
  have h2 : RdV (hX k a b s) Ψ x = RdV (hX k b a (-star (s * (c a / c b)))) (fun y => Ψ (y * x)) 1 := by
    unfold RdV
    congr 1
    funext t
    congr 1
    have e : (t : ℂ) • hX k b a (-star (s * (c a / c b))) = x * ((t : ℂ) • hX k a b s) * x⁻¹ := by
      rw [Matrix.mul_smul, hconj, Matrix.smul_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
    rw [e, Matrix.exp_conj _ _ hu, Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hdet]
  rw [h2, h1, ell_hX hz hab, Matrix.one_mul]
  congr 1
  split_ifs
  · rw [star_neg, star_star]; ring
  · simp

/- English proof (translation)
Use `show EabH (Hpk k r) _ _ Ψ _ = _`. Unfold `EabH`. Rewrite using `[hpart1_eq, hpart2_eq, rdV_left hz hg hc Ψ hΨ hab, rdV_left hz hg hc Ψ hΨ hab, smul_smul, ← add_smul]`. Use `congr 1`. Use `split_ifs`.

Generalize the expression as in `c a / c b = w`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Simplify using the standard rewrite rules.
-/
theorem left_rule {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) (Ψ : Mx k r → E)
    (hΨ : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, Ψ (n * (wCell k r (Fin.last r) c * g)) =
      psi k r z cStd n • Ψ (wCell k r (Fin.last r) c * g))
    {a b : Fin r} (hab : b.val < a.val) :
    EH k r (eI k r a) (eI k r b) Ψ (wCell k r (Fin.last r) c * g) =
      (if a.val = b.val + 1 then c a / c b else 0) • Ψ (wCell k r (Fin.last r) c * g) := by
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_eq, hpart2_eq, rdV_left hz hg hc Ψ hΨ hab, rdV_left hz hg hc Ψ hΨ hab, smul_smul, ← add_smul]
  congr 1
  split_ifs
  · generalize c a / c b = w
    apply Complex.ext <;> simp <;> ring
  · simp

/- English proof (translation)
Establish `hne : eI k r a ≠ esI k r a` using `PI.QnWCellW.eI_ne_esI k r a`. Use extensionality with `p q`. Simplify using `only [hX, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality.

Distinguish the cases in `h1 : p = eI k r a`. Substitute `h1` using the available equality. Simplify using `[hne.symm]`. Distinguish the cases in `h2 : p = esI k r a`. Substitute `h2` using the available equality.

Simplify using `[hne, hne.symm]`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`. Rewrite using `[if_neg hpq, if_neg (fun h => hpq (h.1.symm.trans h.2)), if_neg (fun h => hpq (h.1.symm.trans h.2))]`. Simplify using the standard rewrite rules.
-/
theorem hX_diag (a : Fin r) (s : ℂ) :
    hX k a a s = Matrix.diagonal fun q => if q = eI k r a then s else if q = esI k r a then -star s else 0 := by
  have hne : eI k r a ≠ esI k r a := PI.QnWCellW.eI_ne_esI k r a
  ext p q
  simp only [hX, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r a
    · subst h1; simp [hne.symm]
    · by_cases h2 : p = esI k r a
      · subst h2; simp [hne, hne.symm]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · rw [if_neg hpq, if_neg (fun h => hpq (h.1.symm.trans h.2)), if_neg (fun h => hpq (h.1.symm.trans h.2))]
    simp

/- English proof (translation)
Establish `h1' : p.val ≠ a.val` using `fun h => h1 (Fin.ext h)`. Establish `h2' : p.val ≠ 2 * r + k - a.val` using `fun h => h2 (Fin.ext h)`. Establish `hp` using `p.isLt`. Establish `hN : ∀ j, j ≠ a.val → PI.QnWCellW.cN r (Function.update c a v) j = PI.QnWCellW.cN r c j`. Introduce `j hj`.

Unfold `PI.QnWCellW.cN`. Use `split_ifs with h`. Rewrite using `[Function.update_of_ne (fun e => hj (congrArg Fin.val e))]`. Both sides reduce to the same expression. Unfold `PI.QnWCellW.cf`.

Rewrite using `[hN _ h1', hN _ (by omega)]`.
-/
theorem cf_update (c : Fin r → ℂ) (a : Fin r) (v : ℂ) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r a)
    (h2 : p ≠ esI k r a) : PI.QnWCellW.cf k r (Function.update c a v) p = PI.QnWCellW.cf k r c p := by
  have h1' : p.val ≠ a.val := fun h => h1 (Fin.ext h)
  have h2' : p.val ≠ 2 * r + k - a.val := fun h => h2 (Fin.ext h)
  have hp := p.isLt
  have hN : ∀ j, j ≠ a.val → PI.QnWCellW.cN r (Function.update c a v) j = PI.QnWCellW.cN r c j := by
    intro j hj
    unfold PI.QnWCellW.cN
    split_ifs with h
    · rw [Function.update_of_ne (fun e => hj (congrArg Fin.val e))]
    · rfl
  unfold PI.QnWCellW.cf
  rw [hN _ h1', hN _ (by omega)]

/- English proof (translation)
Establish `hne : eI k r a ≠ esI k r a` using `PI.QnWCellW.eI_ne_esI k r a`. Rewrite using `[hX_diag, ← Matrix.diagonal_smul, Matrix.exp_diagonal]`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Distinguish the cases in `h1 : q = eI k r a`. Substitute `h1` using the available equality. Rewrite using `[col_e hg, col_e hg]`. Apply the tactic sequence `split_ifs <;> simp_all`. Distinguish the cases in `h2 : q = esI k r a`.

Substitute `h2` using the available equality. Rewrite using `[col_es hg, col_es hg, if_neg h1, if_pos rfl]`. Use `split_ifs`. Rewrite using `[Function.update_self, star_mul', mul_inv, mul_neg, Complex.exp_neg]`. Simplify using `[← Complex.exp_conj]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h1, if_neg h2, mul_zero, Complex.exp_zero, mul_one]`. Distinguish the cases in `h3 : p = eI k r a`. Substitute `h3` using the available equality. Rewrite using `[row_e hg, row_e hg, if_neg (Ne.symm h2), if_neg (Ne.symm h2)]`.

Distinguish the cases in `h4 : p = esI k r a`. Substitute `h4` using the available equality. Rewrite using `[row_es hg, row_es hg, if_neg (Ne.symm h1), if_neg (Ne.symm h1)]`. Rewrite using `[cell_apply, cell_apply, cf_update c a _ h3 h4]`.
-/
theorem cell_mul_exp (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (s : ℂ) (t : ℝ) :
    wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s) =
      wCell k r (Fin.last r) (Function.update c a (c a * Complex.exp (t * s))) * g := by
  have hne : eI k r a ≠ esI k r a := PI.QnWCellW.eI_ne_esI k r a
  rw [hX_diag, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : q = eI k r a
  · subst h1
    rw [col_e hg, col_e hg]
    split_ifs <;> simp_all
  · by_cases h2 : q = esI k r a
    · subst h2
      rw [col_es hg, col_es hg, if_neg h1, if_pos rfl]
      split_ifs
      · rw [Function.update_self, star_mul', mul_inv, mul_neg, Complex.exp_neg]
        simp [← Complex.exp_conj]
      · simp
    · rw [if_neg h1, if_neg h2, mul_zero, Complex.exp_zero, mul_one]
      by_cases h3 : p = eI k r a
      · subst h3
        rw [row_e hg, row_e hg, if_neg (Ne.symm h2), if_neg (Ne.symm h2)]
      · by_cases h4 : p = esI k r a
        · subst h4
          rw [row_es hg, row_es hg, if_neg (Ne.symm h1), if_neg (Ne.symm h1)]
        · rw [cell_apply, cell_apply, cf_update c a _ h3 h4]

/- English proof (translation)
Simplify using `only [Fin.val_last, Fin.is_lt, if_true]`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Function.update_self, norm_mul, Complex.norm_exp, mul_pow, Real.exp_nat_mul, ← mul_assoc, mul_comm (‖c a‖ ^ _)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.mem_erase.1 hl).1]`.
-/
theorem gauge_update (c : Fin r → ℂ) (a : Fin r) (w : ℂ) :
    (∏ l : Fin r, (if l.val < (Fin.last r).val then ‖Function.update c a (c a * Complex.exp w) l‖ ^ (Mdim k r l - 1)
      else 1) : ℝ) =
      Real.exp (((Mdim k r a - 1 : ℕ) : ℝ) * w.re) *
        ∏ l : Fin r, (if l.val < (Fin.last r).val then ‖c l‖ ^ (Mdim k r l - 1) else 1) := by
  simp only [Fin.val_last, Fin.is_lt, if_true]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    Function.update_self, norm_mul, Complex.norm_exp, mul_pow, Real.exp_nat_mul, ← mul_assoc, mul_comm (‖c a‖ ^ _)]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.mem_erase.1 hl).1]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hxG` using `cell_mem hg hc`. Establish `hd : DifferentiableAt ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c`. Take `⟨U, F, hU, hxU, hF, hFU⟩` from `P5.Rad.sf_resG hS (c, g) ⟨hc, hx⟩ hg`. Establish `h1 : DifferentiableAt ℝ F (c, g)` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)`. Establish `h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c` using `h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))`.

Use `h2.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hm : ∀ᶠ c' in 𝓝 c, (c', g) ∈ U` using `(Continuous.prodMk_left g).continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)`. Use `filter_upwards [hm] with c' h using hFU (c', g) h hg`. Establish `hcurve : HasDerivAt (fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) (Pi.single a (s * c a)) 0`. Use `hasDerivAt_pi.2 fun l => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : l = a`. Substitute `hl` using the available equality. Simplify using `only [Function.update_self, Pi.single_eq_same]`. Establish `h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp`. Use `((h0.mul_const s).cexp).const_mul (c l)` as an intermediate fact.

Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using `[mul_comm]`. Simplify using `only [Function.update_of_ne hl, Pi.single_eq_of_ne hl]`. Conclude with `hasDerivAt_const _ _`. Establish `h1` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)`.

Establish `hΨ : HasDerivAt (fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s))) (RdV (hX k a a s) Ψ (wCell k r (Fin.last r) c * g)) 0`. Take `⟨U, F, hU, hxU, hF, hFU⟩` from `hS _ ⟨hxG, hx⟩`. Establish `hd' : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g)` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)`. Establish `hlie : inLieLev k r 0 (hX k a a s)`. Use `⟨?_, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩` and prove the remaining obligations.

Unfold `hX`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT, SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, LevelPointCoordinates.single_mul_hpk_eI, L …`. Normalize the expressions using the abelian group laws. Conclude with `(Qx2.hasDeriv_ext hU hxU hxG hlie hd' hFU).differentiableAt.hasDerivAt`. Use `set n : ℝ := ((Mdim k r a - 1 : ℕ) : ℝ) with hn`.

Use `set γ : ℝ := ∏ l : Fin r, (if l.val < (Fin.last r).val then ‖c l‖ ^ (Mdim k r l - 1) else 1) with hγ`. Establish `hγd : HasDerivAt (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) ((n * s.re * γ : ℝ) : ℂ) 0`. Use `((((hasDerivAt_id (0 : ℝ)).mul_const s.re).const_mul n).exp.mul_const γ).ofReal_comp` as an intermediate fact. Simplify using `using this`. Establish `h2` using `hγd.smul hΨ`.

Establish `e : ((fun c' => resG k r (Fin.last r) Ψ c' g) ∘ fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) = (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) • fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s))`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp, resG, Pi.smul_apply']`. Rewrite using `[gauge_update, cell_mul_exp hg, Complex.re_ofReal_mul]`. Rewrite `h1` using `[e]`.

Rewrite using `[h1.unique h2]`. Simplify using `only [resG, ← hγ, smul_smul]`. Simplify using the standard rewrite rules.
-/
theorem fderiv_resG {D : Set (Mx k r)} {Ψ : Mx k r → E} (hS : SmoothLev k r 0 D Ψ) (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (a : Fin r) (s : ℂ) :
    fderiv ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c (Pi.single a (s * c a)) =
      resG k r (Fin.last r) (RdV (hX k a a s) Ψ) c g +
        ((((Mdim k r a - 1 : ℕ) : ℝ) * s.re : ℝ) : ℂ) • resG k r (Fin.last r) Ψ c g := by
  have hxG := cell_mem hg hc
  have hd : DifferentiableAt ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c := by
    obtain ⟨U, F, hU, hxU, hF, hFU⟩ := P5.Rad.sf_resG hS (c, g) ⟨hc, hx⟩ hg
    have h1 : DifferentiableAt ℝ F (c, g) := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
    have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
      h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
    refine h2.congr_of_eventuallyEq ?_
    have hm : ∀ᶠ c' in 𝓝 c, (c', g) ∈ U :=
      (Continuous.prodMk_left g).continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
    filter_upwards [hm] with c' h using hFU (c', g) h hg
  have hcurve : HasDerivAt (fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) (Pi.single a (s * c a)) 0 := by
    refine hasDerivAt_pi.2 fun l => ?_
    by_cases hl : l = a
    · subst hl
      simp only [Function.update_self, Pi.single_eq_same]
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have := ((h0.mul_const s).cexp).const_mul (c l)
      refine this.congr_deriv ?_
      simp [mul_comm]
    · simp only [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
      exact hasDerivAt_const _ _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have hΨ : HasDerivAt (fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s)))
      (RdV (hX k a a s) Ψ (wCell k r (Fin.last r) c * g)) 0 := by
    obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS _ ⟨hxG, hx⟩
    have hd' : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
    have hlie : inLieLev k r 0 (hX k a a s) := by
      refine ⟨?_, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩
      unfold hX
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
        SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
        LevelPointCoordinates.single_mul_hpk_eI, LevelPointCoordinates.single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
        SingleEntryHermitianProducts.hpk_mul_single_eI, SingleEntryHermitianProducts.hpk_mul_single_esI]
      abel
    exact (Qx2.hasDeriv_ext hU hxU hxG hlie hd' hFU).differentiableAt.hasDerivAt
  set n : ℝ := ((Mdim k r a - 1 : ℕ) : ℝ) with hn
  set γ : ℝ := ∏ l : Fin r, (if l.val < (Fin.last r).val then ‖c l‖ ^ (Mdim k r l - 1) else 1) with hγ
  have hγd : HasDerivAt (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) ((n * s.re * γ : ℝ) : ℂ) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const s.re).const_mul n).exp.mul_const γ).ofReal_comp
    simpa using this
  have h2 := hγd.smul hΨ
  have e : ((fun c' => resG k r (Fin.last r) Ψ c' g) ∘ fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) =
      (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) •
        fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s)) := by
    funext t
    simp only [Function.comp, resG, Pi.smul_apply']
    rw [gauge_update, cell_mul_exp hg, Complex.re_ofReal_mul]
  rw [e] at h1
  rw [h1.unique h2]
  simp only [resG, ← hγ, smul_smul]
  simp

/- English proof (translation)
Establish `h1` using `fderiv_resG hS hg hc hx a (1 / 2)`. Establish `h2` using `fderiv_resG hS hg hc hx a (-Complex.I / 2)`. Establish `h3` using `CutHL.torus_id ((fderiv ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c).comp (ContinuousLinearMap.single ℝ (fun _ : Fin r => ℂ) a)) (c a)`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] at h3`. Unfold `pOp wirt`.

Rewrite using `[if_pos hc, ← h3, h1, h2]`. Establish `hM : ((Mdim k r a - 1 : ℕ) : ℂ) = 2 * ((r : ℂ) - (a.val : ℂ)) + k`. Unfold `Mdim`. Rewrite using `[Nat.add_sub_cancel]`. Move the coercions through the operations in `[Nat.cast_sub a.isLt.le]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (1 / 2 : ℂ).re : ℝ) : ℂ) = ((r : ℂ) - (a.val : ℂ)) + (k : ℂ) / 2`. Establish `: (1 / 2 : ℂ).re = 1 / 2` using `by norm_num`. Rewrite using `[this]`. Use `push_cast`.

Rewrite using `[hM]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (-Complex.I / 2 : ℂ).re : ℝ) : ℂ) = 0` using `by simp`. Rewrite using `[e1, e2, zero_smul, add_zero]`. Simplify using `only [resG, EH, EabH, hpart1_eq, hpart2_eq]`.

Use `module`.
-/
theorem torus_rule {D : Set (Mx k r)} {Ψ : Mx k r → E} (hS : SmoothLev k r 0 D Ψ) (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (a : Fin r) :
    pOp a (fun c' => resG k r (Fin.last r) Ψ c' g) c =
      resG k r (Fin.last r) (EH k r (eI k r a) (eI k r a) Ψ) c g +
        (((r : ℂ) - (a.val : ℂ)) + (k : ℂ) / 2) • resG k r (Fin.last r) Ψ c g := by
  have h1 := fderiv_resG hS hg hc hx a (1 / 2)
  have h2 := fderiv_resG hS hg hc hx a (-Complex.I / 2)
  have h3 := CutHL.torus_id ((fderiv ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin r => ℂ) a)) (c a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] at h3
  unfold pOp wirt
  rw [if_pos hc, ← h3, h1, h2]
  have hM : ((Mdim k r a - 1 : ℕ) : ℂ) = 2 * ((r : ℂ) - (a.val : ℂ)) + k := by
    unfold Mdim
    rw [Nat.add_sub_cancel]
    push_cast [Nat.cast_sub a.isLt.le]
    ring
  have e1 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (1 / 2 : ℂ).re : ℝ) : ℂ) = ((r : ℂ) - (a.val : ℂ)) + (k : ℂ) / 2 := by
    have : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [this]; push_cast; rw [hM]; ring
  have e2 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (-Complex.I / 2 : ℂ).re : ℝ) : ℂ) = 0 := by simp
  rw [e1, e2, zero_smul, add_zero]
  simp only [resG, EH, EabH, hpart1_eq, hpart2_eq]
  module

end

end GlobalTheory.HatNF.CellRules
