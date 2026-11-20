import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma lsz_pos {k r : ℕ} (X : B.Mat k r) : 0 < lsz X := lt_of_lt_of_le one_pos (le_max_left _ _)

def sc {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (((lsz X)⁻¹ : ℝ) : ℂ) • X

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma sc_back {k r : ℕ} (X : B.Mat k r) : ((lsz X : ℝ) : ℂ) • sc X = X := by
  unfold sc
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (lsz_pos X).ne', Complex.ofReal_one, one_smul]

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
lemma entry_le_lsz {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖X a b‖ ≤ lsz X := by
  calc ‖X a b‖ = ‖(Matrix.of.symm X) a b‖ := rfl
    _ ≤ ‖(Matrix.of.symm X) a‖ := norm_le_pi_norm _ b
    _ ≤ ‖Matrix.of.symm X‖ := norm_le_pi_norm _ a
    _ ≤ lsz X := le_max_right _ _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma sc_entry {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖sc X a b‖ ≤ 1 := by
  have hp := lsz_pos X
  have h := entry_le_lsz X a b
  have e : sc X a b = (((lsz X)⁻¹ : ℝ) : ℂ) * X a b := rfl
  rw [e, norm_mul, Complex.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_le_iff₀ hp, mul_one]
  exact h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma sc_inLieP {k j ρ : ℕ} {X : B.Mat k (j + ρ)} (hX : inLieP k j ρ X) : inLieP k j ρ (sc X) := by
  obtain ⟨h1, h2⟩ := hX
  have hs : star ((((lsz X)⁻¹ : ℝ) : ℂ)) = (((lsz X)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  refine ⟨?_, fun i b hb hi => ?_⟩
  · unfold B.inLie at h1 ⊢
    unfold sc
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · have e : sc X i b = (((lsz X)⁻¹ : ℝ) : ℂ) * X i b := rfl
    rw [e, h2 i b hb hi, mul_zero]

def scx {k r : ℕ} (x : Bool × B.Mat k r) : Bool × B.Mat k r := (x.1, sc x.2)

/- English proof (translation)
Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
private lemma LdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    B.LdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • B.LdV Y F g := by
  simp only [B.LdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (NormedSpace.exp (-((s : ℂ) • Y)) * g)) 0,
    mul_zero, Complex.coe_smul]

/- English proof (translation)
Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
private lemma RdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    Formalism.REAL.RdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • Formalism.REAL.RdV Y F g := by
  simp only [Formalism.REAL.RdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (g * NormedSpace.exp ((s : ℂ) • Y))) 0,
    mul_zero, Complex.coe_smul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Split into cases according to the possible forms of the given data. A detailed English derivation is pending.
-/
private lemma Dx_eq_lsz_smul_Dx_scx {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : Bool × B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dx x F g = ((lsz x.2 : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) F g := by
  obtain ⟨b, X⟩ := x
  have hX : X = ((lsz X : ℝ) : ℂ) • sc X := (sc_back X).symm
  cases b
  · show Formalism.REAL.RdV X F g = ((lsz X : ℝ) : ℂ) • Formalism.REAL.RdV (sc X) F g
    conv_lhs => rw [hX]
    exact RdV_ofReal_smul _ _ _ _
  · show B.LdV X F g = ((lsz X : ℝ) : ℂ) • B.LdV (sc X) F g
    conv_lhs => rw [hX]
    exact LdV_ofReal_smul _ _ _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma dw_scale {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    P.BetaSesquilinearity.Dw w f = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := by
  induction w with
  | nil => funext g; simp [P.BetaSesquilinearity.Dw]
  | cons x w ih =>
    funext g
    have h1 : P.BetaSesquilinearity.Dw (x :: w) f = P.BetaSesquilinearity.Dx x (P.BetaSesquilinearity.Dw w f) := rfl
    have h2 : P.BetaSesquilinearity.Dw ((x :: w).map scx) f = P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) := rfl
    rw [h1, h2, Dx_eq_lsz_smul_Dx_scx, ih]
    have h3 : P.BetaSesquilinearity.Dx (scx x) (fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g)
        = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) g :=
      P.BetaSesquilinearity.Dw_smul _ [scx x] _
    rw [h3, List.map_cons, List.prod_cons, Complex.ofReal_mul, mul_smul]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma dw_scale_at {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dw w f g = (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := congrFun (dw_scale w f) g

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma map_lsz_LR {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map (fun x => lsz x.2) = (u ++ v).map lsz := by
  simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR, List.map_map, Function.comp_def]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma map_scx_LR {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map scx = P.BetaSesquilinearity.wL (u.map sc) ++ P.BetaSesquilinearity.wR (v.map sc) := by
  simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR, scx, List.map_map, Function.comp_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma dLR_scale {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    B.dLR u v f g = ((((u ++ v).map lsz).prod : ℝ) : ℂ) • B.dLR (u.map sc) (v.map sc) f g := by
  rw [P.BetaSesquilinearity.dLR_eq, P.BetaSesquilinearity.dLR_eq, dw_scale_at (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v), map_lsz_LR, map_scx_LR]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem starScale : StarScale := by
  intro k j ρ E _ _ F₁ A₁ Q B₁ K hS u v hu hv hl g hg
  have hu' : unitP k j ρ (u.map sc) := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact ⟨sc_inLieP (hu Y hY), sc_entry Y⟩
  have hv' : unitP k j ρ (v.map sc) := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact ⟨sc_inLieP (hv Y hY), sc_entry Y⟩
  have hb := hS.2.2 (u.map sc) (v.map sc) hu' hv' (by simpa using hl) g hg
  have hP : 0 ≤ ((u ++ v).map lsz).prod :=
    List.prod_nonneg (fun a ha => by obtain ⟨Y, -, rfl⟩ := List.mem_map.1 ha; exact (lsz_pos Y).le)
  rw [dLR_scale, norm_smul, Complex.norm_of_nonneg hP]
  have := mul_le_mul_of_nonneg_left hb hP
  nlinarith [this]

end PI.UnitaryGroupMassFormula.UsCost
