import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.DiagonalConjDistinctValuationsEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.CuspRep
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

namespace Rig

section Theta

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaGL_val' (n : ℕ) (c : R →+* R) (g : GL (Fin n) R) :
    (thetaGL n c g).val = GlobalTheory.Tw.Phi n R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n R)ᵀ := rfl

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, GlobalTheory.Tw.Model.Phi_apply', ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Phi_conj_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (GlobalTheory.Tw.Phi n R * A * (GlobalTheory.Tw.Phi n R)ᵀ) i j = (-1) ^ (i : ℕ) * (-1) ^ (j : ℕ) * A i.rev j.rev := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, GlobalTheory.Tw.Model.Phi_apply', ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Rewrite using `[← pow_add, Fin.val_rev]`. Use `congr 1`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem neg_one_pow_mul_rev {n : ℕ} (i : Fin n) :
    ((-1 : R) ^ (i : ℕ)) * (-1) ^ (i.rev : ℕ) = (-1) ^ (n - 1) := by
  rw [← pow_add, Fin.val_rev]
  congr 1
  have := i.2
  omega

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]`.
-/
theorem diagT_val_apply {n : ℕ} (t : Fin n → Rˣ) (i j : Fin n) :
    (GlobalTheory.SmGL.diagT R (Fin n) t).val i j = if i = j then (t i : R) else 0 := by
  rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]

/- English proof (translation)
Introduce `t t' h`. Use function extensionality and compare the values at `i`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun g : GL (Fin n) R => g.val i i) h` as an intermediate fact. Simplify `this` using `[diagT_val_apply]`.
-/
theorem diagT_injective {n : ℕ} : Function.Injective (GlobalTheory.SmGL.diagT R (Fin n)) := by
  intro t t' h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) R => g.val i i) h
  simpa [diagT_val_apply] using this

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[thetaGL_val', ← map_inv (GlobalTheory.SmGL.diagT R (Fin n)) t, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply, diagT_val_apply, diagT_val_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => h (Fin.rev_injective h').symm), if_neg h, map_zero, mul_zero]`.
-/
theorem thetaGL_diagT (n : ℕ) (c : R →+* R) (t : Fin n → Rˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT R (Fin n) t) =
      GlobalTheory.SmGL.diagT R (Fin n) (fun i => (Units.map c.toMonoidHom (t i.rev))⁻¹) := by
  apply Units.ext
  ext i j
  rw [thetaGL_val', ← map_inv (GlobalTheory.SmGL.diagT R (Fin n)) t, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply,
    diagT_val_apply, diagT_val_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [if_neg (fun h' => h (Fin.rev_injective h').symm), if_neg h, map_zero, mul_zero]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[thetaGL_val', ← map_inv (thetaGL n c) g, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply, thetaGL_val', inv_inv, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.rev_rev, Fin.rev_rev, map_mul, map_mul, hc, map_pow, map_pow, map_neg, map_one]`. Establish `key : ((-1 : R) ^ (i : ℕ) * (-1) ^ (j : ℕ)) * ((-1) ^ (j.rev : ℕ) * (-1) ^ (i.rev : ℕ)) = 1`. Rewrite using `[show ((-1 : R) ^ (i : ℕ) * (-1) ^ (j : ℕ)) * ((-1) ^ (j.rev : ℕ) * (-1) ^ (i.rev : ℕ)) = ((-1) ^ (i : ℕ) * (-1) ^ (i.rev : ℕ)) * ((-1) ^ (j : ℕ) * (-1) ^ (j.rev : ℕ)) by ring, neg_one_pow_mul_rev, neg_one_pow_mul_rev, ← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Take the linear combination `(g.val i j) * key`.
-/
theorem thetaGL_thetaGL' (n : ℕ) (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin n) R) :
    thetaGL n c (thetaGL n c g) = g := by
  apply Units.ext
  ext i j
  rw [thetaGL_val', ← map_inv (thetaGL n c) g, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply, thetaGL_val',
    inv_inv, Phi_conj_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.rev_rev, Fin.rev_rev, map_mul, map_mul, hc,
    map_pow, map_pow, map_neg, map_one]
  have key : ((-1 : R) ^ (i : ℕ) * (-1) ^ (j : ℕ)) * ((-1) ^ (j.rev : ℕ) * (-1) ^ (i.rev : ℕ)) = 1 := by
    rw [show ((-1 : R) ^ (i : ℕ) * (-1) ^ (j : ℕ)) * ((-1) ^ (j.rev : ℕ) * (-1) ^ (i.rev : ℕ)) =
        ((-1) ^ (i : ℕ) * (-1) ^ (i.rev : ℕ)) * ((-1) ^ (j : ℕ) * (-1) ^ (j.rev : ℕ)) by ring,
      neg_one_pow_mul_rev, neg_one_pow_mul_rev, ← pow_add, ← two_mul, pow_mul]
    simp
  linear_combination (g.val i j) * key

/- English proof (translation)
Establish `hdet : h.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero`. Establish `hdiag : ∀ i, h.val i i ≠ 0`. Introduce `i hi`. Use `hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Conclude with `hi`. Conclude with `hoff i j hij`. Use `⟨fun i => Units.mk0 _ (hdiag i), Units.ext (Matrix.ext fun i j => ?_)⟩` and prove the remaining obligations. Rewrite using `[diagT_val_apply]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, hoff i j hij]`.
-/
theorem exists_diagT {L : Type} [Field L] {n : ℕ} (h : GL (Fin n) L) (hoff : ∀ i j, i ≠ j → h.val i j = 0) :
    ∃ η : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) η := by
  have hdet : h.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  have hdiag : ∀ i, h.val i i ≠ 0 := by
    intro i hi
    refine hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_)
    by_cases hij : i = j
    · subst hij; exact hi
    · exact hoff i j hij
  refine ⟨fun i => Units.mk0 _ (hdiag i), Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [diagT_val_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij, hoff i j hij]

end Theta

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold `ordL`. Use `split_ifs with h`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `conv_rhs => rw [← WithZero.coe_unzero h]`.

Both sides reduce to the same expression.
-/
theorem ordL_eq_neg_log' (y : L) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  split_ifs with h
  · rw [h]; rfl
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

/- English proof (translation)
The claim follows from `(Valuation.ne_zero_iff _).2 hy`.
-/
theorem v_ne_zero' {y : L} (hy : y ≠ 0) : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy

/- English proof (translation)
Establish `hϖ' : WithZero.log (Valued.v (ϖ : L)) = -1` using `by rw [ordL_eq_neg_log'] at hϖ; omega`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, WithZero.log_mul (zpow_ne_zero _ (v_ne_zero' ϖ.ne_zero)) (by rw [hu]; exact one_ne_zero), WithZero.log_zpow, hu, WithZero.log_one, hϖ', smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_v_pow_mul (ϖ u : Lˣ) (hϖ : ordL (ϖ : L) = 1) (hu : Valued.v (u : L) = 1) (k : ℤ) :
    WithZero.log (Valued.v (((ϖ ^ k * u : Lˣ)) : L)) = -k := by
  have hϖ' : WithZero.log (Valued.v (ϖ : L)) = -1 := by rw [ordL_eq_neg_log'] at hϖ; omega
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀,
    WithZero.log_mul (zpow_ne_zero _ (v_ne_zero' ϖ.ne_zero)) (by rw [hu]; exact one_ne_zero), WithZero.log_zpow, hu,
    WithZero.log_one, hϖ', smul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
/- English proof (translation)
Take `⟨η, rfl⟩` from `exists_diagT g hg.1`. Use `⟨η, rfl, fun i => ?_⟩` and prove the remaining obligations. Use `hg.2 i` as an intermediate fact. Rewrite `this` using `[diagT_val_apply, if_pos rfl]`. Then use the resulting hypothesis.
-/
theorem TO_diagT {a : ℕ} {w : Pl E} {g : GLw a w} (hg : g ∈ TO a w) :
    ∃ u : Fin a → (w.adicCompletion E)ˣ, g = GlobalTheory.SmGL.diagT _ (Fin a) u ∧ ∀ i, Valued.v (u i : w.adicCompletion E) = 1 := by
  obtain ⟨η, rfl⟩ := exists_diagT g hg.1
  refine ⟨η, rfl, fun i => ?_⟩
  have := hg.2 i
  rwa [diagT_val_apply, if_pos rfl] at this

/- English proof (translation)
Unfold `thL`. Rewrite using `[if_neg hw]`.
-/
theorem thL_eq' (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : thL n w = thetaGL n (cj w) := by
  unfold thL; rw [if_neg hw]

/- English proof (translation)
Rewrite using `[thL_eq' w hw]`. Conclude with `thetaGL_thetaGL' n (cj w) (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g`.
-/
theorem thL_thL (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) : thL n w (thL n w g) = g := by
  rw [thL_eq' w hw]
  exact thetaGL_thetaGL' n (cj w) (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g

/- English proof (translation)
Rewrite using `[Units.val_mul, map_mul, WithZero.log_mul (v_ne_zero' a.ne_zero) (v_ne_zero' b.ne_zero)]`.
-/
theorem logv_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : Lˣ) :
    WithZero.log (Valued.v ((a * b : Lˣ) : L)) = WithZero.log (Valued.v (a : L)) + WithZero.log (Valued.v (b : L)) := by
  rw [Units.val_mul, map_mul, WithZero.log_mul (v_ne_zero' a.ne_zero) (v_ne_zero' b.ne_zero)]

/- English proof (translation)
Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]`.
-/
theorem logv_inv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : Lˣ) :
    WithZero.log (Valued.v ((a⁻¹ : Lˣ) : L)) = -WithZero.log (Valued.v (a : L)) := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]

/- English proof (translation)
Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]`.
-/
theorem logv_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : Lˣ) (k : ℤ) :
    WithZero.log (Valued.v ((a ^ k : Lˣ) : L)) = k * WithZero.log (Valued.v (a : L)) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `WithZero.log (Valued.v (cj w (b : w.adicCompletion E))) = _`. Rewrite using `[(GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1]`.
-/
theorem logv_cj (hU : Unr E) (w : Pl E) (b : (w.adicCompletion E)ˣ) :
    WithZero.log (Valued.v ((Units.map (cj w).toMonoidHom b : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
      WithZero.log (Valued.v (b : w.adicCompletion E)) := by
  change WithZero.log (Valued.v (cj w (b : w.adicCompletion E))) = _
  rw [(GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1]

/- English proof (translation)
Rewrite using `[thL_eq' w hw]`. Conclude with `thetaGL_diagT n (cj w) t`.
-/
theorem thL_diagT (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (t : Fin n → (w.adicCompletion E)ˣ) :
    thL n w (GlobalTheory.SmGL.diagT _ (Fin n) t) =
      GlobalTheory.SmGL.diagT _ (Fin n) (fun i => (Units.map (cj w).toMonoidHom (t i.rev))⁻¹) := by
  rw [thL_eq' w hw]; exact thetaGL_diagT n (cj w) t

omit [IsCMField E] in
/- English proof (translation)
Rewrite using `[tdiag, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem tdiag_mul_diagT {w : Pl E} {a : ℕ} (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (u : Fin a → (w.adicCompletion E)ˣ) :
    tdiag ϖ x * GlobalTheory.SmGL.diagT _ (Fin a) u = GlobalTheory.SmGL.diagT _ (Fin a) (fun i => ϖ ^ x i * u i) := by
  rw [tdiag, ← map_mul]; rfl

/- English proof (translation)
Introduce `i j hij`. Establish `h1` using `hx hij`. Establish `h2` using `hx (Fin.rev_lt_rev.mpr hij)`. Unfold `nv`. Use linear arithmetic over natural numbers and integers.
-/
theorem nv_strictAnti {a : ℕ} {x : Fin a → ℤ} (hx : StrictAnti x) : StrictAnti (nv x) := by
  intro i j hij
  have h1 := hx hij
  have h2 := hx (Fin.rev_lt_rev.mpr hij)
  unfold nv
  omega

/- English proof (translation)
Establish `hN : h⁻¹ * (GlobalTheory.SmGL.diagT _ (Fin a) D * thL a w (GlobalTheory.SmGL.diagT _ (Fin a) D)) * h = GlobalTheory.SmGL.diagT _ (Fin a) D' * thL a w (GlobalTheory.SmGL.diagT _ (Fin a) D')`. Rewrite using `[← hh, map_mul, map_mul, map_inv, thL_thL hU w hw]`. Use `group`. Rewrite `hN` using `[thL_diagT w hw, thL_diagT w hw, ← map_mul, ← map_mul]`. Establish `hent : ∀ F : Fin a → (w.adicCompletion E)ˣ, (∀ i, WithZero.log (Valued.v (F i : w.adicCompletion E)) = -x i) → (∀ i j : Fin a, i ≠ j → (GlobalTheory.SmGL.diagT _ (Fin a) (F * fun i => (Units.map (cj w).toMonoidHom (F i.rev))⁻¹)).val i j = 0) ∧ ∀ i, ordL ((GlobalTheory.SmGL.diagT …`.

Introduce `F hF`. Use `⟨fun i j hij => by rw [diagT_val_apply, if_neg hij], fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[diagT_val_apply, if_pos rfl, ordL_eq_neg_log', Pi.mul_apply, logv_mul, logv_inv, logv_cj hU, hF, hF]`. Unfold `nv`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨-, hoff⟩` from `diagonal_conj_distinct_valuations_eq w a (nv x) (nv_strictAnti hx).injective _ _ h (hent D hD) (hent D' hD') hN`. Take `⟨η, rfl⟩` from `exists_diagT h hoff`. Use `⟨η, rfl, fun i => ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[thL_diagT w hw, ← map_inv, ← map_mul, ← map_mul]`. Establish `hi` using `congrArg (fun y : (w.adicCompletion E)ˣ => WithZero.log (Valued.v (y : w.adicCompletion E))) (congrFun (diagT_injective hh) i)`.

Simplify using `only [Pi.mul_apply, Pi.inv_apply] at hi`. Rewrite `hi` using `[logv_mul, logv_mul, logv_inv, logv_inv, logv_cj hU, hD, hD']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem twisted_conj_diagonal_valuation_units (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (x : Fin a → ℤ) (hx : StrictAnti x)
    (D D' : Fin a → (w.adicCompletion E)ˣ) (hD : ∀ i, WithZero.log (Valued.v (D i : w.adicCompletion E)) = -x i)
    (hD' : ∀ i, WithZero.log (Valued.v (D' i : w.adicCompletion E)) = -x i) (h : GLw a w)
    (hh : h⁻¹ * GlobalTheory.SmGL.diagT _ (Fin a) D * thL a w h = GlobalTheory.SmGL.diagT _ (Fin a) D') :
    ∃ η : Fin a → (w.adicCompletion E)ˣ, h = GlobalTheory.SmGL.diagT _ (Fin a) η ∧
      ∀ i, WithZero.log (Valued.v (η i : w.adicCompletion E)) + WithZero.log (Valued.v (η i.rev : w.adicCompletion E)) = 0 := by
  have hN : h⁻¹ * (GlobalTheory.SmGL.diagT _ (Fin a) D * thL a w (GlobalTheory.SmGL.diagT _ (Fin a) D)) * h =
      GlobalTheory.SmGL.diagT _ (Fin a) D' * thL a w (GlobalTheory.SmGL.diagT _ (Fin a) D') := by
    rw [← hh, map_mul, map_mul, map_inv, thL_thL hU w hw]
    group
  rw [thL_diagT w hw, thL_diagT w hw, ← map_mul, ← map_mul] at hN
  have hent : ∀ F : Fin a → (w.adicCompletion E)ˣ, (∀ i, WithZero.log (Valued.v (F i : w.adicCompletion E)) = -x i) →
      (∀ i j : Fin a, i ≠ j → (GlobalTheory.SmGL.diagT _ (Fin a) (F * fun i => (Units.map (cj w).toMonoidHom (F i.rev))⁻¹)).val i j = 0) ∧
      ∀ i, ordL ((GlobalTheory.SmGL.diagT _ (Fin a) (F * fun i => (Units.map (cj w).toMonoidHom (F i.rev))⁻¹)).val i i) = nv x i := by
    intro F hF
    refine ⟨fun i j hij => by rw [diagT_val_apply, if_neg hij], fun i => ?_⟩
    rw [diagT_val_apply, if_pos rfl, ordL_eq_neg_log', Pi.mul_apply, logv_mul, logv_inv, logv_cj hU, hF, hF]
    unfold nv
    ring
  obtain ⟨-, hoff⟩ := diagonal_conj_distinct_valuations_eq w a (nv x) (nv_strictAnti hx).injective _ _ h (hent D hD) (hent D' hD') hN
  obtain ⟨η, rfl⟩ := exists_diagT h hoff
  refine ⟨η, rfl, fun i => ?_⟩
  rw [thL_diagT w hw, ← map_inv, ← map_mul, ← map_mul] at hh
  have hi := congrArg (fun y : (w.adicCompletion E)ˣ => WithZero.log (Valued.v (y : w.adicCompletion E)))
    (congrFun (diagT_injective hh) i)
  simp only [Pi.mul_apply, Pi.inv_apply] at hi
  rw [logv_mul, logv_mul, logv_inv, logv_inv, logv_cj hU, hD, hD'] at hi
  linarith

end Rig

open Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hϖv : WithZero.log (Valued.v (ϖ : w.adicCompletion E)) = -1`. Use `hϖ.1` as an intermediate fact. Rewrite `this` using `[ordL_eq_neg_log']`. Use linear arithmetic over natural numbers and integers. Establish `hϖc : Units.map (cj w).toMonoidHom ϖ = ϖ` using `Units.ext hϖ.2`.

Take `⟨u, rfl, hu⟩` from `TO_diagT hτ`. Take `⟨u', rfl, hu'⟩` from `TO_diagT hτ'`. Rewrite `hh` using `[tdiag_mul_diagT, tdiag_mul_diagT]`. Rewrite using `[tdiag_mul_diagT]`. Establish `hlog : ∀ (v : Fin a → (w.adicCompletion E)ˣ), (∀ i, Valued.v (v i : w.adicCompletion E) = 1) → ∀ i, WithZero.log (Valued.v ((ϖ ^ x i * v i : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = -x i`.

Introduce `v hv i`. Rewrite using `[logv_mul, logv_zpow, hϖv, hv i, WithZero.log_one]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨η, rfl, hη⟩` from `twisted_conj_diagonal_valuation_units hU w hw a x hx _ _ (hlog u hu) (hlog u' hu') h hh`. Use `set k : Fin a → ℤ := fun i => -WithZero.log (Valued.v (η i : w.adicCompletion E)) with hk`.

Use `⟨GlobalTheory.SmGL.diagT _ (Fin a) (fun i => ϖ ^ k i), ?_, GlobalTheory.SmGL.diagT _ (Fin a) (fun i => η i * ϖ ^ (-k i)), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * _ = _ * _`. Rewrite using `[thL_diagT w hw, ← map_mul, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.mul_apply, map_zpow, hϖc, ← _root_.zpow_neg]`. Establish `hki : -k i.rev = k i`. Use `hη i` as an intermediate fact. Simplify using `only [hk]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hki, mul_comm]`. Use `⟨fun i j hij => by rw [diagT_val_apply, if_neg hij], fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[diagT_val_apply, if_pos rfl]`. Establish `hl : WithZero.log (Valued.v (((η i * ϖ ^ (-k i)) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 0`. Rewrite using `[logv_mul, logv_zpow, hϖv]`.

Simplify using `only [hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← WithZero.exp_log (v_ne_zero' (Units.ne_zero _)), hl, WithZero.exp_zero]`. Rewrite using `[← map_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[mul_left_comm, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]`.
-/
theorem le_and_half_le_prod_one_sub_exp_neg_of_bounds (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (x : Fin a → ℤ)
    (hx : StrictAnti x) (τ τ' h : GLw a w) (hτ : τ ∈ TO a w) (hτ' : τ' ∈ TO a w)
    (hh : h⁻¹ * (tdiag ϖ x * τ) * thL a w h = tdiag ϖ x * τ') :
    ∃ z ∈ twCent (thL a w) (tdiag ϖ x * τ), ∃ s ∈ TO a w, h = z * s := by
  have hϖv : WithZero.log (Valued.v (ϖ : w.adicCompletion E)) = -1 := by
    have := hϖ.1
    rw [ordL_eq_neg_log'] at this
    omega
  have hϖc : Units.map (cj w).toMonoidHom ϖ = ϖ := Units.ext hϖ.2
  obtain ⟨u, rfl, hu⟩ := TO_diagT hτ
  obtain ⟨u', rfl, hu'⟩ := TO_diagT hτ'
  rw [tdiag_mul_diagT, tdiag_mul_diagT] at hh
  rw [tdiag_mul_diagT]
  have hlog : ∀ (v : Fin a → (w.adicCompletion E)ˣ), (∀ i, Valued.v (v i : w.adicCompletion E) = 1) →
      ∀ i, WithZero.log (Valued.v ((ϖ ^ x i * v i : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = -x i := by
    intro v hv i
    rw [logv_mul, logv_zpow, hϖv, hv i, WithZero.log_one]
    ring
  obtain ⟨η, rfl, hη⟩ := twisted_conj_diagonal_valuation_units hU w hw a x hx _ _ (hlog u hu) (hlog u' hu') h hh
  set k : Fin a → ℤ := fun i => -WithZero.log (Valued.v (η i : w.adicCompletion E)) with hk
  refine ⟨GlobalTheory.SmGL.diagT _ (Fin a) (fun i => ϖ ^ k i), ?_, GlobalTheory.SmGL.diagT _ (Fin a) (fun i => η i * ϖ ^ (-k i)), ?_, ?_⟩
  · change _ * _ = _ * _
    rw [thL_diagT w hw, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, map_zpow, hϖc, ← _root_.zpow_neg]
    have hki : -k i.rev = k i := by
      have := hη i
      simp only [hk]
      linarith
    rw [hki, mul_comm]
  · refine ⟨fun i j hij => by rw [diagT_val_apply, if_neg hij], fun i => ?_⟩
    rw [diagT_val_apply, if_pos rfl]
    have hl : WithZero.log (Valued.v (((η i * ϖ ^ (-k i)) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 0 := by
      rw [logv_mul, logv_zpow, hϖv]
      simp only [hk]
      ring
    rw [← WithZero.exp_log (v_ne_zero' (Units.ne_zero _)), hl, WithZero.exp_zero]
  · rw [← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rw [mul_left_comm, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
