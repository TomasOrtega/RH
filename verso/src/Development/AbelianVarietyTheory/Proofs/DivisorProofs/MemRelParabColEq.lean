import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellDetFirst

open scoped TensorProduct

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem card_two_false' (a b : Type) [Fintype a] [Fintype b] :
    Fintype.card (Two a b false) = Fintype.card a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem card_two_true' (a b : Type) [Fintype a] [Fintype b] :
    Fintype.card (Two a b true) = Fintype.card b := rfl

def sizeFirst (u v : ℕ) : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1)) :=
  ⟨fun i j => cond i (cond j 1 v) (cond j 0 u), by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · cases i <;> simp [Fintype.sum_bool, card_two_false', card_two_true'] <;> omega
    · cases j <;> simp [Fintype.sum_bool, card_two_false', card_two_true'] <;> omega⟩

/- English proof (translation)
Establish `r0` using `b.2.1 false`. Establish `r1` using `b.2.1 true`. Establish `c1` using `b.2.2 true`. Simplify using `only [Fintype.sum_bool, card_two_false', card_two_true', Fintype.card_fin] at r0 r1 c1`. Use `Subtype.ext (funext fun i => funext fun j => ?_)` and prove the remaining obligations.

Apply the tactic sequence `cases i <;> cases j <;> simp [sizeFirst] <;> omega`.
-/
theorem eq_sizeFirst {u v : ℕ} (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1)))
    (h : b.1 false true = 0) : b = sizeFirst u v := by
  have r0 := b.2.1 false
  have r1 := b.2.1 true
  have c1 := b.2.2 true
  simp only [Fintype.sum_bool, card_two_false', card_two_true', Fintype.card_fin] at r0 r1 c1
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  cases i <;> cases j <;> simp [sizeFirst] <;> omega

def colFalse (u v : ℕ) : (Σ i, Fin ((sizeFirst u v).1 i false)) ≃ Fin (u + v) :=
  (Equiv.sigmaCongrRight (β₂ := Two (Fin u) (Fin v)) fun i => match i with
    | false => Equiv.refl (Fin u)
    | true => Equiv.refl (Fin v)).trans (two (stdSum rfl))

def colEq (u v : ℕ) : ∀ j, (Σ i, Fin ((sizeFirst u v).1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j
  | false => colFalse u v
  | true => OneBlockCell.valEquiv (n := fun i => (sizeFirst u v).1 i true) true rfl
      (fun i hi => by cases i <;> simp_all [sizeFirst])

def rowEq (u v : ℕ) : ∀ i, (Σ j, Fin ((sizeFirst u v).1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i :=
  (sizeFirst u v).nonempty_rows.some

/- English proof (translation)
Simplify using `only [blk, colFalse, Equiv.symm_trans_apply]`. Break down `(two (stdSum (rfl : u + v = u + v))).symm x with ⟨a, y⟩` into its components or cases. Both sides reduce to the same expression.
-/
theorem blk_colFalse (u v : ℕ) (x : Fin (u + v)) :
    blk (colFalse u v) x = blk (two (stdSum (rfl : u + v = u + v))) x := by
  simp only [blk, colFalse, Equiv.symm_trans_apply]
  rcases (two (stdSum (rfl : u + v = u + v))).symm x with ⟨a, y⟩
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : x false ∈ parab k (colFalse u v)` using `h false trivial`. Use `mem_parab.2 fun i j hij => mem_parab.1 h1 i j ?_` and prove the remaining obligations. Rewrite using `[blk_colFalse, blk_colFalse]` and apply the resulting hypothesis.

Introduce `h j _`. Consider the cases of `j`. Use `mem_parab.2 fun i i' hij => mem_parab.1 h i i' ?_` and prove the remaining obligations. Rewrite using `[← blk_colFalse, ← blk_colFalse]` and apply the resulting hypothesis. Apply the tactic sequence `exact OneBlockCell.mem_parab_of_single _ true (fun i hi => by cases i <;> simp_all [sizeFirst]) _`.
-/
theorem mem_relParab_colEq {u v : ℕ} (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    x ∈ relParab k (colEq u v) ↔ x false ∈ parab k (two (stdSum (rfl : u + v = u + v))) := by
  constructor
  · intro h
    have h1 : x false ∈ parab k (colFalse u v) := h false trivial
    refine mem_parab.2 fun i j hij => mem_parab.1 h1 i j ?_
    rwa [blk_colFalse, blk_colFalse]
  · intro h j _
    cases j
    · refine mem_parab.2 fun i i' hij => mem_parab.1 h i i' ?_
      rwa [← blk_colFalse, ← blk_colFalse]
    · exact OneBlockCell.mem_parab_of_single _ true (fun i hi => by cases i <;> simp_all [sizeFirst]) _

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem relProj_colEq_ff {u v : ℕ} (p : relParab k (colEq u v)) :
    (relProj k (colEq u v) p false false : GL (Fin u) k) =
      leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false := by
  ext a b; rfl

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem relProj_colEq_ft {u v : ℕ} (p : relParab k (colEq u v)) :
    (relProj k (colEq u v) p false true : GL (Fin v) k) =
      leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true := by
  ext a b; rfl

/- English proof (translation)
Establish `h` using `det_parab k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩`. Rewrite using `[h, Fintype.prod_bool]`. Establish `h0 : GeneralLinearGroup.det (leviProj k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩ false) = 1` using `by haveI : IsEmpty (Fin ((sizeFirst u v).1 false true)) := ⟨fun x => Fin.elim0 x⟩`. Use `ext`. Simplify using `[Matrix.det_isEmpty]`.

Rewrite using `[h0, mul_one]`. Both sides reduce to the same expression.
-/
theorem det_relProj_tt {u v : ℕ} (p : relParab k (colEq u v)) :
    GeneralLinearGroup.det (relProj k (colEq u v) p true true : GL (Fin 1) k) =
      GeneralLinearGroup.det (p.1 true) := by
  have h := det_parab k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩
  rw [h, Fintype.prod_bool]
  have h0 : GeneralLinearGroup.det (leviProj k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩ false) = 1 := by
    haveI : IsEmpty (Fin ((sizeFirst u v).1 false true)) := ⟨fun x => Fin.elim0 x⟩
    ext
    simp [Matrix.det_isEmpty]
  rw [h0, mul_one]
  rfl

abbrev rhoM (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    Representation ℂ (Levi k (Two (Fin u) (Fin (v + 1)))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
    (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom

/- English proof (translation)
The claim follows from `GlobalTheory.IndLineGL.CellTorus.extTensor_detRep_apply χ₁ χ₂ _ w`.
-/
theorem rhoM_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (y : Levi k (Two (Fin u) (Fin (v + 1))))
    (w : ℂ ⊗[ℂ] ℂ) :
    rhoM χ₁ χ₂ u v y w = ((χ₁ (GeneralLinearGroup.det (y false)) *
      χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • w :=
  GlobalTheory.IndLineGL.CellTorus.extTensor_detRep_apply χ₁ χ₂ _ w

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, w, rfl⟩`. Establish `hd : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin u) (Fin (v + 1)))) i) = 1` using `fun i => det_eq_one_of_mem_unipRad k (n.2 i trivial)`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]`. Use `(rhoM_apply χ₁ χ₂ u v (n : Levi k (Two (Fin u) (Fin (v + 1)))) w).trans ?_` and prove the remaining obligations.

Simplify using `[hd]`.
-/
theorem twKer_rhoM (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    twKer (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v)) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨n, w, rfl⟩
  have hd : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin u) (Fin (v + 1)))) i) = 1 :=
    fun i => det_eq_one_of_mem_unipRad k (n.2 i trivial)
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
  refine (rhoM_apply χ₁ χ₂ u v (n : Levi k (Two (Fin u) (Fin (v + 1)))) w).trans ?_
  simp [hd]

abbrev sigmaC (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :=
  (twist ((relJac (rowEq u v) (rhoM (k := k) χ₁ χ₂ u v)).comp
        (swapBlocks k (fun i j => Fin ((sizeFirst u v).1 i j))))
      (relDeltaHalf k (fun j i => Fin ((sizeFirst u v).1 i j)))).comp (relProj k (colEq u v))

end GlobalTheory.CellDetFirst
