import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

noncomputable section

namespace UpperTheory.Gal.Int.Div

section SubSplitAux

variable {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma sumRep_val (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep r s g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      (Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0
        (s g : Matrix (Fin b) (Fin b) k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private def resHom (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (ρ (g * h) : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k) =
      (ρ g : Matrix (Fin n) (Fin n) k).mulVec
        ((ρ h : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') : Γ →* GL (Fin b) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix c c (resHom ρ hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma subRep_val (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (g : Γ) :
    ((subRep ρ hinv c g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) =
      LinearMap.toMatrix c c (resHom ρ hinv g) := rfl

private def colM (A : Matrix (Fin n) (Fin a) k) {W' : Submodule k (Fin n → k)}
    (c : Module.Basis (Fin b) k W') : Matrix (Fin n) (Fin a ⊕ Fin b) k :=
  Matrix.of fun i => Sum.elim (fun j => A i j) (fun j => (c j : Fin n → k) i)

/- English proof (translation)
Use extensionality with `i (j | j)`. Establish `h` using `congrFun (congrFun hA i) j`. Simplify `h` using `[colM, Matrix.mul_apply, Fintype.sum_sum_type]`. Establish `hs` using `congrArg (fun v : W' => (v : Fin n → k) i) (c.sum_repr (resHom ρ hinv g (c j)))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs`.

Simplify using `only [colM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, subRep_val, LinearMap.toMatrix_apply]`. Use `Eq.trans ?_ (hs.symm.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Conclude with `Finset.sum_congr rfl fun x _ => mul_comm _ _`.
-/
private lemma intertw (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (A : Matrix (Fin n) (Fin a) k)
    (R : Matrix (Fin a) (Fin a) k) (g : Γ)
    (hA : (ρ g : Matrix (Fin n) (Fin n) k) * A = A * R) :
    (ρ g : Matrix (Fin n) (Fin n) k) * colM A c =
      colM A c * Matrix.fromBlocks R 0 0 (subRep ρ hinv c g : Matrix (Fin b) (Fin b) k) := by
  ext i (j | j)
  · have h := congrFun (congrFun hA i) j
    simpa [colM, Matrix.mul_apply, Fintype.sum_sum_type] using h
  · have hs := congrArg (fun v : W' => (v : Fin n → k) i) (c.sum_repr (resHom ρ hinv g (c j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hs
    simp only [colM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, subRep_val, LinearMap.toMatrix_apply]
    refine Eq.trans ?_ (hs.symm.trans ?_)
    · rfl
    · exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/- English proof (translation)
Apply `LinearIndependent.sum_type` to reduce the goal to its premises. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.rank_eq_finrank_span_cols]`. Both sides reduce to the same expression.

Conclude with `c.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')`. Use `hc.disjoint.mono ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.range_mulVecLin]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `(c j).2`.
-/
private lemma col_indep (A : Matrix (Fin n) (Fin a) k) (hA : A.rank = a)
    {W' : Submodule k (Fin n → k)} (c : Module.Basis (Fin b) k W')
    (hc : IsCompl (LinearMap.range A.mulVecLin) W') :
    LinearIndependent k (Sum.elim A.col (fun j => (c j : Fin n → k))) := by
  apply LinearIndependent.sum_type
  · rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    calc a = A.rank := hA.symm
      _ = _ := by
        rw [Matrix.rank_eq_finrank_span_cols]
        rfl
  · exact c.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  · refine hc.disjoint.mono ?_ ?_
    · rw [Matrix.range_mulVecLin]
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (c j).2

end SubSplitAux

/- English proof (translation)
Introduce `Γ k _ _ a b r ρ hss ⟨A, hA, hAg⟩`. Establish `hinvW : IsInv ρ (LinearMap.range A.mulVecLin)`. Introduce and unpack `g _ ⟨u, rfl⟩`. Use `⟨(r g : Matrix (Fin a) (Fin a) k).mulVec u, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAg g]`.

Take `⟨W', hinv, hc⟩` from `hss _ hinvW`. Establish `hdim : Module.finrank k W' = b`. Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hc`. Establish `h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a` using `hA`. Rewrite `h1` using `[Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers. Set `c : Module.Basis (Fin b) k W'` to `Module.finBasisOfFinrankEq k W' hdim`. Set `e : Fin a ⊕ Fin b ≃ Fin (a + b)` to `finSumFinEquiv`. Set `P : Matrix (Fin (a + b)) (Fin (a + b)) k` to `(colM A c).submatrix id e.symm`. Establish `hP : IsUnit P`.

Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Establish `h` using `(col_indep A hA c hc).comp e.symm e.symm.injective`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j i`. Apply the tactic sequence `rcases h' : e.symm j with j' | j' <;> simp [P, colM, Matrix.col, h'] <;> rfl`.

Establish `hinvP : ((hP.unit⁻¹ : GL (Fin (a + b)) k) : Matrix _ _ k) * P = 1`. Establish `h` using `hP.unit.inv_mul`. Rewrite `h` using `[hP.unit_spec]`. Then use the resulting hypothesis. Use `⟨subRep ρ hinv c, hP.unit⁻¹, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : (ρ x : Matrix _ _ k) * P = P * (Matrix.fromBlocks (r x : Matrix (Fin a) (Fin a) k) 0 0 (subRep ρ hinv c x : Matrix (Fin b) (Fin b) k)).submatrix e.symm e.symm`.

Rewrite using `[Matrix.submatrix_mul_equiv, ← intertw ρ hinv c A (r x) x (hAg x)]`. Use extensionality with `i j`. Simplify using `[P, Matrix.mul_apply]`. Rewrite using `[inv_inv]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[sumRep_val, Units.val_mul, Units.val_mul, hP.unit_spec, mul_assoc, hx, ← mul_assoc, hinvP, one_mul]`.
-/
theorem subSplit_of : SubSplit := by
  intro Γ k _ _ a b r ρ hss ⟨A, hA, hAg⟩
  have hinvW : IsInv ρ (LinearMap.range A.mulVecLin) := by
    rintro g _ ⟨u, rfl⟩
    refine ⟨(r g : Matrix (Fin a) (Fin a) k).mulVec u, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAg g]
  obtain ⟨W', hinv, hc⟩ := hss _ hinvW
  have hdim : Module.finrank k W' = b := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := hA
    rw [Module.finrank_fin_fun] at h1
    omega
  let c : Module.Basis (Fin b) k W' := Module.finBasisOfFinrankEq k W' hdim
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let P : Matrix (Fin (a + b)) (Fin (a + b)) k := (colM A c).submatrix id e.symm
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have h := (col_indep A hA c hc).comp e.symm e.symm.injective
    convert h using 1
    ext j i
    rcases h' : e.symm j with j' | j' <;> simp [P, colM, Matrix.col, h'] <;> rfl
  have hinvP : ((hP.unit⁻¹ : GL (Fin (a + b)) k) : Matrix _ _ k) * P = 1 := by
    have h := hP.unit.inv_mul
    rwa [hP.unit_spec] at h
  refine ⟨subRep ρ hinv c, hP.unit⁻¹, fun x => ?_⟩
  have hx : (ρ x : Matrix _ _ k) * P = P * (Matrix.fromBlocks (r x : Matrix (Fin a) (Fin a) k) 0 0
      (subRep ρ hinv c x : Matrix (Fin b) (Fin b) k)).submatrix e.symm e.symm := by
    rw [Matrix.submatrix_mul_equiv, ← intertw ρ hinv c A (r x) x (hAg x)]
    ext i j
    simp [P, Matrix.mul_apply]
  rw [inv_inv]
  apply Units.ext
  rw [sumRep_val, Units.val_mul, Units.val_mul, hP.unit_spec, mul_assoc, hx, ← mul_assoc, hinvP,
    one_mul]

end UpperTheory.Gal.Int.Div

end
