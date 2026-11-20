import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ratGL_val {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
      (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem ratGL_map {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ratGL L n g = GeneralLinearGroup.map (algebraMap L (Ad L)) g :=
  Units.ext (ratGL_val n g)

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem alg_inj {L : Type} [Field L] [NumberField L] [IsCMField L] :
    Function.Injective (algebraMap L (Ad L)) := by
  obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := inferInstance
  intro x y h
  have e := congrArg (fun z => coord τ (pInf L z)) h
  simp only [coord_algebraMap] at e
  exact τ.injective e

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem loc_alg {L : Type} [Field L] [NumberField L] (w : Plc L) (x : L) :
    pLoc L w (pFin L (algebraMap L (Ad L) x)) = algebraMap L (Kw w) x := rfl

end UpperTheory.V.Z.Sym.Dict.Br

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.ratFacts :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (g : GL (Fin n) L), (ratGL L n g ∈ UA L n ↔ ((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L) = 1) ∧ Function.Injective (ratGL L n) ∧ ∀ h : ratGL L n g ∈ UA L n, (∀ w, mL w ⟨_, h⟩ = (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Kw w))) ∧ (∀ τ : L →+* ℂ, (cEmb τ ⟨_, h⟩ : Matrix (Fin n) (Fin n) ℂ) = (g : Matrix (Fin n) (Fin n) L).map τ) ∧ ((GeneralLinearGroup.det (ratGL L n g) = 1) ↔ GeneralLinearGroup.det g = 1) := by
  intro L _ _ _ n g
  have hinj := alg_inj (L := L)
  refine ⟨?_, ?_, fun h => ⟨fun w => ?_, fun τ => ?_, ?_⟩⟩
  · have key : Formalism.UG.cT (conjAd L) ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
        ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
        (((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L)).map
          (algebraMap L (Ad L)) := by
      rw [ratGL_val, mul_one, Formalism.UG.cT, Matrix.map_mul]
      congr 1
      ext i j
      simp [conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) _ * 1 * _ = 1 ↔ _
    rw [key]
    constructor
    · intro e
      ext i j
      have := congrFun (congrFun e i) j
      apply hinj
      rw [Matrix.map_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · intro e
      rw [e]
      simp
  · intro a b e
    ext i j
    have := congrArg (fun x : GL (Fin n) (Ad L) => (x : Matrix (Fin n) (Fin n) (Ad L)) i j) e
    simp only [ratGL_val, Matrix.map_apply] at this
    exact hinj this
  · exact Matrix.ext fun i j => loc_alg w _
  · exact Matrix.ext fun i j => coord_algebraMap τ _
  · have hd : ((GeneralLinearGroup.det (ratGL L n g) : (Ad L)ˣ) : Ad L) =
        algebraMap L (Ad L) ((GeneralLinearGroup.det g : Lˣ) : L) := by
      rw [ratGL_map, GlobalTheory.CuspRep.det_map]
    constructor
    · intro e
      rw [e] at hd
      apply Units.ext
      apply hinj
      rw [← hd]
      simp
    · intro e
      apply Units.ext
      rw [hd, e]
      simp
