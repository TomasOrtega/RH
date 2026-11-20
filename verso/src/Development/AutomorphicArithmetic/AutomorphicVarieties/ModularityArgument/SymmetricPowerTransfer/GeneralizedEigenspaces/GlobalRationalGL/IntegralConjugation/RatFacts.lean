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
The claim follows from `Units.ext (ratGL_val n g)`.
-/
private theorem ratGL_map {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ratGL L n g = GeneralLinearGroup.map (algebraMap L (Ad L)) g :=
  Units.ext (ratGL_val n g)

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (L →+* ℂ)` from `inferInstance`. Introduce `x y h`. Establish `e` using `congrArg (fun z => coord τ (pInf L z)) h`. Simplify using `only [coord_algebraMap] at e`. Conclude with `τ.injective e`.
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
Introduce `L _ _ _ n g`. Establish `hinj` using `alg_inj (L := L)`. Use `⟨?_, ?_, fun h => ⟨fun w => ?_, fun τ => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `key : Formalism.UG.cT (conjAd L) ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 * ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = (((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L)).map …`. Rewrite using `[ratGL_val, mul_one, Formalism.UG.cT, Matrix.map_mul]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[conjAd_algebraMap]`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (conjAd L) _ * 1 * _ = 1 ↔ _`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Use extensionality with `i j`. Use `congrFun (congrFun e i) j` as an intermediate fact. Apply `hinj` to reduce the goal to its premises.

Rewrite `this` using `[Matrix.map_apply]`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `e`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Introduce `a b e`. Use extensionality with `i j`. Use `congrArg (fun x : GL (Fin n) (Ad L) => (x : Matrix (Fin n) (Fin n) (Ad L)) i j) e` as an intermediate fact. Simplify using `only [ratGL_val, Matrix.map_apply] at this`.

Conclude with `hinj this`. Conclude with `Matrix.ext fun i j => loc_alg w _`. Conclude with `Matrix.ext fun i j => coord_algebraMap τ _`. Establish `hd : ((GeneralLinearGroup.det (ratGL L n g) : (Ad L)ˣ) : Ad L) = algebraMap L (Ad L) ((GeneralLinearGroup.det g : Lˣ) : L)`. Rewrite using `[ratGL_map, GlobalTheory.CuspRep.det_map]`.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite `hd` using `[e]`. Apply `Units.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hd]`. Simplify using the standard rewrite rules. Introduce `e`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hd, e]`.

Simplify using the standard rewrite rules.
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
