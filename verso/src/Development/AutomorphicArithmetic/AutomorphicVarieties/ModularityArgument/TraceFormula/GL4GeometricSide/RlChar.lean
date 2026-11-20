import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

open NumberField Finset

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b u`. Apply the tactic sequence `by_cases hab : a = b <;> simp [PositivityTheory.RgBcC.RealD.epow, Formalism.REAL.epow, hab]`. Consider the case `succ m ih`.

Introduce `a b u`. Rewrite using `[PositivityTheory.RgBcC.Bridge.epow_succ']`. Simplify using `only [PositivityTheory.RgBcC.RealD.epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h, ih]`.
-/
private theorem map_epow {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) :
    ∀ a b u, j (PositivityTheory.RgBcC.RealD.epow M m a b u) = Formalism.REAL.epow N m a b (j u) := by
  induction m with
  | zero =>
    intro a b u
    by_cases hab : a = b <;> simp [PositivityTheory.RgBcC.RealD.epow, Formalism.REAL.epow, hab]
  | succ m ih =>
    intro a b u
    rw [PositivityTheory.RgBcC.Bridge.epow_succ']
    simp only [PositivityTheory.RgBcC.RealD.epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h, ih]

/- English proof (translation)
Simplify using `only [gelA, Formalism.REAL.etr, LinearMap.sum_apply, map_sum, map_epow j M N h m]`.
-/
private theorem map_gelA {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) (u : U) :
    j (gelA M m u) = Formalism.REAL.etr N m (j u) := by
  simp only [gelA, Formalism.REAL.etr, LinearMap.sum_apply, map_sum, map_epow j M N h m]

end UpperTheory.V.Z.GSp4Splitting

/- English proof (translation)
Introduce `E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w lam hch`. Establish `hin : Function.Injective ((π.V.subtype).comp D.i)` using `Subtype.val_injective.comp D.inj`. Establish `h1` using `(PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.1`. Establish `h2` using `(PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.2`. Prove the components needed by the constructor for the conclusion.

Introduce `m x`. Apply `hin` to reduce the goal to its premises. Establish `e` using `map_gelA ((π.V.subtype).comp D.i) (D.E1 w) (PositivityTheory.RgBcC.Bridge.eopW w true) (fun a b u => D.hE1 w a b u) m x`. Rewrite using `[e, map_smul]`. Simplify `h1 _ (D.i x).2 m` using `[PositivityTheory.RgBcC.Bridge.eopW]`.

Introduce `m x`. Apply `hin` to reduce the goal to its premises. Establish `e` using `map_gelA ((π.V.subtype).comp D.i) (barF (D.E2 w)) (PositivityTheory.RgBcC.Bridge.eopW w false) (fun a b u => by`. Use `D.hE2 w b a u` as an intermediate fact. Simplify using `only [barF, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_neg, this, neg_neg]) m x`.

Rewrite using `[e, map_smul]`. Simplify `h2 _ (D.i x).2 m` using `[PositivityTheory.RgBcC.Bridge.eopW]`.
-/
theorem UpperTheory.V.Z.GSp4Splitting.rlChar :
    RlChar := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w lam hch
  have hin : Function.Injective ((π.V.subtype).comp D.i) :=
    Subtype.val_injective.comp D.inj
  have h1 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.1
  have h2 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.2
  constructor
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (D.E1 w) (PositivityTheory.RgBcC.Bridge.eopW w true)
      (fun a b u => D.hE1 w a b u) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h1 _ (D.i x).2 m
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (barF (D.E2 w)) (PositivityTheory.RgBcC.Bridge.eopW w false)
      (fun a b u => by
        have := D.hE2 w b a u
        simp only [barF, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, Submodule.subtype_apply,
          Submodule.coe_neg, this, neg_neg]) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h2 _ (D.i x).2 m
