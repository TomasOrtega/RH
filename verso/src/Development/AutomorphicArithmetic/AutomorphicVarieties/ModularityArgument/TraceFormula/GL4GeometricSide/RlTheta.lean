import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `e : Bridge.atW (E` using `E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by`. Use function extensionality and compare the values at `i j v`. Rewrite using `[Bridge.atW]`. Conclude with `(locInf_apply w (Unitary.toUnits k) i j v).symm`. Rewrite using `[Bridge.along, e, chart_val]`.

Both sides reduce to the same expression.
-/
private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  classical
  have e : Bridge.atW (E := E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by
    funext i j v
    rw [Bridge.atW]
    exact (locInf_apply w (Unitary.toUnits k) i j v).symm
  rw [Bridge.along, e, chart_val]
  rfl

/- English proof (translation)
Establish `e : φ'.1 = fun x => φ.1 (thetaA E n x)` using `funext h`. Establish `e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y = (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y)` using `fun f y => by`. Simplify using `only [Bridge.eopW, if_true]`. Conclude with `Eop_apply _ a b f y`. Establish `e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y = (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y)` using `fun f y => by`.

Simplify using `only [Bridge.eopW, Bool.false_eq_true, if_false]`. Rewrite using `[Eop_apply, atEmb_conjugate, atEmb_conjugate]`. Simplify using `[sg]`. Rewrite using `[e1, e2, e]`. Simplify using `only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, if_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, if_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

/- English proof (translation)
Introduce `E _ _ _ n _ π _ K _ _ _ _ _ μf _ D`. Establish `hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y` using `fun x y h => D.inj (Subtype.ext (Subtype.ext (funext h)))`. Use `⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w => ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g`. Rewrite using `[D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]`.

Rewrite using `[D.inner_eq, D.inner_eq]`. Conclude with `D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)`. Express the relevant statement in the definitionally equal form `(D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g`. Rewrite using `[D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]`. Express the relevant statement in the definitionally equal form `(D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g`.

Rewrite using `[D.hΘ, D.hE1, D.hE2]`. Conclude with `eop_theta w a b (D.hΘ u) g`.
-/
theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
