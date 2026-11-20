import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

open GlobalTheory.Dict.ColPoly in

/- English proof (translation)
Introduce `E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF`. Establish `hF' : ContDiff ℂ (⊤ : ℕ∞) F` using `hF.contDiff`. Set `a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ` to `fun v k => s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))`. Set `j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n)` to `fun v k => eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩`. Set `Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ` to `MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)`.

Establish `ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2))` using `fun v k => by`. Simplify using `only [a]`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩` using `fun v k => by`. Simplify using `only [j]`.

Rewrite using `[Equiv.symm_apply_apply]`. Establish `hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F, MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) = Φ (MvPolynomial.rename eL (MvPolynomial.map s Q))`. Introduce `Q`. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C x => simp`.

Consider the case `add P Q hP hQ => simp only [map_add, hP, hQ]`. Consider the case `mul_X P v hP`. Simplify using `only [map_mul, hP]`. Use `congr 1`. Simplify using `[pushLet, letB, Φ, ha, hj]`.

Rewrite using `[hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]`. Use `Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `congr 1`. Use function extensionality and compare the values at `v k i`.

Take `⟨⟨τ, ρ, b⟩, rfl⟩` from `eL.surjective v`. Express the relevant statement in the definitionally equal form `Dict.hAct X idx h _ k i = _`. Simplify using `only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp), Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]`. Distinguish the cases in `hi : i = e.symm ⟨τ, ρ⟩`.

Substitute `hi` using the available equality. Simplify using `only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]`. Both sides reduce to the same expression. Simplify using `[hi]`.
-/
theorem GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  intro E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := hF.contDiff
  let a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ := fun v k =>
    s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) := fun v k =>
    eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩
  let Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ :=
    MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)
  have ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2)) := fun v k => by
    simp only [a]; rw [Equiv.symm_apply_apply]
  have hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩ := fun v k => by
    simp only [j]; rw [Equiv.symm_apply_apply]
  have hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) =
        Φ (MvPolynomial.rename eL (MvPolynomial.map s Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P v hP =>
      simp only [map_mul, hP]
      congr 1
      simp [pushLet, letB, Φ, ha, hj]
  rw [hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]
  refine Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)
  rw [map_zero]
  congr 1
  funext v k i
  obtain ⟨⟨τ, ρ, b⟩, rfl⟩ := eL.surjective v
  change Dict.hAct X idx h _ k i = _
  simp only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp),
    Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]
  by_cases hi : i = e.symm ⟨τ, ρ⟩
  · subst hi
    simp only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]
    rfl
  · simp [hi]
