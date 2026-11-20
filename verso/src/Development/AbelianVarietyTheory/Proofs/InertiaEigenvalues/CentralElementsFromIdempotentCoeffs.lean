import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulIdemFromCenter
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop

noncomputable section

namespace GlobalTheory.Pass.CentralStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

/- English proof (translation)
Introduce `_ D P i s`. Establish `hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd)`. Rewrite using `[D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))`.

Rewrite using `[Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]`. Use `haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')`. Establish `key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),`. Set `e` to `(L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod`. Use `e * e = e ∧ ∀ z, e * z = z * e := by`.

Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Take `⟨h1, h2⟩` from `ih`.

Establish `hc` using `Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _ (D.ntypes.eSer_central a.1 (s a)))`. Establish `hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) = ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a))`. Rewrite using `[GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]`. Simplify using `only [List.map_cons, List.prod_cons]`. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]`. Rewrite using `[mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]`. Take `⟨h1, h2⟩` from `key Finset.univ.toList`. Take `⟨ζ, hζ⟩` from `P.zetaPrimitiveRoot i`. Establish `hinj : Function.Injective (iotaO D.nd D.naut i)` using `((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)`.

Take `⟨z, hz, hz'⟩` from `GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2 ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩`. Use `⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩` and prove the remaining obligations. Use extensionality with `h`. Rewrite using `[hcard]`. Simplify `hz' h` using `[PairedCharacterCondition.mapCoef]`.
-/
theorem main : StepCentral := by
  intro _ D P i s
  classical
  have hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd) := by
    rw [D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  have key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),
      let e := (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod
      e * e = e ∧ ∀ z, e * z = z * e := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨h1, h2⟩ := ih
      have hc := Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _
        (D.ntypes.eSer_central a.1 (s a)))
      have hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) =
          ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) := by
        rw [GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]
      simp only [List.map_cons, List.prod_cons]
      refine ⟨?_, fun z => ?_⟩
      · rw [mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]
      · rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
  obtain ⟨h1, h2⟩ := key Finset.univ.toList
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  obtain ⟨z, hz, hz'⟩ := GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2
    ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩
  refine ⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
  ext h
  rw [hcard]
  simpa [PairedCharacterCondition.mapCoef] using hz' h

end GlobalTheory.Pass.CentralStep

end
