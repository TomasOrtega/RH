import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivPow

variable {V : Type} [CommRing V]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
    Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[V] C) : A →+* C))
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem jet_ext {κ : Type} {m : ℕ} {B : Type} [CommRing B] [Algebra V B] (f g : Jet V κ m →ₐ[V] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem jetCopy_X {n d m : ℕ} (i : Fin n) (p : Fin 1 × Fin d) :
    (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun p : Fin 1 × Fin d =>
    (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) V)) (MvPolynomial.X p : MvPolynomial _ V)) = _
  rw [MvPolynomial.aeval_X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i : MvPolynomial κ V) = 0
  rw [MvPolynomial.aeval_X]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jetTrunc_mk {κ : Type} {m : ℕ} (p : MvPolynomial κ V) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zV_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n d : ℕ} (pG : IsPowGrp G' G n)
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) (i : Fin n) :
    zV pG xT m ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m i) ≫ xT m :=
  pG.lim.fac _ ⟨i⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pow_ext {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)}
    (f g : T ⟶ G') (h : ∀ i, f ≫ pG.pr i = g ≫ pG.pr i) : f = g :=
  pG.lim.hom_ext fun i => h i.as

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem one_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)} (i : Fin n) :
    (1 : T ⟶ G') ≫ pG.pr i = 1 := by
  haveI := pG.hom i
  exact MonObj.one_comp _

end GlobalTheory.PowGerm.UnivPow

namespace GlobalTheory.PowGerm
open UnivPow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem univPow : UnivPowSt := by
  intro V _ G G' _ _ n d pG xT ⟨hT, hA, hU⟩
  refine ⟨fun m => pow_ext pG _ _ fun i => ?_, fun m => pow_ext pG _ _ fun i => ?_, ?_⟩
  · rw [Category.assoc, zV_pr, zV_pr, ← hT m, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetCopy_X, jetTrunc_mk, jetTrunc_mk, jetCopy_X]
  · rw [Category.assoc, zV_pr, one_pr, ← hA m, ← Category.assoc, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
  · intro A _ _ aug m hm y hy
    have hi : ∀ i : Fin n, ∃! ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
        aug.comp ψ = jetAug ∧ y ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ xT m := fun i =>
      hU A aug m hm (y ≫ pG.pr i) (by rw [← Category.assoc, hy, one_pr])
    choose ψ hψ hψu using hi
    let a : Fin n × Fin d → A := fun p => ψ p.1 (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))
    have ha : ∀ p, aug (a p) = 0 := fun p => by
      have := congrArg (fun f : Jet V (Fin 1 × Fin d) m →ₐ[V] V =>
        f (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))) (hψ p.1).1
      simp only [AlgHom.comp_apply, jetAug_X] at this
      exact this
    have hsp : Ideal.span (Set.range fun p => (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A)
        (MvPolynomial.X p)) ^ (m + 1) = ⊥ := by
      apply le_bot_iff.1
      rw [← hm]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [MvPolynomial.aeval_X]
      exact ha p
    let Ψ : Jet V (Fin n × Fin d) m →ₐ[V] A := liftJet (MvPolynomial.aeval a) hsp
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = a p := fun p => by
      show (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A) (MvPolynomial.X p) = a p
      rw [MvPolynomial.aeval_X]
    have hc : ∀ i, Ψ.comp (jetCopy d m i) = ψ i := fun i => by
      apply jet_ext
      rintro ⟨u, j⟩
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [AlgHom.comp_apply, jetCopy_X, hΨ]
    refine ⟨Ψ, ⟨?_, pow_ext pG _ _ fun i => ?_⟩, ?_⟩
    · apply jet_ext
      intro p
      rw [AlgHom.comp_apply, hΨ, ha, jetAug_X]
    · rw [Category.assoc, zV_pr, ← Category.assoc, homAt_comp, hc]
      exact (hψ i).2
    · rintro Φ ⟨h1, h2⟩
      have hd : ∀ i, Φ.comp (jetCopy d m i) = ψ i := fun i => by
        apply hψu i
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, h1]
          apply jet_ext
          intro p
          rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
        · rw [h2, Category.assoc, zV_pr, ← Category.assoc, homAt_comp]
      apply jet_ext
      rintro ⟨i, j⟩
      rw [hΨ]
      show _ = ψ i _
      rw [← hd i, AlgHom.comp_apply, jetCopy_X]

end GlobalTheory.PowGerm
