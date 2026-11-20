import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj`. Use `haveI := hj`. Establish `hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j`. Introduce `x`. Apply `(hpt'.range _).1` to reduce the goal to its premises.

Establish `hx : (pt x) ^ p = 1` using `(hpt.range _).2 ⟨x, rfl⟩`. Rewrite using `[← MonObj.pow_comp, hx, MonObj.one_comp]`. Use `choose f hf using hex`. Establish `hadd : ∀ x y : N, f (x + y) = f x + f y`. Introduce `x y`.

Apply `hpt'.inj` to reduce the goal to its premises. Rewrite using `[hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]`. Set `jN : N →+ N'` to `{ toFun := f map_zero' := by`. Establish `h` using `hadd 0 0`. Rewrite `h` using `[add_zero]`.

Simplify using `using h.symm`. Use the proof step `map_add' := hadd }`. Establish `hyp : (T.y ≫ j) ^ p = 1`. Rewrite using `[← MonObj.pow_comp, T.y_p, MonObj.one_comp]`. Take `⟨ψ, hψ, -⟩` from `T'.univ T.A (T.y ≫ j) hyp`.

Use `⟨jN, ψ, fun x => hf x, hψ, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨a, ha⟩` from `hg`. Use `⟨ψ a, ?_⟩` and prove the remaining obligations. Introduce `x φ hφ`.

Establish `key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x)`. Rewrite using `[← Chart.spMap_comp ψ φ]`. Express the relevant statement in the definitionally equal form `(spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)`. Rewrite using `[Category.assoc, hψ, ← Category.assoc, hφ, hf]`. Conclude with `ha (jN x) (φ.comp ψ) key`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
