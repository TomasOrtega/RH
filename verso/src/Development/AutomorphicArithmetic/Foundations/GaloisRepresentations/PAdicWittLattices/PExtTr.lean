import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.G3.pExtTr :
    ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) := by
  intro B R _ T L _ _ Z Y p q s tr h W r c hc J _ σ hσ hs x
  change LinearMap.baseChange L (T.pull c hc) (LinearMap.baseChange L tr x) =
    ∑ j, LinearMap.baseChange L (T.pull (σ j) (hσ j)) x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [LinearMap.baseChange_tmul]
    rw [h W r c hc J σ hσ hs y, TensorProduct.tmul_sum]
  | add x y hx hy =>
    simp only [map_add, hx, hy, ← Finset.sum_add_distrib]
