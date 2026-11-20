import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteTypeStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

/- English proof (translation)
Proceed by induction. Treat this case separately. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem biInf_preimage {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    ⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x
    simp [yS, Proj.basicOpen]
  | insert a S ha ih =>
    rw [Finset.iInf_insert, ih]
    simp only [yS]
    rw [Finset.prod_insert ha, Proj.basicOpen_mul]
    rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isAffineOpen_preimage (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) := by
  haveI := hci
  exact (Proj.isAffineOpen_basicOpen (grK K N) g hg he).preimage i

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem evV_surjective (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) :
    Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first
    | exact GlobalTheory.T.basic_open_eval_surjective ..
    | (intros; apply GlobalTheory.T.basic_open_eval_surjective <;> assumption)

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem range_resO_eq (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) {V W : X.Opens} (hW : W = i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : V ≤ W)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : Set.range (resO h) = Set.range (evV i g V h') := by
  subst hW
  have e0 : i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl ≫ X.presheaf.map (homOfLE h).op = i.appLE _ V h' :=
    Scheme.Hom.appLE_map i _ _
  have hcomp : evV i g V h' = (resO h).comp (evV i g _ le_rfl) := by
    refine RingHom.ext fun a => ?_
    simp only [evV, resO, RingHom.comp_apply, ← e0]
    rfl
  rw [hcomp, RingHom.coe_comp, Set.range_comp, (evV_surjective i hci hg he).range_eq, Set.image_univ]

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem iSup_preimage_eq_top {m e : ℕ} (he : 0 < e) (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i)) :
    ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first
    | exact GlobalTheory.T.basic_opens_cover_of_finite ..
    | (intros; apply GlobalTheory.T.basic_opens_cover_of_finite <;> assumption)

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem finiteType_affine (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}
    (hW : IsAffineOpen W) : letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first
    | exact GlobalTheory.T.affine_open_finiteType ..
    | (intros; apply GlobalTheory.T.affine_open_finiteType <;> assumption)

end CrystallineSemistableComparison.Pb
