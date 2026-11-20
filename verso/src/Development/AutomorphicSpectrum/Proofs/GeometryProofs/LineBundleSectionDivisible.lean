import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sc_res {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (d : R) :
    (X.presheaf.map (homOfLE h).op).hom (sc π U d) = sc π V d := by
  have e := Scheme.Hom.appLE_map π (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  simp only [sc, RingHom.comp_apply]
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sc_ne_zero {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) {V : X.Opens}
    [Nonempty V] {d : R} (hd : sc π ⊤ d ≠ 0) : sc π V d ≠ 0 := by
  intro h
  apply hd
  have hi := map_injective_of_isIntegral X (homOfLE (le_top : V ≤ ⊤))
  apply hi
  have := sc_res π (le_top : V ≤ ⊤) d
  rw [map_zero]
  exact this.trans h

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Substitute using the available equality. A detailed English derivation is pending.
-/
theorem sc_cancel {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) {a b : Γ(X, V)} (h : sc π V d * a = sc π V d * b) : a = b := by
  by_cases hV : Nonempty V
  · exact mul_left_cancel₀ (sc_ne_zero π hd) h
  · have : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨⟨x, hx⟩⟩
    subst this
    exact Subsingleton.elim _ _

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_div {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) (x : Γ(X, V))
    (h : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom x = sc π W d * a) :
    ∃ y : Γ(X, V), x = sc π V d * y := by
  let I := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : I → X.Opens := fun i => (i.1 : X.Opens)
  choose g hg using fun i : I => h (U i) i.2 i.1.2
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    apply sc_cancel π _ hd
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, sc_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (sc π V d * (show Γ(X, V) from s))
  rw [hg i, map_mul, sc_res]
  exact congrArg _ (hs i).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_sec_of_local {X : Scheme.{0}} [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X)
    (s : LB.Sec M) (δ : R) (hδ : sc π ⊤ δ ≠ 0)
    (h : ∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) :
    ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  choose y hy using fun i => exists_div π (M.U i) hδ (s.f i) (h i)
  refine ⟨⟨y, fun i j => ?_⟩, hy⟩
  apply sc_cancel π _ hδ
  have e := s.compat i j
  rw [hy i, hy j, map_mul, map_mul, sc_res, sc_res] at e
  rw [e]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sec_eq_smul_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  intro X _ R _ π M s δ hδ h
  exact exists_sec_of_local R π M s δ hδ h

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue
