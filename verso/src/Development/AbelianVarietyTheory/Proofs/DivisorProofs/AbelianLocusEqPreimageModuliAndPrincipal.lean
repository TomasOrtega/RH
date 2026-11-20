import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelAbLocus

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem relAmple_of_lbIso_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [IsProper A.hom]
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  have h₁ : RelAmple A' (L.pull φ) := AmpleBaseChange.relAmple_of_isPullback hL hA h
  obtain ⟨w, hw⟩ : LBIso L' ((L.pull φ).pull (𝟙 _)) :=
    e.chartPull (chartPullId _) (Geo.Tor.chartPullPull (L.pull φ) _ _ rfl)
  exact PolOfIso.relAmple_pull_of_affine (f := 𝟙 S') (φ := 𝟙 A'.left) (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (pull_isLB hL φ) hL' ((isGen_iff w).1 hw) (fun U hU => ⟨U, hU, fun _ hy => hy⟩) h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem abLocus_eq_range (Y : Model Xo c (RingHom.id c.F)) : abLocus Y.t.G = Set.range Y.j := by
  refine Set.Subset.antisymm (fun x hx => ?_) (GenFan.Tri.range_j_subset_abLocus Y)
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  obtain ⟨z, rfl⟩ := (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective x
  have hz : z ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hx
  obtain ⟨w, rfl⟩ := hz
  exact ⟨w, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem pol_of_fac {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S S' : Scheme.{0}} {χ : S ⟶ Y.X}
    {t : SAB H S} (m : SABMap t Y.t χ) (x : S' ⟶ S) (y : S' ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) :
    RelAmple ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x)) ∧
      KTriv ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x)) := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H S') (p : S' ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have e := LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃
  have := Y.oF.proper
  refine ⟨relAmple_of_lbIso_pull m₃.cart.1 Y.oF.t.PP.isLB hL e Y.oF.ample, ?_⟩
  obtain ⟨w, hw⟩ := e
  exact kTriv_pull m₃.cart Y.oF.t.PP.isLB hL ((isGen_iff w).1 hw) Y.oF.ktriv

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem abLocus_eq_and_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : Scheme.{0}) (π : T ⟶ Y.X) (t : SAB H T), Nonempty (SABMap t Y.t π) → abLocus t.G = π ⁻¹' Set.range Y.j ∧ IsOpen (abLocus t.G) ∧ ∀ W : T.Opens, (W : Set T) ⊆ abLocus t.G → RelAmple ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) := by
  rintro E _ _ _ H Dw l Xo c Y T π t ⟨m⟩
  have hj := GenFan.Tri.isOpenImmersion_j_id Y
  have h₁ : abLocus t.G = π ⁻¹' Set.range Y.j := by
    ext x
    rw [← abLocus_eq_range Y]
    exact (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).symm
  refine ⟨h₁, ?_, fun W hW => ?_⟩
  · rw [h₁]
    exact Y.j.isOpenEmbedding.isOpen_range.preimage π.continuous
  · have hr : Set.range (W.ι ≫ π) ⊆ Set.range Y.j := by
      rintro _ ⟨w, rfl⟩
      have hw : w.1 ∈ π ⁻¹' Set.range Y.j := h₁ ▸ hW w.2
      exact hw
    exact pol_of_fac Y m W.ι (IsOpenImmersion.lift Y.j (W.ι ≫ π) hr) (IsOpenImmersion.lift_fac _ _ _)

end GlobalTheory.ModelAbLocus
