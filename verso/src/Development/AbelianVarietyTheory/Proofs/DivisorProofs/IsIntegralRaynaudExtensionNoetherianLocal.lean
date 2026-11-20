import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RayInt

open ReciprocityTheory.ChartRestriction.G.Semi TopologicalSpace

attribute [local instance] SplitExt.free SplitExt.finite

/- English proof (translation)
Establish `e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k))` using `(Finset.inf_univ_eq_iInf _).symm`. Rewrite using `[e, ← SetLike.mem_coe, Opens.coe_finset_inf]`. Simplify using `only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply, SetLike.mem_coe]`. Conclude with `h`.
-/
theorem mem_chart_of_mem {S : Scheme.{0}} (E : SplitExt S) (j : E.ChartIdx) (b : E.B.left)
    (h : ∀ k, b ∈ (E.O (E.basis k)).L.U (j k)) : b ∈ E.chart j := by
  have e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k)) :=
    (Finset.inf_univ_eq_iInf _).symm
  rw [e, ← SetLike.mem_coe, Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter,
    Function.comp_apply, SetLike.mem_coe]
  exact h

/- English proof (translation)
Take `⟨d⟩` from `hG`. Establish `hB` using `E.isAbelian`. Use `haveI : Smooth E.B.hom := hB.smooth`. Use `haveI : GeometricallyConnected E.B.hom := hB.geomConnected`. Establish `hSne : Nonempty (Spec (CommRingCat.of R))` using `inferInstance`.

Establish `hBne : Nonempty E.B.left` using `⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩`. Use `haveI : IrreducibleSpace E.B.left := GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne`. Use `haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom`. Use `haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _`. Use `haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom`.

Take `⟨b⟩` from `hBne`. Establish `hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i` using `fun k => by`. Establish `hb : b ∈ (⊤ : E.B.left.Opens)` using `trivial`. Rewrite `hb` using `[← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup]`. Conclude with `hb`.

Use `choose j hj using hk`. Establish `hbj : b ∈ E.chart j` using `mem_chart_of_mem E j b hj`. Take `⟨V, hV, hbV, hVj⟩` from `(Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj`. Establish `hbV' : b ∈ V` using `hbV`. Use `haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩`.

Use `haveI := d.q_affine`. Use `haveI := d.q_flat`. Establish `hsurj` using `d.q_surjective`. Use `set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef`. Establish `hV : IsAffineOpen V` using `hV`.

Establish `hW : IsAffineOpen W` using `hV.preimage d.q.left`. Establish `hbij` using `d.coord j V hV hVj`. Use `haveI : IsDomain Γ(G.left, W) := Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom (RingEquiv.ofBijective _ hbij).symm.injective`. Take `⟨g, hg⟩` from `hsurj.surj b`. Establish `hgW : g ∈ W` using `by show d.q.left g ∈ V; rw [hg]; exact hbV'`.

Use `haveI : Nonempty W := ⟨⟨g, hgW⟩⟩`. Use `haveI : IsAffine W := hW`. Use `haveI : IsDomain Γ(W, ⊤) := Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom (W.topIso).commRingCatIsoToRingEquiv.injective`. Use `haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W`. Establish `hirrW : IsIrreducible (W : Set G.left)`.

Establish `hI` using `(IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn`. Rewrite `hI` using `[Set.image_univ, Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Establish `hη : genericPoint E.B.left ∈ V` using `((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩`. Establish `hcl : closure (W : Set G.left) = Set.univ`. Use `Set.eq_univ_of_forall fun z => ?_` and prove the remaining obligations.

Take `⟨z', hz', e⟩` from `Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))`. Establish `hz'W : z' ∈ (W : Set G.left)` using `by show d.q.left z' ∈ V; rw [e]; exact hη`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')`. Use `haveI : IrreducibleSpace G.left := by`. Rewrite using `[irreducibleSpace_def]`.

Use `hirrW.closure` as an intermediate fact. Rewrite `this` using `[hcl]`. Then use the resulting hypothesis. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem isIntegral_of_isGt (R : Type) [CommRing R] [IsDomain R] (E : SplitExt (Spec (CommRingCat.of R)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (hG : E.IsGt G) (hs : Smooth G.hom) :
    IsIntegral G.left := by
  obtain ⟨d⟩ := hG
  have hB := E.isAbelian
  haveI : Smooth E.B.hom := hB.smooth
  haveI : GeometricallyConnected E.B.hom := hB.geomConnected
  have hSne : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  have hBne : Nonempty E.B.left := ⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩
  haveI : IrreducibleSpace E.B.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne
  haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom
  haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  obtain ⟨b⟩ := hBne
  have hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i := fun k => by
    have hb : b ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup] at hb
    exact hb
  choose j hj using hk
  have hbj : b ∈ E.chart j := mem_chart_of_mem E j b hj
  obtain ⟨V, hV, hbV, hVj⟩ := (Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj
  have hbV' : b ∈ V := hbV
  haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩
  haveI := d.q_affine
  haveI := d.q_flat
  have hsurj := d.q_surjective
  set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef
  have hV : IsAffineOpen V := hV
  have hW : IsAffineOpen W := hV.preimage d.q.left
  have hbij := d.coord j V hV hVj
  haveI : IsDomain Γ(G.left, W) :=
    Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom
      (RingEquiv.ofBijective _ hbij).symm.injective
  obtain ⟨g, hg⟩ := hsurj.surj b
  have hgW : g ∈ W := by show d.q.left g ∈ V; rw [hg]; exact hbV'
  haveI : Nonempty W := ⟨⟨g, hgW⟩⟩
  haveI : IsAffine W := hW
  haveI : IsDomain Γ(W, ⊤) :=
    Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom
      (W.topIso).commRingCatIsoToRingEquiv.injective
  haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W
  have hirrW : IsIrreducible (W : Set G.left) := by
    have hI := (IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at hI
  have hη : genericPoint E.B.left ∈ V :=
    ((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩
  have hcl : closure (W : Set G.left) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))
    have hz'W : z' ∈ (W : Set G.left) := by show d.q.left z' ∈ V; rw [e]; exact hη
    exact closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')
  haveI : IrreducibleSpace G.left := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [hcl] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/- English proof (translation)
Introduce `R _ _ _ _ Q O _ _ _ oa Y`. Conclude with `isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)`.
-/
theorem isIntegral_H : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  exact isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)

end GlobalTheory.RayInt
