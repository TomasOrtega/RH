import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

/- English proof (translation)
Use `haveI : Etale (torsion G n).hom := GrpTangent.etale_torsion G hn`. Take `⟨t, ht, e⟩` from `Flat.generalizingMap (torsion G n).hom (genericPoint_specializes ((torsion G n).hom p))`. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : t ∈ Set.range ((torsion G n).left.fromSpecStalk p) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `ht`.

Set `D` to `Spec ((torsion G n).left.presheaf.stalk p)`. Set `y : Sp (AlgebraicClosure (D.residueField q)) ⟶ D` to `Spec.map (CommRingCat.ofHom (algebraMap (D.residueField q) (AlgebraicClosure (D.residueField q)))) ≫ D.fromSpecResidueField q`. Set `g` to `y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom`. Establish `hgen : genericPoint X' ∈ Set.range ℓ`. Take `⟨v⟩` from `‹Nonempty V›`.

Conclude with `((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).mpr ⟨ℓ v, Set.mem_univ _, v, rfl⟩`. Establish `hg : Set.range g ⊆ Set.range ℓ`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hya : y a = q`. Establish `: y a ∈ Set.range (D.fromSpecResidueField q)` using `⟨_, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Then use the resulting hypothesis. Establish `: g a = (torsion G n).hom ((torsion G n).left.fromSpecStalk p (y a))` using `rfl`. Rewrite using `[this, hya, e]`. Conclude with `hgen`. Set `z` to `IsOpenImmersion.lift ℓ g hg`.

Establish `hz : z ≫ ℓ = g` using `IsOpenImmersion.lift_fac ℓ g hg`. Establish `h1` using `h _ y z hz.symm`. Establish `h2` using `h' _ y z hz.symm`. Conclude with `hun _ z c c' (h1.symm.trans h2)`.
-/
theorem valAt_unique {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ)
    (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (p : (torsion G n).left) (c c' : M) (h : GlobalTheory.TorsSpec.ValAt G n ℓ w p c)
    (h' : GlobalTheory.TorsSpec.ValAt G n ℓ w p c') : c = c' := by
  haveI : Etale (torsion G n).hom := GrpTangent.etale_torsion G hn
  obtain ⟨t, ht, e⟩ := Flat.generalizingMap (torsion G n).hom
    (genericPoint_specializes ((torsion G n).hom p))
  obtain ⟨q, rfl⟩ : t ∈ Set.range ((torsion G n).left.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact ht
  let D := Spec ((torsion G n).left.presheaf.stalk p)
  let y : Sp (AlgebraicClosure (D.residueField q)) ⟶ D :=
    Spec.map (CommRingCat.ofHom (algebraMap (D.residueField q) (AlgebraicClosure (D.residueField q)))) ≫
      D.fromSpecResidueField q
  let g := y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).mpr ⟨ℓ v, Set.mem_univ _, v, rfl⟩
  have hg : Set.range g ⊆ Set.range ℓ := by
    rintro _ ⟨a, rfl⟩
    have hya : y a = q := by
      have : y a ∈ Set.range (D.fromSpecResidueField q) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have : g a = (torsion G n).hom ((torsion G n).left.fromSpecStalk p (y a)) := rfl
    rw [this, hya, e]
    exact hgen
  let z := IsOpenImmersion.lift ℓ g hg
  have hz : z ≫ ℓ = g := IsOpenImmersion.lift_fac ℓ g hg
  have h1 := h _ y z hz.symm
  have h2 := h' _ y z hz.symm
  exact hun _ z c c' (h1.symm.trans h2)

end GlobalTheory.TorsSpec
