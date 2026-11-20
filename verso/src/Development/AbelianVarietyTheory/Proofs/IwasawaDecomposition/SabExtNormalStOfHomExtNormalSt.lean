import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `hext E _ _ _ H X U _ j hX hoi hdom t₀ t t' a a' hp`. Establish `hj₁ : IsPreimmersion j` using `inferInstance`. Establish `hj₂ : Flat j` using `inferInstance`. Establish `hj₄ : QuasiCompact j` using `inferInstance`. Take `⟨hgen, -, hsd, -⟩` from `densePart_basic X U j hj₁ hj₂ hdom hj₄`.

Establish `hred : IsReduced X`. Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)` using `fun x => by`. Use `(hX x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk X`.

Use `hsd hred` as an intermediate fact. Take `⟨_, _⟩` from `ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi`. Take `⟨_, _⟩` from `ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi`. Take `⟨F, hF, hφ⟩` from `TripleExt.exists_hom a.cart a'.cart (hext X U j hX hoi hdom t.G t'.G t.semi t'.semi)`. Take `⟨F', -, hφ'⟩` from `TripleExt.exists_hom a'.cart a.cart (hext X U j hX hoi hdom t'.G t.G t'.semi t.semi)`.

Establish `hiso : IsIso F` using `ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F' ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)`. Establish `gp : IsGrpPullback t.G t'.G (𝟙 X) F.left` using `haveI : IsMonHom (asIso F).hom := hF isGrpPullback_of_iso (asIso F)`. Establish `hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left` using `fun x => by`. Establish `: t.act.act x ≫ F = F ≫ t'.act.act x` using `ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by`. Rewrite using `[Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ, a'.act])`.

Conclude with `congrArg (fun z => z.left) this`. Establish `hlb : LBIso t.PP.L (t'.PP.L.pull F.left)`. Take `⟨w, hw, -⟩` from `(isPullCubical_iff _ _ _).1 a.lin`. Take `⟨w', hw', -⟩` from `(isPullCubical_iff _ _ _).1 a'.lin`. Establish `hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w''`.

Rewrite using `[hφ]`. Conclude with `⟨w', hw'⟩`. Take `⟨w'', hw''⟩` from `hw''`. Take `⟨r, hr, -⟩` from `Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw'' a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst`. Take `⟨ρ, hρ, -⟩` from `Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig t'.PP.rigGen t.PP.rigGen`.

Establish `sm` using `t.semi.smooth`. Establish `gc` using `t.semi.geomConnected`. Conclude with `GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX hj₁ hj₂ hdom hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G]) sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (pull_isLB t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩`. Take `⟨b, hb⟩` from `exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb`. Conclude with `⟨b, by rw [hb]; exact hφ⟩`.
-/
theorem sabExtNormalSt_of_homExtNormalSt : HomExtNormalSt → SabExtNormalSt := by
  intro hext E _ _ _ H X U _ j hX hoi hdom t₀ t t' a a' hp
  have hj₁ : IsPreimmersion j := inferInstance
  have hj₂ : Flat j := inferInstance
  have hj₄ : QuasiCompact j := inferInstance
  obtain ⟨hgen, -, hsd, -⟩ := densePart_basic X U j hj₁ hj₂ hdom hj₄
  have hred : IsReduced X := by
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hX x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  have := hsd hred
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart (hext X U j hX hoi hdom t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart (hext X U j hX hoi hdom t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have gp : IsGrpPullback t.G t'.G (𝟙 X) F.left :=
    haveI : IsMonHom (asIso F).hom := hF
    isGrpPullback_of_iso (asIso F)
  have hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left := fun x => by
    have : t.act.act x ≫ F = F ≫ t'.act.act x := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
    exact congrArg (fun z => z.left) this
  have hlb : LBIso t.PP.L (t'.PP.L.pull F.left) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff _ _ _).1 a.lin
    obtain ⟨w', hw', -⟩ := (isPullCubical_iff _ _ _).1 a'.lin
    have hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w'' := by
      rw [hφ]; exact ⟨w', hw'⟩
    obtain ⟨w'', hw''⟩ := hw''
    obtain ⟨r, hr, -⟩ := Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw''
      a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst
    obtain ⟨ρ, hρ, -⟩ := Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig
      t'.PP.rigGen t.PP.rigGen
    have sm := t.semi.smooth
    have gc := t.semi.geomConnected
    exact GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX hj₁ hj₂ hdom hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G])
      sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (pull_isLB t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩
  obtain ⟨b, hb⟩ := exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left
    ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb
  exact ⟨b, by rw [hb]; exact hφ⟩

end GlobalTheory.TorRef
