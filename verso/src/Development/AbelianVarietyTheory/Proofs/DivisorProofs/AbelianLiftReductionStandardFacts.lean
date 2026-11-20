import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

/- English proof (translation)
Introduce `H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg`. Establish `F : AbelianDeRham.Free` using `GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.Proof.abelianDeRhamFree_of_hodge H1 H2)`. Establish `C : CrystallineDeRham` using `H1.toCrystallineDeRham`. Establish `Rg : AbelianDeRham.Rigid` using `AbelianDeRham.rigid_of_free_of_crystallineDeRham F C`. Establish `hA₀ : IsAbelianScheme A₀` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h'`.

Establish `hg₀ : SmoothOfRelativeDimension g A₀.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h'.1 hg`. Establish `p' : AllPrim (dp0 R) (𝟙 _) A'` using `(F R A' g hA hg).1`. Establish `p₀ : AllPrim (dp0 R₀) (𝟙 _) A₀` using `(F R₀ A₀ g hA₀ hg₀).1`. Establish `hκ : IsNilDP (divided₂ hI)` using `isDPNilpotent_squareZero hI`. Establish `bij` using `Rg R A' g hA hg I (divided₂ hI) hκ R₀ π hπ hk A₀ i' h'`.

Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Take `⟨b₁, -⟩` from `C R I (divided₂ hI) hκ R₀ π hπ hk A'.left A₀.left (A'.hom ≫ 𝟙 _) A₀.hom i' inferInstance inferInstance inferInstance (by rw [Category.comp_id]; exact h'.1) (liftMor (divided₂ hI) h').isMor`. Establish `pc : AllPrim (divided₂ hI) (spMap π) A₀`. Use `Submodule.eq_top_iff'.2 fun c ↦ ?_` and prove the remaining obligations.

Take `⟨c', rfl⟩` from `b₁.2 c`. Establish `hc' : c' ∈ prim (dp0 R) (𝟙 _) A'` using `by rw [show prim (dp0 R) (𝟙 _) A' = ⊤ from p']; trivial`. Conclude with `(liftMor (divided₂ hI) h').pullback_mem_primitive hc'`. Set `e` to `LinearEquiv.ofBijective (liftMor (divided₂ hI) h').isMor.pull1 b₁`. Establish `fin : Module.Finite R (FirstDeRham (A'.hom ≫ 𝟙 _))` using `(F R A' g hA hg).2.1`.

Establish `proj : Module.Projective R (FirstDeRham (A'.hom ≫ 𝟙 _))` using `(F R A' g hA hg).2.2.1`. Conclude with `⟨p', p₀, pc, bij, Module.Finite.equiv e, Module.Projective.of_equiv e, hA₀, hg₀⟩`.
-/
theorem abelianLift_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  have F : AbelianDeRham.Free :=
    GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.Proof.abelianDeRhamFree_of_hodge H1 H2)
  have C : CrystallineDeRham := H1.toCrystallineDeRham
  have Rg : AbelianDeRham.Rigid := AbelianDeRham.rigid_of_free_of_crystallineDeRham F C
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h'.1 hg
  have p' : AllPrim (dp0 R) (𝟙 _) A' := (F R A' g hA hg).1
  have p₀ : AllPrim (dp0 R₀) (𝟙 _) A₀ := (F R₀ A₀ g hA₀ hg₀).1
  have hκ : IsNilDP (divided₂ hI) := isDPNilpotent_squareZero hI
  have bij := Rg R A' g hA hg I (divided₂ hI) hκ R₀ π hπ hk A₀ i' h'
  have := hA.smooth
  have := hA.proper
  obtain ⟨b₁, -⟩ := C R I (divided₂ hI) hκ R₀ π hπ hk A'.left A₀.left (A'.hom ≫ 𝟙 _) A₀.hom i' inferInstance
    inferInstance inferInstance (by rw [Category.comp_id]; exact h'.1) (liftMor (divided₂ hI) h').isMor
  have pc : AllPrim (divided₂ hI) (spMap π) A₀ := by
    refine Submodule.eq_top_iff'.2 fun c ↦ ?_
    obtain ⟨c', rfl⟩ := b₁.2 c
    have hc' : c' ∈ prim (dp0 R) (𝟙 _) A' := by rw [show prim (dp0 R) (𝟙 _) A' = ⊤ from p']; trivial
    exact (liftMor (divided₂ hI) h').pullback_mem_primitive hc'
  let e := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').isMor.pull1 b₁
  have fin : Module.Finite R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.1
  have proj : Module.Projective R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.2.1
  exact ⟨p', p₀, pc, bij, Module.Finite.equiv e, Module.Projective.of_equiv e, hA₀, hg₀⟩

end GlobalTheory.LiftSys
