import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenTrait

/- English proof (translation)
Take `⟨V, hV, hzV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial`. Establish `: IsAffine V` using `hV`. Establish `: IsNoetherian V.toScheme` using `{}`. Establish `: NoetherianSpace V.toScheme` using `inferInstance`. Set `z' : V.toScheme` to `⟨z, hzV⟩`.

Establish `hC` using `irreducibleComponent_mem_irreducibleComponents z'`. Take `⟨o, ho, ⟨u, huo⟩, hoC⟩` from `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC`. Establish `hg` using `hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)`. Establish `hoX : IsOpen (V.ι '' o)` using `V.ι.isOpenEmbedding.isOpenMap o ho`. Take `⟨_, ⟨w, hwo, rfl⟩, hwU⟩` from `hU.inter_open_nonempty _ hoX ⟨_, u, huo, rfl⟩`.

Establish `h1 : V.ι hC.1.genericPoint ⤳ V.ι w` using `(hg.specializes (hoC hwo)).map V.ι.continuous`. Establish `h2 : V.ι hC.1.genericPoint ⤳ V.ι z'` using `(hg.specializes mem_irreducibleComponent).map V.ι.continuous`. Establish `h3 : V.ι z' = z` using `rfl`. Rewrite `h2` using `[h3]`. Rewrite using `[← hz _ h2]`.

Conclude with `h1.mem_open U.isOpen hwU`.
-/
theorem mem_of_dense_of_forall_specializes {X : Scheme.{0}} [IsLocallyNoetherian X] {U : X.Opens}
    (hU : Dense (U : Set X)) {z : X} (hz : ∀ ξ : X, ξ ⤳ z → ξ = z) : z ∈ U := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have : IsAffine V := hV
  have : IsNoetherian V.toScheme := {}
  have : NoetherianSpace V.toScheme := inferInstance
  let z' : V.toScheme := ⟨z, hzV⟩
  have hC := irreducibleComponent_mem_irreducibleComponents z'
  obtain ⟨o, ho, ⟨u, huo⟩, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hoX : IsOpen (V.ι '' o) := V.ι.isOpenEmbedding.isOpenMap o ho
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwU⟩ := hU.inter_open_nonempty _ hoX ⟨_, u, huo, rfl⟩
  have h1 : V.ι hC.1.genericPoint ⤳ V.ι w := (hg.specializes (hoC hwo)).map V.ι.continuous
  have h2 : V.ι hC.1.genericPoint ⤳ V.ι z' := (hg.specializes mem_irreducibleComponent).map V.ι.continuous
  have h3 : V.ι z' = z := rfl
  rw [h3] at h2
  rw [← hz _ h2]
  exact h1.mem_open U.isOpen hwU

end GlobalTheory.GenTrait

namespace GlobalTheory.GenTrait

/- English proof (translation)
Use `TF.smooth` as an intermediate fact. Establish `: Smooth TF.Y.s` using `SmoothOfRelativeDimension.smooth Dw.dim _`. Use `TF.X.proper` as an intermediate fact. Conclude with `LocallyOfFiniteType.isLocallyNoetherian (TF.X.π ≫ TF.Y.s)`.
-/
theorem isLocallyNoetherian_flag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) :
    IsLocallyNoetherian TF.X.YY := by
  have := TF.smooth
  have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have := TF.X.proper
  exact LocallyOfFiniteType.isLocallyNoetherian (TF.X.π ≫ TF.Y.s)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z y K _ g hg p _`. Use `isLocallyNoetherian_flag TF` as an intermediate fact. Set `q` to `Spec.map (CommRingCat.ofHom g) p`. Establish `hq0 : q.asIdeal = ⊥`. Establish `hp : p.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime`.

Express the relevant statement in the definitionally equal form `Ideal.comap g p.asIdeal = ⊥`. Rewrite using `[hp, ← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot g).1 hg`. Establish `hq : ∀ q' : Spec ((Y₀ TF.X Z).presheaf.stalk y), q' ⤳ q → q' = q` using `fun q' h => PrimeSpectrum.ext (le_antisymm ((show q'.asIdeal ≤ q.asIdeal from (PrimeSpectrum.le_iff_specializes _ _).2 h)) (hq0.le.trans bot_le))`. Express the relevant statement in the definitionally equal form `((Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) p) ∈ flagOpen TF.X`.

Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Use `mem_of_dense_of_forall_specializes (dense_flagOpen TF.X) fun ξ hξ => ?_` and prove the remaining obligations. Establish `hy : (Y₀ TF.X Z).fromSpecStalk y q ⤳ y`. Establish `: (Y₀ TF.X Z).fromSpecStalk y q ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y)` using `⟨q, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis.

Establish `hmem : ξ ∈ Set.range (inc₀ TF.X Z)`. Rewrite using `[Scheme.Opens.range_ι]`. Use `hξ.mem_open (TopologicalSpace.Opens.isOpen _) ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `⟨_, rfl⟩`.

Take `⟨ξ₀, rfl⟩` from `hmem`. Establish `h₀ : ξ₀ ⤳ (Y₀ TF.X Z).fromSpecStalk y q` using `(inc₀ TF.X Z).isEmbedding.specializes_iff.1 hξ`. Choose the witnesses or unpack the hypotheses as in `⟨q', rfl⟩ : ξ₀ ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `h₀.trans hy`.

Rewrite using `[hq q' (((Y₀ TF.X Z).fromSpecStalk y).isEmbedding.specializes_iff.1 h₀)]`.
-/
theorem top_le_preimage_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z) (K : Type) [Field K] (g : (Y₀ TF.X Z).presheaf.stalk y →+* K), Function.Injective g → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by
  intro E _ _ _ H Dw l Xo c TF Z y K _ g hg p _
  have := isLocallyNoetherian_flag TF
  let q := Spec.map (CommRingCat.ofHom g) p
  have hq0 : q.asIdeal = ⊥ := by
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime
    change Ideal.comap g p.asIdeal = ⊥
    rw [hp, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot g).1 hg
  have hq : ∀ q' : Spec ((Y₀ TF.X Z).presheaf.stalk y), q' ⤳ q → q' = q := fun q' h =>
    PrimeSpectrum.ext (le_antisymm ((show q'.asIdeal ≤ q.asIdeal from (PrimeSpectrum.le_iff_specializes _ _).2 h)) (hq0.le.trans bot_le))
  change ((Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) p) ∈ flagOpen TF.X
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  refine mem_of_dense_of_forall_specializes (dense_flagOpen TF.X) fun ξ hξ => ?_
  have hy : (Y₀ TF.X Z).fromSpecStalk y q ⤳ y := by
    have : (Y₀ TF.X Z).fromSpecStalk y q ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hmem : ξ ∈ Set.range (inc₀ TF.X Z) := by
    rw [Scheme.Opens.range_ι]
    refine hξ.mem_open (TopologicalSpace.Opens.isOpen _) ?_
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨ξ₀, rfl⟩ := hmem
  have h₀ : ξ₀ ⤳ (Y₀ TF.X Z).fromSpecStalk y q := (inc₀ TF.X Z).isEmbedding.specializes_iff.1 hξ
  obtain ⟨q', rfl⟩ : ξ₀ ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact h₀.trans hy
  rw [hq q' (((Y₀ TF.X Z).fromSpecStalk y).isEmbedding.specializes_iff.1 h₀)]

end GlobalTheory.GenTrait
