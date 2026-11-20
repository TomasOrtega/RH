import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcCoverProof

/- English proof (translation)
Introduce `U ι f`. Set `O : ι → U.Opens` to `fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩`. Establish `hcov : iSup O = ⊤` using `eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩`. Establish `hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a` using `fun a v => v.2`. Use `⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `V g a hg`. Establish `hr : Set.range g ⊆ Set.range (O a).ι`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hg v`.

Conclude with `⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩`. Introduce `x y h`. Use `U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_` and prove the remaining obligations. Establish `e : O a ≤ (O a).ι ''ᵁ ⊤` using `by simp`. Establish `hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op = U.presheaf.map (homOfLE (x` using `(O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by`.

Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression. Use `congrArg (U.presheaf.map (homOfLE e).op).hom (h a)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x = (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y`. Rewrite using `[hm]`.

Conclude with `this`. Introduce `R _ G x`. Establish `hG` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond)`. Establish `hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U` using `Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))`. Establish `hsf` using `hG _ hS`.

Rewrite `hsf` using `[Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff]`. Use `hsf x ?_` and prove the remaining obligations. Introduce `a b Z gi gj h`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Establish `: gi = gj` using `by rwa [cancel_mono] at h`. Rewrite using `[this]`. Establish `hE : IsEmpty Z` using `⟨fun z => hab (by`. Establish `h1` using `hval a (gi z)`. Establish `h2` using `hval b (gj z)`.

Rewrite `h1` using `[← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2]`. Conclude with `h1.symm)⟩`. Establish `hz` using `(Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero`. Use `ModuleCat.subsingleton_of_isZero hz` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem lcCover : CrystallineSemistableComparison.E.LcCover := by
  intro U ι f
  let O : ι → U.Opens := fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩
  have hcov : iSup O = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩
  have hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a := fun a v => v.2
  refine ⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩
  · intro V g a hg
    have hr : Set.range g ⊆ Set.range (O a).ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg v
    exact ⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro x y h
    refine U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_
    have e : O a ≤ (O a).ι ''ᵁ ⊤ := by simp
    have hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op =
        U.presheaf.map (homOfLE (x := (O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (U.presheaf.map (homOfLE e).op).hom (h a)
    change (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x =
      (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y
    rw [hm]
    exact this
  · intro R _ G x
    have hG := (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond)
    have hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U :=
      Scheme.zariskiTopology_le_etaleTopology _
        (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))
    have hsf := hG _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsf
    refine hsf x ?_
    intro a b Z gi gj h
    by_cases hab : a = b
    · subst hab
      have : gi = gj := by rwa [cancel_mono] at h
      rw [this]
    · have hE : IsEmpty Z := ⟨fun z => hab (by
        have h1 := hval a (gi z)
        have h2 := hval b (gj z)
        rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2] at h1
        exact h1.symm)⟩
      have hz := (Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero
      have := ModuleCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _

end GlobalTheory.CompanionTheory.LcCoverProof
