import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocusStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

/- English proof (translation)
Introduce `A B _ _ _ _ _ r H R`. Set `e : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex A B))) A B` to `(Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)`. Use `set N := Fintype.card (Module.Free.ChooseBasisIndex A B)`. Use `set ξ := R.homEquiv (𝟙 H) with hξ`. Establish `hR : ∀ {Z : Scheme.{0}} (b : Z ⟶ H), R.homEquiv b = (functor A B r).map b.op ξ`.

Introduce `Z b`. Use `R.homEquiv_comp b (𝟙 H)` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `hmap : ∀ {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (b : Z ⟶ H), (functor A B r).map a.op ((functor A B r).map b.op ξ) = (functor A B r).map (a ≫ b).op ξ`. Introduce `Z Z' a b`.

Rewrite using `[← hR b, ← hR (a ≫ b), R.homEquiv_comp]`. Establish `hrc : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z), Set.range (a ≫ b) = b '' Set.range a`. Introduce `X Y Z a b`. Use extensionality with `p`. Simplify using the standard rewrite rules.

Use `choose W hW hWc using fun σ : Fin r ↪ Fin N => GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ H ξ`. Use `choose X x hXa hXl hXb hXu using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ`. Establish `hcov : ⨆ σ, W σ = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `h _`.

Take `⟨σ, U, hU, hb⟩` from `GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e H ξ h`. Use `(hW σ _ U.ι).2 hb` as an intermediate fact. Rewrite `this` using `[Scheme.Opens.range_ι]`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨σ, this hU⟩`. Establish `hiso : ∀ σ, ∃ g : (W σ).toScheme ⟶ X σ, IsIso g ∧ (W σ).ι ≫ ξ.1 = g ≫ (x σ).1`.

Introduce `σ`. Establish `hb : Basic A B e σ ((functor A B r).map (W σ).ι.op ξ)` using `(hW σ _ _).1 (by rw [Scheme.Opens.range_ι])`. Take `⟨g, hg, -⟩` from `hXu σ _ _ hb`. Take `⟨f, hf⟩ : ∃ f, R.homEquiv f = x σ` from `⟨_, Equiv.apply_symm_apply _ _⟩`. Establish `hfr : Set.range f ⊆ Set.range (W σ).ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(hW σ _ f).2 (by rw [← hR, hf]; exact hXb σ)`. Set `f'` to `IsOpenImmersion.lift (W σ).ι f hfr`. Establish `hf' : f' ≫ (W σ).ι = f` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hgf : g ≫ f = (W σ).ι` using `R.homEquiv.injective (by rw [R.homEquiv_comp, hf, hg, hR])`.

Establish `h1 : g ≫ f' = 𝟙 _`. Rewrite using `[← cancel_mono (W σ).ι, Category.assoc, hf', hgf, Category.id_comp]`. Establish `h2 : f' ≫ g = 𝟙 _`. Take `⟨g0, -, hu⟩` from `hXu σ (X σ) (x σ) (hXb σ)`. Establish `e1 : (functor A B r).map (f' ≫ g).op (x σ) = x σ`.

Rewrite using `[← hf, ← R.homEquiv_comp, Category.assoc, hgf, hf']`. Establish `e2 : (functor A B r).map (𝟙 (X σ)).op (x σ) = x σ` using `by simp`. Conclude with `(hu _ e1).trans (hu _ e2).symm`. Conclude with `⟨g, ⟨f', h1, h2⟩, (congrArg Sigma.fst hg).symm⟩`. Use `choose g hg hgx using hiso`.

Establish `hWa : ∀ σ, IsAffineOpen (W σ)` using `fun σ => by haveI := hg σ; haveI := hXa σ; exact IsAffine.of_isIso (g σ)`. Establish `hint : ∀ (U : H.Opens), CompactSpace U.toScheme → ∀ τ, IsCompact ((U : Set H) ∩ W τ)`. Introduce `U hU τ`. Take `⟨V, hV, hVc⟩` from `GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e τ U.toScheme ((functor A B r).map U.ι.op ξ)`. Establish `key : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ U.toScheme), Set.range a ⊆ V ↔ U.ι '' Set.range a ⊆ W τ` using `fun Z' a => by`.

Rewrite using `[hV, hmap, ← hW, hrc]`. Establish `hVeq : (V : Set U.toScheme) = U.ι ⁻¹' (W τ)`. Apply `subset_antisymm` to reduce the goal to its premises. Use `(key _ V.ι).1 (by rw [Scheme.Opens.range_ι])` as an intermediate fact. Rewrite `this` using `[Scheme.Opens.range_ι]`.

Conclude with `Set.image_subset_iff.1 this`. Use `(key _ (U.ι ⁻¹ᵁ W τ).ι).2 (by` as an intermediate fact. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `Set.image_preimage_subset _ _)`. Rewrite `this` using `[Scheme.Opens.range_ι]`.

Conclude with `this`. Establish `: (U : Set H) ∩ W τ = U.ι '' V`. Rewrite using `[hVeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]`. Rewrite using `[this]`. Conclude with `(hVc hU).image U.ι.continuous`.

Establish `hWc' : ∀ σ, CompactSpace (W σ).toScheme` using `fun σ => by haveI : IsAffine (W σ).toScheme := hWa σ infer_instance`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[quasiCompact_iff_compactSpace] show CompactSpace H`. Rewrite using `[← isCompact_univ_iff]`. Establish `: (Set.univ : Set H) = ⋃ σ, (W σ : Set H)`.

Rewrite using `[← TopologicalSpace.Opens.coe_iSup, hcov]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `isCompact_iUnion fun σ => (hWa σ).isCompact`. Rewrite using `[quasiSeparated_iff_quasiSeparatedSpace]`.

Conclude with `Scheme.quasiSeparatedSpace_of_isOpenCover W hcov hWa (fun σ τ => hint (W σ) (hWc' σ) τ)`. Use `haveI : IsZariskiLocalAtSource @LocallyOfFiniteType := HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) W hcov fun σ => ?_` and prove the remaining obligations. Rewrite using `[hgx σ]`. Use `haveI := hg σ`.

Use `haveI := hXl σ`. Use `infer_instance`.
-/
theorem representing_qc_qs_loft : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧
      LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H R
  classical
  let e : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex A B))) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  set N := Fintype.card (Module.Free.ChooseBasisIndex A B)
  set ξ := R.homEquiv (𝟙 H) with hξ
  have hR : ∀ {Z : Scheme.{0}} (b : Z ⟶ H), R.homEquiv b = (functor A B r).map b.op ξ := by
    intro Z b
    have := R.homEquiv_comp b (𝟙 H)
    rwa [Category.comp_id] at this
  have hmap : ∀ {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (b : Z ⟶ H),
      (functor A B r).map a.op ((functor A B r).map b.op ξ) = (functor A B r).map (a ≫ b).op ξ := by
    intro Z Z' a b
    rw [← hR b, ← hR (a ≫ b), R.homEquiv_comp]
  have hrc : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z),
      Set.range (a ≫ b) = b '' Set.range a := by
    intro X Y Z a b
    ext p
    simp
  choose W hW hWc using fun σ : Fin r ↪ Fin N => GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ H ξ
  choose X x hXa hXl hXb hXu using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  have hcov : ⨆ σ, W σ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨σ, U, hU, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e H ξ h
    have := (hW σ _ U.ι).2 hb
    rw [Scheme.Opens.range_ι] at this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨σ, this hU⟩
  have hiso : ∀ σ, ∃ g : (W σ).toScheme ⟶ X σ, IsIso g ∧ (W σ).ι ≫ ξ.1 = g ≫ (x σ).1 := by
    intro σ
    have hb : Basic A B e σ ((functor A B r).map (W σ).ι.op ξ) :=
      (hW σ _ _).1 (by rw [Scheme.Opens.range_ι])
    obtain ⟨g, hg, -⟩ := hXu σ _ _ hb
    obtain ⟨f, hf⟩ : ∃ f, R.homEquiv f = x σ := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hfr : Set.range f ⊆ Set.range (W σ).ι := by
      rw [Scheme.Opens.range_ι]
      exact (hW σ _ f).2 (by rw [← hR, hf]; exact hXb σ)
    let f' := IsOpenImmersion.lift (W σ).ι f hfr
    have hf' : f' ≫ (W σ).ι = f := IsOpenImmersion.lift_fac _ _ _
    have hgf : g ≫ f = (W σ).ι := R.homEquiv.injective (by rw [R.homEquiv_comp, hf, hg, hR])
    have h1 : g ≫ f' = 𝟙 _ := by
      rw [← cancel_mono (W σ).ι, Category.assoc, hf', hgf, Category.id_comp]
    have h2 : f' ≫ g = 𝟙 _ := by
      obtain ⟨g0, -, hu⟩ := hXu σ (X σ) (x σ) (hXb σ)
      have e1 : (functor A B r).map (f' ≫ g).op (x σ) = x σ := by
        rw [← hf, ← R.homEquiv_comp, Category.assoc, hgf, hf']
      have e2 : (functor A B r).map (𝟙 (X σ)).op (x σ) = x σ := by simp
      exact (hu _ e1).trans (hu _ e2).symm
    exact ⟨g, ⟨f', h1, h2⟩, (congrArg Sigma.fst hg).symm⟩
  choose g hg hgx using hiso
  have hWa : ∀ σ, IsAffineOpen (W σ) := fun σ => by
    haveI := hg σ; haveI := hXa σ; exact IsAffine.of_isIso (g σ)
  have hint : ∀ (U : H.Opens), CompactSpace U.toScheme → ∀ τ, IsCompact ((U : Set H) ∩ W τ) := by
    intro U hU τ
    obtain ⟨V, hV, hVc⟩ := GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e τ U.toScheme ((functor A B r).map U.ι.op ξ)
    have key : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ U.toScheme),
        Set.range a ⊆ V ↔ U.ι '' Set.range a ⊆ W τ := fun Z' a => by
      rw [hV, hmap, ← hW, hrc]
    have hVeq : (V : Set U.toScheme) = U.ι ⁻¹' (W τ) := by
      apply subset_antisymm
      · have := (key _ V.ι).1 (by rw [Scheme.Opens.range_ι])
        rw [Scheme.Opens.range_ι] at this
        exact Set.image_subset_iff.1 this
      · have := (key _ (U.ι ⁻¹ᵁ W τ).ι).2 (by
          rw [Scheme.Opens.range_ι]; exact Set.image_preimage_subset _ _)
        rw [Scheme.Opens.range_ι] at this
        exact this
    have : (U : Set H) ∩ W τ = U.ι '' V := by
      rw [hVeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    rw [this]
    exact (hVc hU).image U.ι.continuous
  have hWc' : ∀ σ, CompactSpace (W σ).toScheme := fun σ => by
    haveI : IsAffine (W σ).toScheme := hWa σ
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [quasiCompact_iff_compactSpace]
    show CompactSpace H
    rw [← isCompact_univ_iff]
    have : (Set.univ : Set H) = ⋃ σ, (W σ : Set H) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hcov]; rfl
    rw [this]
    exact isCompact_iUnion fun σ => (hWa σ).isCompact
  · rw [quasiSeparated_iff_quasiSeparatedSpace]
    exact Scheme.quasiSeparatedSpace_of_isOpenCover W hcov hWa
      (fun σ τ => hint (W σ) (hWc' σ) τ)
  · haveI : IsZariskiLocalAtSource @LocallyOfFiniteType := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) W hcov fun σ => ?_
    rw [hgx σ]
    haveI := hg σ
    haveI := hXl σ
    infer_instance

end GlobalTheory.HilbAff
