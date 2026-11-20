import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianBaseChange

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}

/- English proof (translation)
The claim follows from `hu (h₁.symm.trans h₂)`.
-/
theorem isPull1_unique {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    {w : φ ≫ s = s' ≫ spMap (algebraMap R R')} (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    {c : HH1 s} {c₁ c₂ : HH1 s'} (h₁ : IsPull1 w c c₁) (h₂ : IsPull1 w c c₂) : c₁ = c₂ :=
  hu (h₁.symm.trans h₂)

/- English proof (translation)
Substitute `hs hs'` using the available equality. Establish `key : ∀ c : FirstDeRham s, cmp1 s' (m.pull1 c) = e (1 ⊗ₜ cmp1 s c)` using `fun c ↦ isPull1_unique hu (comparison_pullback m c) (he _)`. Set `C` to `LinearEquiv.ofBijective (cmp1 s) hcmp`. Set `C'` to `LinearEquiv.ofBijective (cmp1 s') hcmp'`. Establish `hsq : (cmp1 s') ∘ₗ liftSemi m.pull1 = e.toLinearMap ∘ₗ (LinearEquiv.baseChange R R' _ _ C).toLinearMap`.

Use `LinearMap.ext fun z ↦ ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.

Consider the case `tmul x c`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, liftSemi_tmul, map_smul, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, key]`. Rewrite using `[← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hb : Function.Bijective ((cmp1 s') ∘ liftSemi m.pull1)`. Use `congrArg DFunLike.coe hsq` as an intermediate fact. Rewrite `this` using `[LinearMap.coe_comp]`. Rewrite using `[this, LinearMap.coe_comp]`. Conclude with `(e.bijective).comp (LinearEquiv.baseChange R R' _ _ C).bijective`.

Conclude with `(Function.Bijective.of_comp_iff' hcmp' _).1 hb`. Use `le_antisymm ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce `c' hc'`. Establish `h1 : cmp1 s' c' ∈ CechHodgeFiltration s'` using `comparison_mem_cechHodgeFiltration s' hc'`. Rewrite `h1` using `[cechHodgeFiltration_eq_range]`.

Take `⟨ω', hω'⟩` from `h1`. Set `Φ : GlobForm s' →ₗ[R'] HH1 s'` to `clForm s' ∘ₗ (LinearEquiv.ofTop _ hcl').symm.toLinearMap`. Set `Ψ : R' ⊗[R] GlobForm s →ₗ[R'] FirstDeRham s'` to `C'.symm.toLinearMap ∘ₗ Φ ∘ₗ e'.toLinearMap`. Establish `hΦ : ∀ ω : ClosedForm s', Φ ω.1 = clForm s' ω` using `fun ω ↦ by`. Simplify using `only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofTop_symm_apply]`.

Take `⟨z, hz⟩` from `e'.surjective ω'.1`. Establish `hc'z : c' = Ψ z`. Apply `hcmp'.1` to reduce the goal to its premises. Simplify using `only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hz, hΦ]`. Rewrite using `[← hω']`.

Conclude with `(C'.apply_symm_apply _).symm`. Rewrite using `[hc'z]`. Use `clear hc'z hz`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `tmul x ω`. Rewrite using `[show x ⊗ₜ[R] ω = x • (1 ⊗ₜ[R] ω) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]`. Use `Submodule.smul_mem _ x (Submodule.subset_span ?_)` and prove the remaining obligations.

Set `ωc : ClosedForm s` to `⟨ω, hcl ▸ trivial⟩`. Use `⟨C.symm (clForm s ωc), ?_, ?_⟩` and prove the remaining obligations. Establish `hF : clForm s ωc ∈ CechHodgeFiltration s` using `by rw [cechHodgeFiltration_eq_range]; exact ⟨ωc, rfl⟩`. Express the relevant statement in the definitionally equal form `toH1O s _ = 0`. Apply `hO` to reduce the goal to its premises.

Rewrite using `[← structureSheaf_comparison_comm, map_zero]`. Establish `: cmp1 s (C.symm (clForm s ωc)) = clForm s ωc` using `C.apply_symm_apply _`. Rewrite using `[this]`. Conclude with `hF`. Apply `hcmp'.1` to reduce the goal to its premises.

Set `ωc' : ClosedForm s'` to `⟨e' (1 ⊗ₜ ω), hcl' ▸ trivial⟩`. Establish `h2 : IsPull1 hpb (clForm s ωc) (clForm s' ωc')` using `IsPullForm.cl (he' ω)`. Establish `h3` using `comparison_pullback m (C.symm (clForm s ωc))`. Establish `h4 : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc` using `C.apply_symm_apply _`. Rewrite `h3` using `[h4]`.

Rewrite using `[isPull1_unique hu h3 h2]`. Simplify using `only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hΦ ωc']`. Conclude with `(C'.apply_symm_apply _).symm`. Introduce and unpack `_ ⟨c, hc, rfl⟩`.

Conclude with `m.pullback1_mem_hodgeFiltration hc`.
-/
theorem core (s₀ s : X ⟶ Sp R) (hs : s = s₀) (s₀' s' : X' ⟶ Sp R') (hs' : s' = s₀') (φ : X' ⟶ X)
    (hpb : φ ≫ s₀ = s₀' ≫ spMap (algebraMap R R'))
    (m : IsMor (dp0 R) s (dp0 R') s' (algebraMap R R') φ)
    (hcmp : Function.Bijective (cmp1 s)) (hcmp' : Function.Bijective (cmp1 s'))
    (hO : Function.Injective (cmpO s)) (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    (hcl : ClosedForm s₀ = ⊤) (hcl' : ClosedForm s₀' = ⊤)
    (e : R' ⊗[R] HH1 s₀ ≃ₗ[R'] HH1 s₀') (he : ∀ c, IsPull1 hpb c (e (1 ⊗ₜ c)))
    (e' : R' ⊗[R] GlobForm s₀ ≃ₗ[R'] GlobForm s₀') (he' : ∀ c, IsPullForm hpb c (e' (1 ⊗ₜ c))) :
    Function.Bijective (liftSemi m.pull1) ∧
      F1 s' = Submodule.span R' (m.pull1 '' (F1 s : Set (FirstDeRham s))) := by
  subst hs hs'

  have key : ∀ c : FirstDeRham s, cmp1 s' (m.pull1 c) = e (1 ⊗ₜ cmp1 s c) := fun c ↦
    isPull1_unique hu (comparison_pullback m c) (he _)
  let C := LinearEquiv.ofBijective (cmp1 s) hcmp
  let C' := LinearEquiv.ofBijective (cmp1 s') hcmp'
  have hsq : (cmp1 s') ∘ₗ liftSemi m.pull1 =
      e.toLinearMap ∘ₗ (LinearEquiv.baseChange R R' _ _ C).toLinearMap := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul x c =>
      simp only [LinearMap.coe_comp, Function.comp_apply, liftSemi_tmul, map_smul,
        LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, key]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  refine ⟨?_, ?_⟩
  · have hb : Function.Bijective ((cmp1 s') ∘ liftSemi m.pull1) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [this, LinearMap.coe_comp]
      exact (e.bijective).comp (LinearEquiv.baseChange R R' _ _ C).bijective
    exact (Function.Bijective.of_comp_iff' hcmp' _).1 hb
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro c' hc'
      have h1 : cmp1 s' c' ∈ CechHodgeFiltration s' := comparison_mem_cechHodgeFiltration s' hc'
      rw [cechHodgeFiltration_eq_range] at h1
      obtain ⟨ω', hω'⟩ := h1
      let Φ : GlobForm s' →ₗ[R'] HH1 s' :=
        clForm s' ∘ₗ (LinearEquiv.ofTop _ hcl').symm.toLinearMap
      let Ψ : R' ⊗[R] GlobForm s →ₗ[R'] FirstDeRham s' := C'.symm.toLinearMap ∘ₗ Φ ∘ₗ e'.toLinearMap
      have hΦ : ∀ ω : ClosedForm s', Φ ω.1 = clForm s' ω := fun ω ↦ by
        simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.ofTop_symm_apply]
      obtain ⟨z, hz⟩ := e'.surjective ω'.1
      have hc'z : c' = Ψ z := by
        apply hcmp'.1
        simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hz, hΦ]
        rw [← hω']
        exact (C'.apply_symm_apply _).symm
      rw [hc'z]
      clear hc'z hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul x ω =>
        rw [show x ⊗ₜ[R] ω = x • (1 ⊗ₜ[R] ω) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul]
        refine Submodule.smul_mem _ x (Submodule.subset_span ?_)
        let ωc : ClosedForm s := ⟨ω, hcl ▸ trivial⟩
        refine ⟨C.symm (clForm s ωc), ?_, ?_⟩
        · have hF : clForm s ωc ∈ CechHodgeFiltration s := by rw [cechHodgeFiltration_eq_range]; exact ⟨ωc, rfl⟩
          change toH1O s _ = 0
          apply hO
          rw [← structureSheaf_comparison_comm, map_zero]
          have : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [this]
          exact hF
        · apply hcmp'.1
          let ωc' : ClosedForm s' := ⟨e' (1 ⊗ₜ ω), hcl' ▸ trivial⟩
          have h2 : IsPull1 hpb (clForm s ωc) (clForm s' ωc') := IsPullForm.cl (he' ω)
          have h3 := comparison_pullback m (C.symm (clForm s ωc))
          have h4 : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [h4] at h3
          rw [isPull1_unique hu h3 h2]
          simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
          rw [hΦ ωc']
          exact (C'.apply_symm_apply _).symm
    · rintro _ ⟨c, hc, rfl⟩
      exact m.pullback1_mem_hodgeFiltration hc

end GlobalTheory.AbelianBaseChange

namespace GlobalTheory.AbelianBaseChange

/- English proof (translation)
Introduce `R _ A _ g hA hg R' _ _ A' _ φ h`. Establish `hA' : IsAbelianScheme A'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h`. Establish `hg' : SmoothOfRelativeDimension g A'.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h.1 hg`. Establish `hF` using `GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison H₁ H₂)`. Establish `hP : primDR A = ⊤` using `(hF R A g hA hg).1`.

Establish `hP' : primDR A' = ⊤` using `(hF R' A' g hA' hg').1`. Establish `geom : ∀ {S : Type} [CommRing S] (B : Over (Sp S)) [GrpObj B], IsAbelianScheme B → Smooth (B.hom ≫ 𝟙 _) ∧ IsSeparated (B.hom ≫ 𝟙 _) ∧ QuasiCompact (B.hom ≫ 𝟙 _)`. Introduce `S _ B _ hB`. Rewrite using `[Category.comp_id]`. Use `haveI := hB.smooth`.

Use `haveI := hB.proper`. Conclude with `⟨inferInstance, inferInstance, inferInstance⟩`. Take `⟨sm, se, sq⟩` from `geom A hA`. Take `⟨sm', se', sq'⟩` from `geom A' hA'`. Establish `hcmp` using `(GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R A.left (A.hom ≫ 𝟙 _) sm se sq).1`.

Establish `hcmp'` using `(GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R' A'.left (A'.hom ≫ 𝟙 _) sm' se' sq').1`. Take `⟨-, -, -, -, ⟨hcl, -, -⟩, hbc⟩` from `H₂ R A g hA hg`. Take `⟨-, -, -, -, ⟨hcl', -, -⟩, -⟩` from `H₂ R' A' g hA' hg'`. Take `⟨⟨e, he⟩, ⟨e', he'⟩, -⟩` from `hbc R' A'.left A'.hom φ h.1`. Set `m` to `(GlobalTheory.Published.AbelianDeRham.bcMor h).isMor`.

Take `⟨hB, hF1⟩` from `core A.hom (A.hom ≫ 𝟙 _) (Category.comp_id _) A'.hom (A'.hom ≫ 𝟙 _) (Category.comp_id _) φ h.1.w m hcmp hcmp' (GlobalTheory.T.structure_sheaf_comparison_injective R A.left _) (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (A'.hom ≫ 𝟙 _)).2.2 hcl hcl' e he e' he …`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hsq : (LinearEquiv.ofTop _ hP').toLinearMap ∘ₗ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull = liftSemi m.pull1 ∘ₗ (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).toLinearMap`. Use `LinearMap.ext fun z ↦ ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `tmul x c => rfl`. Establish `hb : Function.Bijective ((LinearEquiv.ofTop _ hP') ∘ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull)`.

Use `congrArg DFunLike.coe hsq` as an intermediate fact. Rewrite `this` using `[LinearMap.coe_comp]`. Rewrite `this` using `[LinearEquiv.coe_toLinearMap]`. Rewrite using `[this, LinearMap.coe_comp]`. Conclude with `hB.comp (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).bijective`.

Conclude with `(Function.Bijective.of_comp_iff' (LinearEquiv.ofTop _ hP').bijective _).1 hb`. Apply `Submodule.map_injective_of_injective (primDR A').injective_subtype` to reduce the goal to its premises. Rewrite using `[PrimitiveSubmodule, Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 (by rw [hP']; exact le_top), hF1, Submodule.map_span, Set.image_image]`. Use `congr 1`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `⟨⟨c, by rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hP]; trivial⟩, hc, rfl⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `⟨c.1, hc, rfl⟩`.
-/
theorem abelianDeRham_baseChange_of_smoothLift (H₁ : GlobalTheory.Published.CrystallineSmoothLift) (H₂ : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro R _ A _ g hA hg R' _ _ A' _ φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h.1 hg
  have hF := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison H₁ H₂)
  have hP : primDR A = ⊤ := (hF R A g hA hg).1
  have hP' : primDR A' = ⊤ := (hF R' A' g hA' hg').1
  have geom : ∀ {S : Type} [CommRing S] (B : Over (Sp S)) [GrpObj B], IsAbelianScheme B →
      Smooth (B.hom ≫ 𝟙 _) ∧ IsSeparated (B.hom ≫ 𝟙 _) ∧ QuasiCompact (B.hom ≫ 𝟙 _) := by
    intro S _ B _ hB
    rw [Category.comp_id]
    haveI := hB.smooth
    haveI := hB.proper
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨sm, se, sq⟩ := geom A hA
  obtain ⟨sm', se', sq'⟩ := geom A' hA'
  have hcmp := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R A.left (A.hom ≫ 𝟙 _) sm se sq).1
  have hcmp' := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R' A'.left (A'.hom ≫ 𝟙 _) sm' se' sq').1
  obtain ⟨-, -, -, -, ⟨hcl, -, -⟩, hbc⟩ := H₂ R A g hA hg
  obtain ⟨-, -, -, -, ⟨hcl', -, -⟩, -⟩ := H₂ R' A' g hA' hg'
  obtain ⟨⟨e, he⟩, ⟨e', he'⟩, -⟩ := hbc R' A'.left A'.hom φ h.1
  let m := (GlobalTheory.Published.AbelianDeRham.bcMor h).isMor
  obtain ⟨hB, hF1⟩ := core A.hom (A.hom ≫ 𝟙 _) (Category.comp_id _) A'.hom (A'.hom ≫ 𝟙 _)
    (Category.comp_id _) φ h.1.w m hcmp hcmp' (GlobalTheory.T.structure_sheaf_comparison_injective R A.left _)
    (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (A'.hom ≫ 𝟙 _)).2.2 hcl hcl' e he e' he'
  refine ⟨?_, ?_⟩
  · have hsq : (LinearEquiv.ofTop _ hP').toLinearMap ∘ₗ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull =
        liftSemi m.pull1 ∘ₗ (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).toLinearMap := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul x c => rfl
    have hb : Function.Bijective
        ((LinearEquiv.ofTop _ hP') ∘ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [LinearEquiv.coe_toLinearMap] at this
      rw [this, LinearMap.coe_comp]
      exact hB.comp (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).bijective
    exact (Function.Bijective.of_comp_iff' (LinearEquiv.ofTop _ hP').bijective _).1 hb
  · apply Submodule.map_injective_of_injective (primDR A').injective_subtype
    rw [PrimitiveSubmodule, Submodule.map_comap_eq, Submodule.range_subtype,
      inf_eq_right.2 (by rw [hP']; exact le_top), hF1,
      Submodule.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, by rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hP]; trivial⟩, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.1, hc, rfl⟩

end GlobalTheory.AbelianBaseChange
