import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PullSupp

/- English proof (translation)
Use `Scheme.Modules.SupportedIn.of_isZero_restrict fun U hU => ?_` and prove the remaining obligations. Set `V : X.Opens` to `⟨T₀ᶜ, hT.isOpen_compl⟩`. Establish `hr : Set.range (U.ι ≫ φ) ⊆ Set.range V.ι`. Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce `hx`. Conclude with `Set.disjoint_left.1 hU u.2 hx`. Set `g` to `IsOpenImmersion.lift V.ι (U.ι ≫ φ) hr`. Establish `hg : g ≫ V.ι = U.ι ≫ φ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj C)` using `h.isZero_restrict V disjoint_compl_left`.

Establish `h1 : IsZero ((Scheme.Modules.pullback g).obj ((Scheme.Modules.restrictFunctor V.ι).obj C))` using `Functor.map_isZero _ h0`. Use `h1.of_iso ?_` and prove the remaining obligations. Conclude with `(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ (Scheme.Modules.pullbackComp U.ι φ).app C ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app C ≪≫ ((Scheme.Modules.pullbackComp g V.ι).app C).symm ≪≫ (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback …`.
-/
theorem supportedIn_pullback {X Z : Scheme.{0}} (φ : Z ⟶ X) {C : X.Modules} {T₀ : Set X}
    (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn C T₀) :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pullback φ).obj C) (φ.base ⁻¹' T₀) := by
  refine Scheme.Modules.SupportedIn.of_isZero_restrict fun U hU => ?_
  let V : X.Opens := ⟨T₀ᶜ, hT.isOpen_compl⟩
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    intro hx
    exact Set.disjoint_left.1 hU u.2 hx
  let g := IsOpenImmersion.lift V.ι (U.ι ≫ φ) hr
  have hg : g ≫ V.ι = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj C) :=
    h.isZero_restrict V disjoint_compl_left
  have h1 : IsZero ((Scheme.Modules.pullback g).obj ((Scheme.Modules.restrictFunctor V.ι).obj C)) :=
    Functor.map_isZero _ h0
  refine h1.of_iso ?_
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι φ).app C ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app C ≪≫
    ((Scheme.Modules.pullbackComp g V.ι).app C).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app C).symm

end GlobalTheory.CompanionTheory.GE.PullSupp

namespace GlobalTheory.CompanionTheory.GE.PullSupp

/- English proof (translation)
Set `f` to `(Scheme.Modules.pullback φ).map (S 0).arrow`. Establish `hle : imageSubobject f ≤ pullSys I φ E S 0` using `le_sup_left`. Establish `w : f ≫ cokernel.π (pullSys I φ E S 0).arrow = 0`. Rewrite using `[← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc, cokernel.condition, comp_zero, comp_zero]`. Establish `hd : Epi (cokernel.desc f _ w)` using `epi_of_epi_fac (cokernel.π_desc f _ w)`.

Establish `h1 : Scheme.Modules.SupportedIn (cokernel f) (φ.base ⁻¹' T₀)` using `(supportedIn_pullback φ hT h).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback φ) (S 0).arrow)`. Conclude with `Scheme.Modules.SupportedIn.of_epi (cokernel.desc f _ w) h1`.
-/
theorem supportedIn_cokernel_pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E)
    {T₀ : Set X} (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn (cokernel (S 0).arrow) T₀) :
    Scheme.Modules.SupportedIn (cokernel (pullSys I φ E S 0).arrow) (φ.base ⁻¹' T₀) := by
  let f := (Scheme.Modules.pullback φ).map (S 0).arrow
  have hle : imageSubobject f ≤ pullSys I φ E S 0 := le_sup_left
  have w : f ≫ cokernel.π (pullSys I φ E S 0).arrow = 0 := by
    rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  have hd : Epi (cokernel.desc f _ w) := epi_of_epi_fac (cokernel.π_desc f _ w)
  have h1 : Scheme.Modules.SupportedIn (cokernel f) (φ.base ⁻¹' T₀) :=
    (supportedIn_pullback φ hT h).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback φ) (S 0).arrow)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc f _ w) h1

/- English proof (translation)
Set `p` to `pullback.fst φ T.subschemeι`. Set `q` to `pullback.snd φ T.subschemeι`. Establish `hpc : IsClosedImmersion p` using `inferInstance`. Set `T' : Z.IdealSheafData` to `p.ker`. Establish `hk1 : p.ker ≤ T'.subschemeι.ker` using `by rw [Scheme.IdealSheafData.ker_subschemeι]`.

Establish `hk2 : T'.subschemeι.ker ≤ p.ker` using `by rw [Scheme.IdealSheafData.ker_subschemeι]`. Set `u` to `IsClosedImmersion.lift p T'.subschemeι hk1`. Set `v` to `IsClosedImmersion.lift T'.subschemeι p hk2`. Establish `hu : u ≫ p = T'.subschemeι` using `IsClosedImmersion.lift_fac _ _ _`. Establish `hv : v ≫ T'.subschemeι = p` using `IsClosedImmersion.lift_fac _ _ _`.

Use `⟨T', ?_, ?_⟩` and prove the remaining obligations. Establish `hq : IsProper q` using `by haveI := hφ; infer_instance`. Establish `huc : IsClosedImmersion u`. Establish `: IsClosedImmersion (u ≫ p)` using `by rw [hu]; infer_instance`. Conclude with `IsClosedImmersion.of_comp u p`.

Establish `e : T'.subschemeι ≫ (Z ↘ Spec (.of A)) = u ≫ q ≫ (T.subschemeι ≫ (X ↘ Spec (.of A)))`. Rewrite using `[← hu, ← hc, Category.assoc, ← Category.assoc p, pullback.condition]`. Simplify using `only [Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `infer_instance`. Introduce `z hz`. Take `⟨w, hw⟩` from `T.range_subschemeι.ge hz`. Take `⟨t, ht, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := φ) (g := T.subschemeι) z w hw.symm`. Rewrite using `[← T'.range_subschemeι]`.

Use `⟨v t, ?_⟩` and prove the remaining obligations. Establish `hv' : v ≫ T'.subschemeι = pullback.fst φ T.subschemeι` using `hv`. Rewrite using `[← ht, ← hv']`. Both sides reduce to the same expression.
-/
theorem exists_proper_preimage {A : Type} [CommRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))]
    [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (hφ : IsProper φ)
    (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ (X ↘ Spec (.of A)))) :
    ∃ T' : Z.IdealSheafData, IsProper (T'.subschemeι ≫ (Z ↘ Spec (.of A))) ∧
      φ.base ⁻¹' (T.support : Set X) ⊆ (T'.support : Set Z) := by
  let p := pullback.fst φ T.subschemeι
  let q := pullback.snd φ T.subschemeι
  have hpc : IsClosedImmersion p := inferInstance
  let T' : Z.IdealSheafData := p.ker
  have hk1 : p.ker ≤ T'.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  have hk2 : T'.subschemeι.ker ≤ p.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  let u := IsClosedImmersion.lift p T'.subschemeι hk1
  let v := IsClosedImmersion.lift T'.subschemeι p hk2
  have hu : u ≫ p = T'.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hv : v ≫ T'.subschemeι = p := IsClosedImmersion.lift_fac _ _ _
  refine ⟨T', ?_, ?_⟩
  · have hq : IsProper q := by haveI := hφ; infer_instance
    have huc : IsClosedImmersion u := by
      have : IsClosedImmersion (u ≫ p) := by rw [hu]; infer_instance
      exact IsClosedImmersion.of_comp u p
    have e : T'.subschemeι ≫ (Z ↘ Spec (.of A)) = u ≫ q ≫ (T.subschemeι ≫ (X ↘ Spec (.of A))) := by
      rw [← hu, ← hc, Category.assoc, ← Category.assoc p, pullback.condition]
      simp only [Category.assoc]
      rfl
    rw [e]
    infer_instance
  · intro z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := T.subschemeι) z w hw.symm
    rw [← T'.range_subschemeι]
    refine ⟨v t, ?_⟩
    have hv' : v ≫ T'.subschemeι = pullback.fst φ T.subschemeι := hv
    rw [← ht, ← hv']
    rfl

/- English proof (translation)
Introduce `A _ _ I X Z _ _ _ φ hφ hc E _ S _ hS`. Take `⟨T, hTp, hTs⟩` from `hS`. Take `⟨T', hT'p, hT's⟩` from `exists_proper_preimage φ hφ hc T hTp`. Conclude with `⟨T', hT'p, (supportedIn_cokernel_pullSys I φ E S T.support.isClosed hTs).mono hT's⟩`.
-/
theorem propSupp_pullSys : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ →
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  intro A _ _ I X Z _ _ _ φ hφ hc E _ S _ hS
  obtain ⟨T, hTp, hTs⟩ := hS
  obtain ⟨T', hT'p, hT's⟩ := exists_proper_preimage φ hφ hc T hTp
  exact ⟨T', hT'p, (supportedIn_cokernel_pullSys I φ E S T.support.isClosed hTs).mono hT's⟩

end GlobalTheory.CompanionTheory.GE.PullSupp
