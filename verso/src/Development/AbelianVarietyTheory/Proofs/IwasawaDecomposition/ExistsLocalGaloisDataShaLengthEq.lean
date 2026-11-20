import Mathlib
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.ShaTransport

section General

variable {R : Type*} [CommRing R] {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/- English proof (translation)
Establish `hc' : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho' (e' g) m) = rho g ((LinearMap.id : M →ₗ[R] M) m)`. Introduce `g m`. Use `hc (e' g) m` as an intermediate fact. Simplify using `only [LinearMap.id_apply, h1] at this ⊢`. Conclude with `this.symm`.

Use `Function.bijective_iff_has_inverse.2 ⟨pairH1DecompositionMap rho' rho e' he' LinearMap.id continuous_id hc', fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Simplify using `only [pairH1DecompositionMap, Submodule.mapQ_apply]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => by simp [h1])`.

Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Simplify using `only [pairH1DecompositionMap, Submodule.mapQ_apply]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => by simp [h2])`.
-/
theorem pairH1_id_bijective (rho : Representation R G M) (rho' : Representation R G' M)
    (e : G' →* G) (he : Continuous e) (e' : G →* G') (he' : Continuous e')
    (h1 : ∀ g, e (e' g) = g) (h2 : ∀ g, e' (e g) = g)
    (hc : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho (e g) m) = rho' g ((LinearMap.id : M →ₗ[R] M) m)) :
    Function.Bijective (pairH1DecompositionMap rho rho' e he LinearMap.id continuous_id hc) := by
  have hc' : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho' (e' g) m) = rho g ((LinearMap.id : M →ₗ[R] M) m) := by
    intro g m
    have := hc (e' g) m
    simp only [LinearMap.id_apply, h1] at this ⊢
    exact this.symm
  refine Function.bijective_iff_has_inverse.2
    ⟨pairH1DecompositionMap rho' rho e' he' LinearMap.id continuous_id hc', fun x => ?_, fun x => ?_⟩
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [h1])
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [h2])

end General

section Field

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω']

/- English proof (translation)
Rewrite using `[mem_Dec]`. Use extensionality with `y`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Take `⟨z, rfl⟩` from `σ.surjective y`. Establish `: (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G F Ω) z)`.

Rewrite using `[← map_inv]`. Use `show σ ((g⁻¹ : G F Ω) (σ.symm (σ z))) = _`. Rewrite using `[σ.symm_apply_apply]`. Rewrite using `[this, hA, hA]`. Conclude with `apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) z`.
-/
theorem autCongr_mem_Dec (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {g : G F Ω} (hg : g ∈ Dec (F := F) A) :
    (AlgEquiv.autCongr σ g : G F Ω') ∈ Dec (F := F) A₁ := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨z, rfl⟩ := σ.surjective y
  have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G F Ω) z) := by
    rw [← map_inv]
    show σ ((g⁻¹ : G F Ω) (σ.symm (σ z))) = _
    rw [σ.symm_apply_apply]
  rw [this, hA, hA]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) z

/- English proof (translation)
Introduce `x`. Rewrite using `[← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← σ.commutes, hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]`.
-/
theorem isPlaceOver_transport (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω}
    {A₁ : ValuationSubring Ω'} (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : IsPlaceOver A₁ v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← σ.commutes, hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]

/- English proof (translation)
Establish `hcont` using `GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ`. Establish `hN : ((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom).Normal` using `Subgroup.Normal.comap inferInstance _`. Establish `hcl : IsClosed (((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom : Subgroup (G F Ω)) : Set (G F Ω))` using `(isClosed_NS Ω' S).preimage hcont.1`. Unfold `NS`. Apply `Subgroup.topologicalClosure_minimal _ _ hcl` to reduce the goal to its premises.

Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `g hg`. Simplify using `only [Set.mem_iUnion] at hg`. Take `⟨v, hv, A, hA, hg⟩` from `hg`. Use `show AlgEquiv.autCongr σ g ∈ NS Ω' S`.

Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises. Establish `hA₁ : ∀ y, σ y ∈ A.comap (σ.symm : Ω' →+* Ω) ↔ y ∈ A` using `fun y => by`. Rewrite using `[ValuationSubring.mem_comap]`. Simplify using the standard rewrite rules.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨v, hv, A.comap (σ.symm : Ω' →+* Ω), isPlaceOver_transport σ hA₁ hA, hcont.2.2 A _ hA₁ g hg⟩`.
-/
theorem NS_le_comap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S ≤ (NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom := by
  have hcont := GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ
  have hN : ((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hcl : IsClosed (((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom : Subgroup (G F Ω)) :
      Set (G F Ω)) := (isClosed_NS Ω' S).preimage hcont.1
  unfold NS
  apply Subgroup.topologicalClosure_minimal _ _ hcl
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  show AlgEquiv.autCongr σ g ∈ NS Ω' S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  have hA₁ : ∀ y, σ y ∈ A.comap (σ.symm : Ω' →+* Ω) ↔ y ∈ A := fun y => by
    rw [ValuationSubring.mem_comap]
    simp
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A.comap (σ.symm : Ω' →+* Ω), isPlaceOver_transport σ hA₁ hA,
    hcont.2.2 A _ hA₁ g hg⟩

def gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) : GS Ω' S →* GS Ω S :=
  QuotientGroup.map (NS Ω' S) (NS Ω S) (AlgEquiv.autCongr σ.symm).toMonoidHom (NS_le_comap σ.symm S)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gsMap_mk (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω') :
    gsMap σ S (toGS Ω' S g) = toGS Ω S (AlgEquiv.autCongr σ.symm g) := rfl

/- English proof (translation)
The claim follows from `(QuotientGroup.isQuotientMap_mk (NS Ω' S)).continuous_iff.2 ((continuous_toGS Ω S).comp (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).1)`.
-/
theorem continuous_gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    Continuous (gsMap σ S) :=
  (QuotientGroup.isQuotientMap_mk (NS Ω' S)).continuous_iff.2
    ((continuous_toGS Ω S).comp (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).1)

/- English proof (translation)
Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Use `show toGS Ω S (AlgEquiv.autCongr σ.symm (AlgEquiv.autCongr σ.symm.symm g)) = toGS Ω S g`. Use `congr 1`. Use extensionality with `y`. Simplify using `[AlgEquiv.autCongr_apply]`.
-/
theorem gsMap_gsMap_symm (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (x : GS Ω S) :
    gsMap σ S (gsMap σ.symm S x) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show toGS Ω S (AlgEquiv.autCongr σ.symm (AlgEquiv.autCongr σ.symm.symm g)) = toGS Ω S g
  congr 1
  ext y
  simp [AlgEquiv.autCongr_apply]

def transport {l : ℕ} [Fact l.Prime] (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) : LData F Ω' l where
  S := D.S
  hS := D.hS
  A v := (D.A v).comap (σ.symm : Ω' →+* Ω)
  hA v := isPlaceOver_transport σ (fun y => by rw [ValuationSubring.mem_comap]; simp) (D.hA v)
  chi := D.chi.comp (gsMap σ _)
  hchi := by
    ext g
    have h1 := congrArg (fun f => ((f (AlgEquiv.autCongr σ.symm g) : ℤ_[l]ˣ) : ℤ_[l])) D.hchi
    have h2 := (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).2.1 l g
    simp only [MonoidHom.comp_apply] at h1
    simp only [MonoidHom.comp_apply, gsMap_mk]
    rw [h1, h2]

end Field

section Sha

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] {l : ℕ} [Fact l.Prime]

def decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Dec (F := F) A →* Dec (F := F) A₁ :=
  ((AlgEquiv.autCongr σ).toMonoidHom.comp (Dec (F := F) A).subtype).codRestrict _
    (fun g => autCongr_mem_Dec σ hA g.2)

/- English proof (translation)
The claim follows from `Continuous.subtype_mk ((GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ).1.comp continuous_subtype_val) _`.
-/
theorem continuous_decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Continuous (decMap σ hA) :=
  Continuous.subtype_mk ((GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ).1.comp
    continuous_subtype_val) _

/- English proof (translation)
Establish `hc : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (gsMap σ _ g) m) = qzTw (transport σ D) e g ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m)` using `fun _ _ => rfl`. Establish `hΦ` using `pairH1_id_bijective (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _) (continuous_gsMap σ _) (gsMap σ.symm _) (continuous_gsMap σ.symm _) (gsMap_gsMap_symm σ _) (gsMap_gsMap_symm σ.symm _) hc`. Use `set Φ := pairH1DecompositionMap (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _) (continuous_gsMap σ _) LinearMap.id continuous_id hc with hΦdef`. Establish `key : ∀ x, x ∈ Sha D e ↔ Φ x ∈ Sha (transport σ D) e`. Introduce `x`.

Simplify using `only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker]`. Use `forall_congr' fun v => ?_` and prove the remaining obligations. Establish `hA₁ : ∀ y, σ.symm y ∈ D.A v ↔ y ∈ (transport σ D).A v` using `fun y => by show _ ↔ y ∈ (D.A v).comap (σ.symm : Ω' →+* Ω)`. Rewrite using `[ValuationSubring.mem_comap]`. Both sides reduce to the same expression.

Establish `hA : ∀ y, σ y ∈ (transport σ D).A v ↔ y ∈ D.A v` using `fun y => by`. Rewrite using `[← hA₁, σ.symm_apply_apply]`. Establish `hcv : ∀ k m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) ((qzTw D e).comp (locFam D.S D.A v) (decMap σ.symm hA₁ k) m) = ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v)) k ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m)` using `fun _ _ => rfl`. Establish `hΔ` using `pairH1_id_bijective ((qzTw D e).comp (locFam D.S D.A v)) ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v)) (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) (decMap σ hA) (continuous_decMap σ hA) (fun g => Subtype.ext (by ext y; simp [decMap, AlgEqui …`. Establish `hres : resH1 (qzTw (transport σ D) e) (locFam (transport σ D).S (transport σ D).A v) (continuous_locFam _ _ v) (Φ x) = pairH1DecompositionMap _ _ (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) LinearMap.id continuous_id hcv (resH1 (qzTw D e) (locFam D.S D.A v) (continuous_loc …`.

Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `hres.trans (by rw [h, map_zero])`.

Introduce `h`. Conclude with `hΔ.1 (by rw [map_zero]; exact hres.symm.trans h)`. Set `Φe` to `LinearEquiv.ofBijective Φ hΦ`. Establish `hmap : (Sha D e).map Φe.toLinearMap = Sha (transport σ D) e`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(key x).1 hx`. Introduce `hy`. Use `⟨Φe.symm y, (key _).2 ?_, Φe.apply_symm_apply y⟩` and prove the remaining obligations.

Establish `: Φ (Φe.symm y) = y` using `Φe.apply_symm_apply y`. Rewrite using `[this]`. Conclude with `hy`. Conclude with `(LinearEquiv.ofSubmodules Φe _ _ hmap).length_eq.symm`.
-/
theorem shaLen_transport (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) (e : ℤ) :
    shaLen (transport σ D) e = shaLen D e := by
  have hc : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (gsMap σ _ g) m) =
      qzTw (transport σ D) e g ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
  have hΦ := pairH1_id_bijective (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _)
    (continuous_gsMap σ _) (gsMap σ.symm _) (continuous_gsMap σ.symm _)
    (gsMap_gsMap_symm σ _) (gsMap_gsMap_symm σ.symm _) hc
  set Φ := pairH1DecompositionMap (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _) (continuous_gsMap σ _)
    LinearMap.id continuous_id hc with hΦdef
  have key : ∀ x, x ∈ Sha D e ↔ Φ x ∈ Sha (transport σ D) e := by
    intro x
    simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun v => ?_
    have hA₁ : ∀ y, σ.symm y ∈ D.A v ↔ y ∈ (transport σ D).A v := fun y => by
      show _ ↔ y ∈ (D.A v).comap (σ.symm : Ω' →+* Ω)
      rw [ValuationSubring.mem_comap]
      rfl
    have hA : ∀ y, σ y ∈ (transport σ D).A v ↔ y ∈ D.A v := fun y => by
      rw [← hA₁, σ.symm_apply_apply]
    have hcv : ∀ k m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l)
        ((qzTw D e).comp (locFam D.S D.A v) (decMap σ.symm hA₁ k) m) =
        ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v)) k
          ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
    have hΔ := pairH1_id_bijective ((qzTw D e).comp (locFam D.S D.A v))
      ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v))
      (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) (decMap σ hA) (continuous_decMap σ hA)
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply]))
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply])) hcv
    have hres : resH1 (qzTw (transport σ D) e) (locFam (transport σ D).S (transport σ D).A v)
        (continuous_locFam _ _ v) (Φ x) =
        pairH1DecompositionMap _ _ (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) LinearMap.id continuous_id hcv
          (resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam _ _ v) x) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    constructor
    · intro h
      exact hres.trans (by rw [h, map_zero])
    · intro h
      exact hΔ.1 (by rw [map_zero]; exact hres.symm.trans h)
  let Φe := LinearEquiv.ofBijective Φ hΦ
  have hmap : (Sha D e).map Φe.toLinearMap =
      Sha (transport σ D) e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (key x).1 hx
    · intro hy
      refine ⟨Φe.symm y, (key _).2 ?_, Φe.apply_symm_apply y⟩
      have : Φ (Φe.symm y) = y := Φe.apply_symm_apply y
      rw [this]
      exact hy
  exact (LinearEquiv.ofSubmodules Φe _ _ hmap).length_eq.symm

/- English proof (translation)
Introduce `F Ω Ω' _ _ _ _ _ _ _ _ l _ D`. Conclude with `⟨transport (IsAlgClosure.equiv F Ω Ω') D, shaLen_transport _ D⟩`.
-/
theorem exists_lData_shaLen_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ)
    [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l),
    ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  intro F Ω Ω' _ _ _ _ _ _ _ _ l _ D
  exact ⟨transport (IsAlgClosure.equiv F Ω Ω') D, shaLen_transport _ D⟩

end Sha

end GlobalTheory.ShaTransport
