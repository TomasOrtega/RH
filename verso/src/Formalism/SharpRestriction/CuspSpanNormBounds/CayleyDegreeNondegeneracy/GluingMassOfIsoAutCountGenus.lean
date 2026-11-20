import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tr

variable (D : D7)

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [isomAct_mem_gmap, Submodule.mem_inf]`.
-/
theorem gmap_inf_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]

/- English proof (translation)
The claim follows from `Submodule.map_sup _ _ _`.
-/
theorem gmap_sup_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊔ B) = gmap g A ⊔ gmap g B := Submodule.map_sup _ _ _

variable {D}

/- English proof (translation)
Establish `hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y` using `hσ`. Establish `hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X`. Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : σ.symm x ∈ F0.X` using `h`. Use `hX _ h'` as an intermediate fact. Establish `e : σ.symm x = x`. Apply `σ.symm.injective` to reduce the goal to its premises.

Conclude with `this`. Rewrite `h` using `[e]`. Conclude with `h`. Introduce `h`. Establish `h' : x ∈ F0.X` using `h`.

Rewrite using `[hX x h']`. Conclude with `h`. Establish `hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X)`. Use extensionality with `y`. Rewrite using `[isomAct_mem_gmap]`.

Express the relevant statement in the definitionally equal form `σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X`. Rewrite using `[Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]`. Use `forall₂_congr fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]`. Establish `: σ x = x`.

Rewrite using `[← LinearEquiv.eq_symm_apply, hX x hx]`. Rewrite using `[this]`. Establish `hXLam : XLam (gmap σ Λ) (lf D F0) = XLam Λ (lf D F0)`. Establish `h1 : XLam (gmap σ Λ) (lf D F0) = gmap σ (XLam Λ (lf D F0))`. Unfold `XLam`.

Rewrite using `[gmap_inf_cayley_degree_nondegeneracy]`. Express the relevant statement in the definitionally equal form `gmap σ Λ ⊓ toO (hS D) F0.X = gmap σ Λ ⊓ gmap σ (toO (hS D) F0.X)`. Rewrite using `[hgX]`. Rewrite using `[h1]`. Use extensionality with `x`.

Rewrite using `[isomAct_mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : σ.symm x ∈ F0.X` using `h.2`. Establish `e : σ.symm x = x` using `σ.symm.injective (hX _ h')`.

Rewrite `h` using `[e]`. Conclude with `h`. Introduce `h`. Establish `h' : x ∈ F0.X` using `h.2`. Rewrite using `[hX x h']`.

Conclude with `h`. Establish `hLsub : Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0))`. Unfold `Lsub Lrep`. Rewrite using `[gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]`. Express the relevant statement in the definitionally equal form `(gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) = (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X))`.

Rewrite using `[hgX, hgO]`. Use `⟨?_, hLsub⟩` and prove the remaining obligations. Take `⟨⟨hlat1, hgen1⟩, ⟨hL, hU, hLift, hConv⟩, hXS⟩` from `hΛ`. Take `⟨_, hloc, _, huni, _⟩` from `isomAct (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT σ hσ Λ`. Use `⟨⟨isomAct_lattice σ Λ hlat1, fun p hp => ?_⟩, ⟨isomAct_lattice σ Λ hL, huni.2 hU, ⟨?_, hLift.2⟩, ?_, fun c hc => hConv.2 c ?_⟩, hXLam.trans hXS⟩` and prove the remaining obligations.

Take `⟨g, hg, e⟩` from `hgen1 p hp`. Conclude with `⟨σ * g, (isom (VS D).hT).mul_mem hσ hg, by rw [gmap_mul, e, hloc p]⟩`. Rewrite using `[isomAct_mem_gmap]`. Express the relevant statement in the definitionally equal form `σ.symm F0.z ∈ Λ`. Rewrite using `[hz]`.

Conclude with `hLift.1`. Rewrite using `[hXLam]`. Conclude with `hConv.1`. Rewrite `hc` using `[hLsub, isomAct_mem_gmap, map_smul]`. Express the relevant statement in the definitionally equal form `c • σ.symm F0.z ∈ _ at hc`.

Rewrite `hc` using `[hz]`. Conclude with `hc`.
-/
theorem isLattice_gmap_of_flag_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : ∀ x ∈ F0.X, σ.symm x = x) (hz : σ.symm F0.z = F0.z) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap σ Λ) ∧ Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h
      have := hX _ h'
      have e : σ.symm x = x := by
        apply σ.symm.injective
        exact this
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h
      rw [hX x h']
      exact h
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    refine forall₂_congr fun x hx => ?_
    rw [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
    have : σ x = x := by
      rw [← LinearEquiv.eq_symm_apply, hX x hx]
    rw [this]
  have hXLam : XLam (gmap σ Λ) (lf D F0) = XLam Λ (lf D F0) := by
    have h1 : XLam (gmap σ Λ) (lf D F0) = gmap σ (XLam Λ (lf D F0)) := by
      unfold XLam
      rw [gmap_inf_cayley_degree_nondegeneracy]
      change gmap σ Λ ⊓ toO (hS D) F0.X = gmap σ Λ ⊓ gmap σ (toO (hS D) F0.X)
      rw [hgX]
    rw [h1]
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h.2
      have e : σ.symm x = x := σ.symm.injective (hX _ h')
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h.2
      rw [hX x h']
      exact h
  have hLsub : Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
    unfold Lsub Lrep
    rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
    change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
      (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
        gmap σ (toO (hS D) (orth (hS D) F0.X))
    rw [hgX, hgO]
  refine ⟨?_, hLsub⟩
  obtain ⟨⟨hlat1, hgen1⟩, ⟨hL, hU, hLift, hConv⟩, hXS⟩ := hΛ
  obtain ⟨_, hloc, _, huni, _⟩ := isomAct (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT σ hσ Λ
  refine ⟨⟨isomAct_lattice σ Λ hlat1, fun p hp => ?_⟩,
    ⟨isomAct_lattice σ Λ hL, huni.2 hU, ⟨?_, hLift.2⟩, ?_, fun c hc => hConv.2 c ?_⟩, hXLam.trans hXS⟩
  · obtain ⟨g, hg, e⟩ := hgen1 p hp
    exact ⟨σ * g, (isom (VS D).hT).mul_mem hσ hg, by rw [gmap_mul, e, hloc p]⟩
  · rw [isomAct_mem_gmap]
    change σ.symm F0.z ∈ Λ
    rw [hz]
    exact hLift.1
  · rw [hXLam]
    exact hConv.1
  · rw [hLsub, isomAct_mem_gmap, map_smul] at hc
    change c • σ.symm F0.z ∈ _ at hc
    rw [hz] at hc
    exact hc

variable (D)

/- English proof (translation)
Introduce `_ _ _ F0 he hz γ hγ Λ₁ hΛ₁`. Establish `hzO : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[hz]`.

Conclude with `Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)`. Establish `hXO : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[he]`.

Express the relevant statement in the definitionally equal form `D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `(D.sp.hyp_orthX a w).1`. Apply the tactic sequence `obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ) (fun x hx => extendByIdentity_symm_fix_orth D γ x (hXO hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ₁ hΛ₁`.

Use `⟨gmap (extendByIdentity D γ) Λ₁, hrow, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨w, c⟩`. Unfold `latticeWithZ`. Rewrite using `[Submodule.mem_comap, hLsub, isomAct_mem_gmap, isomAct_mem_gmap, Submodule.mem_comap]`. Establish `e1 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) (w, c) = D.sp.iXY 0 w + c • F0.z`.

Simplify using `[embedWithZ]`. Establish `e2 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) ((extendByOne D γ).symm (w, c)) = D.sp.iXY 0 (γ.symm w) + c • F0.z`. Establish `: (extendByOne D γ).symm (w, c) = (γ.symm w, c)` using `rfl`. Rewrite using `[this]`. Simplify using `[embedWithZ]`.

Rewrite using `[e1, e2, extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]`.
-/
theorem isometries_transport_lattices (u : D.what₂.Word) : IsometriesTransportLattices D u := by
  intro _ _ _ F0 he hz γ hγ Λ₁ hΛ₁
  have hzO : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    rw [hz]
    exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)
  have hXO : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [he]
    change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    exact (D.sp.hyp_orthX a w).1
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (hXO hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ₁ hΛ₁
  refine ⟨gmap (extendByIdentity D γ) Λ₁, hrow, ?_⟩
  ext ⟨w, c⟩
  unfold latticeWithZ
  rw [Submodule.mem_comap, hLsub, isomAct_mem_gmap, isomAct_mem_gmap, Submodule.mem_comap]
  have e1 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) (w, c) = D.sp.iXY 0 w + c • F0.z := by
    simp [embedWithZ]
  have e2 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) ((extendByOne D γ).symm (w, c)) =
      D.sp.iXY 0 (γ.symm w) + c • F0.z := by
    have : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [this]
    simp [embedWithZ]
  rw [e1, e2, extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

/- English proof (translation)
The claim follows from `gluing_mass_of_gluing_facts D u hpos hlat h1 h2 (isometries_transport_lattices D u) h4 h5`.
-/
theorem gluing_mass_of_iso_aut_count_genus (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_gluing_facts D u hpos hlat h1 h2 (isometries_transport_lattices D u) h4 h5

end Tr

end Formalism.MainNotions.BridgeLemma₂

end
