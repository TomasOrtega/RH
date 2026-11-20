import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Use `haveI := hM`. Use `haveI := hB`. Establish `hepi : Epi (Subobject.ofLE M B hle)`. Use `(GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov haff _).2 fun i y ↦ ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `h i ⟨y, rfl⟩`.

Use `⟨x, GlobalTheory.QCoh.injective_app_of_mono B.arrow _ ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Subobject.ofLE M B hle ≫ B.arrow).app _ x = _`. Rewrite using `[Subobject.ofLE_arrow]`. Conclude with `hx`. Use `haveI hmono : Mono (Subobject.ofLE M B hle) := mono_of_mono_fac (Subobject.ofLE_arrow hle)`.

Use `haveI : IsIso (Subobject.ofLE M B hle) := isIso_of_mono_of_epi _`. Use `le_antisymm (Subobject.le_of_comm (inv (Subobject.ofLE M B hle)) ?_) hle` and prove the remaining obligations. Rewrite using `[IsIso.inv_comp_eq, Subobject.ofLE_arrow]`.
-/
theorem eq_of_le_of_secs_subset {X : Scheme.{0}} {P : X.Modules} {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : TopologicalSpace.IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) {M B : Subobject P}
    (hM : (M : X.Modules).IsQuasicoherent) (hB : (B : X.Modules).IsQuasicoherent) (hle : M ≤ B)
    (h : ∀ i, secs B (𝒰 i) ⊆ secs M (𝒰 i)) : B = M := by
  haveI := hM
  haveI := hB
  have hepi : Epi (Subobject.ofLE M B hle) := by
    refine (GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov haff _).2 fun i y ↦ ?_
    obtain ⟨x, hx⟩ := h i ⟨y, rfl⟩
    refine ⟨x, GlobalTheory.QCoh.injective_app_of_mono B.arrow _ ?_⟩
    change (Subobject.ofLE M B hle ≫ B.arrow).app _ x = _
    rw [Subobject.ofLE_arrow]
    exact hx
  haveI hmono : Mono (Subobject.ofLE M B hle) := mono_of_mono_fac (Subobject.ofLE_arrow hle)
  haveI : IsIso (Subobject.ofLE M B hle) := isIso_of_mono_of_epi _
  refine le_antisymm (Subobject.le_of_comm (inv (Subobject.ofLE M B hle)) ?_) hle
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]

/- English proof (translation)
Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ U.1.isOpen) (fun x _ ↦ by`. Take `⟨U, ⟨V, hV, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩)`. Set `𝒰 : t → X.Opens` to `fun i ↦ (i.1 : X.Opens)`. Establish `hcov : TopologicalSpace.IsOpenCover 𝒰` using `top_le_iff.1 fun x _ ↦ by`.

Take `⟨U, hU, hx⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩`. Establish `haff : ∀ i, IsAffineOpen (𝒰 i)` using `fun i ↦ i.1.2`. Use `haveI hnoeth : ∀ i : t, IsNoetherianRing Γ(X, 𝒰 i) := fun i ↦ IsLocallyNoetherian.component_noetherian ⟨𝒰 i, haff i⟩`. Use `haveI hfin : ∀ i : t, Module.Finite Γ(X, 𝒰 i) Γ(P, 𝒰 i) := fun i ↦ hP.2 _ (haff i)`.

Use `haveI hwf : ∀ i : t, WellFoundedLT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ := fun i ↦ inferInstanceAs (WellFoundedGT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i)))`. Set `g : Subobject P → ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ` to `fun B i ↦ OrderDual.toDual (secsSub B (𝒰 i))`. Establish `hmin` using `(wellFounded_lt (α := ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ)).has_min (g '' F) (hF.image g)`. Take `⟨_, ⟨M, hM, rfl⟩, hmin⟩` from `hmin`. Use `⟨M, hM, fun B hB hle ↦ ?_⟩` and prove the remaining obligations.

Establish `hle' : g B ≤ g M` using `fun i ↦ by`. Express the relevant statement in the definitionally equal form `secsSub M (𝒰 i) ≤ secsSub B (𝒰 i)`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `⟨(Subobject.ofLE M B hle).app (𝒰 i) x, ?_⟩` and prove the remaining obligations. Rewrite using `[← Subobject.ofLE_arrow hle]`.

Both sides reduce to the same expression. Establish `heq : g B = g M`. Assume the negation of the conclusion as `hne`. Conclude with `hmin _ ⟨B, hB, rfl⟩ (lt_of_le_of_ne hle' hne)`. Use `eq_of_le_of_secs_subset 𝒰 hcov haff (hq M hM) (hq B hB) hle fun i ↦ ?_` and prove the remaining obligations.

Establish `hi : secsSub B (𝒰 i) = secsSub M (𝒰 i)` using `congrFun heq i`. Introduce `y hy`. Establish `hy' : y ∈ secsSub B (𝒰 i)` using `hy`. Rewrite `hy'` using `[hi]`. Conclude with `hy'`.
-/
theorem exists_maximal_qcoh_subobject {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}
    (hP : IsCoherent P) (F : Set (Subobject P)) (hF : F.Nonempty)
    (hq : ∀ B ∈ F, (B : X.Modules).IsQuasicoherent) :
    ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ U.1.isOpen) (fun x _ ↦ by
      obtain ⟨U, ⟨V, hV, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩)
  let 𝒰 : t → X.Opens := fun i ↦ (i.1 : X.Opens)
  have hcov : TopologicalSpace.IsOpenCover 𝒰 := top_le_iff.1 fun x _ ↦ by
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩
  have haff : ∀ i, IsAffineOpen (𝒰 i) := fun i ↦ i.1.2
  haveI hnoeth : ∀ i : t, IsNoetherianRing Γ(X, 𝒰 i) := fun i ↦
    IsLocallyNoetherian.component_noetherian ⟨𝒰 i, haff i⟩
  haveI hfin : ∀ i : t, Module.Finite Γ(X, 𝒰 i) Γ(P, 𝒰 i) := fun i ↦ hP.2 _ (haff i)
  haveI hwf : ∀ i : t, WellFoundedLT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ := fun i ↦
    inferInstanceAs (WellFoundedGT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i)))
  let g : Subobject P → ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ :=
    fun B i ↦ OrderDual.toDual (secsSub B (𝒰 i))
  have hmin := (wellFounded_lt (α := ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ)).has_min
    (g '' F) (hF.image g)
  obtain ⟨_, ⟨M, hM, rfl⟩, hmin⟩ := hmin
  refine ⟨M, hM, fun B hB hle ↦ ?_⟩
  have hle' : g B ≤ g M := fun i ↦ by
    change secsSub M (𝒰 i) ≤ secsSub B (𝒰 i)
    rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.ofLE M B hle).app (𝒰 i) x, ?_⟩
    rw [← Subobject.ofLE_arrow hle]
    rfl
  have heq : g B = g M := by
    by_contra hne
    exact hmin _ ⟨B, hB, rfl⟩ (lt_of_le_of_ne hle' hne)
  refine eq_of_le_of_secs_subset 𝒰 hcov haff (hq M hM) (hq B hB) hle fun i ↦ ?_
  have hi : secsSub B (𝒰 i) = secsSub M (𝒰 i) := congrFun heq i
  intro y hy
  have hy' : y ∈ secsSub B (𝒰 i) := hy
  rw [hi] at hy'
  exact hy'

end GlobalTheory.CompanionTheory.GE
