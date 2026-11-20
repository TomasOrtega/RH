import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.UV

/- English proof (translation)
Use `subsingleton_of_forall_eq 0 fun s => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app (biproduct.desc φ) hV s`. Establish `hle : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) ≤ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨i, x, rfl⟩` from `Set.mem_iUnion.1 hy`. Establish `hz : φ i ≫ cokernel.π (biproduct.desc φ) = 0`. Rewrite using `[← biproduct.ι_desc φ i, Category.assoc, cokernel.condition, comp_zero]`. Express the relevant statement in the definitionally equal form `(cokernel.π (biproduct.desc φ)).app V ((φ i).app V x) = 0`. Rewrite using `[GlobalTheory.QCoh.app_app, hz]`.

Both sides reduce to the same expression. Establish `ht : t ∈ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V)` using `hle (h ▸ Submodule.mem_top)`. Conclude with `ht`.
-/
theorem subsingleton_cokernel_desc_of_span {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} [∀ i, (F i).IsQuasicoherent] [G.IsQuasicoherent]
    [(biproduct F).IsQuasicoherent] (φ : ∀ i, F i ⟶ G) {V : X.Opens} (hV : IsAffineOpen V)
    (h : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) = ⊤) :
    Subsingleton Γ(cokernel (biproduct.desc φ), V) := by
  refine subsingleton_of_forall_eq 0 fun s => ?_
  obtain ⟨t, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app (biproduct.desc φ) hV s
  have hle : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) ≤
      LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) := by
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hy
    have hz : φ i ≫ cokernel.π (biproduct.desc φ) = 0 := by
      rw [← biproduct.ι_desc φ i, Category.assoc, cokernel.condition, comp_zero]
    change (cokernel.π (biproduct.desc φ)).app V ((φ i).app V x) = 0
    rw [GlobalTheory.QCoh.app_app, hz]
    rfl
  have ht : t ∈ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) :=
    hle (h ▸ Submodule.mem_top)
  exact ht

/- English proof (translation)
Use `(Submodule.eq_top_iff').2 fun s => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `h s`. Rewrite using `[GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum F U t, map_sum]`. Use `Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ?_⟩)` and prove the remaining obligations. Use `⟨(biproduct.π F j).app U t, ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.QCoh.app_app (biproduct.ι F j), biproduct.ι_desc]`.
-/
theorem span_range_app_eq_top_of_surjective {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} (φ : ∀ i, F i ⟶ G) (U : X.Opens)
    (h : Function.Surjective ((biproduct.desc φ).app U)) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun s => ?_
  obtain ⟨t, rfl⟩ := h s
  rw [GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum F U t, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ?_⟩)
  refine ⟨(biproduct.π F j).app U t, ?_⟩
  rw [GlobalTheory.QCoh.app_app (biproduct.ι F j), biproduct.ι_desc]

/- English proof (translation)
Introduce `X ι _ F G hF hG φ hloc U`. Use `haveI := Fintype.ofFinite ι`. Use `haveI := hF`. Use `haveI := hG`. Use `haveI : (biproduct F).IsQuasicoherent := GroundTheory.Arith.SchemeCoh.isQuasicoherent_biproduct F`.

Use `choose W hxW hW using hloc`. Establish `hcov : TopologicalSpace.IsOpenCover (fun x : X => (W x : X.Opens))`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩`. Establish `hzero : IsZero (cokernel (biproduct.desc φ))` using `(GlobalTheory.QCoh.isZero_iff_affineCover (fun x : X => (W x : X.Opens)) hcov (fun x => (W x).2)).2 fun x => subsingleton_cokernel_desc_of_span φ (W x).2 (hW x)`.

Use `haveI : Epi (biproduct.desc φ) := Preadditive.epi_of_isZero_cokernel _ hzero`. Conclude with `span_range_app_eq_top_of_surjective φ U (GlobalTheory.QCoh.surjective_app_of_epi (biproduct.desc φ) U.2)`.
-/
theorem span_range_app_eq_top_of_local : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι]
    {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent →
    ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) →
    ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  intro X ι _ F G hF hG φ hloc U
  classical
  haveI := Fintype.ofFinite ι
  haveI := hF
  haveI := hG
  haveI : (biproduct F).IsQuasicoherent := GroundTheory.Arith.SchemeCoh.isQuasicoherent_biproduct F
  choose W hxW hW using hloc
  have hcov : TopologicalSpace.IsOpenCover (fun x : X => (W x : X.Opens)) := by
    refine eq_top_iff.2 fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  have hzero : IsZero (cokernel (biproduct.desc φ)) :=
    (GlobalTheory.QCoh.isZero_iff_affineCover (fun x : X => (W x : X.Opens)) hcov (fun x => (W x).2)).2
      fun x => subsingleton_cokernel_desc_of_span φ (W x).2 (hW x)
  haveI : Epi (biproduct.desc φ) := Preadditive.epi_of_isZero_cokernel _ hzero
  exact span_range_app_eq_top_of_surjective φ U
    (GlobalTheory.QCoh.surjective_app_of_epi (biproduct.desc φ) U.2)

end GlobalTheory.CompanionTheory.GE.UV
