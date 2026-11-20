import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Uniform

/- English proof (translation)
Establish `hι : ∀ i (z : Γ(A, U)), (biproduct.desc T).app U ((biproduct.ι (fun _ : Fin k => A) i).app U z) = (T i).app U z`. Introduce `i z`. Rewrite using `[← GlobalTheory.QCoh.appLinear_apply, ← GlobalTheory.QCoh.appLinear_apply, ← LinearMap.comp_apply, ← GlobalTheory.QCoh.appLinear_comp, biproduct.ι_desc, GlobalTheory.QCoh.appLinear_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`.

Establish `hy : y ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U))` using `h ▸ Submodule.mem_top`. Establish `hle : Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) ≤ LinearMap.range (GlobalTheory.QCoh.appLinear (biproduct.desc T) U)`. Rewrite using `[Submodule.span_le]`. Introduce `w hw`. Take `⟨i, z, rfl⟩` from `Set.mem_iUnion.1 hw`.

Conclude with `⟨(biproduct.ι (fun _ : Fin k => A) i).app U z, by rw [GlobalTheory.QCoh.appLinear_apply, hι]⟩`. Take `⟨x, hx⟩` from `hle hy`. Conclude with `⟨x, hx⟩`. Introduce `h`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Take `⟨x, rfl⟩` from `h y`. Rewrite using `[biproduct_app_eq_sum (fun _ : Fin k => A) U x, ← GlobalTheory.QCoh.appLinear_apply, map_sum]`. Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (biproduct.π (fun _ : Fin k => A) i).app U x, ?_⟩)` and prove the remaining obligations. Rewrite using `[GlobalTheory.QCoh.appLinear_apply, hι]`.
-/
theorem span_range_eq_top_iff_surjective {X : Scheme.{0}} {k : ℕ} {A B : X.Modules}
    (T : Fin k → (A ⟶ B)) (U : X.Opens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) = ⊤ ↔
      Function.Surjective ((biproduct.desc T).app U) := by
  have hι : ∀ i (z : Γ(A, U)),
      (biproduct.desc T).app U ((biproduct.ι (fun _ : Fin k => A) i).app U z) = (T i).app U z := by
    intro i z
    rw [← GlobalTheory.QCoh.appLinear_apply, ← GlobalTheory.QCoh.appLinear_apply, ← LinearMap.comp_apply,
      ← GlobalTheory.QCoh.appLinear_comp, biproduct.ι_desc, GlobalTheory.QCoh.appLinear_apply]
  constructor
  · intro h y
    have hy : y ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) := h ▸ Submodule.mem_top
    have hle : Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) ≤
        LinearMap.range (GlobalTheory.QCoh.appLinear (biproduct.desc T) U) := by
      rw [Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact ⟨(biproduct.ι (fun _ : Fin k => A) i).app U z, by rw [GlobalTheory.QCoh.appLinear_apply, hι]⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := h y
    rw [biproduct_app_eq_sum (fun _ : Fin k => A) U x, ← GlobalTheory.QCoh.appLinear_apply, map_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      (Set.mem_iUnion.2 ⟨i, (biproduct.π (fun _ : Fin k => A) i).app U x, ?_⟩)
    rw [GlobalTheory.QCoh.appLinear_apply, hι]

/- English proof (translation)
Introduce `X _ k K T hq hgen`. Take `⟨ι, _, 𝒰, haff, hcov⟩` from `GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X) (W := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)`. Use `choose dU hdU using fun i => hgen ⟨𝒰 i, haff i⟩`. Use `⟨Finset.univ.sup dU, fun e he U => ?_⟩` and prove the remaining obligations. Use `haveI := hq e`.

Use `haveI := hq (e + 1)`. Establish `hepi : Epi (biproduct.desc fun i => T i e)`. Rewrite using `[GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov.symm haff]`. Introduce `i`. Conclude with `(span_range_eq_top_iff_surjective (fun j => T j e) (𝒰 i)).1 (hdU i e ((Finset.le_sup (f := dU) (Finset.mem_univ i)).trans he))`.

Conclude with `(span_range_eq_top_iff_surjective (fun j => T j e) U).2 (GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen _ U.2)`.
-/
theorem span_range_eq_top_uniform : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ}
    {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) →
    (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e →
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens,
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  intro X _ k K T hq hgen
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X)
    (W := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  choose dU hdU using fun i => hgen ⟨𝒰 i, haff i⟩
  refine ⟨Finset.univ.sup dU, fun e he U => ?_⟩
  haveI := hq e
  haveI := hq (e + 1)
  have hepi : Epi (biproduct.desc fun i => T i e) := by
    rw [GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov.symm haff]
    intro i
    exact (span_range_eq_top_iff_surjective (fun j => T j e) (𝒰 i)).1
      (hdU i e ((Finset.le_sup (f := dU) (Finset.mem_univ i)).trans he))
  exact (span_range_eq_top_iff_surjective (fun j => T j e) U).2
    (GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen _ U.2)

end GlobalTheory.CompanionTheory.GE.Uniform
