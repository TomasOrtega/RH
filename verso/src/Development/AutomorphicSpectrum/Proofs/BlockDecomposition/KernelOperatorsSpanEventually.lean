import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}}

def secMap {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secMap_apply {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (x : Γ(F, U)) :
    secMap φ U x = φ.app U x := rfl

/- English proof (translation)
Rewrite using `[secMap_apply, secMap_apply, secMap_apply, Scheme.Modules.Hom.comp_app]`. Both sides reduce to the same expression.
-/
theorem secMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (U : X.Opens) (x : Γ(F, U)) :
    secMap ψ U (secMap φ U x) = secMap (φ ≫ ψ) U x := by
  rw [secMap_apply, secMap_apply, secMap_apply, Scheme.Modules.Hom.comp_app]
  rfl

/- English proof (translation)
Use `haveI : SheafOfModules.IsQuasicoherent F := hF.1`. Use `And.intro (isQuasicoherent_biproduct _) fun U hU => ?_` and prove the remaining obligations. Use `haveI : Module.Finite Γ(X, U) Γ(F, U) := hF.2 U hU`. Set `L : (Fin k → Γ(F, U)) →ₗ[Γ(X, U)] Γ(⨁ fun _ : Fin k => F, U)` to `∑ j, (secMap (biproduct.ι (fun _ : Fin k => F) j) U).comp (LinearMap.proj (R := Γ(X, U)) j)`. Use `Module.Finite.of_surjective L fun m => ⟨fun j => secMap (biproduct.π (fun _ : Fin k => F) j) U m, ?_⟩` and prove the remaining obligations.

Use `Eq.trans ?_ (biproduct_app_eq_sum (fun _ : Fin k => F) U m).symm` and prove the remaining obligations. Simplify using `only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, secMap_apply]`.
-/
theorem isCoherent_copies {k : ℕ} {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent (⨁ fun _ : Fin k => F) := by
  haveI : SheafOfModules.IsQuasicoherent F := hF.1
  refine And.intro (isQuasicoherent_biproduct _) fun U hU => ?_
  haveI : Module.Finite Γ(X, U) Γ(F, U) := hF.2 U hU
  let L : (Fin k → Γ(F, U)) →ₗ[Γ(X, U)] Γ(⨁ fun _ : Fin k => F, U) :=
    ∑ j, (secMap (biproduct.ι (fun _ : Fin k => F) j) U).comp (LinearMap.proj (R := Γ(X, U)) j)
  refine Module.Finite.of_surjective L fun m =>
    ⟨fun j => secMap (biproduct.π (fun _ : Fin k => F) j) U m, ?_⟩
  refine Eq.trans ?_ (biproduct_app_eq_sum (fun _ : Fin k => F) U m).symm
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    secMap_apply]

variable {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}

/- English proof (translation)
Establish `key : ∀ c : Fin k, ⊤ ≤ (⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens))).comap (secMap (biproduct.ι (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens))`. Introduce `c`. Rewrite using `[← h.gen (d + e) (Nat.le_add_right d e) U]`. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Take `⟨i, x, rfl⟩` from `Set.mem_iUnion.mp hy`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr ⟨secMap (biproduct.ι (fun _ : Fin k => M (d + e)) c) (U : X.Opens) x, ?_⟩)` and prove the remaining obligations. Rewrite using `[secMap_comp, ← secMap_apply (T i (d + e)), secMap_comp]`. Rewrite using `[show biproduct.ι (fun _ : Fin k => M (d + e)) c ≫ diagOp T d i e = T i (d + e) ≫ biproduct.ι (fun _ : Fin k => M (d + e + 1)) c by`. Unfold `diagOp`.

Conclude with `biproduct.ι_map _ _]`. Rewrite using `[eq_top_iff]`. Introduce `m _`. Rewrite using `[biproduct_app_eq_sum (fun _ : Fin k => M (d + e + 1)) (U : X.Opens) m]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations.

Establish `hc` using `Submodule.mem_comap.mp (key c (Submodule.mem_top (x := secMap (biproduct.π (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens) m)))`. Rewrite `hc` using `[secMap_apply, secMap_apply]`. Then use the resulting hypothesis.
-/
theorem iSup_range_diagOp (h : OpSeq k M T d) (U : X.affineOpens) (e : ℕ) :
    ⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens)) = ⊤ := by
  have key : ∀ c : Fin k, ⊤ ≤ (⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens))).comap
      (secMap (biproduct.ι (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens)) := by
    intro c
    rw [← h.gen (d + e) (Nat.le_add_right d e) U]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr
      ⟨secMap (biproduct.ι (fun _ : Fin k => M (d + e)) c) (U : X.Opens) x, ?_⟩)
    rw [secMap_comp, ← secMap_apply (T i (d + e)), secMap_comp]
    rw [show biproduct.ι (fun _ : Fin k => M (d + e)) c ≫ diagOp T d i e =
        T i (d + e) ≫ biproduct.ι (fun _ : Fin k => M (d + e + 1)) c by
          unfold diagOp
          exact biproduct.ι_map _ _]
  rw [eq_top_iff]
  intro m _
  rw [biproduct_app_eq_sum (fun _ : Fin k => M (d + e + 1)) (U : X.Opens) m]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hc := Submodule.mem_comap.mp (key c (Submodule.mem_top
    (x := secMap (biproduct.π (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens) m)))
  rwa [secMap_apply, secMap_apply] at hc

/- English proof (translation)
Introduce `hGN X _ k M T d h U`. Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U`. Establish `hfin : ∀ e, Module.Finite Γ(X, U) Γ(sumN M k d e, U)` using `fun e => (isCoherent_copies (k := k) (h.coherent (d + e))).2 U U.2`. Take `⟨d', hd'⟩` from `hGN Γ(X, U) k (fun e => Γ(sumN M k d e, U)) (fun j e => secMap (diagOp T d j e) (U : X.Opens)) (fun i j e x => by`. Rewrite using `[secMap_comp, secMap_comp, diagOp_comm T h.comm d i j e])`.

Use `0 (fun e _ => iSup_range_diagOp h U e)`. Use the proof step `(fun e => LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens)))`. Use the proof step `(fun i e => by`. Introduce `y hy`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hy`.

Take `⟨x, rfl⟩` from `LinearMap.mem_range.mp hz`. Use `LinearMap.mem_range.mpr ⟨secMap (kerOp T h.comm d i e) (U : X.Opens) x, ?_⟩` and prove the remaining obligations. Rewrite using `[secMap_comp, secMap_comp, kerOp_ι])`. Use `⟨d', fun e he => ?_⟩` and prove the remaining obligations. Establish `hd'' : ⨆ i, Submodule.map (secMap (diagOp T d i e) (U : X.Opens)) (LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens))) = LinearMap.range (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens))` using `hd' e he`.

Establish `hinj : Function.Injective (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens))` using `GlobalTheory.QCoh.app_injective_of_mono _ _`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Establish `hS : Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⨆ i, LinearMap.range (secMap (kerOp T h.comm d i e) (U : X.Opens))`. Rewrite using `[Submodule.iSup_eq_span]`. Simplify using `only [LinearMap.coe_range]`.

Both sides reduce to the same expression. Rewrite using `[hS, Submodule.map_iSup, Submodule.map_top, ← hd'']`. Use `iSup_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.range_comp, ← LinearMap.range_comp]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[secMap_comp, secMap_comp, kerOp_ι]`.
-/
theorem kerSeq_gen_bounded : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  intro hGN X _ k M T d h U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hfin : ∀ e, Module.Finite Γ(X, U) Γ(sumN M k d e, U) := fun e =>
    (isCoherent_copies (k := k) (h.coherent (d + e))).2 U U.2
  obtain ⟨d', hd'⟩ := hGN Γ(X, U) k (fun e => Γ(sumN M k d e, U))
    (fun j e => secMap (diagOp T d j e) (U : X.Opens))
    (fun i j e x => by
      rw [secMap_comp, secMap_comp, diagOp_comm T h.comm d i j e])
    0 (fun e _ => iSup_range_diagOp h U e)
    (fun e => LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens)))
    (fun i e => by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨secMap (kerOp T h.comm d i e) (U : X.Opens) x, ?_⟩
      rw [secMap_comp, secMap_comp, kerOp_ι])
  refine ⟨d', fun e he => ?_⟩
  have hd'' : ⨆ i, Submodule.map (secMap (diagOp T d i e) (U : X.Opens))
      (LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens))) =
      LinearMap.range (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) := hd' e he
  have hinj : Function.Injective (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) :=
    GlobalTheory.QCoh.app_injective_of_mono _ _
  apply Submodule.map_injective_of_injective hinj
  have hS : Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) =
      ⨆ i, LinearMap.range (secMap (kerOp T h.comm d i e) (U : X.Opens)) := by
    rw [Submodule.iSup_eq_span]
    simp only [LinearMap.coe_range]
    rfl
  rw [hS, Submodule.map_iSup, Submodule.map_top, ← hd'']
  refine iSup_congr fun i => ?_
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply]
  rw [secMap_comp, secMap_comp, kerOp_ι]

end GlobalTheory.CompanionTheory.GE.KerSeq
