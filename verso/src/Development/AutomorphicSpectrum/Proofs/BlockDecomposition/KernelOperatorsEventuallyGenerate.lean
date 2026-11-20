import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}

variable (M T) in

def kerι (e : ℕ) : kerSeq M T e ⟶ M e := kernel.ι (T (Fin.last k) e)

/- English proof (translation)
The claim follows from `kernel.condition _`.
-/
theorem kerι_comp (e : ℕ) : kerι M T e ≫ T (Fin.last k) e = 0 :=
  kernel.condition _

/- English proof (translation)
Simplify using `[kerOps, kerι, kerSeq, kernel.map]`.
-/
theorem kerOps_comp_kerι (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k)
    (e : ℕ) : kerOps hc i e ≫ kerι M T (e + 1) = kerι M T e ≫ T i.castSucc e := by
  simp [kerOps, kerι, kerSeq, kernel.map]

open GlobalTheory.CompanionTheory.GE.KerSeq in

/- English proof (translation)
Introduce `hG X _ k M T d hM U`. Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U`. Use `haveI : ∀ e, Module.Finite Γ(X, U) Γ(M e, (U : X.Opens)) := fun e => (hM.coherent e).2 U U.2`. Establish `hcomm : ∀ (i j : Fin (k + 1)) (e : ℕ) (x : Γ(M e, (U : X.Opens))), secMap (T j (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) = secMap (T i (e + 1)) (U : X.Opens) (secMap (T j e) (U : X.Opens) x)`. Introduce `i j e x`.

Simplify using `only [secMap_comp]`. Rewrite using `[hM.comm i j e]`. Take `⟨d', hd'⟩` from `hG Γ(X, U) (k + 1) (fun e => Γ(M e, (U : X.Opens))) (fun i e => secMap (T i e) (U : X.Opens)) hcomm d (fun e he => by`. Establish `h` using `hM.gen e he U`. Rewrite using `[eq_top_iff, ← h, Submodule.span_le]`.

Introduce `w hw`. Take `⟨i, z, rfl⟩` from `Set.mem_iUnion.1 hw`. Conclude with `Submodule.mem_iSup_of_mem i ⟨z, rfl⟩)`. Use the proof step `(fun e => LinearMap.ker (secMap (T (Fin.last k) e) (U : X.Opens)))`. Use the proof step `(fun i e => by`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : secMap (T (Fin.last k) e) (U : X.Opens) x = 0` using `hx`. Express the relevant statement in the definitionally equal form `secMap (T (Fin.last k) (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) = 0`. Rewrite using `[hcomm i (Fin.last k) e x, hx', map_zero])`. Use `⟨d', fun e he => ?_⟩` and prove the remaining obligations.

Establish `hι : ∀ e, Function.Injective (secMap (kerι M T e) (U : X.Opens))` using `fun e => kernel_ι_app_injective _ _`. Establish `hιo : ∀ (i : Fin k) e (y : Γ(kerSeq M T e, (U : X.Opens))), secMap (kerι M T (e + 1)) (U : X.Opens) (secMap (kerOps hM.comm i e) (U : X.Opens) y) = secMap (T i.castSucc e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y)`. Introduce `i e y`. Rewrite using `[secMap_comp, secMap_comp, kerOps_comp_kerι]`. Use `set S : Submodule Γ(X, U) Γ(kerSeq M T (e + 1), (U : X.Opens)) := Submodule.span Γ(X, U) (⋃ i, Set.range ((kerOps hM.comm i e).app U)) with hS`.

Establish `hle : LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) ≤ S.map (secMap (kerι M T (e + 1)) (U : X.Opens))`. Rewrite using `[← hd' e he]`. Use `iSup_le fun i => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, hy⟩ : ∃ y : Γ(kerSeq M T e, (U : X.Opens)), secMap (kerι M T e) (U : X.Opens) y = x` from `kernel_ι_app_exact (T (Fin.last k) e) (U : X.Opens) x hx`.

Substitute `hy` using the available equality. Express the relevant statement in the definitionally equal form `secMap (T i e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y) ∈ _`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Rewrite using `[show secMap (T (Fin.last k) e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y) = 0 from hx]`.

Conclude with `Submodule.zero_mem _`. Consider the case `cast i`. Use `⟨secMap (kerOps hM.comm i e) (U : X.Opens) y, ?_, hιo i e y⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span (Set.mem_iUnion.2 ⟨i, y, rfl⟩)`. Rewrite using `[eq_top_iff]`.

Introduce `z _`. Establish `hz : secMap (kerι M T (e + 1)) (U : X.Opens) z ∈ LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens))`. Rewrite using `[LinearMap.mem_ker, secMap_comp, kerι_comp]`. Simplify using `[secMap_apply, Scheme.Modules.Hom.zero_app]`. Take `⟨w, hw, hwz⟩` from `hle hz`.

Rewrite using `[← hι _ hwz]` and apply the resulting hypothesis.
-/
theorem kerOps_gen_bounded : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  intro hG X _ k M T d hM U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  haveI : ∀ e, Module.Finite Γ(X, U) Γ(M e, (U : X.Opens)) := fun e => (hM.coherent e).2 U U.2
  have hcomm : ∀ (i j : Fin (k + 1)) (e : ℕ) (x : Γ(M e, (U : X.Opens))),
      secMap (T j (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) =
        secMap (T i (e + 1)) (U : X.Opens) (secMap (T j e) (U : X.Opens) x) := by
    intro i j e x
    simp only [secMap_comp]
    rw [hM.comm i j e]
  obtain ⟨d', hd'⟩ := hG Γ(X, U) (k + 1) (fun e => Γ(M e, (U : X.Opens)))
    (fun i e => secMap (T i e) (U : X.Opens)) hcomm d
    (fun e he => by
      have h := hM.gen e he U
      rw [eq_top_iff, ← h, Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact Submodule.mem_iSup_of_mem i ⟨z, rfl⟩)
    (fun e => LinearMap.ker (secMap (T (Fin.last k) e) (U : X.Opens)))
    (fun i e => by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : secMap (T (Fin.last k) e) (U : X.Opens) x = 0 := hx
      change secMap (T (Fin.last k) (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) = 0
      rw [hcomm i (Fin.last k) e x, hx', map_zero])
  refine ⟨d', fun e he => ?_⟩

  have hι : ∀ e, Function.Injective (secMap (kerι M T e) (U : X.Opens)) :=
    fun e => kernel_ι_app_injective _ _
  have hιo : ∀ (i : Fin k) e (y : Γ(kerSeq M T e, (U : X.Opens))),
      secMap (kerι M T (e + 1)) (U : X.Opens)
          (secMap (kerOps hM.comm i e) (U : X.Opens) y) =
        secMap (T i.castSucc e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) := by
    intro i e y
    rw [secMap_comp, secMap_comp, kerOps_comp_kerι]
  set S : Submodule Γ(X, U) Γ(kerSeq M T (e + 1), (U : X.Opens)) :=
    Submodule.span Γ(X, U) (⋃ i, Set.range ((kerOps hM.comm i e).app U)) with hS

  have hle : LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) ≤
      S.map (secMap (kerι M T (e + 1)) (U : X.Opens)) := by
    rw [← hd' e he]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : Γ(kerSeq M T e, (U : X.Opens)), secMap (kerι M T e) (U : X.Opens) y = x :=
      kernel_ι_app_exact (T (Fin.last k) e) (U : X.Opens) x hx
    subst hy
    change secMap (T i e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y) ∈ _
    induction i using Fin.lastCases with
    | last =>
      rw [show secMap (T (Fin.last k) e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) = 0 from hx]
      exact Submodule.zero_mem _
    | cast i =>
      refine ⟨secMap (kerOps hM.comm i e) (U : X.Opens) y, ?_, hιo i e y⟩
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, y, rfl⟩)
  rw [eq_top_iff]
  intro z _
  have hz : secMap (kerι M T (e + 1)) (U : X.Opens) z ∈
      LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) := by
    rw [LinearMap.mem_ker, secMap_comp, kerι_comp]
    simp [secMap_apply, Scheme.Modules.Hom.zero_app]
  obtain ⟨w, hw, hwz⟩ := hle hz
  rwa [← hι _ hwz]

end GlobalTheory.CompanionTheory.GE.UV
