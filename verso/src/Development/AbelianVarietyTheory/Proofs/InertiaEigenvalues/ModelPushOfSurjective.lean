import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

/- English proof (translation)
Take `⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩` from `hN`. Establish `hC : F.Obj C` using `M.base_obj C Nb hb`. Establish `h1 : F.Obj A₁` using `F.obj_sub A₁ C j hj hji hC`. Establish `hA : F.Obj A` using `F.obj_quot A₁ A q hq hqs h1`. Establish `hB : F.Obj B` using `F.obj_quot A B p hp hs hA`.

Use `⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]`. Use function extensionality and compare the values at `i`. Simplify using `only [DFun.push]`. Rewrite using `[F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]`.

Both sides reduce to the same expression.
-/
theorem ModTh.model_push_of_surjective {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) (hp : IsHom A B p)
    (hs : Function.Surjective p) (hN : M.Model A N) : M.Model B (F.push A B p N) := by
  obtain ⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩ := hN
  have hC : F.Obj C := M.base_obj C Nb hb
  have h1 : F.Obj A₁ := F.obj_sub A₁ C j hj hji hC
  have hA : F.Obj A := F.obj_quot A₁ A q hq hqs h1
  have hB : F.Obj B := F.obj_quot A B p hp hs hA
  refine ⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]
  · funext i
    simp only [DFun.push]
    rw [F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]
    rfl

end GlobalTheory.Models
