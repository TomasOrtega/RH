import Mathlib
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.PlacesOverU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealRepTmul

open NumberField Matrix GlobalTheory.UPel.HT
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

/- English proof (translation)
Use `letI : Algebra F ℂ := σ.toAlgebra`. Establish `hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a` using `fun a => by`. Rewrite using `[hf, Matrix.algebraMap_eq_diagonal]`. Both sides reduce to the same expression. Set `g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ` to `{ f with commutes' := hg }`.

Set `L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)`. Establish `hn : 0 < n`. Use `Module.finrank_pos (R := F) (M := B)` as an intermediate fact. Rewrite `this` using `[hdim]`. Conclude with `Nat.pos_of_ne_zero fun h => by simp [h] at this`.

Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Establish `hinj : Function.Injective L` using `(IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)`. Establish `hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]`. Simplify using `[sq]`.

Establish `hsurj : Function.Surjective L.toLinearMap` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj`. Use `eq_top_iff.2 fun m _ => ?_` and prove the remaining obligations. Use `clear ‹m ∈ ⊤›`. Take `⟨x, rfl⟩` from `hsurj m`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c b`. Establish `: L.toLinearMap (c ⊗ₜ b) = c • f b` using `by dsimp only [L]`. Rewrite using `[AlgHom.toLinearMap_apply]`. Use `erw [Algebra.TensorProduct.lift_tmul]`.

Rewrite using `[Algebra.ofId_apply, Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [IsCMField K] [Field F] [NumberField F] [IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
