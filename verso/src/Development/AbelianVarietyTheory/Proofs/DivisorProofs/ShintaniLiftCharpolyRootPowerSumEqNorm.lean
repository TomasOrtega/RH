import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Unfold `rootSum pullθ`. Establish `e1 : (P.map (algebraMap F F')).map (algebraMap F' (AlgebraicClosure F')) = (P.map (algebraMap F (AlgebraicClosure F))).map (ι : AlgebraicClosure F →+* AlgebraicClosure F')`. Rewrite using `[Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`. Use `congr 1`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[e1, (IsAlgClosed.splits _).roots_map, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem rootSum_map_pullθ {F F' : Type} [Field F] [Field F'] [Algebra F F']
    (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F[X]) :
    rootSum θ k (P.map (algebraMap F F')) = rootSum (pullθ ι θ) k P := by
  unfold rootSum pullθ
  have e1 : (P.map (algebraMap F F')).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map (ι : AlgebraicClosure F →+* AlgebraicClosure F') := by
    rw [Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    ext x
    simp
  rw [e1, (IsAlgClosed.splits _).roots_map, Multiset.map_map]
  rfl

/- English proof (translation)
Take `⟨c, rfl⟩` from `isConj_iff.1 h`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
theorem charpoly_of_isConj {K : Type} [Field K] {n : ℕ} {a b : GL (Fin n) K} (h : IsConj a b) :
    Matrix.charpoly (a : Matrix (Fin n) (Fin n) K) = Matrix.charpoly (b : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs ι θ k n δ`. Establish `hex : ∃ γ, IsNorm s δ γ` using `GlobalTheory.T.every_element_is_norm F F' s hs n δ`. Unfold `shLift`. Rewrite using `[dif_pos hex]`. Generalize the expression as in `hex.choose = γ, hex.choose_spec = hγ`.

Unfold `IsNorm at hγ`. Unfold `chG`. Rewrite using `[← charpoly_of_isConj hγ]`. Establish `hm : ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[hm, Matrix.charpoly_map, rootSum_map_pullθ]`.
-/
theorem shLift_chG_rootSum : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k n : ℕ) (δ : GL (Fin n) F'), shLift s (chG (rootSum (pullθ ι θ) k) n) δ = chG (rootSum θ k) n (nrm s δ) := by
  intro F F' _ _ _ _ s hs ι θ k n δ
  have hex : ∃ γ, IsNorm s δ γ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  unfold shLift
  rw [dif_pos hex]
  generalize hex.choose = γ, hex.choose_spec = hγ
  unfold IsNorm at hγ
  unfold chG
  rw [← charpoly_of_isConj hγ]
  have hm : ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F') := by
    ext i j; rfl
  rw [hm, Matrix.charpoly_map, rootSum_map_pullθ]

end GlobalTheory.Shin
