import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

/- English proof (translation)
Set `f : (A ⊗[F] E) →+* (A' ⊗[F] E)` to `(Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom`. Establish `hf : ∀ e : E, f (inclR (F` using `F) A e) = inclR (F := F) A' e := fun e => by`. Simplify using `[f, inclR]`. Establish `hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Z.map (inclR (F` using `F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by`. Use extensionality with `i j`.

Simplify using `[hf]`. Establish `hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)), (P * Q).map f = P.map f * Q.map f` using `fun P Q => Matrix.map_mul`. Establish `hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f` using `fun P Q => Matrix.map_add f (map_add f) P Q`. Establish `hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f` using `fun P Q => Matrix.map_sub f (map_sub f) P Q`. Establish `hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1` using `Matrix.map_one f (map_zero f) (map_one f)`.

Establish `hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i))` using `fun d => by`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [diagonal, h]`. Express the relevant statement in the definitionally equal form `leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f`. Apply the tactic sequence `have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i := fun _ _ => rfl`.

Simplify using `only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]`.
-/
theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
