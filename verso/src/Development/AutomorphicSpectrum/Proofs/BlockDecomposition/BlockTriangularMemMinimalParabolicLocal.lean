import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extH tensNU tensNU_tmul)

namespace GlobalTheory.CompanionTheory.KFin

section Step

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
  [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_mul, map_add, hx, hy]`. Consider the case `tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem tensNU_mul_inclR (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * inclR (F := F) R' e = tensNU j hj (u * inclR (F := F) R e) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  | tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Use extensionality with `r s`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]`.
-/
theorem map_tensNU_mul_inclR {a b c : Type} [Fintype b] (A : Matrix a b (R ⊗[F] E)) (X : Matrix b c E) :
    A.map (tensNU j hj) * X.map (inclR (F := F) R') = (A * X.map (inclR (F := F) R)).map (tensNU j hj) := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]

/- English proof (translation)
Use extensionality with `r s`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _), tensNU_mul_inclR, map_sum]`.
-/
theorem inclR_mul_map_tensNU {a b c : Type} [Fintype b] (X : Matrix a b E) (A : Matrix b c (R ⊗[F] E)) :
    X.map (inclR (F := F) R') * A.map (tensNU j hj) = (X.map (inclR (F := F) R) * A).map (tensNU j hj) := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _),
    tensNU_mul_inclR, map_sum]

/- English proof (translation)
Use extensionality with `r s`. Rewrite using `[GlobalTheory.AutFunCompare.mat_extH]`. Distinguish the cases in `h : r = s`. Substitute `h` using the available equality. Simplify using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.one_apply, h]`.
-/
theorem mat_extH_eq_add (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J) :
    (HA.mat R' σ J (extH σ J j hj g)).1 = 1 + ((HA.mat R σ J g).1 - 1).map (tensNU j hj) := by
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp [map_sub]
    ring
  · simp [Matrix.one_apply, h]

/- English proof (translation)
Use `⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `hne : a ≠ b` using `fun e => by subst e; exact lt_irrefl _ hab`. Establish `h0 : B a b = 0` using `hB hab`. Simplify using `[Matrix.one_apply, hne, h0]`.

Rewrite using `[mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR, inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem extH_stab (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J)
    (X : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (hB : B.BlockTriangular id)
    (h : (HA.mat R σ J g).1 * X.map (inclR (F := F) R) = X.map (inclR (F := F) R) * B) :
    ∃ B' : Matrix (Fin r) (Fin r) (R' ⊗[F] E), B'.BlockTriangular id ∧
      (HA.mat R' σ J (extH σ J j hj g)).1 * X.map (inclR (F := F) R') = X.map (inclR (F := F) R') * B' := by
  refine ⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩
  · intro a b hab
    have hne : a ≠ b := fun e => by subst e; exact lt_irrefl _ hab
    have h0 : B a b = 0 := hB hab
    simp [Matrix.one_apply, hne, h0]
  · rw [mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR,
      inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]

end Step

/- English proof (translation)
Take `⟨B₁, hB₁, h₁⟩` from `extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h`. Take `⟨B₂, hB₂, h₂⟩` from `extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁`. Conclude with `⟨B₂, hB₂, h₂⟩`.
-/
theorem emb_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E))
    (hB : B.BlockTriangular id)
    (h : (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B) :
    emb σ J v p ∈ minPar σ J X := by
  obtain ⟨B₁, hB₁, h₁⟩ := extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h
  obtain ⟨B₂, hB₂, h₂⟩ := extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁
  exact ⟨B₂, hB₂, h₂⟩

end GlobalTheory.CompanionTheory.KFin

end
