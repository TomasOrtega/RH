import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha`. Take `⟨h1, h2, h3⟩` from `ha`. Establish `hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0`. Rewrite using `[← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]`. Establish `hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1`.

Rewrite using `[← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1`. Rewrite using `[← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0`. Rewrite using `[← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]`.

Use `set A := (matHom _ σ J a).1 with hAdef`. Use `set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs`. Use `set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs`. Use `set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP`. Establish `hXP : Xs * P = 0`.

Rewrite using `[hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]`. Establish `hYP : Ys * P = 0`. Rewrite using `[hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]`. Establish `hAP : A * P = P`. Use extensionality with `i j`.

Establish `hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ`. Rewrite using `[Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `k _`.

Express the relevant statement in the definitionally equal form `(Xs *ᵥ fun k => P k j) k = 0`. Rewrite using `[show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]`. Both sides reduce to the same expression. Simplify using `only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `k _`.

Express the relevant statement in the definitionally equal form `(Ys *ᵥ fun k => P k j) k = 0`. Rewrite using `[show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]`. Both sides reduce to the same expression. Use `congrFun (h3 _ hz) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Establish `hsum : P + adMat F X * Ys + adMat F Y * Xs = 1` using `by rw [hP]; abel`. Establish `hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]`. Establish `hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1` using `fun f => by`.

Rewrite using `[← diagonal_one, diagonal_sub]`. Rewrite using `[hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]`. Normalize the expressions using the abelian group laws.
-/
theorem mat_eq_of_isIdTorusElt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha
  obtain ⟨h1, h2, h3⟩ := ha
  have hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
    rw [← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  set A := (matHom _ σ J a).1 with hAdef
  set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs
  set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs
  set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP
  have hXP : Xs * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hYP : Ys * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hAP : A * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Xs *ᵥ fun k => P k j) k = 0
        rw [show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]; rfl
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Ys *ᵥ fun k => P k j) k = 0
        rw [show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]; rfl
    have := congrFun (h3 _ hz) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hsum : P + adMat F X * Ys + adMat F Y * Xs = 1 := by rw [hP]; abel
  have hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs := by
    calc A = A * (P + adMat F X * Ys + adMat F Y * Xs) := by rw [hsum, Matrix.mul_one]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]
  have hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1 := fun f => by
    rw [← diagonal_one, diagonal_sub]
  rw [hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]
  abel

end GlobalTheory.IdTorus
