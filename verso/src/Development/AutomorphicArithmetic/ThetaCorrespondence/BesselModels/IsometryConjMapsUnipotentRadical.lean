import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.UnipRadConj

/- English proof (translation)
Introduce `n r J G Q Qi e e' h1 h2 hg he u hu`. Take `⟨hu1, hu2, hu3⟩` from `hu`. Establish `hu1' : uᴴ * G * u = G` using `hu1`. Establish `hw1 : Q * u * Qi - 1 = Q * (u - 1) * Qi`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]`.

Establish `hcol : ∀ i : Fin r, (fun k => e k i) = Q *ᵥ fun k => e' k i`. Introduce `i`. Rewrite using `[← he]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (Q * u * Qi)ᴴ * J * (Q * u * Qi) = J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Qiᴴ * G * Qi := by rw [hg, hu1']`. Use `_ = (Q * Qi)ᴴ * J * (Q * Qi) := by`. Rewrite using `[← hg, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [h1]; simp`.

Introduce `i`. Take `⟨a, ha0, ha⟩` from `hu2 i`. Use `⟨a, ha0, ?_⟩` and prove the remaining obligations. Establish `hq : Q * (u - 1) * Qi * Q = Q * (u - 1)` using `by rw [Matrix.mul_assoc, h2, Matrix.mul_one]`. Rewrite using `[hw1, hcol i, Matrix.mulVec_mulVec, hq, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]`.

Introduce `x hx`. Establish `hy : (e'ᴴ * G) *ᵥ (Qi *ᵥ x) = 0`. Establish `hm : e'ᴴ * (Qᴴ * J * Q) * Qi = eᴴ * J`. Rewrite using `[← he, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[h1, Matrix.mul_one]`. Rewrite using `[Matrix.mulVec_mulVec, ← hg, hm]`. Conclude with `hx`. Take `⟨a, ha⟩` from `hu3 _ hy`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]`.
-/
theorem conj_mem_unipRad : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e)
    {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  intro n r J G Q Qi e e' h1 h2 hg he u hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hu1' : uᴴ * G * u = G := hu1
  have hw1 : Q * u * Qi - 1 = Q * (u - 1) * Qi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hcol : ∀ i : Fin r, (fun k => e k i) = Q *ᵥ fun k => e' k i := by
    intro i
    rw [← he]
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · show (Q * u * Qi)ᴴ * J * (Q * u * Qi) = J
    calc (Q * u * Qi)ᴴ * J * (Q * u * Qi) = Qiᴴ * (uᴴ * (Qᴴ * J * Q) * u) * Qi := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Qiᴴ * G * Qi := by rw [hg, hu1']
      _ = (Q * Qi)ᴴ * J * (Q * Qi) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [h1]; simp
  · intro i
    obtain ⟨a, ha0, ha⟩ := hu2 i
    refine ⟨a, ha0, ?_⟩
    have hq : Q * (u - 1) * Qi * Q = Q * (u - 1) := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [hw1, hcol i, Matrix.mulVec_mulVec, hq, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]
  · intro x hx
    have hy : (e'ᴴ * G) *ᵥ (Qi *ᵥ x) = 0 := by
      have hm : e'ᴴ * (Qᴴ * J * Q) * Qi = eᴴ * J := by
        rw [← he, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rw [h1, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, ← hg, hm]
      exact hx
    obtain ⟨a, ha⟩ := hu3 _ hy
    refine ⟨a, ?_⟩
    rw [hw1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]

end UpperTheory.Lit.Bur.UnipRadConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | exact UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | (intros; apply UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  first | exact @UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | exact UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | (intros; apply UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad <;> assumption)
