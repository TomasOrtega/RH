import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Set `B` to `Algebra.TensorProduct.basis K b`. Establish `hB0 : B 0 = 1` using `by simp [B, h0, Algebra.TensorProduct.one_def]`.

Establish `hB1 : B 1 * B 1 = algebraMap F K d • (1 : K ⊗[F] E)`. Simplify using `only [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1, mul_one, algebraMap_smul]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]`. Use `⟨⟨0, 1, ?_⟩, mul_comm, fun {x} hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hB0]`.

Conclude with `(B.ne_zero 0).symm`. Establish `hs` using `B.sum_repr x`. Rewrite `hs` using `[Fin.sum_univ_two, hB0]`. Use `set s := B.repr x 0`. Use `set t := B.repr x 1`.

Establish `hn : s * s - algebraMap F K d * (t * t) ≠ 0`. Introduce `hn`. Distinguish the cases in `ht : t = 0`. Establish `hs0 : s = 0` using `by simpa [ht] using hn`. Conclude with `hx (by rw [← hs, hs0, ht]; simp)`.

Use `hc (s / t) ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `hn`. Use `⟨(s * s - algebraMap F K d * (t * t))⁻¹ • (s • (1 : K ⊗[F] E) - t • B 1), ?_⟩` and prove the remaining obligations. Establish `: x * (s • (1 : K ⊗[F] E) - t • B 1) = (s * s - algebraMap F K d * (t * t)) • (1 : K ⊗[F] E)`.

Rewrite using `[← hs]`. Simplify using `only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hB1, one_mul, mul_one]`. Use `module`. Rewrite using `[mul_smul_comm, this, smul_smul, inv_mul_cancel₀ hn, one_smul]`.
-/
theorem exists_sq_of_not_isField_tensor {F E K : Type} [Field F] [CommRing E] [Algebra F E]
    [Field K] [Algebra F K] (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1)
    (h1 : b 1 * b 1 = algebraMap F E d) (h : ¬ IsField (K ⊗[F] E)) :
    ∃ c : K, c * c = algebraMap F K d := by
  by_contra hc
  push_neg at hc
  apply h
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = 1 := by simp [B, h0, Algebra.TensorProduct.one_def]
  have hB1 : B 1 * B 1 = algebraMap F K d • (1 : K ⊗[F] E) := by
    simp only [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1,
      mul_one, algebraMap_smul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
  refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {x} hx => ?_⟩
  · rw [← hB0]; exact (B.ne_zero 0).symm
  · have hs := B.sum_repr x
    rw [Fin.sum_univ_two, hB0] at hs
    set s := B.repr x 0
    set t := B.repr x 1
    have hn : s * s - algebraMap F K d * (t * t) ≠ 0 := by
      intro hn
      by_cases ht : t = 0
      · have hs0 : s = 0 := by simpa [ht] using hn
        exact hx (by rw [← hs, hs0, ht]; simp)
      · refine hc (s / t) ?_
        field_simp
        linear_combination hn
    refine ⟨(s * s - algebraMap F K d * (t * t))⁻¹ • (s • (1 : K ⊗[F] E) - t • B 1), ?_⟩
    have : x * (s • (1 : K ⊗[F] E) - t • B 1) =
        (s * s - algebraMap F K d * (t * t)) • (1 : K ⊗[F] E) := by
      rw [← hs]
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hB1, one_mul, mul_one]
      module
    rw [mul_smul_comm, this, smul_smul, inv_mul_cancel₀ hn, one_smul]

/- English proof (translation)
Introduce `F E _ _ _ _ σ hσ P _ _ k K _ _ ⟨e⟩`. Take `⟨b, d, h0, hb, hd, h1⟩` from `quad_exists_basis hσ`. Establish `hc : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∃ c : K i, c * c * algebraMap F _ d = 1`. Introduce `i`. Take `⟨c, hc⟩` from `exists_sq_of_not_isField_tensor b d h0 h1 i.2`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hd ((algebraMap F (K i)).injective (by simpa using hc.symm))`. Conclude with `⟨c⁻¹, by rw [← hc]; field_simp⟩`. Use `choose c hc using hc`.

Set `u : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P` to `fun i => e.symm (Pi.single i.1 1)`. Set `v : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P` to `fun i => e.symm (Pi.single i.1 (c i))`. Establish `same : ∀ (i : Fin k) (x y : K i), e.symm (Pi.single i x) * e.symm (Pi.single i y) = e.symm (Pi.single i (x * y))` using `fun i x y => by rw [← map_mul, Pi.single_mul]`. Establish `diff : ∀ (i j : Fin k) (x : K i) (y : K j), i ≠ j → e.symm (Pi.single i x) * e.symm (Pi.single j y) = 0` using `fun i j x y hij => by`. Rewrite using `[← map_mul, ← map_zero e.symm]`.

Use `congr 1`. Use extensionality with `l`. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality. Simplify using `[Pi.single_eq_of_ne hij]`.

Simplify using `[Pi.single_eq_of_ne hl]`. Establish `hUU : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (u i ⊗ₜ[F] (1 : E)) = u i ⊗ₜ[F] (1 : E)` using `fun i => by`. Simplify using `[u, same]`. Establish `hUV : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (v i ⊗ₜ[F] b 1) = v i ⊗ₜ[F] b 1` using `fun i => by`. Simplify using `[u, v, same]`.

Establish `hVV : ∀ i, (v i ⊗ₜ[F] b 1) * (v i ⊗ₜ[F] b 1) = u i ⊗ₜ[F] (1 : E)` using `fun i => by`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, h1, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Use `congr 1`. Simplify using `only [u, v, same]`. Rewrite using `[← map_smul, ← Pi.single_smul, Algebra.smul_def, mul_comm, hc]`.

Establish `hconj : ∀ j, tConj P σ ((2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) + v j ⊗ₜ[F] b 1)) = (2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) - v j ⊗ₜ[F] b 1)` using `fun j => by`. Simplify using `[tConj, hb, TensorProduct.tmul_neg, sub_eq_add_neg]`. Use `⟨fun i => (2⁻¹ : F) • (u i ⊗ₜ[F] (1 : E) + v i ⊗ₜ[F] b 1), fun i hi => ?_, fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `hi' : u i ⊗ₜ[F] (b 0) + v i ⊗ₜ[F] b 1 = 0`. Rewrite using `[h0]`.

Conclude with `(smul_eq_zero.1 hi).resolve_left (inv_ne_zero two_ne_zero)`. Establish `h2` using `congrArg (fun x => (Algebra.TensorProduct.basis P b).repr x 0) hi'`. Simplify using `only [map_add, Finsupp.add_apply, Algebra.TensorProduct.basis_repr_tmul] at h2`. Establish `h3 : u i = 0` using `by simpa using h2`. Establish `h4` using `congrFun (e.symm.injective (h3.trans (map_zero e.symm).symm)) i.1`.

Simplify using `at h4`. Simplify using `only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hUU, hVV, hUV, mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))] module`. Establish `hij' : i.1 ≠ j.1` using `fun h => hij (Subtype.ext h)`. Simplify using `[add_mul, mul_add, u, v, diff _ _ _ _ hij']`. Rewrite using `[hconj]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, hUU, hVV, hUV, mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]`. Use `module`. Establish `hij' : i.1 ≠ j.1` using `fun h => hij (Subtype.ext h)`.

Simplify using `[add_mul, mul_sub, u, v, diff _ _ _ _ hij']`.
-/
theorem splitIdempotents : SplitIdempotents := by
  intro F E _ _ _ _ σ hσ P _ _ k K _ _ ⟨e⟩
  classical
  obtain ⟨b, d, h0, hb, hd, h1⟩ := quad_exists_basis hσ
  have hc : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∃ c : K i, c * c * algebraMap F _ d = 1 := by
    intro i
    obtain ⟨c, hc⟩ := exists_sq_of_not_isField_tensor b d h0 h1 i.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hd ((algebraMap F (K i)).injective (by simpa using hc.symm))
    exact ⟨c⁻¹, by rw [← hc]; field_simp⟩
  choose c hc using hc
  let u : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 1)
  let v : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 (c i))
  have same : ∀ (i : Fin k) (x y : K i), e.symm (Pi.single i x) * e.symm (Pi.single i y) =
      e.symm (Pi.single i (x * y)) := fun i x y => by rw [← map_mul, Pi.single_mul]
  have diff : ∀ (i j : Fin k) (x : K i) (y : K j), i ≠ j →
      e.symm (Pi.single i x) * e.symm (Pi.single j y) = 0 := fun i j x y hij => by
    rw [← map_mul, ← map_zero e.symm]
    congr 1
    ext l
    by_cases hl : l = i
    · subst hl; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hl]
  have hUU : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (u i ⊗ₜ[F] (1 : E)) = u i ⊗ₜ[F] (1 : E) := fun i => by
    simp [u, same]
  have hUV : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (v i ⊗ₜ[F] b 1) = v i ⊗ₜ[F] b 1 := fun i => by
    simp [u, v, same]
  have hVV : ∀ i, (v i ⊗ₜ[F] b 1) * (v i ⊗ₜ[F] b 1) = u i ⊗ₜ[F] (1 : E) := fun i => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h1, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    simp only [u, v, same]
    rw [← map_smul, ← Pi.single_smul, Algebra.smul_def, mul_comm, hc]
  have hconj : ∀ j, tConj P σ ((2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) + v j ⊗ₜ[F] b 1)) =
      (2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) - v j ⊗ₜ[F] b 1) := fun j => by
    simp [tConj, hb, TensorProduct.tmul_neg, sub_eq_add_neg]
  refine ⟨fun i => (2⁻¹ : F) • (u i ⊗ₜ[F] (1 : E) + v i ⊗ₜ[F] b 1), fun i hi => ?_, fun i => ?_,
    fun i j hij => ?_, fun i j => ?_⟩
  · have hi' : u i ⊗ₜ[F] (b 0) + v i ⊗ₜ[F] b 1 = 0 := by
      rw [h0]; exact (smul_eq_zero.1 hi).resolve_left (inv_ne_zero two_ne_zero)
    have h2 := congrArg (fun x => (Algebra.TensorProduct.basis P b).repr x 0) hi'
    simp only [map_add, Finsupp.add_apply, Algebra.TensorProduct.basis_repr_tmul] at h2
    have h3 : u i = 0 := by simpa using h2
    have h4 := congrFun (e.symm.injective (h3.trans (map_zero e.symm).symm)) i.1
    simp at h4
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hUU, hVV, hUV,
      mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
    module
  · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [add_mul, mul_add, u, v, diff _ _ _ _ hij']
  · rw [hconj]
    by_cases hij : i = j
    · subst hij
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, hUU, hVV, hUV,
        mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
      module
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [add_mul, mul_sub, u, v, diff _ _ _ _ hij']

end GlobalTheory.RegSS
