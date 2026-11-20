import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `R S _ _ _ _ _ n b t ht`. Set `φ : S →ₐ[R] Matrix (Fin n) (Fin n) R` to `(LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul R S)`. Establish `hφ : ∀ s, φ s = LinearMap.toMatrix b b (LinearMap.mulLeft R s)`. Introduce `s`. Use extensionality with `i j`.

Simplify using `[φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]`. Use `set N := LinearMap.toMatrix b b (LinearMap.mulLeft R t) with hN`. Use `set Nb := N.map (IsLocalRing.residue R) with hNb`. Establish `hcp : Nb.charpoly ≠ 0` using `(Matrix.charpoly_monic Nb).ne_zero`. Take `⟨hb, hfac, hndvd⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd Nb.charpoly hcp 0`.

Establish `h0 : hb.eval 0 ≠ 0`. Introduce `h`. Apply `hndvd` to reduce the goal to its premises. Rewrite using `[dvd_iff_isRoot]`. Conclude with `h`.

Take `⟨h, rfl⟩` from `Polynomial.map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective hb`. Establish `hu0 : IsUnit (h.coeff 0)`. Assume the negation of the conclusion as `hc`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← coeff_zero_eq_eval_zero, coeff_map]`.

Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hc)`. Take `⟨q, hq⟩` from `X_dvd_sub_C (p := h)`. Establish `hsplit : aeval t h = algebraMap R S (h.coeff 0) + t * aeval t q`. Establish `: h = C (h.coeff 0) + X * q` using `by rw [← hq]; ring`. Use `conv_lhs => rw [this]`.

Simplify using the standard rewrite rules. Establish `hut : IsUnit (aeval t h)`. Rewrite using `[hsplit]`. Assume the negation of the conclusion as `hc`. Establish `h1 : algebraMap R S (h.coeff 0) + t * aeval t q ∈ IsLocalRing.maximalIdeal S` using `(IsLocalRing.mem_maximalIdeal _).2 hc`.

Establish `h2 : t * aeval t q ∈ IsLocalRing.maximalIdeal S` using `Ideal.mul_mem_right _ _ ht`. Establish `h3 : algebraMap R S (h.coeff 0) ∈ IsLocalRing.maximalIdeal S`. Use `Ideal.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h3 (hu0.map (algebraMap R S))`.

Establish `huN : IsUnit (aeval N h)`. Use `hut.map φ` as an intermediate fact. Rewrite `this` using `[← Polynomial.aeval_algHom_apply, hφ]`. Then use the resulting hypothesis. Establish `hmap : (IsLocalRing.residue R).mapMatrix (aeval N h) = aeval Nb (h.map (IsLocalRing.residue R))`. Rewrite using `[aeval_def, aeval_def, hom_eval₂, eval₂_map]`.

Use `congr 1`. Use extensionality with `r i j`. Simplify using `[Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `huNb : IsUnit (aeval Nb (h.map (IsLocalRing.residue R)))`.

Rewrite using `[← hmap]`. Conclude with `huN.map _`. Establish `hCH` using `Matrix.aeval_self_charpoly Nb`. Rewrite `hCH` using `[hfac, C_0, sub_zero, map_mul, map_pow, aeval_X]`. Conclude with `⟨_, (huNb.mul_left_eq_zero).1 hCH⟩`.
-/
theorem isNilpotent_residue_toMatrix_mulLeft : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  intro R S _ _ _ _ _ n b t ht
  let φ : S →ₐ[R] Matrix (Fin n) (Fin n) R :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul R S)
  have hφ : ∀ s, φ s = LinearMap.toMatrix b b (LinearMap.mulLeft R s) := by
    intro s; ext i j
    simp [φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft R t) with hN
  set Nb := N.map (IsLocalRing.residue R) with hNb
  have hcp : Nb.charpoly ≠ 0 := (Matrix.charpoly_monic Nb).ne_zero
  obtain ⟨hb, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Nb.charpoly hcp 0
  have h0 : hb.eval 0 ≠ 0 := by
    intro h; apply hndvd; rw [dvd_iff_isRoot]; exact h
  obtain ⟨h, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R)
    IsLocalRing.residue_surjective hb
  have hu0 : IsUnit (h.coeff 0) := by
    by_contra hc
    apply h0
    rw [← coeff_zero_eq_eval_zero, coeff_map]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hc)
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := h)
  have hsplit : aeval t h = algebraMap R S (h.coeff 0) + t * aeval t q := by
    have : h = C (h.coeff 0) + X * q := by rw [← hq]; ring
    conv_lhs => rw [this]
    simp
  have hut : IsUnit (aeval t h) := by
    rw [hsplit]
    by_contra hc
    have h1 : algebraMap R S (h.coeff 0) + t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_right _ _ ht
    have h3 : algebraMap R S (h.coeff 0) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 (hu0.map (algebraMap R S))
  have huN : IsUnit (aeval N h) := by
    have := hut.map φ
    rwa [← Polynomial.aeval_algHom_apply, hφ] at this
  have hmap : (IsLocalRing.residue R).mapMatrix (aeval N h) = aeval Nb (h.map (IsLocalRing.residue R)) := by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    ext r i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  have huNb : IsUnit (aeval Nb (h.map (IsLocalRing.residue R))) := by
    rw [← hmap]; exact huN.map _
  have hCH := Matrix.aeval_self_charpoly Nb
  rw [hfac, C_0, sub_zero, map_mul, map_pow, aeval_X] at hCH
  exact ⟨_, (huNb.mul_left_eq_zero).1 hCH⟩

end GlobalTheory
