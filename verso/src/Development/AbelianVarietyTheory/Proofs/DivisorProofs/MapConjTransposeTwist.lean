import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix ComplexOrder

namespace GlobalTheory.QuotRational

/- English proof (translation)
Establish `hAu : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit`. Establish `hM : IsUnit (P * A⁻¹ * Pᴴ).det`. Assume the negation of the conclusion as `h`. Rewrite `h2` using `[Matrix.nonsing_inv_apply_not_isUnit _ h]`. Substitute `h2` using the available equality.

Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Conclude with `h (by simp)`. Establish `: Nonempty (Fin d)` using `⟨⟨0, hd⟩⟩`. Simplify using `at hG`. Establish `h3 : G * (P * A⁻¹ * Pᴴ) = 1` using `by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM`.

Establish `h4 : Dᴴ * Pᴴ = 1`. Rewrite `h3` using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one]`. Conclude with `h3`. Establish `h5 : P * D = 1`. Use `congrArg Matrix.conjTranspose h4` as an intermediate fact.

Simplify `this` using `[Matrix.conjTranspose_mul]`. Rewrite using `[← h1, Matrix.mul_assoc, h5, Matrix.mul_one]`.
-/
theorem gram_of_quotMet {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : IsUnit G.det) (P : Matrix (Fin d) (Fin n) ℂ) (D : Matrix (Fin n) (Fin d) ℂ) (h1 : G * P = Dᴴ * A)
    (h2 : (P * A⁻¹ * Pᴴ)⁻¹ = G) : Dᴴ * A * D = G := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hM : IsUnit (P * A⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h2
    subst h2
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact h (by simp)
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp at hG
  have h3 : G * (P * A⁻¹ * Pᴴ) = 1 := by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM
  have h4 : Dᴴ * Pᴴ = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu,
      Matrix.mul_one] at h3
    exact h3
  have h5 : P * D = 1 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul] using this
  rw [← h1, Matrix.mul_assoc, h5, Matrix.mul_one]

/- English proof (translation)
Establish `hG : Gᴴ = G`. Rewrite using `[← h1]`. Simplify using `[Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]`. Establish `h4 : Cᴴ * A * D = G`. Use `congrArg Matrix.conjTranspose h3` as an intermediate fact.

Rewrite `this` using `[hG]`. Simplify `this` using `[Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]`. Establish `h5 : (C - D)ᴴ * A * (C - D) = 0`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]`. Simplify using the standard rewrite rules.

Establish `h6 : ∀ x, (C - D) *ᵥ x = 0`. Introduce `x`. Assume the negation of the conclusion as `hx`. Use `hA.dotProduct_mulVec_pos hx` as an intermediate fact. Rewrite `this` using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5]`.

Simplify using `at this`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Simplify using `using congrFun (h6 (Pi.single j 1)) i`.
-/
theorem eq_of_gram {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (C D : Matrix (Fin n) (Fin d) ℂ) (h1 : Dᴴ * A * D = G) (h2 : Cᴴ * A * C = G) (h3 : Dᴴ * A * C = G) : C = D := by
  have hG : Gᴴ = G := by
    rw [← h1]; simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]
  have h4 : Cᴴ * A * D = G := by
    have := congrArg Matrix.conjTranspose h3
    rw [hG] at this
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  have h5 : (C - D)ᴴ * A * (C - D) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    simp
  have h6 : ∀ x, (C - D) *ᵥ x = 0 := by
    intro x
    by_contra hx
    have := hA.dotProduct_mulVec_pos hx
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5] at this
    simp at this
  rw [← sub_eq_zero]
  ext i j
  simpa using congrFun (h6 (Pi.single j 1)) i

variable {K : Type} [Field K] [StarRing K]

/- English proof (translation)
Use extensionality with `a i`. Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply, starRingEnd_apply, star_star]`.
-/
theorem map_conjTranspose_twist (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (Eᴴ).map σ = (E.map (twist σ))ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply, starRingEnd_apply, star_star]

/- English proof (translation)
Use extensionality with `a`. Simplify using `[twist]`.
-/
theorem twist_twist (σ : K →+* ℂ) : twist (twist σ) = σ := by
  ext a
  simp [twist]

/- English proof (translation)
Use extensionality with `i j`. Establish `: σ (star (H i j)) = starRingEnd ℂ (σ (H i j))` using `hH i j σ`. Simplify using `only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]`.
-/
theorem map_twist_of_mem (σ : K →+* ℂ) {n d : ℕ} (H : Matrix (Fin n) (Fin d) K) (hH : ∀ i j, H i j ∈ cmMax K) :
    H.map (twist σ) = H.map σ := by
  ext i j
  have : σ (star (H i j)) = starRingEnd ℂ (σ (H i j)) := hH i j σ
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]

/- English proof (translation)
Establish `hsurj : Function.Surjective Pr.mulVec` using `Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩`. Establish `hGP : Eᴴ * H * E * Pr = Eᴴ * H`. Establish `h2` using `hP.2`. Rewrite `h2` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Rewrite using `[Matrix.mul_assoc (Eᴴ * H), ← h2]`.

Establish `hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (twist v.embedding) = (Eᴴ * H * E).map v.embedding`. Introduce `v`. Establish `hq` using `(quotFrameIsQuot K n d H hpos Pr hsurj v).2`. Establish `hr` using `(hR.2 v).2`. Rewrite using `[map_conjTranspose_twist]`.

Use `gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)` and prove the remaining obligations. Rewrite using `[← hr]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit`. Rewrite using `[← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]`. Establish `hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (twist σ) = (Eᴴ * H * E).map σ`.

Introduce `σ`. Break down `InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hv _`. Establish `h1` using `congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))`.

Simplify using `only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1`. Rewrite using `[← h]`. Conclude with `h1`. Establish `hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (twist v.embedding)`. Introduce `v`.

Use `eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_conjTranspose_twist]`. Conclude with `hall _`. Establish `h1` using `hall (twist v.embedding)`. Rewrite `h1` using `[map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1]`. Then use the resulting hypothesis.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]`. Introduce `i a σ`. Establish `h1` using `congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a`. Simplify using `only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply] at h1`. Break down `InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h` into its components or cases.

Rewrite `h1` using `[h]`. Rewrite using `[h1, starRingEnd_apply, star_star]`. Rewrite using `[← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]`. Simplify using the standard rewrite rules.
-/
theorem entries_mem_cmMax [NumberField K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ cmMax K)
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hR : IsRatHerm (cmMax K) (Eᴴ * H * E) (quotFrame Pr H)) : ∀ i a, E i a ∈ cmMax K := by
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hGP : Eᴴ * H * E * Pr = Eᴴ * H := by
    have h2 := hP.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Eᴴ * H), ← h2]
  have hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (twist v.embedding) =
      (Eᴴ * H * E).map v.embedding := by
    intro v
    have hq := (quotFrameIsQuot K n d H hpos Pr hsurj v).2
    have hr := (hR.2 v).2
    rw [map_conjTranspose_twist]
    refine gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)
    · rw [← hr]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit
    · rw [← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]
  have hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (twist σ) = (Eᴴ * H * E).map σ := by
    intro σ
    rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
    · rw [← h]; exact hv _
    · have h1 := congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))
      simp only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1
      rw [← h]
      exact h1
  have hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (twist v.embedding) := by
    intro v
    refine eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_
    · rw [← map_conjTranspose_twist]; exact hall _
    · have h1 := hall (twist v.embedding)
      rwa [map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1] at h1
    · rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]
  intro i a σ
  have h1 := congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply] at h1
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
  · rw [h] at h1
    rw [h1, starRingEnd_apply, star_star]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]
    simp

/- English proof (translation)
Introduce `K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k`. Establish `hE` using `entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr) (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR`. Rewrite using `[BlockDat.fE, Matrix.mul_apply]`. Conclude with `Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)`.
-/
theorem fE_mem_cmMax : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → ∀ a k, B.fE ℓ Z a k ∈ cmMax K := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k
  have hE := entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr)
    (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR
  rw [BlockDat.fE, Matrix.mul_apply]
  exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)

end GlobalTheory.QuotRational
