import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Take `⟨⟨hd, hh⟩, h2, h3⟩` from `hk`. Take `⟨⟨hd', hh'⟩, h2', h3'⟩` from `hk'`. Use `⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, hh, hh']`. Take `⟨y2, hy2, e2⟩` from `h2' x hx`.

Establish `hx' : k' *ᵥ x ∈ hat F L`. Establish `: k' *ᵥ x = x + M • y2` using `by rw [← e2]; abel`. Rewrite using `[this]`. Conclude with `add_mem hx (nsmul_mem hy2 _)`. Take `⟨y1, hy1, e1⟩` from `h2 _ hx'`.

Use `⟨y1 + y2, add_mem hy1 hy2, ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, smul_add, ← e1, ← e2]`. Normalize the expressions using the abelian group laws. Take `⟨y1, hy1, e1⟩` from `h3 x hx`. Take `⟨y2, hy2, e2⟩` from `h3' y1 hy1`.

Conclude with `⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩`.
-/
theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

/- English proof (translation)
Take `⟨⟨hd, hh⟩, h2, h3⟩` from `hk`. Establish `hkk : k * k⁻¹ = 1` using `mul_nonsing_inv k hd`. Establish `hkk' : k⁻¹ * k = 1` using `nonsing_inv_mul k hd`. Establish `hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L`. Introduce `x hx`.

Take `⟨y, hy, e⟩` from `h2 x hx`. Establish `: k *ᵥ x = x + M • y` using `by rw [← e]; abel`. Rewrite using `[this]`. Conclude with `add_mem hx (nsmul_mem hy _)`. Use `⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[det_nonsing_inv]`. Conclude with `hd.ringInverse`. Rewrite using `[← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]`. Take `⟨y, hy, e⟩` from `h3 x hx`. Take `⟨z, hz, ez⟩` from `h2 y hy`.

Use `⟨-z, neg_mem hz, ?_⟩` and prove the remaining obligations. Establish `: k⁻¹ *ᵥ x = y` using `by rw [← e, mulVec_mulVec, hkk', one_mulVec]`. Rewrite using `[this, ← e, smul_neg, ← ez]`. Normalize the expressions using the abelian group laws. Conclude with `⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩`.
-/
theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩`.
-/
theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

/- English proof (translation)
Take `⟨u, hu, k, hk, rfl⟩` from `h`. Establish `hu0 : u ≠ 0` using `left_ne_zero_of_mul_eq_one hu`. Use `⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩` and prove the remaining obligations. Establish `hd : IsUnit k.det` using `hk.1.1`. Establish `e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]`. Establish `e2 : k.det * k⁻¹.det = 1` using `by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, one_mul, mul_one]`. Use `_ = _ := by ring`.
-/
theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

/- English proof (translation)
Take `⟨u, hu, k, hk, rfl⟩` from `h`. Take `⟨u', hu', k', hk', rfl⟩` from `h'`. Use `⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[det_mul, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

/- English proof (translation)
The claim follows from `(Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h`.
-/
theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

/- English proof (translation)
Introduce `E _ _ _ r M G L a b h`. Conclude with `GlobalTheory.UCls.tEquiv_of_eqvGen a b h`.
-/
theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
