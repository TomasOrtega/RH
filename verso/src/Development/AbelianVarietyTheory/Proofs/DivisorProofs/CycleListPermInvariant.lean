import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

/- English proof (translation)
Establish `hu : IsUnit (N : ℤ_[ℓ])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN`. Take `⟨u, hu⟩` from `hu`. Establish `hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F` using `Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩`.

Establish `heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c))`. Establish `h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)`. Rewrite using `[hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]`. Rewrite using `[← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Rewrite using `[heq]`.

Conclude with `Subalgebra.smul_mem _ hmem _`.
-/
theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := F) s`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩` and prove the remaining obligations. Establish `h` using `hy c hc`. Rewrite `h` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases.

Rewrite `h` using `[e]`. Simplify using `using h`. Rewrite `h` using `[e]`. Use `h.neg` as an intermediate fact. Simplify `this` using `[neg_mul]`.
-/
theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

/- English proof (translation)
Establish `hl : r.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom ∈ Polynomial.lifts ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Rewrite using `[Polynomial.coeff_map]`. Conclude with `⟨⟨_, tmul_mem_cenOrder ℓ hN (hr n)⟩, rfl⟩`.

Take `⟨q, hq⟩` from `hl`. Conclude with `⟨q, hq⟩`.
-/
theorem exists_lift {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) (r : Polynomial F) (hr : ∀ n, IsIntegral ℤ ((N : F) * r.coeff n)) :
    ∃ q : Polynomial (cenOrder ℓ F), q.map ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) =
      r.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom := by
  have hl : r.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom ∈
      Polynomial.lifts ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, tmul_mem_cenOrder ℓ hN (hr n)⟩, rfl⟩
  obtain ⟨q, hq⟩ := hl
  exact ⟨q, hq⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `hp`. Take `⟨N, hN0, hN⟩` from `exists_nat_integral (p.coeffs ∪ a.coeffs ∪ b.coeffs)`. Establish `hcoef : ∀ r : Polynomial F, r.coeffs ⊆ p.coeffs ∪ a.coeffs ∪ b.coeffs → ∀ n, IsIntegral ℤ ((N : F) * r.coeff n)`. Introduce `r hs n`. Distinguish the cases in `h0 : r.coeff n = 0`.

Rewrite using `[h0, mul_zero]`. Conclude with `isIntegral_zero`. Conclude with `hN _ (hs (Polynomial.coeff_mem_coeffs h0))`. Use `⟨N, hN0, fun ℓ _ hℓ => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `exists_lift ℓ hℓ p (hcoef p (fun x hx => by simp [hx]))`.

Take `⟨a', ha'⟩` from `exists_lift ℓ hℓ a (hcoef a (fun x hx => by simp [hx]))`. Take `⟨b', hb'⟩` from `exists_lift ℓ hℓ b (hcoef b (fun x hx => by simp [hx]))`. Use `⟨q, hq, a', b', ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, ha', hb', hq, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]`.
-/
theorem separable_model (F : Type) [Field F] [NumberField F] (p : Polynomial F) (hp : p.Separable) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ q : Polynomial (cenOrder ℓ F), q.map ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) =
        p.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom ∧ q.Separable := by
  classical
  obtain ⟨a, b, hab⟩ := hp
  obtain ⟨N, hN0, hN⟩ := exists_nat_integral (p.coeffs ∪ a.coeffs ∪ b.coeffs)
  have hcoef : ∀ r : Polynomial F, r.coeffs ⊆ p.coeffs ∪ a.coeffs ∪ b.coeffs →
      ∀ n, IsIntegral ℤ ((N : F) * r.coeff n) := by
    intro r hs n
    by_cases h0 : r.coeff n = 0
    · rw [h0, mul_zero]; exact isIntegral_zero
    · exact hN _ (hs (Polynomial.coeff_mem_coeffs h0))
  refine ⟨N, hN0, fun ℓ _ hℓ => ?_⟩
  obtain ⟨q, hq⟩ := exists_lift ℓ hℓ p (hcoef p (fun x hx => by simp [hx]))
  obtain ⟨a', ha'⟩ := exists_lift ℓ hℓ a (hcoef a (fun x hx => by simp [hx]))
  obtain ⟨b', hb'⟩ := exists_lift ℓ hℓ b (hcoef b (fun x hx => by simp [hx]))
  refine ⟨q, hq, a', b', ?_⟩
  apply Polynomial.map_injective ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) Subtype.val_injective
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha', hb', hq, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.SepModel
