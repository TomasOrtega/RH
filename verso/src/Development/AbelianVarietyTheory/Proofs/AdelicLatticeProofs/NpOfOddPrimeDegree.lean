import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPushoutPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankPrimeOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Use `letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra`. Use `haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Take `⟨y₀, hy₀⟩` from `h`. Set `ψ : K →ₐ[F] K'` to `{ φ with commutes' := hφ }`. Set `y : K' ⊗[F] E` to `Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀`.

Establish `hy : Algebra.norm K' y = algebraMap F K' x`. Rewrite using `[tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]`. Set `e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E` to `Algebra.TensorProduct.cancelBaseChange F F' K' K' E`. Set `e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E'` to `Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')`. Use `⟨(e₁.symm.trans e₂) y, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]`.
-/
theorem tNorm_baseChange_of_ringHom (F F' E E' K K' : Type) [Field F] [Field F'] [Field E]
    [Field E'] [Algebra F F'] [Algebra F E] [Algebra F' E'] [Algebra E E'] [Algebra F E']
    [IsScalarTower F F' E'] [IsScalarTower F E E'] [Algebra.IsPushout F F' E E']
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field K'] [Algebra F' K'] (φ : K →+* K')
    (hφ : ∀ x : F, φ (algebraMap F K x) = algebraMap F' K' (algebraMap F F' x)) (x : F)
    (h : TNorm F E K x) : TNorm F' E' K' (algebraMap F F' x) := by
  letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra
  haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y₀, hy₀⟩ := h
  let ψ : K →ₐ[F] K' := { φ with commutes' := hφ }
  let y : K' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀
  have hy : Algebra.norm K' y = algebraMap F K' x := by
    rw [tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]
  let e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E :=
    Algebra.TensorProduct.cancelBaseChange F F' K' K' E
  let e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E' :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')
  refine ⟨(e₁.symm.trans e₂) y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Use `⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]`. Simplify using the standard rewrite rules.
-/
theorem exists_norm_eq_of_coprime_pow {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {m n : ℕ} (hc : Nat.Coprime m n) {x : F} (hx : x ≠ 0) {a b : E}
    (ha : Algebra.norm F a = x ^ m) (hb : Algebra.norm F b = x ^ n) :
    ∃ y : E, Algebra.norm F y = x := by
  refine ⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩
  rw [map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]
  simp

/- English proof (translation)
Introduce `p F E _ _ _ _ _ _ hp h2 hd x hx hl`. Take `⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩` from `exists_pushout_primitiveRoot p F E hp h2 hd`. Establish `hl' : LocNorm F' E' (algebraMap F F' x)`. Use `⟨fun w => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w`.

Conclude with `tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)`. It suffices to derive a contradiction. Set `ψ : F' →+* ℂ` to `Complex.ofRealHom.comp (algebraMap F' ℝ)`. Apply `IsTotallyComplex.complexEmbedding_not_isReal ψ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `y`. Simplify using `[ψ]`. Take `⟨b, hb⟩` from `np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'`. Establish `h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F'`. Rewrite using `[Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]`.

Establish `h3 : Algebra.norm F (algebraMap F E x) = x ^ p`. Rewrite using `[Algebra.norm_algebraMap, hd]`. Conclude with `exists_norm_eq_of_coprime_pow hc hx h1 h3`.
-/
theorem np_of_odd_prime_degree : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E],
    p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ hp h2 hd x hx hl
  obtain ⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩ :=
    exists_pushout_primitiveRoot p F E hp h2 hd
  have hl' : LocNorm F' E' (algebraMap F F' x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w
      exact tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)
    · exfalso
      let ψ : F' →+* ℂ := Complex.ofRealHom.comp (algebraMap F' ℝ)
      apply IsTotallyComplex.complexEmbedding_not_isReal ψ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      simp [ψ]
  obtain ⟨b, hb⟩ :=
    np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'
  have h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F' := by
    rw [Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]
  have h3 : Algebra.norm F (algebraMap F E x) = x ^ p := by
    rw [Algebra.norm_algebraMap, hd]
  exact exists_norm_eq_of_coprime_pow hc hx h1 h3

end GlobalTheory.CNorm
