import Mathlib

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `: NeZero l` using `⟨hl.ne'⟩`. Take `⟨g₀, hg₀⟩` from `AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) M σ`. Establish `hg₀ζ : IsPrimitiveRoot (g₀ ζ) l` using `hζ.map_of_injective g₀.injective`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one hg₀ζ.pow_eq_one`.

Establish `hcop : i.Coprime l` using `(hζ.pow_iff_coprime hl i).mp (hi ▸ hg₀ζ)`. Use `set u : (ZMod l)ˣ := ZMod.unitOfCoprime i hcop with hu`. Use `set t : (ZMod l)ˣ := τ * u⁻¹ with ht`. Use `set h : M ≃ₐ[K] M := (IsCyclotomicExtension.autEquivPow M hirr).symm t with hh`. Establish `hz` using `IsCyclotomicExtension.zeta_spec l K M`.

Establish `hhz : h (IsCyclotomicExtension.zeta l K M) = (IsCyclotomicExtension.zeta l K M) ^ (t : ZMod l).val`. Establish `h1` using `hz.autToPow_spec K h`. Establish `h2 : hz.autToPow K h = t`. Use `(IsCyclotomicExtension.autEquivPow M hirr).apply_symm_apply t` as an intermediate fact. Conclude with `this`.

Rewrite using `[← h1, h2]`. Take `⟨a, -, ha⟩` from `hz.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Establish `hhζ : h ζ = ζ ^ (t : ZMod l).val`. Rewrite using `[← ha, map_pow, hhz, ← pow_mul, ← pow_mul, mul_comm]`. Use `⟨h.restrictScalars ℚ * g₀, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : AlgEquiv.restrictNormal (h.restrictScalars ℚ) K = 1`. Use extensionality with `x`. Establish `e` using `AlgEquiv.restrictNormal_commutes (h.restrictScalars ℚ : M ≃ₐ[ℚ] M) K x`. Establish `e2 : (h.restrictScalars ℚ) (algebraMap K M x) = algebraMap K M x` using `h.commutes x`. Rewrite `e` using `[e2]`.

Conclude with `(algebraMap K M).injective e`. Establish `h2 : AlgEquiv.restrictNormal (h.restrictScalars ℚ * g₀) K = AlgEquiv.restrictNormal (h.restrictScalars ℚ) K * AlgEquiv.restrictNormal g₀ K` using `map_mul (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) K) _ _`. Rewrite using `[h2, h1, one_mul]`. Conclude with `hg₀`. Use `show h (g₀ ζ) = _`.

Rewrite using `[← hi, map_pow, hhζ, ← pow_mul]`. Rewrite using `[← pow_mod_orderOf, ← hζ.eq_orderOf, ← pow_mod_orderOf ζ (τ : ZMod l).val, ← hζ.eq_orderOf]`. Use `congr 1`. Rewrite using `[← ZMod.natCast_eq_natCast_iff']`. Use `push_cast`.

Rewrite using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Establish `: ((u : (ZMod l)ˣ) : ZMod l) = (i : ZMod l)` using `rfl`. Rewrite using `[← this]`. Rewrite using `[← Units.val_mul, ht, inv_mul_cancel_right]`.
-/
theorem exists_lift_pow {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M] (l : ℕ) [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    (hirr : Irreducible (cyclotomic l K)) {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (τ : (ZMod l)ˣ) :
    ∃ g : Gal(M/ℚ), AlgEquiv.restrictNormal g K = σ ∧ g ζ = ζ ^ (τ : ZMod l).val := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨g₀, hg₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) M σ
  have hg₀ζ : IsPrimitiveRoot (g₀ ζ) l := hζ.map_of_injective g₀.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg₀ζ.pow_eq_one
  have hcop : i.Coprime l := (hζ.pow_iff_coprime hl i).mp (hi ▸ hg₀ζ)
  set u : (ZMod l)ˣ := ZMod.unitOfCoprime i hcop with hu
  set t : (ZMod l)ˣ := τ * u⁻¹ with ht
  set h : M ≃ₐ[K] M := (IsCyclotomicExtension.autEquivPow M hirr).symm t with hh
  have hz := IsCyclotomicExtension.zeta_spec l K M
  have hhz : h (IsCyclotomicExtension.zeta l K M) = (IsCyclotomicExtension.zeta l K M) ^ (t : ZMod l).val := by
    have h1 := hz.autToPow_spec K h
    have h2 : hz.autToPow K h = t := by
      have := (IsCyclotomicExtension.autEquivPow M hirr).apply_symm_apply t
      exact this
    rw [← h1, h2]
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hhζ : h ζ = ζ ^ (t : ZMod l).val := by
    rw [← ha, map_pow, hhz, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨h.restrictScalars ℚ * g₀, ?_, ?_⟩
  · have h1 : AlgEquiv.restrictNormal (h.restrictScalars ℚ) K = 1 := by
      ext x
      have e := AlgEquiv.restrictNormal_commutes (h.restrictScalars ℚ : M ≃ₐ[ℚ] M) K x
      have e2 : (h.restrictScalars ℚ) (algebraMap K M x) = algebraMap K M x := h.commutes x
      rw [e2] at e
      exact (algebraMap K M).injective e
    have h2 : AlgEquiv.restrictNormal (h.restrictScalars ℚ * g₀) K =
        AlgEquiv.restrictNormal (h.restrictScalars ℚ) K * AlgEquiv.restrictNormal g₀ K :=
      map_mul (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) K) _ _
    rw [h2, h1, one_mul]
    exact hg₀
  · show h (g₀ ζ) = _
    rw [← hi, map_pow, hhζ, ← pow_mul]
    rw [← pow_mod_orderOf, ← hζ.eq_orderOf, ← pow_mod_orderOf ζ (τ : ZMod l).val, ← hζ.eq_orderOf]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((u : (ZMod l)ˣ) : ZMod l) = (i : ZMod l) := rfl
    rw [← this]
    rw [← Units.val_mul, ht, inv_mul_cancel_right]

end ReciprocityTheory.Cheb
