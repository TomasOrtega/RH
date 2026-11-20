import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `O _ bar ψ X _ _ _ m n γ v hγ hbal hnn hcone`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hγ.strict`. Establish `hk : ∀ j, ∃ k : ℕ, 0 < k ∧ ((k : ℤ) • v j) ∈ Submodule.span ℤ (Set.range γ)`. Introduce `j`. Take `⟨c, hc, e⟩` from `hcone j`.

Establish `hl` using `apply_eq_of_toReal_eq e ℓ`. Establish `hlin` using `(linearOn_iff ψ γ).1 hγ.linear c hc`. Rewrite `hlin` using `[← e, evalR_toReal]`. Establish `heq : (N : ℝ) * ψ.evalZ (v j) = ℓ (v j)`. Rewrite using `[hl, hlin, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h1 i]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, c', hk, hc'⟩` from `h3 (v j) (hbal j) (hnn j) heq`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[natCast_zsmul, hc']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `choose k hkpos hkmem using hk`. Use `set K : ℕ := ∏ j, k j with hKdef`. Establish `hK : 0 < K` using `Finset.prod_pos fun j _ => hkpos j`.

Use `set S := Submodule.span ℤ (Set.range γ) with hS`. Establish `hle : Submodule.span ℤ (Set.range v) ≤ S.comap ((K : ℤ) • LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Take `⟨r, hr⟩ : k j ∣ K` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ j)`.

Use `show ((K : ℤ) • LinearMap.id) (v j) ∈ S`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[hr, Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `S.smul_mem _ (hkmem j)`. Set `f : Submodule.span ℤ (Set.range v) →ₗ[ℤ] S` to `(((K : ℤ) • LinearMap.id).comp (Submodule.span ℤ (Set.range v)).subtype).codRestrict S fun x => hle x.2`.

Establish `hf : Function.Injective f`. Introduce `x y hxy`. Establish `e` using `congrArg Subtype.val hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations.

Establish `e2` using `LinearMap.congr_fun₂ e a b`. Simplify using `only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at e2`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hK.ne') e2`. Use `haveI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range γ)`. Conclude with `LinearMap.finrank_le_finrank_of_injective hf`.
-/
theorem genRank_le_of_inRCone_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) →
    genRank v ≤ genRank γ := by
  intro O _ bar ψ X _ _ _ m n γ v hγ hbal hnn hcone
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hk : ∀ j, ∃ k : ℕ, 0 < k ∧ ((k : ℤ) • v j) ∈ Submodule.span ℤ (Set.range γ) := by
    intro j
    obtain ⟨c, hc, e⟩ := hcone j
    have hl := apply_eq_of_toReal_eq e ℓ
    have hlin := (linearOn_iff ψ γ).1 hγ.linear c hc
    rw [← e, evalR_toReal] at hlin
    have heq : (N : ℝ) * ψ.evalZ (v j) = ℓ (v j) := by
      rw [hl, hlin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i]; ring
    obtain ⟨k, c', hk, hc'⟩ := h3 (v j) (hbal j) (hnn j) heq
    refine ⟨k, hk, ?_⟩
    rw [natCast_zsmul, hc']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose k hkpos hkmem using hk
  set K : ℕ := ∏ j, k j with hKdef
  have hK : 0 < K := Finset.prod_pos fun j _ => hkpos j
  set S := Submodule.span ℤ (Set.range γ) with hS
  have hle : Submodule.span ℤ (Set.range v) ≤ S.comap ((K : ℤ) • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr⟩ : k j ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show ((K : ℤ) • LinearMap.id) (v j) ∈ S
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hr, Nat.cast_mul, mul_comm, mul_smul]
    exact S.smul_mem _ (hkmem j)
  let f : Submodule.span ℤ (Set.range v) →ₗ[ℤ] S :=
    (((K : ℤ) • LinearMap.id).comp (Submodule.span ℤ (Set.range v)).subtype).codRestrict S fun x => hle x.2
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    apply Subtype.ext
    refine LinearMap.ext₂ fun a b => ?_
    have e2 := LinearMap.congr_fun₂ e a b
    simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul] at e2
    exact mul_left_cancel₀ (by exact_mod_cast hK.ne') e2
  haveI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  exact LinearMap.finrank_le_finrank_of_injective hf

end GlobalTheory.PolFan
