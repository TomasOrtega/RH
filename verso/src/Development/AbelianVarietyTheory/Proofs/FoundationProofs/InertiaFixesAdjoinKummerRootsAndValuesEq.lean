import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.InertKummer

/- English proof (translation)
Establish `hu : IsUnit (⟨x, hx⟩ : B)` using `isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩`. Conclude with `(B.valuation_eq_one_iff ⟨x, hx⟩).mp hu`.
-/
theorem valuation_eq_one_of_mem {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B) (hx' : x⁻¹ ∈ B)
    (h0 : x ≠ 0) : B.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : B) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (B.valuation_eq_one_iff ⟨x, hx⟩).mp hu

/- English proof (translation)
Introduce `k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 → B.valuation (algebraMap K Ω x) = 1`. Introduce `x hx hx' hx0`. Use `valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)` and prove the remaining obligations.

Rewrite using `[← map_inv₀]`. Conclude with `hB _ hx'`. Establish `hNK0 : (N : K) ≠ 0`. Establish `: ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K)` using `map_natCast _ _`. Rewrite using `[← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')`.

Establish `hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K` using `Subalgebra.natCast_mem _ N`. Establish `hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K`. Establish `: ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹`. Rewrite using `[map_inv₀, map_natCast]`. Rewrite using `[← this]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Establish `hvN : B.valuation (N : Ω) = 1`. Use `hunit _ hNmem hNinv hNK0` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 → γ ^ N = algebraMap K Ω x → g γ = γ`.

Introduce `γ x hx hx' hx0 hγ`. Use `GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[hγ]`. Conclude with `g.commutes x`. Rewrite using `[one_pow, div_one, hγ]`.

Conclude with `hunit x hx hx' hx0`. Establish `hgα : g α = α` using `hroot α a ha ha' ha0 hα`. Establish `hgβ : g β = β` using `hroot β b hb hb' hb0 hβ`. Establish `hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup`. Establish `hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup`.

Rewrite using `[← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Establish `hgx : g x = x`. Break down `hx with rfl | hx` into its components or cases. Conclude with `hgα`.

Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `hgβ`. Establish `hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x` using `hgx`. Introduce `f`. Establish `hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x` using `Subgroup.zpowers_le.mpr hs f.2`.

Conclude with `hf`. Conclude with `hz (Subgroup.mem_zpowers g)`. Establish `hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x` using `fun x hx => hfix ⟨x, hx⟩`. Use `⟨hfix, ?_⟩` and prove the remaining obligations. Establish `hgθN : g (θ ^ N) = θ ^ N` using `hfixE _ hθE`.

Establish `hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N`. Take `⟨y, hy⟩` from `hθ₀K`. Rewrite using `[← hy]`. Conclude with `g.commutes y`. Establish `hq : g (θ / θ₀) = θ / θ₀`.

Use `GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_` and prove the remaining obligations. Rewrite using `[div_pow, map_div₀, hgθN, hgθ₀N]`. Rewrite using `[div_pow, div_div]`. Conclude with `hv`. Establish `hq' : g θ₀ = g θ * θ₀ / θ`.

Rewrite `hq` using `[map_div₀]`. Establish `hgθ₀0 : g θ₀ ≠ 0` using `(_root_.map_ne_zero g).mpr hθ₀`. Rewrite `hq` using `[div_eq_div_iff hgθ₀0 hθ₀]`. Rewrite using `[eq_div_iff hθ, hq, mul_comm]`. Establish `hξ : (g θ / θ) ^ N = 1`.

Rewrite using `[div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]`. Take `⟨i, hiN, hi⟩` from `hζ.eq_pow_of_pow_eq_one hξ`. Establish `hval : ((i : ZMod N)).val = i` using `ZMod.val_cast_of_lt hiN`. Establish `h1 : g θ = ζ ^ ((i : ZMod N)).val * θ`. Rewrite using `[hval, hi]`.

Clear the denominators using the available nonvanishing facts. Establish `h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀`. Rewrite using `[hq', h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]`.
-/
theorem inert_fixes_adjoin_and_kum_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      B.valuation (algebraMap K Ω x) = 1 := by
    intro x hx hx' hx0
    refine valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)
    rw [← map_inv₀]; exact hB _ hx'

  have hNK0 : (N : K) ≠ 0 := by
    have : ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K) := map_natCast _ _
    rw [← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')
  have hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K := Subalgebra.natCast_mem _ N
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have := hunit _ hNmem hNinv hNK0
    rwa [map_natCast] at this

  have hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      γ ^ N = algebraMap K Ω x → g γ = γ := by
    intro γ x hx hx' hx0 hγ
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_
    · rw [hγ]; exact g.commutes x
    · rw [one_pow, div_one, hγ]; exact hunit x hx hx' hx0
  have hgα : g α = α := hroot α a ha ha' ha0 hα
  have hgβ : g β = β := hroot β b hb hb' hb0 hβ
  have hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
    have hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
      intro x hx
      have hgx : g x = x := by
        rcases hx with rfl | hx
        · exact hgα
        · rw [Set.mem_singleton_iff.mp hx]; exact hgβ
      have hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := hgx
      intro f
      have hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := Subgroup.zpowers_le.mpr hs f.2
      exact hf
    exact hz (Subgroup.mem_zpowers g)
  have hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x := fun x hx => hfix ⟨x, hx⟩
  refine ⟨hfix, ?_⟩

  have hgθN : g (θ ^ N) = θ ^ N := hfixE _ hθE
  have hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N := by
    obtain ⟨y, hy⟩ := hθ₀K; rw [← hy]; exact g.commutes y
  have hq : g (θ / θ₀) = θ / θ₀ := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_
    · rw [div_pow, map_div₀, hgθN, hgθ₀N]
    · rw [div_pow, div_div]; exact hv
  have hq' : g θ₀ = g θ * θ₀ / θ := by
    rw [map_div₀] at hq
    have hgθ₀0 : g θ₀ ≠ 0 := (_root_.map_ne_zero g).mpr hθ₀
    rw [div_eq_div_iff hgθ₀0 hθ₀] at hq
    rw [eq_div_iff hθ, hq, mul_comm]

  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hval : ((i : ZMod N)).val = i := ZMod.val_cast_of_lt hiN
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [hval, hi]; field_simp
  have h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀ := by
    rw [hq', h1]; field_simp
  rw [kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]

end GlobalTheory.InertKummer
