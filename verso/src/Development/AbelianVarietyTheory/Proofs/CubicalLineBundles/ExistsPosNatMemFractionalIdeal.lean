import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Take `⟨x, hx0, hx⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger ha`. Establish `hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥` using `by simpa using hx0`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))`. Use `⟨Ideal.absNorm (Ideal.span {x}), Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩` and prove the remaining obligations. Establish `h` using `(a : Submodule (𝓞 E) E).smul_mem e hx`.

Rewrite `h` using `[Algebra.smul_def, ← map_mul, he, map_natCast]`. Conclude with `h`.
-/
theorem exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger ha
  have hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥ := by simpa using hx0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨Ideal.absNorm (Ideal.span {x}),
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h := (a : Submodule (𝓞 E) E).smul_mem e hx
  rw [Algebra.smul_def, ← map_mul, he, map_natCast] at h
  exact h

/- English proof (translation)
Use `le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, u, hu, rfl⟩`. Conclude with `Submodule.smul_mem_smul hα hu`.
-/
theorem fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu

/- English proof (translation)
Introduce `E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong`. Establish `hbc : 𝔄b = conjFrac 𝔄`. Use extensionality with `a`. Rewrite using `[mem_conjFrac]`. Conclude with `hb a`.

Substitute `hbc` using the available equality. Establish `hA : 𝔄 ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hone`. Establish `hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ` using `⟨X.Λ_fg, X.Λ_span⟩`.

Establish `hd` using `(perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩`. Establish `hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ) = ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ`. Rewrite using `[hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]`. Use `congr 2`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations.

Rewrite using `[← hone]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hi, hdual⟩` from `hermDual_eq_self_iff.1 hself`. Take `⟨NA, hNA, hNA'⟩` from `exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)`. Take `⟨NC, hNC, hNC'⟩` from `exists_pos_nat_mem_fractionalIdeal hA`.

Establish `hk0 : 0 < k`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Rewrite using `[← habs τ, norm_pos_iff]`. Conclude with `(map_ne_zero τ).2 X.ξ0_ne`. Use `⟨{ toData := X k0 := 2 * k minWeight_pos := by positivity k0_le := by linarith ξ0_abs := fun τ => by rw [habs]; ring EF_int := hint EF_perf := hperf L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ L'_fg := (isLattice_fractionalIdeal_smul (inv_n …` and prove the remaining obligations.

Establish `h` using `Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx`. Rewrite `h` using `[fractionalIdeal_smul_inv_smul hA]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `X.Λ = _`. Rewrite using `[← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]`.
-/
theorem exists_dataX_of_perfect_traceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔄 𝔄b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (k : ℝ) (g : ℕ), (∀ a : E, a ∈ 𝔄b ↔ cc a ∈ 𝔄) → FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * 𝔄b * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = k) → k ≤ 1 → (∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ n : ℤ, EFf X.ξ0 X.Gm x y = n) → (∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y) → 0 < g → (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ) → ∃ Xx : DataX E r, Xx.toData = X ∧ Xx.g = g ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong
  have hbc : 𝔄b = conjFrac 𝔄 := by
    ext a; rw [mem_conjFrac]; exact hb a
  subst hbc
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  have hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hd := (perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩
  have hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) • X.Λ) =
      ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ := by
    rw [hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  obtain ⟨hi, hdual⟩ := hermDual_eq_self_iff.1 hself
  obtain ⟨NA, hNA, hNA'⟩ := exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)
  obtain ⟨NC, hNC, hNC'⟩ := exists_pos_nat_mem_fractionalIdeal hA
  have hk0 : 0 < k := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← habs τ, norm_pos_iff]
    exact (map_ne_zero τ).2 X.ξ0_ne
  refine ⟨{ toData := X
            k0 := 2 * k
            minWeight_pos := by positivity
            k0_le := by linarith
            ξ0_abs := fun τ => by rw [habs]; ring
            EF_int := hint
            EF_perf := hperf
            L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ
            L'_fg := (isLattice_fractionalIdeal_smul (inv_ne_zero hA) hΛ).1
            L'_int := hi
            L'_dual := hdual
            NA := NA
            NC := NC
            NA_pos := hNA
            NC_pos := hNC
            NA_sub := fun x hx => Submodule.smul_mem_smul hNA' hx
            NC_sub := fun x hx => ?_
            g := g
            g_pos := hg
            cong := hcong }, rfl, rfl, ?_⟩
  · have h := Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx
    rwa [fractionalIdeal_smul_inv_smul hA] at h
  · change X.Λ = _
    rw [← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]

end GlobalTheory
