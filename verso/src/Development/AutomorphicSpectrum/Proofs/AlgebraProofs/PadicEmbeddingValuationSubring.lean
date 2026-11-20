import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `F p κ`. Establish `hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖` using `fun a b => IsUltrametricDist.norm_add_le_max a b`. Establish `hone : ‖κ 1‖ = 1` using `by simp`. Set `A : Subring ℂ` to `{ carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1} mul_mem' := by`. Introduce and unpack `_ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩`.

Use `⟨x * y, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ hx (norm_nonneg _) hy`. Use the proof step `one_mem' := ⟨1, by simp, by simp⟩`. Use the proof step `add_mem' := by`.

Introduce and unpack `_ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩`. Use `⟨x + y, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `(hna _ _).trans (max_le hx hy)`. Use the proof step `zero_mem' := ⟨0, by simp, by simp⟩`.

Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨x, rfl, hx⟩`. Conclude with `⟨-x, by simp, by simpa using hx⟩ }`. Set `I : Ideal A` to `{ carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1} add_mem' := by`. Introduce and unpack `a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩`.

Use `⟨x + y, by simp [hxa, hyb], ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `(hna _ _).trans_lt (max_lt hx hy)`. Use the proof step `zero_mem' := ⟨0, by simp, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩`. Use `⟨z * x, by simp [hzc, hxa], ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hI : I ≠ ⊤`.

Introduce `htop`. Establish `h1 : (1 : A) ∈ I` using `by rw [htop]; trivial`. Take `⟨x, hx1, hx⟩` from `h1`. Establish `hx1' : x = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hx1`. Rewrite `hx` using `[hx1', hone]`. Conclude with `lt_irrefl _ hx`. Take `⟨W, hAW, hIW⟩` from `Ideal.image_subset_nonunits_valuationSubring I hI`. Establish `key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits`.

Introduce `x hx`. Establish `hxA : (x : ℂ) ∈ A` using `⟨x, rfl, hx.le⟩`. Conclude with `hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩`. Use `⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩` and prove the remaining obligations. Establish `hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1`.

Rewrite using `[← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)`. Use `key ((p : ℕ) : F) (by simpa using hnorm)` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hlt`.

Establish `hlt' : 1 < ‖κ x‖` using `not_le.mp hlt`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hlt'`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinv : ‖κ x⁻¹‖ < 1`. Rewrite using `[map_inv₀, norm_inv]`. Conclude with `inv_lt_one_of_one_lt₀ hlt'`. Establish `hnu` using `key x⁻¹ hinv`. Rewrite `hnu` using `[ValuationSubring.mem_nonunits_iff]`.

Establish `hle : W.valuation (x : ℂ) ≤ 1` using `(W.valuation_le_one_iff _).2 hxW`. Establish `hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1`. Rewrite using `[← map_mul]`. Establish `: (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1`. Establish `h0 : (x : ℂ) ≠ 0` using `by simpa using hx0`.

Simplify using `[h0]`. Rewrite using `[this, map_one]`. Establish `: W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu`. Conclude with `absurd hprod this.ne`.
-/
theorem exists_valuationSubring_of_padicEmbedding :
    ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]),
      ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧
        ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  intro F p κ
  have hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b =>
    IsUltrametricDist.norm_add_le_max a b
  have hone : ‖κ 1‖ = 1 := by simp
  let A : Subring ℂ :=
    { carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1}
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x * y, by simp, ?_⟩
        rw [map_mul, norm_mul]
        exact mul_le_one₀ hx (norm_nonneg _) hy
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x + y, by simp, ?_⟩
        rw [map_add]
        exact (hna _ _).trans (max_le hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        exact ⟨-x, by simp, by simpa using hx⟩ }
  let I : Ideal A :=
    { carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1}
      add_mem' := by
        rintro a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩
        refine ⟨x + y, by simp [hxa, hyb], ?_⟩
        rw [map_add]
        exact (hna _ _).trans_lt (max_lt hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro ⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩
        refine ⟨z * x, by simp [hzc, hxa], ?_⟩
        rw [map_mul, norm_mul]
        calc ‖κ z‖ * ‖κ x‖ ≤ 1 * ‖κ x‖ := by gcongr
          _ < 1 := by simpa using hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := by rw [htop]; trivial
    obtain ⟨x, hx1, hx⟩ := h1
    have hx1' : x = 1 := by
      apply Subtype.ext
      simpa using hx1
    rw [hx1', hone] at hx
    exact lt_irrefl _ hx
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits := by
    intro x hx
    have hxA : (x : ℂ) ∈ A := ⟨x, rfl, hx.le⟩
    exact hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩
  refine ⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩
  · have hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
        Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have := key ((p : ℕ) : F) (by simpa using hnorm)
    simpa using this
  · by_contra hlt
    have hlt' : 1 < ‖κ x‖ := not_le.mp hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hlt'
      linarith
    have hinv : ‖κ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt'
    have hnu := key x⁻¹ hinv
    rw [ValuationSubring.mem_nonunits_iff] at hnu
    have hle : W.valuation (x : ℂ) ≤ 1 := (W.valuation_le_one_iff _).2 hxW
    have hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1 := by
      rw [← map_mul]
      have : (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1 := by
        have h0 : (x : ℂ) ≠ 0 := by simpa using hx0
        simp [h0]
      rw [this, map_one]
    have : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu
    exact absurd hprod this.ne

end GlobalTheory.CompanionTheory.Ar.Flat
