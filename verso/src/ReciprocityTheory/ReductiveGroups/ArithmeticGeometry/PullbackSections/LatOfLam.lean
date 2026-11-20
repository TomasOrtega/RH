import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.TB

/- English proof (translation)
Introduce `D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2`. Set `Nf : NormFam B.KO (B.Cusp j ka)` to `{ N := B.supN j ka nonneg := B.supN_nonneg j ka eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h smul := B.supN_smul j ka add := B.supN_add j ka }`. Establish `hPL : ProdLower Nf (B.Mlat j ka) ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size))`. Introduce `f hf hne`. Establish `h1` using `hlam f hf hne`.

Unfold `WeightFamilies.meanLogSup at h1`. Distinguish the cases in `hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0`. Establish `hc' : Fintype.card (B.KO →+* ℂ) = 0` using `by exact_mod_cast hc`. Establish `hempty : IsEmpty (B.KO →+* ℂ)` using `Fintype.card_eq_zero_iff.mp hc'`. Rewrite using `[hc, zero_mul, neg_zero]`.

Simplify using the standard rewrite rules. Establish `hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ)` using `lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)`. Establish `h2` using `(le_div_iff₀ hpos).mp h1`. Use `show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hUD` using `discriminant_of_product_lower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL`. Establish `hFG` using `formalGroup_of_discriminant B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD`. Use `⟨hFG, ?_⟩` and prove the remaining obligations. Use `set c : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n) with hc`. Establish `hc0 : c ≠ 0`.

Use `pow_ne_zero _ ?_` and prove the remaining obligations. Establish `: (D.host.g 0 * D.host.g 1 : ℕ) ≠ 0` using `Nat.mul_ne_zero (hg 0).ne' (hg 1).ne'`. Conclude with `this` after adjusting the coercions. Establish `hsc : ((S.sK * c : 𝓞 B.KO) : B.KO) ≠ 0`. Introduce `h0`.

Conclude with `mul_ne_zero hs hc0 (by exact_mod_cast h0)`. Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_le.mpr fun x hx => ?_` and prove the remaining obligations. Establish `hmem : (S.sK * c : 𝓞 B.KO) • x ∈ B.Mlat j ka`. Apply `hH2.2.2.2` to reduce the goal to its premises.

Simplify using `only [WeightAlgebra.PJ.Thc, WeightAlgebra.PJ.scaled]`. Use `⟨c • x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[mul_smul]`. Establish `hx' : x = ((S.sK * c : 𝓞 B.KO) : B.KO)⁻¹ • (((S.sK * c : 𝓞 B.KO) : B.KO) • x)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hsc, one_smul]`. Rewrite using `[hx']`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `: (((S.sK * c : 𝓞 B.KO) : B.KO) • x) = (S.sK * c : 𝓞 B.KO) • x` using `algebraMap_smul B.KO _ x`. Rewrite using `[this]`.

Conclude with `Submodule.subset_span hmem`.
-/
theorem latOfLam : LatOfLamSt := by
  intro D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2
  let Nf : NormFam B.KO (B.Cusp j ka) :=
    { N := B.supN j ka
      nonneg := B.supN_nonneg j ka
      eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h
      smul := B.supN_smul j ka
      add := B.supN_add j ka }
  have hPL : ProdLower Nf (B.Mlat j ka)
      ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size)) := by
    intro f hf hne
    have h1 := hlam f hf hne
    unfold WeightFamilies.meanLogSup at h1
    by_cases hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0
    · have hc' : Fintype.card (B.KO →+* ℂ) = 0 := by exact_mod_cast hc
      have hempty : IsEmpty (B.KO →+* ℂ) := Fintype.card_eq_zero_iff.mp hc'
      rw [hc, zero_mul, neg_zero]
      simp
    · have hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ) :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have h2 := (le_div_iff₀ hpos).mp h1
      show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)
      linarith
  have hUD := discriminant_of_product_lower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL
  have hFG := formalGroup_of_discriminant B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD
  refine ⟨hFG, ?_⟩
  set c : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n) with hc
  have hc0 : c ≠ 0 := by
    refine pow_ne_zero _ ?_
    have : (D.host.g 0 * D.host.g 1 : ℕ) ≠ 0 := Nat.mul_ne_zero (hg 0).ne' (hg 1).ne'
    exact_mod_cast this
  have hsc : ((S.sK * c : 𝓞 B.KO) : B.KO) ≠ 0 := by
    intro h0
    exact mul_ne_zero hs hc0 (by exact_mod_cast h0)
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.mpr fun x hx => ?_
  have hmem : (S.sK * c : 𝓞 B.KO) • x ∈ B.Mlat j ka := by
    apply hH2.2.2.2
    simp only [WeightAlgebra.PJ.Thc, WeightAlgebra.PJ.scaled]
    refine ⟨c • x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [mul_smul]
  have hx' : x = ((S.sK * c : 𝓞 B.KO) : B.KO)⁻¹ • (((S.sK * c : 𝓞 B.KO) : B.KO) • x) := by
    rw [smul_smul, inv_mul_cancel₀ hsc, one_smul]
  rw [hx']
  refine Submodule.smul_mem _ _ ?_
  have : (((S.sK * c : 𝓞 B.KO) : B.KO) • x) = (S.sK * c : 𝓞 B.KO) • x := algebraMap_smul B.KO _ x
  rw [this]
  exact Submodule.subset_span hmem

end ReciprocityTheory.ChartRestriction.G.PullbackSections
