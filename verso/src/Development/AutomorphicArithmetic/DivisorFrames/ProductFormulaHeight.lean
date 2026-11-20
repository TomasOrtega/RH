import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

/- English proof (translation)
Establish `h` using `congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)`. Simplify using `only [norm_prod] at h`. Rewrite using `[← Real.log_prod (fun σ _ => by simpa using hN)]`. Use `congr 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖) (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]`.

Simplify using `[← Complex.norm_ratCast]`.
-/
private theorem sum_log_emb (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
  simp only [norm_prod] at h
  rw [← Real.log_prod (fun σ _ => by simpa using hN)]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
    (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp [← Complex.norm_ratCast]

/- English proof (translation)
Establish `h : {θ : K →+* L | θ.comp (algebraMap F K) = algebraMap F L} = Set.range (fun σ : K →ₐ[F] L => (σ : K →+* L))`. Use extensionality with `θ`. Prove the components needed by the constructor for the conclusion. Introduce `hθ`. Conclude with `⟨⟨θ, fun r => RingHom.congr_fun hθ r⟩, rfl⟩`.

Introduce and unpack `⟨σ, rfl⟩`. Conclude with `σ.comp_algebraMap`. Establish `h2` using `finsum_mem_range (f := g) (g := fun σ : K →ₐ[F] L => (σ : K →+* L)) AlgHom.coe_ringHom_injective`. Rewrite `h2` using `[← h]`. Rewrite using `[← finsum_eq_sum_of_fintype, ← h2]`.

Both sides reduce to the same expression.
-/
private theorem finsum_emb (F K L : Type) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] (g : (K →+* L) → ℝ) :
    ∑ᶠ (θ : K →+* L) (_ : θ.comp (algebraMap F K) = algebraMap F L), g θ
      = ∑ σ : K →ₐ[F] L, g (σ : K →+* L) := by
  have h : {θ : K →+* L | θ.comp (algebraMap F K) = algebraMap F L}
      = Set.range (fun σ : K →ₐ[F] L => (σ : K →+* L)) := by
    ext θ
    constructor
    · intro hθ
      exact ⟨⟨θ, fun r => RingHom.congr_fun hθ r⟩, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact σ.comp_algebraMap
  have h2 := finsum_mem_range (f := g) (g := fun σ : K →ₐ[F] L => (σ : K →+* L)) AlgHom.coe_ringHom_injective
  rw [← h] at h2
  rw [← finsum_eq_sum_of_fintype, ← h2]
  rfl

/- English proof (translation)
Introduce `F K _ _ _ _ φ ε c hc`. Use `letI : Algebra F K := φ.toAlgebra`. Use `haveI : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K`. Establish `hN : Algebra.norm F c ≠ 0` using `Algebra.norm_ne_zero_iff.2 hc`.

Establish `key : (fun v : HeightOneSpectrum (𝓞 F) => ∑ᶠ (θ : K →+* AlgebraicClosure F) (_ : θ.comp φ = algebraMap F (AlgebraicClosure F)), Real.log ((ε v).w (θ c))) = fun v => Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F c))`. Use function extensionality and compare the values at `v`. Establish `h1` using `finsum_emb F K (AlgebraicClosure F) (fun θ => Real.log ((ε v).w (θ c)))`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[← Real.log_prod (fun σ _ => by simpa using hc), ← map_prod, ← (ε v).w_alg, Algebra.norm_eq_prod_embeddings F (AlgebraicClosure F) c]`.

Both sides reduce to the same expression. Rewrite using `[key]`. Take `⟨h1, h2⟩` from `GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F _ hN`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[sum_log_emb F _ hN, Algebra.norm_norm]`.

Rewrite using `[sum_log_emb K c hc]`. Conclude with `h2`.
-/
theorem UpperTheory.product_formula_height :
    ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (φ : F →+* K) (ε : ∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.TrueGeo.Ext v) (c : K), c ≠ 0 → (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ᶠ (θ : K →+* AlgebraicClosure F) (_ : θ.comp φ = algebraMap F (AlgebraicClosure F)), Real.log ((ε v).w (θ c))).Finite ∧ ∑ σ : K →+* ℂ, Real.log ‖σ c‖ + ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (θ : K →+* AlgebraicClosure F) (_ : θ.comp φ = algebraMap F (AlgebraicClosure F)), Real.log ((ε v).w (θ c)) = 0 := by
  intro F K _ _ _ _ φ ε c hc
  letI : Algebra F K := φ.toAlgebra
  haveI : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hN : Algebra.norm F c ≠ 0 := Algebra.norm_ne_zero_iff.2 hc
  have key : (fun v : HeightOneSpectrum (𝓞 F) => ∑ᶠ (θ : K →+* AlgebraicClosure F) (_ : θ.comp φ = algebraMap F (AlgebraicClosure F)), Real.log ((ε v).w (θ c))) = fun v => Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F c)) := by
    funext v
    have h1 := finsum_emb F K (AlgebraicClosure F) (fun θ => Real.log ((ε v).w (θ c)))
    refine h1.trans ?_
    rw [← Real.log_prod (fun σ _ => by simpa using hc), ← map_prod, ← (ε v).w_alg,
      Algebra.norm_eq_prod_embeddings F (AlgebraicClosure F) c]
    rfl
  rw [key]
  obtain ⟨h1, h2⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F _ hN
  refine ⟨h1, ?_⟩
  rw [sum_log_emb F _ hN, Algebra.norm_norm] at h2
  rw [sum_log_emb K c hc]
  exact h2
