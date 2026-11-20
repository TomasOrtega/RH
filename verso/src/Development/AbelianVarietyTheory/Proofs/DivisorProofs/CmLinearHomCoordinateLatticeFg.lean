import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefiniteStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem lat_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, hG, hdet⟩ := GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite E H hH K ρ σ₁ p X
  set N : 𝓞 E := H.bar.symm gP.det with hNdef
  have hN0 : N ≠ 0 := fun h => hdet (by simpa [hNdef] using congrArg H.bar h)
  have hN : (N : E) ≠ 0 := by exact_mod_cast hN0
  have key : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ b, ∃ z : 𝓞 E, (z : E) = (N : E) * c b := by
    rintro c ⟨n, hn, x, hx, f, hf, hfx⟩ b
    choose y hy using GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow E H hH K ρ σ₁ p 0 X gP gQ hG n x f hn hf hfx
    have hmv : gP.mulVec (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * y a := by
      funext a; simp [Matrix.mulVec, dotProduct, hy]
    have hadj : gP.det • (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * gP.adjugate.mulVec y a := by
      have := congrArg gP.adjugate.mulVec hmv
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [this]; funext a; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    have hb := congrArg H.bar.symm (congrFun hadj b)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, map_natCast] at hb
    refine ⟨H.bar.symm (gP.adjugate.mulVec y b), ?_⟩
    have hnE : ((n : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hnE
    have h2 : ((N : 𝓞 E) : E) * ((x b : 𝓞 E) : E) =
        (n : E) * ((H.bar.symm (gP.adjugate.mulVec y b) : 𝓞 E) : E) := by
      rw [hNdef]; exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hb
    push_cast
    rw [← h2, hx b]; ring
  let incl : (Fin p → 𝓞 E) →ₗ[𝓞 E] (Fin p → E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)
  let scal : (Fin p → E) →ₗ[𝓞 E] (Fin p → E) := N • LinearMap.id
  have hscal : Function.Injective scal := by
    intro v w h
    funext i
    have := congrFun h i
    simp only [scal, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hN this
  apply Submodule.fg_of_fg_map_injective scal hscal
  refine Submodule.FG.of_le (T := LinearMap.range incl) ?_ ?_
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map incl
  · rw [GlobalTheory.FlatCM.HomLat.lat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    choose z hz using key c hc
    refine ⟨z, ?_⟩
    funext b
    simp [incl, scal, hz, Algebra.smul_def]

end GlobalTheory.FlatCM.HomLat

end
