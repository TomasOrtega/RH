import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import GroundTheory.GlobalFields.TateThesis.AdelicChar

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_nat_mul_integral_at_all_finite_places :
    ∀ (E : Type) [Field E] [NumberField E] (θ : E), ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, d ∣ e → ∀ w : H.P E, Valued.v (H.cp w (rt ((e : E) * θ))) ≤ 1 := by
  intro E _ _ θ
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) θ)).exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : E) * θ) := by
    simpa [zsmul_eq_mul] using hy
  have h1 : IsIntegral ℤ ((y.natAbs : E) * θ) := by
    rcases Int.natAbs_eq y with h | h
    · have hc : ((y.natAbs : E)) = (y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc]
      exact hy'
    · have hc : ((y.natAbs : E)) = -(y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc, neg_mul]
      exact hy'.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rintro e ⟨k, rfl⟩ w
  have hint : IsIntegral ℤ (((y.natAbs * k : ℕ) : E) * θ) := by
    have he : (((y.natAbs * k : ℕ) : E) * θ) = (k : E) * ((y.natAbs : E) * θ) := by
      push_cast
      ring
    rw [he]
    have hk : IsIntegral ℤ (k : E) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact hk.mul h1
  have hm := coe_algebraMap_mem_adicCompletionIntegers w (⟨_, hint⟩ : 𝓞 E)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm
