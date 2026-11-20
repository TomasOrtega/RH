import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.PolFin
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem UpperTheory.ConvolutionTheory.G2.lpol_twist {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ)
    (w : Pl E) (g x : GLw n w) :
    UpperTheory.ConvolutionTheory.G3.lpol w (g⁻¹ * x * thL n w g) = UpperTheory.ConvolutionTheory.G3.lpol w x := by
  unfold UpperTheory.ConvolutionTheory.G3.lpol
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hU]
  simpa using Matrix.charpoly_units_conj g⁻¹ (nrmL n w x).val

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem UpperTheory.ConvolutionTheory.G2.exists_supp {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (a b : ℕ)
    (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y : GLw a w × GLw b w, φ y ≠ 0 ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.1 = Q₁ ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.2 = Q₂ := by
  by_contra hno
  apply h
  unfold stTw2 clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hc
  · rw [UpperTheory.ConvolutionTheory.G3.orbZero _ _ _ _ _ ?_, mul_zero]
    rintro y ⟨g, hg⟩
    by_contra hy
    have h1 : y.1 = g.1⁻¹ * c.rep.1 * thL a w g.1 := by rw [hg]; rfl
    have h2 : y.2 = g.2⁻¹ * c.rep.2 * thL b w g.2 := by rw [hg]; rfl
    refine hno ⟨y, hy, ?_, ?_⟩
    · rw [h1, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.1
    · rw [h2, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.2
  · rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
private theorem UpperTheory.ConvolutionTheory.G2.tsupport_unit2 {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) :
    tsupport (UpperTheory.ConvolutionTheory.G2.unit2 a b w) ⊆ (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := by
  refine closure_minimal ?_ ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.isClosed.prod
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2.isClosed)
  intro y hy
  by_contra hn
  exact hy (Set.indicator_of_notMem hn _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.G2.finP :
    UpperTheory.ConvolutionTheory.G2.FinP := by
  intro E _ _ _ hU a b S hS φ hc hae
  have f₁ := UpperTheory.ConvolutionTheory.G3.polFin E hU a S hS (fun w => Prod.fst '' tsupport (φ w))
    (fun w => (hc w).image continuous_fst) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).1)
  have f₂ := UpperTheory.ConvolutionTheory.G3.polFin E hU b S hS (fun w => Prod.snd '' tsupport (φ w))
    (fun w => (hc w).image continuous_snd) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).2)
  refine (f₁.prod f₂).subset ?_
  rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, e₂⟩
