import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDerivative

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Express the relevant assertion in an equivalent form by its definition. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem evalPoly_congr {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (τ : D.what₂.Tau)
    (hp : ∀ v ∈ p.vars, v.1 ≠ τ) (z z' : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    evalPoly p z = evalPoly p z' := by
  unfold evalPoly
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ p = MvPolynomial.eval₂ (RingHom.id ℂ) _ p
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  have hv : i ∈ p.vars := (MvPolynomial.mem_vars i).2 ⟨c, (MvPolynomial.mem_support_iff).2 hc, hi⟩
  have e := h i.1 (hp i hv)
  simp only [e]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem gAway_congr (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z z' : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    gAway V l s τ z = gAway V l s τ z' := by
  classical
  unfold gAway
  congr 2
  refine Finset.sum_congr rfl (fun τ' hτ' => ?_)
  rw [h τ' (Finset.mem_filter.1 hτ').2]

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem dep (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Ψ x = Ψ x' := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, _, hp, rfl⟩ := hφ
    simp only
    have hf' : (fun i j => finPart D (x i j)) = (fun i j => finPart D (x' i j)) := hf
    rw [evalPoly_congr p τ hp _ _ hx, gAway_congr V l s τ _ _ hx, hf']
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
  | smul c a _ ha => simp only [Pi.smul_apply, ha]

end PositivityTheory.Rg.Sw.Glob.AwayPf
