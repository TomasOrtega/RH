import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRealLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRealLineSmoothStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

namespace GlobalTheory.ThK.ZFinDer

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem I_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (h k : UA σ W.J) : M.I om Φ (h * k) = M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1; funext g
  have : ((g, h * k) : UA σ X.J × UA σ W.J) = (g, h) * (1, k) := by simp
  rw [this, map_mul, Module.End.mul_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem derivs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ l : List (ℝ → GAd σ (c • G.W.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • G.W.J.map σ) γ) →
      (l.map (back hσ G.W.J hc)).foldr (derR om) Φ ∈ GlobalTheory.ThK.PolData B G.M ∧
      l.foldr lineDer (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
        fun x => G.M.I om ((l.map (back hσ G.W.J hc)).foldr (derR om) Φ) ((toGAd hσ G.W.J hc).symm x) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ l hl
  induction l with
  | nil => exact ⟨by simpa using hΦ, by simp⟩
  | cons γ l ih =>
    obtain ⟨hP, hE⟩ := ih (fun γ' h' => hl γ' (List.mem_cons_of_mem _ h'))
    have hγ := hl γ List.mem_cons_self
    refine ⟨by simpa using GlobalTheory.T.theta_integral_real_line_derivative F E σ hσ B a a' G X om om' hK hT c hc hcc _ hP γ hγ, ?_⟩
    simp only [List.foldr_cons, List.map_cons]
    rw [hE]
    funext x
    simp only [lineDer]
    have : (fun t => G.M.I om ((l.map (back hσ G.W.J hc)).foldr (derR om) Φ) ((toGAd hσ G.W.J hc).symm (x * γ t))) =
        fun t => G.M.I om (om (1, back hσ G.W.J hc γ t) ((l.map (back hσ G.W.J hc)).foldr (derR om) Φ))
          ((toGAd hσ G.W.J hc).symm x) := by
      funext t; rw [map_mul, I_mul]; rfl
    rw [this]
    exact (GlobalTheory.T.theta_integral_real_line_smooth F E σ hσ B a a' G X om om' hK hT c hc hcc _ hP γ hγ _).deriv

end GlobalTheory.ThK.ZFinDer
