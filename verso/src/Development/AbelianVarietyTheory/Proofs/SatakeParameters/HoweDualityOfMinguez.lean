import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTransposeInverseStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTwistDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTrivialRankZeroStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

section General

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem irr_twist {π : Representation ℂ G V} (h : π.IsIrreducible) (χ : G →* ℂˣ) :
    (twist π χ).IsIrreducible := by
  let E : Subrepresentation (twist π χ) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        have h1 := U.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (U.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h1⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem irr_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem equiv_of_twist {σ : Representation ℂ G V} {σ' : Representation ℂ G V'} (χ : G →* ℂˣ)
    (e : (twist σ χ).Equiv (twist σ' χ)) : Nonempty (σ.Equiv σ') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (σ g v) = σ' g (e.toIntertwiningMap v)
  rw [twist_apply, twist_apply, map_smul] at h1
  exact smul_right_injective V' (Units.ne_zero (χ g)) h1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Simplify to obtain the desired conclusion from the available facts.
-/
theorem equiv_of_comp {σ : Representation ℂ G V} {σ' : Representation ℂ G V'} (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (e : Representation.Equiv (σ.comp θ : Representation ℂ G V) (σ'.comp θ : Representation ℂ G V')) :
    Nonempty (σ.Equiv σ') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (θ g) v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (σ g v) = σ' g (e.toIntertwiningMap v)
  simpa [MonoidHom.coe_comp, Function.comp_apply, hθ] using h1

end General

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_form_ne_zero {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (TensorProduct.map ℓ LinearMap.id x) ≠ 0 := by
  let b := Module.Free.chooseBasis ℂ V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have key : ∀ i (y : V ⊗[ℂ] W),
      TensorProduct.lid ℂ W (TensorProduct.map (b.coord i) LinearMap.id y) = e y i := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, Finsupp.add_apply]
  have hne : e x ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  exact ⟨b.coord i, by rw [key]; simpa using hi⟩

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : ℕ) : GL (Fin n) k →* GL (Fin n) k where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem invT_val (n : ℕ) (g : GL (Fin n) k) : (invT n g).val = (g⁻¹).val.transpose := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem invT_invT (n : ℕ) (g : GL (Fin n) k) : invT n (invT n g) = g := by
  apply Units.ext
  show ((invT n g)⁻¹).val.transpose = g.val
  show (g.val.transpose).transpose = g.val
  rw [Matrix.transpose_transpose]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_invT (n : ℕ) : Continuous (invT (k := k) n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem uniq_left (hM : GlobalTheory.Published.MinguezThetaGL) (r n : ℕ) {V V' W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (σ' : Representation ℂ (GL (Fin r) k) V')
    (τ : Representation ℂ (GL (Fin n) k) W) (hσ : IsSmooth σ) (hσi : σ.IsIrreducible)
    (hσ' : IsSmooth σ') (hσ'i : σ'.IsIrreducible) (hτ : IsSmooth τ) (hτi : τ.IsIrreducible)
    (h1 : OmQuot 1 σ τ) (h2 : OmQuot 1 σ' τ) : Nonempty (σ.Equiv σ') := by
  by_cases h0 : r = 0 ∨ n = 0
  · obtain ⟨⟨a⟩, -⟩ := GlobalTheory.T.om_quotient_trivial_rank_zero k r n V W σ τ h0 hσi hτi h1
    obtain ⟨⟨b⟩, -⟩ := GlobalTheory.T.om_quotient_trivial_rank_zero k r n V' W σ' τ h0 hσ'i hτi h2
    exact ⟨a.trans b.symm⟩
  · push_neg at h0
    obtain ⟨F, hF0, hF⟩ := h1
    obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ, F Φ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hF0 (LinearMap.ext h)
    obtain ⟨ℓ, hℓ⟩ := exists_form_ne_zero hΦ₀
    let f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W :=
      (TensorProduct.lid ℂ W).toLinearMap ∘ₗ TensorProduct.map ℓ LinearMap.id ∘ₗ F
    have hf0 : f ≠ 0 := fun h => hℓ (LinearMap.congr_fun h Φ₀)
    have hf : ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
        (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om 1 (1 : GL (Fin r) k) h Φ → f Φ' = τ h (f Φ) := by
      intro h Φ Φ' hΦ
      have e1 := hF 1 h Φ Φ' hΦ
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, map_one]
      generalize F Φ = x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v w => simp
      | add y z hy hz => simp only [map_add, hy, hz]
    obtain ⟨V0, _, _, π', -, -, -, hU, -⟩ :=
      hM k n r (Nat.one_le_iff_ne_zero.2 h0.2) (Nat.one_le_iff_ne_zero.2 h0.1) W τ hτ hτi ⟨f, hf0, hf⟩
    obtain ⟨a⟩ := hU V σ hσ hσi ⟨F, hF0, hF⟩
    obtain ⟨b⟩ := hU V' σ' hσ' hσ'i h2
    exact ⟨a.trans b.symm⟩

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem main : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  intro hM k _ _ _ _ r n μ hμ
  have hr : IsSmoothChar (detChar (Fin r) μ⁻¹) := hμ.inv.detChar
  have hn : IsSmoothChar (detChar (Fin n) μ) := hμ.detChar
  refine ⟨?_, ?_⟩
  · intro V W W' _ _ _ _ _ _ σ τ τ' hσ hσi hτ hτi hτ' hτ'i h1 h2
    have h1' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W σ τ).1 h1
    have h2' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W' σ τ').1 h2
    have t1 := GlobalTheory.T.om_quotient_transpose_inverse k r n V W _ _ (invT r) (invT n) (fun _ => rfl) (fun _ => rfl) h1'
    have t2 := GlobalTheory.T.om_quotient_transpose_inverse k r n V W' _ _ (invT r) (invT n) (fun _ => rfl) (fun _ => rfl) h2'
    have hs : ∀ m : ℕ, Function.Surjective (invT (k := k) m) := fun m g => ⟨invT m g, invT_invT m g⟩
    obtain ⟨e⟩ := uniq_left hM n r _ _ _
      (isSmooth_comp (isSmooth_twist hτ hn) _ (continuous_invT n)) (irr_comp _ (hs n) (irr_twist hτi _))
      (isSmooth_comp (isSmooth_twist hτ' hn) _ (continuous_invT n)) (irr_comp _ (hs n) (irr_twist hτ'i _))
      (isSmooth_comp (isSmooth_twist hσ hr) _ (continuous_invT r)) (irr_comp _ (hs r) (irr_twist hσi _))
      t1 t2
    obtain ⟨e'⟩ := equiv_of_comp (invT n) (invT_invT n) e
    exact equiv_of_twist _ e'
  · intro V V' W _ _ _ _ _ _ σ σ' τ hσ hσi hσ' hσ'i hτ hτi h1 h2
    have h1' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W σ τ).1 h1
    have h2' := (GlobalTheory.T.om_quotient_twist_det k r n μ V' W σ' τ).1 h2
    obtain ⟨e⟩ := uniq_left hM r n _ _ _
      (isSmooth_twist hσ hr) (irr_twist hσi _) (isSmooth_twist hσ' hr) (irr_twist hσ'i _)
      (isSmooth_twist hτ hn) (irr_twist hτi _) h1' h2'
    exact equiv_of_twist _ e

end GlobalTheory.HoweBridge
