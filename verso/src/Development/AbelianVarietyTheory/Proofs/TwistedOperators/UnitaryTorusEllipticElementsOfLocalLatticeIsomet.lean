import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem trEll_latticeConj_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n n' P J J' L L' v j hj
  obtain ⟨a, ha, -, hja⟩ := hj
  have iso : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J x φ → IsIsom P (Fv F v) J' x (φ.trans a) := by
    intro x φ h y y'
    have e := ha (φ y) (φ y')
    simp only [GlobalTheory.AdelicU.hLin, hR] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e]
    exact h y y'
  have iso' : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J' x φ → IsIsom P (Fv F v) J x (φ.trans a.symm) := by
    intro x φ h y y'
    have e := ha (a.symm (φ y)) (a.symm (φ y'))
    simp only [GlobalTheory.AdelicU.hLin, hR, LinearEquiv.apply_symm_apply] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← e]
    exact h y y'
  have tor : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
      (h : IsIsom P (Fv F v) J x φ) (t : Tor P (Fv F v)), torEmb (iso x φ h) t = j (torEmb h t) := by
    intro x φ h t
    apply GlobalTheory.AdelicU.matHom_injective (Fv F v) σ J'
    apply Units.ext
    have key : ∀ w, (GlobalTheory.AdelicU.matHom _ σ J' (torEmb (iso x φ h) t)).1 *ᵥ w =
        (GlobalTheory.AdelicU.matHom _ σ J' (j (torEmb h t))).1 *ᵥ w := by
      intro w
      obtain ⟨y, rfl⟩ := (φ.trans a).surjective w
      rw [LinearEquiv.trans_apply, hja]
      change mulMat (φ.trans a) (torUnit t).1 *ᵥ (φ.trans a) y = a (mulMat φ (torUnit t).1 *ᵥ φ y)
      rw [mulMat_mulVec, mulMat_mulVec]
      rfl
    exact Matrix.ext_of_mulVec_single fun i => key _
  refine ⟨?_, fun x φ h => ⟨φ.trans a, iso _ φ h, tor _ φ h _, tor _ φ h⟩⟩
  ext q
  constructor
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a.symm, e, iso' _ φ h⟩
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a, e, iso _ φ h⟩

end GlobalTheory
