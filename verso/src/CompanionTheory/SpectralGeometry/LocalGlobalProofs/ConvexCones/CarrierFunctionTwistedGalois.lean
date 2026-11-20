import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem twEval_of_isTwG {O : Type} [CommRing O] {w0 : O} {ψ : InvFun O}
    (htw : IsTwG w0 ψ) {σ : O ≃+* O} (hσ : σ w0 = w0) : Tw.TwEval σ ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O Y
  have hsy : ∀ (a : O) (y : Y), τ.symm (σ a • y) = a • τ.symm y := fun a y => by
    apply τ.injective
    rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let s' : (Fin n → O) →ₗ[O] Y' :=
    { toFun := fun x => τ.symm (s fun i => σ (x i))
      map_add' := fun x x' => by
        have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := by ext i; simp
        rw [this, map_add, map_add]
      map_smul' := fun c x => by
        have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := by ext i; simp
        rw [this, map_smul, hsy]
        rfl }
  have hs' : Function.Surjective s' := fun y => by
    obtain ⟨x, hx⟩ := hs (τ y)
    refine ⟨fun i => σ.symm (x i), ?_⟩
    show τ.symm (s fun i => σ (σ.symm (x i))) = y
    simp only [RingEquiv.apply_symm_apply]
    rw [hx, AddEquiv.symm_apply_apply]
  rw [ψ.eval_eq hs', ψ.eval_eq hs]
  have := htw σ hσ n fun a b => B (s a) (s b)
  simpa [s'] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify by unfolding definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isTwG_carFun : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  intro O _ _ _ _ bar w0 hb ψ htw σ hσ n B
  have hc : ∀ a, σ (bar a) = bar (σ a) := hb.comm σ
  have hev : Tw.TwEval σ ψ := twEval_of_isTwG htw hσ
  let τ : (Fin n → O) ≃+ (Fin n → O) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hτ : ∀ (a : O) (y : Fin n → O), τ (a • y) = σ a • τ y := fun a y => by ext i; simp [τ]
  have hτs := Tw.symm_smul hτ
  have hcs := Tw.symm_comm hc
  show (carFun bar ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun bar ψ).toFun n B
  dsimp only [carFun]
  by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b
  · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b :=
      ⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _,
        fun a b => h.choose_spec.2.2 _ _⟩
    rw [dif_pos h, dif_pos h']
    have e : h'.choose = Tw.pullA τ h.choose := LinearMap.ext₂ fun a b => by
      have h1 := h'.choose_spec.2.2 a b
      have h2 := h.choose_spec.2.2 (τ a) (τ b)
      rw [Tw.pullA_apply]
      exact_mod_cast h1.symm.trans h2
    rw [e]
    unfold cdimQ
    congr 2
    refine (Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))
    have := Tw.cdimSet_subset (bar := bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)
    rwa [Tw.pullA_symm_pullA] at this
  · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b := by
      rintro ⟨β, h1, h2, h3⟩
      refine h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩
      rw [Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [dif_neg h, dif_neg h']

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction
