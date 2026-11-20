import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hU hW hth hD κ γ hκf hκ hs h`. Substitute `hr` using the available equality. Take `⟨γ₁, hγ₁, hΛ₁, hm₁, hfr₁⟩` from `hD.2 h`. Take `⟨γ₂, hγ₂, hΛ₂, hm₂, hfr₂⟩` from `hD.2 (h * κ)`. Take `⟨δ, hδu, hδf, hδa⟩` from `GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))`.

Establish `hκ' : latGHat V κ = latGHat V 1`. Use `((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.1 1 1 κ hκ).2` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `hprod : γ₂ * γ₁⁻¹ * (γ₁ * h) * κ = γ₂ * (h * κ)` using `by group`. Take `⟨gam, -, t₁, hgam⟩` from `GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _ (φ _) (φ _) (F.t _) (F.t _) γ (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hD.1.1 _) (hD.1.1 _) δ hδu hδf hκ' (fun a ha => by`.

Take `⟨w, hw, ew⟩` from `hs a ha`. Conclude with `⟨w, hw, sub_eq_iff_eq_add'.1 ew⟩) ⟨hΛ₁, hm₁⟩ (by rw [hprod]; exact ⟨hΛ₂, hm₂⟩)`. Establish `hG : ∀ k, (U.X k).Gm = -V.gramᵀ` using `fun k => (hW k).1`. Establish `hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v` using `fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `hm : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ`.

Use `⟨Finset.ext fun τ => ?_, ?_, (hW _).2.trans (hW _).2.symm, fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(hU.2.1 _).2 τ, (hU.2.1 _).2 τ]`. Rewrite using `[(hU.2.1 _).1, (hU.2.1 _).1]`. Rewrite using `[hG, hG]`. Conclude with `hδu u v`.

Use `hgam ((φ _).symm ⟨v, hv⟩)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Conclude with `this ▸ (φ _ _).2`. Use `hgam (gam.symm ((φ _).symm ⟨_, hv⟩))` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.

Establish `e₁` using `congrArg (fun w => (δ⁻¹).1 *ᵥ w) this`. Simplify using `only [hli] at e₁`. Conclude with `e₁ ▸ (φ _ _).2`. Use `⟨δ, hm, funext fun τ => ?_, gam, hgam, t₁⟩` and prove the remaining obligations. Take `⟨θ, hθ⟩` from `(GlobalTheory.Member.infiniteAdele_bijective D).1`.

Take `⟨hAr, -, -⟩` from `GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ`. Establish `h1` using `hfr₁ ⟨τ.1, hm.mem τ⟩`. Establish `h2` using `hfr₂ τ`. Rewrite `h1` using `[GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ ⟨τ.1, hm.mem τ⟩) (hθ τ.1)]`. Rewrite `h2` using `[GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ τ) (hθ τ.1), ← hprod, (hAr τ.1).2.1, (hAr τ.1).2.1, (hAr τ.1).2.2.1 κ hκf, hδa τ.1 _ (hθ τ.1), Matrix.mul_one]`.

Express the relevant statement in the definitionally equal form `mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hm.mem τ⟩`. Rewrite using `[h1, h2, ← Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem dict_mul_markRel : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsUnf U → (∀ k, ModelW V hr (U.X k)) → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictLat U V hr dict io e F ik φ th x₀ → ∀ (κ : GA D V) (γ : Dw.La →ₗ[𝓞 D.host.E] Dw.La), κ ∈ GfC V → FinCong V 1 κ → (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) - finVec V (io (γ a)) = (l.M : ℕ) • w) → ∀ h : GA D V, ∃ (δ : GL (Fin r) D.host.E) (hm : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ), (dict (h * κ)).2 = lact δ (castFr hm.psi (dict h).2) ∧ MarkRel l (φ (dict h).1) (φ (dict (h * κ)).1) (F.t (ik (dict h).1)) (F.t (ik (dict (h * κ)).1)) γ δ := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hU hW hth hD κ γ hκf hκ hs h
  subst hr
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hfr₁⟩ := hD.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hfr₂⟩ := hD.2 (h * κ)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  have hκ' : latGHat V κ = latGHat V 1 := by
    have := ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.1 1 1 κ hκ).2
    rwa [one_mul] at this
  have hprod : γ₂ * γ₁⁻¹ * (γ₁ * h) * κ = γ₂ * (h * κ) := by group
  obtain ⟨gam, -, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) γ (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hD.1.1 _) (hD.1.1 _) δ hδu hδf hκ'
    (fun a ha => by
      obtain ⟨w, hw, ew⟩ := hs a ha
      exact ⟨w, hw, sub_eq_iff_eq_add'.1 ew⟩) ⟨hΛ₁, hm₁⟩ (by rw [hprod]; exact ⟨hΛ₂, hm₂⟩)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hm : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ?_, ?_, (hW _).2.trans (hW _).2.symm, fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [(hU.2.1 _).2 τ, (hU.2.1 _).2 τ]
    · rw [(hU.2.1 _).1, (hU.2.1 _).1]
    · rw [hG, hG]
      exact hδu u v
    · have := hgam ((φ _).symm ⟨v, hv⟩)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ (φ _ _).2
    · have := hgam (gam.symm ((φ _).symm ⟨_, hv⟩))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      have e₁ := congrArg (fun w => (δ⁻¹).1 *ᵥ w) this
      simp only [hli] at e₁
      exact e₁ ▸ (φ _ _).2
  refine ⟨δ, hm, funext fun τ => ?_, gam, hgam, t₁⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have h1 := hfr₁ ⟨τ.1, hm.mem τ⟩
  have h2 := hfr₂ τ
  rw [GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ ⟨τ.1, hm.mem τ⟩) (hθ τ.1)] at h1
  rw [GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ τ) (hθ τ.1), ← hprod, (hAr τ.1).2.1, (hAr τ.1).2.1,
    (hAr τ.1).2.2.1 κ hκf, hδa τ.1 _ (hθ τ.1), Matrix.mul_one] at h2
  change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hm.mem τ⟩
  rw [h1, h2, ← Matrix.mul_assoc]
  rfl

end GlobalTheory.GeoLevel
