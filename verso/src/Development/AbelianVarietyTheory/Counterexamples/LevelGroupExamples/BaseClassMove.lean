import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.BaseClassMove

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem latAdm_unit (l : Level H) (bad n : ℕ) : LatAdm l bad (unitLat E n) := by
  have ht : ∀ m, (unitLat E n).TrivAt m := fun m => ⟨1, by simp, by simp [unitLat], by simp [unitLat]⟩
  refine ⟨fun v => ⟨fun hv w hw => ?_, fun hv => ?_⟩, ht _, ht _⟩
  · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hv j trivial)
      exact ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hw j trivial)
      exact ⟨a, ha⟩
  · intro j _
    have h := hv (Pi.single j 1) (fun i _ => by
      by_cases hi : i = j
      · subst hi; simpa using Submodule.one_le.1 le_rfl
      · simp [Pi.single_eq_of_ne hi])
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    obtain ⟨a, ha⟩ := h
    refine Submodule.mem_one.2 ⟨H.bar a, ?_⟩
    have := H.bar_eq a
    change ((H.bar a : 𝓞 E) : E) = v j
    rw [this]
    change IsCMField.complexConj E (algebraMap _ _ a) = _
    rw [ha, IsCMField.complexConj_apply_apply]

variable (Xo : Moduli Dw l) (c : Coeff l)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Take a linear combination of the given relations to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
theorem shortValAt_beta (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F)
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (T : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * T ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * T := by
    intro S' _ _ φ a b d T
    have hu : algebraMap c.F S' β * algebraMap c.F S' β⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
    simp only [map_mul, AlgHom.commutes, inv_one, map_one]
    constructor
    · intro h; rw [h]; linear_combination (algebraMap c.F S' a * algebraMap c.F S' b * algebraMap c.F S' d * T) * hu
    · intro h; linear_combination (algebraMap c.F S' β⁻¹) * h - φ v * hu
  constructor
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem isBeta_unit (n : ℕ) : IsBeta Dw c (unitLat E n) 1 := by
  have e : (unitLat E n).Ln = (unitLat E n).La := inf_idem _
  refine ⟨one_ne_zero, ?_, fun σ => ?_⟩
  · unfold BetaIs; rw [e, ← Submodule.one_eq_span, one_mul]
  · rw [e]; simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem zetaM_pow : zetaM c ^ l.M = 1 := by
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  unfold zetaM
  rw [← pow_mul, Nat.div_mul_cancel hM]
  apply Subtype.ext
  exact (Complex.isPrimitiveRoot_exp l.M' h0).pow_eq_one

end GlobalTheory.Survey.BaseClassMove
