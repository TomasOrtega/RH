import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
private theorem sg_diag (σ : E ≃+* E) (u : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) u) = diagT E (Fin n) (sgT σ u) := by
  ext i j
  rw [sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp [sgT]
  · simp [Matrix.diagonal_apply_ne _ h]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem diag_inj : Function.Injective (diagT E (Fin n)) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simpa [val_diagT] using this

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem near_val {r : ValueGroupWithZero E} (hr : r < 1) {s : Fin n → Eˣ} (hs : Near r s) (i : Fin n) :
    valuation E (s i : E) = 1 := by
  have h1 : valuation E ((s i : E) - 1) < valuation E (1 : E) := by
    rw [map_one]
    exact lt_of_le_of_lt (hs i) hr
  have h2 := Valuation.map_add_eq_of_lt_right (valuation E) h1
  simpa using h2

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem strict_near {r : ValueGroupWithZero E} (hr : r < 1) {t s : Fin n → Eˣ} (ht : Strict t)
    (hs : Near r s) : Strict (t * s) := by
  have key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E) := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]
  intro i j hij
  rw [key, key]
  exact ht i j hij

/- English proof (translation)
Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem ball_sg {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  simp only [ball, Set.mem_setOf_eq] at ha ⊢
  intro i j
  have h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j
      = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [sg, GeneralLinearGroup.map_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [h, hσ]
  exact ha i j

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules.
-/
private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (hs : Near r s) :
    diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases h : i = j
  · subst h
    simpa using hs i
  · simp [Matrix.diagonal_apply_ne _ h, one_apply_ne h]

end

end UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.suppE :
    UpperTheory.Gal.InertialTypesAlt.L.SuppE := by
  intro E _ _ _ _ n σ q hc r hr0 hr1 A hA
  have hσ : Isom σ := hc.isom
  obtain ⟨K, hK, -, -⟩ := ballSub E n r hr0 hr1
  have bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r := by
    intro a ha b hb
    rw [← hK] at ha hb ⊢
    exact K.mul_mem ha hb
  have binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r := by
    intro a ha
    rw [← hK] at ha ⊢
    exact K.inv_mem ha
  have step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A →
      ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧
        g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    intro δ g hg
    obtain ⟨a, ha, b, hb, t, ht, he⟩ := hg
    obtain ⟨k, hk, s, hs, hks⟩ := contractB E n σ hσ t (hA t ht) r hr1 a ha b hb
    exact ⟨k, hk, t, ht, s, hs, he.trans hks⟩
  refine ⟨?_, ?_⟩
  · intro δ g hg
    obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
    refine ⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩
    calc (g * k⁻¹)⁻¹ * δ * sg σ (g * k⁻¹)
        = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
          rw [map_mul, map_inv]
          group
      _ = diagT E (Fin n) (t * s) := by
          rw [he]
          group
  · intro δ y d hd hy g
    constructor
    · intro hg
      obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
      have hts : Strict (t * s) := UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs
      have hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹)
          = diagT E (Fin n) (t * s) := by
        rw [← hy]
        calc (y⁻¹ * g * k⁻¹)⁻¹ * (y⁻¹ * δ * sg σ y) * sg σ (y⁻¹ * g * k⁻¹)
            = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
              rw [map_mul, map_mul, map_inv, map_inv]
              group
          _ = diagT E (Fin n) (t * s) := by
              rw [he]
              group
      obtain ⟨u, hu⟩ := strictNormal E n σ q hc d (t * s) hd hts _ hx
      have h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s := by
        apply UpperTheory.Gal.InertialTypesAlt.L.diag_inj
        rw [map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]
        exact hx
      refine ⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩
      · have h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s := by
          calc d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = (u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
            _ = s := by
                rw [h2]
                simp
        rw [h3]
        exact hs
      · rw [← hu]
        group
    · rintro ⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩
      have hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) := by
        rw [mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]
      have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
        rw [← hy]
        group
      refine ⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ,
        bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩
      rw [hδ]
      calc (y * diagT E (Fin n) u * κ)⁻¹ * (y * diagT E (Fin n) d * (sg σ y)⁻¹)
            * sg σ (y * diagT E (Fin n) u * κ)
          = κ⁻¹ * ((diagT E (Fin n) u)⁻¹ * diagT E (Fin n) d * sg σ (diagT E (Fin n) u)) * sg σ κ := by
            rw [map_mul, map_mul]
            group
        _ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by
            rw [UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]
        _ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by
            group
