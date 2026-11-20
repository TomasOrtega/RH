import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot

section Cont

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Use `continuous_of_continuousAt_zero σ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]`. Use `fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]` and apply the resulting hypothesis.
-/
theorem continuous_of_v_eq (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const`.
-/
theorem continuous_nU_val : Continuous fun x : L => ((nU x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;> first | exact continuous_id | exact continuous_const | exact continuous_neg`.
-/
theorem continuous_nU_inv_val :
    Continuous fun x : L => (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;>
    first | exact continuous_id | exact continuous_const | exact continuous_neg

/- English proof (translation)
Unfold `partner cT`. Conclude with `(continuous_const.matrix_mul (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const`.
-/
theorem continuous_partner_nU (σ : L →+* L) (hc : Continuous σ) :
    Continuous fun x : L => partner σ (nU x) := by
  unfold partner cT
  exact (continuous_const.matrix_mul
    (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const

/- English proof (translation)
Simplify using `only [uR, rootHom_val, blockM]`. Conclude with `(continuous_const.add (((continuous_const.matrix_mul (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add ((continuous_const.matrix_mul ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)`.
-/
theorem continuous_uR_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (a : ℕ)
    (h : 2 * (a + 2) ≤ n) :
    Continuous fun x : L => (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  simp only [uR, rootHom_val, blockM]
  exact (continuous_const.add (((continuous_const.matrix_mul
    (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul
    ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)

/- English proof (translation)
Establish `h0 : uR σ hσ a h (0 : L) = 1`. Establish `e : nU (0 : L) = 1`. Apply the tactic sequence `ext p r; fin_cases p <;> fin_cases r <;> simp [nU]`. Simplify using `only [uR, e, map_one]`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[← uR_add, add_neg_cancel, h0]`.
-/
theorem uR_neg (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) :
    (uR σ hσ a h x)⁻¹ = uR σ hσ a h (-x) := by
  have h0 : uR σ hσ a h (0 : L) = 1 := by
    have e : nU (0 : L) = 1 := by
      ext p r; fin_cases p <;> fin_cases r <;> simp [nU]
    simp only [uR, e, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← uR_add, add_neg_cancel, h0]

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU a h`. Establish `hc : Continuous σ` using `continuous_of_v_eq σ hU.2.1`. Use `Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _` and prove the remaining obligations. Use `Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)` using `fun x => by`.

Rewrite using `[← uR_neg, Subgroup.coe_inv]`. Simplify using `only [e]`. Conclude with `(continuous_uR_val σ hU.1 hc a h).comp continuous_neg`.
-/
theorem continuous_uR : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    Continuous (uR σ hU.1 a h : L → GU σ n) := by
  intro L _ _ ϖ σ q n hU a h
  have hc : Continuous σ := continuous_of_v_eq σ hU.2.1
  refine Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _
  refine Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩
  have e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun x => by
    rw [← uR_neg, Subgroup.coe_inv]
  simp only [e]
  exact (continuous_uR_val σ hU.1 hc a h).comp continuous_neg

end Cont

end GlobalTheory.CompanionTheory.SwapRoot

end
