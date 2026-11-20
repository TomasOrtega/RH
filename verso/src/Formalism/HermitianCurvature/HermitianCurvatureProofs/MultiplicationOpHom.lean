import Formalism.HermitianCurvature.StatementM

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem vz_ne {r : ℕ} : (vz : Var r) ≠ vzb := by
  simp [vz, vzb]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem euler_support {r : ℕ} (v : Var r) (f : Fn r) : (euler v f).support ⊆ f.support := by
  intro γ hγ
  rw [HahnSeries.mem_support] at hγ ⊢
  intro h
  apply hγ
  show ((ofLex γ v : ℤ) : ℂ) * f.coeff γ = 0
  rw [h, mul_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem multiplication_op_hom : Formalism.FourierDecayAlt.M.MulOpHom := by
  intro r f g z
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;>
    simp [mulOp, mul_assoc, add_mul, Algebra.smul_def]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_leibniz : Formalism.FourierDecayAlt.M.EulerLeibniz := by
  intro r v f g
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  ext γ
  rw [hc, HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (Mx1.euler_support v f),
    HahnSeries.coeff_mul_right' g.isPWO_support (Mx1.euler_support v g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [hc, hc, ← hsum, ofLex_add, Pi.add_apply]
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Substitute using the available equality. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem euler_coordinates : Formalism.FourierDecayAlt.M.EulerCoord := by
  intro r v w z
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  constructor
  · ext γ
    rw [hc]
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      simp only [coord, HahnSeries.coeff_single]
      split_ifs with hγ
      · subst hγ
        simp
      · simp
    · rw [if_neg hvw]
      simp only [coord, HahnSeries.coeff_single, HahnSeries.coeff_zero]
      split_ifs with hγ
      · subst hγ
        simp [Pi.single_apply, hvw]
      · simp
  · ext γ
    rw [hc]
    simp only [HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single,
      HahnSeries.coeff_zero, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs with hγ
    · subst hγ
      simp
      left
      rfl
    · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_commute : Formalism.FourierDecayAlt.M.EulerComm := by
  intro r v w
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  refine LinearMap.ext fun f => ?_
  ext γ
  simp only [Module.End.mul_apply, hc]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem eulerMul_statement : Formalism.FourierDecayAlt.M.EulerMul := by
  intro r v f
  refine LinearMap.ext fun g => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [euler_leibniz r v f g, add_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem function_nonzero : Formalism.FourierDecayAlt.M.FnNonzero := by
  intro r v TT
  refine ⟨coord_ne r v, fun h => ?_⟩
  have he : (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1) : Expo r) ≠ 0 := by
    intro h0
    have := congrFun (congrArg ofLex h0) vz
    change ((Pi.single vz (1 : ℤ) + Pi.single vzb 1 : Var r → ℤ) vz) = (0 : Var r → ℤ) vz at this
    simp [Pi.single_apply, vz_ne (r := r)] at this
  have hc := congrArg (fun s : Fn r => s.coeff (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1))) h
  simp [gg, coord, HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single, he] at hc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem level_star : Formalism.FourierDecayAlt.M.LevelStar := by
  intro P L hL
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩ := hL
  have hS := star_generators P
  refine ⟨?_, ?_, ?_⟩
  · rw [hz, hzb]
    exact hS.2.1
  · rw [hn, hns]
    exact hS.2.2.2.2.2
  · rw [hT]
    simp [Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
