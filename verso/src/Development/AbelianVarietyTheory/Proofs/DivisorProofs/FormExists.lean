import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockInvariantSubspaceEquivariantProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRankEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionCommutesWithEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerRightCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedUpperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointUpperBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointLowerBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasFormStatement

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

/- English proof (translation)
The claim follows from `GlobalTheory.T.fock_invariant_subspace_equivariant_projection p q r s W hW hg`.
-/
theorem L_proj (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hW : ∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) (hg : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := GlobalTheory.T.fock_invariant_subspace_equivariant_projection p q r s W hW hg

/- English proof (translation)
The claim follows from `GlobalTheory.T.homogeneous_component_in_range_embedding P Q R h k G n`.
-/
theorem L_grad (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := GlobalTheory.T.homogeneous_component_in_range_embedding P Q R h k G n

/- English proof (translation)
The claim follows from `GlobalTheory.T.injective_rank_embedding P Q R h k`.
-/
theorem L_inj (P Q R : ℕ) (h : P ≤ R) (k : ℕ) : Function.Injective (embR P Q R h k) := GlobalTheory.T.injective_rank_embedding P Q R h k

/- English proof (translation)
Apply the tactic sequence `rcases i with a | b <;> rcases j with a' | b'`. Conclude with `GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G`. Conclude with `GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G`. Conclude with `GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G`. Conclude with `GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G`.
-/
theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G
  · exact GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G
  · exact GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G
  · exact GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G

/- English proof (translation)
Apply the tactic sequence `rcases i with a | b <;> rcases j with a' | b'`. Conclude with `GlobalTheory.T.fischer_pairing_adjoint_upper_block P Q S h k' a a' G f`. Conclude with `GlobalTheory.T.fischer_pairing_adjoint_mixed_upper P Q S h k' a b' G f`. Conclude with `GlobalTheory.T.fischer_pairing_adjoint_mixed_lower P Q S h k' a' b G f`. Conclude with `GlobalTheory.T.fischer_pairing_adjoint_lower_block P Q S h k' b b' G f`.
-/
theorem L_actS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (i j : Ix P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab i j) f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' i j G)) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fischer_pairing_adjoint_upper_block P Q S h k' a a' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_upper P Q S h k' a b' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_lower P Q S h k' a' b G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_lower_block P Q S h k' b b' G f

/- English proof (translation)
The claim follows from `GlobalTheory.T.nonzero_equivariant_pairing_has_form P Q R S x b hb hinv`.
-/
theorem L_tensor (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ) (hb : b ≠ 0)
    (hinv : ∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) :
    GlobalTheory.RealLift.HasForm P Q R S x := GlobalTheory.T.nonzero_equivariant_pairing_has_form P Q R S x b hb hinv

/- English proof (translation)
The claim follows from `detS_ne_zero P Q S h`.
-/
theorem L_detS (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := detS_ne_zero P Q S h

/- English proof (translation)
Establish `hk' : ((S + k' : ℕ) : ℂ) = ((R + k : ℕ) : ℂ)` using `by rw [hk]`. Establish `hk2 : (k' : ℂ) = R + k - S`. Use `congrArg (fun n : ℕ => (n : ℂ)) hk` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.

Apply the tactic sequence `rcases i with a | b <;> rcases j with a' | b'`. Simplify using `only [opR, opS, Sum.inl.injEq] split_ifs with hh`. Rewrite using `[hx]`. Use `module`. Simplify using the standard rewrite rules.

Simplify using `[opR, opS]`. Simplify using `only [opR, opS, hk', reduceCtorEq, if_false, zero_smul]`. Normalize the expressions using the abelian group laws. Simplify using `only [opR, opS, Sum.inr.injEq] split_ifs with hh`. Rewrite using `[hx, hk2]`.

Use `module`. Simplify using the standard rewrite rules.
-/
theorem op_sum' (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (i j : Ix P Q) :
    opR P Q R k i j + opS P Q S k' i j = (if i = j then x else 0) • (1 : Module.End ℂ (Mdl P Q)) := by
  have hk' : ((S + k' : ℕ) : ℂ) = ((R + k : ℕ) : ℂ) := by rw [hk]
  have hk2 : (k' : ℂ) = R + k - S := by
    have := congrArg (fun n : ℕ => (n : ℂ)) hk; push_cast at this; linear_combination this
  rcases i with a | b <;> rcases j with a' | b'
  · simp only [opR, opS, Sum.inl.injEq]
    split_ifs with hh
    · rw [hx]; module
    · simp
  · simp [opR, opS]
  · simp only [opR, opS, hk', reduceCtorEq, if_false, zero_smul]
    abel
  · simp only [opR, opS, Sum.inr.injEq]
    split_ifs with hh
    · rw [hx, hk2]; module
    · simp

/- English proof (translation)
Establish `h : actR P Q R k Z + actS P Q S k' Z = (x * Z.trace) • (1 : Module.End ℂ (Mdl P Q))`. Rewrite using `[actR_apply, actS_apply, ← Finset.sum_add_distrib]`. Repeatedly rewrite using `[← Finset.sum_add_distrib, ← smul_add, op_sum' P Q R S k k' x hk hx, smul_smul, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_smul]`. Use `congr 1`. Simplify using `[Matrix.trace, Finset.mul_sum, mul_comm, mul_add]`.

Rewrite using `[← LinearMap.add_apply, h]`. Simplify using the standard rewrite rules.
-/
theorem act_sum (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (Z : Mat P Q) (G : Mdl P Q) :
    actR P Q R k Z G + actS P Q S k' Z G = (x * Z.trace) • G := by
  have h : actR P Q R k Z + actS P Q S k' Z = (x * Z.trace) • (1 : Module.End ℂ (Mdl P Q)) := by
    rw [actR_apply, actS_apply, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← smul_add, op_sum' P Q R S k k' x hk hx, smul_smul, mul_ite, mul_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_smul]
    congr 1
    simp [Matrix.trace, Finset.mul_sum, mul_comm, mul_add]
  rw [← LinearMap.add_apply, h]; simp

/- English proof (translation)
Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Simplify using `[Eab, Matrix.smul_single]`.
-/
theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

/- English proof (translation)
Use `conv_lhs => rw [mat_eq_sum Z]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]`.
-/
theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

/- English proof (translation)
Use `conv_lhs => rw [mat_eq_sum Z]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actS, actS_apply, smul_eq_mul]`.
-/
theorem actS_full (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (Z : Mat P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S Z f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (actS P Q S k' Z G)) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actS, actS_apply, smul_eq_mul]

/- English proof (translation)
Introduce `P Q R S x k k' hP hQ _ _ hk hk'`. Establish `hkk : S + k' = R + k`. Establish `h1 : ((S + k' : ℕ) : ℚ) = ((R + k : ℕ) : ℚ)` using `by push_cast; rw [← hk, ← hk']; unfold cPair; ring`. Conclude with `h1` after adjusting the coercions. Establish `hx : (x : ℂ) = k + (R : ℂ) / 2 - (S : ℂ) / 2`.

Establish `: x = k + (R : ℚ) / 2 - (S : ℚ) / 2` using `by rw [← hk]; unfold cPair; ring`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set e := embR P Q R hP k`.

Establish `hinj` using `L_inj P Q R hP k`. Take `⟨π, hπW, hπid, hπeq⟩` from `L_proj P Q R 0 (LinearMap.range e) (by rintro Z _ ⟨G, rfl⟩; exact ⟨_, (actR_full P Q R hP k Z G).symm⟩) (by rintro _ ⟨G, rfl⟩ n; exact L_grad P Q R hP k G n)`. Set `eq` to `LinearEquiv.ofInjective e hinj`. Set `κ : Pol P Q R 0 →ₗ[ℂ] Mdl P Q` to `eq.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ π hπW`. Establish `hκ : ∀ f, e (κ f) = π f`.

Introduce `f`. Use `eq.apply_symm_apply ⟨π f, hπW f⟩` as an intermediate fact. Simplify `congrArg Subtype.val this` using `[eq, κ]`. Establish `hκeq : ∀ Z f, κ (fockAct1 P Q R 0 Z f) = actR P Q R k Z (κ f)`. Introduce `Z f`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hκ, hπeq, ← hκ, actR_full]`. Establish `hκ1 : κ (e 1) = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hκ, hπid _ ⟨1, rfl⟩]`.

Set `b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ` to `GlobalTheory.DefLift.BilFischer.pair.flip ∘ₗ (embS P Q S hQ k') ∘ₗ κ`. Establish `hb : ∀ f g, b f g = GlobalTheory.DefLift.BilFischer.pair g (embS P Q S hQ k' (κ f))` using `fun _ _ => rfl`. Apply `L_tensor P Q R S x b` to reduce the goal to its premises. Introduce `h0`. Establish `hne : embS P Q S hQ k' 1 ≠ 0`.

Simplify using `only [embS, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one, LinearMap.mulRight_apply, one_mul]`. Conclude with `pow_ne_zero _ (L_detS P Q S hQ)`. Apply `hne` to reduce the goal to its premises. Apply `GlobalTheory.DefLift.BilFischer.pair_nondeg` to reduce the goal to its premises. Introduce `g`.

Use `congrArg (fun t => t (e 1) g) h0` as an intermediate fact. Simplify `this` using `[hb, hκ1]`. Introduce `Z f g`. Rewrite using `[hb, hb, hb, hκeq, actS_full, ← map_add, ← map_add, act_sum P Q R S k k' x hkk hx, map_smul, map_smul, smul_eq_mul]`.
-/
theorem formEx : GlobalTheory.RealLift.FormEx := by
  intro P Q R S x k k' hP hQ _ _ hk hk'
  have hkk : S + k' = R + k := by
    have h1 : ((S + k' : ℕ) : ℚ) = ((R + k : ℕ) : ℚ) := by
      push_cast; rw [← hk, ← hk']; unfold cPair; ring
    exact_mod_cast h1
  have hx : (x : ℂ) = k + (R : ℂ) / 2 - (S : ℂ) / 2 := by
    have : x = k + (R : ℚ) / 2 - (S : ℚ) / 2 := by rw [← hk]; unfold cPair; ring
    rw [this]; push_cast; ring
  set e := embR P Q R hP k
  have hinj := L_inj P Q R hP k
  obtain ⟨π, hπW, hπid, hπeq⟩ := L_proj P Q R 0 (LinearMap.range e)
    (by rintro Z _ ⟨G, rfl⟩; exact ⟨_, (actR_full P Q R hP k Z G).symm⟩)
    (by rintro _ ⟨G, rfl⟩ n; exact L_grad P Q R hP k G n)
  let eq := LinearEquiv.ofInjective e hinj
  let κ : Pol P Q R 0 →ₗ[ℂ] Mdl P Q := eq.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ π hπW
  have hκ : ∀ f, e (κ f) = π f := by
    intro f
    have := eq.apply_symm_apply ⟨π f, hπW f⟩
    simpa [eq, κ] using congrArg Subtype.val this
  have hκeq : ∀ Z f, κ (fockAct1 P Q R 0 Z f) = actR P Q R k Z (κ f) := by
    intro Z f; apply hinj
    rw [hκ, hπeq, ← hκ, actR_full]
  have hκ1 : κ (e 1) = 1 := by
    apply hinj; rw [hκ, hπid _ ⟨1, rfl⟩]
  let b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ :=
    GlobalTheory.DefLift.BilFischer.pair.flip ∘ₗ (embS P Q S hQ k') ∘ₗ κ
  have hb : ∀ f g, b f g = GlobalTheory.DefLift.BilFischer.pair g (embS P Q S hQ k' (κ f)) := fun _ _ => rfl
  apply L_tensor P Q R S x b
  · intro h0
    have hne : embS P Q S hQ k' 1 ≠ 0 := by
      simp only [embS, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one, LinearMap.mulRight_apply, one_mul]
      exact pow_ne_zero _ (L_detS P Q S hQ)
    apply hne
    apply GlobalTheory.DefLift.BilFischer.pair_nondeg
    intro g
    have := congrArg (fun t => t (e 1) g) h0
    simpa [hb, hκ1] using this
  · intro Z f g
    rw [hb, hb, hb, hκeq, actS_full, ← map_add, ← map_add, act_sum P Q R S k k' x hkk hx, map_smul, map_smul,
      smul_eq_mul]

end GlobalTheory.CharPair

end
