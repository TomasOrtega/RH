import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.DensityPointOfCornerSimple

noncomputable section

open Matrix Polynomial PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.LocP

variable {n : ℕ}

/- English proof (translation)
Establish `hnd : γ.charpoly.roots.Nodup` using `nodup_roots h`. Establish `hcard : γ.charpoly.roots.toFinset.card = n`. Rewrite using `[Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits γ.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Set `e : Fin n ≃ γ.charpoly.roots.toFinset` to `(Finset.equivFinOfCardEq hcard).symm`. Set `lam : Fin n → ℂ` to `fun i => (e i : ℂ)`.

Establish `hl : Function.Injective lam` using `Subtype.val_injective.comp e.injective`. Establish `hroot : ∀ i, γ.charpoly.IsRoot (lam i)` using `fun i => isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)`. Establish `hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' γ) (lam i)` using `fun i => by`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']`. Conclude with `hroot i`.

Use `choose v hv using fun i => (hev i).exists_hasEigenvector`. Establish `hli : LinearIndependent ℂ v` using `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' γ) lam hl v hv`. Set `Pm : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun a i => v i a`. Establish `hPu : IsUnit Pm` using `Matrix.linearIndependent_cols_iff_isUnit.1 hli`. Take `⟨P, hP⟩` from `hPu`.

Establish `hγ : γ * P.val = P.val * diagonal lam`. Rewrite using `[hP]`. Use extensionality with `a i`. Establish `h1` using `congrFun (hv i).apply_eq_smul a`. Rewrite `h1` using `[Matrix.toLin'_apply]`.

Rewrite using `[Matrix.mul_diagonal]`. Simplify using `only [Pm, Matrix.of_apply]`. Rewrite using `[mul_comm]`. Simplify `h1` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Use `⟨P, lam, hl, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hγ, Matrix.mul_assoc, ← Units.val_mul]`. Simplify using the standard rewrite rules.
-/
theorem exists_diag (γ : Matrix (Fin n) (Fin n) ℂ) (h : γ.charpoly.Separable) :
    ∃ (P : GL (Fin n) ℂ) (lam : Fin n → ℂ), Function.Injective lam ∧
      γ = P.val * diagonal lam * (P⁻¹).val := by
  classical
  have hnd : γ.charpoly.roots.Nodup := nodup_roots h
  have hcard : γ.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits γ.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ γ.charpoly.roots.toFinset := (Finset.equivFinOfCardEq hcard).symm
  let lam : Fin n → ℂ := fun i => (e i : ℂ)
  have hl : Function.Injective lam := Subtype.val_injective.comp e.injective
  have hroot : ∀ i, γ.charpoly.IsRoot (lam i) := fun i =>
    isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' γ) (lam i) := fun i => by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot i
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' γ) lam hl v hv
  let Pm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a i => v i a
  have hPu : IsUnit Pm := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨P, hP⟩ := hPu
  have hγ : γ * P.val = P.val * diagonal lam := by
    rw [hP]
    ext a i
    have h1 := congrFun (hv i).apply_eq_smul a
    rw [Matrix.toLin'_apply] at h1
    rw [Matrix.mul_diagonal]
    simp only [Pm, Matrix.of_apply]
    rw [mul_comm]
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h1
  refine ⟨P, lam, hl, ?_⟩
  rw [← hγ, Matrix.mul_assoc, ← Units.val_mul]
  simp

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, ((y⁻¹).val * A * y.val) ^ k = (y⁻¹).val * A ^ k * y.val` using `fun k => by`. Simplify using `using Units.conj_pow y⁻¹ A k`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]`. Consider the case `monomial k a`.

Simplify using `only [aeval_monomial, hpow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem aeval_conj_units (y : GL (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ[X]) :
    aeval ((y⁻¹).val * A * y.val) q = (y⁻¹).val * aeval A q * y.val := by
  have hpow : ∀ k : ℕ, ((y⁻¹).val * A * y.val) ^ k = (y⁻¹).val * A ^ k * y.val := fun k => by
    simpa using Units.conj_pow y⁻¹ A k
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, hpow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h : diagonal lam = Matrix.diagonalAlgHom ℂ lam` using `rfl`. Rewrite using `[h, aeval_algHom_apply]`. Establish `h2 : aeval lam q = fun j => q.eval (lam j)`. Use function extensionality and compare the values at `j`. Use `aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) j) lam q` as an intermediate fact.

Simplify using `using this.symm`. Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem aeval_diagonal (lam : Fin n → ℂ) (q : ℂ[X]) :
    aeval (diagonal lam) q = diagonal fun j => q.eval (lam j) := by
  have h : diagonal lam = Matrix.diagonalAlgHom ℂ lam := rfl
  rw [h, aeval_algHom_apply]
  have h2 : aeval lam q = fun j => q.eval (lam j) := by
    funext j
    have := aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) j) lam q
    simpa using this.symm
  rw [h2]
  rfl

/- English proof (translation)
Use `set S : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖M i j‖ ≤ B} with hS`. Establish `hSc : IsCompact S`. Establish `: S = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) B`. Use extensionality with `M`. Conclude with `⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩`.

Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `h` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))`. Conclude with `h`.
-/
theorem isCompact_entryBall (n : ℕ) (B : ℝ) :
    IsCompact {k : GL (Fin n) ℂ | (∀ i j, ‖k.val i j‖ ≤ B) ∧ ∀ i j, ‖(k⁻¹).val i j‖ ≤ B} := by
  set S : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖M i j‖ ≤ B} with hS
  have hSc : IsCompact S := by
    have : S = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) B := by
      ext M
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))
  exact h

/- English proof (translation)
Set `p : Fin n → ℂ[X]` to `fun i => Lagrange.basis Finset.univ lam i`. Establish `hp : ∀ i j, (p i).eval (lam j) = if j = i then 1 else 0`. Introduce `i j`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)`. Conclude with `Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)`. Set `G : Matrix (Fin n) (Fin n) ℂ → Fin n → Fin n → Fin n → ℂ` to `fun g i a b => aeval g (p i) a b`. Establish `hG : Continuous G`. Use `continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations.

Conclude with `(continuous_id.matrix_elem a b).comp (Polynomial.continuous_aeval (p i))`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hG.continuousOn`. Use `⟨_, isCompact_entryBall n (max B 1), fun y hy => ?_⟩` and prove the remaining obligations. Establish `hE : ∀ i a b, ‖(y⁻¹).val a i * y.val i b‖ ≤ B`. Introduce `i a b`.

Establish `h1 : aeval ((y⁻¹).val * diagonal lam * y.val) (p i) = (y⁻¹).val * diagonal (fun j => (p i).eval (lam j)) * y.val`. Rewrite using `[aeval_conj_units, aeval_diagonal]`. Establish `h2 : G ((y⁻¹).val * diagonal lam * y.val) i a b = (y⁻¹).val a i * y.val i b`. Simplify using `only [G, h1, hp]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.mul_diagonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← h2]`. Conclude with `((norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans (norm_le_pi_norm _ i))).trans (hB _ hy)`. Establish `hrow : ∀ i, ∃ j, ∀ j', ‖y.val i j'‖ ≤ ‖y.val i j‖` using `fun i => by haveI : Nonempty (Fin n) := ⟨i⟩`. Conclude with `Finite.exists_max _`.

Use `choose c hc using hrow`. Establish `hne : ∀ i, y.val i (c i) ≠ 0`. Introduce `i h0`. Establish `h1 : (y.val * (y⁻¹).val) i i = 1`. Rewrite using `[← Units.val_mul]`.

Simplify using the standard rewrite rules. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_zero]`. Conclude with `zero_ne_one h1`. Introduce `j _`. Establish `: y.val i j = 0`.

Use `hc i j` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `norm_le_zero_iff.1 this`. Rewrite using `[this, zero_mul]`. Set `s : Fin n → ℂ` to `fun i => y.val i (c i)`.

Set `t : GL (Fin n) ℂ` to `⟨diagonal s, diagonal fun i => (s i)⁻¹, by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne], by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne]⟩`. Use `⟨t, t⁻¹ * y, s, ⟨?_, ?_⟩, by group, rfl⟩` and prove the remaining obligations. Introduce `i j`. Establish `htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹` using `rfl`. Establish `h1 : (t⁻¹ * y).val i j = (s i)⁻¹ * y.val i j`.

Rewrite using `[Units.val_mul, htinv, Matrix.diagonal_mul]`. Rewrite using `[h1, norm_mul, norm_inv]`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Conclude with `(inv_mul_le_one₀ (norm_pos_iff.2 (hne i))).2 (hc i j)`. Introduce `a i`.

Establish `h1 : ((t⁻¹ * y)⁻¹).val a i = (y⁻¹).val a i * y.val i (c i)`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul]`. Express the relevant statement in the definitionally equal form `((y⁻¹).val * diagonal s) a i = _`. Rewrite using `[Matrix.mul_diagonal]`. Rewrite using `[h1]`.

Conclude with `(hE i a (c i)).trans (le_max_left _ _)`.
-/
theorem diag_proper (lam : Fin n → ℂ) (hl : Function.Injective lam)
    (C : Set (Matrix (Fin n) (Fin n) ℂ)) (hC : IsCompact C) :
    ∃ K : Set (GL (Fin n) ℂ), IsCompact K ∧ ∀ y : GL (Fin n) ℂ,
      (y⁻¹).val * diagonal lam * y.val ∈ C →
      ∃ (t k : GL (Fin n) ℂ) (s : Fin n → ℂ), k ∈ K ∧ y = t * k ∧ t.val = diagonal s := by
  classical
  let p : Fin n → ℂ[X] := fun i => Lagrange.basis Finset.univ lam i
  have hp : ∀ i j, (p i).eval (lam j) = if j = i then 1 else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)
  let G : Matrix (Fin n) (Fin n) ℂ → Fin n → Fin n → Fin n → ℂ := fun g i a b => aeval g (p i) a b
  have hG : Continuous G := by
    refine continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_id.matrix_elem a b).comp (Polynomial.continuous_aeval (p i))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨_, isCompact_entryBall n (max B 1), fun y hy => ?_⟩
  have hE : ∀ i a b, ‖(y⁻¹).val a i * y.val i b‖ ≤ B := by
    intro i a b
    have h1 : aeval ((y⁻¹).val * diagonal lam * y.val) (p i) =
        (y⁻¹).val * diagonal (fun j => (p i).eval (lam j)) * y.val := by
      rw [aeval_conj_units, aeval_diagonal]
    have h2 : G ((y⁻¹).val * diagonal lam * y.val) i a b = (y⁻¹).val a i * y.val i b := by
      simp only [G, h1, hp]
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← h2]
    exact ((norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans (norm_le_pi_norm _ i))).trans (hB _ hy)

  have hrow : ∀ i, ∃ j, ∀ j', ‖y.val i j'‖ ≤ ‖y.val i j‖ := fun i => by
    haveI : Nonempty (Fin n) := ⟨i⟩
    exact Finite.exists_max _
  choose c hc using hrow
  have hne : ∀ i, y.val i (c i) ≠ 0 := by
    intro i h0
    have h1 : (y.val * (y⁻¹).val) i i = 1 := by
      rw [← Units.val_mul]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro j _
      have : y.val i j = 0 := by
        have := hc i j
        rw [h0, norm_zero] at this
        exact norm_le_zero_iff.1 this
      rw [this, zero_mul]
  let s : Fin n → ℂ := fun i => y.val i (c i)
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne], by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne]⟩
  refine ⟨t, t⁻¹ * y, s, ⟨?_, ?_⟩, by group, rfl⟩
  · intro i j
    have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
    have h1 : (t⁻¹ * y).val i j = (s i)⁻¹ * y.val i j := by
      rw [Units.val_mul, htinv, Matrix.diagonal_mul]
    rw [h1, norm_mul, norm_inv]
    refine le_trans ?_ (le_max_right _ _)
    exact (inv_mul_le_one₀ (norm_pos_iff.2 (hne i))).2 (hc i j)
  · intro a i
    have h1 : ((t⁻¹ * y)⁻¹).val a i = (y⁻¹).val a i * y.val i (c i) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
      change ((y⁻¹).val * diagonal s) a i = _
      rw [Matrix.mul_diagonal]
    rw [h1]
    exact (hE i a (c i)).trans (le_max_left _ _)

def phiU (n : ℕ) : GL (Fin n) ℂ :=
  ⟨GlobalTheory.Tw.Phi n ℂ, (GlobalTheory.Tw.Phi n ℂ)ᵀ, GlobalTheory.Tw.Model.Phi_mul_transpose, GlobalTheory.Tw.Model.transpose_mul_Phi⟩

/- English proof (translation)
Rewrite using `[thetaR_val, inv_inv]`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`.
-/
theorem conjT_eq (g : GL (Fin n) ℂ) : (g.val)ᴴ = (thetaR (starRingEnd ℂ) n g⁻¹).val := by
  rw [thetaR_val, inv_inv]
  ext i j
  simp [Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[GlobalTheory.Tw.theta, ← Matrix.coe_units_inv, conjT_eq, inv_inv]`. Both sides reduce to the same expression.
-/
theorem theta_val (g : GL (Fin n) ℂ) :
    GlobalTheory.Tw.theta g.val = (phiU n * thetaR (starRingEnd ℂ) n g * (phiU n)⁻¹).val := by
  rw [GlobalTheory.Tw.theta, ← Matrix.coe_units_inv, conjT_eq, inv_inv]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[thetaR_val]`. Express the relevant statement in the definitionally equal form `(((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ))ᵀ = GlobalTheory.Tw.Phi n ℂ`. Establish `h` using `GlobalTheory.Tw.Model.Phi_conjTranspose (n := n) (R := ℂ)`. Establish `h2 : ((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ) = (GlobalTheory.Tw.Phi n ℂ)ᵀ` using `h`.

Rewrite using `[h2, Matrix.transpose_transpose]`.
-/
theorem theta_phiU : thetaR (starRingEnd ℂ) n (phiU n) = phiU n := by
  apply Units.ext
  rw [thetaR_val]
  change (((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ))ᵀ = GlobalTheory.Tw.Phi n ℂ
  have h := GlobalTheory.Tw.Model.Phi_conjTranspose (n := n) (R := ℂ)
  have h2 : ((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ) = (GlobalTheory.Tw.Phi n ℂ)ᵀ := h
  rw [h2, Matrix.transpose_transpose]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GlobalTheory.Tw.Phi n ℂ)ᵀ * (GlobalTheory.Tw.Phi n ℂ)ᵀ = _`. Use `nth_rewrite 2 [GlobalTheory.Tw.Model.Phi_transpose]`. Rewrite using `[Matrix.mul_smul, GlobalTheory.Tw.Model.transpose_mul_Phi]`.
-/
theorem phi_sq : ((phiU n)⁻¹ * (phiU n)⁻¹).val = ((-1 : ℂ) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  change (GlobalTheory.Tw.Phi n ℂ)ᵀ * (GlobalTheory.Tw.Phi n ℂ)ᵀ = _
  nth_rewrite 2 [GlobalTheory.Tw.Model.Phi_transpose]
  rw [Matrix.mul_smul, GlobalTheory.Tw.Model.transpose_mul_Phi]

/- English proof (translation)
Rewrite using `[GlobalTheory.Tw.nrm, theta_val, ← Units.val_mul]`. Establish `: d * (phiU n)⁻¹ * (phiU n * thetaR (starRingEnd ℂ) n (d * (phiU n)⁻¹) * (phiU n)⁻¹) = (d * thetaR (starRingEnd ℂ) n d) * ((phiU n)⁻¹ * (phiU n)⁻¹)`. Simplify using `only [map_mul, map_inv, theta_phiU]`. Use `group`. Rewrite using `[this, Units.val_mul, phi_sq, Matrix.mul_smul, Matrix.mul_one]`.
-/
theorem nrm_eq (d : GL (Fin n) ℂ) :
    GlobalTheory.Tw.nrm (d * (phiU n)⁻¹).val = ((-1 : ℂ) ^ (n - 1)) • (d * thetaR (starRingEnd ℂ) n d).val := by
  rw [GlobalTheory.Tw.nrm, theta_val, ← Units.val_mul]
  have : d * (phiU n)⁻¹ * (phiU n * thetaR (starRingEnd ℂ) n (d * (phiU n)⁻¹) * (phiU n)⁻¹) =
      (d * thetaR (starRingEnd ℂ) n d) * ((phiU n)⁻¹ * (phiU n)⁻¹) := by
    simp only [map_mul, map_inv, theta_phiU]
    group
  rw [this, Units.val_mul, phi_sq, Matrix.mul_smul, Matrix.mul_one]

/- English proof (translation)
Establish `: d * (thetaR (starRingEnd ℂ) n z)⁻¹ * d⁻¹ = d * (phiU n)⁻¹ * phiU n * thetaR (starRingEnd ℂ) n z⁻¹ * (phiU n)⁻¹ * (d * (phiU n)⁻¹)⁻¹`. Simplify using `only [map_inv]`. Use `group`. Rewrite using `[this, GlobalTheory.Tw.adj, conjT_eq, ← Matrix.coe_units_inv]`. Both sides reduce to the same expression.
-/
theorem adj_eq (d z : GL (Fin n) ℂ) :
    GlobalTheory.Tw.adj (d * (phiU n)⁻¹).val z.val = (d * (thetaR (starRingEnd ℂ) n z)⁻¹ * d⁻¹).val := by
  have : d * (thetaR (starRingEnd ℂ) n z)⁻¹ * d⁻¹ =
      d * (phiU n)⁻¹ * phiU n * thetaR (starRingEnd ℂ) n z⁻¹ * (phiU n)⁻¹ * (d * (phiU n)⁻¹)⁻¹ := by
    simp only [map_inv]
    group
  rw [this, GlobalTheory.Tw.adj, conjT_eq, ← Matrix.coe_units_inv]
  rfl

/- English proof (translation)
Use `set δ : GL (Fin n) ℂ := d * (phiU n)⁻¹ with hδ`. Establish `hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Establish `hReg : GlobalTheory.Tw.Reg δ.val` using `⟨δ.isUnit, by rw [nrm_eq]; exact Formalism.RepresentationBoundsCohomology.ringDataObjects.charpoly_smul_sep _ _ hε hd⟩`. Establish `TC` using `GlobalTheory.Tw.twisted_centraliser n ℂ δ.val hReg`. Use `set C' : Set (GL (Fin n) ℂ) := (fun c : GL (Fin n) ℂ => d * c⁻¹) '' C`.

Establish `hC' : IsCompact C'` using `hC.image (continuous_const.mul continuous_inv)`. Take `⟨D, hD, hDp⟩` from `GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact ℂ (fun x => norm_star x) n δ.val hReg C' hC'`. Use `⟨D, hD, fun z hz hzC => ?_⟩` and prove the remaining obligations. Establish `hzv : z.val * GlobalTheory.Tw.nrm δ.val = GlobalTheory.Tw.nrm δ.val * z.val`. Establish `h1 : z.val * (d * thetaR (starRingEnd ℂ) n d).val = (d * thetaR (starRingEnd ℂ) n d).val * z.val`.

Rewrite using `[← Units.val_mul, hz, Units.val_mul]`. Rewrite using `[nrm_eq, Matrix.mul_smul, Matrix.smul_mul, h1]`. Establish `hzA : z.val ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val}` using `(TC.2.2.2.2.1 z.val).1 hzv`. Establish `hcomm : ∀ x ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val}, z.val * x = x * z.val`. Introduce `x hx`.

Establish `hle : Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val} ≤ Subalgebra.centralizer ℂ {z.val}`. Rewrite using `[Algebra.adjoin_le_iff, Set.singleton_subset_iff]`. Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality.

Conclude with `hzv`. Conclude with `hle hx z.val (Set.mem_singleton _)`. Establish `hu : (d * (twConj (thetaR (starRingEnd ℂ) n) z d)⁻¹).val = z.val * GlobalTheory.Tw.adj δ.val z.val`. Rewrite using `[hcomm _ (TC.2.2.2.1 _ hzA).1, adj_eq, ← Units.val_mul]`. Simplify using `only [twConj]`.

Use `congr 1`. Use `group`. Take `⟨t, htA, ht1, e, he, rfl⟩` from `hDp z hzA _ ⟨_, hzC, rfl⟩ hu`. Use `⟨t, ?_, e, he, rfl⟩` and prove the remaining obligations. Establish `htc : t.val ∈ GlobalTheory.Tw.cent δ.val` using `by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩`.

Establish `h2 : t * δ = δ * (phiU n * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹)` using `Units.ext (by rw [Units.val_mul t δ, Units.val_mul δ, ← theta_val]; exact htc.2)`. Express the relevant statement in the definitionally equal form `t⁻¹ * d * thetaR (starRingEnd ℂ) n t = d`. Establish `h3 : t * d = d * thetaR (starRingEnd ℂ) n t`. Establish `: t * d * (phiU n)⁻¹ = d * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹`. Rewrite using `[mul_assoc t, ← hδ, h2, hδ]`.

Use `group`. Conclude with `mul_right_cancel this`. Rewrite using `[mul_assoc, ← h3]`. Use `group`.
-/
theorem norm_proper (d : GL (Fin n) ℂ) (hd : (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable)
    (C : Set (GL (Fin n) ℂ)) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin n) ℂ), IsCompact D ∧ ∀ z : GL (Fin n) ℂ,
      z * (d * thetaR (starRingEnd ℂ) n d) = (d * thetaR (starRingEnd ℂ) n d) * z →
      twConj (thetaR (starRingEnd ℂ) n) z d ∈ C →
      ∃ t ∈ twCent (thetaR (starRingEnd ℂ) n) d, ∃ e ∈ D, z = t * e := by
  set δ : GL (Fin n) ℂ := d * (phiU n)⁻¹ with hδ
  have hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hReg : GlobalTheory.Tw.Reg δ.val :=
    ⟨δ.isUnit, by rw [nrm_eq]; exact Formalism.RepresentationBoundsCohomology.ringDataObjects.charpoly_smul_sep _ _ hε hd⟩
  have TC := GlobalTheory.Tw.twisted_centraliser n ℂ δ.val hReg
  set C' : Set (GL (Fin n) ℂ) := (fun c : GL (Fin n) ℂ => d * c⁻¹) '' C
  have hC' : IsCompact C' := hC.image (continuous_const.mul continuous_inv)
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact ℂ (fun x => norm_star x) n δ.val hReg C' hC'
  refine ⟨D, hD, fun z hz hzC => ?_⟩
  have hzv : z.val * GlobalTheory.Tw.nrm δ.val = GlobalTheory.Tw.nrm δ.val * z.val := by
    have h1 : z.val * (d * thetaR (starRingEnd ℂ) n d).val = (d * thetaR (starRingEnd ℂ) n d).val * z.val := by
      rw [← Units.val_mul, hz, Units.val_mul]
    rw [nrm_eq, Matrix.mul_smul, Matrix.smul_mul, h1]
  have hzA : z.val ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val} := (TC.2.2.2.2.1 z.val).1 hzv
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val}, z.val * x = x * z.val := by
    intro x hx
    have hle : Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val} ≤ Subalgebra.centralizer ℂ {z.val} := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hzv
    exact hle hx z.val (Set.mem_singleton _)
  have hu : (d * (twConj (thetaR (starRingEnd ℂ) n) z d)⁻¹).val = z.val * GlobalTheory.Tw.adj δ.val z.val := by
    rw [hcomm _ (TC.2.2.2.1 _ hzA).1, adj_eq, ← Units.val_mul]
    simp only [twConj]
    congr 1
    group
  obtain ⟨t, htA, ht1, e, he, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
  refine ⟨t, ?_, e, he, rfl⟩
  have htc : t.val ∈ GlobalTheory.Tw.cent δ.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
  have h2 : t * δ = δ * (phiU n * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹) :=
    Units.ext (by rw [Units.val_mul t δ, Units.val_mul δ, ← theta_val]; exact htc.2)
  change t⁻¹ * d * thetaR (starRingEnd ℂ) n t = d
  have h3 : t * d = d * thetaR (starRingEnd ℂ) n t := by
    have : t * d * (phiU n)⁻¹ = d * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹ := by
      rw [mul_assoc t, ← hδ, h2, hδ]; group
    exact mul_right_cancel this
  rw [mul_assoc, ← h3]; group

/- English proof (translation)
Introduce `n d hd C hC`. Establish `hcont : Continuous (thetaR (starRingEnd ℂ) n)` using `GlobalTheory.CompanionTheory.LocVan.continuous_thC`. Establish `hinv : ∀ g : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g` using `fun g => GlobalTheory.CompanionTheory.FlagCent.thetaR_thetaR (starRingEnd ℂ) (fun x => Complex.conj_conj x) g`. Take `⟨P, lam, hl, hP⟩` from `exists_diag _ hd`. Use `set C₂ : Set (Matrix (Fin n) (Fin n) ℂ) := (fun c : GL (Fin n) ℂ => (c * thetaR (starRingEnd ℂ) n c).val) '' C with hC₂`.

Establish `hC₂c : IsCompact C₂` using `hC.image (Units.continuous_val.comp (continuous_id.mul hcont))`. Take `⟨K, hK, hKp⟩` from `diag_proper lam hl C₂ hC₂c`. Use `set K' : Set (GL (Fin n) ℂ) := (fun k => P * k) '' K with hK'`. Establish `hK'c : IsCompact K'` using `hK.image (continuous_const.mul continuous_id)`. Use `set C₃ : Set (GL (Fin n) ℂ) := (fun p : GL (Fin n) ℂ × GL (Fin n) ℂ => p.1 * p.2 * (thetaR (starRingEnd ℂ) n p.1)⁻¹) '' (K' ×ˢ C) with hC₃`.

Establish `hC₃c : IsCompact C₃` using `(hK'c.prod hC).image ((continuous_fst.mul continuous_snd).mul (hcont.comp continuous_fst).inv)`. Take `⟨D, hD, hDp⟩` from `norm_proper d hd C₃ hC₃c`. Use `⟨D * K', hD.mul hK'c, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : twConj (thetaR (starRingEnd ℂ) n) x d ∈ C` using `hx`.

Establish `hnorm : ((P⁻¹ * x)⁻¹).val * diagonal lam * (P⁻¹ * x).val ∈ C₂`. Use `⟨_, hx', ?_⟩` and prove the remaining obligations. Establish `e : twConj (thetaR (starRingEnd ℂ) n) x d * thetaR (starRingEnd ℂ) n (twConj (thetaR (starRingEnd ℂ) n) x d) = x⁻¹ * (d * thetaR (starRingEnd ℂ) n d) * x`. Simplify using `only [twConj, map_mul, map_inv, hinv]`. Use `group`.

Use `show (_ : GL (Fin n) ℂ).val = _`. Rewrite using `[e, Units.val_mul, Units.val_mul, hP]`. Simplify using `only [_root_.mul_inv_rev, inv_inv, Units.val_mul]`. Simplify using `only [Matrix.mul_assoc]`. Take `⟨t, k, s, hk, hy, ht⟩` from `hKp _ hnorm`.

Establish `hx2 : x = (P * t * P⁻¹) * (P * k)`. Establish `: x = P * (t * k)` using `by rw [← hy]; group`. Rewrite using `[this]`. Use `group`. Use `set z := P * t * P⁻¹ with hz`.

Establish `hcomm : z * (d * thetaR (starRingEnd ℂ) n d) = (d * thetaR (starRingEnd ℂ) n d) * z`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul z, Units.val_mul _ z, hP, hz]`. Simplify using `only [Units.val_mul]`. Establish `hPP : (P⁻¹).val * P.val = 1` using `by rw [← Units.val_mul]; simp`.

Establish `hdt : t.val * diagonal lam = diagonal lam * t.val`. Rewrite using `[ht, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use extensionality with `i`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hPP]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Establish `hzC : twConj (thetaR (starRingEnd ℂ) n) z d ∈ C₃`.

Use `⟨(P * k, twConj (thetaR (starRingEnd ℂ) n) x d), ⟨⟨k, hk, rfl⟩, hx'⟩, ?_⟩` and prove the remaining obligations. Use `show (P * k) * twConj (thetaR (starRingEnd ℂ) n) x d * (thetaR (starRingEnd ℂ) n (P * k))⁻¹ = _`. Rewrite using `[hx2]`. Simplify using `only [twConj, map_mul, map_inv]`. Use `group`.

Take `⟨u, hu, e, he, hze⟩` from `hDp z hcomm hzC`. Use `⟨u, hu, e * (P * k), Set.mul_mem_mul he ⟨k, hk, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show u * (e * (P * k)) = x`. Rewrite using `[hx2, hze, mul_assoc]`.
-/
theorem main : PositivityTheory.Rg.BcB.D4.LocProper := by
  intro n d hd C hC
  have hcont : Continuous (thetaR (starRingEnd ℂ) n) := GlobalTheory.CompanionTheory.LocVan.continuous_thC
  have hinv : ∀ g : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
    fun g => GlobalTheory.CompanionTheory.FlagCent.thetaR_thetaR (starRingEnd ℂ) (fun x => Complex.conj_conj x) g
  obtain ⟨P, lam, hl, hP⟩ := exists_diag _ hd

  set C₂ : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun c : GL (Fin n) ℂ => (c * thetaR (starRingEnd ℂ) n c).val) '' C with hC₂
  have hC₂c : IsCompact C₂ := hC.image (Units.continuous_val.comp (continuous_id.mul hcont))
  obtain ⟨K, hK, hKp⟩ := diag_proper lam hl C₂ hC₂c
  set K' : Set (GL (Fin n) ℂ) := (fun k => P * k) '' K with hK'
  have hK'c : IsCompact K' := hK.image (continuous_const.mul continuous_id)
  set C₃ : Set (GL (Fin n) ℂ) :=
    (fun p : GL (Fin n) ℂ × GL (Fin n) ℂ => p.1 * p.2 * (thetaR (starRingEnd ℂ) n p.1)⁻¹) '' (K' ×ˢ C) with hC₃
  have hC₃c : IsCompact C₃ := (hK'c.prod hC).image
    ((continuous_fst.mul continuous_snd).mul (hcont.comp continuous_fst).inv)
  obtain ⟨D, hD, hDp⟩ := norm_proper d hd C₃ hC₃c
  refine ⟨D * K', hD.mul hK'c, ?_⟩
  intro x hx
  have hx' : twConj (thetaR (starRingEnd ℂ) n) x d ∈ C := hx

  have hnorm : ((P⁻¹ * x)⁻¹).val * diagonal lam * (P⁻¹ * x).val ∈ C₂ := by
    refine ⟨_, hx', ?_⟩
    have e : twConj (thetaR (starRingEnd ℂ) n) x d * thetaR (starRingEnd ℂ) n (twConj (thetaR (starRingEnd ℂ) n) x d)
        = x⁻¹ * (d * thetaR (starRingEnd ℂ) n d) * x := by
      simp only [twConj, map_mul, map_inv, hinv]
      group
    show (_ : GL (Fin n) ℂ).val = _
    rw [e, Units.val_mul, Units.val_mul, hP]
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨t, k, s, hk, hy, ht⟩ := hKp _ hnorm
  have hx2 : x = (P * t * P⁻¹) * (P * k) := by
    have : x = P * (t * k) := by rw [← hy]; group
    rw [this]; group
  set z := P * t * P⁻¹ with hz
  have hcomm : z * (d * thetaR (starRingEnd ℂ) n d) = (d * thetaR (starRingEnd ℂ) n d) * z := by
    apply Units.ext
    rw [Units.val_mul z, Units.val_mul _ z, hP, hz]
    simp only [Units.val_mul]
    have hPP : (P⁻¹).val * P.val = 1 := by rw [← Units.val_mul]; simp
    have hdt : t.val * diagonal lam = diagonal lam * t.val := by
      rw [ht, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; ext i; ring
    calc P.val * t.val * (P⁻¹).val * (P.val * diagonal lam * (P⁻¹).val)
        = P.val * t.val * ((P⁻¹).val * P.val) * diagonal lam * (P⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = P.val * (t.val * diagonal lam) * (P⁻¹).val := by rw [hPP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = P.val * (diagonal lam * t.val) * (P⁻¹).val := by rw [hdt]
      _ = P.val * diagonal lam * ((P⁻¹).val * P.val) * t.val * (P⁻¹).val := by
          rw [hPP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hzC : twConj (thetaR (starRingEnd ℂ) n) z d ∈ C₃ := by
    refine ⟨(P * k, twConj (thetaR (starRingEnd ℂ) n) x d), ⟨⟨k, hk, rfl⟩, hx'⟩, ?_⟩
    show (P * k) * twConj (thetaR (starRingEnd ℂ) n) x d * (thetaR (starRingEnd ℂ) n (P * k))⁻¹ = _
    rw [hx2]
    simp only [twConj, map_mul, map_inv]
    group
  obtain ⟨u, hu, e, he, hze⟩ := hDp z hcomm hzC
  refine ⟨u, hu, e * (P * k), Set.mul_mem_mul he ⟨k, hk, rfl⟩, ?_⟩
  show u * (e * (P * k)) = x
  rw [hx2, hze, mul_assoc]

end PositivityTheory.Rg.BcB.CV.LocP

end
