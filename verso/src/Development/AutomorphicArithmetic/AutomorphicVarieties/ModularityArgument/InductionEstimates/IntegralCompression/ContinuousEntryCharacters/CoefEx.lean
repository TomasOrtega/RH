import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpNorm

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h0` using `(expBasic π).2.2.2 0`. Simplify using `only [zpow_zero] at h0`. Simplify using `only [pow_zero, zero_smul]`.

Conclude with `h0`. Consider the case `succ n ih`. Establish `h1` using `expMul π _ _ _ _ ih h`. Simplify using `only [pow_succ, succ_nsmul]`. Conclude with `h1`.
-/
private lemma oexp_pow (π : Equiv.Perm (Fin (2 + 2))) (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) (h : OExp π ψ μ) (n : ℕ) :
    OExp π (fun k => ψ k ^ n) (n • μ) := by
  induction n with
  | zero =>
    have h0 := (expBasic π).2.2.2 0
    simp only [zpow_zero] at h0
    simp only [pow_zero, zero_smul]
    exact h0
  | succ n ih =>
    have h1 := expMul π _ _ _ _ ih h
    simp only [pow_succ, succ_nsmul]
    exact h1

private noncomputable def F (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) : ℂ :=
  en i i k ^ α * (en i i k * en j j k - en i j k * en j i k) ^ β * conj (en l l k) ^ γ *
    (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ

/- English proof (translation)
Substitute `hi hj hl hμ` using the available equality. Take `⟨h1, h2, h3, h4⟩` from `expBasic π`. Conclude with `expNorm π _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (oexp_pow π _ _ h1 α) (oexp_pow π _ _ h2 β)) (oexp_pow π _ _ h3 γ)) (h4 δ))`.
-/
private lemma F_exp (π : Equiv.Perm (Fin (2 + 2))) (i j l : Fin (2 + 2)) (hi : π 0 = i) (hj : π 1 = j) (hl : π 3 = l)
    (α β γ : ℕ) (δ : ℤ) (μ : Fin (2 + 2) → ℤ)
    (hμ : μ = α • (Pi.single i 1 : Fin (2 + 2) → ℤ) + β • (Pi.single i 1 + Pi.single j 1) + γ • (-Pi.single l 1) + fun _ => δ) :
    WExp (F i j l α β γ δ) μ := by
  subst hi hj hl hμ
  obtain ⟨h1, h2, h3, h4⟩ := expBasic π
  exact expNorm π _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (oexp_pow π _ _ h1 α) (oexp_pow π _ _ h2 β))
    (oexp_pow π _ _ h3 γ)) (h4 δ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma en_inv (i j : Fin (2 + 2)) (k : U4) : en i j k⁻¹ = conj (en j i k) := rfl

/- English proof (translation)
Establish `hd : ((k⁻¹ : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det = conj ((k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det)`. Express the relevant statement in the definitionally equal form `(star (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ)).det = _`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]`. Both sides reduce to the same expression. Simplify using `only [F, en_inv, hd, map_mul, map_pow, map_zpow₀, map_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma F_star (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) :
    F i j l α β γ δ k⁻¹ = conj (F i j l α β γ δ k) := by
  have hd : ((k⁻¹ : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det = conj ((k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det) := by
    change (star (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ)).det = _
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl
  simp only [F, en_inv, hd, map_mul, map_pow, map_zpow₀, map_sub]
  ring

/- English proof (translation)
Unfold `en`. Rewrite using `[u4.1 a b]`. Both sides reduce to the same expression.
-/
private lemma en_bd (i j : Fin (2 + 2)) (a b : U2) : en i j (bd a b) =
    fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  unfold en
  rw [u4.1 a b]
  rfl

/- English proof (translation)
Rewrite using `[u4.1 a b, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
private lemma det_bd (a b : U2) : (bd a b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det =
    (a : Matrix (Fin 2) (Fin 2) ℂ).det * (b : Matrix (Fin 2) (Fin 2) ℂ).det := by
  rw [u4.1 a b, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Evaluate the decidable proposition.
-/
private lemma s0 : (finSumFinEquiv.symm (0 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
private lemma s1 : (finSumFinEquiv.symm (1 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
private lemma s2 : (finSumFinEquiv.symm (2 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
private lemma s3 : (finSumFinEquiv.symm (3 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide

/- English proof (translation)
Establish `hd` using `det_ne_zero_of_U2 m`. Establish `h : star (m : Matrix (Fin 2) (Fin 2) ℂ) * (m : Matrix (Fin 2) (Fin 2) ℂ) = 1` using `m.2.1`. Establish `h0` using `congrFun (congrFun h 1) 0`. Establish `h1` using `congrFun (congrFun h 1) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h0 h1`.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ hd, Matrix.det_fin_two]`. Take the linear combination `((m : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * h1 - ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * h0`.
-/
private lemma unitary_two_conj_entry_eq (m : U2) : conj ((m : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
    (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((m : Matrix (Fin 2) (Fin 2) ℂ).det)⁻¹ := by
  have hd := det_ne_zero_of_U2 m
  have h : star (m : Matrix (Fin 2) (Fin 2) ℂ) * (m : Matrix (Fin 2) (Fin 2) ℂ) = 1 := m.2.1
  have h0 := congrFun (congrFun h 1) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h0 h1
  rw [eq_mul_inv_iff_mul_eq₀ hd, Matrix.det_fin_two]
  linear_combination ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * h1 - ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * h0

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 1 ∧ π 3 = 3` from `by decide`. Use `⟨F 0 1 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c1 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α) (hq : q = β + δ)
    (hn' : n' = γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 1 ∧ π 3 = 3 := by decide
  refine ⟨F 0 1 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 3` from `by decide`. Use `⟨F 0 2 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c2 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β) (hq : q = δ)
    (hn' : n' = β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 3 := by decide
  refine ⟨F 0 2 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 1` from `by decide`. Use `⟨F 0 2 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c3 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β + γ) (hq : q = δ - γ)
    (hn' : n' = β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 1 := by decide
  refine ⟨F 0 2 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 3` from `by decide`. Use `⟨F 2 0 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c4 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β) (hq : q = δ)
    (hn' : n' = α + β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 3 := by decide
  refine ⟨F 2 0 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 1` from `by decide`. Use `⟨F 2 0 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c5 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β + γ) (hq : q = δ - γ)
    (hn' : n' = α + β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 1 := by decide
  refine ⟨F 2 0 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

/- English proof (translation)
Take `⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 3 ∧ π 3 = 1` from `by decide`. Use `⟨F 2 3 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext x fin_cases x <;> simp [wt, Pi.single_apply] <;> omega`. Establish `ha` using `det_ne_zero_of_U2 a`. Establish `hb` using `det_ne_zero_of_U2 b`.

Rewrite using `[hn, hq, hn', hq']`. Simplify using `only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero, zpow_add₀ ha, zpow_add₀ hb, zpo …`. Clear the denominators using the available nonvanishing facts.
-/
private lemma c6 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = γ) (hq : q = δ - γ)
    (hn' : n' = α) (hq' : q' = β + δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 3 ∧ π 3 = 1 := by decide
  refine ⟨F 2 3 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

/- English proof (translation)
Introduce `n q n' q'`. Distinguish the cases in `h1 : (n' : ℤ) + q' ≤ q`. Conclude with `c1 n (q - n' - q').toNat n' (n' + q') n q n' q' rfl (by omega) rfl (by omega)`. Distinguish the cases in `h2 : (n : ℤ) + q ≤ q'`. Conclude with `c6 n' (q' - n - q).toNat n (n + q) n q n' q' rfl (by omega) rfl (by omega)`.

Distinguish the cases in `h3 : (n' : ℤ) + q' ≤ n + q`. Distinguish the cases in `h4 : q' ≤ q`. Conclude with `c2 (n + q - n' - q').toNat (n' + q' - q).toNat (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)`. Conclude with `c3 (n + q - n' - q').toNat n' (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)`. Distinguish the cases in `h4 : q' ≤ q`.

Conclude with `c4 (n' + q' - n - q).toNat n (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)`. Conclude with `c5 (n' + q' - n - q).toNat (n + q - q').toNat (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefEx :
    ∀ n q n' q', ∃ ψ, Coef ψ n q n' q' := by
  intro n q n' q'
  by_cases h1 : (n' : ℤ) + q' ≤ q
  · exact c1 n (q - n' - q').toNat n' (n' + q') n q n' q' rfl (by omega) rfl (by omega)
  by_cases h2 : (n : ℤ) + q ≤ q'
  · exact c6 n' (q' - n - q).toNat n (n + q) n q n' q' rfl (by omega) rfl (by omega)
  by_cases h3 : (n' : ℤ) + q' ≤ n + q
  · by_cases h4 : q' ≤ q
    · exact c2 (n + q - n' - q').toNat (n' + q' - q).toNat (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c3 (n + q - n' - q').toNat n' (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
  · by_cases h4 : q' ≤ q
    · exact c4 (n' + q' - n - q).toNat n (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c5 (n' + q' - n - q).toNat (n + q - q').toNat (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
