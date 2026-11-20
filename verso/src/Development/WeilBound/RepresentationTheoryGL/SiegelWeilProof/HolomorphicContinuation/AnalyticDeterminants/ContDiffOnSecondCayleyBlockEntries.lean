import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cdo_matrix {ι κ : Type} [Fintype ι] [Fintype κ] {s : Set E} {M : E → Matrix ι κ ℂ} :
    ContDiffOn ℂ ∞ M s ↔ ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s := by
  constructor
  · intro h i j
    have h1 : ContDiffOn ℂ ∞ (fun x => M x i) s := (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).1 h i
    exact (contDiffOn_pi (Φ := fun x => M x i)).1 h1 j
  · intro h
    exact (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).2 fun i =>
      (contDiffOn_pi (Φ := fun x => M x i)).2 fun j => h i j

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cdo_det {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (h : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem cdo_zpow {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (k : ℤ) :
    ContDiffOn ℂ ∞ (fun x => f x ^ k) s := by
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast] using hf.pow j
  · refine ((hf.pow j).inv fun x hx => pow_ne_zero j (h0 x hx)).congr fun x _ => ?_
    simp [_root_.zpow_neg]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cd_entry {ι κ : Type} [Fintype ι] [Fintype κ] (i : ι) (j : κ) :
    ContDiff ℂ ∞ (fun x : Matrix ι κ ℂ => x i j) :=
  contDiff_apply_apply (𝕜 := ℂ) (E := ℂ) i j

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiff_first_cayley_block : ContDiff ℂ ∞ (u1 (n := n)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  refine (cdo_matrix (s := Set.univ)).2 (fun i j => ?_) |>.contDiffAt Filter.univ_mem
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((contDiff_const.mul (cd_entry _ _)).add (cd_entry _ _)).contDiffOn

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiff_second_cayley_block : ContDiff ℂ ∞ (u2 (n := n)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  refine (cdo_matrix (s := Set.univ)).2 (fun i j => ?_) |>.contDiffAt Filter.univ_mem
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact ((contDiff_const.mul (cd_entry _ _)).neg.add (cd_entry _ _)).contDiffOn

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cdo_mul {ι κ μ' : Type} [Fintype ι] [Fintype κ] [Fintype μ'] {s : Set E} {M : E → Matrix ι κ ℂ}
    {N : E → Matrix κ μ' ℂ} (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s)
    (hN : ∀ i j, ContDiffOn ℂ ∞ (fun x => N x i j) s) : ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x * N x) i j) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hM i k).mul (hN k j)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cdo_inv {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) (h0 : ∀ x ∈ s, (M x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x)⁻¹ i j) s := by
  intro i j
  have e : ∀ x, (M x)⁻¹ i j = ((M x).det)⁻¹ * ((M x).updateRow j (Pi.single i 1)).det := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ((cdo_det hM).inv h0).mul (cdo_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM a b

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem contDiffOn_first_cayley_block_entries (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x => u1 x i j) s := fun i j =>
  ((cdo_matrix (M := u1 (n := n)) (s := s)).1 contDiff_first_cayley_block.contDiffOn) i j

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem contDiffOn_second_cayley_block_entries (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x => u2 x i j) s := fun i j =>
  ((cdo_matrix (M := u2 (n := n)) (s := s)).1 contDiff_second_cayley_block.contDiffOn) i j

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem cdo_id (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => x i j) s := fun i j =>
  (cd_entry i j).contDiffOn

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cdo_wM (s : Set (M2 n)) (hs : ∀ x ∈ s, (u2 x).det ≠ 0) : ∀ i j, ContDiffOn ℂ ∞ (fun x => wM x i j) s :=
  cdo_mul (cdo_inv (contDiffOn_second_cayley_block_entries s) hs) (contDiffOn_first_cayley_block_entries s)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem det_wM (x : M2 n) (h2 : (u2 x).det ≠ 0) : (wM x).det = ((u2 x).det)⁻¹ * (u1 x).det := by
  rw [wM, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cdo_wM_inv (s : Set (M2 n)) (hs : ∀ x ∈ s, (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (wM x)⁻¹ i j) s :=
  cdo_inv (cdo_wM s fun x hx => (hs x hx).2) fun x hx => by
    rw [det_wM x (hs x hx).2]; exact mul_ne_zero (inv_ne_zero (hs x hx).2) (hs x hx).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cdo_minorOn {s : Set E} (t : Finset (Fin n)) {M : E → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => minorOn t (M x)) s :=
  cdo_det fun i j => hM _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiffOn_inverse_first_block (s : Set (M2 n)) (hs : ∀ x ∈ s, IsUnit x.det) : ∀ i j, ContDiffOn ℂ ∞ (fun x => ub1 x i j) s := by
  intro i j
  have hinv := cdo_inv (cdo_id s) fun x hx => (hs x hx).ne_zero
  simp only [ub1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (hinv _ _).add (contDiffOn_const.mul (hinv _ _))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem contDiffOn_scalar_section_of_units (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := by
  unfold f0
  exact (cdo_zpow (cdo_det (contDiffOn_first_cayley_block_entries _)) (fun x hx => hx.1) _).mul (cdo_zpow (cdo_det (contDiffOn_second_cayley_block_entries _)) (fun x hx => hx.2) _)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem dom_sub (x : M2 n) (hx : x ∈ Dom n) : (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 := ⟨hx.2.1, hx.2.2.1⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.
-/
theorem contDiffOn_hF' (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := by
  unfold hF
  refine (((contDiffOn_scalar_section_of_units p q).mono fun x hx => dom_sub x hx).mul
    (cdo_minorOn _ (cdo_wM _ fun x hx => hx.2.2.1))).mul (cdo_minorOn _ (cdo_wM_inv _ dom_sub))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem contDiffOn_fV' (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := by
  unfold fV
  exact ((cdo_zpow (cdo_det (contDiffOn_first_cayley_block_entries _)) (fun x hx => hx.2.1) _).mul
    (cdo_zpow (cdo_det (contDiffOn_second_cayley_block_entries _)) (fun x hx => hx.2.2.1) _)).mul
    (cdo_zpow (cdo_det (contDiffOn_inverse_first_block _ fun x hx => hx.1)) (fun x hx => hx.2.2.2) _)

def Cinv (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Cm_mul_Cinv : Cm n * Cinv n = 1 := by
  have hI : (2 * Complex.I) ≠ 0 := by simp
  rw [Cm, Cinv, Matrix.mul_smul, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
      smul_eq_mul, Matrix.smul_apply] <;>
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, one_mul, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    split_ifs <;> (try simp_all) <;> (try split_ifs) <;> (try simp_all) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Cm_inv : (Cm n)⁻¹ = Cinv n := Matrix.inv_eq_right_inv Cm_mul_Cinv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Cinv_mul_Cm : (Cm n)⁻¹ * Cm n = 1 := by
  rw [Matrix.nonsing_inv_mul]
  exact (Matrix.isUnit_det_of_right_inverse Cm_mul_Cinv)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Cm_mul_inv : Cm n * (Cm n)⁻¹ = 1 := by rw [Cm_inv]; exact Cm_mul_Cinv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem fromBlocks_one_eq (Q R : Matrix (Fin n) (Fin n) ℂ) :
    (fromBlocks 1 Q R 1 : M2 n) = 1 + fromBlocks 0 Q R 0 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mX_eq' (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹ := by
  rw [mX, fromBlocks_one_eq, Matrix.mul_add, Matrix.add_mul, mul_one, Cm_mul_inv]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem embOn_mul_embOn_disj {s t : Finset (Fin n)} (hst : ∀ c, c ∈ s → c ∉ t) (T : Matrix s s ℂ) (S : Matrix t t ℂ) :
    embOn s T * embOn t S = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply, embOn]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : a ∈ s ∧ c ∈ s
  · by_cases h2 : c ∈ t ∧ b ∈ t
    · exact absurd h2.1 (hst c h1.2)
    · rw [dif_neg h2, mul_zero]
  · rw [dif_neg h1, zero_mul]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem WD_prod (Q R Q' R' : Matrix (Fin n) (Fin n) ℂ) :
    (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * fromBlocks (Q * R') 0 0 (R * Q') * (Cm n)⁻¹ := by
  have e : (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * (fromBlocks 0 Q R 0 * ((Cm n)⁻¹ * Cm n) * fromBlocks 0 Q' R' 0) * (Cm n)⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, Cinv_mul_Cm, mul_one, Matrix.fromBlocks_multiply]
  simp

def mulLc (M : M2 n) : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ M)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulLc_apply (M v : M2 n) : mulLc M v = M * v := rfl

def mulLcL : M2 n →ₗ[ℂ] (M2 n →L[ℂ] M2 n) where
  toFun := mulLc
  map_add' a b := by ext1 v; simp [mulLc_apply, Matrix.add_mul]
  map_smul' c a := by ext1 v; simp [mulLc_apply, Matrix.smul_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_mulLc : Continuous (fun M : M2 n => mulLc M) :=
  (mulLcL (n := n)).continuous_of_finiteDimensional

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem left_mul' (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (M x : M2 n)
    (hx : M * x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F (M * y)) x v = iteratedFDeriv ℂ N F (M * x) (fun i => M * v i) := by
  have hV' : IsOpen (mulLc M ⁻¹' U) := hU.preimage (mulLc M).continuous
  have key := (mulLc M).iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hV'.uniqueDiffOn
    (show mulLc M x ∈ U from hx) (i := N) (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ N (F ∘ mulLc M) (mulLc M ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ mulLc M) x :=
    iteratedFDerivWithin_of_isOpen N hV' (show x ∈ mulLc M ⁻¹' U from hx)
  have e2 : iteratedFDerivWithin ℂ N F U (mulLc M x) = iteratedFDeriv ℂ N F (mulLc M x) :=
    iteratedFDerivWithin_of_isOpen N hU (show mulLc M x ∈ U from hx)
  have key' : iteratedFDeriv ℂ N (F ∘ mulLc M) x =
      (iteratedFDeriv ℂ N F (mulLc M x)).compContinuousLinearMap (fun _ => mulLc M) :=
    e1.symm.trans (key.trans (congrArg (fun A => ContinuousMultilinearMap.compContinuousLinearMap A
      (fun _ : Fin N => mulLc M)) e2))
  exact congrArg (fun A => A v) key'

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cont_translate' (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by
  set Φ := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ (fun _ : Fin N => M2 n)
    (fun _ : Fin N => M2 n) ℂ with hΦ
  have h1 : ContinuousOn (iteratedFDeriv ℂ N F) U :=
    (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)
  have hA : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2))
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) :=
    h1.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)
  have hL : Continuous (fun y : Kg × M2 n => Φ (fun _ => mulLc (ι y.1))) :=
    Φ.cont.comp (continuous_pi fun _ => continuous_mulLc.comp (hι.comp continuous_fst))
  refine (((hc.comp continuous_fst).continuousOn).smul (hL.continuousOn.clm_apply hA)).congr ?_
  intro y hy
  have hyU : ι y.1 * y.2 ∈ U := hy.2 y.1
  have hcd : ContDiffAt ℂ N (fun x => F (ι y.1 * x)) y.2 :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).comp y.2 (mulLc (ι y.1)).contDiff.contDiffAt).of_le
      (by exact_mod_cast le_top)
  have e : (fun x => F (ι y.1 * x) * c y.1) = c y.1 • (fun x => F (ι y.1 * x)) := by
    funext x; simp [smul_eq_mul, mul_comm]
  ext v
  simp only [Function.comp_apply]
  rw [e, iteratedFDeriv_const_smul_apply hcd, _root_.smul_apply, smul_eq_mul,
    left_mul' F U hU hF (ι y.1) y.2 hyU N v]
  rfl

end PositivityTheory.Rg.Sw.LVs
