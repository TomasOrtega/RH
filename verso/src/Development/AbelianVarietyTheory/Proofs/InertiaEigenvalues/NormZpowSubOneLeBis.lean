import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLe

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycEigen

section Abstract

variable {C : Type} [NormedField C] [IsUltrametricDist C]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc`.
-/
theorem norm_mulVec_le {r : ℕ} (B : Matrix (Fin r) (Fin r) C) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (v : Fin r → C) (a : Fin r) : ‖B.mulVec v a‖ ≤ c * ‖v‖ := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc

omit [IsUltrametricDist C] in
/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `X.sum_mem fun b _ => hB a b _ (hv b)`.
-/
theorem mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by
  simp only [Matrix.mulVec, dotProduct]
  exact X.sum_mem fun b _ => hB a b _ (hv b)

omit [IsUltrametricDist C] in
/- English proof (translation)
Set `T' : X →+ C` to `AddMonoidHom.mk' (fun x => T x) fun x x' => hadd _ x.2 _ x'.2`. Use function extensionality and compare the values at `a`. Establish `h` using `map_sum T' (fun b => (⟨B a b * v b, hOX _ (hB a b) _ (hv b)⟩ : X)) Finset.univ`. Simplify using `only [T', AddMonoidHom.mk'_apply, AddSubgroup.val_finset_sum] at h`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Rewrite using `[h]`. Conclude with `Finset.sum_congr rfl fun b _ => hlin _ (hB a b) _ (hv b)`.
-/
theorem map_mulVec {r : ℕ} (X : AddSubgroup C) (O : Set C) (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X)
    (T : C → C) (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hB : ∀ a b, B a b ∈ O) (v : Fin r → C) (hv : ∀ a, v a ∈ X) :
    (fun a => T (B.mulVec v a)) = B.mulVec fun a => T (v a) := by
  let T' : X →+ C := AddMonoidHom.mk' (fun x => T x) fun x x' => hadd _ x.2 _ x'.2
  funext a
  have h := map_sum T' (fun b => (⟨B a b * v b, hOX _ (hB a b) _ (hv b)⟩ : X)) Finset.univ
  simp only [T', AddMonoidHom.mk'_apply, AddSubgroup.val_finset_sum] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  exact Finset.sum_congr rfl fun b _ => hlin _ (hB a b) _ (hv b)

/- English proof (translation)
Establish `hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X` using `fun a b => hOX _ (hBO a b)`. Establish `h1 : ∀ (n : ℕ) (z : Fin r → C), (∀ a, z a ∈ X) → (∀ a, B.mulVec^[n] z a ∈ X) ∧ ‖B.mulVec^[n] z‖ ≤ c ^ n ∧ (fun a => T (B.mulVec^[n] z a)) = B.mulVec^[n] fun a => T (z a)`. Introduce `n z hz`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨hz, (pi_norm_le_iff_of_nonneg (by simp)).2 fun a => by`.

Simplify using `using hX1 _ (hz a), rfl⟩`. Consider the case `succ n ih`. Take `⟨i1, i2, i3⟩` from `ih`. Simplify using `only [Function.iterate_succ_apply']`. Use `⟨mulVec_mem X B hBX _ i1, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ']`. Conclude with `(norm_mulVec_le B hc hB _ a).trans (mul_le_mul_of_nonneg_left i2 hc)`. Rewrite using `[map_mulVec X O hOX T hadd hlin B hBO _ i1, i3]`. Establish `h2 : ∀ n : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ y = B.mulVec^[n] z`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨y, hy, rfl⟩`. Consider the case `succ n ih`. Take `⟨z, hz, e⟩` from `ih`. Use `⟨fun a => T (z a), fun a => hTX _ (hz a), ?_⟩` and prove the remaining obligations.

Rewrite using `[Function.iterate_succ_apply', ← (h1 n z hz).2.2, ← e]`. Conclude with `h`. Establish `h3 : ∀ n : ℕ, ‖y‖ ≤ c ^ n` using `fun n => by`. Take `⟨z, hz, e⟩` from `h2 n`. Rewrite using `[e]`.

Conclude with `(h1 n z hz).2.1`. Conclude with `norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) h3)`.
-/
theorem eq_zero_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (O : Set C)
    (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X) (T : C → C) (hTX : ∀ x ∈ X, T x ∈ X)
    (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hBO : ∀ a b, B a b ∈ O) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : y = B.mulVec fun a => T (y a)) : y = 0 := by
  have hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X := fun a b => hOX _ (hBO a b)
  have h1 : ∀ (n : ℕ) (z : Fin r → C), (∀ a, z a ∈ X) →
      (∀ a, B.mulVec^[n] z a ∈ X) ∧ ‖B.mulVec^[n] z‖ ≤ c ^ n ∧
        (fun a => T (B.mulVec^[n] z a)) = B.mulVec^[n] fun a => T (z a) := by
    intro n z hz
    induction n with
    | zero => exact ⟨hz, (pi_norm_le_iff_of_nonneg (by simp)).2 fun a => by
        simpa using hX1 _ (hz a), rfl⟩
    | succ n ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      simp only [Function.iterate_succ_apply']
      refine ⟨mulVec_mem X B hBX _ i1, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_, ?_⟩
      · rw [pow_succ']
        exact (norm_mulVec_le B hc hB _ a).trans (mul_le_mul_of_nonneg_left i2 hc)
      · rw [map_mulVec X O hOX T hadd hlin B hBO _ i1, i3]
  have h2 : ∀ n : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ y = B.mulVec^[n] z := by
    intro n
    induction n with
    | zero => exact ⟨y, hy, rfl⟩
    | succ n ih =>
      obtain ⟨z, hz, e⟩ := ih
      refine ⟨fun a => T (z a), fun a => hTX _ (hz a), ?_⟩
      rw [Function.iterate_succ_apply', ← (h1 n z hz).2.2, ← e]
      exact h
  have h3 : ∀ n : ℕ, ‖y‖ ≤ c ^ n := fun n => by
    obtain ⟨z, hz, e⟩ := h2 n
    rw [e]; exact (h1 n z hz).2.1
  exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) h3)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le`. Consider the case `exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le`. Consider the case `(apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le ..)`.
-/
theorem norm_zpow_sub_one_le (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le ..)

end Abstract

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Establish `h2 : 2 ≤ l` using `hl.1.two_le`. Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Rewrite using `[rho1, ← Real.rpow_intCast]`. Apply `Real.rpow_lt_rpow_of_exponent_lt h1` to reduce the goal to its premises. Rewrite using `[lt_div_iff₀ (by linarith)]`.

Use `push_cast`. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj.1`. Break down `h2.eq_or_lt with h | h` into its components or cases. Establish `hj2 : (2 : ℝ) ≤ j` using `by exact_mod_cast hj.2 h.symm`. Establish `: (l : ℝ) = 2` using `by exact_mod_cast h.symm`.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (3 : ℝ) ≤ l` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pow_lt_rho {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Rewrite using `[rho1]`. Apply `Real.rpow_lt_one_of_one_lt_of_neg h1` to reduce the goal to its premises. Conclude with `div_neg_of_neg_of_pos (by norm_num) (by linarith)`.
-/
theorem rho_lt_one : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/- English proof (translation)
Use `GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])` as an intermediate fact. Simplify `this` using `[rho1]`.
-/
theorem norm_root_sub_one {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) : ‖ζ - 1‖ = rho1 l := by
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  simpa [rho1] using this

/- English proof (translation)
Simplify using `[inC, PadicComplex.coe_eq]`.
-/
theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := by
  simp [inC, PadicComplex.coe_eq]

/- English proof (translation)
Use `haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l`. Establish `hη'` using `hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective`. Take `⟨k, -, hk⟩` from `hη'.eq_pow_of_pow_eq_one h.pow_eq_one`. Use `⟨η ^ k, ?_, ?_⟩` and prove the remaining obligations.

Use `pow_mem (?_ : η ∈ Ks K j) k` and prove the remaining obligations. Use `(le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations. Conclude with `(hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))`. Simplify using `only [PadicComplex.coe_eq, map_pow]`. Conclude with `hk`.
-/
theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩`.
-/
theorem chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩

/- English proof (translation)
Establish `h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l` using `hg.2 ▸ pow_lt_rho hj`. Establish `h2` using `norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i`. Establish `e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1)`. Simplify using `[chiC]`. Rewrite using `[e, norm_algebraMap']`.

Conclude with `h2.trans_lt h1`.
-/
theorem norm_chiC_sub_one {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1

/- English proof (translation)
Establish `hz` using `norm_root_sub_one h`. Establish `hz0 : ζ - 1 ≠ 0` using `sub_ne_zero.2 (h.ne_one hl.1.one_lt)`. Establish `hzp : 0 < ‖ζ - 1‖` using `norm_pos_iff.2 hz0`. Establish `hc` using `norm_chiC_sub_one hj hg i`. Establish `hc1 : ‖chiC χ i g‖ ≤ 1`.

Use `IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le (hc.trans rho_lt_one).le le_rfl)`. Set `B : Matrix (Fin r) (Fin r) (PadicComplex l)` to `(ζ - 1)⁻¹ • (chiC χ i g • U - 1)`. Establish `hB : ∀ a b, ‖B a b‖ < 1`.

Introduce `a b`. Establish `e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b)`. Simplify using `only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)`. Rewrite using `[norm_mul]`. Use `(mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc` and prove the remaining obligations.

Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Use `⟨B, ‖fun p : Fin r × Fin r => B p.1 p.2‖, norm_nonneg _, (pi_norm_lt_iff one_pos).2 fun p => hB _ _, fun a b => norm_le_pi_norm (fun p : Fin r × Fin r => B p.1 p.2) (a, b), fun a b => ⟨?_, (hB a b).le⟩, ?_⟩` and prove the remaining obligations. Establish `m1` using `(mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)`. Establish `m2` using `(mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))`. Establish `m3` using `(mem_inC_iff _ _).1 (hU a b).1`.

Rewrite using `[mem_inC_iff]`. Simplify using `only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Use `mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Simplify using `only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_quot {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) {r : ℕ} (U : Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U - 1) a b‖ < rho1 l) (i : ℤ)
    {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) :
    ∃ (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (c : ℝ), 0 ≤ c ∧ c < 1 ∧
      (∀ a b, ‖B a b‖ ≤ c) ∧ (∀ a b, B a b ∈ intC (Ks K j)) ∧
      chiC χ i g • U = 1 + (ζ - 1) • B := by
  have hz := norm_root_sub_one h
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  have hzp : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hz0
  have hc := norm_chiC_sub_one hj hg i
  have hc1 : ‖chiC χ i g‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hc.trans rho_lt_one).le le_rfl)
  let B : Matrix (Fin r) (Fin r) (PadicComplex l) := (ζ - 1)⁻¹ • (chiC χ i g • U - 1)
  have hB : ∀ a b, ‖B a b‖ < 1 := by
    intro a b
    have e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b
        + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b) := by
      simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
    rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc
      rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨B, ‖fun p : Fin r × Fin r => B p.1 p.2‖, norm_nonneg _,
    (pi_norm_lt_iff one_pos).2 fun p => hB _ _,
    fun a b => norm_le_pi_norm (fun p : Fin r × Fin r => B p.1 p.2) (a, b),
    fun a b => ⟨?_, (hB a b).le⟩, ?_⟩
  · have m1 := (mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)
    have m2 := (mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))
    have m3 := (mem_inC_iff _ _).1 (hU a b).1
    rw [mem_inC_iff]
    simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]; abel

/- English proof (translation)
Rewrite using `[twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twAct_sub {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ} {i : ℤ}
    {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l} {p : PadicComplex l}
    {B : Matrix (Fin r) (Fin r) (PadicComplex l)} (h : chiC χ i g • U g = 1 + p • B)
    (y : Fin r → PadicComplex l) (a : Fin r) :
    (twAct act χ i U g y - y) a
      = act g (y a) - y a + p * B.mulVec (fun b => act g (y b)) a := by
  rw [twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hy`. Rewrite using `[ha.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx]`.
-/
theorem act_inC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [ha.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx]

/- English proof (translation)
Establish `: closure (intC (Kinf K)) ⊆ {y : PadicComplex l | ‖y‖ ≤ 1}` using `closure_minimal (fun _ h => h.2) (isClosed_le continuous_norm continuous_const)`. Conclude with `this hy`.
-/
theorem ohat_norm (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have : closure (intC (Kinf K)) ⊆ {y : PadicComplex l | ‖y‖ ≤ 1} :=
    closure_minimal (fun _ h => h.2) (isClosed_le continuous_norm continuous_const)
  exact this hy

/- English proof (translation)
Take `⟨-, -, hO, hmul, hstab, -⟩` from `GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1`. Establish `hg0 : g ∈ (K0 K).fixingSubgroup` using `IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1`. Establish `hgX` using `hstab g hg0`. Use `haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l`.

Take `⟨S, hS, hadd, hlin⟩` from `GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ`. Take `⟨B, c, hc0, hc1, hB, hBO, hBe⟩` from `exists_quot hj hg (U g) hU hU1 i hζ`. Establish `hBO' : ∀ a b, (-B) a b ∈ intC (Ks K j)` using `fun a b => ⟨(mem_inC_iff _ _).2 (neg_mem ((mem_inC_iff _ _).1 (hBO a b).1)), by`. Rewrite using `[Matrix.neg_apply, norm_neg]`. Conclude with `(hBO a b).2⟩`.

Establish `hp : ζ - 1 ∈ intC (Ks K j)` using `⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)), by`. Rewrite using `[norm_root_sub_one hζ]`. Conclude with `rho_lt_one.le⟩`. Establish `hp0 : ζ - 1 ≠ 0` using `sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)`. Use `eq_zero_of_small (Xj K j) (fun x hx => ohat_norm K (hO x hx)) _ hmul (fun x => S (act g x)) (fun x hx => (hS _ (hgX x hx)).1) (fun x hx x' hx' => by rw [map_add, hadd _ (hgX x hx) _ (hgX x' hx')]) (fun o ho x hx => by rw [map_mul, act_inC hact hg.1 ho.1, hlin _ ho _ (hgX x hx)]) …` and prove the remaining obligations.

Rewrite using `[← map_mulVec (Xj K j) _ hmul S hadd hlin (-B) hBO' _ fun a => hgX _ (hy a)]`. Use function extensionality and compare the values at `a`. Establish `h1 : act g (y a) - y a = (ζ - 1) * (-B).mulVec (fun b => act g (y b)) a`. Use `twAct_sub (act := act) hBe y a` as an intermediate fact. Rewrite `this` using `[hfix, sub_self, Pi.zero_apply]`.

Rewrite using `[Matrix.neg_mulVec, Pi.neg_apply]`. Take the linear combination `-this`. Establish `h2` using `(hS _ (hy a)).2.2`. Rewrite `h2` using `[h1, hlin _ hp _ (mulVec_mem (Xj K j) (-B) (fun a b => hmul _ (hBO' a b)) _ (fun b => hgX _ (hy b)) a)]`. Conclude with `(mul_left_cancel₀ hp0 h2).symm`.
-/
theorem twAct_fixed_eq_zero {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U g a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U g - 1) a b‖ < rho1 l) (i : ℤ)
    (y : Fin r → PadicComplex l) (hy : ∀ a, y a ∈ Xj K j) (hfix : twAct act χ i U g y = y) :
    y = 0 := by
  obtain ⟨-, -, hO, hmul, hstab, -⟩ :=
    GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  obtain ⟨S, hS, hadd, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
  obtain ⟨B, c, hc0, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
  have hBO' : ∀ a b, (-B) a b ∈ intC (Ks K j) := fun a b =>
    ⟨(mem_inC_iff _ _).2 (neg_mem ((mem_inC_iff _ _).1 (hBO a b).1)), by
      rw [Matrix.neg_apply, norm_neg]; exact (hBO a b).2⟩
  have hp : ζ - 1 ∈ intC (Ks K j) :=
    ⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)), by
      rw [norm_root_sub_one hζ]; exact rho_lt_one.le⟩
  have hp0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  refine eq_zero_of_small (Xj K j) (fun x hx => ohat_norm K (hO x hx)) _ hmul
    (fun x => S (act g x)) (fun x hx => (hS _ (hgX x hx)).1)
    (fun x hx x' hx' => by rw [map_add, hadd _ (hgX x hx) _ (hgX x' hx')])
    (fun o ho x hx => by rw [map_mul, act_inC hact hg.1 ho.1, hlin _ ho _ (hgX x hx)])
    (-B) hBO' hc0 hc1 (fun a b => by rw [Matrix.neg_apply, norm_neg]; exact hB a b) y hy ?_
  rw [← map_mulVec (Xj K j) _ hmul S hadd hlin (-B) hBO' _ fun a => hgX _ (hy a)]
  funext a
  have h1 : act g (y a) - y a = (ζ - 1) * (-B).mulVec (fun b => act g (y b)) a := by
    have := twAct_sub (act := act) hBe y a
    rw [hfix, sub_self, Pi.zero_apply] at this
    rw [Matrix.neg_mulVec, Pi.neg_apply]
    linear_combination -this
  have h2 := (hS _ (hy a)).2.2
  rw [h1, hlin _ hp _ (mulVec_mem (Xj K j) (-B) (fun a b => hmul _ (hBO' a b)) _
    (fun b => hgX _ (hy b)) a)] at h2
  exact (mul_left_cancel₀ hp0 h2).symm

end GlobalTheory.CycEigen
