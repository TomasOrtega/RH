import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

noncomputable section

namespace GlobalTheory.MajorantConj

section General

open scoped Matrix

abbrev sgnDiag (A : Type) [CommRing A] {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) A :=
  Matrix.diagonal fun i => if ε i then 1 else -1

/- English proof (translation)
Simplify using `only [sgnDiag, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply] <;> ring`.
-/
theorem re_form {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (sgnDiag ℂ ε *ᵥ x)).re = ∑ i, (if ε i then 1 else -1) * Complex.normSq (x i) := by
  simp only [sgnDiag, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply] <;> ring

/- English proof (translation)
Establish `key : ∀ x : Fin n → ℂ, star x ⬝ᵥ (sgnDiag ℂ ε' *ᵥ x) = star (M *ᵥ x) ⬝ᵥ (sgnDiag ℂ ε *ᵥ (M *ᵥ x))`. Introduce `x`. Rewrite using `[← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Set `T` to `(LinearMap.funLeft ℂ ℂ (Subtype.val : {i // ε i = false} → Fin n)) ∘ₗ M.mulVecLin ∘ₗ (Function.ExtendByZero.linearMap ℂ (Subtype.val : {i // ε' i = false} → Fin n))`. Establish `hT : Function.Injective T`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Take `⟨x, hx⟩ : ∃ x : Fin n → ℂ, x = Function.extend Subtype.val y 0` from `⟨_, rfl⟩`. Establish `hxt : ∀ i, ε' i = true → x i = 0`. Introduce `i hi`.

Rewrite using `[hx, Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨j, rfl⟩`. Rewrite `hi` using `[j.2]`. Conclude with `Bool.false_ne_true hi`.

Establish `hxf : ∀ j : {i // ε' i = false}, x j.1 = y j` using `fun j => by`. Rewrite using `[hx]`. Conclude with `Subtype.val_injective.extend_apply _ _ _`. Establish `hv : ∀ j : {i // ε i = false}, (M *ᵥ x) j.1 = 0` using `fun j => by`. Use `congrFun hy j` as an intermediate fact.

Rewrite using `[hx]`. Conclude with `this`. Establish `h1` using `congrArg Complex.re (key x)`. Rewrite `h1` using `[re_form, re_form]`. Establish `hL : ∀ i, (if ε' i then (1 : ℝ) else -1) * Complex.normSq (x i) = -Complex.normSq (x i)`.

Introduce `i`. Consider the cases of `hi : ε' i`. Simplify using the standard rewrite rules. Simplify using `[hxt i hi]`. Establish `hR : 0 ≤ ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq ((M *ᵥ x) i)`.

Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Consider the cases of `hi : ε i`. Simplify using `[hv ⟨i, hi⟩]`. Simplify using `[Complex.normSq_nonneg]`.

Simplify using `only [hL, Finset.sum_neg_distrib] at h1`. Establish `hz : ∑ i, Complex.normSq (x i) = 0` using `le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)`. Rewrite `hz` using `[Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)]`. Use function extensionality and compare the values at `j`. Rewrite using `[← hxf j]`.

Conclude with `Complex.normSq_eq_zero.mp (hz j.1 (Finset.mem_univ _))`. Use `LinearMap.finrank_le_finrank_of_injective hT` as an intermediate fact. Simplify `this` using `[Module.finrank_fintype_fun_eq_card]`.
-/
theorem card_neg_le {n : ℕ} (ε ε' : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * sgnDiag ℂ ε * M = sgnDiag ℂ ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have key : ∀ x : Fin n → ℂ,
      star x ⬝ᵥ (sgnDiag ℂ ε' *ᵥ x) = star (M *ᵥ x) ⬝ᵥ (sgnDiag ℂ ε *ᵥ (M *ᵥ x)) := by
    intro x
    rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  let T := (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // ε i = false} → Fin n)) ∘ₗ M.mulVecLin ∘ₗ
    (Function.ExtendByZero.linearMap ℂ (Subtype.val : {i // ε' i = false} → Fin n))
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℂ, x = Function.extend Subtype.val y 0 := ⟨_, rfl⟩
    have hxt : ∀ i, ε' i = true → x i = 0 := by
      intro i hi
      rw [hx, Function.extend_apply']
      · rfl
      · rintro ⟨j, rfl⟩
        rw [j.2] at hi
        exact Bool.false_ne_true hi
    have hxf : ∀ j : {i // ε' i = false}, x j.1 = y j := fun j => by
      rw [hx]
      exact Subtype.val_injective.extend_apply _ _ _
    have hv : ∀ j : {i // ε i = false}, (M *ᵥ x) j.1 = 0 := fun j => by
      have := congrFun hy j
      rw [hx]
      exact this
    have h1 := congrArg Complex.re (key x)
    rw [re_form, re_form] at h1
    have hL : ∀ i, (if ε' i then (1 : ℝ) else -1) * Complex.normSq (x i) = -Complex.normSq (x i) := by
      intro i
      cases hi : ε' i
      · simp
      · simp [hxt i hi]
    have hR : 0 ≤ ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq ((M *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      cases hi : ε i
      · simp [hv ⟨i, hi⟩]
      · simp [Complex.normSq_nonneg]
    simp only [hL, Finset.sum_neg_distrib] at h1
    have hz : ∑ i, Complex.normSq (x i) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)] at hz
    funext j
    rw [← hxf j]
    exact Complex.normSq_eq_zero.mp (hz j.1 (Finset.mem_univ _))
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Module.finrank_fintype_fun_eq_card] using this

/- English proof (translation)
Establish `e0 : {i // ε i = false} ≃ {i // ε' i = false}` using `Fintype.equivOfCardEq h.symm`. Establish `e1 : {i // ¬ε i = false} ≃ {i // ¬ε' i = false}` using `Fintype.equivOfCardEq (by`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_subtype_compl, h])`. Use `⟨(Equiv.sumCompl fun i => ε i = false).symm.trans ((e0.sumCongr e1).trans (Equiv.sumCompl fun i => ε' i = false)), fun i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : ε i = false`.

Simplify using `only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`. Rewrite using `[hi]`. Conclude with `(e0 ⟨i, hi⟩).2`. Simplify using `only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]`. Use `(e1 ⟨i, hi⟩).2` as an intermediate fact.

Simplify using `only [Bool.not_eq_false] at hi this`. Rewrite using `[hi, this]`.
-/
theorem exists_perm {n : ℕ} (ε ε' : Fin n → Bool)
    (h : Fintype.card {i // ε' i = false} = Fintype.card {i // ε i = false}) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ε' (π i) = ε i := by
  classical
  have e0 : {i // ε i = false} ≃ {i // ε' i = false} := Fintype.equivOfCardEq h.symm
  have e1 : {i // ¬ε i = false} ≃ {i // ¬ε' i = false} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h])
  refine ⟨(Equiv.sumCompl fun i => ε i = false).symm.trans
    ((e0.sumCongr e1).trans (Equiv.sumCompl fun i => ε' i = false)), fun i => ?_⟩
  by_cases hi : ε i = false
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [hi]
    exact (e0 ⟨i, hi⟩).2
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have := (e1 ⟨i, hi⟩).2
    simp only [Bool.not_eq_false] at hi this
    rw [hi, this]

variable {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cT_mul (M N : Matrix (Fin n) (Fin n) A) : Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_one s (map_zero s) (map_one s), Matrix.transpose_one]`.
-/
theorem cT_one : Formalism.UG.cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one s (map_zero s) (map_one s), Matrix.transpose_one]

/- English proof (translation)
Rewrite using `[← h]`. Establish `h1 : Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1 = 1`. Rewrite using `[← cT_mul, Units.mul_inv, cT_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = J := by rw [h1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem congr_inv {J D : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D) :
    Formalism.UG.cT s (b⁻¹).1 * D * (b⁻¹).1 = J := by
  rw [← h]
  have h1 : Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1 = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  calc Formalism.UG.cT s (b⁻¹).1 * (Formalism.UG.cT s b.1 * J * b.1) * (b⁻¹).1
      = (Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1) * J * (b.1 * (b⁻¹).1) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[← h', ← h, Units.val_mul, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem congr_mul {J D D' : Matrix (Fin n) (Fin n) A} (b c : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D)
    (h' : Formalism.UG.cT s c.1 * D * c.1 = D') : Formalism.UG.cT s (b * c).1 * J * (b * c).1 = D' := by
  rw [← h', ← h, Units.val_mul, cT_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hc : (Formalism.UG.cT s M).map φ = (M.map φ)ᴴ`. Use extensionality with `i j`. Use `show φ (s (M j i)) = star (φ (M j i))`. Rewrite using `[← hφ]`. Both sides reduce to the same expression.

Establish `hd : ∀ e : Fin n → Bool, (sgnDiag A e).map φ = sgnDiag ℂ e`. Introduce `e`. Rewrite using `[sgnDiag, Matrix.diagonal_map (map_zero φ)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `congrArg (fun X => X.map φ) h`. Simplify using `only [Matrix.map_mul, hc, hd] at h2`. Conclude with `card_neg_le ε ε' (M.map φ) h2`.
-/
theorem card_neg_le' (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) (ε ε' : Fin n → Bool)
    (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * sgnDiag A ε * M = sgnDiag A ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have hc : (Formalism.UG.cT s M).map φ = (M.map φ)ᴴ := by
    ext i j
    show φ (s (M j i)) = star (φ (M j i))
    rw [← hφ]
    rfl
  have hd : ∀ e : Fin n → Bool, (sgnDiag A e).map φ = sgnDiag ℂ e := by
    intro e
    rw [sgnDiag, Matrix.diagonal_map (map_zero φ)]
    congr 1
    funext i
    split_ifs <;> simp
  have h2 := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul, hc, hd] at h2
  exact card_neg_le ε ε' (M.map φ) h2

def permGL (π : Equiv.Perm (Fin n)) : GL (Fin n) A where
  val := (1 : Matrix (Fin n) (Fin n) A).submatrix id π
  inv := (1 : Matrix (Fin n) (Fin n) A).submatrix π id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv]
    simp
  inv_val := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]

/- English proof (translation)
Establish `hP : ((permGL (A` using `A) π).1).map s = (permGL (A := A) π).1 := by show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π).map s = (1 : Matrix (Fin n) (Fin n) A).submatrix id π`. Rewrite using `[← Matrix.submatrix_map, Matrix.map_one s (map_zero s) (map_one s)]`. Unfold `Formalism.UG.cT`. Rewrite using `[hP]`. Use `show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π)ᵀ * Matrix.diagonal d * (1 : Matrix (Fin n) (Fin n) A).submatrix id π = _`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.transpose_apply]`. Use `split_ifs with hij`. Rewrite using `[hij]`. Both sides reduce to the same expression.
-/
theorem permGL_diagonal (π : Equiv.Perm (Fin n)) (d : Fin n → A) :
    Formalism.UG.cT s (permGL (A := A) π).1 * Matrix.diagonal d * (permGL (A := A) π).1 = Matrix.diagonal fun i => d (π i) := by
  have hP : ((permGL (A := A) π).1).map s = (permGL (A := A) π).1 := by
    show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π).map s = (1 : Matrix (Fin n) (Fin n) A).submatrix id π
    rw [← Matrix.submatrix_map, Matrix.map_one s (map_zero s) (map_one s)]
  unfold Formalism.UG.cT
  rw [hP]
  show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π)ᵀ * Matrix.diagonal d *
    (1 : Matrix (Fin n) (Fin n) A).submatrix id π = _
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  split_ifs with hij
  · rw [hij]
  · rfl

/- English proof (translation)
Establish `hle : Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false}` using `card_neg_le' s φ hφ ε ε' (b⁻¹ * b').1 (congr_mul s b⁻¹ b' (congr_inv s b h) h')`. Establish `hge : Fintype.card {i // ε i = false} ≤ Fintype.card {i // ε' i = false}` using `card_neg_le' s φ hφ ε' ε (b'⁻¹ * b).1 (congr_mul s b'⁻¹ b (congr_inv s b' h') h)`. Take `⟨π, hπ⟩` from `exists_perm ε ε' (le_antisymm hle hge)`. Use `⟨permGL π, ?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.cT s (permGL (A := A) π).1 * 1 * (permGL (A := A) π).1 = 1`.

Use `permGL_diagonal s π (fun _ => (1 : A))` as an intermediate fact. Simplify `this` using `[Matrix.diagonal_one]`. Use `show Formalism.UG.cT s (b' * permGL π * b⁻¹).1 * J * (b' * permGL π * b⁻¹).1 = J`. Establish `h1 : Formalism.UG.cT s (b' * permGL π).1 * J * (b' * permGL π).1 = sgnDiag A ε`. Use `congr_mul s b' (permGL π) h' (permGL_diagonal s π (fun i => if ε' i then (1 : A) else -1))` as an intermediate fact.

Simplify `this` using `[sgnDiag, hπ]`. Conclude with `congr_mul s (b' * permGL π) b⁻¹ h1 (congr_inv s b h)`.
-/
theorem exists_unitary (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) {J : Matrix (Fin n) (Fin n) A}
    {ε ε' : Fin n → Bool} (b b' : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = sgnDiag A ε)
    (h' : Formalism.UG.cT s b'.1 * J * b'.1 = sgnDiag A ε') :
    ∃ P ∈ Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) A), b' * P * b⁻¹ ∈ Formalism.UG.UJ s J := by
  have hle : Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} :=
    card_neg_le' s φ hφ ε ε' (b⁻¹ * b').1 (congr_mul s b⁻¹ b' (congr_inv s b h) h')
  have hge : Fintype.card {i // ε i = false} ≤ Fintype.card {i // ε' i = false} :=
    card_neg_le' s φ hφ ε' ε (b'⁻¹ * b).1 (congr_mul s b'⁻¹ b (congr_inv s b' h') h)
  obtain ⟨π, hπ⟩ := exists_perm ε ε' (le_antisymm hle hge)
  refine ⟨permGL π, ?_, ?_⟩
  · show Formalism.UG.cT s (permGL (A := A) π).1 * 1 * (permGL (A := A) π).1 = 1
    have := permGL_diagonal s π (fun _ => (1 : A))
    simpa [Matrix.diagonal_one] using this
  · show Formalism.UG.cT s (b' * permGL π * b⁻¹).1 * J * (b' * permGL π * b⁻¹).1 = J
    have h1 : Formalism.UG.cT s (b' * permGL π).1 * J * (b' * permGL π).1 = sgnDiag A ε := by
      have := congr_mul s b' (permGL π) h' (permGL_diagonal s π (fun i => if ε' i then (1 : A) else -1))
      simpa [sgnDiag, hπ] using this
    exact congr_mul s (b' * permGL π) b⁻¹ h1 (congr_inv s b h)

end General

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ a a' ha ha' w`. Take `⟨ε, hε⟩` from `ha w`. Take `⟨ε', hε'⟩` from `ha' w`. Generalize the expression as in `Formalism.UG.bc (compInf F E w) a = b at hε ⊢`. Generalize the expression as in `Formalism.UG.bc (compInf F E w) a' = b' at hε' ⊢`.

Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Take `⟨P, hP, hg⟩` from `exists_unitary (sigR w.Completion σ) (infEmb τ) (fun y => infEmb_sigR hcm τ y) b b' hε hε'`. Establish `key : ∀ m : GL (Fin n) (w.Completion ⊗[F] E), b⁻¹ * ((b' * P * b⁻¹)⁻¹ * m * (b' * P * b⁻¹)) * b = P⁻¹ * (b'⁻¹ * m * b') * P` using `fun m => by group`. Use `⟨(⟨b' * P * b⁻¹, hg⟩ : HR w.Completion σ J), fun k => ?_⟩` and prove the remaining obligations. Unfold `stabArch`.

Use `first`. Consider the case `(show b'⁻¹ * AdelicU.matHom w.Completion σ J k * b'⁻¹⁻¹ ∈ Formalism.UG.UJ (sigR w.Completion σ) 1 ↔ b⁻¹ * ((b' * P * b⁻¹)⁻¹ * AdelicU.matHom w.Completion σ J k * (b' * P * b⁻¹)) * b⁻¹⁻¹ ∈ Formalism.UG.UJ (sigR w.Completion σ) 1`. Rewrite using `[inv_inv, inv_inv, key, mul_mem_cancel_right hP, mul_mem_cancel_left (inv_mem hP)])`. Consider the case `(simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Simplify using `only [map_mul, map_inv, inv_inv]`.

Conclude with `(mul_mem_cancel_right hP).symm.trans ((mul_mem_cancel_left (inv_mem hP)).symm.trans (by rw [← key]; exact Iff.rfl)))`.
-/
theorem stabArch_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (a a' : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → IsMajorantFrame σ J a' → ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w, k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔ g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ a a' ha ha' w
  obtain ⟨ε, hε⟩ := ha w
  obtain ⟨ε', hε'⟩ := ha' w
  generalize Formalism.UG.bc (compInf F E w) a = b at hε ⊢
  generalize Formalism.UG.bc (compInf F E w) a' = b' at hε' ⊢
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨P, hP, hg⟩ := exists_unitary (sigR w.Completion σ) (infEmb τ) (fun y => infEmb_sigR hcm τ y) b b' hε hε'
  have key : ∀ m : GL (Fin n) (w.Completion ⊗[F] E),
      b⁻¹ * ((b' * P * b⁻¹)⁻¹ * m * (b' * P * b⁻¹)) * b = P⁻¹ * (b'⁻¹ * m * b') * P := fun m => by group
  refine ⟨(⟨b' * P * b⁻¹, hg⟩ : HR w.Completion σ J), fun k => ?_⟩
  unfold stabArch
  first
  | (show b'⁻¹ * AdelicU.matHom w.Completion σ J k * b'⁻¹⁻¹ ∈ Formalism.UG.UJ (sigR w.Completion σ) 1 ↔
        b⁻¹ * ((b' * P * b⁻¹)⁻¹ * AdelicU.matHom w.Completion σ J k * (b' * P * b⁻¹)) * b⁻¹⁻¹ ∈
          Formalism.UG.UJ (sigR w.Completion σ) 1
     rw [inv_inv, inv_inv, key, mul_mem_cancel_right hP, mul_mem_cancel_left (inv_mem hP)])
  | (simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
     simp only [map_mul, map_inv, inv_inv]
     exact (mul_mem_cancel_right hP).symm.trans ((mul_mem_cancel_left (inv_mem hP)).symm.trans
       (by rw [← key]; exact Iff.rfl)))

end GlobalTheory.MajorantConj

end
