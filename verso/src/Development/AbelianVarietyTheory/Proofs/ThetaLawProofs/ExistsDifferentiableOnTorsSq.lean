import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa

namespace GlobalTheory.TorsionHolomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableOn_const 1`. Introduce `a s ha ih`. Simplify using `only [Finset.prod_insert ha]`.

Conclude with `(hf a).mul ih`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
The claim follows from `DifferentiableOn.fun_sum (fun i _ => hf i)`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_sum {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∑ i ∈ s, f i e) W :=
  DifferentiableOn.fun_sum (fun i _ => hf i)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in

/- English proof (translation)
Establish `hdet : (fun e => (A e).det) = fun e => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A e (σ i) i`. Use function extensionality and compare the values at `e`. Conclude with `Matrix.det_apply' _`. Rewrite using `[hdet]`. Use `DifferentiableOn.fun_sum (fun σ _ => ?_)` and prove the remaining obligations.

Conclude with `(differentiableOn_const _).mul (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod Finset.univ (fun i e => A e (σ i) i) W (fun i => hA _ _))`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W) :
    DifferentiableOn ℂ (fun e => (A e).det) W := by
  have hdet : (fun e => (A e).det) =
      fun e => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A e (σ i) i := by
    funext e
    exact Matrix.det_apply' _
  rw [hdet]
  refine DifferentiableOn.fun_sum (fun σ _ => ?_)
  exact (differentiableOn_const _).mul
    (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod Finset.univ (fun i e => A e (σ i) i) W
      (fun i => hA _ _))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Conclude with `DifferentiableOn.fun_sum (fun r _ => (hA p r).mul (hB r q))`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul {n : Type} [Fintype n] (A B : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hB : ∀ p q, DifferentiableOn ℂ (fun e => B e p q) W) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e * B e) p q) W := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum (fun r _ => (hA p r).mul (hB r q))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in

/- English proof (translation)
Establish `key : ∀ e, (A e)⁻¹ p q = ((A e).det)⁻¹ * (A e).adjugate p q`. Introduce `e`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]`. Simplify using `only [key]`. Use `(DifferentiableOn.inv (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA) hdet).mul ?_` and prove the remaining obligations.

Simplify using `only [Matrix.adjugate_apply]`. Apply the tactic sequence `have hentry : ∀ i j, DifferentiableOn ℂ (fun e => (A e).updateRow q (Pi.single p 1) i j) W := by`. Introduce `i j`. Distinguish the cases in `hi : i = q`. Substitute `hi` using the available equality.

Simplify using `only [Matrix.updateRow_self]`. Conclude with `differentiableOn_const _`. Simplify using `only [Matrix.updateRow_ne hi]`. Conclude with `hA i j`. Conclude with `_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (A e).updateRow q (Pi.single p 1)) W hentry`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hdet : ∀ e ∈ W, (A e).det ≠ 0) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e)⁻¹ p q) W := by
  have key : ∀ e, (A e)⁻¹ p q = ((A e).det)⁻¹ * (A e).adjugate p q := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  simp only [key]
  refine (DifferentiableOn.inv (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA) hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  have hentry : ∀ i j, DifferentiableOn ℂ
      (fun e => (A e).updateRow q (Pi.single p 1) i j) W := by
    intro i j
    by_cases hi : i = q
    · subst hi
      simp only [Matrix.updateRow_self]
      exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j
  exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (A e).updateRow q (Pi.single p 1))
    W hentry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Use extensionality with `p q`. Establish `h1 : ∀ r, D p r * (if deg r = deg q + 1 then h r q else 0) = if deg p = deg q then D p r * h r q else 0`. Introduce `r`. Distinguish the cases in `hr : deg r = deg p + 1`. Distinguish the cases in `hpq : deg p = deg q`.

Rewrite using `[if_pos (by omega), if_pos hpq]`. Rewrite using `[if_neg (by omega), if_neg hpq, mul_zero]`. Rewrite using `[hD p r hr, zero_mul, zero_mul, ite_self]`. Establish `h2 : ∀ r, (if deg p = deg r + 1 then h p r else 0) * D r q = if deg p = deg q then h p r * D r q else 0`. Introduce `r`.

Distinguish the cases in `hr : deg q = deg r + 1`. Distinguish the cases in `hpq : deg p = deg q`. Rewrite using `[if_pos (by omega), if_pos hpq]`. Rewrite using `[if_neg (by omega), if_neg hpq, zero_mul]`. Rewrite using `[hD r q hr, mul_zero, mul_zero, ite_self]`.

Establish `hpq'` using `congrFun (congrFun hh p) q`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply] at hpq' ⊢`. Simplify using `only [h1, h2]`. Distinguish the cases in `hpq : deg p = deg q`. Simplify using `only [if_pos hpq]`.

Conclude with `hpq'`. Simplify using `only [if_neg hpq, Finset.sum_const_zero, add_zero]`. Establish `hne : p ≠ q` using `fun h => hpq (h ▸ rfl)`. Rewrite using `[Matrix.one_apply_ne hne]`.
-/
private theorem degree_part_homotopy_of_anticommutator_eq_one {Ix : Type} [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D h : Matrix Ix Ix ℂ) (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0)
    (hh : D * h + h * D = 1) :
    D * Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) +
      Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) * D = 1 := by
  ext p q
  have h1 : ∀ r, D p r * (if deg r = deg q + 1 then h r q else 0) =
      if deg p = deg q then D p r * h r q else 0 := by
    intro r
    by_cases hr : deg r = deg p + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, mul_zero]
    · rw [hD p r hr, zero_mul, zero_mul, ite_self]
  have h2 : ∀ r, (if deg p = deg r + 1 then h p r else 0) * D r q =
      if deg p = deg q then h p r * D r q else 0 := by
    intro r
    by_cases hr : deg q = deg r + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, zero_mul]
    · rw [hD r q hr, mul_zero, mul_zero, ite_self]
  have hpq' := congrFun (congrFun hh p) q
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply] at hpq' ⊢
  simp only [h1, h2]
  by_cases hpq : deg p = deg q
  · simp only [if_pos hpq]
    exact hpq'
  · simp only [if_neg hpq, Finset.sum_const_zero, add_zero]
    have hne : p ≠ q := fun h => hpq (h ▸ rfl)
    rw [Matrix.one_apply_ne hne]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Use `set A := D * h + h * D with hA`. Establish `hu : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hcomm : D * A = A * D`. Rewrite using `[hA, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hDD, Matrix.zero_mul, zero_add, Matrix.mul_assoc h D D, hDD, Matrix.mul_zero, add_zero, Matrix.mul_assoc]`. Establish `hinv : A⁻¹ * D = D * A⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc h, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`. Use `_ = A * A⁻¹ := by rw [hA, Matrix.add_mul]`.

Use `_ = 1 := Matrix.mul_nonsing_inv A hu`.
-/
private theorem contracting_homotopy_of_det_anticommutator_ne_zero {Ix : Type} [Fintype Ix]
    [DecidableEq Ix] (D h : Matrix Ix Ix ℂ) (hDD : D * D = 0)
    (hdet : (D * h + h * D).det ≠ 0) :
    D * (h * (D * h + h * D)⁻¹) + h * (D * h + h * D)⁻¹ * D = 1 := by
  set A := D * h + h * D with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hcomm : D * A = A * D := by
    rw [hA, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hDD, Matrix.zero_mul, zero_add,
      Matrix.mul_assoc h D D, hDD, Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  have hinv : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = A⁻¹ * (D * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hcomm]
      _ = D * A⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]
  calc D * (h * A⁻¹) + h * A⁻¹ * D = D * h * A⁻¹ + h * D * A⁻¹ := by
        rw [Matrix.mul_assoc h, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = A * A⁻¹ := by rw [hA, Matrix.add_mul]
    _ = 1 := Matrix.mul_nonsing_inv A hu

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in

/- English proof (translation)
Introduce `E Ix _ _ _ _ deg D W e₀ t₀ hW he₀ hD hcx htor`. Take `⟨h₀, -, hcontr₀, σ, -⟩` from `htor`. Use `set A : E → Matrix Ix Ix ℂ := fun e => D e * h₀ + h₀ * D e with hAdef`. Establish `hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W`. Introduce `p q`.

Simplify using `only [hAdef, Matrix.add_apply]`. Conclude with `(_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul D (fun _ => h₀) W hD (fun _ _ => differentiableOn_const _) p q).add (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) D W (fun _ _ => differentiableOn_const _) hD p q)`. Establish `hAdet` using `_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA`. Use `set W' := W ∩ (fun e => (A e).det) ⁻¹' {(0 : ℂ)}ᶜ with hW'`. Establish `hW'open : IsOpen W'` using `hAdet.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton`.

Establish `hsub : W' ⊆ W` using `Set.inter_subset_left`. Establish `hdetW' : ∀ e ∈ W', (A e).det ≠ 0` using `fun e he => he.2`. Establish `hAe₀ : A e₀ = 1` using `hcontr₀`. Establish `he₀' : e₀ ∈ W'` using `⟨he₀, by simp [hAe₀]⟩`. Use `set hh : E → Matrix Ix Ix ℂ := fun e => Matrix.of (fun p q => if deg p = deg q + 1 then (h₀ * (A e)⁻¹) p q else 0) with hhdef`.

Establish `hhdiff : ∀ p q, DifferentiableOn ℂ (fun e => hh e p q) W'`. Introduce `p q`. Simplify using `only [hhdef, Matrix.of_apply]`. Distinguish the cases in `hpq : deg p = deg q + 1`. Simplify using `only [if_pos hpq]`.

Conclude with `_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) (fun e => (A e)⁻¹) W' (fun _ _ => differentiableOn_const _) (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv A W' (fun i j => (hA i j).mono hsub) hdetW') p q`. Simplify using `only [if_neg hpq]`. Conclude with `differentiableOn_const _`. Use `⟨W', fun e => ((D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix)) (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))).det ^ 2, hW'open, he₀', hsub, ?_, ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.pow ?_ 2` and prove the remaining obligations.

Use `_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix)) (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))) W' (fun i j => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply, Matrix.add_apply]`. Conclude with `((hD _ _).mono hsub).add (hhdiff _ _)`. Introduce `e he`. Use `⟨hh e, ?_, ?_, σ, rfl⟩` and prove the remaining obligations.

Introduce `p q hpq`. Simplify using `only [hhdef, Matrix.of_apply, if_neg hpq]`. Conclude with `degree_part_homotopy_of_anticommutator_eq_one deg (D e) (h₀ * (A e)⁻¹) (hcx e (hsub he)).1 (contracting_homotopy_of_det_anticommutator_ne_zero (D e) h₀ (hcx e (hsub he)).2 (hdetW' e he))`.
-/
theorem _root_.GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq :
    ∀ (E Ix : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : E → Matrix Ix Ix ℂ) (W : Set E) (e₀ : E) (t₀ : ℂ), IsOpen W → e₀ ∈ W → (∀ p q, DifferentiableOn ℂ (fun e => D e p q) W) → (∀ e ∈ W, _root_.GlobalTheory.KeyKa.IsCx deg (D e)) → _root_.GlobalTheory.KeyKa.TorsSq deg (D e₀) t₀ → ∃ (W' : Set E) (t : E → ℂ), IsOpen W' ∧ e₀ ∈ W' ∧ W' ⊆ W ∧ DifferentiableOn ℂ t W' ∧ ∀ e ∈ W', _root_.GlobalTheory.KeyKa.TorsSq deg (D e) (t e) := by
  intro E Ix _ _ _ _ deg D W e₀ t₀ hW he₀ hD hcx htor
  obtain ⟨h₀, -, hcontr₀, σ, -⟩ := htor
  set A : E → Matrix Ix Ix ℂ := fun e => D e * h₀ + h₀ * D e with hAdef
  have hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W := by
    intro p q
    simp only [hAdef, Matrix.add_apply]
    exact (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul D (fun _ => h₀) W hD (fun _ _ => differentiableOn_const _)
      p q).add (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) D W
        (fun _ _ => differentiableOn_const _) hD p q)
  have hAdet := _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA
  set W' := W ∩ (fun e => (A e).det) ⁻¹' {(0 : ℂ)}ᶜ with hW'
  have hW'open : IsOpen W' := hAdet.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hsub : W' ⊆ W := Set.inter_subset_left
  have hdetW' : ∀ e ∈ W', (A e).det ≠ 0 := fun e he => he.2
  have hAe₀ : A e₀ = 1 := hcontr₀
  have he₀' : e₀ ∈ W' := ⟨he₀, by simp [hAe₀]⟩
  set hh : E → Matrix Ix Ix ℂ := fun e =>
    Matrix.of (fun p q => if deg p = deg q + 1 then (h₀ * (A e)⁻¹) p q else 0) with hhdef
  have hhdiff : ∀ p q, DifferentiableOn ℂ (fun e => hh e p q) W' := by
    intro p q
    simp only [hhdef, Matrix.of_apply]
    by_cases hpq : deg p = deg q + 1
    · simp only [if_pos hpq]
      exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) (fun e => (A e)⁻¹) W'
        (fun _ _ => differentiableOn_const _)
        (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv A W' (fun i j => (hA i j).mono hsub) hdetW') p q
    · simp only [if_neg hpq]
      exact differentiableOn_const _
  refine ⟨W', fun e => ((D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix))
    (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))).det ^ 2,
    hW'open, he₀', hsub, ?_, ?_⟩
  · refine DifferentiableOn.pow ?_ 2
    refine _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (D e + hh e).submatrix
      (fun p : {p // Even (deg p)} => (p : Ix))
      (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))) W' (fun i j => ?_)
    simp only [Matrix.submatrix_apply, Matrix.add_apply]
    exact ((hD _ _).mono hsub).add (hhdiff _ _)
  · intro e he
    refine ⟨hh e, ?_, ?_, σ, rfl⟩
    · intro p q hpq
      simp only [hhdef, Matrix.of_apply, if_neg hpq]
    · exact degree_part_homotopy_of_anticommutator_eq_one deg (D e) (h₀ * (A e)⁻¹) (hcx e (hsub he)).1
        (contracting_homotopy_of_det_anticommutator_ne_zero (D e) h₀ (hcx e (hsub he)).2 (hdetW' e he))

end GlobalTheory.TorsionHolomorphic
