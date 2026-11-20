import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisFurther
open scoped BigOperators

namespace GlobalTheory.CommTriang

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target`. Consider the case `exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target`. Consider the case `(apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)`.
-/
theorem exists_common_eigenvector_commuting {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, f i w ∈ W) →
      ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : k, f i x = c • x := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | (apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)

/- English proof (translation)
Introduce `k ι _ _ n T hT`. Establish `hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i)`. Introduce `i j`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]`. Take `⟨x, -, hx0, hx⟩` from `exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl (by simp) (fun _ _ _ => Submodule.mem_top)`.

Use `choose χ hχ using hx`. Conclude with `⟨x, hx0, χ, fun i => by simpa using hχ i⟩`.
-/
theorem exists_common_eigenvector : ∀ (k ι : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (T : ι → Matrix (Fin (n+1)) (Fin (n+1)) k), (∀ i j, T i * T j = T j * T i) →
    ∃ v : Fin (n+1) → k, v ≠ 0 ∧ ∃ χ : ι → k, ∀ i, (T i).mulVec v = χ i • v := by
  intro k ι _ _ n T hT
  have hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i) := by
    intro i j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
  obtain ⟨x, -, hx0, hx⟩ := exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl
    (by simp) (fun _ _ _ => Submodule.mem_top)
  choose χ hχ using hx
  exact ⟨x, hx0, χ, fun i => by simpa using hχ i⟩

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralCriterion.main`. Consider the case `exact _root_.GlobalTheory.IntegralCriterion.main`. Consider the case `(apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralCriterion.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralCriterion.main ..)`.
-/
theorem exists_unit_col_zero : ∀ (k : Type) [Field k] (n : ℕ) (v : Fin (n+1) → k), v ≠ 0 →
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) k, IsUnit P ∧ ∀ a, P a 0 = v a := by
  first
  | exact @_root_.GlobalTheory.IntegralCriterion.main
  | exact _root_.GlobalTheory.IntegralCriterion.main
  | (apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCriterion.main ..)

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

/- English proof (translation)
Introduce `k ι V _ _ _ f v u χ μ r hc hv0 hu0 hv hu`. Distinguish the cases in `h : ∀ i, χ i = μ i`. Conclude with `⟨v, hv0, fun i => by rw [hv, h]⟩`. Use `push_neg at h`. Take `⟨i₀, hi₀⟩` from `h`.

Establish `hd : μ i₀ - χ i₀ ≠ 0` using `sub_ne_zero.mpr (Ne.symm hi₀)`. Use `set t : k := r i₀ / (μ i₀ - χ i₀) with ht`. Establish `htd : t * (μ i₀ - χ i₀) = r i₀` using `div_mul_cancel₀ _ hd`. Establish `hfx : ∀ j, f j (u + t • v) = μ j • (u + t • v) + (r j + t * χ j - t * μ j) • v`. Introduce `j`.

Rewrite using `[map_add, map_smul, hu, hv]`. Use `module`. Establish `h0 : f i₀ (u + t • v) = μ i₀ • (u + t • v)`. Rewrite using `[hfx]`. Establish `: r i₀ + t * χ i₀ - t * μ i₀ = 0` using `by rw [← htd]; ring`.

Rewrite using `[this, zero_smul, add_zero]`. Take `⟨x, hx⟩ : ∃ x, x = u + t • v` from `⟨_, rfl⟩`. Rewrite `hfx`, `h0` using `[← hx]`. Use `⟨x, hx ▸ hu0 t, fun j => ?_⟩` and prove the remaining obligations. Establish `e1 : f i₀ (f j x) = f j (f i₀ x)`.

Rewrite using `[← Module.End.mul_apply, hc, Module.End.mul_apply]`. Rewrite `e1` using `[h0, map_smul, hfx j, map_add, map_smul, map_smul, h0, hv]`. Establish `e2 : ((r j + t * χ j - t * μ j) * (χ i₀ - μ i₀)) • v = 0`. Take the linear combination `(norm := module) e1`. Break down `smul_eq_zero.mp e2 with h | h` into its components or cases.

Break down `mul_eq_zero.mp h with h | h` into its components or cases. Rewrite using `[hfx j, h, zero_smul, add_zero]`. Conclude with `absurd (sub_eq_zero.mp h) hi₀`. Conclude with `absurd h hv0`.
-/
theorem lift_eigen : ∀ (k ι V : Type) [Field k] [AddCommGroup V] [Module k V] (f : ι → Module.End k V) (v u : V) (χ μ r : ι → k),
    (∀ i j, f i * f j = f j * f i) → v ≠ 0 → (∀ t : k, u + t • v ≠ 0) → (∀ i, f i v = χ i • v) →
    (∀ i, f i u = μ i • u + r i • v) → ∃ x : V, x ≠ 0 ∧ ∀ i, f i x = μ i • x := by
  intro k ι V _ _ _ f v u χ μ r hc hv0 hu0 hv hu
  by_cases h : ∀ i, χ i = μ i
  · exact ⟨v, hv0, fun i => by rw [hv, h]⟩
  push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hd : μ i₀ - χ i₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi₀)
  set t : k := r i₀ / (μ i₀ - χ i₀) with ht
  have htd : t * (μ i₀ - χ i₀) = r i₀ := div_mul_cancel₀ _ hd
  have hfx : ∀ j, f j (u + t • v) = μ j • (u + t • v) + (r j + t * χ j - t * μ j) • v := by
    intro j
    rw [map_add, map_smul, hu, hv]
    module
  have h0 : f i₀ (u + t • v) = μ i₀ • (u + t • v) := by
    rw [hfx]
    have : r i₀ + t * χ i₀ - t * μ i₀ = 0 := by rw [← htd]; ring
    rw [this, zero_smul, add_zero]
  obtain ⟨x, hx⟩ : ∃ x, x = u + t • v := ⟨_, rfl⟩
  rw [← hx] at hfx h0
  refine ⟨x, hx ▸ hu0 t, fun j => ?_⟩
  have e1 : f i₀ (f j x) = f j (f i₀ x) := by
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
  rw [h0, map_smul, hfx j, map_add, map_smul, map_smul, h0, hv] at e1
  have e2 : ((r j + t * χ j - t * μ j) * (χ i₀ - μ i₀)) • v = 0 := by
    linear_combination (norm := module) e1
  rcases smul_eq_zero.mp e2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [hfx j, h, zero_smul, add_zero]
    · exact absurd (sub_eq_zero.mp h) hi₀
  · exact absurd h hv0

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

open Matrix

def blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n+1)) (Fin (n+1)) k :=
  Matrix.of fun a b => Fin.cases (motive := fun _ => k) (Fin.cases (motive := fun _ => k) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => k) 0 (fun b' => Q a' b') b) a

section
variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockOne_zero_zero (Q : Matrix (Fin n) (Fin n) k) : blockOne Q 0 0 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockOne_zero_succ (Q : Matrix (Fin n) (Fin n) k) (b : Fin n) : blockOne Q 0 b.succ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockOne_succ_zero (Q : Matrix (Fin n) (Fin n) k) (a : Fin n) : blockOne Q a.succ 0 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockOne_succ_succ (Q : Matrix (Fin n) (Fin n) k) (a b : Fin n) : blockOne Q a.succ b.succ = Q a b := rfl

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem blockOne_mul (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.one_apply, Fin.succ_ne_zero] <;> exact (Fin.succ_ne_zero _).symm`.
-/
theorem blockOne_one : blockOne (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.one_apply, Fin.succ_ne_zero] <;> exact (Fin.succ_ne_zero _).symm

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem conj_succ_succ (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a b : Fin n) :
    (blockOne R * S * blockOne Q) a.succ b.succ = (R * S.submatrix Fin.succ Fin.succ * Q) a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem conj_succ_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a : Fin n) :
    (blockOne R * S * blockOne Q) a.succ 0 = ∑ c, R a c * S c.succ 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem conj_zero_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) :
    (blockOne R * S * blockOne Q) 0 0 = S 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

end

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

/- English proof (translation)
Establish `hQd : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).mp hQ`. Establish `h : blockOne Q * blockOne Q⁻¹ = 1`. Rewrite using `[blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]`. Conclude with `⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩`.
-/
theorem isUnit_blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) (hQ : IsUnit Q) :
    IsUnit (blockOne Q) ∧ (blockOne Q)⁻¹ = blockOne Q⁻¹ := by
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h : blockOne Q * blockOne Q⁻¹ = 1 := by
    rw [blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro T _`. Conclude with `⟨1, isUnit_one, fun i a b _ => a.elim0, fun a => a.elim0⟩`. Consider the case `succ n ih`.

Introduce `T hT`. Take `⟨v, hv0, χ, hv⟩` from `exists_common_eigenvector k ι n T hT`. Take `⟨P₀, hP₀, hP₀v⟩` from `exists_unit_col_zero k n v hv0`. Establish `hP₀d : IsUnit P₀.det` using `(Matrix.isUnit_iff_isUnit_det P₀).mp hP₀`. Establish `hl : P₀⁻¹ * P₀ = 1` using `Matrix.nonsing_inv_mul _ hP₀d`.

Establish `hr : P₀ * P₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hP₀d`. Use `set S : ι → Matrix (Fin (n+1)) (Fin (n+1)) k := fun i => P₀⁻¹ * T i * P₀ with hSdef`. Establish `hST : ∀ i, P₀ * S i = T i * P₀`. Introduce `i`. Simplify using `only [hSdef, ← Matrix.mul_assoc, hr, Matrix.one_mul]`.

Establish `hSc : ∀ i j, S i * S j = S j * S i`. Introduce `i j`. Establish `e : ∀ i j, S i * S j = P₀⁻¹ * (T i * T j) * P₀`. Introduce `i j`. Simplify using `only [hSdef, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc P₀ P₀⁻¹, hr, Matrix.one_mul]`. Rewrite using `[e, e, hT]`. Use `set e0 : Fin (n+1) → k := Pi.single 0 1 with he0`. Establish `hPe : P₀.mulVec e0 = v`. Use extensionality with `a`.

Simplify using `[he0, Matrix.mulVec, dotProduct, Pi.single_apply, hP₀v]`. Establish `hSe : ∀ i, (S i).mulVec e0 = χ i • e0`. Introduce `i`. Establish `: P₀⁻¹.mulVec v = e0` using `by rw [← hPe, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]`. Simplify using `only [hSdef]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, hv, Matrix.mulVec_smul, this]`. Establish `hScol : ∀ i a, S i a 0 = χ i * e0 a`. Introduce `i a`. Use `congrFun (hSe i) a` as an intermediate fact. Simplify `this` using `[he0, Matrix.mulVec, dotProduct, Pi.single_apply]`.

Establish `hS0 : ∀ i (a : Fin n), S i a.succ 0 = 0`. Introduce `i a`. Rewrite using `[hScol]`. Simplify using `[he0, Fin.succ_ne_zero]`. Establish `hS00 : ∀ i, S i 0 0 = χ i`.

Introduce `i`. Rewrite using `[hScol]`. Simplify using `[he0]`. Use `set B : ι → Matrix (Fin n) (Fin n) k := fun i => (S i).submatrix Fin.succ Fin.succ with hBdef`. Establish `hBc : ∀ i j, B i * B j = B j * B i`.

Introduce `i j`. Use extensionality with `a b`. Use `congrFun (congrFun (hSc i j) a.succ) b.succ` as an intermediate fact. Simplify `this` using `[hBdef, Matrix.mul_apply, Fin.sum_univ_succ, hS0]`. Take `⟨Q, hQ, hQtri, hQev⟩` from `ih B hBc`.

Take `⟨hDQ, hDQinv⟩` from `isUnit_blockOne Q hQ`. Use `⟨P₀ * blockOne Q, hP₀.mul hDQ, ?_⟩` and prove the remaining obligations. Establish `hM : ∀ i, (P₀ * blockOne Q)⁻¹ * T i * (P₀ * blockOne Q) = blockOne Q⁻¹ * S i * blockOne Q`. Introduce `i`. Rewrite using `[Matrix.mul_inv_rev, hDQinv]`.

Simplify using `only [hSdef, Matrix.mul_assoc]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i a b hab`. Rewrite using `[hM]`. Consider the cases of `a using Fin.cases with`.

Consider the case `zero => exact absurd hab (Fin.not_lt_zero _)`. Consider the case `succ a`. Consider the cases of `b using Fin.cases with`. Consider the case `zero => rw [conj_succ_zero]`. Simplify using `[hS0]`.

Consider the case `succ b`. Rewrite using `[conj_succ_succ]`. Conclude with `hQtri i (by simpa using hab)`. Introduce `a`. Consider the cases of `a using Fin.cases with`.

Consider the case `zero`. Use `⟨v, hv0, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hM, conj_zero_zero, hS00, hv]`. Consider the case `succ a`. Take `⟨y, hy0, hy⟩` from `hQev a`.

Use `set μ : ι → k := fun i => (Q⁻¹ * B i * Q) a a with hμ`. Use `set u : Fin (n+1) → k := Fin.cons 0 y with hu`. Take `⟨x', hx'0, hx'⟩` from `lift_eigen k ι (Fin (n+1) → k) (fun i => Matrix.toLin' (S i)) e0 u χ μ (fun i => ∑ b, S i 0 b.succ * y b) (by intro i j; rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hSc]) (by simp [he0]) (by`. Introduce `t h`. Take `⟨b, hb⟩` from `Function.ne_iff.mp hy0`.

Use `congrFun h b.succ` as an intermediate fact. Simplify using `[hu, he0, Fin.succ_ne_zero] at this`. Conclude with `hb this)`. Use the proof step `(fun i => by simpa using hSe i)`. Use the proof step `(by`.

Introduce `i`. Use extensionality with `c`. Consider the cases of `c using Fin.cases with`. Consider the case `zero => simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`. Consider the case `succ c`.

Establish `hyi : (B i).mulVec y = μ i • y` using `hy i`. Use `congrFun hyi c` as an intermediate fact. Simplify using `only [hBdef, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `[hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hS0, Fin.succ_ne_zero, this])`. Use `⟨P₀.mulVec x', ?_, fun i => ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hx'0` to reduce the goal to its premises. Apply `(Matrix.mulVec_injective_iff_isUnit.mpr hP₀)` to reduce the goal to its premises. Rewrite using `[h, Matrix.mulVec_zero]`. Establish `hx` using `hx' i`.

Simplify using `only [Matrix.toLin'_apply] at hx`. Rewrite using `[hM, conj_succ_succ, Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]`.
-/
theorem exists_triangular (k ι : Type) [Field k] [IsAlgClosed k] : ∀ (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) k),
    (∀ i j, T i * T j = T j * T i) →
    ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ (∀ i, (P⁻¹ * T i * P).BlockTriangular id) ∧
      ∀ a, ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, (T i).mulVec x = (P⁻¹ * T i * P) a a • x := by
  intro n
  induction n with
  | zero => intro T _; exact ⟨1, isUnit_one, fun i a b _ => a.elim0, fun a => a.elim0⟩
  | succ n ih =>
    intro T hT
    obtain ⟨v, hv0, χ, hv⟩ := exists_common_eigenvector k ι n T hT
    obtain ⟨P₀, hP₀, hP₀v⟩ := exists_unit_col_zero k n v hv0
    have hP₀d : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP₀
    have hl : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hP₀d
    have hr : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP₀d
    set S : ι → Matrix (Fin (n+1)) (Fin (n+1)) k := fun i => P₀⁻¹ * T i * P₀ with hSdef
    have hST : ∀ i, P₀ * S i = T i * P₀ := by
      intro i; simp only [hSdef, ← Matrix.mul_assoc, hr, Matrix.one_mul]
    have hSc : ∀ i j, S i * S j = S j * S i := by
      intro i j
      have e : ∀ i j, S i * S j = P₀⁻¹ * (T i * T j) * P₀ := by
        intro i j
        simp only [hSdef, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P₀ P₀⁻¹, hr, Matrix.one_mul]
      rw [e, e, hT]
    set e0 : Fin (n+1) → k := Pi.single 0 1 with he0
    have hPe : P₀.mulVec e0 = v := by
      ext a; simp [he0, Matrix.mulVec, dotProduct, Pi.single_apply, hP₀v]
    have hSe : ∀ i, (S i).mulVec e0 = χ i • e0 := by
      intro i
      have : P₀⁻¹.mulVec v = e0 := by rw [← hPe, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
      simp only [hSdef]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, hv, Matrix.mulVec_smul, this]
    have hScol : ∀ i a, S i a 0 = χ i * e0 a := by
      intro i a
      have := congrFun (hSe i) a
      simpa [he0, Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hS0 : ∀ i (a : Fin n), S i a.succ 0 = 0 := by
      intro i a; rw [hScol]; simp [he0, Fin.succ_ne_zero]
    have hS00 : ∀ i, S i 0 0 = χ i := by
      intro i; rw [hScol]; simp [he0]
    set B : ι → Matrix (Fin n) (Fin n) k := fun i => (S i).submatrix Fin.succ Fin.succ with hBdef
    have hBc : ∀ i j, B i * B j = B j * B i := by
      intro i j; ext a b
      have := congrFun (congrFun (hSc i j) a.succ) b.succ
      simpa [hBdef, Matrix.mul_apply, Fin.sum_univ_succ, hS0] using this
    obtain ⟨Q, hQ, hQtri, hQev⟩ := ih B hBc
    obtain ⟨hDQ, hDQinv⟩ := isUnit_blockOne Q hQ
    refine ⟨P₀ * blockOne Q, hP₀.mul hDQ, ?_⟩
    have hM : ∀ i, (P₀ * blockOne Q)⁻¹ * T i * (P₀ * blockOne Q) = blockOne Q⁻¹ * S i * blockOne Q := by
      intro i
      rw [Matrix.mul_inv_rev, hDQinv]
      simp only [hSdef, Matrix.mul_assoc]
    refine ⟨?_, ?_⟩
    · intro i a b hab
      rw [hM]
      cases a using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ a =>
        cases b using Fin.cases with
        | zero => rw [conj_succ_zero]; simp [hS0]
        | succ b =>
          rw [conj_succ_succ]
          exact hQtri i (by simpa using hab)
    · intro a
      cases a using Fin.cases with
      | zero =>
        refine ⟨v, hv0, fun i => ?_⟩
        rw [hM, conj_zero_zero, hS00, hv]
      | succ a =>
        obtain ⟨y, hy0, hy⟩ := hQev a
        set μ : ι → k := fun i => (Q⁻¹ * B i * Q) a a with hμ
        set u : Fin (n+1) → k := Fin.cons 0 y with hu
        obtain ⟨x', hx'0, hx'⟩ := lift_eigen k ι (Fin (n+1) → k) (fun i => Matrix.toLin' (S i)) e0 u χ μ
          (fun i => ∑ b, S i 0 b.succ * y b)
          (by intro i j; rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hSc])
          (by simp [he0])
          (by
            intro t h
            obtain ⟨b, hb⟩ := Function.ne_iff.mp hy0
            have := congrFun h b.succ
            simp [hu, he0, Fin.succ_ne_zero] at this
            exact hb this)
          (fun i => by simpa using hSe i)
          (by
            intro i
            ext c
            cases c using Fin.cases with
            | zero => simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            | succ c =>
              have hyi : (B i).mulVec y = μ i • y := hy i
              have := congrFun hyi c
              simp only [hBdef, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at this
              simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hS0, Fin.succ_ne_zero, this])
        refine ⟨P₀.mulVec x', ?_, fun i => ?_⟩
        · intro h
          apply hx'0
          apply (Matrix.mulVec_injective_iff_isUnit.mpr hP₀)
          rw [h, Matrix.mulVec_zero]
        · have hx := hx' i
          simp only [Matrix.toLin'_apply] at hx
          rw [hM, conj_succ_succ, Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

end GlobalTheory.CommTriang
