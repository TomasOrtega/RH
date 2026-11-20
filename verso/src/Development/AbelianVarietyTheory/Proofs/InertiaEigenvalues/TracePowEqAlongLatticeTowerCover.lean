import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CoverTrace

section Ultra

variable {E : Type} [NormedField E] [IsUltrametricDist E]

/- English proof (translation)
Unfold `dotProduct`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hx i) (hy i) (norm_nonneg _) hα`.
-/
theorem norm_dot_le {ι : Type} [Fintype ι] {x y : ι → E} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : ∀ i, ‖x i‖ ≤ α) (hy : ∀ i, ‖y i‖ ≤ β) : ‖x ⬝ᵥ y‖ ≤ α * β := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hx i) (hy i) (norm_nonneg _) hα

/- English proof (translation)
The claim follows from `norm_dot_le hα hβ (fun j => hA i j) hy`.
-/
theorem norm_mulVec_le {ι κ : Type} [Fintype κ] {A : Matrix ι κ E} {y : κ → E} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : ∀ i j, ‖A i j‖ ≤ α) (hy : ∀ j, ‖y j‖ ≤ β) (i : ι) :
    ‖(A *ᵥ y) i‖ ≤ α * β :=
  norm_dot_le hα hβ (fun j => hA i j) hy

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun j _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hA i j) (hC j k) (norm_nonneg _) hα`.
-/
theorem norm_mul_le' {ι κ μ : Type} [Fintype κ] {A : Matrix ι κ E} {C : Matrix κ μ E} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : ∀ i j, ‖A i j‖ ≤ α) (hC : ∀ i j, ‖C i j‖ ≤ β) (i : ι) (k : μ) :
    ‖(A * C) i k‖ ≤ α * β := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i j) (hC j k) (norm_nonneg _) hα

/- English proof (translation)
Proceed by induction on `n generalizing i j with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ n ih`.

Rewrite using `[pow_succ', pow_succ']`. Conclude with `norm_mul_le' (by linarith) (pow_nonneg (by linarith) n) hU ih i j`.
-/
theorem norm_pow_le {ι : Type} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι E} {B : ℝ} (hB : 1 ≤ B)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (n : ℕ) (i j : ι) : ‖(U ^ n) i j‖ ≤ B ^ n := by
  induction n generalizing i j with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact norm_mul_le' (by linarith) (pow_nonneg (by linarith) n) hU ih i j

/- English proof (translation)
Proceed by induction on `n generalizing i j with`. Consider the case `zero => simp [hδ]`. Consider the case `succ n ih`. Establish `e : U ^ (n + 1) * P - P * U' ^ (n + 1) = U * (U ^ n * P - P * U' ^ n) + (U * P - P * U') * U' ^ n`. Rewrite using `[pow_succ', pow_succ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Establish `hB0 : 0 ≤ B` using `by linarith`. Establish `hBn : 1 ≤ B ^ n` using `one_le_pow₀ hB`. Rewrite using `[e, Matrix.add_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Use `norm_mul_le' hB0 (mul_nonneg (pow_nonneg hB0 n) hδ) hU ih i j` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Use `norm_mul_le' hδ (pow_nonneg hB0 n) hc (norm_pow_le hB hU' n) i j` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ]`.

Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hδ (pow_nonneg hB0 n)) (sub_nonneg.2 hB)]`.
-/
theorem norm_comm_pow_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {U : Matrix ι ι E} {U' : Matrix κ κ E} {P : Matrix ι κ E} {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (hU' : ∀ i j, ‖U' i j‖ ≤ B) (hc : ∀ i j, ‖(U * P - P * U') i j‖ ≤ δ)
    (n : ℕ) (i : ι) (j : κ) : ‖(U ^ n * P - P * U' ^ n) i j‖ ≤ B ^ n * δ := by
  induction n generalizing i j with
  | zero => simp [hδ]
  | succ n ih =>
    have e : U ^ (n + 1) * P - P * U' ^ (n + 1) = U * (U ^ n * P - P * U' ^ n) + (U * P - P * U') * U' ^ n := by
      rw [pow_succ', pow_succ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    have hB0 : 0 ≤ B := by linarith
    have hBn : 1 ≤ B ^ n := one_le_pow₀ hB
    rw [e, Matrix.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := norm_mul_le' hB0 (mul_nonneg (pow_nonneg hB0 n) hδ) hU ih i j
      calc _ ≤ _ := this
        _ = B ^ (n + 1) * δ := by ring
    · have := norm_mul_le' hδ (pow_nonneg hB0 n) hc (norm_pow_le hB hU' n) i j
      calc _ ≤ _ := this
        _ ≤ B ^ (n + 1) * δ := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg hδ (pow_nonneg hB0 n)) (sub_nonneg.2 hB)]

/- English proof (translation)
Establish `hB0 : 0 ≤ B` using `by linarith`. Establish `hBn : 0 ≤ B ^ n` using `pow_nonneg hB0 n`. Establish `e1 : ((P * U' ^ n) *ᵥ v') ⬝ᵥ t = (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P)`. Rewrite using `[← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]`. Establish `e2 : U ^ n *ᵥ (P *ᵥ v') = (U ^ n * P) *ᵥ v'` using `Matrix.mulVec_mulVec _ _ _`.

Establish `e : (U ^ n *ᵥ v) ⬝ᵥ t - (U' ^ n *ᵥ v') ⬝ᵥ T' = (U ^ n *ᵥ (v - P *ᵥ v')) ⬝ᵥ t + ((U ^ n * P - P * U' ^ n) *ᵥ v') ⬝ᵥ t + (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P - T')`. Rewrite using `[Matrix.mulVec_sub, Matrix.sub_mulVec, sub_dotProduct, sub_dotProduct, dotProduct_sub, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)` and prove the remaining obligations.

Conclude with `norm_dot_le (mul_nonneg hBn hε) hτ (norm_mulVec_le hBn hε (norm_pow_le hB hU n) hv) ht`. Use `norm_dot_le (mul_nonneg (mul_nonneg hBn hδ) zero_le_one) hτ (norm_mulVec_le (mul_nonneg hBn hδ) zero_le_one (norm_comm_pow_le hB hδ hU hU' hc n) hv') ht` as an intermediate fact. Simplify using `using this`. Use `norm_dot_le (mul_nonneg hBn zero_le_one) hε (norm_mulVec_le hBn zero_le_one (norm_pow_le hB hU' n) hv') hT` as an intermediate fact. Simplify `this` using `[mul_comm]`.
-/
theorem core {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι E) (U' : Matrix κ κ E) (P : Matrix ι κ E) (t v : ι → E) (v' T' : κ → E)
    (B τ ε δ : ℝ) (hB : 1 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (hU' : ∀ i j, ‖U' i j‖ ≤ B) (ht : ∀ i, ‖t i‖ ≤ τ) (hv' : ∀ s, ‖v' s‖ ≤ 1)
    (hv : ∀ i, ‖(v - P *ᵥ v') i‖ ≤ ε) (hc : ∀ i j, ‖(U * P - P * U') i j‖ ≤ δ)
    (hT : ∀ s, ‖(t ᵥ* P - T') s‖ ≤ ε) (n : ℕ) :
    ‖(U ^ n *ᵥ v) ⬝ᵥ t - (U' ^ n *ᵥ v') ⬝ᵥ T'‖ ≤ B ^ n * ε * τ + B ^ n * δ * τ + B ^ n * ε := by
  have hB0 : 0 ≤ B := by linarith
  have hBn : 0 ≤ B ^ n := pow_nonneg hB0 n
  have e1 : ((P * U' ^ n) *ᵥ v') ⬝ᵥ t = (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  have e2 : U ^ n *ᵥ (P *ᵥ v') = (U ^ n * P) *ᵥ v' := Matrix.mulVec_mulVec _ _ _
  have e : (U ^ n *ᵥ v) ⬝ᵥ t - (U' ^ n *ᵥ v') ⬝ᵥ T' =
      (U ^ n *ᵥ (v - P *ᵥ v')) ⬝ᵥ t + ((U ^ n * P - P * U' ^ n) *ᵥ v') ⬝ᵥ t + (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P - T') := by
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec, sub_dotProduct, sub_dotProduct, dotProduct_sub, e1, e2]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact norm_dot_le (mul_nonneg hBn hε) hτ (norm_mulVec_le hBn hε (norm_pow_le hB hU n) hv) ht
  · have := norm_dot_le (mul_nonneg (mul_nonneg hBn hδ) zero_le_one) hτ
      (norm_mulVec_le (mul_nonneg hBn hδ) zero_le_one (norm_comm_pow_le hB hδ hU hU' hc n) hv') ht
    simpa using this
  · have := norm_dot_le (mul_nonneg hBn zero_le_one) hε (norm_mulVec_le hBn zero_le_one (norm_pow_le hB hU' n) hv') hT
    simpa [mul_comm] using this

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < x` using `lt_of_le_of_ne hx (Ne.symm hne)`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (div_pos hpos (by linarith : (0 : ℝ) < K + 1)) hr`. Establish `h1 : (K + 1) * r ^ N < x`. Rewrite using `[lt_div_iff₀ (by linarith)] at hN; linarith`.

Establish `h2` using `h N`. Use polynomial arithmetic with `[pow_nonneg hr0 N]`.
-/
theorem eq_zero_of_le_pow {x K r : ℝ} (hx : 0 ≤ x) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r < 1)
    (h : ∀ N : ℕ, x ≤ K * r ^ N) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hpos (by linarith : (0 : ℝ) < K + 1)) hr
  have h1 : (K + 1) * r ^ N < x := by
    rw [lt_div_iff₀ (by linarith)] at hN; linarith
  have h2 := h N
  nlinarith [pow_nonneg hr0 N]

end Ultra

section Concrete

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `show ‖((zOm l x : Om l) : ℂ_[l])‖ = ‖x‖`. Rewrite using `[PadicComplex.norm_extends]`. Use `show ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] x)‖ = ‖x‖`. Rewrite using `[PadicAlgCl.norm_extends]`. Conclude with `PadicInt.padic_norm_e_of_padicInt x`.
-/
theorem norm_zC (x : ℤ_[l]) : ‖((algebraMap (Om l) ℂ_[l]).comp (zOm l)) x‖ = ‖x‖ := by
  show ‖((zOm l x : Om l) : ℂ_[l])‖ = ‖x‖
  rw [PadicComplex.norm_extends]
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] x)‖ = ‖x‖
  rw [PadicAlgCl.norm_extends]
  exact PadicInt.padic_norm_e_of_padicInt x

/- English proof (translation)
Take `⟨y, rfl⟩` from `h`. Rewrite using `[norm_zC, norm_mul, norm_pow, PadicInt.norm_p, inv_pow]`. Conclude with `mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one y)`.
-/
theorem norm_zC_le_of_dvd {x : ℤ_[l]} {m : ℕ} (h : (l : ℤ_[l]) ^ m ∣ x) :
    ‖((algebraMap (Om l) ℂ_[l]).comp (zOm l)) x‖ ≤ ((l : ℝ) ^ m)⁻¹ := by
  obtain ⟨y, rfl⟩ := h
  rw [norm_zC, norm_mul, norm_pow, PadicInt.norm_p, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one y)

/- English proof (translation)
Use `show ‖((σ x : Om l) : ℂ_[l])‖ = ‖x‖`. Rewrite using `[PadicComplex.norm_extends]`. Conclude with `(spectralNorm_eq_of_equiv σ x).symm`.
-/
theorem norm_gal_C (σ : GQ l) (x : Om l) : ‖algebraMap (Om l) ℂ_[l] (σ x)‖ = ‖x‖ := by
  show ‖((σ x : Om l) : ℂ_[l])‖ = ‖x‖
  rw [PadicComplex.norm_extends]
  exact (spectralNorm_eq_of_equiv σ x).symm

/- English proof (translation)
Use `show σ (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] x)) = _`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem gal_zOm (σ : GQ l) (x : ℤ_[l]) : σ (zOm l x) = zOm l x := by
  show σ (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] x)) = _
  rw [AlgEquiv.commutes]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.trace_sum]`. Unfold `dotProduct`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.trace_smul, smul_eq_mul]`. Use `congr 1`.

Simplify using `[Matrix.trace, map_sum]`.
-/
theorem trace_sum_smul_map {a : ℕ} {ι : Type} [Fintype ι] (w : ι → ℂ_[l])
    (M : ι → Matrix (Fin a) (Fin a) (Om l)) (f : Om l →+* ℂ_[l]) :
    (∑ i, w i • (M i).map f).trace = w ⬝ᵥ fun i => f (M i).trace := by
  rw [Matrix.trace_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp [Matrix.trace, map_sum]

end Concrete

/- English proof (translation)
Introduce `l _ Γ _ _ L₀ a ha r Cl Cv σ U U' Bd S hS0 hU hU' hcomm htr`. Set `f : Om l →+* ℂ_[l]` to `(algebraMap (Om l) ℂ_[l]).comp (σ : Om l →+* Om l)`. Set `Z : ℤ_[l] →+* ℂ_[l]` to `(algebraMap (Om l) ℂ_[l]).comp (zOm l)`. Establish `hfZ : ∀ x, f (zOm l x) = Z x` using `fun x => by show algebraMap (Om l) ℂ_[l] (σ (zOm l x)) = _`. Rewrite using `[gal_zOm]`.

Both sides reduce to the same expression. Establish `hfn : ∀ x, ‖f x‖ = ‖x‖` using `norm_gal_C σ`. Set `t : Fin Cv.d → ℂ_[l]` to `fun i => f (Cv.b i).trace`. Set `v : Fin Cv.d → ℂ_[l]` to `fun s => Z (Cv.e s)`. Establish `key' : ∀ m k n, (U' m ^ n *ᵥ (fun s => Z ((Cv.lay m).e s))) ⬝ᵥ (fun s => f ((Cv.lay m).b s k).trace) = S n` using `fun m k n => by rw [← htr m k n]; exact (trace_sum_smul_map _ _ f).symm`.

Introduce `n`. Rewrite using `[show (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = (U ^ n *ᵥ v) ⬝ᵥ t from trace_sum_smul_map _ _ f]`. Establish `hX0 : (U ^ 0 *ᵥ v) ⬝ᵥ t = a`. Rewrite using `[pow_zero, Matrix.one_mulVec]`. Establish `h1` using `congrArg (fun M => f M.trace) Cv.reads.one`.

Simplify using `only [Matrix.trace_sum, Matrix.trace_smul, map_sum, smul_eq_mul, map_mul, hfZ, Matrix.trace_one, Fintype.card_fin, map_natCast] at h1`. Simplify `h1` using `[dotProduct, v, t]`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Use `set B : ℝ := max Bd 1 with hBdef`.

Establish `hB : 1 ≤ B` using `le_max_right _ _`. Establish `hB0 : 0 ≤ B` using `by linarith`. Use `set τ : ℝ := ∑ i, ‖t i‖ with hτdef`. Establish `hτ : 0 ≤ τ` using `Finset.sum_nonneg fun i _ => norm_nonneg _`. Establish `ht : ∀ i, ‖t i‖ ≤ τ` using `fun i => Finset.single_le_sum (fun j _ => norm_nonneg (t j)) (Finset.mem_univ i)`.

Establish `est : ∀ N : ℕ, ∃ C : ℂ_[l], ∀ n, ‖(U ^ n *ᵥ v) ⬝ᵥ t - C * S n‖ ≤ (B ^ n * τ + B ^ n * B * τ + B ^ n) * ((l : ℝ) ^ N)⁻¹`. Introduce `N`. Take `⟨m, hmN, hm⟩` from `hcomm N`. Establish `hεN : 0 ≤ ((l : ℝ) ^ N)⁻¹` using `inv_nonneg.2 (pow_nonneg hl0.le N)`. Establish `hε : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ N)⁻¹` using `inv_anti₀ (pow_pos hl0 N) (pow_le_pow_right₀ hl1.le hmN)`.

Set `P : Matrix (Fin Cv.d) (Fin (Cv.tw.d' m)) ℂ_[l]` to `(Cv.tw.Pi m).map Z`. Set `v' : Fin (Cv.tw.d' m) → ℂ_[l]` to `fun s => Z ((Cv.lay m).e s)`. Set `t' : Fin (Cv.lay m).m → Fin (Cv.tw.d' m) → ℂ_[l]` to `fun k s => f ((Cv.lay m).b s k).trace`. Set `T' : Fin (Cv.tw.d' m) → ℂ_[l]` to `∑ k, f ((Cv.lay m).c k) • t' k`. Use `⟨∑ k, f ((Cv.lay m).c k), fun n => ?_⟩` and prove the remaining obligations.

Establish `hT'n : (U' m ^ n *ᵥ v') ⬝ᵥ T' = (∑ k, f ((Cv.lay m).c k)) * S n`. Simplify using `only [T', dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [key' m k n]`. Rewrite using `[← hT'n]`. Establish `hv' : ∀ s, ‖v' s‖ ≤ 1` using `fun s => (norm_zC _).trans_le (PadicInt.norm_le_one _)`.

Establish `hv : ∀ i, ‖(v - P *ᵥ v') i‖ ≤ ((l : ℝ) ^ N)⁻¹`. Introduce `i`. Establish `e : (P *ᵥ v') i = Z ((Cv.tw.Pi m *ᵥ (Cv.lay m).e) i)`. Simplify using `[P, v', Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[Pi.sub_apply, e, norm_sub_rev, ← map_sub]`.

Establish `hd` using `Cv.unit m i`. Rewrite `hd` using `[Pi.sub_apply]`. Conclude with `(norm_zC_le_of_dvd hd).trans hε`. Establish `hc : ∀ i j, ‖(U * P - P * U' m) i j‖ ≤ B * ((l : ℝ) ^ N)⁻¹` using `fun i j => (hm i j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hεN)`. Establish `hT : ∀ s, ‖(t ᵥ* P - T') s‖ ≤ ((l : ℝ) ^ N)⁻¹`.

Introduce `s`. Establish `h` using `Cv.trace m s`. Establish `e : (t ᵥ* P - T') s = f ((∑ i, zOm l (Cv.tw.Pi m i s) • Cv.b i).trace - ∑ k, (Cv.lay m).c k * ((Cv.lay m).b s k).trace)`. Rewrite using `[map_sub, Matrix.trace_sum, map_sum, map_sum]`. Simplify using `only [Pi.sub_apply, Matrix.vecMul, dotProduct, T', t', t, P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.trace_smul, map_mul, hfZ, Matrix.map_apply]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[e, hfn]`. Conclude with `h.trans hε`. Establish `hc'` using `core U (U' m) P t v v' T' B τ (((l : ℝ) ^ N)⁻¹) (B * ((l : ℝ) ^ N)⁻¹) hB hτ hεN (mul_nonneg hB0 hεN) (fun i j => (hU i j).trans (le_max_left _ _)) (fun i j => (hU' m i j).trans (le_max_left _ _)) ht hv' hv hc hT n`.

Combine the equalities or inequalities in the displayed calculation. Establish `ha0 : (a : ℂ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hapos : 0 < ‖(a : ℂ_[l])‖` using `norm_pos_iff.2 ha0`. Establish `hKn : 0 ≤ B ^ n * τ + B ^ n * B * τ + B ^ n`. Use `pow_nonneg hB0 n` as an intermediate fact.

Establish `h2` using `mul_nonneg this hτ`. Establish `h3` using `mul_nonneg (mul_nonneg this hB0) hτ`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK0 : 0 ≤ B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0`. Establish `h3` using `mul_nonneg hB0 hτ`.

Simplify using `only [pow_zero, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbound : ∀ N : ℕ, ‖(U ^ n *ᵥ v) ⬝ᵥ t - S n‖ ≤ ((B ^ n * τ + B ^ n * B * τ + B ^ n) + (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ‖S n‖ / ‖(a : ℂ_[l])‖) * ((l : ℝ)⁻¹) ^ N`. Introduce `N`. Take `⟨C, hC⟩` from `est N`.

Establish `h0` using `hC 0`. Rewrite `h0` using `[hX0, hS0]`. Establish `hC1 : ‖C - 1‖ * ‖(a : ℂ_[l])‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹`. Rewrite using `[← norm_mul, show (C - 1) * (a : ℂ_[l]) = -((a : ℂ_[l]) - C * a) by ring, norm_neg]`. Conclude with `h0`.

Establish `hCb : ‖C - 1‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ / ‖(a : ℂ_[l])‖`. Rewrite using `[le_div_iff₀ hapos]`. Conclude with `hC1`. Rewrite using `[show (U ^ n *ᵥ v) ⬝ᵥ t - S n = ((U ^ n *ᵥ v) ⬝ᵥ t - C * S n) + (C - 1) * S n by ring]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hz` using `eq_zero_of_le_pow (norm_nonneg _) (add_nonneg hKn (div_nonneg (mul_nonneg hK0 (norm_nonneg _)) (norm_nonneg _))) (inv_nonneg.2 hl0.le) (inv_lt_one_of_one_lt₀ hl1) hbound`. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 hz)`.
-/
theorem trace_pow_eq : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ), 1 ≤ a → ∀ (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (σ : GQ l) (U : Matrix (Fin Cv.d) (Fin Cv.d) (ℂ_[l])) (U' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (ℂ_[l])) (Bd : ℝ) (S : ℕ → ℂ_[l]), S 0 = a → (∀ i j, ‖U i j‖ ≤ Bd) → (∀ m i j, ‖U' m i j‖ ≤ Bd) → (∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹) → (∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i • ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n) → ∀ n, (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
  intro l _ Γ _ _ L₀ a ha r Cl Cv σ U U' Bd S hS0 hU hU' hcomm htr
  let f : Om l →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp (σ : Om l →+* Om l)
  let Z : ℤ_[l] →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp (zOm l)
  have hfZ : ∀ x, f (zOm l x) = Z x := fun x => by
    show algebraMap (Om l) ℂ_[l] (σ (zOm l x)) = _
    rw [gal_zOm]; rfl
  have hfn : ∀ x, ‖f x‖ = ‖x‖ := norm_gal_C σ
  let t : Fin Cv.d → ℂ_[l] := fun i => f (Cv.b i).trace
  let v : Fin Cv.d → ℂ_[l] := fun s => Z (Cv.e s)
  have key' : ∀ m k n, (U' m ^ n *ᵥ (fun s => Z ((Cv.lay m).e s))) ⬝ᵥ (fun s => f ((Cv.lay m).b s k).trace) = S n :=
    fun m k n => by rw [← htr m k n]; exact (trace_sum_smul_map _ _ f).symm
  intro n
  rw [show (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i •
      (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = (U ^ n *ᵥ v) ⬝ᵥ t from trace_sum_smul_map _ _ f]
  have hX0 : (U ^ 0 *ᵥ v) ⬝ᵥ t = a := by
    rw [pow_zero, Matrix.one_mulVec]
    have h1 := congrArg (fun M => f M.trace) Cv.reads.one
    simp only [Matrix.trace_sum, Matrix.trace_smul, map_sum, smul_eq_mul, map_mul, hfZ, Matrix.trace_one,
      Fintype.card_fin, map_natCast] at h1
    simpa [dotProduct, v, t] using h1
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set B : ℝ := max Bd 1 with hBdef
  have hB : 1 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := by linarith
  set τ : ℝ := ∑ i, ‖t i‖ with hτdef
  have hτ : 0 ≤ τ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have ht : ∀ i, ‖t i‖ ≤ τ := fun i => Finset.single_le_sum (fun j _ => norm_nonneg (t j)) (Finset.mem_univ i)
  have est : ∀ N : ℕ, ∃ C : ℂ_[l], ∀ n, ‖(U ^ n *ᵥ v) ⬝ᵥ t - C * S n‖ ≤
      (B ^ n * τ + B ^ n * B * τ + B ^ n) * ((l : ℝ) ^ N)⁻¹ := by
    intro N
    obtain ⟨m, hmN, hm⟩ := hcomm N
    have hεN : 0 ≤ ((l : ℝ) ^ N)⁻¹ := inv_nonneg.2 (pow_nonneg hl0.le N)
    have hε : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ N)⁻¹ := inv_anti₀ (pow_pos hl0 N) (pow_le_pow_right₀ hl1.le hmN)
    let P : Matrix (Fin Cv.d) (Fin (Cv.tw.d' m)) ℂ_[l] := (Cv.tw.Pi m).map Z
    let v' : Fin (Cv.tw.d' m) → ℂ_[l] := fun s => Z ((Cv.lay m).e s)
    let t' : Fin (Cv.lay m).m → Fin (Cv.tw.d' m) → ℂ_[l] := fun k s => f ((Cv.lay m).b s k).trace
    let T' : Fin (Cv.tw.d' m) → ℂ_[l] := ∑ k, f ((Cv.lay m).c k) • t' k
    refine ⟨∑ k, f ((Cv.lay m).c k), fun n => ?_⟩
    have hT'n : (U' m ^ n *ᵥ v') ⬝ᵥ T' = (∑ k, f ((Cv.lay m).c k)) * S n := by
      simp only [T', dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [key' m k n]
    rw [← hT'n]
    have hv' : ∀ s, ‖v' s‖ ≤ 1 := fun s => (norm_zC _).trans_le (PadicInt.norm_le_one _)
    have hv : ∀ i, ‖(v - P *ᵥ v') i‖ ≤ ((l : ℝ) ^ N)⁻¹ := by
      intro i
      have e : (P *ᵥ v') i = Z ((Cv.tw.Pi m *ᵥ (Cv.lay m).e) i) := by
        simp [P, v', Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [Pi.sub_apply, e, norm_sub_rev, ← map_sub]
      have hd := Cv.unit m i
      rw [Pi.sub_apply] at hd
      exact (norm_zC_le_of_dvd hd).trans hε
    have hc : ∀ i j, ‖(U * P - P * U' m) i j‖ ≤ B * ((l : ℝ) ^ N)⁻¹ := fun i j =>
      (hm i j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hεN)
    have hT : ∀ s, ‖(t ᵥ* P - T') s‖ ≤ ((l : ℝ) ^ N)⁻¹ := by
      intro s
      have h := Cv.trace m s
      have e : (t ᵥ* P - T') s = f ((∑ i, zOm l (Cv.tw.Pi m i s) • Cv.b i).trace -
          ∑ k, (Cv.lay m).c k * ((Cv.lay m).b s k).trace) := by
        rw [map_sub, Matrix.trace_sum, map_sum, map_sum]
        simp only [Pi.sub_apply, Matrix.vecMul, dotProduct, T', t', t, P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.trace_smul, map_mul, hfZ, Matrix.map_apply]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e, hfn]
      exact h.trans hε
    have hc' := core U (U' m) P t v v' T' B τ (((l : ℝ) ^ N)⁻¹) (B * ((l : ℝ) ^ N)⁻¹) hB hτ hεN
      (mul_nonneg hB0 hεN) (fun i j => (hU i j).trans (le_max_left _ _))
      (fun i j => (hU' m i j).trans (le_max_left _ _)) ht hv' hv hc hT n
    calc _ ≤ _ := hc'
      _ = _ := by ring
  have ha0 : (a : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hapos : 0 < ‖(a : ℂ_[l])‖ := norm_pos_iff.2 ha0
  have hKn : 0 ≤ B ^ n * τ + B ^ n * B * τ + B ^ n := by
    have := pow_nonneg hB0 n
    have h2 := mul_nonneg this hτ
    have h3 := mul_nonneg (mul_nonneg this hB0) hτ
    linarith
  have hK0 : 0 ≤ B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0 := by
    have h3 := mul_nonneg hB0 hτ
    simp only [pow_zero, one_mul]
    linarith
  have hbound : ∀ N : ℕ, ‖(U ^ n *ᵥ v) ⬝ᵥ t - S n‖ ≤
      ((B ^ n * τ + B ^ n * B * τ + B ^ n) + (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ‖S n‖ / ‖(a : ℂ_[l])‖) *
        ((l : ℝ)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := est N
    have h0 := hC 0
    rw [hX0, hS0] at h0
    have hC1 : ‖C - 1‖ * ‖(a : ℂ_[l])‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ := by
      rw [← norm_mul, show (C - 1) * (a : ℂ_[l]) = -((a : ℂ_[l]) - C * a) by ring, norm_neg]
      exact h0
    have hCb : ‖C - 1‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ / ‖(a : ℂ_[l])‖ := by
      rw [le_div_iff₀ hapos]; exact hC1
    rw [show (U ^ n *ᵥ v) ⬝ᵥ t - S n = ((U ^ n *ᵥ v) ⬝ᵥ t - C * S n) + (C - 1) * S n by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    calc _ ≤ (B ^ n * τ + B ^ n * B * τ + B ^ n) * ((l : ℝ) ^ N)⁻¹ +
          (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ / ‖(a : ℂ_[l])‖ * ‖S n‖ :=
          add_le_add (hC n) (mul_le_mul_of_nonneg_right hCb (norm_nonneg _))
      _ = _ := by rw [inv_pow]; field_simp
  have hz := eq_zero_of_le_pow (norm_nonneg _)
    (add_nonneg hKn (div_nonneg (mul_nonneg hK0 (norm_nonneg _)) (norm_nonneg _)))
    (inv_nonneg.2 hl0.le) (inv_lt_one_of_one_lt₀ hl1) hbound
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

end GlobalTheory.CoverTrace
