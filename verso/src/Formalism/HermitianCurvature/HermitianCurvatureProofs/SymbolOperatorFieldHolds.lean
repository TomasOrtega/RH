import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SymbolOperatorExtension

variable {d : ℕ}

def ext (S : SOp d) (n : ℕ) (w : Fin n → Fin d) : (Fin d → ℝ) → ℂ :=
  if h : n < S.ord + 1 then S.a ⟨n, h⟩ w else fun _ => 0

/- English proof (translation)
Unfold `ext`. Rewrite using `[dif_pos k.isLt]`.
-/
theorem ext_fin (S : SOp d) (k : Fin (S.ord + 1)) (w : Fin k → Fin d) : ext S k w = S.a k w := by
  unfold ext
  rw [dif_pos k.isLt]

/- English proof (translation)
Unfold `ext`. Rewrite using `[dif_pos (Nat.lt_succ_self _)]`. Both sides reduce to the same expression.
-/
theorem ext_last (S : SOp d) (w : Fin S.ord → Fin d) : ext S S.ord w = S.a (Fin.last S.ord) w := by
  unfold ext
  rw [dif_pos (Nat.lt_succ_self _)]
  rfl

/- English proof (translation)
Unfold `ext`. Rewrite using `[dif_neg (lt_irrefl _)]`.
-/
theorem ext_top (S : SOp d) (w : Fin (S.ord + 1) → Fin d) : ext S (S.ord + 1) w = fun _ => 0 := by
  unfold ext
  rw [dif_neg (lt_irrefl _)]

/- English proof (translation)
Unfold `ext`. Use `split_ifs with h`. Conclude with `hS _ _`. Conclude with `contDiffOn_const`.
-/
theorem ext_contDiffOn (S : SOp d) {O : Set (Fin d → ℝ)} (hS : ∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) (n : ℕ)
    (w : Fin n → Fin d) : ContDiffOn ℝ ∞ (ext S n w) O := by
  unfold ext
  split_ifs with h
  · exact hS _ _
  · exact contDiffOn_const

/- English proof (translation)
Rewrite using `[← Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x)]`. Unfold `SOp.app`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [ext_fin]`.
-/
theorem app_eq (S : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    S.app u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x)]
  unfold SOp.app
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ext_fin]

/- English proof (translation)
The claim follows from `| [], k, h => hu.of_le (by exact_mod_cast (show k ≤ m by simpa using h)) | i :: l, k, h => by have ih := pdc_contDiffOn hO hu l (k + 1) (by simp at h; omega) have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (pdc l u)) O := ih.fderiv_of_isOpen hO (by push_cast; exact le_rfl) show …`.
-/
theorem pdc_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) :
    ∀ (l : List (Fin d)) (k : ℕ), l.length + k ≤ m → ContDiffOn ℝ (k : WithTop ℕ∞) (pdc l u) O
  | [], k, h => hu.of_le (by exact_mod_cast (show k ≤ m by simpa using h))
  | i :: l, k, h => by
    have ih := pdc_contDiffOn hO hu l (k + 1) (by simp at h; omega)
    have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (pdc l u)) O :=
      ih.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
    show ContDiffOn ℝ (k : WithTop ℕ∞) (fun x => fderiv ℝ (pdc l u) x (Pi.single i 1)) O
    exact h1.clm_apply contDiffOn_const

/- English proof (translation)
The claim follows from `((pdc_contDiffOn hO hu l 1 hl).differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)`.
-/
theorem pdc_diffAt {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) (l : List (Fin d)) (hl : l.length + 1 ≤ m) {x : Fin d → ℝ}
    (hx : x ∈ O) : DifferentiableAt ℝ (pdc l u) x :=
  ((pdc_contDiffOn hO hu l 1 hl).differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single v]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i (v i) : Fin d → ℝ) = v i • (Pi.single i 1 : Fin d → ℝ)`. Use extensionality with `j`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[this, map_smul, Complex.real_smul]`.
-/
theorem fderiv_apply_sum (f : (Fin d → ℝ) → ℂ) (x v : Fin d → ℝ) :
    fderiv ℝ f x v = ∑ i, (v i : ℂ) * fderiv ℝ f x (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin d → ℝ) = v i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, Complex.real_smul]

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp g, Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem sum_fin_succ_fun {n : ℕ} (g : (Fin (n + 1) → Fin d) → ℂ) :
    ∑ w, g w = ∑ i : Fin d, ∑ w : Fin n → Fin d, g (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp g, Fintype.sum_prod_type]
  rfl

def cD (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (n : ℕ) (w : Fin n → Fin d) (x : Fin d → ℝ) : ℂ :=
  fderiv ℝ (ext S n w) x (V x)

def cE (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : (n : ℕ) → (Fin n → Fin d) → (Fin d → ℝ) → ℂ
  | 0, _, _ => 0
  | n + 1, w, x => ext S n (Fin.tail w) x * ((V x (w 0) : ℝ) : ℂ)

def fieldOp (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : SOp d :=
  ⟨S.ord + 1, fun k w x => cD S V k w x + cE S V k w x⟩

/- English proof (translation)
Simplify using `[cD, ext_top]`.
-/
theorem cD_top (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (w : Fin (S.ord + 1) → Fin d) (x : Fin d → ℝ) :
    cD S V (S.ord + 1) w x = 0 := by
  simp [cD, ext_top]

/- English proof (translation)
Unfold `SOp.app fieldOp`. Conclude with `Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x) (S.ord + 1 + 1)`.
-/
theorem fieldOp_app (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    (fieldOp S V).app u x = ∑ n ∈ Finset.range (S.ord + 1 + 1),
      ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x := by
  unfold SOp.app fieldOp
  exact Fin.sum_univ_eq_sum_range
    (fun n => ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x) (S.ord + 1 + 1)

end SymbolOperatorExtension

open SymbolOperatorExtension in
/- English proof (translation)
Introduce `d S V O hO hS hV`. Use `⟨fieldOp S V, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k w show ContDiffOn ℝ ∞ (fun x => cD S V k w x + cE S V k w x) O`. Use `ContDiffOn.add ?_ ?_` and prove the remaining obligations. Conclude with `((ext_contDiffOn S hS k w).fderiv_of_isOpen hO (by simp)).clm_apply hV`.

Break down `k with ⟨_ | n, hk⟩` into its components or cases. Conclude with `contDiffOn_const`. Establish `hv : ContDiffOn ℝ ∞ (fun x => ((V x (w 0) : ℝ) : ℂ)) O`. Use `Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hV (w 0))` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Conclude with `(ext_contDiffOn S hS n _).mul hv`. Introduce `u hu x hx`. Establish `hdiff : ∀ n ∈ Finset.range (S.ord + 1), ∀ w : Fin n → Fin d, DifferentiableAt ℝ (ext S n w) x ∧ DifferentiableAt ℝ (pdc (List.ofFn w) u) x`. Introduce `n hn w`. Use `⟨((ext_contDiffOn S hS n w).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx), pdc_diffAt hO hu _ ?_ hx⟩` and prove the remaining obligations.

Use `Finset.mem_range.mp hn` as an intermediate fact. Simplify using `only [List.length_ofFn]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ n ∈ Finset.range (S.ord + 1), fderiv ℝ (fun y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) x (V x) = ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x + ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x)`. Introduce `n hn`.

Rewrite using `[fderiv_fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) (fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[fderiv_fun_mul (hdiff n hn w).1 (hdiff n hn w).2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, fderiv_apply_sum (pdc (List.ofFn w) u), Finset.mul_sum, add_comm]`. Use `congr 1`. Simplify using `only [cD]`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression. Establish `hR : fderiv ℝ (S.app u) x (V x) = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x + ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x)`.

Establish `hSu : S.app u = fun y => ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y` using `funext (app_eq S u)`. Rewrite using `[hSu, fderiv_fun_sum (A := fun n y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) (fun n hn => DifferentiableAt.fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl key`. Establish `hsplit : ∀ n, ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x = ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x + ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x`. Introduce `n`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun w _ => add_mul _ _ _`. Establish `hD : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x`. Rewrite using `[Finset.sum_range_succ]`. Simplify using `[cD_top]`.

Establish `hE : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x`. Rewrite using `[Finset.sum_range_succ']`. Simplify using `only [cE, zero_mul, Finset.sum_const_zero, add_zero]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[sum_fin_succ_fun, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ]`. Rewrite using `[fieldOp_app]`. Simplify using `only [hsplit]`. Rewrite using `[Finset.sum_add_distrib, hD, hE, ← Finset.sum_add_distrib]`.

Use `show _ = fderiv ℝ (S.app u) x (V x)`. Rewrite using `[hR]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib]`. Introduce `x _ ξ show ∑ w : Fin (S.ord + 1) → Fin d, (∏ i, (ξ (w i) : ℂ)) * (cD S V (S.ord + 1) w x + cE S V (S.ord + 1) w x) = _`.

Simplify using `only [cD_top, zero_add, cE]`. Rewrite using `[sum_fin_succ_fun]`. Simplify using `only [Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]`. Unfold `SOp.symb`. Simplify using `only [dotProduct]`.

Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[ext_last]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symbol_operator_field_holds : SOpField := by
  intro d S V O hO hS hV
  refine ⟨fieldOp S V, rfl, ?_, ?_, ?_⟩
  · intro k w
    show ContDiffOn ℝ ∞ (fun x => cD S V k w x + cE S V k w x) O
    refine ContDiffOn.add ?_ ?_
    · exact ((ext_contDiffOn S hS k w).fderiv_of_isOpen hO (by simp)).clm_apply hV
    · rcases k with ⟨_ | n, hk⟩
      · exact contDiffOn_const
      · have hv : ContDiffOn ℝ ∞ (fun x => ((V x (w 0) : ℝ) : ℂ)) O := by
          have := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hV (w 0))
          simpa [Function.comp_def] using this
        exact (ext_contDiffOn S hS n _).mul hv
  · intro u hu x hx
    have hdiff : ∀ n ∈ Finset.range (S.ord + 1), ∀ w : Fin n → Fin d,
        DifferentiableAt ℝ (ext S n w) x ∧ DifferentiableAt ℝ (pdc (List.ofFn w) u) x := by
      intro n hn w
      refine ⟨((ext_contDiffOn S hS n w).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx),
        pdc_diffAt hO hu _ ?_ hx⟩
      have := Finset.mem_range.mp hn
      simp only [List.length_ofFn]
      omega
    have key : ∀ n ∈ Finset.range (S.ord + 1),
        fderiv ℝ (fun y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) x (V x) =
          ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x +
            ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      intro n hn
      rw [fderiv_fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y)
        (fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [fderiv_fun_mul (hdiff n hn w).1 (hdiff n hn w).2, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        fderiv_apply_sum (pdc (List.ofFn w) u), Finset.mul_sum, add_comm]
      congr 1
      · simp only [cD]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        rfl
    have hR : fderiv ℝ (S.app u) x (V x) = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
        (cD S V n w x * pdc (List.ofFn w) u x +
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      have hSu : S.app u = fun y => ∑ n ∈ Finset.range (S.ord + 1),
          ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y := funext (app_eq S u)
      rw [hSu, fderiv_fun_sum (A := fun n y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y)
        (fun n hn => DifferentiableAt.fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) fun w _ =>
        (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl key
    have hsplit : ∀ n, ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x =
        ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x +
          ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x := by
      intro n
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => add_mul _ _ _
    have hD : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x := by
      rw [Finset.sum_range_succ]
      simp [cD_top]
    have hE : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x := by
      rw [Finset.sum_range_succ']
      simp only [cE, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sum_fin_succ_fun, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ]
    rw [fieldOp_app]
    simp only [hsplit]
    rw [Finset.sum_add_distrib, hD, hE, ← Finset.sum_add_distrib]
    show _ = fderiv ℝ (S.app u) x (V x)
    rw [hR]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_add_distrib]
  · intro x _ ξ
    show ∑ w : Fin (S.ord + 1) → Fin d, (∏ i, (ξ (w i) : ℂ)) * (cD S V (S.ord + 1) w x + cE S V (S.ord + 1) w x) = _
    simp only [cD_top, zero_add, cE]
    rw [sum_fin_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
    unfold SOp.symb
    simp only [dotProduct]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ext_last]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
