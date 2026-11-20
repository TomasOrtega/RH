import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open Polynomial Matrix
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

namespace GelfH

def qm (S : Multiset ℂ) : ℂ[X] := (S.map fun c => 1 - C c * X).prod

/- English proof (translation)
Simplify using `[qm, Multiset.map_add, Multiset.prod_add]`.
-/
theorem qm_add (S T : Multiset ℂ) : qm (S + T) = qm S * qm T := by
  simp [qm, Multiset.map_add, Multiset.prod_add]

/- English proof (translation)
Rewrite using `[mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hc]`. Simplify using `only [C_neg, neg_mul, C_1, sub_neg_eq_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_sub_eq (c : ℂ) (hc : c ≠ 0) : (1 - C c * X : ℂ[X]) = C (-c) * (X - C c⁻¹) := by
  rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hc]
  simp only [C_neg, neg_mul, C_1, sub_neg_eq_add]
  ring

/- English proof (translation)
Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simp [qm]`. Consider the case `cons a S ih`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality.

Rewrite using `[show qm (0 ::ₘ S) = qm S by simp [qm]]`. Rewrite using `[Multiset.filter_cons_of_neg (p := fun c : ℂ => c ≠ 0) S (by simp)]`. Conclude with `ih`. Rewrite using `[show qm (a ::ₘ S) = (1 - C a * X) * qm S by simp [qm], ih, Multiset.filter_cons_of_pos (p := fun c : ℂ => c ≠ 0) S ha]`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, C_mul, one_sub_eq a ha]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem qm_eq (S : Multiset ℂ) :
    qm S = C ((S.filter (· ≠ 0)).map (fun c => -c)).prod * ((S.filter (· ≠ 0)).map fun c => X - C c⁻¹).prod := by
  induction S using Multiset.induction_on with
  | empty => simp [qm]
  | cons a S ih =>
    by_cases ha : a = 0
    · subst ha
      rw [show qm (0 ::ₘ S) = qm S by simp [qm]]
      rw [Multiset.filter_cons_of_neg (p := fun c : ℂ => c ≠ 0) S (by simp)]
      exact ih
    · rw [show qm (a ::ₘ S) = (1 - C a * X) * qm S by simp [qm], ih, Multiset.filter_cons_of_pos (p := fun c : ℂ => c ≠ 0) S ha]
      simp only [Multiset.map_cons, Multiset.prod_cons, C_mul, one_sub_eq a ha]
      ring

/- English proof (translation)
Rewrite using `[qm_eq, roots_C_mul]`. Use `roots_multiset_prod_X_sub_C ((S.filter (· ≠ 0)).map fun c => c⁻¹)` as an intermediate fact. Rewrite `this` using `[Multiset.map_map]`. Conclude with `this`. Conclude with `Multiset.prod_ne_zero (by simp)`.
-/
theorem roots_qm (S : Multiset ℂ) : (qm S).roots = (S.filter (· ≠ 0)).map fun c => c⁻¹ := by
  rw [qm_eq, roots_C_mul]
  · have := roots_multiset_prod_X_sub_C ((S.filter (· ≠ 0)).map fun c => c⁻¹)
    rw [Multiset.map_map] at this
    exact this
  · exact Multiset.prod_ne_zero (by simp)

/- English proof (translation)
Establish `e` using `congrArg Polynomial.roots h`. Rewrite `e` using `[roots_qm, roots_qm]`. Establish `e2` using `congrArg (Multiset.map fun c : ℂ => c⁻¹) e`. Simplify using `only [Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_id'] at e2`. Conclude with `e2`.
-/
theorem filter_eq_of_qm {S T : Multiset ℂ} (h : qm S = qm T) : S.filter (· ≠ 0) = T.filter (· ≠ 0) := by
  have e := congrArg Polynomial.roots h
  rw [roots_qm, roots_qm] at e
  have e2 := congrArg (Multiset.map fun c : ℂ => c⁻¹) e
  simp only [Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_id'] at e2
  exact e2

/- English proof (translation)
Establish `h1` using `filter_eq_of_qm h`. Establish `hS` using `Multiset.filter_add_not (· ≠ (0 : ℂ)) S`. Establish `hT` using `Multiset.filter_add_not (· ≠ (0 : ℂ)) T`. Establish `z1 : S.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (S.filter fun c => ¬ c ≠ 0)) 0` using `Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩`. Establish `z2 : T.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (T.filter fun c => ¬ c ≠ 0)) 0` using `Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩`.

Establish `cS` using `congrArg Multiset.card hS`. Establish `cT` using `congrArg Multiset.card hT`. Rewrite `cS`, `cT` using `[Multiset.card_add]`. Rewrite using `[← hS, ← hT, h1, z1, z2]`. Use `congr 2`.

Rewrite `cS` using `[h1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_qm {S T : Multiset ℂ} (h : qm S = qm T) (hc : Multiset.card S = Multiset.card T) : S = T := by
  have h1 := filter_eq_of_qm h
  have hS := Multiset.filter_add_not (· ≠ (0 : ℂ)) S
  have hT := Multiset.filter_add_not (· ≠ (0 : ℂ)) T
  have z1 : S.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (S.filter fun c => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩
  have z2 : T.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (T.filter fun c => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩
  have cS := congrArg Multiset.card hS
  have cT := congrArg Multiset.card hT
  rw [Multiset.card_add] at cS cT
  rw [← hS, ← hT, h1, z1, z2]
  congr 2
  rw [h1] at cS
  omega

def sh (M : Multiset ℂ) : Multiset ℂ := M.map (· + 1)

/- English proof (translation)
The claim follows from `Multiset.count_eq_zero.2 fun h => by have := hx _ h; simp at this; linarith`.
-/
theorem count_sh_top {M : Multiset ℂ} {x : ℂ} (hx : ∀ c ∈ M, c.re ≤ x.re) : M.count (x + 1) = 0 :=
  Multiset.count_eq_zero.2 fun h => by have := hx _ h; simp at this; linarith

/- English proof (translation)
Rewrite using `[sh, Multiset.count_map_eq_count' _ _ (add_left_injective 1)]`.
-/
theorem count_sh (M : Multiset ℂ) (x : ℂ) : (sh M).count (x + 1) = M.count x := by
  rw [sh, Multiset.count_map_eq_count' _ _ (add_left_injective 1)]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `a b hN h`. Distinguish the cases in `h0 : a + b = 0`.

Rewrite `h0` using `[add_eq_zero]`. Rewrite using `[h0.1, h0.2]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hmax⟩ : ∃ x ∈ a + b, ∀ c ∈ a + b, c.re ≤ x.re := by`. Conclude with `Multiset.exists_max_image (fun c : ℂ => c.re) h0`. Establish `ha : ∀ c ∈ a, c.re ≤ x.re` using `fun c hc => hmax c (Multiset.mem_add.2 (Or.inl hc))`.

Establish `hb : ∀ c ∈ b, c.re ≤ x.re` using `fun c hc => hmax c (Multiset.mem_add.2 (Or.inr hc))`. Establish `e` using `congrArg (fun M => Multiset.count (x + 1) M) h`. Simplify using `only [Multiset.count_add, count_sh_top ha, count_sh_top hb, count_sh, zero_add] at e`. Establish `hxa : x ∈ a`. Break down `Multiset.mem_add.1 hx with h1 | h1` into its components or cases.

Conclude with `h1`. Rewrite using `[← Multiset.count_pos, ← e]`. Conclude with `Multiset.count_pos.2 h1`. Establish `hxb : x ∈ b` using `by rw [← Multiset.count_pos, e]; exact Multiset.count_pos.2 hxa`. Take `⟨a', rfl⟩` from `Multiset.exists_cons_of_mem hxa`.

Take `⟨b', rfl⟩` from `Multiset.exists_cons_of_mem hxb`. Establish `e1 : x ::ₘ a' + sh (x ::ₘ b') = x ::ₘ (x + 1) ::ₘ (a' + sh b')`. Rewrite using `[sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]`. Establish `e2 : x ::ₘ b' + sh (x ::ₘ a') = x ::ₘ (x + 1) ::ₘ (b' + sh a')`. Rewrite using `[sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]`.

Rewrite `h` using `[e1, e2]`. Establish `h' : a' + sh b' = b' + sh a'` using `(Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 h)`. Use `ih (Multiset.card a' + Multiset.card b') (by rw [← hN]; simp; omega) a' b' rfl h'` as an intermediate fact. Rewrite using `[this]`.
-/
theorem eq_of_shift : ∀ (N : ℕ) (a b : Multiset ℂ), Multiset.card a + Multiset.card b = N →
    a + sh b = b + sh a → a = b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b hN h
  by_cases h0 : a + b = 0
  · rw [add_eq_zero] at h0
    rw [h0.1, h0.2]
  obtain ⟨x, hx, hmax⟩ : ∃ x ∈ a + b, ∀ c ∈ a + b, c.re ≤ x.re := by
    exact Multiset.exists_max_image (fun c : ℂ => c.re) h0
  have ha : ∀ c ∈ a, c.re ≤ x.re := fun c hc => hmax c (Multiset.mem_add.2 (Or.inl hc))
  have hb : ∀ c ∈ b, c.re ≤ x.re := fun c hc => hmax c (Multiset.mem_add.2 (Or.inr hc))
  have e := congrArg (fun M => Multiset.count (x + 1) M) h
  simp only [Multiset.count_add, count_sh_top ha, count_sh_top hb, count_sh, zero_add] at e
  have hxa : x ∈ a := by
    rcases Multiset.mem_add.1 hx with h1 | h1
    · exact h1
    · rw [← Multiset.count_pos, ← e]; exact Multiset.count_pos.2 h1
  have hxb : x ∈ b := by rw [← Multiset.count_pos, e]; exact Multiset.count_pos.2 hxa
  obtain ⟨a', rfl⟩ := Multiset.exists_cons_of_mem hxa
  obtain ⟨b', rfl⟩ := Multiset.exists_cons_of_mem hxb
  have e1 : x ::ₘ a' + sh (x ::ₘ b') = x ::ₘ (x + 1) ::ₘ (a' + sh b') := by
    rw [sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
  have e2 : x ::ₘ b' + sh (x ::ₘ a') = x ::ₘ (x + 1) ::ₘ (b' + sh a') := by
    rw [sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
  rw [e1, e2] at h
  have h' : a' + sh b' = b' + sh a' := (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 h)
  have := ih (Multiset.card a' + Multiset.card b') (by rw [← hN]; simp; omega) a' b' rfl h'
  rw [this]

end GelfH

namespace GelfM

open PowerSeries

variable {n : ℕ}

def S (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ := Matrix.of fun i j => mk fun k => (A ^ k) i j

def M (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ := 1 - (PowerSeries.X : ℂ⟦X⟧) • A.map (fun a => (PowerSeries.C a : ℂ⟦X⟧))

/- English proof (translation)
Use extensionality with `i j m`. Simplify using `only [Matrix.mul_apply, S, Matrix.map_apply, Matrix.of_apply, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]`. Rewrite using `[pow_succ', Matrix.mul_apply]`.
-/
theorem mapC_mul_S (A : Matrix (Fin n) (Fin n) ℂ) :
    A.map (fun a => (PowerSeries.C a : ℂ⟦X⟧)) * S A = Matrix.of fun i j => mk fun k => (A ^ (k + 1)) i j := by
  ext i j m
  simp only [Matrix.mul_apply, S, Matrix.map_apply, Matrix.of_apply, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  rw [pow_succ', Matrix.mul_apply]

/- English proof (translation)
Use `PowerSeries.ext (R := ℂ) fun m => ?_` and prove the remaining obligations. Consider the cases of `m with`. Consider the case `zero => simp [coeff_zero_X_mul]`. Consider the case `succ m => simp [coeff_succ_X_mul]`.
-/
theorem X_mul_shift (f : ℕ → ℂ) : (PowerSeries.X : ℂ⟦X⟧) * mk (fun k => f (k + 1)) = mk f - PowerSeries.C (f 0) := by
  refine PowerSeries.ext (R := ℂ) fun m => ?_
  cases m with
  | zero => simp [coeff_zero_X_mul]
  | succ m => simp [coeff_succ_X_mul]

/- English proof (translation)
Rewrite using `[M, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, mapC_mul_S]`. Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, S]`. Rewrite using `[X_mul_shift (fun k => (A ^ k) i j)]`. Simplify using `only [pow_zero, sub_sub_cancel]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem M_mul_S (A : Matrix (Fin n) (Fin n) ℂ) : M A * S A = 1 := by
  rw [M, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, mapC_mul_S]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, S]
  rw [X_mul_shift (fun k => (A ^ k) i j)]
  simp only [pow_zero, sub_sub_cancel]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (M_mul_S A)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ h`.
-/
theorem isUnit_det (A : Matrix (Fin n) (Fin n) ℂ) : IsUnit (M A).det := by
  have h := congrArg Matrix.det (M_mul_S A)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (M_mul_S A)`.
-/
theorem inv_M (A : Matrix (Fin n) (Fin n) ℂ) : (M A)⁻¹ = S A := Matrix.inv_eq_right_inv (M_mul_S A)

def tot (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ := ∑ a, ∑ b, (A ^ k) a b

/- English proof (translation)
Use `(Matrix.det_add_replicateCol_mul_replicateRow (ι := Fin 1) (isUnit_det A) _ _).trans ?_` and prove the remaining obligations. Rewrite using `[inv_M]`. Establish `hdet : ∀ B : Matrix (Fin 1) (Fin 1) ℂ⟦X⟧, @Matrix.det (Fin 1) (fun a b => decidableEq_of_subsingleton a b) Unique.fintype _ _ B = B 0 0` using `fun B => by`. Conclude with `Matrix.det_unique B`. Rewrite using `[hdet]`.

Establish `hsum : ∑ i, ∑ j, S A i j = mk (tot A)`. Use `PowerSeries.ext (R := ℂ) fun m => ?_` and prove the remaining obligations. Simplify using `[S, tot, map_sum, coeff_mk]`. Use `congr 1`. Simplify using `only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply, one_mul]`.

Rewrite using `[← Finset.sum_mul, Finset.sum_comm, hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_rank_one (A : Matrix (Fin n) (Fin n) ℂ) :
    (M A + Matrix.replicateCol (Fin 1) (fun _ => -(PowerSeries.X : ℂ⟦X⟧)) * Matrix.replicateRow (Fin 1) (fun _ => (1 : ℂ⟦X⟧))).det =
      (M A).det * (1 - PowerSeries.X * mk (tot A)) := by
  refine (Matrix.det_add_replicateCol_mul_replicateRow (ι := Fin 1) (isUnit_det A) _ _).trans ?_
  rw [inv_M]
  have hdet : ∀ B : Matrix (Fin 1) (Fin 1) ℂ⟦X⟧,
      @Matrix.det (Fin 1) (fun a b => decidableEq_of_subsingleton a b) Unique.fintype _ _ B = B 0 0 := fun B => by
    exact Matrix.det_unique B
  rw [hdet]
  have hsum : ∑ i, ∑ j, S A i j = mk (tot A) := by
    refine PowerSeries.ext (R := ℂ) fun m => ?_
    simp [S, tot, map_sum, coeff_mk]
  congr 1
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, one_mul]
  rw [← Finset.sum_mul, Finset.sum_comm, hsum]
  ring

end GelfM

namespace GelfM

open PowerSeries

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[GelfH.qm, map_multiset_prod, Multiset.map_map]`. Use `congr 1`. Use `Multiset.map_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]`.
-/
theorem coe_qm (S : Multiset ℂ) :
    Polynomial.coeToPowerSeries.ringHom (GelfH.qm S) = (S.map fun c => 1 - PowerSeries.C c * PowerSeries.X).prod := by
  rw [GelfH.qm, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun c _ => ?_
  simp only [Function.comp_apply, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular, coe_qm, Multiset.map_map]`. Rewrite using `[show (Finset.univ.val.map ((fun c => 1 - PowerSeries.C c * PowerSeries.X) ∘ l)) = Finset.univ.val.map (fun i => M (Formalism.REAL.Amat l) i i) from ?_]`. Both sides reduce to the same expression. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[M, Formalism.REAL.Amat, mul_comm]`.

Introduce `i j hij`. Establish `h1 : i ≠ j` using `fun h => by subst h; exact lt_irrefl _ hij`. Establish `h2 : ¬ i < j` using `fun h => lt_asymm h hij`. Simplify using `[M, Formalism.REAL.Amat, h1, h2]`.
-/
theorem det_M (l : Fin n → ℂ) :
    (M (Formalism.REAL.Amat l)).det = Polynomial.coeToPowerSeries.ringHom (GelfH.qm (Finset.univ.val.map l)) := by
  rw [Matrix.det_of_isUpperTriangular, coe_qm, Multiset.map_map]
  · rw [show (Finset.univ.val.map ((fun c => 1 - PowerSeries.C c * PowerSeries.X) ∘ l)) =
        Finset.univ.val.map (fun i => M (Formalism.REAL.Amat l) i i) from ?_]
    · rfl
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [M, Formalism.REAL.Amat, mul_comm]
  · intro i j hij
    have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    have h2 : ¬ i < j := fun h => lt_asymm h hij
    simp [M, Formalism.REAL.Amat, h1, h2]

def M1 (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ :=
  M A + Matrix.replicateCol (Fin 1) (fun _ => -(PowerSeries.X : ℂ⟦X⟧)) * Matrix.replicateRow (Fin 1) (fun _ => (1 : ℂ⟦X⟧))

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular, coe_qm, GelfH.sh, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]`. Use `congr 1`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[M1, M, Formalism.REAL.Amat, Matrix.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i j hij`. Establish `h3 : i < j` using `hij`. Establish `h1 : i ≠ j` using `ne_of_lt h3`. Simplify using `[M1, M, Formalism.REAL.Amat, h1, h3, Matrix.mul_apply]`.
-/
theorem det_gelfand_matrix_eq (l : Fin n → ℂ) :
    (M1 (Formalism.REAL.Amat l)).det = Polynomial.coeToPowerSeries.ringHom (GelfH.qm (GelfH.sh (Finset.univ.val.map l))) := by
  rw [Matrix.det_of_isLowerTriangular, coe_qm, GelfH.sh, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  · congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [M1, M, Formalism.REAL.Amat, Matrix.mul_apply]
    ring
  · intro i j hij
    have h3 : i < j := hij
    have h1 : i ≠ j := ne_of_lt h3
    simp [M1, M, Formalism.REAL.Amat, h1, h3, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[← det_gelfand_matrix_eq, M1, det_rank_one, det_M]`.
-/
theorem key (l : Fin n → ℂ) :
    Polynomial.coeToPowerSeries.ringHom (GelfH.qm (GelfH.sh (Finset.univ.val.map l))) =
      Polynomial.coeToPowerSeries.ringHom (GelfH.qm (Finset.univ.val.map l)) * (1 - PowerSeries.X * mk (tot (Formalism.REAL.Amat l))) := by
  rw [← det_gelfand_matrix_eq, M1, det_rank_one, det_M]

end GelfM

open GelfH GelfM in
/- English proof (translation)
Introduce `n x y h`. Use `set l : Fin n → ℂ := fun c => x c + ((n : ℂ) - 1) / 2 with hl`. Use `set l' : Fin n → ℂ := fun c => y c + ((n : ℂ) - 1) / 2 with hl'`. Establish `ht : tot (Formalism.REAL.Amat l) = tot (Formalism.REAL.Amat l')` using `funext fun k => h k`. Establish `k1` using `key l`.

Establish `k2` using `key l'`. Rewrite `k2` using `[← ht]`. Use `set a := Finset.univ.val.map l`. Use `set b := Finset.univ.val.map l'`. Establish `e : Polynomial.coeToPowerSeries.ringHom (qm (a + sh b)) = Polynomial.coeToPowerSeries.ringHom (qm (b + sh a))`.

Rewrite using `[qm_add, qm_add, map_mul, map_mul, k1, k2]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : qm (a + sh b) = qm (b + sh a)` using `Polynomial.coe_injective ℂ (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using e)`. Establish `hc : Multiset.card (a + sh b) = Multiset.card (b + sh a)` using `by simp [a, b, sh]`. Establish `e3` using `eq_of_qm e2 hc`.

Establish `e4` using `eq_of_shift _ a b rfl e3`. Establish `e5` using `congrArg (Multiset.map fun c => c - ((n : ℂ) - 1) / 2) e4`. Simplify using `only [a, b, Multiset.map_map, Function.comp_def, hl, hl', add_sub_cancel_right] at e5`. Conclude with `e5`.
-/
theorem gelfInj : GelfInj := by
  intro n x y h
  set l : Fin n → ℂ := fun c => x c + ((n : ℂ) - 1) / 2 with hl
  set l' : Fin n → ℂ := fun c => y c + ((n : ℂ) - 1) / 2 with hl'
  have ht : tot (Formalism.REAL.Amat l) = tot (Formalism.REAL.Amat l') := funext fun k => h k
  have k1 := key l
  have k2 := key l'
  rw [← ht] at k2
  set a := Finset.univ.val.map l
  set b := Finset.univ.val.map l'
  have e : Polynomial.coeToPowerSeries.ringHom (qm (a + sh b)) = Polynomial.coeToPowerSeries.ringHom (qm (b + sh a)) := by
    rw [qm_add, qm_add, map_mul, map_mul, k1, k2]
    ring
  have e2 : qm (a + sh b) = qm (b + sh a) := Polynomial.coe_injective ℂ (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using e)
  have hc : Multiset.card (a + sh b) = Multiset.card (b + sh a) := by simp [a, b, sh]
  have e3 := eq_of_qm e2 hc
  have e4 := eq_of_shift _ a b rfl e3
  have e5 := congrArg (Multiset.map fun c => c - ((n : ℂ) - 1) / 2) e4
  simp only [a, b, Multiset.map_map, Function.comp_def, hl, hl', add_sub_cancel_right] at e5
  exact e5

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
