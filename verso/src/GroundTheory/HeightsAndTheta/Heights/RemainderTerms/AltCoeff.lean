import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VandermondeOfEqDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

variable {m : ℕ}

abbrev ex (v : Fin m → ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm v

def cf (v : Fin m → ℕ) (P : MvPolynomial (Fin m) ℚ) : ℚ := coeff (ex v) P

def alt (v : Fin m → ℕ) : MvPolynomial (Fin m) ℚ :=
  (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) ℚ) ^ v j).det

def IsAlt (P : MvPolynomial (Fin m) ℚ) : Prop :=
  ∀ σ : Perm (Fin m), rename σ P = (Perm.sign σ : ℤ) • P

def stair (m : ℕ) : Fin m → ℕ := fun j => m - 1 - (j : ℕ)

/- English proof (translation)
Use extensionality with `i`. Use `conv_lhs => rw [← σ.apply_symm_apply i]`. Rewrite using `[Finsupp.mapDomain_apply σ.injective]`. Simplify using the standard rewrite rules.
-/
theorem ex_comp_symm (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    Finsupp.mapDomain σ (ex v) = ex (v ∘ σ.symm) := by
  ext i
  conv_lhs => rw [← σ.apply_symm_apply i]
  rw [Finsupp.mapDomain_apply σ.injective]
  simp

/- English proof (translation)
Unfold `cf`. Rewrite using `[← ex_comp_symm, coeff_rename_mapDomain _ σ.injective]`.
-/
theorem cf_rename (v : Fin m → ℕ) (σ : Perm (Fin m)) (P : MvPolynomial (Fin m) ℚ) :
    cf (v ∘ σ.symm) (rename σ P) = cf v P := by
  unfold cf
  rw [← ex_comp_symm, coeff_rename_mapDomain _ σ.injective]

/- English proof (translation)
Unfold `alt`. Rewrite using `[AlgHom.map_det, zsmul_eq_mul, ← Matrix.det_permute]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.submatrix]`.
-/
theorem rename_alt (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    rename σ (alt v) = (Perm.sign σ : ℤ) • alt v := by
  unfold alt
  rw [AlgHom.map_det, zsmul_eq_mul, ← Matrix.det_permute]
  congr 1
  ext i j
  simp [Matrix.submatrix]

/- English proof (translation)
Introduce `σ` and use `rename_alt v σ`.
-/
theorem alt_isAlt (v : Fin m → ℕ) : IsAlt (alt v) := fun σ => rename_alt v σ

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]`.
-/
theorem sign_mul_self (σ : Perm (Fin m)) :
    ((Perm.sign σ : ℤ) : ℚ) * ((Perm.sign σ : ℤ) : ℚ) = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Establish `h` using `cf_rename v σ P`. Rewrite `h` using `[hP σ]`. Unfold `cf at h ⊢`. Rewrite `h` using `[coeff_smul, zsmul_eq_mul]`. Rewrite using `[← h, ← mul_assoc, sign_mul_self, one_mul]`.
-/
theorem cf_perm {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m)) (v : Fin m → ℕ) :
    cf (v ∘ σ.symm) P = ((Perm.sign σ : ℤ) : ℚ) * cf v P := by
  have h := cf_rename v σ P
  rw [hP σ] at h
  unfold cf at h ⊢
  rw [coeff_smul, zsmul_eq_mul] at h
  rw [← h, ← mul_assoc, sign_mul_self, one_mul]

/- English proof (translation)
Establish `h1` using `cf_perm hP (Equiv.swap i j) v`. Establish `h2 : v ∘ (Equiv.swap i j).symm = v`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, Equiv.symm_swap]`. Break down `eq_or_ne k i with rfl | hki` into its components or cases.

Simplify using `[h]`. Break down `eq_or_ne k j with rfl | hkj` into its components or cases. Simplify using `[h]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hki hkj]`. Rewrite `h1` using `[h2, Perm.sign_swap hij]`.

Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cf_eq_zero_of_eq {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) {v : Fin m → ℕ} {i j : Fin m}
    (hij : i ≠ j) (h : v i = v j) : cf v P = 0 := by
  have h1 := cf_perm hP (Equiv.swap i j) v
  have h2 : v ∘ (Equiv.swap i j).symm = v := by
    funext k
    simp only [Function.comp_apply, Equiv.symm_swap]
    rcases eq_or_ne k i with rfl | hki
    · simp [h]
    rcases eq_or_ne k j with rfl | hkj
    · simp [h]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [h2, Perm.sign_swap hij] at h1
  simp at h1
  linarith

/- English proof (translation)
Unfold `alt`. Rewrite using `[Matrix.det_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]`. Conclude with `Fintype.prod_equiv σ _ _ (fun i => by simp)`.
-/
theorem alt_eq_sum (v : Fin m → ℕ) :
    alt v = ∑ σ : Perm (Fin m), (Perm.sign σ : ℤ) • monomial (ex (v ∘ σ.symm)) (1 : ℚ) := by
  unfold alt
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Matrix.of_apply]
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

/- English proof (translation)
Unfold `cf`. Rewrite using `[coeff_monomial]`. Distinguish the cases in `h : l = v`. Simplify using `[h]`. Rewrite using `[if_neg, if_neg h]`.

Introduce `h'`. Apply `h` to reduce the goal to its premises. Use `congrArg (fun d : Fin m →₀ ℕ => (d : Fin m → ℕ)) h'` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem cf_monomial (l v : Fin m → ℕ) :
    cf l (monomial (ex v) (1 : ℚ)) = if l = v then 1 else 0 := by
  unfold cf
  rw [coeff_monomial]
  by_cases h : l = v
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    apply h
    have := congrArg (fun d : Fin m →₀ ℕ => (d : Fin m → ℕ)) h'
    simpa using this.symm

/- English proof (translation)
The claim follows from `coeff_sum _ _ _`.
-/
theorem cf_sum {ι : Type*} (s : Finset ι) (v : Fin m → ℕ) (P : ι → MvPolynomial (Fin m) ℚ) :
    cf v (∑ i ∈ s, P i) = ∑ i ∈ s, cf v (P i) := coeff_sum _ _ _

/- English proof (translation)
Unfold `cf`. Rewrite using `[coeff_smul, zsmul_eq_mul]`.
-/
theorem cf_zsmul (v : Fin m → ℕ) (z : ℤ) (P : MvPolynomial (Fin m) ℚ) :
    cf v (z • P) = z * cf v P := by
  unfold cf; rw [coeff_smul, zsmul_eq_mul]

/- English proof (translation)
Rewrite using `[alt_eq_sum, cf_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[cf_zsmul, cf_monomial]`.
-/
theorem cf_alt (l v : Fin m → ℕ) :
    cf l (alt v) = ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) * if l = v ∘ σ.symm then 1 else 0 := by
  rw [alt_eq_sum, cf_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cf_zsmul, cf_monomial]

/- English proof (translation)
Establish `hmono : StrictMono σ`. Introduce `a b hab`. Use `h hab` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`. Conclude with `hv.lt_iff_gt.mp this`.

Establish `hmono' : StrictMono σ.symm`. Introduce `a b hab`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hmono.monotone hc` as an intermediate fact.

Simplify using `at this`. Conclude with `absurd hab (not_lt.mpr this)`. Use extensionality with `i`. Establish `h1 : i ≤ σ i` using `hmono.le_apply`. Establish `h2 : i ≤ σ.symm i` using `hmono'.le_apply`.

Establish `h3 : σ i ≤ σ (σ.symm i)` using `hmono.monotone h2`. Simplify using `only [Equiv.apply_symm_apply] at h3`. Simplify using `[le_antisymm h3 h1]`.
-/
theorem perm_eq_one_of_strictAnti {v : Fin m → ℕ} (hv : StrictAnti v) (σ : Perm (Fin m))
    (h : StrictAnti (v ∘ σ)) : σ = 1 := by
  have hmono : StrictMono σ := by
    intro a b hab
    have := h hab
    simp only [Function.comp_apply] at this
    exact hv.lt_iff_gt.mp this
  have hmono' : StrictMono σ.symm := by
    intro a b hab
    by_contra hc
    push Not at hc
    have := hmono.monotone hc
    simp at this
    exact absurd hab (not_lt.mpr this)
  ext i
  have h1 : i ≤ σ i := hmono.le_apply
  have h2 : i ≤ σ.symm i := hmono'.le_apply
  have h3 : σ i ≤ σ (σ.symm i) := hmono.monotone h2
  simp only [Equiv.apply_symm_apply] at h3
  simp [le_antisymm h3 h1]

/- English proof (translation)
Rewrite using `[cf_alt, Finset.sum_eq_single (1 : Perm (Fin m))]`. Establish `h1 : v ∘ ⇑(Equiv.symm (1 : Perm (Fin m))) = v` using `rfl`. Simplify using `[h1]`. Introduce `σ _ hσ`. Rewrite using `[if_neg, mul_zero]`.

Introduce `h`. Apply `hσ` to reduce the goal to its premises. Establish `: σ.symm = 1`. Apply `perm_eq_one_of_strictAnti hv` to reduce the goal to its premises. Rewrite using `[← h]`.

Conclude with `hl`. Rewrite using `[← Equiv.symm_symm σ, this]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem cf_alt_of_strictAnti {l v : Fin m → ℕ} (hl : StrictAnti l) (hv : StrictAnti v) :
    cf l (alt v) = if l = v then 1 else 0 := by
  rw [cf_alt, Finset.sum_eq_single (1 : Perm (Fin m))]
  · have h1 : v ∘ ⇑(Equiv.symm (1 : Perm (Fin m))) = v := rfl
    simp [h1]
  · intro σ _ hσ
    rw [if_neg, mul_zero]
    intro h
    apply hσ
    have : σ.symm = 1 := by
      apply perm_eq_one_of_strictAnti hv
      rw [← h]; exact hl
    rw [← Equiv.symm_symm σ, this]; rfl
  · simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det v`.
-/
theorem vandermondeOf_eq_det {R : Type*} [CommRing R] (v : Fin m → R) :
    vandermondeOf v = (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))).det :=
  _root_.UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det v

/- English proof (translation)
Rewrite using `[vandermondeOf_eq_det]`. Both sides reduce to the same expression.
-/
theorem vandermondeOf_X_eq_alt :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) = alt (stair m) := by
  rw [vandermondeOf_eq_det]; rfl

/- English proof (translation)
Unfold `psum`. Rewrite using `[Finset.mul_sum, cf_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `cf`. Rewrite using `[X_pow_eq_monomial, coeff_mul_monomial', mul_one]`.

Establish `hle : Finsupp.single i q ≤ ex l ↔ q ≤ l i`. Rewrite using `[Finsupp.single_le_iff]`. Simplify using the standard rewrite rules. Distinguish the cases in `h : q ≤ l i`. Rewrite using `[if_pos (hle.mpr h), if_pos h]`.

Use `congr 1`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne hj, Ne.symm hj]`. Rewrite using `[if_neg (fun h' => h (hle.mp h')), if_neg h]`.
-/
theorem cf_mul_psum (l : Fin m → ℕ) (A : MvPolynomial (Fin m) ℚ) (q : ℕ) :
    cf l (A * psum (Fin m) ℚ q) =
      ∑ i, if q ≤ l i then cf (Function.update l i (l i - q)) A else 0 := by
  unfold psum
  rw [Finset.mul_sum, cf_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cf
  rw [X_pow_eq_monomial, coeff_mul_monomial', mul_one]
  have hle : Finsupp.single i q ≤ ex l ↔ q ≤ l i := by
    rw [Finsupp.single_le_iff]; simp
  by_cases h : q ≤ l i
  · rw [if_pos (hle.mpr h), if_pos h]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, Ne.symm hj]
  · rw [if_neg (fun h' => h (hle.mp h')), if_neg h]

/- English proof (translation)
Introduce `σ`. Rewrite using `[map_mul, hP σ, hS σ, smul_mul_assoc]`.
-/
theorem IsAlt.mul_symm {P S : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (hS : S.IsSymmetric) :
    IsAlt (P * S) := by
  intro σ
  rw [map_mul, hP σ, hS σ, smul_mul_assoc]

/- English proof (translation)
Introduce `σ`. Rewrite using `[map_add, hP σ, hQ σ, smul_add]`.
-/
theorem IsAlt.add {P Q : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (hQ : IsAlt Q) : IsAlt (P + Q) := by
  intro σ; rw [map_add, hP σ, hQ σ, smul_add]

/- English proof (translation)
Introduce `σ`. Rewrite using `[map_sub, hP σ, hQ σ, smul_sub]`.
-/
theorem IsAlt.sub {P Q : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (hQ : IsAlt Q) : IsAlt (P - Q) := by
  intro σ; rw [map_sub, hP σ, hQ σ, smul_sub]

/- English proof (translation)
Introduce `σ`. Rewrite using `[map_smul, hP σ, smul_comm]`.
-/
theorem IsAlt.smul {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (c : ℚ) : IsAlt (c • P) := by
  intro σ; rw [map_smul, hP σ, smul_comm]

/- English proof (translation)
Introduce `σ`. Simplify using the standard rewrite rules.
-/
theorem IsAlt.zero : IsAlt (0 : MvPolynomial (Fin m) ℚ) := by intro σ; simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using IsAlt.zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(hP a (mem_insert_self a s)).add (ih fun i hi => hP i (mem_insert_of_mem hi))`.
-/
theorem IsAlt.sum {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Fin m) ℚ}
    (hP : ∀ i ∈ s, IsAlt (P i)) : IsAlt (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsAlt.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hP a (mem_insert_self a s)).add (ih fun i hi => hP i (mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `ρ with`. Consider the case `nil => simp only [List.map_nil, List.prod_nil]`. Conclude with `IsSymmetric.one`. Consider the case `cons q ρ ih => simpa using (psum_isSymmetric (Fin m) ℚ q).mul ih`.
-/
theorem isSymmetric_prod_psum (ρ : List ℕ) :
    ((ρ.map fun q => psum (Fin m) ℚ q).prod).IsSymmetric := by
  induction ρ with
  | nil => simp only [List.map_nil, List.prod_nil]; exact IsSymmetric.one
  | cons q ρ ih => simpa using (psum_isSymmetric (Fin m) ℚ q).mul ih

/- English proof (translation)
Rewrite using `[vandermondeOf_X_eq_alt]`. Conclude with `(alt_isAlt _).mul_symm (isSymmetric_prod_psum ρ)`.
-/
theorem isAlt_vandermonde_mul_prod (ρ : List ℕ) :
    IsAlt (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
      (ρ.map fun q => psum (Fin m) ℚ q).prod) := by
  rw [vandermondeOf_X_eq_alt]
  exact (alt_isAlt _).mul_symm (isSymmetric_prod_psum ρ)

/- English proof (translation)
Establish `hmono : StrictMono (u ∘ Tuple.sort u)` using `(Tuple.monotone_sort u).strictMono_of_injective (hu.comp (Tuple.sort u).injective)`. Use `⟨Fin.revPerm.trans (Tuple.sort u), fun a b hab => ?_⟩` and prove the remaining obligations. Use `hmono (Fin.rev_lt_rev.mpr hab)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_perm_strictAnti {u : Fin m → ℕ} (hu : Function.Injective u) :
    ∃ σ : Perm (Fin m), StrictAnti (u ∘ σ) := by
  have hmono : StrictMono (u ∘ Tuple.sort u) :=
    (Tuple.monotone_sort u).strictMono_of_injective (hu.comp (Tuple.sort u).injective)
  refine ⟨Fin.revPerm.trans (Tuple.sort u), fun a b hab => ?_⟩
  have := hmono (Fin.rev_lt_rev.mpr hab)
  simpa using this

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_zero]`. Establish `hd : coeff d P = cf (⇑d) P` using `by unfold cf; simp`. Rewrite using `[hd]`. Distinguish the cases in `hinj : Function.Injective (⇑d)`.

Take `⟨σ, hσ⟩` from `exists_perm_strictAnti hinj`. Establish `h1` using `cf_perm hP σ (⇑d ∘ σ)`. Establish `h2 : (⇑d ∘ σ) ∘ σ.symm = ⇑d` using `by funext i; simp`. Rewrite `h1` using `[h2, h _ hσ, mul_zero]`. Conclude with `h1`.

Simplify using `only [Function.Injective, not_forall] at hinj`. Take `⟨i, j, hij, hne⟩` from `hinj`. Conclude with `cf_eq_zero_of_eq hP hne hij`.
-/
theorem IsAlt.eq_zero_of_cf {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P)
    (h : ∀ l : Fin m → ℕ, StrictAnti l → cf l P = 0) : P = 0 := by
  ext d
  rw [coeff_zero]
  have hd : coeff d P = cf (⇑d) P := by unfold cf; simp
  rw [hd]
  by_cases hinj : Function.Injective (⇑d)
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
    have h1 := cf_perm hP σ (⇑d ∘ σ)
    have h2 : (⇑d ∘ σ) ∘ σ.symm = ⇑d := by funext i; simp
    rw [h2, h _ hσ, mul_zero] at h1
    exact h1
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact cf_eq_zero_of_eq hP hne hij

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `(hP.sub (IsAlt.sum _ fun d _ => (alt_isAlt _).smul _)).eq_zero_of_cf fun l hl => ?_` and prove the remaining obligations. Unfold `cf`. Rewrite using `[coeff_sub, coeff_sum, sub_eq_zero]`. Establish `hterm : ∀ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)), coeff (ex l) (coeff d P • alt (⇑d)) = if d = ex l then coeff d P else 0`.

Introduce `d hd`. Rewrite `hd` using `[Finset.mem_filter]`. Use `cf_alt_of_strictAnti hl hd.2` as an intermediate fact. Unfold `cf at this`. Rewrite using `[coeff_smul, this, smul_eq_mul]`.

Distinguish the cases in `hdl : d = ex l`. Substitute `hdl` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg, if_neg hdl, mul_zero]`. Introduce `h`.

Apply `hdl` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `[h]`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_ite_eq']`. Use `split_ifs with hmem`.

Both sides reduce to the same expression. Rewrite `hmem` using `[Finset.mem_filter, not_and]`. Assume the negation of the conclusion as `hne`. Conclude with `hmem (mem_support_iff.mpr hne) (by simpa using hl)`.
-/
theorem IsAlt.eq_sum_alt {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) :
    P = ∑ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)), coeff d P • alt (⇑d) := by
  rw [← sub_eq_zero]
  refine (hP.sub (IsAlt.sum _ fun d _ => (alt_isAlt _).smul _)).eq_zero_of_cf fun l hl => ?_
  unfold cf
  rw [coeff_sub, coeff_sum, sub_eq_zero]
  have hterm : ∀ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)),
      coeff (ex l) (coeff d P • alt (⇑d)) = if d = ex l then coeff d P else 0 := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have := cf_alt_of_strictAnti hl hd.2
    unfold cf at this
    rw [coeff_smul, this, smul_eq_mul]
    by_cases hdl : d = ex l
    · subst hdl; simp
    · rw [if_neg, if_neg hdl, mul_zero]
      intro h; apply hdl; ext i; simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finset.mem_filter, not_and] at hmem
    by_contra hne
    exact hmem (mem_support_iff.mpr hne) (by simpa using hl)

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
