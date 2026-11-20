import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.ProductIdentities

noncomputable section

set_option linter.unusedSectionVars false

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace PositivityTheory.Rg.Cz.J

section DetDeriv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
The claim follows from `_root_.Bl.ProductIdentities.goal1 A A' h0 h`.
-/
theorem hasDerivAt_det_one (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 :=
  _root_.Bl.ProductIdentities.goal1 A A' h0 h

end DetDeriv

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Apply the tactic sequence `unfold coord; split_ifs <;> simp`.
-/
theorem coord_star' (τ : E →+* ℂ) (x : Cinf E) : coord τ (star x) = starRingEnd ℂ (coord τ x) := by
  unfold coord; split_ifs <;> simp

/- English proof (translation)
The claim follows from `Subalgebra.mul_mem _ hf hg`.
-/
theorem regFun_mul' {f g : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (hg : g ∈ regFun E a) :
    (fun y => f y * g y) ∈ regFun E a := Subalgebra.mul_mem _ hf hg

/- English proof (translation)
Establish `e : (fun y => ∏ i ∈ u, f i y) = ∏ i ∈ u, f i` using `by funext y; simp [Finset.prod_apply]`. Rewrite using `[e]`. Conclude with `Subalgebra.prod_mem _ h`.
-/
theorem regFun_prod' {ι : Type} (u : Finset ι) (f : ι → GL (Fin a) (Cinf E) → ℂ) (h : ∀ i ∈ u, f i ∈ regFun E a) :
    (fun y => ∏ i ∈ u, f i y) ∈ regFun E a := by
  have e : (fun y => ∏ i ∈ u, f i y) = ∏ i ∈ u, f i := by funext y; simp [Finset.prod_apply]
  rw [e]; exact Subalgebra.prod_mem _ h

/- English proof (translation)
Establish `e : (fun y => ∑ i ∈ u, f i y) = ∑ i ∈ u, f i` using `by funext y; simp [Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `Subalgebra.sum_mem _ h`.
-/
theorem regFun_sum' {ι : Type} (u : Finset ι) (f : ι → GL (Fin a) (Cinf E) → ℂ) (h : ∀ i ∈ u, f i ∈ regFun E a) :
    (fun y => ∑ i ∈ u, f i y) ∈ regFun E a := by
  have e : (fun y => ∑ i ∈ u, f i y) = ∑ i ∈ u, f i := by funext y; simp [Finset.sum_apply]
  rw [e]; exact Subalgebra.sum_mem _ h

/- English proof (translation)
The claim follows from `Subalgebra.smul_mem _ hf c`.
-/
theorem regFun_cmul' (c : ℂ) {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    (fun y => c * f y) ∈ regFun E a := Subalgebra.smul_mem _ hf c

/- English proof (translation)
Establish `e : (fun y => f y ^ n) = f ^ n` using `by funext y; simp`. Rewrite using `[e]`. Conclude with `Subalgebra.pow_mem _ hf n`.
-/
theorem regFun_pow' {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (n : ℕ) :
    (fun y => f y ^ n) ∈ regFun E a := by
  have e : (fun y => f y ^ n) = f ^ n := by funext y; simp
  rw [e]; exact Subalgebra.pow_mem _ hf n

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin (Or.inl ⟨τ, i, j, rfl⟩)`.
-/
theorem regFun_entry (τ : E →+* ℂ) (i j : Fin a) : (fun y : GL (Fin a) (Cinf E) => coord τ (y.val i j)) ∈ regFun E a :=
  Algebra.subset_adjoin (Or.inl ⟨τ, i, j, rfl⟩)

/- English proof (translation)
Establish `e : (fun y : GL (Fin a) (Cinf E) => coord τ y.val.det) = fun y => ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, coord τ (y.val (σ i) i)`. Use function extensionality and compare the values at `y`. Rewrite using `[RingHom.map_det, Matrix.det_apply']`. Both sides reduce to the same expression. Rewrite using `[e]`.

Apply the tactic sequence `exact regFun_sum' _ _ fun σ _ => regFun_cmul' _ (regFun_prod' _ _ fun i _ => regFun_entry τ (σ i) i)`.
-/
theorem regFun_det (τ : E →+* ℂ) : (fun y : GL (Fin a) (Cinf E) => coord τ y.val.det) ∈ regFun E a := by
  have e : (fun y : GL (Fin a) (Cinf E) => coord τ y.val.det) =
      fun y => ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, coord τ (y.val (σ i) i) := by
    funext y; rw [RingHom.map_det, Matrix.det_apply']; rfl
  rw [e]
  exact regFun_sum' _ _ fun σ _ => regFun_cmul' _ (regFun_prod' _ _ fun i _ => regFun_entry τ (σ i) i)

/- English proof (translation)
Break down `Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩` into its components or cases. Simplify using `only [zpow_natCast]`. Conclude with `regFun_pow' (regFun_prod' _ _ fun τ _ => regFun_det τ) m`. Establish `e : (fun y : GL (Fin a) (Cinf E) => (∏ τ : E →+* ℂ, coord τ y.val.det) ^ (-(m : ℤ))) = fun y => (∏ τ : E →+* ℂ, (coord τ y.val.det)⁻¹) ^ m`. Use function extensionality and compare the values at `y`.

Rewrite using `[_root_.zpow_neg, zpow_natCast, Finset.prod_inv_distrib, inv_pow]`. Rewrite using `[e]`. Conclude with `regFun_pow' (regFun_prod' _ _ fun τ _ => Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)) m`.
-/
theorem regFun_zpow (n : ℤ) :
    (fun y : GL (Fin a) (Cinf E) => (∏ τ : E →+* ℂ, coord τ y.val.det) ^ n) ∈ regFun E a := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp only [zpow_natCast]
    exact regFun_pow' (regFun_prod' _ _ fun τ _ => regFun_det τ) m
  · have e : (fun y : GL (Fin a) (Cinf E) => (∏ τ : E →+* ℂ, coord τ y.val.det) ^ (-(m : ℤ))) =
        fun y => (∏ τ : E →+* ℂ, (coord τ y.val.det)⁻¹) ^ m := by
      funext y; rw [_root_.zpow_neg, zpow_natCast, Finset.prod_inv_distrib, inv_pow]
    rw [e]
    exact regFun_pow' (regFun_prod' _ _ fun τ _ => Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)) m

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/- English proof (translation)
The claim follows from `regFun_mul' (regFun_zpow (-s)) (regFun_prod' _ _ fun p _ => regFun_entry (lab p) (I p) (J p))`.
-/
theorem bigM_reg (lab : Q → (E →+* ℂ)) (s : ℤ) (I J : Q → Fin a) :
    (fun y => bigM lab s y I J) ∈ regFun E a :=
  regFun_mul' (regFun_zpow (-s)) (regFun_prod' _ _ fun p _ => regFun_entry (lab p) (I p) (J p))

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Take `⟨p, hp⟩` from `Function.ne_iff.1 h`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ p) (by rw [Matrix.one_apply_ne hp, map_zero])`.
-/
theorem prod_one (lab : Q → (E →+* ℂ)) (I J : Q → Fin a) :
    ∏ p, coord (lab p) ((1 : Matrix (Fin a) (Fin a) (Cinf E)) (I p) (J p)) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨p, hp⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by rw [Matrix.one_apply_ne hp, map_zero])

/- English proof (translation)
Use `split_ifs with h`. Conclude with `Finset.prod_eq_one fun q hq => by`. Rewrite using `[h q (Finset.ne_of_mem_erase hq), Matrix.one_apply_eq, map_one]`. Simplify using `only [not_forall, exists_prop] at h`. Take `⟨r, hr, hIJ⟩` from `h`.

Conclude with `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hr, Finset.mem_univ r⟩) (by rw [Matrix.one_apply_ne hIJ, map_zero])`.
-/
theorem prod_erase_one (lab : Q → (E →+* ℂ)) (I J : Q → Fin a) (p : Q) :
    ∏ q ∈ Finset.univ.erase p, coord (lab q) ((1 : Matrix (Fin a) (Fin a) (Cinf E)) (I q) (J q)) =
      if (∀ r, r ≠ p → I r = J r) then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun q hq => by
      rw [h q (Finset.ne_of_mem_erase hq), Matrix.one_apply_eq, map_one]
  · simp only [not_forall, exists_prop] at h
    obtain ⟨r, hr, hIJ⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hr, Finset.mem_univ r⟩)
      (by rw [Matrix.one_apply_ne hIJ, map_zero])

/- English proof (translation)
Use extensionality with `I J`. Simplify using `only [bigM, Matrix.of_apply, Units.val_one, Matrix.det_one, map_one, Finset.prod_const_one, _root_.one_zpow, one_mul]`. Rewrite using `[prod_one, Matrix.one_apply]`.
-/
theorem bigM_one (lab : Q → (E →+* ℂ)) (s : ℤ) : bigM (a := a) lab s 1 = 1 := by
  ext I J
  simp only [bigM, Matrix.of_apply, Units.val_one, Matrix.det_one, map_one, Finset.prod_const_one, _root_.one_zpow, one_mul]
  rw [prod_one, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `I J`. Simplify using `only [bigM, Matrix.of_apply, Matrix.mul_apply, Units.val_mul, Matrix.det_mul, map_mul, Finset.prod_mul_distrib, mul_zpow, map_sum]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun K _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bigM_mul (lab : Q → (E →+* ℂ)) (s : ℤ) (y z : GL (Fin a) (Cinf E)) :
    bigM lab s (y * z) = bigM lab s y * bigM lab s z := by
  ext I J
  simp only [bigM, Matrix.of_apply, Matrix.mul_apply, Units.val_mul, Matrix.det_mul, map_mul,
    Finset.prod_mul_distrib, mul_zpow, map_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.prod_mul_distrib]; ring

/- English proof (translation)
Establish `hv : (star y).val = (y.val)ᴴ` using `rfl`. Establish `hs : ∀ z : ℂ, star z = starRingEnd ℂ z` using `fun _ => rfl`. Use extensionality with `I J`. Simplify using `only [bigM, Matrix.of_apply, Matrix.conjTranspose_apply, hv, Matrix.det_conjTranspose, coord_star']`. Rewrite using `[hs, map_mul, map_zpow₀, map_prod, map_prod]`.
-/
theorem bigM_star (lab : Q → (E →+* ℂ)) (s : ℤ) (y : GL (Fin a) (Cinf E)) :
    bigM lab s (star y) = (bigM lab s y)ᴴ := by
  have hv : (star y).val = (y.val)ᴴ := rfl
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  ext I J
  simp only [bigM, Matrix.of_apply, Matrix.conjTranspose_apply, hv, Matrix.det_conjTranspose, coord_star']
  rw [hs, map_mul, map_zpow₀, map_prod, map_prod]

/- English proof (translation)
Establish `he : ∀ i j, HasDerivAt (fun t => (c t).val i j) (X i j) 0` using `fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc i) j`. Establish `hco : ∀ (τ : E →+* ℂ) i j, HasDerivAt (fun t => coord τ ((c t).val i j)) (coord τ (X i j)) 0` using `fun τ i j => (coordL τ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (he i j)`. Establish `hdet : ∀ τ : E →+* ℂ, HasDerivAt (fun t => coord τ (c t).val.det) (∑ i, coord τ (X i i)) 0` using `fun τ => by`. Establish `h2` using `hasDerivAt_det_one (fun t => (c t).val.map (coord τ)) ((Matrix.of X).map (coord τ)) (by rw [h0]; simp) (fun i j => hco τ i j)`. Establish `e : (fun t => coord τ (c t).val.det) = fun t => ((c t).val.map (coord τ)).det`.

Use function extensionality and compare the values at `fun t => RingHom.map_det _ _`. Rewrite using `[e]`. Conclude with `h2.congr_deriv (by simp [Matrix.trace])`. Establish `hD : HasDerivAt (fun t => ∏ τ : E →+* ℂ, coord τ (c t).val.det) (∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) 0`. Establish `h2` using `HasDerivAt.fun_finsetProd (u := Finset.univ) (fun τ _ => hdet τ)`.

Use `h2.congr_deriv (Finset.sum_congr rfl fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_one (fun j _ => by rw [h0]; simp), one_smul]`. Establish `h1 : (∏ τ : E →+* ℂ, coord τ (c 0).val.det) = 1` using `by rw [h0]; simp`. Establish `hZ : HasDerivAt (fun t => (∏ τ : E →+* ℂ, coord τ (c t).val.det) ^ (-s)) (((-s : ℤ) : ℂ) * ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) 0`. Establish `hz` using `hasDerivAt_zpow (-s) (∏ τ : E →+* ℂ, coord τ (c 0).val.det) (Or.inl (by rw [h1]; exact one_ne_zero))`.

Establish `h2` using `hz.comp (0 : ℝ) hD`. Conclude with `h2.congr_deriv (by rw [h1]; simp)`. Establish `hP : HasDerivAt (fun t => ∏ p, coord (lab p) ((c t).val (I p) (J p))) (∑ p, (∏ q ∈ Finset.univ.erase p, coord (lab q) ((c 0).val (I q) (J q))) • coord (lab p) (X (I p) (J p))) 0` using `HasDerivAt.fun_finsetProd (fun p _ => hco (lab p) (I p) (J p))`. Establish `key : HasDerivAt (fun t => bigM lab s (c t) I J) _ 0` using `hZ.mul hP`. Use `key.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [bigD, Matrix.of_apply, h0, Units.val_one, prod_erase_one, prod_one, Matrix.det_one, map_one, Finset.prod_const_one, _root_.one_zpow, one_mul]`. Apply the tactic sequence `have e2 : ∀ p, ((if (∀ r, r ≠ p → I r = J r) then (1 : ℂ) else 0) • coord (lab p) (X (I p) (J p))) = if (∀ r, r ≠ p → I r = J r) then coord (lab p) (X (I p) (J p)) else 0 := fun p => by split_ifs <;> simp`. Simplify using `only [e2]`. Distinguish the cases in `hIJ : I = J`. Simplify using `only [if_pos hIJ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg hIJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bigM_der (lab : Q → (E →+* ℂ)) (s : ℤ) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) (I J : Q → Fin a) :
    HasDerivAt (fun t => bigM lab s (c t) I J) (bigD lab s X I J) 0 := by
  classical
  have he : ∀ i j, HasDerivAt (fun t => (c t).val i j) (X i j) 0 := fun i j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hc i) j
  have hco : ∀ (τ : E →+* ℂ) i j, HasDerivAt (fun t => coord τ ((c t).val i j)) (coord τ (X i j)) 0 :=
    fun τ i j => (coordL τ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (he i j)
  have hdet : ∀ τ : E →+* ℂ, HasDerivAt (fun t => coord τ (c t).val.det) (∑ i, coord τ (X i i)) 0 := fun τ => by
    have h2 := hasDerivAt_det_one (fun t => (c t).val.map (coord τ)) ((Matrix.of X).map (coord τ))
      (by rw [h0]; simp) (fun i j => hco τ i j)
    have e : (fun t => coord τ (c t).val.det) = fun t => ((c t).val.map (coord τ)).det :=
      funext fun t => RingHom.map_det _ _
    rw [e]
    exact h2.congr_deriv (by simp [Matrix.trace])
  have hD : HasDerivAt (fun t => ∏ τ : E →+* ℂ, coord τ (c t).val.det)
      (∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) 0 := by
    have h2 := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun τ _ => hdet τ)
    refine h2.congr_deriv (Finset.sum_congr rfl fun τ _ => ?_)
    rw [Finset.prod_eq_one (fun j _ => by rw [h0]; simp), one_smul]
  have h1 : (∏ τ : E →+* ℂ, coord τ (c 0).val.det) = 1 := by rw [h0]; simp
  have hZ : HasDerivAt (fun t => (∏ τ : E →+* ℂ, coord τ (c t).val.det) ^ (-s))
      (((-s : ℤ) : ℂ) * ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) 0 := by
    have hz := hasDerivAt_zpow (-s) (∏ τ : E →+* ℂ, coord τ (c 0).val.det) (Or.inl (by rw [h1]; exact one_ne_zero))
    have h2 := hz.comp (0 : ℝ) hD
    exact h2.congr_deriv (by rw [h1]; simp)
  have hP : HasDerivAt (fun t => ∏ p, coord (lab p) ((c t).val (I p) (J p)))
      (∑ p, (∏ q ∈ Finset.univ.erase p, coord (lab q) ((c 0).val (I q) (J q))) • coord (lab p) (X (I p) (J p))) 0 :=
    HasDerivAt.fun_finsetProd (fun p _ => hco (lab p) (I p) (J p))
  have key : HasDerivAt (fun t => bigM lab s (c t) I J) _ 0 := hZ.mul hP
  refine key.congr_deriv ?_
  simp only [bigD, Matrix.of_apply, h0, Units.val_one, prod_erase_one, prod_one, Matrix.det_one, map_one,
    Finset.prod_const_one, _root_.one_zpow, one_mul]
  have e2 : ∀ p, ((if (∀ r, r ≠ p → I r = J r) then (1 : ℂ) else 0) • coord (lab p) (X (I p) (J p))) =
      if (∀ r, r ≠ p → I r = J r) then coord (lab p) (X (I p) (J p)) else 0 := fun p => by
    split_ifs <;> simp
  simp only [e2]
  by_cases hIJ : I = J
  · simp only [if_pos hIJ]; push_cast; ring
  · simp only [if_neg hIJ]; ring

/- English proof (translation)
Establish `hs : ∀ z : ℂ, star z = starRingEnd ℂ z` using `fun _ => rfl`. Use extensionality with `I J`. Simplify using `only [bigD, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.of_symm_apply, Matrix.star_apply, coord_star']`. Rewrite using `[hs, map_sub, map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∀ r, r ≠ p → I r = J r`. Establish `h' : ∀ r, r ≠ p → J r = I r` using `fun r hr => (h r hr).symm`. Rewrite using `[if_pos h, if_pos h']`. Establish `h' : ¬ ∀ r, r ≠ p → J r = I r` using `fun h' => h fun r hr => (h' r hr).symm`.

Rewrite using `[if_neg h, if_neg h', map_zero]`. Distinguish the cases in `h : I = J`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Simplify using `[map_sum]`.

Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero]`.
-/
theorem bigD_star (lab : Q → (E →+* ℂ)) (s : ℤ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    bigD lab s (toL (star X)) = (bigD lab s (toL X))ᴴ := by
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  ext I J
  simp only [bigD, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.of_symm_apply, Matrix.star_apply, coord_star']
  rw [hs, map_sub, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : ∀ r, r ≠ p → I r = J r
    · have h' : ∀ r, r ≠ p → J r = I r := fun r hr => (h r hr).symm
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ r, r ≠ p → J r = I r := fun h' => h fun r hr => (h' r hr).symm
      rw [if_neg h, if_neg h', map_zero]
  · by_cases h : I = J
    · subst h; rw [if_pos rfl, if_pos rfl]; simp [map_sum]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]

end

/- English proof (translation)
Introduce `E _ _ _ a Q _ _ lab s`. Conclude with `{ one := bigM_one lab s mul := bigM_mul lab s reg := bigM_reg lab s star := bigM_star lab s der := fun c X h0 hc I J => bigM_der lab s c X h0 hc I J dstar := bigD_star lab s }`.
-/
theorem bigRep_holds : BigRep := by
  intro E _ _ _ a Q _ _ lab s
  exact
    { one := bigM_one lab s
      mul := bigM_mul lab s
      reg := bigM_reg lab s
      star := bigM_star lab s
      der := fun c X h0 hc I J => bigM_der lab s c X h0 hc I J
      dstar := bigD_star lab s }

end PositivityTheory.Rg.Cz.J

end
