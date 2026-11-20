import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Blocks

variable {n : Type*} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun := slice a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
The claim follows from `(LinearMap.toContinuousLinearMap (sliceL (n := n) a)).analyticAt z`.
-/
theorem slice_analyticAt (a : Fin 4) (z : Fin 4 × n → ℂ) :
    AnalyticAt ℂ (slice a : (Fin 4 × n → ℂ) → n → ℂ) z :=
  (LinearMap.toContinuousLinearMap (sliceL (n := n) a)).analyticAt z

def mk4 (u : Fin 4 → n → ℂ) : Fin 4 × n → ℂ := fun p => u p.1 p.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockSlice_fourfoldMk (u : Fin 4 → n → ℂ) (a : Fin 4) : slice a (mk4 u) = u a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem slice_add (a : Fin 4) (z w : Fin 4 × n → ℂ) : slice a (z + w) = slice a z + slice a w := rfl

def emb0 : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun v := fun p => if p.1 = 0 then v p.2 else 0
  map_add' u v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]
  map_smul' c v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases ha : a = 0 <;> simp [slice, emb0, ha]`.
-/
theorem blockSlice_firstBlockEmb (a : Fin 4) (v : n → ℂ) : slice a (emb0 v) = if a = 0 then v else 0 := by
  funext i
  by_cases ha : a = 0 <;> simp [slice, emb0, ha]

/- English proof (translation)
Introduce `a`. Rewrite using `[blockSlice_firstBlockEmb]`. Use `split_ifs`. Conclude with `hx`. Conclude with `Λ.zero_mem`.
-/
theorem firstBlockEmb_mem_fourfoldLattice (Λ : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ Λ) : emb0 x ∈ pow4 Λ := by
  intro a
  rw [blockSlice_firstBlockEmb]
  split_ifs
  · exact hx
  · exact Λ.zero_mem

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single (0 : Fin 4)]`. Rewrite using `[blockSlice_firstBlockEmb, if_pos rfl]`. Introduce `a _ ha`. Rewrite using `[blockSlice_firstBlockEmb, if_neg ha, hα0]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem prod_blockSlice_firstBlockEmb (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1) (x : n → ℂ) :
    ∏ a, α (slice a (emb0 x)) = α x := by
  rw [Finset.prod_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, hα0]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[matrixForm_fourfoldBlock, Finset.sum_eq_single (0 : Fin 4)]`. Rewrite using `[blockSlice_firstBlockEmb, if_pos rfl]`. Introduce `a _ ha`. Rewrite using `[blockSlice_firstBlockEmb, if_neg ha, map_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem matrixForm_fourfoldBlock_firstBlockEmb (h : Matrix n n ℂ) (z : Fin 4 × n → ℂ) (x : n → ℂ) :
    matH (blk4 h) z (emb0 x) = matH h (slice 0 z) x := by
  rw [matrixForm_fourfoldBlock, Finset.sum_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem fourfoldTensor_smul (c : ℂ) (θ : (n → ℂ) → ℂ) : tens4 (c • θ) = c ^ 4 • tens4 θ := by
  funext z
  simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `v _`. Conclude with `(hP.1 (z₁ + emb0 v) (Set.mem_univ _)).comp_of_eq (analyticAt_const.add ((LinearMap.toContinuousLinearMap (emb0 (n := n))).analyticAt v)) rfl`. Introduce `x hx v`. Establish `h1` using `hP.2 (emb0 x) (firstBlockEmb_mem_fourfoldLattice Λ hx) (z₁ + emb0 v)`.

Simplify using `only [opU, prod_blockSlice_firstBlockEmb α hα0, matrixForm_fourfoldBlock_firstBlockEmb, slice_add, hz₁, zero_add] at h1 ⊢`. Rewrite `h1` using `[blockSlice_firstBlockEmb, if_pos rfl, blockSlice_firstBlockEmb, if_pos rfl, add_assoc, ← map_add]`. Conclude with `h1`.
-/
theorem restrict_mem (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ}
    (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z₁ : Fin 4 × n → ℂ) (hz₁ : slice 0 z₁ = 0) :
    (fun v => P (z₁ + emb0 v)) ∈ Th (matH h) α Λ := by
  refine ⟨?_, ?_⟩
  · intro v _
    exact (hP.1 (z₁ + emb0 v) (Set.mem_univ _)).comp_of_eq
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (emb0 (n := n))).analyticAt v)) rfl
  · intro x hx v
    have h1 := hP.2 (emb0 x) (firstBlockEmb_mem_fourfoldLattice Λ hx) (z₁ + emb0 v)
    simp only [opU, prod_blockSlice_firstBlockEmb α hα0, matrixForm_fourfoldBlock_firstBlockEmb, slice_add, hz₁, zero_add] at h1 ⊢
    rw [blockSlice_firstBlockEmb, if_pos rfl, blockSlice_firstBlockEmb, if_pos rfl, add_assoc, ← map_add] at h1
    exact h1

end Blocks

/- English proof (translation)
Introduce `n _ h Λ α θ hθ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `z _`. Use `Finset.analyticAt_fun_prod _ fun a _ => ?_` and prove the remaining obligations. Conclude with `((hθ a).1 (slice a z) (Set.mem_univ _)).comp_of_eq (slice_analyticAt a z) rfl`.

Introduce `x hx z`. Rewrite using `[(heisenbergFourfold n h).2 x θ z]`. Use `show (∏ a, α (slice a x)) * _ = ∏ a, θ a (slice a z)`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun a _ => (hθ a).2 (slice a x) (hx a) (slice a z)`.
-/
theorem fourfoldTensorMem : Tens4Mem := by
  intro n _ h Λ α θ hθ
  refine ⟨?_, ?_⟩
  · intro z _
    refine Finset.analyticAt_fun_prod _ fun a _ => ?_
    exact ((hθ a).1 (slice a z) (Set.mem_univ _)).comp_of_eq (slice_analyticAt a z) rfl
  · intro x hx z
    rw [(heisenbergFourfold n h).2 x θ z]
    show (∏ a, α (slice a x)) * _ = ∏ a, θ a (slice a z)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hθ a).2 (slice a x) (hx a) (slice a z)

/- English proof (translation)
Introduce `n _ h Λ α hα0 P hP hP0 hline`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, P z ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hP0 (funext hcon)`.

Establish `key_line : ∀ θ ∈ Th (matH h) α Λ, tens4 θ = P → ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ`. Introduce `θ hθ hθP F hF`. Establish `hw : θ (slice 0 z) ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises.

Rewrite using `[← hθP]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) h0`. Apply the tactic sequence `obtain ⟨c, hc⟩ := hline _ (h4 n h Λ α (fun a => if a = 0 then F else θ) (by intro a; split_ifs <;> assumption))`. Use `⟨c, funext fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun hc (mk4 (fun a => if a = 0 then v else slice 0 z))`.

Rewrite `h1` using `[← hθP]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, tens4, Fin.prod_univ_four, blockSlice_fourfoldMk] at h1`. Simplify using `only [if_true, Fin.isValue, one_ne_zero, if_false, Fin.reduceEq] at h1`. Establish `h3 : θ (slice 0 z) * θ (slice 0 z) * θ (slice 0 z) ≠ 0` using `mul_ne_zero (mul_ne_zero hw hw) hw`. Apply `mul_right_cancel₀ h3` to reduce the goal to its premises.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Take the linear combination `h1`. Use `⟨?_, fun θ hθ hθP => ⟨?_, key_line θ hθ hθP⟩⟩` and prove the remaining obligations. Use `set z₁ : Fin 4 × n → ℂ := fun p => if p.1 = 0 then 0 else z p with hz₁def`. Establish `hz₁ : slice 0 z₁ = 0`.

Use function extensionality and compare the values at `i`. Simplify using `[slice, hz₁def]`. Establish `hzz : z₁ + emb0 (slice 0 z) = z`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.1 = 0`.

Establish `: p = (0, p.2)` using `Prod.ext hp rfl`. Simplify using `only [Pi.add_apply, hz₁def, emb0, LinearMap.coe_mk, AddHom.coe_mk, hp, if_true, slice, zero_add]`. Rewrite using `[← this]`. Simplify using `[hz₁def, emb0, hp]`. Establish `hθ₁` using `restrict_mem h Λ α hα0 hP z₁ hz₁`.

Use `set θ₁ : (n → ℂ) → ℂ := fun v => P (z₁ + emb0 v) with hθ₁def`. Take `⟨c, hc⟩` from `hline _ (h4 n h Λ α (fun _ => θ₁) (fun _ => hθ₁))`. Establish `hc' : tens4 θ₁ = c • P` using `hc`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Establish `h1` using `congrFun hc' (mk4 fun _ => slice 0 z)`. Simplify using `only [tens4, blockSlice_fourfoldMk, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_smul, Pi.zero_apply, hθ₁def, hzz] at h1`. Conclude with `hz (pow_eq_zero_iff (by norm_num) |>.1 h1)`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_pow_nat_eq (c⁻¹) (n := 4) (by norm_num)`. Use `⟨r • θ₁, (Th (matH h) α Λ).smul_mem r hθ₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[fourfoldTensor_smul, hr, hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Introduce `θ' hθ' hθ'P`. Take `⟨c, rfl⟩` from `key_line θ hθ hθP θ' hθ'`. Use `⟨c, ?_, rfl⟩` and prove the remaining obligations. Rewrite `hθ'P` using `[fourfoldTensor_smul, hθP]`.

Establish `h1` using `congrFun hθ'P z`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h1`. Conclude with `mul_right_cancel₀ hz (by rw [h1, one_mul])`.
-/
theorem FourthRoot_of (h4 : Tens4Mem) : FourthRoot := by
  intro n _ h Λ α hα0 P hP hP0 hline
  obtain ⟨z, hz⟩ : ∃ z, P z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP0 (funext hcon)
  have key_line : ∀ θ ∈ Th (matH h) α Λ, tens4 θ = P → ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ := by
    intro θ hθ hθP F hF
    have hw : θ (slice 0 z) ≠ 0 := by
      intro h0
      apply hz
      rw [← hθP]
      exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) h0
    obtain ⟨c, hc⟩ := hline _ (h4 n h Λ α (fun a => if a = 0 then F else θ)
      (by intro a; split_ifs <;> assumption))
    refine ⟨c, funext fun v => ?_⟩
    have h1 := congrFun hc (mk4 (fun a => if a = 0 then v else slice 0 z))
    rw [← hθP] at h1
    simp only [Pi.smul_apply, smul_eq_mul, tens4, Fin.prod_univ_four, blockSlice_fourfoldMk] at h1
    simp only [if_true, Fin.isValue, one_ne_zero, if_false, Fin.reduceEq] at h1
    have h3 : θ (slice 0 z) * θ (slice 0 z) * θ (slice 0 z) ≠ 0 := mul_ne_zero (mul_ne_zero hw hw) hw
    apply mul_right_cancel₀ h3
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination h1
  refine ⟨?_, fun θ hθ hθP => ⟨?_, key_line θ hθ hθP⟩⟩
  · set z₁ : Fin 4 × n → ℂ := fun p => if p.1 = 0 then 0 else z p with hz₁def
    have hz₁ : slice 0 z₁ = 0 := by
      funext i
      simp [slice, hz₁def]
    have hzz : z₁ + emb0 (slice 0 z) = z := by
      funext p
      by_cases hp : p.1 = 0
      · have : p = (0, p.2) := Prod.ext hp rfl
        simp only [Pi.add_apply, hz₁def, emb0, LinearMap.coe_mk, AddHom.coe_mk, hp, if_true, slice,
          zero_add]
        rw [← this]
      · simp [hz₁def, emb0, hp]
    have hθ₁ := restrict_mem h Λ α hα0 hP z₁ hz₁
    set θ₁ : (n → ℂ) → ℂ := fun v => P (z₁ + emb0 v) with hθ₁def
    obtain ⟨c, hc⟩ := hline _ (h4 n h Λ α (fun _ => θ₁) (fun _ => hθ₁))
    have hc' : tens4 θ₁ = c • P := hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := congrFun hc' (mk4 fun _ => slice 0 z)
      simp only [tens4, blockSlice_fourfoldMk, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_smul,
        Pi.zero_apply, hθ₁def, hzz] at h1
      exact hz (pow_eq_zero_iff (by norm_num) |>.1 h1)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (n := 4) (by norm_num)
    refine ⟨r • θ₁, (Th (matH h) α Λ).smul_mem r hθ₁, ?_⟩
    rw [fourfoldTensor_smul, hr, hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · intro θ' hθ' hθ'P
    obtain ⟨c, rfl⟩ := key_line θ hθ hθP θ' hθ'
    refine ⟨c, ?_, rfl⟩
    rw [fourfoldTensor_smul, hθP] at hθ'P
    have h1 := congrFun hθ'P z
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hz (by rw [h1, one_mul])

/- English proof (translation)
The claim follows from `FourthRoot_of fourfoldTensorMem`.
-/
theorem fourth_root : FourthRoot := FourthRoot_of fourfoldTensorMem

/- English proof (translation)
Break down `Int.even_or_odd' m with ⟨j, rfl | rfl⟩` into its components or cases. Use `left`. Establish `: (Real.pi : ℂ) * Complex.I * ((2 * j : ℤ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Use `right`. Establish `: (Real.pi : ℂ) * Complex.I * ((2 * j + 1 : ℤ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]`.
-/
theorem exp_pi_I_int (m : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 ∨
      Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = -1 := by
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · left
    have : (Real.pi : ℂ) * Complex.I * ((2 * j : ℤ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · right
    have : (Real.pi : ℂ) * Complex.I * ((2 * j + 1 : ℤ) : ℂ)
        = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

/- English proof (translation)
Introduce `V _ _ H hH b d hb Λ hdual hstab`. Establish `key : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k e : ℤ, altE H x y = (e : ℝ) ∧ Real.sqrt d * (H x y).re = 2 * (k : ℝ) - (b : ℝ) * (e : ℝ)`. Introduce `x hx y hy`. Take `⟨e, he⟩` from `hdual hx y hy`. Take `⟨k, hk⟩` from `hdual (hstab x hx) y hy`.

Use `⟨k, e, he, ?_⟩` and prove the remaining obligations. Establish `hθ : Formalism.L2.Th1.F.cmTheta b d = ⟨(b : ℝ) / 2, Real.sqrt d / 2⟩`. Apply the tactic sequence `apply Complex.ext <;> simp [Formalism.L2.Th1.F.cmTheta]`. Simplify using `only [altE, map_smul, LinearMap.smul_apply, smul_eq_mul, hθ, Complex.mul_im] at hk he`. Rewrite `hk` using `[he]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : ∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ)`. Introduce `x hx`. Take `⟨k, e, he, hk⟩` from `key x hx x hx`. Establish `him : altE H x x = 0`.

Use `altE_swap H hH x x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `he` using `[him]`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[← he]`.

Simplify using `only [qOf]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ)`. Introduce `x hx y hy`. Take `⟨k, e, he, hk⟩` from `key x hx y hy`.

Take `⟨t, rfl⟩` from `hb`. Use `⟨k - (t + 1) * e, ?_⟩` and prove the remaining obligations. Establish `hs` using `re_swap H hH x y`. Simplify using `only [qOf, map_add, LinearMap.add_apply, Complex.add_re]`. Rewrite using `[hs, he]`.

Move the coercions through the operations in `at hk ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hq, hadd, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨m, hm⟩` from `hq x hx`.

Simplify using `only [alphaQ, hm]`. Conclude with `exp_pi_I_int m` after adjusting the coercions. Introduce `x hx y hy`. Take `⟨m, hm⟩` from `hadd x hx y hy`. Establish `h1 : qOf (Real.sqrt d / 2) H (x + y) = qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y + altE H x y + 2 * (m : ℝ)`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [alphaQ]`. Rewrite using `[h1, ← Complex.exp_add, ← Complex.exp_add]`. Establish `h2 : (Real.pi : ℂ) * Complex.I * ((qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y + altE H x y + 2 * (m : ℝ) : ℝ) : ℂ) = ((Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H x : ℂ) + (Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H y : ℂ) + (Real.pi : ℂ) * Complex.I * …`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, Complex.exp_add _ ((m : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem quadMultiplierSemicharacter : AlphaQSemi := by
  intro V _ _ H hH b d hb Λ hdual hstab
  have key : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k e : ℤ, altE H x y = (e : ℝ) ∧
      Real.sqrt d * (H x y).re = 2 * (k : ℝ) - (b : ℝ) * (e : ℝ) := by
    intro x hx y hy
    obtain ⟨e, he⟩ := hdual hx y hy
    obtain ⟨k, hk⟩ := hdual (hstab x hx) y hy
    refine ⟨k, e, he, ?_⟩
    have hθ : Formalism.L2.Th1.F.cmTheta b d = ⟨(b : ℝ) / 2, Real.sqrt d / 2⟩ := by
      apply Complex.ext <;> simp [Formalism.L2.Th1.F.cmTheta]
    simp only [altE, map_smul, LinearMap.smul_apply, smul_eq_mul, hθ, Complex.mul_im] at hk he
    rw [he] at hk
    linarith
  have hq : ∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ) := by
    intro x hx
    obtain ⟨k, e, he, hk⟩ := key x hx x hx
    have him : altE H x x = 0 := by
      have := altE_swap H hH x x
      linarith
    rw [him] at he
    refine ⟨k, ?_⟩
    rw [← he] at hk
    simp only [qOf]
    linarith
  have hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x
        - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ) := by
    intro x hx y hy
    obtain ⟨k, e, he, hk⟩ := key x hx y hy
    obtain ⟨t, rfl⟩ := hb
    refine ⟨k - (t + 1) * e, ?_⟩
    have hs := re_swap H hH x y
    simp only [qOf, map_add, LinearMap.add_apply, Complex.add_re]
    rw [hs, he]
    push_cast at hk ⊢
    linarith
  refine ⟨hq, hadd, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := hq x hx
    simp only [alphaQ, hm]
    exact_mod_cast exp_pi_I_int m
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hadd x hx y hy
    have h1 : qOf (Real.sqrt d / 2) H (x + y)
        = qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y + altE H x y + 2 * (m : ℝ) := by
      linarith
    simp only [alphaQ]
    rw [h1, ← Complex.exp_add, ← Complex.exp_add]
    have h2 : (Real.pi : ℂ) * Complex.I * ((qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y
          + altE H x y + 2 * (m : ℝ) : ℝ) : ℂ)
        = ((Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H x : ℂ)
          + (Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H y : ℂ)
          + (Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_add _ ((m : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `V W _ _ _ _ H H' g hg c x`. Simplify using `only [alphaQ, qOf, hg x x]`. Introduce `n _ h c x`. Simplify using `only [alphaQ, qOf, matrixForm_fourfoldBlock]`.

Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Rewrite using `[Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]`.
-/
theorem quadMultiplierRules : AlphaQRules := by
  refine ⟨?_, ?_⟩
  · intro V W _ _ _ _ H H' g hg c x
    simp only [alphaQ, qOf, hg x x]
  · intro n _ h c x
    simp only [alphaQ, qOf, matrixForm_fourfoldBlock]
    rw [← Complex.exp_sum]
    congr 1
    rw [Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

/- English proof (translation)
Use `⟨fun x hx => by rw [hab x hx]; exact hβ.1 x hx, fun x hx y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hab x hx, hab y hy, hab _ (Λ.add_mem hx hy)]`. Conclude with `hβ.2 x hx y hy`.
-/
theorem isSemiChar_congr {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (α β : V → ℂ) (hab : ∀ x ∈ Λ, α x = β x) (hβ : IsSemiChar H Λ β) : IsSemiChar H Λ α := by
  refine ⟨fun x hx => by rw [hab x hx]; exact hβ.1 x hx, fun x hx y hy => ?_⟩
  rw [hab x hx, hab y hy, hab _ (Λ.add_mem hx hy)]
  exact hβ.2 x hx y hy

/- English proof (translation)
Introduce `L ω₀ n _ _ h Λ α β g D κ hκ`. Establish `hHerm : IsHerm (stdH L (Fin 4 × n))` using `(standardFormBasic L (Fin 4 × n)).2.1`. Establish `hβ1 : IsSemiChar (stdH L (Fin 4 × n)) (stdLat L (Fin 4 × n)) β` using `isSemiChar_congr _ _ _ _ D.betaStd (hSC L ω₀ (Fin 4 × n) D.per)`. Take `⟨hFmem, hF1⟩` from `hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd`. Establish `hFne : F0 L ω₀ (Fin 4 × n) ≠ 0`.

Introduce `h0`. Rewrite `hF1` using `[h0]`. Simplify using `at hF1`. Take `⟨hIne, hIline⟩` from `hLine (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β (hSD L _) D.selfDual hβ1 D.betaSemi D.idx₁ D.idx₂ _ hFmem hFne (fun F hF => ⟨F 0, hStd L ω₀ _ D.per D.half β D.betaStd F hF⟩)`. Establish `hImem` using `InterTh_of semicharacterHom heisenbergAnalytic (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi D.idx₁ _ hFmem`.

Establish `hβg : (fun v => β (g v)) = fun x => ∏ a, α (slice a x)` using `funext D.betaAlpha`. Establish `hiso` using `hIso (Fin 4 × n → ℂ) (Fin 4 × n → ℂ) (matH (blk4 h)) (stdH L (Fin 4 × n)) g D.isom (pow4 Λ) β`. Rewrite `hiso` using `[hβg]`. Establish `hK : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ)` using `(hiso _).1 hImem`. Establish `hK0 : kernel4 L ω₀ Λ β g ≠ 0`.

Introduce `h0`. Apply `hIne` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Use `congrFun h0 (g.symm w)` as an intermediate fact. Simplify `this` using `[kernel4]`.

Establish `hP : κ • kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ)` using `Submodule.smul_mem _ κ hK`. Establish `hP0 : κ • kernel4 L ω₀ Λ β g ≠ 0` using `smul_ne_zero hκ hK0`. Establish `hPline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ), ∃ c : ℂ, G = c • (κ • kernel4 L ω₀ Λ β g)`. Introduce `G hG`. Establish `hG' : (fun w => G (g.symm w)) ∈ Th (stdH L (Fin 4 × n)) β (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))`.

Use `(hiso _).2 ?_` and prove the remaining obligations. Simplify using `using hG`. Take `⟨c, hc⟩` from `hIline _ hG'`. Use `⟨c * κ⁻¹, funext fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun hc (g z)`.

Simplify using `only [LinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at h1`. Simplify using `only [Pi.smul_apply, smul_eq_mul, kernel4]`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Take `⟨hex, huniq⟩` from `h4 n h Λ α D.alpha0 _ hP hP0 hPline`.

Use `⟨hex, fun θ hθ hθP => ⟨?_, huniq θ hθ hθP⟩⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hP0` to reduce the goal to its premises. Rewrite using `[← hθP]`. Use function extensionality and compare the values at `z`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) rfl`.
-/
theorem ThetaVector_of (hLine : LineTransport) (hStd : ThStd) (hF0 : ProductThetaMem) (hSD : StdSelfDual)
    (hSC : StdSemiChar) (hIso : ThIsom) (h4 : FourthRoot) : ThetaVector := by
  intro L ω₀ n _ _ h Λ α β g D κ hκ
  have hHerm : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hβ1 : IsSemiChar (stdH L (Fin 4 × n)) (stdLat L (Fin 4 × n)) β :=
    isSemiChar_congr _ _ _ _ D.betaStd (hSC L ω₀ (Fin 4 × n) D.per)
  obtain ⟨hFmem, hF1⟩ := hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd
  have hFne : F0 L ω₀ (Fin 4 × n) ≠ 0 := by
    intro h0
    rw [h0] at hF1
    simp at hF1
  obtain ⟨hIne, hIline⟩ := hLine (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β (hSD L _) D.selfDual hβ1 D.betaSemi
    D.idx₁ D.idx₂ _ hFmem hFne (fun F hF => ⟨F 0, hStd L ω₀ _ D.per D.half β D.betaStd F hF⟩)
  have hImem := InterTh_of semicharacterHom heisenbergAnalytic (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm
    (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi
    D.idx₁ _ hFmem
  have hβg : (fun v => β (g v)) = fun x => ∏ a, α (slice a x) := funext D.betaAlpha
  have hiso := hIso (Fin 4 × n → ℂ) (Fin 4 × n → ℂ) (matH (blk4 h)) (stdH L (Fin 4 × n)) g D.isom
    (pow4 Λ) β
  rw [hβg] at hiso
  have hK : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    (hiso _).1 hImem
  have hK0 : kernel4 L ω₀ Λ β g ≠ 0 := by
    intro h0
    apply hIne
    funext w
    have := congrFun h0 (g.symm w)
    simpa [kernel4] using this
  have hP : κ • kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    Submodule.smul_mem _ κ hK
  have hP0 : κ • kernel4 L ω₀ Λ β g ≠ 0 := smul_ne_zero hκ hK0
  have hPline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ),
      ∃ c : ℂ, G = c • (κ • kernel4 L ω₀ Λ β g) := by
    intro G hG
    have hG' : (fun w => G (g.symm w)) ∈ Th (stdH L (Fin 4 × n)) β
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
      refine (hiso _).2 ?_
      simpa using hG
    obtain ⟨c, hc⟩ := hIline _ hG'
    refine ⟨c * κ⁻¹, funext fun z => ?_⟩
    have h1 := congrFun hc (g z)
    simp only [LinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [h1]
    field_simp
  obtain ⟨hex, huniq⟩ := h4 n h Λ α D.alpha0 _ hP hP0 hPline
  refine ⟨hex, fun θ hθ hθP => ⟨?_, huniq θ hθ hθP⟩⟩
  rintro rfl
  apply hP0
  rw [← hθP]
  funext z
  exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) rfl

end Formalism.L2.Th1.H
