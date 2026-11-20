import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.AdelicLattice
import GroundTheory.AutomorphicForms.DefiniteClassNumber.GramReduction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

variable (K) in

abbrev IntBasisIdx := Free.ChooseBasisIndex ℤ (𝓞 K)

def ratCoords (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℚ :=
  fun j => (integralBasis K).repr (vecCoords K b x j.1) j.2

def ofRatCoords (c : (ι × κ) × IntBasisIdx K → ℚ) : ι → K ⊗[K] E :=
  vecOfCoords b K fun a => (integralBasis K).equivFun.symm fun t => c (a, t)

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [ratCoords, ofRatCoords, vecCoords_vecOfCoords]`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem ratCoords_ofRatCoords (c : (ι × κ) × IntBasisIdx K → ℚ) :
    ratCoords b (ofRatCoords b c) = c := by
  funext j
  simp only [ratCoords, ofRatCoords, vecCoords_vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use `conv_rhs => rw [← vecOfCoords_vecCoords b K x]`. Simplify using `only [ofRatCoords, ratCoords]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `(integralBasis K).equivFun.symm_apply_apply (vecCoords K b x a)`.
-/
theorem ofRatCoords_ratCoords (x : ι → K ⊗[K] E) : ofRatCoords b (ratCoords b x) = x := by
  conv_rhs => rw [← vecOfCoords_vecCoords b K x]
  simp only [ofRatCoords, ratCoords]
  congr 1
  funext a
  exact (integralBasis K).equivFun.symm_apply_apply (vecCoords K b x a)

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Introduce `x y h` and use `by rw [← ofRatCoords_ratCoords b x, h, ofRatCoords_ratCoords]`.
-/
theorem ratCoords_injective : Function.Injective (ratCoords (ι := ι) b) := fun x y h => by
  rw [← ofRatCoords_ratCoords b x, h, ofRatCoords_ratCoords]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[ratCoords, vecCoords_add]`.
-/
theorem ratCoords_add (x y : ι → K ⊗[K] E) :
    ratCoords b (x + y) = ratCoords b x + ratCoords b y := by
  funext j
  simp [ratCoords, vecCoords_add]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[ratCoords, vecCoords_zero]`.
-/
theorem ratCoords_zero : ratCoords b (0 : ι → K ⊗[K] E) = 0 := by
  funext j
  simp [ratCoords, vecCoords_zero]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [ratCoords, vecCoords_smul, Pi.smul_apply]`. Rewrite using `[← Rat.smul_def, map_smul]`. Both sides reduce to the same expression.
-/
theorem ratCoords_smul (q : ℚ) (x : ι → K ⊗[K] E) :
    ratCoords b ((q : K) • x) = q • ratCoords b x := by
  funext j
  simp only [ratCoords, vecCoords_smul, Pi.smul_apply]
  rw [← Rat.smul_def, map_smul]
  rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Rewrite using `[← ratCoords_smul, Rat.cast_intCast]`.
-/
theorem ratCoords_intSmul (m : ℤ) (x : ι → K ⊗[K] E) :
    ratCoords b ((m : K) • x) = (m : ℚ) • ratCoords b x := by
  rw [← ratCoords_smul, Rat.cast_intCast]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [ratCoords_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratCoords_add, ih]`.
-/
theorem ratCoords_sum {ι' : Type*} {s : Finset ι'} (x : ι' → ι → K ⊗[K] E) :
    ratCoords b (∑ i ∈ s, x i) = ∑ i ∈ s, ratCoords b (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ratCoords_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratCoords_add, ih]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] in

/- English proof (translation)
Simplify using `only [ofRatCoords, vecCoords_vecOfCoords, Basis.equivFun_symm_apply]`. Use `IsIntegral.sum _ fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Rewrite using `[one_smul, integralBasis_apply]`.

Conclude with `RingOfIntegers.isIntegral_coe _`. Rewrite using `[zero_smul]`. Conclude with `isIntegral_zero`.
-/
theorem isIntegral_vecCoords_ofRatCoords_single [DecidableEq κ] (j : (ι × κ) × IntBasisIdx K)
    (a : ι × κ) : IsIntegral ℤ (vecCoords K b (ofRatCoords b (Pi.single j 1)) a) := by
  classical
  simp only [ofRatCoords, vecCoords_vecOfCoords, Basis.equivFun_symm_apply]
  refine IsIntegral.sum _ fun t _ => ?_
  rw [Pi.single_apply]
  split_ifs
  · rw [one_smul, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · rw [zero_smul]
    exact isIntegral_zero

variable (H : Matrix ι ι E)

def ratForm (θ : K) (x y : ι → K ⊗[K] E) : ℚ := Algebra.trace ℚ K (θ * hermTrace K H K x y)

variable {H}

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `[ratForm, hermTrace_add_left, mul_add]`.
-/
theorem ratForm_add_left (θ : K) (x x' y : ι → K ⊗[K] E) :
    ratForm H θ (x + x') y = ratForm H θ x y + ratForm H θ x' y := by
  simp [ratForm, hermTrace_add_left, mul_add]

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `[ratForm, hermTrace_add_right, mul_add]`.
-/
theorem ratForm_add_right (θ : K) (x y y' : ι → K ⊗[K] E) :
    ratForm H θ x (y + y') = ratForm H θ x y + ratForm H θ x y' := by
  simp [ratForm, hermTrace_add_right, mul_add]

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [ratForm, hermTrace_smul_left]`. Put the polynomial expressions in normal form.
-/
theorem ratForm_smul_left (θ : K) (c : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ (c • x) y = Algebra.trace ℚ K (c * θ * hermTrace K H K x y) := by
  simp only [ratForm, hermTrace_smul_left]
  ring_nf

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [ratForm, hermTrace_smul_right]`. Put the polynomial expressions in normal form.
-/
theorem ratForm_smul_right (θ : K) (c : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ x (c • y) = Algebra.trace ℚ K (c * θ * hermTrace K H K x y) := by
  simp only [ratForm, hermTrace_smul_right]
  ring_nf

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[ratForm_smul_left, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem ratForm_ratSmul_left (θ : K) (q : ℚ) (x y : ι → K ⊗[K] E) :
    ratForm H θ ((q : K) • x) y = q * ratForm H θ x y := by
  rw [ratForm_smul_left, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[ratForm_smul_right, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem ratForm_ratSmul_right (θ : K) (q : ℚ) (x y : ι → K ⊗[K] E) :
    ratForm H θ x ((q : K) • y) = q * ratForm H θ x y := by
  rw [ratForm_smul_right, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[ratForm, ratForm, hermTrace_comm hH]`.
-/
theorem ratForm_comm (hH : IsHermitianFor (conjHom K E) H) (θ : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ y x = ratForm H θ x y := by
  rw [ratForm, ratForm, hermTrace_comm hH]

variable (H) in

/- English proof (translation)
Use `set ω := integralBasis K`. Establish `hv : ∀ (z : ι → K ⊗[K] E) (a : ι × κ), vecCoords K b z a = ∑ t, (ratCoords b z (a, t) : K) * ω t`. Introduce `z a`. Use `conv_lhs => rw [← ω.sum_repr (vecCoords K b z a)]`. Simplify using `only [Rat.smul_def]`.

Both sides reduce to the same expression. Establish `swap4 : ∀ F : ι × κ → IntBasisIdx K → ι × κ → IntBasisIdx K → K, ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t'` using `fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Establish `key : θ * hermTrace K H K x y = ∑ j, ∑ j', ((ratCoords b x j * ratCoords b y j' : ℚ) : K) * (θ * ω j.2 * ω j'.2 * traceGram H b j.1 j'.1)`. Rewrite using `[hermTrace_eq_sum_traceGram (H := H) (b := b) K]`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply, hv, Finset.mul_sum, Finset.sum_mul]`.

Simplify using `only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := IntBasisIdx K)]`. Establish `swap2 : ∀ F : IntBasisIdx K → IntBasisIdx K → K, ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t'` using `fun F => Finset.sum_comm`. Rewrite using `[swap4]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[swap2]`.

Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ratForm, key, map_sum]`. Simplify using `only [dotProduct, mulVec, ratGram, Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Rewrite using `[← Rat.smul_def, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratForm_eq (θ : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ x y = ratCoords b x ⬝ᵥ (ratGram H b θ *ᵥ ratCoords b y) := by
  set ω := integralBasis K
  have hv : ∀ (z : ι → K ⊗[K] E) (a : ι × κ),
      vecCoords K b z a = ∑ t, (ratCoords b z (a, t) : K) * ω t := by
    intro z a
    conv_lhs => rw [← ω.sum_repr (vecCoords K b z a)]
    simp only [Rat.smul_def]
    rfl
  have swap4 : ∀ F : ι × κ → IntBasisIdx K → ι × κ → IntBasisIdx K → K,
      ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t' :=
    fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have key : θ * hermTrace K H K x y = ∑ j, ∑ j', ((ratCoords b x j * ratCoords b y j' : ℚ) : K) *
      (θ * ω j.2 * ω j'.2 * traceGram H b j.1 j'.1) := by
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hv, Finset.mul_sum, Finset.sum_mul]
    simp only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := IntBasisIdx K)]
    have swap2 : ∀ F : IntBasisIdx K → IntBasisIdx K → K,
        ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t' := fun F => Finset.sum_comm
    rw [swap4]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [swap2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    push_cast
    ring
  rw [ratForm, key, map_sum]
  simp only [dotProduct, mulVec, ratGram, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← Rat.smul_def, map_smul, smul_eq_mul]
  ring

def ratEmb (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℝ := fun j => (ratCoords b x j : ℝ)

variable (H) in
/- English proof (translation)
Rewrite using `[ratForm_eq b H]`. Simplify using `only [ratEmb, dotProduct, mulVec, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul]`.
-/
theorem ratEmb_gram (θ : K) (x y : ι → K ⊗[K] E) :
    ratEmb b x ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ ratEmb b y) = (ratForm H θ x y : ℝ) := by
  rw [ratForm_eq b H]
  simp only [ratEmb, dotProduct, mulVec, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul]

variable (H) in

def ratEmbHom : (ι → K ⊗[K] E) →+ ((ι × κ) × IntBasisIdx K → ℝ) where
  toFun := ratEmb b
  map_zero' := by funext j; simp [ratEmb, ratCoords_zero]
  map_add' x y := by funext j; simp [ratEmb, ratCoords_add]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Introduce `x y h` and use `by apply ratCoords_injective b funext j have := congrFun h j simp only [ratEmb] at this exact_mod_cast this`.
-/
theorem ratEmb_injective : Function.Injective (ratEmb (ι := ι) b) := fun x y h => by
  apply ratCoords_injective b
  funext j
  have := congrFun h j
  simp only [ratEmb] at this
  exact_mod_cast this

/- English proof (translation)
Establish `: (0 : ℝ) < (ratForm H θ x x : ℝ)`. Rewrite using `[ratForm, trace_eq_sum_realEmb hreal]`. Conclude with `Finset.sum_pos (fun w _ => realEmb_mul_hermTrace_pos hθ (hreal w) hx) Finset.univ_nonempty`. Conclude with `this` after adjusting the coercions.
-/
theorem ratForm_self_pos (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {x : ι → K ⊗[K] E} (hx : x ≠ 0) : 0 < ratForm H θ x x := by
  have : (0 : ℝ) < (ratForm H θ x x : ℝ) := by
    rw [ratForm, trace_eq_sum_realEmb hreal]
    exact Finset.sum_pos (fun w _ => realEmb_mul_hermTrace_pos hθ (hreal w) hx) Finset.univ_nonempty
  exact_mod_cast this

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `: hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0`. Rewrite using `[← hermTraceBilin_apply, map_zero]`. Simplify using `[ratForm, this]`.

Conclude with `(ratForm_self_pos b hreal hθ hx).le`.
-/
theorem ratForm_self_nonneg (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    (x : ι → K ⊗[K] E) : 0 ≤ ratForm H θ x x := by
  by_cases hx : x = 0
  · subst hx
    have : hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0 := by
      rw [← hermTraceBilin_apply, map_zero]
    simp [ratForm, this]
  · exact (ratForm_self_pos b hreal hθ hx).le

end GroundTheory.Automorphic
