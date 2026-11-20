import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CongrOrbit

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite using `[Matrix.sub_apply, ← Ideal.Quotient.eq]`. Simplify `this` using `[Matrix.one_apply, apply_ite]`.

Introduce `h`. Use extensionality with `i j`. Use `h i j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, ← Ideal.Quotient.eq]`. Simplify `this` using `[Matrix.one_apply, apply_ite]`.
-/
theorem quot_mapMatrix_eq_one_iff (I : Ideal O) (A : Matrix n n O) :
    (Ideal.Quotient.mk I).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ I := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simpa [Matrix.one_apply, apply_ite] using this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simpa [Matrix.one_apply, apply_ite] using this

/- English proof (translation)
Establish `h1` using `(quot_mapMatrix_eq_one_iff I A).2 hA`. Establish `h2 : Ideal.Quotient.mk I A.det = 1`. Rewrite using `[RingHom.map_det, h1, Matrix.det_one]`. Establish `h3 : A.det - 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq, h2, map_one]`.

Establish `h4` using `(Ideal.mem_jacobson_bot.1 (hI h3)) 1`. Simplify using `using h4`.
-/
theorem isUnit_det_of_sub_one_mem (I : Ideal O) (hI : I ≤ Ideal.jacobson ⊥) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) : IsUnit A.det := by
  have h1 := (quot_mapMatrix_eq_one_iff I A).2 hA
  have h2 : Ideal.Quotient.mk I A.det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have h3 : A.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, h2, map_one]
  have h4 := (Ideal.mem_jacobson_bot.1 (hI h3)) 1
  simpa using h4

variable {a b : Type} [Fintype a] [Fintype b]

def colFix (f : a → n) (ξ : a → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ p, (ξ p i - if i = f p then 1 else 0) * (if j = f p then 1 else 0)

def rowFix (g : b → n) (ζ : b → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ q, (if i = g q then 1 else 0) * (ζ q j - if g q = j then 1 else 0)

/- English proof (translation)
Simplify using `only [colFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]`. Conclude with `Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hξ p i)`.
-/
theorem colFix_sub_one_mem (I : Ideal O) (f : a → n) (ξ : a → n → O)
    (hξ : ∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) (i j : n) :
    (colFix f ξ - 1) i j ∈ I := by
  simp only [colFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hξ p i)

/- English proof (translation)
Simplify using `only [colFix, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single p₀]`. Rewrite using `[if_pos rfl, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Introduce `p _ hp`.

Rewrite using `[if_neg (fun h => hp (hf h).symm), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem colFix_apply_col {f : a → n} (hf : Function.Injective f) (ξ : a → n → O) (i : n)
    (p₀ : a) : colFix f ξ i (f p₀) = ξ p₀ i := by
  simp only [colFix, Matrix.of_apply]
  rw [Finset.sum_eq_single p₀]
  · rw [if_pos rfl, mul_one]; ring
  · intro p _ hp
    rw [if_neg (fun h => hp (hf h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `only [rowFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]`. Conclude with `Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hζ q j)`.
-/
theorem rowFix_sub_one_mem (I : Ideal O) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I) (i j : n) :
    (rowFix g ζ - 1) i j ∈ I := by
  simp only [rowFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hζ q j)

/- English proof (translation)
Simplify using `only [rowFix, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single q₀]`. Rewrite using `[if_pos rfl, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `q _ hq`.

Rewrite using `[if_neg (fun h => hq (hg h).symm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem rowFix_apply_row {g : b → n} (hg : Function.Injective g) (ζ : b → n → O) (j : n)
    (q₀ : b) : rowFix g ζ (g q₀) j = ζ q₀ j := by
  simp only [rowFix, Matrix.of_apply]
  rw [Finset.sum_eq_single q₀]
  · rw [if_pos rfl, one_mul]; ring
  · intro q _ hq
    rw [if_neg (fun h => hq (hg h).symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `only [rowFix, Matrix.of_apply, hζ, sub_self, mul_zero, Finset.sum_const_zero, add_zero]`.
-/
theorem rowFix_apply_col (f : a → n) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0) (i : n) (p : a) :
    rowFix g ζ i (f p) = if i = f p then 1 else 0 := by
  simp only [rowFix, Matrix.of_apply, hζ, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Establish `e1 : (v ᵥ* A) j = (v ᵥ* (A - 1)) j + v j`. Rewrite using `[Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (if c = j then (1 : O) else 0) = if j = c then 1 else 0`. Distinguish the cases in `h : c = j`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[e1, e2, add_sub_assoc]`. Use `add_mem ?_ (hv j)` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct]`.

Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hA i j)`.
-/
theorem vecMul_sub_single_mem (I : Ideal O) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) (v : n → O) (c : n)
    (hv : ∀ i, v i - (if i = c then 1 else 0) ∈ I) (j : n) :
    (v ᵥ* A) j - (if c = j then 1 else 0) ∈ I := by
  have e1 : (v ᵥ* A) j = (v ᵥ* (A - 1)) j + v j := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]; ring
  have e2 : (if c = j then (1 : O) else 0) = if j = c then 1 else 0 := by
    by_cases h : c = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e1, e2, add_sub_assoc]
  refine add_mem ?_ (hv j)
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hA i j)

end GlobalTheory.AscFin.CongrOrbit

/- English proof (translation)
Introduce `O _ I hI n a b _ _ _ _ f g hf hg ξ η hξ hη hηξ`. Use `open GlobalTheory.AscFin.CongrOrbit in`. Use `set k₁ := colFix f ξ with hk₁`. Establish `hk₁I` using `colFix_sub_one_mem I f ξ hξ`. Use `set ζ : b → n → O := fun q => η q ᵥ* k₁ with hζdef`.

Establish `hζI : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I` using `fun q j => vecMul_sub_single_mem I k₁ hk₁I (η q) (g q) (hη q) j`. Establish `hζcol : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0`. Introduce `q p`. Establish `hc : (fun i => k₁ i (f p)) = ξ p` using `funext fun i => colFix_apply_col hf ξ i p`. Simplify using `only [hζdef, Matrix.vecMul]`.

Rewrite using `[hc, hηξ]`. Use `set m := rowFix g ζ with hm`. Establish `hmI` using `rowFix_sub_one_mem I g ζ hζI`. Establish `hmcol : ∀ i p, m i (f p) = if i = f p then 1 else 0` using `rowFix_apply_col f g ζ hζcol`. Establish `u₁` using `isUnit_det_of_sub_one_mem I hI k₁ hk₁I`.

Establish `um` using `isUnit_det_of_sub_one_mem I hI m hmI`. Use `set U₁ := Matrix.nonsingInvUnit k₁ u₁`. Use `set Um := Matrix.nonsingInvUnit m um`. Use `set Wm : Matrix n n O := ((Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) with hWm`. Establish `hWmm : Wm * m = 1` using `Um.inv_mul`.

Establish `hmWm : m * Wm = 1` using `Um.mul_inv`. Establish `hval : ((U₁ * Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) = k₁ * Wm` using `rfl`. Use `⟨U₁ * Um⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ← quot_mapMatrix_eq_one_iff]`. Establish `e1` using `(quot_mapMatrix_eq_one_iff I k₁).2 hk₁I`.

Establish `e2` using `(quot_mapMatrix_eq_one_iff I m).2 hmI`. Establish `eW : (Ideal.Quotient.mk I).mapMatrix Wm = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, mul_one]`. Use `_ = 1 := by rw [← map_mul, hWmm, map_one]`.

Rewrite using `[map_mul, e1, eW, one_mul]`. Introduce `p i`. Rewrite using `[hval]`. Establish `hWcol : ∀ l, Wm l (f p) = if l = f p then 1 else 0`. Introduce `l`.

Use `congrFun (congrFun hWmm l) (f p)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify `this` using `only [hmcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hWcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Conclude with `colFix_apply_col hf ξ i p`. Introduce `q`. Rewrite using `[hval, ← Matrix.vecMul_vecMul]`. Use function extensionality and compare the values at `j`. Establish `hrow : η q ᵥ* k₁ = fun l => m (g q) l`.

Use function extensionality and compare the values at `l`. Rewrite using `[hm, rowFix_apply_row hg]`. Rewrite using `[hrow]`. Use `congrFun (congrFun hmWm (g q)) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Simplify using `only [Matrix.vecMul, dotProduct]`. Rewrite using `[this]`. Distinguish the cases in `h : g q = j`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem GlobalTheory.AscFin.exists_gl_congr_cols_rows : ∀ (O : Type) [CommRing O] (I : Ideal O), I ≤ Ideal.jacobson ⊥ → ∀ (n a b : Type) [Fintype n] [DecidableEq n] [Fintype a] [Fintype b] (f : a → n) (g : b → n), Function.Injective f → Function.Injective g → ∀ (ξ : a → n → O) (η : b → n → O), (∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) → (∀ q i, η q i - (if i = g q then 1 else 0) ∈ I) → (∀ p q, η q ⬝ᵥ ξ p = if g q = f p then 1 else 0) → ∃ k : GL n O, (∀ i j, (k.1 - 1) i j ∈ I) ∧ (∀ p i, k.1 i (f p) = ξ p i) ∧ ∀ q, η q ᵥ* k.1 = fun i => if i = g q then 1 else 0 := by
  intro O _ I hI n a b _ _ _ _ f g hf hg ξ η hξ hη hηξ
  open GlobalTheory.AscFin.CongrOrbit in
  set k₁ := colFix f ξ with hk₁
  have hk₁I := colFix_sub_one_mem I f ξ hξ
  set ζ : b → n → O := fun q => η q ᵥ* k₁ with hζdef
  have hζI : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I := fun q j =>
    vecMul_sub_single_mem I k₁ hk₁I (η q) (g q) (hη q) j
  have hζcol : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0 := by
    intro q p
    have hc : (fun i => k₁ i (f p)) = ξ p := funext fun i => colFix_apply_col hf ξ i p
    simp only [hζdef, Matrix.vecMul]
    rw [hc, hηξ]
  set m := rowFix g ζ with hm
  have hmI := rowFix_sub_one_mem I g ζ hζI
  have hmcol : ∀ i p, m i (f p) = if i = f p then 1 else 0 := rowFix_apply_col f g ζ hζcol
  have u₁ := isUnit_det_of_sub_one_mem I hI k₁ hk₁I
  have um := isUnit_det_of_sub_one_mem I hI m hmI
  set U₁ := Matrix.nonsingInvUnit k₁ u₁
  set Um := Matrix.nonsingInvUnit m um
  set Wm : Matrix n n O := ((Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) with hWm
  have hWmm : Wm * m = 1 := Um.inv_mul
  have hmWm : m * Wm = 1 := Um.mul_inv
  have hval : ((U₁ * Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) = k₁ * Wm := rfl
  refine ⟨U₁ * Um⁻¹, ?_, ?_, ?_⟩
  · rw [hval, ← quot_mapMatrix_eq_one_iff]
    have e1 := (quot_mapMatrix_eq_one_iff I k₁).2 hk₁I
    have e2 := (quot_mapMatrix_eq_one_iff I m).2 hmI
    have eW : (Ideal.Quotient.mk I).mapMatrix Wm = 1 := by
      calc (Ideal.Quotient.mk I).mapMatrix Wm
          = (Ideal.Quotient.mk I).mapMatrix Wm * (Ideal.Quotient.mk I).mapMatrix m := by
            rw [e2, mul_one]
        _ = 1 := by rw [← map_mul, hWmm, map_one]
    rw [map_mul, e1, eW, one_mul]
  · intro p i
    rw [hval]
    have hWcol : ∀ l, Wm l (f p) = if l = f p then 1 else 0 := by
      intro l
      have := congrFun (congrFun hWmm l) (f p)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simpa only [hmcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] using this
    rw [Matrix.mul_apply]
    simp only [hWcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact colFix_apply_col hf ξ i p
  · intro q
    rw [hval, ← Matrix.vecMul_vecMul]
    funext j
    have hrow : η q ᵥ* k₁ = fun l => m (g q) l := by
      funext l; rw [hm, rowFix_apply_row hg]
    rw [hrow]
    have := congrFun (congrFun hmWm (g q)) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.vecMul, dotProduct]
    rw [this]
    by_cases h : g q = j
    · simp [h]
    · simp [h, Ne.symm h]
