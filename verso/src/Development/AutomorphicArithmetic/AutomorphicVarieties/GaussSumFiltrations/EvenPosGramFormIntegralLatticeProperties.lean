import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Mathlib
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.FormLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Establish `h` using `hG.1.1`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `[Matrix.conjTranspose_apply, Matrix.map_apply] at this`. Simplify using `only [Matrix.transpose_apply]`.

Conclude with `this` after adjusting the coercions.
-/
theorem symm_of_evenPos {G : Matrix κ κ ℤ} (hG : EvenPos G) : Gᵀ = G := by
  have h := hG.1.1
  ext i j
  have := congrFun (congrFun h i) j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply] at this
  simp only [Matrix.transpose_apply]
  exact_mod_cast this

/- English proof (translation)
Unfold `BF`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, hG]`.
-/
theorem bf_symm {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : BF G x y = BF G y x := by
  unfold BF
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, hG]

/- English proof (translation)
Unfold `BF`. Rewrite using `[add_dotProduct]`.
-/
theorem bf_add_left (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G (x + y) z = BF G x z + BF G y z := by
  unfold BF; rw [add_dotProduct]

/- English proof (translation)
Unfold `BF`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
theorem bf_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  unfold BF; rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `BF`. Rewrite using `[smul_dotProduct, smul_eq_mul]`.
-/
theorem bf_smul_left (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G (a • x) y = a * BF G x y := by
  unfold BF; rw [smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `BF`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem bf_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  unfold BF; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Unfold `QF`. Rewrite using `[bf_add_left, bf_add_right, bf_add_right, bf_symm hG y x]`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qf_add {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : QF G (x + y) = QF G x + BF G x y + QF G y := by
  unfold QF
  rw [bf_add_left, bf_add_right, bf_add_right, bf_symm hG y x]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  ring

/- English proof (translation)
Simplify using `[LL, AddSubgroup.mem_pi, mem_integralClosure_iff]`.
-/
theorem mem_LL {x : κ → F} : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]

/- English proof (translation)
Simplify using `using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)`.
-/
theorem intCast_isIntegral (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

/- English proof (translation)
Unfold `BF`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.map_apply]`. Conclude with `IsIntegral.sum _ fun i _ => (hx i).mul (IsIntegral.sum _ fun j _ => (intCast_isIntegral _).mul (hy j))`.
-/
theorem bf_int (G : Matrix κ κ ℤ) {x y : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) :
    IsIntegral ℤ (BF G x y) := by
  unfold BF
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  exact IsIntegral.sum _ fun i _ => (hx i).mul (IsIntegral.sum _ fun j _ => (intCast_isIntegral _).mul (hy j))

/- English proof (translation)
Use `Algebra.isIntegral_trace (L := ℚ) hx` as an intermediate fact. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp this`. Conclude with `⟨n, by rw [← hn]; simp⟩`.
-/
theorem trace_int {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  have := Algebra.isIntegral_trace (L := ℚ) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  exact ⟨n, by rw [← hn]; simp⟩

/- English proof (translation)
Simplify using `[QF, BF, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem qf_single (G : Matrix κ κ ℤ) (i : κ) (c : F) : QF G (Pi.single i c) = c * ((G i i : F) * c) / 2 := by
  simp [QF, BF, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Establish `hs : Gᵀ = G` using `symm_of_evenPos hG`. Establish `hsingle : ∀ i, IsIntegral ℤ (QF G (Pi.single i (x i)))`. Introduce `i`. Take `⟨m, hm⟩` from `hG.2 i`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`.

Establish `: QF G (Pi.single i (x i)) = (m : F) * x i * x i`. Rewrite using `[qf_single, hm]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `((intCast_isIntegral m).mul (hx i)).mul (hx i)`. Establish `hvi : ∀ (s : Finset κ) (j : κ), IsIntegral ℤ ((∑ i ∈ s, Pi.single i (x i) : κ → F) j)`. Introduce `s j`. Rewrite using `[Finset.sum_apply]`.

Conclude with `IsIntegral.sum _ fun i _ => by`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using hx j`. Simplify using `[Pi.single_apply, h, isIntegral_zero]`.

Establish `key : ∀ s : Finset κ, IsIntegral ℤ (QF G (∑ i ∈ s, Pi.single i (x i)))`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify `(isIntegral_zero : IsIntegral ℤ (0 : F))` using `[QF, BF]`. Introduce `i s hi ih`.

Rewrite using `[Finset.sum_insert hi, qf_add hs]`. Use `((hsingle i).add (bf_int G ?_ (hvi s))).add ih` and prove the remaining obligations. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `using hx j`. Simplify using `[Pi.single_apply, h, isIntegral_zero]`. Simplify `key Finset.univ` using `[Finset.univ_sum_single]`.
-/
theorem qf_int {G : Matrix κ κ ℤ} (hG : EvenPos G) {x : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) : IsIntegral ℤ (QF G x) := by
  have hs : Gᵀ = G := symm_of_evenPos hG
  have hsingle : ∀ i, IsIntegral ℤ (QF G (Pi.single i (x i))) := by
    intro i
    obtain ⟨m, hm⟩ := hG.2 i
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : QF G (Pi.single i (x i)) = (m : F) * x i * x i := by
      rw [qf_single, hm]; push_cast; field_simp; ring
    rw [this]
    exact ((intCast_isIntegral m).mul (hx i)).mul (hx i)
  have hvi : ∀ (s : Finset κ) (j : κ), IsIntegral ℤ ((∑ i ∈ s, Pi.single i (x i) : κ → F) j) := by
    intro s j
    rw [Finset.sum_apply]
    exact IsIntegral.sum _ fun i _ => by
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  have key : ∀ s : Finset κ, IsIntegral ℤ (QF G (∑ i ∈ s, Pi.single i (x i))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [QF, BF] using (isIntegral_zero : IsIntegral ℤ (0 : F))
    · intro i s hi ih
      rw [Finset.sum_insert hi, qf_add hs]
      refine ((hsingle i).add (bf_int G ?_ (hvi s))).add ih
      intro j
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  simpa [Finset.univ_sum_single] using key Finset.univ

/- English proof (translation)
Establish `h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `by simp [Real.pi_ne_zero]`. Establish `hiff : et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n`. Unfold `et`. Rewrite using `[Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨n, hn⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ)`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Introduce and unpack `⟨n, hn⟩`. Conclude with `⟨n, by rw [hn]; push_cast; ring⟩`.

Use `⟨?_, ?_, hiff, fun hx => hiff.mpr (trace_int hx)⟩` and prove the remaining obligations. Unfold `et`. Rewrite using `[map_add, Rat.cast_add, mul_add, Complex.exp_add]`. Unfold `et`. Establish `: 2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((2 * Real.pi * (Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`.

Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem et_props (x y : F) : et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧
    (IsIntegral ℤ x → et x = 1) := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hiff : et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n := by
    unfold et
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        apply mul_left_cancel₀ h0
        rw [hn]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; ring⟩
  refine ⟨?_, ?_, hiff, fun hx => hiff.mpr (trace_int hx)⟩
  · unfold et; rw [map_add, Rat.cast_add, mul_add, Complex.exp_add]
  · unfold et
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ) =
        ((2 * Real.pi * (Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

end GlobalTheory.HilbertThetaSeries.FormLat

open GlobalTheory.HilbertThetaSeries.FormLat in

/- English proof (translation)
Introduce `F _ _ κ _ _ G hG`. Establish `hs : Gᵀ = G` using `symm_of_evenPos hG`. Use `⟨fun x y => ⟨bf_symm hs x y, qf_add hs x y⟩, fun a x y => ⟨bf_smul_left G a x y, ?_, ?_⟩, bf_add_left G, fun x hx => ⟨qf_int hG (mem_LL.mp hx), fun y hy => bf_int G (mem_LL.mp hx) (mem_LL.mp hy)⟩, fun x => mem_LL, fun a x => ?_, et_props, ?_⟩` and prove the remaining obligations. Unfold `QF`. Rewrite using `[bf_smul_left, bf_smul_right]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `QF BF`. Rewrite using `[Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]`. Unfold `aL`. Rewrite using `[AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`. Conclude with `⟨l, hl, rfl⟩`. Introduce and unpack `⟨l, hl, rfl⟩`. Conclude with `⟨l, hl, rfl⟩`.

Introduce `y hy l hl`. Conclude with `trace_int (bf_int G (mem_LL.mp hy) (mem_LL.mp hl))`.
-/
theorem GlobalTheory.HilbertThetaSeries.formLatticeProps : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  intro F _ _ κ _ _ G hG
  have hs : Gᵀ = G := symm_of_evenPos hG
  refine ⟨fun x y => ⟨bf_symm hs x y, qf_add hs x y⟩, fun a x y => ⟨bf_smul_left G a x y, ?_, ?_⟩,
    bf_add_left G, fun x hx => ⟨qf_int hG (mem_LL.mp hx), fun y hy => bf_int G (mem_LL.mp hx) (mem_LL.mp hy)⟩,
    fun x => mem_LL, fun a x => ?_, et_props, ?_⟩
  · unfold QF; rw [bf_smul_left, bf_smul_right]; ring
  · unfold QF BF; rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  · unfold aL
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · intro y hy l hl
    exact trace_int (bf_int G (mem_LL.mp hy) (mem_LL.mp hl))

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.formLatticeProps | exact GlobalTheory.HilbertThetaSeries.formLatticeProps | (intros; apply GlobalTheory.HilbertThetaSeries.formLatticeProps <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.evenPos_gramForm_integral_lattice_properties : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  first | exact @GlobalTheory.HilbertThetaSeries.formLatticeProps | exact GlobalTheory.HilbertThetaSeries.formLatticeProps | (intros; apply GlobalTheory.HilbertThetaSeries.formLatticeProps <;> assumption)
