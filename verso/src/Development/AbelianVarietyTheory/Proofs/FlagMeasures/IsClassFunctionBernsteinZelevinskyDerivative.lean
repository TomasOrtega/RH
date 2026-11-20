import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.DerClass

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g)) (D : Mt g b) :
    Mt g (a + b) :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/- English proof (translation)
Use `⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩` and prove the remaining obligations. Rewrite using `[blocks, Matrix.fromBlocks_toBlocks]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem exists_blocks (M : Mt g (a + b)) : ∃ A B C D, M = blocks A B C D := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blocks, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.GLm.DerClass.blocks`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem _root_.GlobalTheory.GLm.DerClass.blocks_mul (A A' : _root_.GlobalTheory.GLq.Mt g a)
    (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (C C' : Matrix (Fin b) (Fin a) (ZMod g))
    (D D' : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLm.DerClass.blocks A B C D * _root_.GlobalTheory.GLm.DerClass.blocks A' B' C' D' =
      _root_.GlobalTheory.GLm.DerClass.blocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.GLm.DerClass.blocks`. Rewrite using `[Matrix.fromBlocks_one]`. Conclude with `Matrix.submatrix_one_equiv _`.
-/
theorem _root_.GlobalTheory.GLm.DerClass.blocks_one :
    _root_.GlobalTheory.GLm.DerClass.blocks (1 : _root_.GlobalTheory.GLq.Mt g a) 0 0 (1 : _root_.GlobalTheory.GLq.Mt g b) = 1 := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[tl, entN, dif_pos ⟨by omega, by omega⟩]`. Express the relevant statement in the definitionally equal form `blocks A B C D (Fin.castAdd b i) (Fin.castAdd b j) = _`.

Simplify using `[blocks]`.
-/
theorem tl_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : tl a (blocks A B C D) = A := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [tl, entN, dif_pos ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.castAdd b i) (Fin.castAdd b j) = _
  simp [blocks]

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[br, entN, dif_pos ⟨by omega, by omega⟩]`. Express the relevant statement in the definitionally equal form `blocks A B C D (Fin.natAdd a i) (Fin.natAdd a j) = _`.

Simplify using `[blocks]`.
-/
theorem br_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : br a b (blocks A B C D) = D := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [br, entN, dif_pos ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.natAdd a i) (Fin.natAdd a j) = _
  simp [blocks]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Use `h (Fin.natAdd a i) (Fin.castAdd b j) (by simp) (by simp)` as an intermediate fact. Simplify `this` using `[blocks]`.

Introduce and unpack `rfl i j hj hi`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => have := i.2`. Simplify using `at hi`. Use linear arithmetic over natural numbers and integers.

Consider the case `right i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j => simp [blocks]`. Consider the case `right j => simp at hj`.
-/
theorem inPar_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : InPar a (blocks A B C D) ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Fin.natAdd a i) (Fin.castAdd b j) (by simp) (by simp)
    simpa [blocks] using this
  · rintro rfl i j hj hi
    induction i using Fin.addCases with
    | left i => have := i.2; simp at hi; omega
    | right i =>
      induction j using Fin.addCases with
      | left j => simp [blocks]
      | right j => simp at hj

/- English proof (translation)
Introduce `i j hi`. Rewrite using `[← blocks_one]`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => have := i.2`. Simplify using `at hi`.

Use linear arithmetic over natural numbers and integers. Consider the case `right i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j => simp [blocks]`. Consider the case `right j`.

Establish `hj` using `j.2`. Simplify using `only [Fin.val_natAdd] at hi`. Simplify using `only [blocks, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]`. Distinguish the cases in `h : i = j`. Rewrite using `[(hD i j).2 h, h, Matrix.one_apply_eq]`.

Rewrite using `[Matrix.one_apply_ne h]`. Use `(hD i j).1 ?_` and prove the remaining obligations. Establish `: (i : ℕ) ≠ j` using `fun e => h (Fin.ext e)`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem inMir_blocks (hb : 0 < b) (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) {D : Mt g b} (hD : IsUniUp D) :
    InMir (blocks A B 0 D) := by
  intro i j hi
  rw [← blocks_one]
  induction i using Fin.addCases with
  | left i => have := i.2; simp at hi; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => simp [blocks]
    | right j =>
      have hj := j.2
      simp only [Fin.val_natAdd] at hi
      simp only [blocks, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
      by_cases h : i = j
      · rw [(hD i j).2 h, h, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne h]
        refine (hD i j).1 ?_
        have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
        rw [Fin.lt_def]
        omega

/- English proof (translation)
Introduce `i j` and use `⟨fun h => Matrix.one_apply_ne h.ne', fun h => by rw [h, Matrix.one_apply_eq]⟩`.
-/
theorem isUniUp_one : IsUniUp (1 : Mt g b) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by rw [h, Matrix.one_apply_eq]⟩

def dg (b : ℕ) (y : Gn g a) : Gn g (a + b) where
  val := blocks y.val 0 0 1
  inv := blocks (y⁻¹).val 0 0 1
  val_inv := by rw [blocks_mul]; simpa using blocks_one
  inv_val := by rw [blocks_mul]; simpa using blocks_one

/- English proof (translation)
Express the relevant statement in the definitionally equal form `blocks y.val 0 0 1 * x.val * blocks (y⁻¹).val 0 0 1 = _`. Rewrite using `[hx, blocks_mul, blocks_mul]`. Simplify using the standard rewrite rules.
-/
theorem conj_val (y : Gn g a) (x : Gn g (a + b)) {A : Mt g a} {B : Matrix (Fin a) (Fin b) (ZMod g)}
    {C : Matrix (Fin b) (Fin a) (ZMod g)} {D : Mt g b} (hx : x.val = blocks A B C D) :
    (dg b y * x * (dg b y)⁻¹).val = blocks (y.val * A * (y⁻¹).val) (y.val * B) (C * (y⁻¹).val) D := by
  change blocks y.val 0 0 1 * x.val * blocks (y⁻¹).val 0 0 1 = _
  rw [hx, blocks_mul, blocks_mul]
  simp

/- English proof (translation)
Unfold `res`. Use `congr 1`. Use `symm`. Use `Fintype.sum_equiv (MulAut.conj (dg b y)).toEquiv _ _ fun x => ?_` and prove the remaining obligations. Take `⟨A, B, C, D, hx⟩` from `exists_blocks x.val`.

Establish `e` using `conj_val y x hx`. Express the relevant statement in the definitionally equal form `_ = if InPar a (dg b y * x * (dg b y)⁻¹).val ∧ tl a (dg b y * x * (dg b y)⁻¹).val = (y * h * y⁻¹).val ∧ br a b (dg b y * x * (dg b y)⁻¹).val = u.val then F (dg b y * x * (dg b y)⁻¹) else 0`. Rewrite using `[e, hx, inPar_blocks, inPar_blocks, tl_blocks, tl_blocks, br_blocks, br_blocks]`. Establish `h1 : C * (y⁻¹).val = 0 ↔ C = 0`. Prove the components needed by the constructor for the conclusion.

Introduce `hc`. Use `congrArg (· * y.val) hc` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc]`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules.

Establish `h2 : y.val * A * (y⁻¹).val = (y * h * y⁻¹).val ↔ A = h.val`. Rewrite using `[Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]`. Simplify using `only [h1, h2]`. Use `split_ifs with hc`. Take `⟨rfl, -, rfl⟩` from `hc`.

Use `(hF _ _ ?_ ?_).symm` and prove the remaining obligations. Conclude with `inMir_blocks hb _ _ isUniUp_one`. Rewrite using `[hx]`. Conclude with `inMir_blocks hb _ _ hu`. Both sides reduce to the same expression.
-/
theorem res_conj (hb : 0 < b) {F : Gn g (a + b) → ℂ} (hF : IsMirClass F) (h y : Gn g a) (u : Gn g b)
    (hu : IsUniUp (u : Mt g b)) : res a b F (y * h * y⁻¹) u = res a b F h u := by
  unfold res
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dg b y)).toEquiv _ _ fun x => ?_
  obtain ⟨A, B, C, D, hx⟩ := exists_blocks x.val
  have e := conj_val y x hx
  change _ = if InPar a (dg b y * x * (dg b y)⁻¹).val ∧ tl a (dg b y * x * (dg b y)⁻¹).val = (y * h * y⁻¹).val ∧
    br a b (dg b y * x * (dg b y)⁻¹).val = u.val then F (dg b y * x * (dg b y)⁻¹) else 0
  rw [e, hx, inPar_blocks, inPar_blocks, tl_blocks, tl_blocks, br_blocks, br_blocks]
  have h1 : C * (y⁻¹).val = 0 ↔ C = 0 := by
    constructor
    · intro hc
      have := congrArg (· * y.val) hc
      simpa [Matrix.mul_assoc] using this
    · rintro rfl
      simp
  have h2 : y.val * A * (y⁻¹).val = (y * h * y⁻¹).val ↔ A = h.val := by
    rw [Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
  simp only [h1, h2]
  split_ifs with hc
  · obtain ⟨rfl, -, rfl⟩ := hc
    refine (hF _ _ ?_ ?_).symm
    · exact inMir_blocks hb _ _ isUniUp_one
    · rw [hx]
      exact inMir_blocks hb _ _ hu
  · rfl

/- English proof (translation)
Unfold `wh tr`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : IsUniUp (u : Mt g b)`. Rewrite using `[h u hu]`. Establish `: (eU g b ψ).coeff u = 0`.

Simplify using `only [eU, eDat, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_eq_zero, smul_zero]`. Introduce `v hv`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce and unpack `rfl`.

Conclude with `hu (Finset.mem_filter.1 hv).2`. Rewrite using `[this, zero_mul, zero_mul]`.
-/
theorem wh_congr (ψ : AddChar (ZMod g) ℂ) {α β : Gn g b → ℂ} (h : ∀ u : Gn g b, IsUniUp (u : Mt g b) → α u = β u) :
    wh ψ α = wh ψ β := by
  unfold wh tr
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : IsUniUp (u : Mt g b)
  · rw [h u hu]
  · have : (eU g b ψ).coeff u = 0 := by
      simp only [eU, eDat, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
        Finsupp.smul_apply, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_zero, smul_zero]
      intro v hv
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hu (Finset.mem_filter.1 hv).2
    rw [this, zero_mul, zero_mul]

/- English proof (translation)
Introduce `g _ ψ i n F hin hF h y`. Take `⟨b, rfl⟩` from `Nat.exists_eq_add_of_le hin.le`. Unfold `der`. Rewrite using `[Nat.add_sub_cancel_left]`. Conclude with `wh_congr ψ fun u hu => res_conj (by omega) hF h y u hu`.
-/
theorem isClass_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n →
    IsMirClass F → IsClass (der ψ i F) := by
  intro g _ ψ i n F hin hF h y
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hin.le
  unfold der
  rw [Nat.add_sub_cancel_left]
  exact wh_congr ψ fun u hu => res_conj (by omega) hF h y u hu

end GlobalTheory.GLm.DerClass
