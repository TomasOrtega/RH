import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace PhiModule

open Matrix Module

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {φ : R →+* R}
variable {M : Type*} [AddCommGroup M] [Module R M]

def IsPhiModule (Φ : M →ₛₗ[φ] M) : Prop := Submodule.span R (Set.range Φ) = ⊤

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phiMatrix (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) : Matrix ι ι R :=
  Matrix.of fun i j => b.repr (Φ (b j)) i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiMatrix_apply (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (i j : ι) :
    phiMatrix b Φ i j = b.repr (Φ (b j)) i := rfl

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr x]`. Use function extensionality and compare the values at `i`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, map_smul, Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul, mulVec, dotProduct, phiMatrix_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem repr_phi (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (x : M) :
    ⇑(b.repr (Φ x)) = (phiMatrix b Φ).mulVec (fun j => φ (b.repr x j)) := by
  conv_lhs => rw [← b.sum_repr x]
  funext i
  simp only [map_sum, LinearMap.map_smulₛₗ, map_smul, Finset.sum_apply, Finsupp.coe_finsetSum,
    Finsupp.smul_apply, smul_eq_mul, mulVec, dotProduct, phiMatrix_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr (Φ (b j))]`. Both sides reduce to the same expression.
-/
theorem phi_basis (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (j : ι) :
    Φ (b j) = ∑ i, phiMatrix b Φ i j • b i := by
  conv_lhs => rw [← b.sum_repr (Φ (b j))]
  rfl

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.range_comp_subset_range _ _))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← b.sum_repr x, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem span_range_eq (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    Submodule.span R (Set.range Φ) = Submodule.span R (Set.range (Φ ∘ b)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.range_comp_subset_range _ _))
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Rewrite using `[← isUnit_iff_isUnit_det, ← mulVec_surjective_iff_isUnit, IsPhiModule, span_range_eq b Φ, eq_top_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.mem_top (x := b.equivFun.symm v)))`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Use `congrArg b.equivFun hc` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[← this]`. Use function extensionality and compare the values at `i`. Simplify using `[Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm, Finsupp.single_apply]`.

Introduce `h x _`. Take `⟨c, hc⟩` from `h (b.equivFun x)`. Use `(Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, ?_⟩` and prove the remaining obligations. Apply `b.equivFun.injective` to reduce the goal to its premises. Rewrite using `[← hc]`.

Use function extensionality and compare the values at `i`. Simplify using `[Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm, Finsupp.single_apply]`.
-/
theorem isPhiModule_iff_isUnit_det (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    IsPhiModule Φ ↔ IsUnit (phiMatrix b Φ).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_surjective_iff_isUnit, IsPhiModule, span_range_eq b Φ,
    eq_top_iff]
  constructor
  · intro h v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.mem_top (x := b.equivFun.symm v)))
    refine ⟨c, ?_⟩
    have := congrArg b.equivFun hc
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    funext i
    simp [Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm,
      Finsupp.single_apply]
  · intro h x _
    obtain ⟨c, hc⟩ := h (b.equivFun x)
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, ?_⟩
    apply b.equivFun.injective
    rw [← hc]
    funext i
    simp [Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm,
      Finsupp.single_apply]

/- English proof (translation)
Use `congrArg (fun z => b.repr z i) (b'.sum_repr y)` as an intermediate fact. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem sum_repr_mul_repr (b b' : Basis ι R M) (y : M) (i : ι) :
    ∑ k, b.repr (b' k) i * b'.repr y k = b.repr y i := by
  have := congrArg (fun z => b.repr z i) (b'.sum_repr y)
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : (b.toMatrix b' * phiMatrix b' Φ) i j = b.repr (Φ (b' j)) i`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Basis.toMatrix_apply, phiMatrix_apply]`. Conclude with `sum_repr_mul_repr b b' _ i`.

Establish `h2 : (phiMatrix b Φ * (b.toMatrix b').map φ) i j = b.repr (Φ (b' j)) i`. Rewrite using `[repr_phi b Φ (b' j)]`. Simplify using `[Matrix.mul_apply, mulVec, dotProduct, Basis.toMatrix_apply]`. Rewrite using `[h1, h2]`.
-/
theorem toMatrix_mul_phiMatrix (b b' : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    b.toMatrix b' * phiMatrix b' Φ = phiMatrix b Φ * (b.toMatrix b').map φ := by
  ext i j
  have h1 : (b.toMatrix b' * phiMatrix b' Φ) i j = b.repr (Φ (b' j)) i := by
    rw [Matrix.mul_apply]
    simp only [Basis.toMatrix_apply, phiMatrix_apply]
    exact sum_repr_mul_repr b b' _ i
  have h2 : (phiMatrix b Φ * (b.toMatrix b').map φ) i j = b.repr (Φ (b' j)) i := by
    rw [repr_phi b Φ (b' j)]
    simp [Matrix.mul_apply, mulVec, dotProduct, Basis.toMatrix_apply]
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[← det_mul, toMatrix_mul_phiMatrix, det_mul, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_toMatrix_mul_det (b b' : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    (b.toMatrix b').det * (phiMatrix b' Φ).det = (phiMatrix b Φ).det * φ (b.toMatrix b').det := by
  rw [← det_mul, toMatrix_mul_phiMatrix, det_mul, RingHom.map_det]
  rfl

/- English proof (translation)
Use `isUnit_iff_exists_inv.2 ⟨(b'.toMatrix b).det, ?_⟩` and prove the remaining obligations. Rewrite using `[← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one]`.
-/
theorem isUnit_det_toMatrix (b b' : Basis ι R M) : IsUnit (b.toMatrix b').det := by
  refine isUnit_iff_exists_inv.2 ⟨(b'.toMatrix b).det, ?_⟩
  rw [← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiMatrix_apply]`.
-/
theorem phiMatrix_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (e : ι ≃ ι') (Φ : M →ₛₗ[φ] M) :
    phiMatrix (b.reindex e) Φ = (phiMatrix b Φ).submatrix e.symm e.symm := by
  ext i j
  simp [phiMatrix_apply]

/- English proof (translation)
Rewrite using `[phiMatrix_reindex, det_submatrix_equiv_self]`.
-/
theorem det_phiMatrix_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (e : ι ≃ ι') (Φ : M →ₛₗ[φ] M) :
    (phiMatrix (b.reindex e) Φ).det = (phiMatrix b Φ).det := by
  rw [phiMatrix_reindex, det_submatrix_equiv_self]

variable (R φ) in

structure UnitOrd where

  ord : Rˣ → ℤ
  map_mul : ∀ a b, ord (a * b) = ord a + ord b
  map_phi : ∀ a, ord (Units.map (φ : R →* R) a) = ord a

namespace UnitOrd

variable (v : UnitOrd R φ)

/- English proof (translation)
Use `v.map_mul 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem map_one : v.ord 1 = 0 := by
  have := v.map_mul 1 1
  rw [mul_one] at this
  omega

/- English proof (translation)
Use `v.map_mul a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, v.map_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem map_inv (a : Rˣ) : v.ord a⁻¹ = -v.ord a := by
  have := v.map_mul a a⁻¹
  rw [mul_inv_cancel, v.map_one] at this
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [v.map_one]`. Consider the case `succ n ih => rw [pow_succ, v.map_mul, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_pow (a : Rˣ) (n : ℕ) : v.ord (a ^ n) = n * v.ord a := by
  induction n with
  | zero => simp [v.map_one]
  | succ n ih => rw [pow_succ, v.map_mul, ih]; push_cast; ring

/- English proof (translation)
Use `congr 1`. Use `ext`. Simplify using `[h]`.
-/
theorem ord_unit_eq {x y : R} (hx : IsUnit x) (hy : IsUnit y) (h : x = y) :
    v.ord hx.unit = v.ord hy.unit := by
  congr 1; ext; simp [h]

/- English proof (translation)
Rewrite using `[← v.map_mul]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem ord_unit_mul {x y : R} (hx : IsUnit x) (hy : IsUnit y) :
    v.ord (hx.mul hy).unit = v.ord hx.unit + v.ord hy.unit := by
  rw [← v.map_mul]; congr 1; ext; simp

/- English proof (translation)
Rewrite using `[← v.map_phi hx.unit]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem ord_unit_phi {x : R} (hx : IsUnit x) :
    v.ord (hx.map φ).unit = v.ord hx.unit := by
  rw [← v.map_phi hx.unit]; congr 1; ext; simp

def pow (d : ℕ) : UnitOrd R (φ ^ d) where
  ord := v.ord
  map_mul := v.map_mul
  map_phi a := by
    induction d with
    | zero => congr 1
    | succ d ih =>
      have e : Units.map ((φ ^ (d + 1) : R →+* R) : R →* R) a =
          Units.map (φ : R →* R) (Units.map ((φ ^ d : R →+* R) : R →* R) a) := by
        ext; simp [pow_succ', RingHom.mul_def]
      rw [e, v.map_phi, ih]

end UnitOrd

variable (v : UnitOrd R φ) [Nontrivial R]

def degIn (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (h : IsPhiModule Φ) : ℤ :=
  v.ord ((isPhiModule_iff_isUnit_det b Φ).1 h).unit

/- English proof (translation)
Set `e : ι' ≃ ι` to `b'.indexEquiv b`. Establish `hre : degIn v b' Φ h = degIn v (b'.reindex e) Φ h` using `v.ord_unit_eq _ _ (det_phiMatrix_reindex b' e Φ).symm`. Rewrite using `[hre]`. Use `set b'' := b'.reindex e`. Establish `hP` using `isUnit_det_toMatrix b b''`.

Establish `hA` using `(isPhiModule_iff_isUnit_det b Φ).1 h`. Establish `hA'` using `(isPhiModule_iff_isUnit_det b'' Φ).1 h`. Establish `key : v.ord (hP.mul hA').unit = v.ord (hA.mul (hP.map φ)).unit` using `v.ord_unit_eq _ _ (det_toMatrix_mul_det b b'' Φ)`. Rewrite `key` using `[v.ord_unit_mul hP hA', v.ord_unit_mul hA (hP.map φ), v.ord_unit_phi hP]`. Unfold `degIn`.

Use linear arithmetic over natural numbers and integers.
-/
theorem degIn_eq {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (b' : Basis ι' R M)
    (Φ : M →ₛₗ[φ] M) (h : IsPhiModule Φ) : degIn v b Φ h = degIn v b' Φ h := by

  let e : ι' ≃ ι := b'.indexEquiv b
  have hre : degIn v b' Φ h = degIn v (b'.reindex e) Φ h :=
    v.ord_unit_eq _ _ (det_phiMatrix_reindex b' e Φ).symm
  rw [hre]
  set b'' := b'.reindex e
  have hP := isUnit_det_toMatrix b b''
  have hA := (isPhiModule_iff_isUnit_det b Φ).1 h
  have hA' := (isPhiModule_iff_isUnit_det b'' Φ).1 h
  have key : v.ord (hP.mul hA').unit = v.ord (hA.mul (hP.map φ)).unit :=
    v.ord_unit_eq _ _ (det_toMatrix_mul_det b b'' Φ)
  rw [v.ord_unit_mul hP hA', v.ord_unit_mul hA (hP.map φ), v.ord_unit_phi hP] at key
  unfold degIn
  omega

variable [Module.Free R M] [Module.Finite R M]

open Classical in

def deg (Φ : M →ₛₗ[φ] M) : ℤ :=
  if h : IsPhiModule Φ then degIn v (Module.Free.chooseBasis R M) Φ h else 0

/- English proof (translation)
Rewrite using `[deg, dif_pos h]`. Conclude with `degIn_eq v _ _ Φ h`.
-/
theorem deg_eq (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (h : IsPhiModule Φ) :
    deg v Φ = degIn v b Φ h := by
  classical
  rw [deg, dif_pos h]
  exact degIn_eq v _ _ Φ h

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiMatrix_apply]`.
-/
theorem phiMatrix_smul (b : Basis ι R M) (c : R) (Φ : M →ₛₗ[φ] M) :
    phiMatrix b (c • Φ) = c • phiMatrix b Φ := by
  ext i j
  simp [phiMatrix_apply]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite `h`, the goal using `[isPhiModule_iff_isUnit_det b]`. Rewrite using `[phiMatrix_smul, det_smul]`. Conclude with `(c.isUnit.pow _).mul h`.
-/
theorem isPhiModule_smul {Φ : M →ₛₗ[φ] M} (h : IsPhiModule Φ) (c : Rˣ) :
    IsPhiModule ((c : R) • Φ) := by
  let b := Module.Free.chooseBasis R M
  classical
  rw [isPhiModule_iff_isUnit_det b] at h ⊢
  rw [phiMatrix_smul, det_smul]
  exact (c.isUnit.pow _).mul h

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite using `[deg_eq v b _ (isPhiModule_smul h c), deg_eq v b _ h, degIn, degIn]`. Establish `hA` using `(isPhiModule_iff_isUnit_det b Φ).1 h`. Establish `e` using `v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (isPhiModule_smul h c)) ((c.isUnit.pow (Fintype.card (Module.Free.ChooseBasisIndex R M))).mul hA) (by rw [phiMatrix_smul, det_smul])`. Rewrite using `[e, v.ord_unit_mul (c.isUnit.pow _) hA, Module.finrank_eq_card_chooseBasisIndex]`.

Establish `: v.ord (c.isUnit.pow (Fintype.card (Module.Free.ChooseBasisIndex R M))).unit = v.ord (c ^ Fintype.card (Module.Free.ChooseBasisIndex R M))` using `by congr 1; ext; simp`. Rewrite using `[this, v.map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_smul {Φ : M →ₛₗ[φ] M} (h : IsPhiModule Φ) (c : Rˣ) :
    deg v ((c : R) • Φ) = deg v Φ + Module.finrank R M * v.ord c := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [deg_eq v b _ (isPhiModule_smul h c), deg_eq v b _ h, degIn, degIn]
  have hA := (isPhiModule_iff_isUnit_det b Φ).1 h
  have e := v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (isPhiModule_smul h c))
    ((c.isUnit.pow (Fintype.card (Module.Free.ChooseBasisIndex R M))).mul hA)
    (by rw [phiMatrix_smul, det_smul])
  rw [e, v.ord_unit_mul (c.isUnit.pow _) hA, Module.finrank_eq_card_chooseBasisIndex]
  have : v.ord (c.isUnit.pow (Fintype.card (Module.Free.ChooseBasisIndex R M))).unit =
      v.ord (c ^ Fintype.card (Module.Free.ChooseBasisIndex R M)) := by congr 1; ext; simp
  rw [this, v.map_pow]; ring

def iterate (Φ : M →ₛₗ[φ] M) (d : ℕ) : M →ₛₗ[φ ^ d] M where
  toFun := Φ^[d]
  map_add' x y := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [Function.iterate_succ_apply', ih, map_add]
  map_smul' r x := by
    induction d with
    | zero => simp
    | succ d ih =>
      simp only [Function.iterate_succ_apply', ih, LinearMap.map_smulₛₗ,
        pow_succ', RingHom.mul_def, RingHom.comp_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iterate_apply (Φ : M →ₛₗ[φ] M) (d : ℕ) (x : M) : iterate Φ d x = Φ^[d] x := rfl

/- English proof (translation)
The claim follows from `Function.iterate_succ_apply' _ _ _`.
-/
theorem iterate_succ_apply (Φ : M →ₛₗ[φ] M) (d : ℕ) (x : M) :
    iterate Φ (d + 1) x = Φ (iterate Φ d x) := Function.iterate_succ_apply' _ _ _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiMatrix_apply, iterate_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]`.
-/
theorem phiMatrix_iterate_zero (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    phiMatrix b (iterate Φ 0) = 1 := by
  ext i j
  simp [phiMatrix_apply, iterate_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[phiMatrix_apply, iterate_succ_apply, repr_phi]`. Simplify using `[Matrix.mul_apply, mulVec, dotProduct, phiMatrix_apply]`.
-/
theorem phiMatrix_iterate_succ (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (d : ℕ) :
    phiMatrix b (iterate Φ (d + 1)) = phiMatrix b Φ * (phiMatrix b (iterate Φ d)).map φ := by
  ext i j
  rw [phiMatrix_apply, iterate_succ_apply, repr_phi]
  simp [Matrix.mul_apply, mulVec, dotProduct, phiMatrix_apply]

/- English proof (translation)
The claim follows from `| 0 => by rw [phiMatrix_iterate_zero, det_one]; exact isUnit_one | d + 1 => by rw [phiMatrix_iterate_succ, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] exact h.mul ((isUnit_det_iterate b h d).map φ)`.
-/
theorem isUnit_det_iterate (b : Basis ι R M) {Φ : M →ₛₗ[φ] M} (h : IsUnit (phiMatrix b Φ).det) :
    ∀ d, IsUnit (phiMatrix b (iterate Φ d)).det
  | 0 => by rw [phiMatrix_iterate_zero, det_one]; exact isUnit_one
  | d + 1 => by
    rw [phiMatrix_iterate_succ, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact h.mul ((isUnit_det_iterate b h d).map φ)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite `h`, the goal using `[isPhiModule_iff_isUnit_det b]`. Conclude with `isUnit_det_iterate b h d`.
-/
theorem isPhiModule_iterate {Φ : M →ₛₗ[φ] M}
    (h : IsPhiModule Φ) (d : ℕ) : IsPhiModule (iterate Φ d) := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [isPhiModule_iff_isUnit_det b] at h ⊢
  exact isUnit_det_iterate b h d

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Simplify using `only [degIn, CharP.cast_eq_zero, zero_mul]`. Use `v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (h' 0)) isUnit_one (by rw [phiMatrix_iterate_zero, det_one])` as an intermediate fact. Rewrite using `[show (v.pow 0).ord = v.ord from rfl, this]`.

Establish `e : (isUnit_one : IsUnit (1 : R)).unit = 1` using `by ext; simp`. Rewrite using `[e, v.map_one]`. Consider the case `succ d ih`. Establish `hA` using `(isPhiModule_iff_isUnit_det b Φ).1 h`. Establish `hd` using `(isPhiModule_iff_isUnit_det b _).1 (h' d)`.

Establish `key` using `v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (h' (d + 1))) (hA.mul (hd.map φ)) (by rw [phiMatrix_iterate_succ, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det])`. Simplify using `only [degIn] at ih ⊢`. Rewrite using `[show (v.pow (d + 1)).ord = v.ord from rfl, key, v.ord_unit_mul hA (hd.map φ), v.ord_unit_phi hd]`. Rewrite `ih` using `[show (v.pow d).ord = v.ord from rfl]`. Rewrite using `[ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degIn_iterate (b : Basis ι R M) {Φ : M →ₛₗ[φ] M} (h : IsPhiModule Φ)
    (h' : ∀ d, IsPhiModule (iterate Φ d)) (d : ℕ) :
    degIn (v.pow d) b (iterate Φ d) (h' d) = d * degIn v b Φ h := by
  induction d with
  | zero =>
    simp only [degIn, CharP.cast_eq_zero, zero_mul]
    have := v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (h' 0)) isUnit_one
      (by rw [phiMatrix_iterate_zero, det_one])
    rw [show (v.pow 0).ord = v.ord from rfl, this]
    have e : (isUnit_one : IsUnit (1 : R)).unit = 1 := by ext; simp
    rw [e, v.map_one]
  | succ d ih =>
    have hA := (isPhiModule_iff_isUnit_det b Φ).1 h
    have hd := (isPhiModule_iff_isUnit_det b _).1 (h' d)
    have key := v.ord_unit_eq ((isPhiModule_iff_isUnit_det b _).1 (h' (d + 1))) (hA.mul (hd.map φ))
      (by rw [phiMatrix_iterate_succ, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det])
    simp only [degIn] at ih ⊢
    rw [show (v.pow (d + 1)).ord = v.ord from rfl, key, v.ord_unit_mul hA (hd.map φ),
      v.ord_unit_phi hd]
    rw [show (v.pow d).ord = v.ord from rfl] at ih
    rw [ih]; push_cast; ring

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite using `[deg_eq (v.pow d) b _ (isPhiModule_iterate h d), deg_eq v b _ h]`. Conclude with `degIn_iterate v b h (isPhiModule_iterate h) d`.
-/
theorem deg_iterate {Φ : M →ₛₗ[φ] M} (h : IsPhiModule Φ)
    (d : ℕ) : deg (v.pow d) (iterate Φ d) = d * deg v Φ := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [deg_eq (v.pow d) b _ (isPhiModule_iterate h d), deg_eq v b _ h]
  exact degIn_iterate v b h (isPhiModule_iterate h) d

end PhiModule

end GroundTheory.PAdicHodge
