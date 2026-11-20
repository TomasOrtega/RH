import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReal

section Point

open Matrix Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ComplexConjugate ComplexOrder

variable {n : ℕ}

/- English proof (translation)
Distinguish the cases in `h : Disjoint S T`. Take `⟨ε, e⟩` from `bas_mul h`. Rewrite using `[e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]`. Distinguish the cases in `hU : S ∪ T = U`. Conclude with `⟨ε, by simp [hU], fun _ => ⟨h, hU.symm⟩⟩`.

Conclude with `⟨0, by simp [Finsupp.single_apply, hU], fun h => (h rfl).elim⟩`. Use `ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h` as an intermediate fact. Establish `e : bas n S * bas n T = 0` using `this`. Conclude with `⟨0, by simp [e], fun h => (h rfl).elim⟩`.
-/
theorem repr_bas_mul (S T U : Finset (Fin (n + n))) : ∃ m : ℤ, (bas n).repr (bas n S * bas n T) U = m ∧
    (m ≠ 0 → Disjoint S T ∧ U = S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    by_cases hU : S ∪ T = U
    · exact ⟨ε, by simp [hU], fun _ => ⟨h, hU.symm⟩⟩
    · exact ⟨0, by simp [Finsupp.single_apply, hU], fun h => (h rfl).elim⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by simp [e], fun h => (h rfl).elim⟩

/- English proof (translation)
Use `conv_lhs => rw [← (bas n).sum_repr α, ← (bas n).sum_repr β]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem repr_mul (α β : Alt n) (U : Finset (Fin (n + n))) : (bas n).repr (α * β) U =
    ∑ S, ∑ T, (bas n).repr α S * (bas n).repr β T * (bas n).repr (bas n S * bas n T) U := by
  conv_lhs => rw [← (bas n).sum_repr α, ← (bas n).sum_repr β]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `S h` and use `(h (by simp)).elim`.
-/
theorem isType_zero (p q : ℕ) : IsType p q (0 : Alt n) := fun S h => (h (by simp)).elim

/- English proof (translation)
Introduce `S hS` and use `by by_cases e : (bas n).repr α S = 0 · exact h' S fun e' => hS (by simp [e, e']) · exact h S e`.
-/
theorem isType_add {p q : ℕ} {α β : Alt n} (h : IsType p q α) (h' : IsType p q β) : IsType p q (α + β) := fun S hS => by
  by_cases e : (bas n).repr α S = 0
  · exact h' S fun e' => hS (by simp [e, e'])
  · exact h S e

/- English proof (translation)
Introduce `S hS` and use `h S fun e => hS (by simp [e])`.
-/
theorem isType_smul {p q : ℕ} {α : Alt n} (c : ℂ) (h : IsType p q α) : IsType p q (c • α) := fun S hS =>
  h S fun e => hS (by simp [e])

/- English proof (translation)
Introduce `U hU` and use `by rw [repr_mul] at hU obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS obtain ⟨m, e, hm⟩ := repr_bas_mul S T U obtain ⟨hd, rfl⟩ := hm fun h0 => hT (by rw [e, h0]; simp) obtain ⟨a, b⟩ := h S fun h0 => hT (by …`.
-/
theorem isType_mul {p q p' q' : ℕ} {α β : Alt n} (h : IsType p q α) (h' : IsType p' q' β) :
    IsType (p + p') (q + q') (α * β) := fun U hU => by
  rw [repr_mul] at hU
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨m, e, hm⟩ := repr_bas_mul S T U
  obtain ⟨hd, rfl⟩ := hm fun h0 => hT (by rw [e, h0]; simp)
  obtain ⟨a, b⟩ := h S fun h0 => hT (by rw [h0]; simp)
  obtain ⟨a', b'⟩ := h' T fun h0 => hT (by rw [h0]; simp)
  rw [Finset.filter_union, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd), a, b, a', b']
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Introduce `S hS` and use `by rw [dz, ← bas_singleton] at hS obtain rfl : {finSumFinEquiv (.inl a)} = S := by by_contra h simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_left] at hS simp [Finset.filter_singleton]`.
-/
theorem isType_dz (a : Fin n) : IsType 1 0 (dz a) := fun S hS => by
  rw [dz, ← bas_singleton] at hS
  obtain rfl : {finSumFinEquiv (.inl a)} = S := by
    by_contra h
    simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_left] at hS
  simp [Finset.filter_singleton]

/- English proof (translation)
Introduce `S hS` and use `by rw [dzb, ← bas_singleton] at hS obtain rfl : {finSumFinEquiv (.inr a)} = S := by by_contra h simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_right] at hS simp [Finset.filter_singleton]`.
-/
theorem isType_dzb (a : Fin n) : IsType 0 1 (dzb a) := fun S hS => by
  rw [dzb, ← bas_singleton] at hS
  obtain rfl : {finSumFinEquiv (.inr a)} = S := by
    by_contra h
    simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_right] at hS
  simp [Finset.filter_singleton]

def IsConj (α β : Alt n) : Prop := ∀ S, (bas n).repr β S = conj ((bas n).repr α S)

/- English proof (translation)
Introduce `S` and use `by simp [h S, h' S]`.
-/
theorem IsConj.add {α β α' β' : Alt n} (h : IsConj α β) (h' : IsConj α' β') : IsConj (α + α') (β + β') := fun S => by
  simp [h S, h' S]

/- English proof (translation)
Introduce `S` and use `by simp [h S]`.
-/
theorem IsConj.smul {α β : Alt n} (c : ℂ) (h : IsConj α β) : IsConj (c • α) (conj c • β) := fun S => by
  simp [h S]

/- English proof (translation)
Introduce `U` and use `by rw [repr_mul, repr_mul, map_sum] refine Finset.sum_congr rfl fun S _ => ?_ rw [map_sum] refine Finset.sum_congr rfl fun T _ => ?_ obtain ⟨m, e, -⟩ := repr_bas_mul S T U rw [e, h S, h' T, map_mul, map_mul, map_intCast]`.
-/
theorem IsConj.mul {α β α' β' : Alt n} (h : IsConj α β) (h' : IsConj α' β') : IsConj (α * α') (β * β') := fun U => by
  rw [repr_mul, repr_mul, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  obtain ⟨m, e, -⟩ := repr_bas_mul S T U
  rw [e, h S, h' T, map_mul, map_mul, map_intCast]

/- English proof (translation)
Introduce `S` and use `by simp only [Module.Basis.repr_self, Finsupp.single_apply] split_ifs <;> simp`.
-/
theorem isConj_bas (T : Finset (Fin (n + n))) : IsConj (bas n T) (bas n T) := fun S => by
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsConj (dz x.1 * dzb x.2) (dz x.1 * dzb x.2)`. Rewrite using `[dz, dzb, ← bas_singleton, ← bas_singleton]`. Conclude with `(isConj_bas _).mul (isConj_bas _)`.
-/
theorem isConj_sym (x : Fin n × Fin n) : IsConj (sym x : Alt n) (sym x : Alt n) := by
  change IsConj (dz x.1 * dzb x.2) (dz x.1 * dzb x.2)
  rw [dz, dzb, ← bas_singleton, ← bas_singleton]
  exact (isConj_bas _).mul (isConj_bas _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `swap (dz x.2 * dzb x.1) = -(dz x.1 * dzb x.2)`. Rewrite using `[map_mul, (swap_dz _).1, (swap_dz _).2, dz, dzb]`. Conclude with `eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)`.
-/
theorem swap_sym (x : Fin n × Fin n) : swap (sym x.swap : Alt n) = -(sym x : Alt n) := by
  change swap (dz x.2 * dzb x.1) = -(dz x.1 * dzb x.2)
  rw [map_mul, (swap_dz _).1, (swap_dz _).2, dz, dzb]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

def star (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
  eval₂Hom (C.comp (starRingEnd ℂ)) fun x => X x.swap

/- English proof (translation)
Simplify using `[star]`.
-/
theorem star_C (c : ℂ) : star n (C c) = C (conj c) := by simp [star]

/- English proof (translation)
Simplify using `[star]`.
-/
theorem star_X (x : Fin n × Fin n) : star n (X x) = X x.swap := by simp [star]

/- English proof (translation)
Rewrite `hP` using `[← mem_homogeneousSubmodule, ← homogeneousSubmodule_one_pow]`. Proceed by induction on `hP using Submodule.pow_induction_on_left' with`. Consider the case `algebraMap r`. Establish `h1` using `isType_isReal_const (n := n) 1`. Rewrite `h1` using `[Complex.ofReal_one, map_one]`.

Establish `h2 : IsConj (1 : Alt n) 1` using `by rw [← bas_empty]; exact isConj_bas _`. Rewrite using `[MvPolynomial.algebraMap_eq, star_C, aeval_C, aeval_C, pow_zero, one_smul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_smul, Subalgebra.coe_one, map_smul, map_one]`. Conclude with `⟨isType_smul _ h1.1, h2.smul _⟩`. Consider the case `add x y i hx hy ihx ihy`. Simplify using `only [map_add, Subalgebra.coe_add, smul_add]`.

Conclude with `⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩`. Consider the case `mem_mul m hm i x hx ih`. Establish `key : IsType 1 1 ((aeval sym m : Ev n) : Alt n) ∧ IsConj ((aeval sym m : Ev n) : Alt n) (-swap ((aeval sym (star n m) : Ev n) : Alt n))`. Rewrite `hm` using `[homogeneousSubmodule_one_eq_span_X]`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨y, rfl⟩` from `hz`. Rewrite using `[star_X, aeval_X, aeval_X, swap_sym, neg_neg]`. Conclude with `⟨isType_mul (isType_dz _) (isType_dzb _), isConj_sym y⟩`. Consider the case `zero => simpa using ⟨isType_zero 1 1, fun S => by simp⟩`.

Consider the case `add x y _ _ ihx ihy`. Simplify using `only [map_add, Subalgebra.coe_add, neg_add]`. Conclude with `⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩`. Consider the case `smul c x _ ih`. Rewrite using `[← C_mul', map_mul, map_mul, map_mul, star_C, aeval_C, aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, ← smul_neg]`.

Conclude with `⟨isType_smul _ ih.1, ih.2.smul _⟩`. Simplify using `only [map_mul, Subalgebra.coe_mul]`. Use `⟨by simpa [add_comm] using isType_mul key.1 ih.1, ?_⟩` and prove the remaining obligations. Use `key.2.mul ih.2` as an intermediate fact. Rewrite `this` using `[mul_smul_comm, neg_mul, smul_neg, ← neg_smul, ← mul_neg_one, ← pow_succ]`. Then use the resulting hypothesis.
-/
theorem homog {j : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous j) :
    IsType j j ((aeval sym P : Ev n) : Alt n) ∧
      IsConj ((aeval sym P : Ev n) : Alt n) ((-1 : ℂ) ^ j • swap ((aeval sym (star n P) : Ev n) : Alt n)) := by
  rw [← mem_homogeneousSubmodule, ← homogeneousSubmodule_one_pow] at hP
  induction hP using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have h1 := isType_isReal_const (n := n) 1
    rw [Complex.ofReal_one, map_one] at h1
    have h2 : IsConj (1 : Alt n) 1 := by rw [← bas_empty]; exact isConj_bas _
    rw [MvPolynomial.algebraMap_eq, star_C, aeval_C, aeval_C, pow_zero, one_smul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_smul, Subalgebra.coe_one, map_smul, map_one]
    exact ⟨isType_smul _ h1.1, h2.smul _⟩
  | add x y i hx hy ihx ihy =>
    simp only [map_add, Subalgebra.coe_add, smul_add]
    exact ⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩
  | mem_mul m hm i x hx ih =>
    have key : IsType 1 1 ((aeval sym m : Ev n) : Alt n) ∧
        IsConj ((aeval sym m : Ev n) : Alt n) (-swap ((aeval sym (star n m) : Ev n) : Alt n)) := by
      rw [homogeneousSubmodule_one_eq_span_X] at hm
      induction hm using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, rfl⟩ := hz
        rw [star_X, aeval_X, aeval_X, swap_sym, neg_neg]
        exact ⟨isType_mul (isType_dz _) (isType_dzb _), isConj_sym y⟩
      | zero => simpa using ⟨isType_zero 1 1, fun S => by simp⟩
      | add x y _ _ ihx ihy =>
        simp only [map_add, Subalgebra.coe_add, neg_add]
        exact ⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩
      | smul c x _ ih =>
        rw [← C_mul', map_mul, map_mul, map_mul, star_C, aeval_C, aeval_C, ← Algebra.smul_def, ← Algebra.smul_def,
          Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, ← smul_neg]
        exact ⟨isType_smul _ ih.1, ih.2.smul _⟩
    simp only [map_mul, Subalgebra.coe_mul]
    refine ⟨by simpa [add_comm] using isType_mul key.1 ih.1, ?_⟩
    have := key.2.mul ih.2
    rwa [mul_smul_comm, neg_mul, smul_neg, ← neg_smul, ← mul_neg_one, ← pow_succ] at this

variable {r : Type} [Fintype r] [DecidableEq r]

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b : 2`. Apply the tactic sequence `by_cases h : a = b <;> simp [h]`.
-/
theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

/- English proof (translation)
Establish `hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1`. Rewrite using `[← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev]`. Establish `e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q)ᵀ.map Polynomial.C = (P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C)ᵀ`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, transpose_sub, transpose_one, transpose_smul, transpose_map]`.

Rewrite using `[e, det_transpose, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]`.
-/
theorem charpolyRev_conj {R : Type} [CommRing R] (P Q M : Matrix r r R) (hPQ : P * Q = 1) :
    (P * M * Q)ᵀ.charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q)ᵀ.map Polynomial.C
      = (P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C)ᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, transpose_sub, transpose_one, transpose_smul, transpose_map]
  rw [e, det_transpose, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

/- English proof (translation)
Establish `hu' : IsUnit (H v)ᵀ.det` using `by rwa [det_transpose]`. Establish `hc (ξ η : V n) : (curv H v ξ η)ᴴ = (H v)ᵀ * curv H v η ξ * (H v)ᵀ⁻¹`. Rewrite using `[← adj_curv h hh hu ξ η, adj]`. Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu', mul_nonsing_inv _ hu', Matrix.mul_one]`. Establish `hP : (H v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * ((H v)ᵀ⁻¹).map C = 1`.

Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu', Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e0 : curvPoly H v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv H v (coordVec a) (coordVec b)).map C`. Use extensionality with `i k : 2`. Simplify using `[curvPoly, Matrix.sum_apply, mul_comm]`. Establish `e : (-curvPoly H v).map (star n) = ((H v)ᵀ.map C * (-curvPoly H v) * ((H v)ᵀ⁻¹).map C)ᵀ` using `by conv_rhs => rw [e0, Finset.sum_comm]`.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← hc]`. Use extensionality with `i k : 2`. Simplify using `[curvPoly, Matrix.sum_apply, star_C, star_X, mul_comm]`. Rewrite using `[chernPoly, ← Polynomial.coeff_map, charpolyRev_map, e, charpolyRev_conj _ _ _ hP]`.
-/
theorem star_chernPoly {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 2 H v) (hh : ∀ᶠ x in 𝓝 v, (H x).IsHermitian)
    (hu : IsUnit (H v).det) (j : ℕ) : star n (chernPoly H v j) = chernPoly H v j := by
  have hu' : IsUnit (H v)ᵀ.det := by rwa [det_transpose]
  have hc (ξ η : V n) : (curv H v ξ η)ᴴ = (H v)ᵀ * curv H v η ξ * (H v)ᵀ⁻¹ := by
    rw [← adj_curv h hh hu ξ η, adj]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu', mul_nonsing_inv _ hu', Matrix.mul_one]
  have hP : (H v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * ((H v)ᵀ⁻¹).map C = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu', Matrix.map_one _ (map_zero _) (map_one _)]
  have e0 : curvPoly H v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv H v (coordVec a) (coordVec b)).map C := by
    ext i k : 2
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have e : (-curvPoly H v).map (star n) = ((H v)ᵀ.map C * (-curvPoly H v) * ((H v)ᵀ⁻¹).map C)ᵀ := by
    conv_rhs => rw [e0, Finset.sum_comm]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, ← hc]
    ext i k : 2
    simp [curvPoly, Matrix.sum_apply, star_C, star_X, mul_comm]
  rw [chernPoly, ← Polynomial.coeff_map, charpolyRev_map, e, charpolyRev_conj _ _ _ hP]

/- English proof (translation)
Take `⟨h1, h2⟩` from `homog (ChernCoord.chernPoly_isHomogeneous H v j)`. Rewrite `h2` using `[star_chernPoly h hh hu]`. Rewrite using `[chernAt, Subalgebra.coe_smul]`. Use `⟨isType_smul _ h1, ?_⟩` and prove the remaining obligations. Establish `h3` using `h2.smul (kappa ^ j)`.

Establish `hk : conj kappa * -1 = kappa` using `by simp [kappa, neg_div, map_ofNat]`. Rewrite `h3` using `[smul_smul, map_pow, ← mul_pow, hk, ← map_smul]`. Conclude with `h3`.
-/
theorem chernAt_isType_isReal {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 2 H v)
    (hh : ∀ᶠ x in 𝓝 v, (H x).IsHermitian) (hu : IsUnit (H v).det) (j : ℕ) :
    IsType j j (chernAt H v j : Alt n) ∧ IsReal (chernAt H v j : Alt n) := by
  obtain ⟨h1, h2⟩ := homog (ChernCoord.chernPoly_isHomogeneous H v j)
  rw [star_chernPoly h hh hu] at h2
  rw [chernAt, Subalgebra.coe_smul]
  refine ⟨isType_smul _ h1, ?_⟩
  have h3 := h2.smul (kappa ^ j)
  have hk : conj kappa * -1 = kappa := by simp [kappa, neg_div, map_ofNat]
  rw [smul_smul, map_pow, ← mul_pow, hk, ← map_smul] at h3
  exact h3

end Point

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical ComplexOrder

/- English proof (translation)
Introduce `k _ X _ p D hX σ E h H fl`. Establish `hS` using `lineSC_shortExact fl`. Establish `hsm (a : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) : (hX.atlas σ).SmoothOn (ptsIn p σ a.U) fun y => (h.met σ).gram a.frame y i j` using `hX.smoothOn (fun _ => (H σ).gram a.frame) i j`. Establish `hpos (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U)` using `(h.met σ).posDef_gram_frame hS a hy`. Establish `hhol (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) : (hX.atlas σ).HolOn (ptsIn p σ a.U ∩ ptsIn p σ b.U) fun y => a.tr p σ hS b y i j` using `fun c => (c.holo _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩`.

Establish `htr (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U ∩ ptsIn p σ b.U)` using `Met.gram_frame_trans (S := lineSC fl) (r := 1) (s := 1) (h.met σ) hS a b hy.1 hy.2`. Establish `hcov (y : CxPts p σ) : ∃ a : VBExt.AdaptedChart (lineSC fl) 1 1, y ∈ ptsIn p σ a.U` using `⟨_, mem_frameAt fl y⟩`. Take `⟨h1, h2⟩` from `GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) (fun a : VBExt.AdaptedChart (lineSC fl) 1 1 => ptsIn p σ a.U) (fun _ => isOpen_ptsIn _) hcov (fun a b => a.tr p σ hS b) hhol (fun a => (h.met σ).gram a.frame) hsm hpos htr 2`. Take `⟨h3, h4, h5⟩` from `h2 (fld _ (c2F hX σ h fl)) fun a x hx => congrArg Subtype.val (h1 _ a x (mem_frameAt fl x.pt) hx)`. Use `⟨⟨h3, fun x => ?_⟩, h4, h5⟩` and prove the remaining obligations.

Establish `hop : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U)` using `x.ch.isOpen_inter_preimage_symm (isOpen_ptsIn _)`. Establish `hx : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U` using `⟨x.ch.map_source x.2, by simp only [Set.mem_preimage]; rw [x.ch.left_inv x.2]; exact mem_frameAt fl x.pt⟩`. Conclude with `chernAt_isType_isReal (H := fun v => (h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm v)) (fun i j => ((hsm _ i j x.1.1).contDiffAt (hop.mem_nhds hx)).of_le (by norm_cast)) (Filter.eventually_of_mem (hop.mem_nhds hx) fun v hv => (hpos _ _ hv.2).isHermitian) ((Matrix.isUnit_iff_i …`.
-/
theorem c2F_isRealForm_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧ (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 := by
  intro k _ X _ p D hX σ E h H fl
  have hS := lineSC_shortExact fl
  have hsm (a : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) :
      (hX.atlas σ).SmoothOn (ptsIn p σ a.U) fun y => (h.met σ).gram a.frame y i j :=
    hX.smoothOn (fun _ => (H σ).gram a.frame) i j
  have hpos (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U) :=
    (h.met σ).posDef_gram_frame hS a hy
  have hhol (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) :
      (hX.atlas σ).HolOn (ptsIn p σ a.U ∩ ptsIn p σ b.U) fun y => a.tr p σ hS b y i j :=
    fun c => (c.holo _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  have htr (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U ∩ ptsIn p σ b.U) :=
    Met.gram_frame_trans (S := lineSC fl) (r := 1) (s := 1) (h.met σ) hS a b hy.1 hy.2
  have hcov (y : CxPts p σ) : ∃ a : VBExt.AdaptedChart (lineSC fl) 1 1, y ∈ ptsIn p σ a.U := ⟨_, mem_frameAt fl y⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) (fun a : VBExt.AdaptedChart (lineSC fl) 1 1 => ptsIn p σ a.U)
    (fun _ => isOpen_ptsIn _) hcov (fun a b => a.tr p σ hS b) hhol
    (fun a => (h.met σ).gram a.frame) hsm hpos htr 2
  obtain ⟨h3, h4, h5⟩ := h2 (fld _ (c2F hX σ h fl)) fun a x hx =>
    congrArg Subtype.val (h1 _ a x (mem_frameAt fl x.pt) hx)
  refine ⟨⟨h3, fun x => ?_⟩, h4, h5⟩
  have hop : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U) :=
    x.ch.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hx : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage]; rw [x.ch.left_inv x.2]; exact mem_frameAt fl x.pt⟩
  exact chernAt_isType_isReal (H := fun v => (h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm v))
    (fun i j => ((hsm _ i j x.1.1).contDiffAt (hop.mem_nhds hx)).of_le (by norm_cast))
    (Filter.eventually_of_mem (hop.mem_nhds hx) fun v hv => (hpos _ _ hv.2).isHermitian)
    ((Matrix.isUnit_iff_isUnit_det _).1 (hpos _ _ hx.2).isUnit) 2

end GlobalTheory.ChernReal
