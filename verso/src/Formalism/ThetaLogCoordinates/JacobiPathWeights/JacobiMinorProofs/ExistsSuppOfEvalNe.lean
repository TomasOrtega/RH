import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

section Laurent

variable {A : Type*} [CommRing A] [IsDomain A]

/- English proof (translation)
Rewrite using `[Finsupp.support_nonempty_iff]`. Simplify using `using hx`.
-/
theorem lp_supp_nonempty {x : LaurentPolynomial A} (hx : x ≠ 0) : x.coeff.support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  simpa using hx

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Take `⟨a, ha⟩` from `Finset.min_of_nonempty (lp_supp_nonempty hx)`.

Take `⟨b, hb⟩` from `Finset.min_of_nonempty (lp_supp_nonempty hy)`. Rewrite using `[ha, hb]`. Establish `ha'` using `Finset.mem_of_min ha`. Establish `hb'` using `Finset.mem_of_min hb`. Establish `hc : (x * y).coeff (a + b) = x.coeff a * y.coeff b`.

Apply `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd` to reduce the goal to its premises. Introduce `a' b' ha'' hb'' h`. Establish `h1 : a ≤ a'` using `Finset.min_le_of_eq ha'' ha`. Establish `h2 : b ≤ b'` using `Finset.min_le_of_eq hb'' hb`. Apply the tactic sequence `constructor <;> omega`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← WithTop.coe_add]`. Apply `Finset.min_le` to reduce the goal to its premises. Rewrite using `[Finsupp.mem_support_iff, hc]`. Conclude with `mul_ne_zero (Finsupp.mem_support_iff.mp ha') (Finsupp.mem_support_iff.mp hb')`.

Apply `Finset.le_min` to reduce the goal to its premises. Introduce `c hc'`. Use `AddMonoidAlgebra.support_coeff_mul_subset x y hc'` as an intermediate fact. Take `⟨a', ha'', b', hb'', rfl⟩` from `Finset.mem_add.mp this`. Establish `h1 : a ≤ a'` using `Finset.min_le_of_eq ha'' ha`.

Establish `h2 : b ≤ b'` using `Finset.min_le_of_eq hb'' hb`. Rewrite using `[← WithTop.coe_add]`. Conclude with `WithTop.coe_le_coe.mpr (by omega)`.
-/
theorem lp_min_mul (x y : LaurentPolynomial A) :
    (x * y).coeff.support.min = x.coeff.support.min + y.coeff.support.min := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty (lp_supp_nonempty hx)
  obtain ⟨b, hb⟩ := Finset.min_of_nonempty (lp_supp_nonempty hy)
  rw [ha, hb]
  have ha' := Finset.mem_of_min ha
  have hb' := Finset.mem_of_min hb
  have hc : (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
    apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
    intro a' b' ha'' hb'' h
    have h1 : a ≤ a' := Finset.min_le_of_eq ha'' ha
    have h2 : b ≤ b' := Finset.min_le_of_eq hb'' hb
    constructor <;> omega
  apply le_antisymm
  · rw [← WithTop.coe_add]
    apply Finset.min_le
    rw [Finsupp.mem_support_iff, hc]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha') (Finsupp.mem_support_iff.mp hb')
  · apply Finset.le_min
    intro c hc'
    have := AddMonoidAlgebra.support_coeff_mul_subset x y hc'
    obtain ⟨a', ha'', b', hb'', rfl⟩ := Finset.mem_add.mp this
    have h1 : a ≤ a' := Finset.min_le_of_eq ha'' ha
    have h2 : b ≤ b' := Finset.min_le_of_eq hb'' hb
    rw [← WithTop.coe_add]
    exact WithTop.coe_le_coe.mpr (by omega)

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Take `⟨a, ha⟩` from `Finset.max_of_nonempty (lp_supp_nonempty hx)`.

Take `⟨b, hb⟩` from `Finset.max_of_nonempty (lp_supp_nonempty hy)`. Rewrite using `[ha, hb]`. Establish `ha'` using `Finset.mem_of_max ha`. Establish `hb'` using `Finset.mem_of_max hb`. Establish `hc : (x * y).coeff (a + b) = x.coeff a * y.coeff b`.

Apply `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd` to reduce the goal to its premises. Introduce `a' b' ha'' hb'' h`. Establish `h1 : a' ≤ a` using `Finset.le_max_of_eq ha'' ha`. Establish `h2 : b' ≤ b` using `Finset.le_max_of_eq hb'' hb`. Apply the tactic sequence `constructor <;> omega`.

Apply `le_antisymm` to reduce the goal to its premises. Apply `Finset.max_le` to reduce the goal to its premises. Introduce `c hc'`. Use `AddMonoidAlgebra.support_coeff_mul_subset x y hc'` as an intermediate fact. Take `⟨a', ha'', b', hb'', rfl⟩` from `Finset.mem_add.mp this`.

Establish `h1 : a' ≤ a` using `Finset.le_max_of_eq ha'' ha`. Establish `h2 : b' ≤ b` using `Finset.le_max_of_eq hb'' hb`. Rewrite using `[← WithBot.coe_add]`. Conclude with `WithBot.coe_le_coe.mpr (by omega)`. Rewrite using `[← WithBot.coe_add]`.

Apply `Finset.le_max` to reduce the goal to its premises. Rewrite using `[Finsupp.mem_support_iff, hc]`. Conclude with `mul_ne_zero (Finsupp.mem_support_iff.mp ha') (Finsupp.mem_support_iff.mp hb')`.
-/
theorem lp_max_mul (x y : LaurentPolynomial A) :
    (x * y).coeff.support.max = x.coeff.support.max + y.coeff.support.max := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty (lp_supp_nonempty hx)
  obtain ⟨b, hb⟩ := Finset.max_of_nonempty (lp_supp_nonempty hy)
  rw [ha, hb]
  have ha' := Finset.mem_of_max ha
  have hb' := Finset.mem_of_max hb
  have hc : (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
    apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
    intro a' b' ha'' hb'' h
    have h1 : a' ≤ a := Finset.le_max_of_eq ha'' ha
    have h2 : b' ≤ b := Finset.le_max_of_eq hb'' hb
    constructor <;> omega
  apply le_antisymm
  · apply Finset.max_le
    intro c hc'
    have := AddMonoidAlgebra.support_coeff_mul_subset x y hc'
    obtain ⟨a', ha'', b', hb'', rfl⟩ := Finset.mem_add.mp this
    have h1 : a' ≤ a := Finset.le_max_of_eq ha'' ha
    have h2 : b' ≤ b := Finset.le_max_of_eq hb'' hb
    rw [← WithBot.coe_add]
    exact WithBot.coe_le_coe.mpr (by omega)
  · rw [← WithBot.coe_add]
    apply Finset.le_max
    rw [Finsupp.mem_support_iff, hc]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha') (Finsupp.mem_support_iff.mp hb')

omit [IsDomain A] in
/- English proof (translation)
Apply `Finset.le_min` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[AddMonoidAlgebra.coeff_add]`. Break down `Finset.mem_union.mp (Finsupp.support_add hc) with h | h` into its components or cases. Conclude with `min_le_of_left_le (Finset.min_le h)`.

Conclude with `min_le_of_right_le (Finset.min_le h)`.
-/
theorem lp_min_add (x y : LaurentPolynomial A) :
    min x.coeff.support.min y.coeff.support.min ≤ (x + y).coeff.support.min := by
  classical
  apply Finset.le_min
  intro c hc
  rw [AddMonoidAlgebra.coeff_add] at hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with h | h
  · exact min_le_of_left_le (Finset.min_le h)
  · exact min_le_of_right_le (Finset.min_le h)

omit [IsDomain A] in
/- English proof (translation)
Apply `Finset.max_le` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[AddMonoidAlgebra.coeff_add]`. Break down `Finset.mem_union.mp (Finsupp.support_add hc) with h | h` into its components or cases. Conclude with `le_max_of_le_left (Finset.le_max h)`.

Conclude with `le_max_of_le_right (Finset.le_max h)`.
-/
theorem lp_max_add (x y : LaurentPolynomial A) :
    (x + y).coeff.support.max ≤ max x.coeff.support.max y.coeff.support.max := by
  classical
  apply Finset.max_le
  intro c hc
  rw [AddMonoidAlgebra.coeff_add] at hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with h | h
  · exact le_max_of_le_left (Finset.le_max h)
  · exact le_max_of_le_right (Finset.le_max h)

omit [IsDomain A] in
/- English proof (translation)
The claim follows from `LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero hp m`.
-/
theorem lp_supp_CT {p : A} (hp : p ≠ 0) (m : ℤ) :
    (LaurentPolynomial.C p * LaurentPolynomial.T m).coeff.support = {m} :=
  LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero hp m

omit [IsDomain A] in
/- English proof (translation)
Use `lp_supp_CT hp 0` as an intermediate fact. Simplify using `using this`.
-/
theorem lp_supp_C {p : A} (hp : p ≠ 0) :
    (LaurentPolynomial.C p).coeff.support = {0} := by
  have := lp_supp_CT hp 0
  simpa using this

omit [IsDomain A] in
/- English proof (translation)
Rewrite using `[LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
theorem lp_coeff_TC (p : A) (m j : ℤ) :
    (LaurentPolynomial.T m * LaurentPolynomial.C p).coeff j = if m = j then p else 0 := by
  rw [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]

omit [IsDomain A] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih]`.
-/
theorem lp_coeff_sum {κ : Type*} (s : Finset κ) (f : κ → LaurentPolynomial A) (j : ℤ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih]

omit [IsDomain A] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]`.
-/
theorem prod_laurent_T {κ : Type*} (s : Finset κ) (f : κ → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (f i) : LaurentPolynomial A) = LaurentPolynomial.T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]

end Laurent

section Sharp

variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]

def wtX (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) : LVar ι ζ n → ℤ
  | Sum.inl (i, a) =>
    if i ∈ S then
      (if (if last then a.val + 1 = n else a.val = 0) then (if isVec i then 1 else -1) else 0)
    else 0
  | Sum.inr _ => 0

def wExp (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) (e : LVar ι ζ n →₀ ℕ) : ℤ :=
  ∑ x ∈ e.support, (e x : ℤ) * wtX isVec S last x

abbrev cc (τ : Type*) (L : Type*) [CommRing L] : L →+* LaurentPolynomial (MvPolynomial τ L) :=
  (LaurentPolynomial.C).comp C

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjS_eq (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    conjS τ g gi last e = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := rfl

/- English proof (translation)
Rewrite using `[conjS_eq, Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`.
-/
theorem conjS_mul (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    conjS τ g gi last e * g.map (cc τ L) = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e := by
  rw [conjS_eq, Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one]

/- English proof (translation)
Rewrite using `[conjS_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`.
-/
theorem mul_conjS (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    gi.map (cc τ L) * conjS τ g gi last e = diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := by
  rw [conjS_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def tw (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) L →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom (cc _ L) fun x =>
    LaurentPolynomial.T (wtX isVec S last x) * LaurentPolynomial.C (sharpHom isVec S g gi (X x))

/- English proof (translation)
Simplify using `[conjAct]`.
-/
theorem conjAct_C {k : Type*} [CommRing k] (φ : k →+* L) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (c : k) :
    conjAct (ζ := ζ) φ isVec S g gi last (C c) = cc _ L (φ c) := by
  simp [conjAct]

/- English proof (translation)
It suffices to establish `hh : (conjAct (ζ` using `ζ) (RingHom.id L) isVec S g gi last).comp (sharpHom isVec S g gi).toRingHom = tw isVec S g gi last from by`. Rewrite using `[← hh]`. Both sides reduce to the same expression. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Simplify using `[tw, conjAct_C, sharpHom]`. Introduce `x`. Break down `x with ⟨i, a⟩ | z` into its components or cases. Distinguish the cases in `h1 : i ∈ S`. Distinguish the cases in `h3 : isVec i`.

Establish `e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a`. Simplify using `[sharpHom, h1, h3]`. Establish `e2 : (⇑(conjAct (ζ` using `ζ) (RingHom.id L) isVec S g gi last) ∘ fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) = Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) := by`. Use function extensionality and compare the values at `b`. Simplify using `[conjAct, h1, h3]`.

Establish `e3 : (g.map C).map ⇑(conjAct (ζ` using `ζ) (RingHom.id L) isVec S g gi last) = g.map (cc _ L) := by`. Use extensionality with `p q`. Simplify using `[conjAct_C]`. Establish `e4 : (g.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).map ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) = g.map (cc _ L)`. Use extensionality with `p q`.

Simplify using the standard rewrite rules. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]`. Rewrite using `[e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, conjS_mul _ h, ← Matrix.vecMul_vecMul, diagS, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]`. Use `congr 1`. Apply the tactic sequence `by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]`.

Establish `e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a`. Simplify using `[sharpHom, h1, h3]`. Establish `e2 : (⇑(conjAct (ζ` using `ζ) (RingHom.id L) isVec S g gi last) ∘ fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) = Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last (-1)).transpose := by`. Use function extensionality and compare the values at `b`. Simplify using `[conjAct, h1, h3]`.

Establish `e3 : ((gi.map C).transpose).map ⇑(conjAct (ζ` using `ζ) (RingHom.id L) isVec S g gi last) = (gi.map (cc _ L)).transpose := by`. Use extensionality with `p q`. Simplify using `[conjAct_C]`. Establish `e4 : ((gi.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).transpose).map ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) = (gi.map (cc _ L)).transpose`. Use extensionality with `p q`.

Simplify using the standard rewrite rules. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]`. Rewrite using `[e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, mul_conjS _ h, Matrix.transpose_mul, ← Matrix.vecMul_vecMul, diagS, Matrix.diagonal_transpose, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]`. Use `congr 1`. Apply the tactic sequence `by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]`.

Simplify using `[tw, conjAct, sharpHom, wtX, h1]`. Simplify using `[tw, conjAct, sharpHom, wtX]`.
-/
theorem conjAct_sharp {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool)
    (H : MvPolynomial (LVar ι ζ n) L) :
    conjAct (RingHom.id L) isVec S g gi last (sharpHom isVec S g gi H) = tw isVec S g gi last H := by
  suffices hh : (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp
      (sharpHom isVec S g gi).toRingHom = tw isVec S g gi last from by
    rw [← hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [tw, conjAct_C, sharpHom]
  · intro x
    rcases x with ⟨i, a⟩ | z
    · by_cases h1 : i ∈ S
      · by_cases h3 : isVec i
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : (g.map C).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) = g.map (cc _ L) := by
            ext p q
            simp [conjAct_C]
          have e4 : (g.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              g.map (cc _ L) := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, conjS_mul _ h, ← Matrix.vecMul_vecMul,
            diagS, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
                (conjS _ g gi last (-1)).transpose := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : ((gi.map C).transpose).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp [conjAct_C]
          have e4 : ((gi.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).transpose).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, mul_conjS _ h,
            Matrix.transpose_mul, ← Matrix.vecMul_vecMul,
            diagS, Matrix.diagonal_transpose, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
      · simp [tw, conjAct, sharpHom, wtX, h1]
    · simp [tw, conjAct, sharpHom, wtX]

/- English proof (translation)
Establish `e1 : sharpHom isVec S g gi (monomial e c) = C c * ∏ x ∈ e.support, (sharpHom isVec S g gi (X x)) ^ (e x)`. Rewrite using `[MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]`. Simplify using `[sharpHom]`. Rewrite using `[e1, tw, coe_eval₂Hom, eval₂_monomial, Finsupp.prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, LaurentPolynomial.T_pow, prod_laurent_T, map_mul, map_prod, map_pow, wExp, RingHom.comp_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tw_monomial (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : LVar ι ζ n →₀ ℕ) (c : L) :
    tw isVec S g gi last (monomial e c) =
      LaurentPolynomial.T (wExp isVec S last e) * LaurentPolynomial.C (sharpHom isVec S g gi (monomial e c)) := by
  have e1 : sharpHom isVec S g gi (monomial e c) =
      C c * ∏ x ∈ e.support, (sharpHom isVec S g gi (X x)) ^ (e x) := by
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    simp [sharpHom]
  rw [e1, tw, coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, LaurentPolynomial.T_pow, prod_laurent_T, map_mul, map_prod, map_pow,
    wExp, RingHom.comp_apply]
  ring

/- English proof (translation)
Use `conv_lhs => rw [H.as_sum]`. Rewrite using `[map_sum, lp_coeff_sum, map_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[tw_monomial, lp_coeff_TC]`.
-/
theorem tw_coeff (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (H : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    (tw isVec S g gi last H).coeff j =
      sharpHom isVec S g gi
        (∑ e ∈ H.support.filter (fun e => wExp isVec S last e = j), monomial e (coeff e H)) := by
  conv_lhs => rw [H.as_sum]
  rw [map_sum, lp_coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [tw_monomial, lp_coeff_TC]

/- English proof (translation)
It suffices to establish `hh : (sharpHom (ζ` using `ζ) isVec S g gi).comp (sharpHom isVec S gi g) = AlgHom.id L _ from by`. Use `congrArg (fun f => f H) hh` as an intermediate fact. Simplify using `using this`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`.

Break down `x with ⟨i, a⟩ | z` into its components or cases. Distinguish the cases in `h1 : i ∈ S`. Distinguish the cases in `h3 : isVec i`. Establish `e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C) a`. Simplify using `[sharpHom, h1, h3]`.

Establish `e2 : (⇑(sharpHom (ζ` using `ζ) isVec S g gi).toRingHom ∘ fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) := by`. Use function extensionality and compare the values at `b`. Simplify using `[sharpHom, h1, h3]`. Establish `e3 : (gi.map C).map ⇑(sharpHom (ζ` using `ζ) isVec S g gi).toRingHom = gi.map C := by`. Use extensionality with `p q`.

Simplify using `[sharpHom]`. Rewrite using `[AlgHom.comp_apply, e1]`. Express the relevant statement in the definitionally equal form `(sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _`. Rewrite using `[RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]`. Both sides reduce to the same expression.

Establish `e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C).transpose a`. Simplify using `[sharpHom, h1, h3]`. Establish `e2 : (⇑(sharpHom (ζ` using `ζ) isVec S g gi).toRingHom ∘ fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) = Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose := by`. Use function extensionality and compare the values at `b`. Simplify using `[sharpHom, h1, h3]`.

Establish `e3 : ((g.map C).transpose).map ⇑(sharpHom (ζ` using `ζ) isVec S g gi).toRingHom = (g.map C).transpose := by`. Use extensionality with `p q`. Simplify using `[sharpHom]`. Rewrite using `[AlgHom.comp_apply, e1]`. Express the relevant statement in the definitionally equal form `(sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _`.

Rewrite using `[RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.vecMul_one]`. Both sides reduce to the same expression. Simplify using `[sharpHom, h1]`. Simplify using `[sharpHom]`.
-/
theorem sharp_sharp {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (H : MvPolynomial (LVar ι ζ n) L) :
    sharpHom isVec S g gi (sharpHom isVec S gi g H) = H := by
  suffices hh : (sharpHom (ζ := ζ) isVec S g gi).comp (sharpHom isVec S gi g) = AlgHom.id L _ from by
    have := congrArg (fun f => f H) hh
    simpa using this
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · by_cases h3 : isVec i
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C) a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : (gi.map C).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom = gi.map C := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
        rfl
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C).transpose a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : ((g.map C).transpose).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom =
            (g.map C).transpose := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.vecMul_one]
        rfl
    · simp [sharpHom, h1]
  · simp [sharpHom]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Function.LeftInverse.injective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h'), Function.RightInverse.surjective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h)⟩`.
-/
theorem sharp_bij {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) :
    Function.Bijective (sharpHom (ζ := ζ) isVec S g gi) :=
  ⟨Function.LeftInverse.injective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h'),
   Function.RightInverse.surjective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h)⟩

end Sharp

section Gen

variable {ι ζ : Type*} {n : ℕ}

/- English proof (translation)
It suffices to establish `hh : conjAct (ζ` using `ζ) φ isVec S g gi last = (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp (map φ) from by`. Rewrite using `[hh]`. Both sides reduce to the same expression. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Simplify using `[conjAct_C]`. Introduce `x`. Simplify using `[conjAct]`.
-/
theorem conjAct_map {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (G : MvPolynomial (LVar ι ζ n) k) :
    conjAct φ isVec S g gi last G = conjAct (RingHom.id L) isVec S g gi last (map φ G) := by
  suffices hh : conjAct (ζ := ζ) φ isVec S g gi last =
      (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp (map φ) from by
    rw [hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [conjAct_C]
  · intro x
    simp [conjAct]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Establish `: H.support.filter p = ∅`.

Rewrite using `[Finset.filter_eq_empty_iff]`. Introduce `e he hp`. Conclude with `hc ⟨e, he, hp⟩`. Rewrite using `[this, Finset.sum_empty]`. Introduce and unpack `⟨e, he, hp⟩ h`.

Use `congrArg (coeff e) h` as an intermediate fact. Rewrite `this` using `[coeff_sum]`. Simplify using `only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, coeff_zero] at this`. Rewrite `this` using `[if_pos ⟨he, hp⟩]`. Conclude with `(mem_support_iff.mp he) this`.
-/
theorem part_ne_zero {σ L : Type*} [CommRing L] (H : MvPolynomial σ L) (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    (∑ e ∈ H.support.filter p, monomial e (coeff e H)) ≠ 0 ↔ ∃ e ∈ H.support, p e := by
  classical
  constructor
  · intro h
    by_contra hc
    apply h
    have : H.support.filter p = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hp
      exact hc ⟨e, he, hp⟩
    rw [this, Finset.sum_empty]
  · rintro ⟨e, he, hp⟩ h
    have := congrArg (coeff e) h
    rw [coeff_sum] at this
    simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, coeff_zero] at this
    rw [if_pos ⟨he, hp⟩] at this
    exact (mem_support_iff.mp he) this

/- English proof (translation)
Use `conv_lhs => rw [← sharp_sharp isVec S h G]`. Rewrite using `[conjAct_sharp isVec S h', Finsupp.mem_support_iff, tw_coeff, ← part_ne_zero]`. Conclude with `(map_ne_zero_iff _ (sharp_bij isVec S h h').1)`.
-/
theorem conj_mem_supp {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    j ∈ (conjAct (RingHom.id L) isVec S g gi last G).coeff.support ↔
      ∃ e ∈ (sharpHom isVec S gi g G).support, wExp isVec S last e = j := by
  conv_lhs => rw [← sharp_sharp isVec S h G]
  rw [conjAct_sharp isVec S h', Finsupp.mem_support_iff, tw_coeff, ← part_ne_zero]
  exact (map_ne_zero_iff _ (sharp_bij isVec S h h').1)

variable (k : Type*) [Field k]

abbrev genφ (n : ℕ) : k →+* GenField k n := (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[genMat, Matrix.mvPolynomialX]`.
-/
theorem genMat_eq (n : ℕ) : genMat k n =
    (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
  ext a b
  simp [genMat, Matrix.mvPolynomialX]

/- English proof (translation)
Rewrite using `[genMat_eq, ← RingHom.map_det]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)`.
-/
theorem genMat_det_ne (n : ℕ) : (genMat k n).det ≠ 0 := by
  rw [genMat_eq, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)

/- English proof (translation)
The claim follows from `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))`.
-/
theorem genMat_mul_inv (n : ℕ) : genMat k n * (genMat k n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))

/- English proof (translation)
The claim follows from `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))`.
-/
theorem genMat_inv_mul (n : ℕ) : (genMat k n)⁻¹ * genMat k n = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))

variable {k}

def genH (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (G : MvPolynomial (LVar ι ζ n) k) :
    MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n)⁻¹ (genMat k n) (map (genφ k n) G)

/- English proof (translation)
Rewrite using `[genAct, conjAct_map]`. Conclude with `conj_mem_supp isVec S (genMat_mul_inv k n) (genMat_inv_mul k n) last _ j`.
-/
theorem gen_mem_supp (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ) :
    j ∈ (genAct k isVec S last G).coeff.support ↔ ∃ e ∈ (genH isVec S G).support, wExp isVec S last e = j := by
  rw [genAct, conjAct_map]
  exact conj_mem_supp isVec S (genMat_mul_inv k n) (genMat_inv_mul k n) last _ j

end Gen

section Consts

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

/- English proof (translation)
Rewrite using `[genAct, conjAct_C]`. Both sides reduce to the same expression.
-/
theorem genAct_C (last : Bool) (c : k) :
    genAct (ζ := ζ) (n := n) k isVec S last (C c) = LaurentPolynomial.C (C (genφ k n c)) := by
  rw [genAct, conjAct_C]; rfl

/- English proof (translation)
Rewrite using `[valS, genAct_C, lp_supp_C]`. Both sides reduce to the same expression. Simplify using `using hc`.
-/
theorem val_C {c : k} (hc : c ≠ 0) : valS (ζ := ζ) (n := n) isVec S (C c) = 0 := by
  rw [valS, genAct_C, lp_supp_C]
  · rfl
  · simpa using hc

/- English proof (translation)
Rewrite using `[lam1S, genAct_C, lp_supp_C]`. Both sides reduce to the same expression. Simplify using `using hc`.
-/
theorem lam_C {c : k} (hc : c ≠ 0) : lam1S (ζ := ζ) (n := n) isVec S (C c) = 0 := by
  rw [lam1S, genAct_C, lp_supp_C]
  · rfl
  · simpa using hc

/- English proof (translation)
Simplify using `only [valS, map_mul]`. Conclude with `lp_min_mul _ _`.
-/
theorem val_mul (G H : MvPolynomial (LVar ι ζ n) k) :
    valS isVec S (G * H) = valS isVec S G + valS isVec S H := by
  simp only [valS, map_mul]; exact lp_min_mul _ _

/- English proof (translation)
Simplify using `only [lam1S, map_mul]`. Conclude with `lp_max_mul _ _`.
-/
theorem lam_mul (G H : MvPolynomial (LVar ι ζ n) k) :
    lam1S isVec S (G * H) = lam1S isVec S G + lam1S isVec S H := by
  simp only [lam1S, map_mul]; exact lp_max_mul _ _

/- English proof (translation)
Simplify using `only [valS, map_add]`. Conclude with `lp_min_add _ _`.
-/
theorem val_add (G H : MvPolynomial (LVar ι ζ n) k) :
    min (valS isVec S G) (valS isVec S H) ≤ valS isVec S (G + H) := by
  simp only [valS, map_add]; exact lp_min_add _ _

/- English proof (translation)
Simplify using `only [lam1S, map_add]`. Conclude with `lp_max_add _ _`.
-/
theorem lam_add (G H : MvPolynomial (LVar ι ζ n) k) :
    lam1S isVec S (G + H) ≤ max (lam1S isVec S G) (lam1S isVec S H) := by
  simp only [lam1S, map_add]; exact lp_max_add _ _

/- English proof (translation)
Simplify using `[valS]`.
-/
theorem val_zero : valS isVec S (0 : MvPolynomial (LVar ι ζ n) k) = ⊤ := by
  simp [valS]

/- English proof (translation)
Simplify using `[lam1S]`.
-/
theorem lam_zero : lam1S isVec S (0 : MvPolynomial (LVar ι ζ n) k) = ⊥ := by
  simp [lam1S]

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc, val_zero]`. Rewrite using `[MvPolynomial.smul_eq_C_mul, val_mul, val_C isVec S hc, zero_add]`. Conclude with `h`.
-/
theorem val_smul_le (θ : WithTop ℤ) (c : k) (G : MvPolynomial (LVar ι ζ n) k) (h : θ ≤ valS isVec S G) :
    θ ≤ valS isVec S (c • G) := by
  by_cases hc : c = 0
  · simp [hc, val_zero]
  · rw [MvPolynomial.smul_eq_C_mul, val_mul, val_C isVec S hc, zero_add]; exact h

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc, lam_zero]`. Rewrite using `[MvPolynomial.smul_eq_C_mul, lam_mul, lam_C isVec S hc, zero_add]`. Conclude with `h`.
-/
theorem lam_smul_le (M : WithBot ℤ) (c : k) (G : MvPolynomial (LVar ι ζ n) k) (h : lam1S isVec S G ≤ M) :
    lam1S isVec S (c • G) ≤ M := by
  by_cases hc : c = 0
  · simp [hc, lam_zero]
  · rw [MvPolynomial.smul_eq_C_mul, lam_mul, lam_C isVec S hc, zero_add]; exact h

end Consts

/- English proof (translation)
Introduce `k _ ι ζ n isVec S _ θ M c G H`. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Conclude with `le_trans (le_min (val_smul_le isVec S θ c G h1) h2) (val_add isVec S _ _)`. Introduce `h1 h2`.

Conclude with `le_trans (lam_add isVec S _ _) (max_le (lam_smul_le isVec S M c G h1) h2)`.
-/
theorem cornerValSubmodule : PropVdSub := by
  intro k _ ι ζ n isVec S _ θ M c G H
  constructor
  · intro h1 h2
    exact le_trans (le_min (val_smul_le isVec S θ c G h1) h2) (val_add isVec S _ _)
  · intro h1 h2
    exact le_trans (lam_add isVec S _ _) (max_le (lam_smul_le isVec S M c G h1) h2)

section Coord

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

/- English proof (translation)
Simplify using `[wExp]`.
-/
theorem wExp_single (last : Bool) (x : LVar ι ζ n) :
    wExp isVec S last (Finsupp.single x 1) = wtX isVec S last x := by
  simp [wExp]

end Coord

section DetPart

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

/- English proof (translation)
Use `val_C (ζ := ζ) (n := n) (k := k) isVec S (one_ne_zero)` as an intermediate fact. Simplify using `using this`.
-/
theorem val_one : valS isVec S (1 : MvPolynomial (LVar ι ζ n) k) = 0 := by
  have := val_C (ζ := ζ) (n := n) (k := k) isVec S (one_ne_zero)
  simpa using this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [val_one]`. Consider the case `succ m ih => rw [pow_succ, val_mul, ih, succ_nsmul]`.
-/
theorem val_pow (G : MvPolynomial (LVar ι ζ n) k) (m : ℕ) :
    valS isVec S (G ^ m) = m • valS isVec S G := by
  induction m with
  | zero => simp [val_one]
  | succ m ih => rw [pow_succ, val_mul, ih, succ_nsmul]

end DetPart

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
