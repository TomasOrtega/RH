import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.IwaFam

open Matrix

/- English proof (translation)
Establish `h` using `Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b`. Establish `e : Matrix.replicateCol Unit a * Matrix.replicateRow Unit b = Matrix.vecMulVec a b`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.vecMulVec_apply]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
lemma det_one_add_vmv {R : Type} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (1 + Matrix.vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  have e : Matrix.replicateCol Unit a * Matrix.replicateRow Unit b = Matrix.vecMulVec a b := by
    ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rwa [e] at h

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/- English proof (translation)
Set `M' : Matrix (Fin n) (Fin n) v.O` to `Matrix.of fun i j => ⟨M i j, (Valuation.mem_valuationSubring_iff _ _).2 (h i j)⟩`. Establish `e : v.O.subtype M'.det = M.det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[← e]`. Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 M'.det.2`.
-/
lemma val_det_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, v.1 (M i j) ≤ 1) : v.1 M.det ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) v.O := Matrix.of fun i j => ⟨M i j, (Valuation.mem_valuationSubring_iff _ _).2 (h i j)⟩
  have e : v.O.subtype M'.det = M.det := by rw [RingHom.map_det]; rfl
  rw [← e]; exact (Valuation.mem_valuationSubring_iff _ _).1 M'.det.2

/- English proof (translation)
The claim follows from `le_antisymm hb (calc 1 = a * b := h.symm _ ≤ b := mul_le_of_le_one_left' ha)`.
-/
lemma eq_one_of_mul {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : b = 1 :=
  le_antisymm hb (calc 1 = a * b := h.symm
    _ ≤ b := mul_le_of_le_one_left' ha)

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.
-/
lemma val_sign (v : Place k F) {n : ℕ} (σ : Equiv.Perm (Fin n)) : v.1 ((Equiv.Perm.sign σ : ℤ) : F) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hmax, -⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k F v`. Take `⟨i, hi, -, -, hle⟩` from `hmax (r+1) y hy`. Use `set c : Fin (r+1) → F := fun j => if j = i then 0 else y j / y i with hc`. Use `set u0 : Matrix (Fin (r+1)) (Fin (r+1)) F := 1 + Matrix.vecMulVec (-c) (Pi.single i 1) with hu0`. Establish `hcle : ∀ j, v.1 (c j) ≤ 1`.

Introduce `j`. Simplify using `only [hc]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[Valuation.map_div]`.

Conclude with `div_le_one_of_le₀ (hle j) zero_le'`. Establish `hu0y : ∀ j, (u0 *ᵥ y) j = y j - c j * y i`. Introduce `j`. Simplify using `only [hu0, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply, ite_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨u0.submatrix (Equiv.swap 0 i) id, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `only [Matrix.submatrix_apply, id, hu0, Matrix.add_apply, Matrix.vecMulVec_apply]`. Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations.

Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Rewrite using `[Pi.neg_apply, Valuation.map_mul, Valuation.map_neg]`. Use `mul_le_one' (hcle _) ?_` and prove the remaining obligations. Apply the tactic sequence `rw [Pi.single_apply]; split_ifs <;> simp`. Rewrite using `[Matrix.det_permute, det_one_add_vmv, Valuation.map_mul, val_sign]`.

Simplify using `[hc]`. Introduce `a show (u0 *ᵥ y) (Equiv.swap 0 i a.succ) = 0`. Establish `hne : Equiv.swap 0 i a.succ ≠ i`. Introduce `h`. Use `congrArg (Equiv.swap 0 i) h` as an intermediate fact.

Rewrite `this` using `[Equiv.swap_apply_self, Equiv.swap_apply_right]`. Conclude with `Fin.succ_ne_zero a this`. Rewrite using `[hu0y]`. Simplify using `only [hc, if_neg hne]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_u (v : Place k F) {r : ℕ} (y : Fin (r+1) → F) (hy : y ≠ 0) :
    ∃ u : Matrix (Fin (r+1)) (Fin (r+1)) F, Unimod v u ∧ ∀ a : Fin r, (u *ᵥ y) a.succ = 0 := by
  obtain ⟨-, -, -, -, -, -, hmax, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
  obtain ⟨i, hi, -, -, hle⟩ := hmax (r+1) y hy
  set c : Fin (r+1) → F := fun j => if j = i then 0 else y j / y i with hc
  set u0 : Matrix (Fin (r+1)) (Fin (r+1)) F := 1 + Matrix.vecMulVec (-c) (Pi.single i 1) with hu0
  have hcle : ∀ j, v.1 (c j) ≤ 1 := by
    intro j; simp only [hc]; split_ifs
    · simp
    · rw [Valuation.map_div]
      exact div_le_one_of_le₀ (hle j) zero_le'
  have hu0y : ∀ j, (u0 *ᵥ y) j = y j - c j * y i := by
    intro j
    simp only [hu0, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply, ite_mul]
    ring
  refine ⟨u0.submatrix (Equiv.swap 0 i) id, ⟨?_, ?_⟩, ?_⟩
  · intro a b
    simp only [Matrix.submatrix_apply, id, hu0, Matrix.add_apply, Matrix.vecMulVec_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Pi.neg_apply, Valuation.map_mul, Valuation.map_neg]
      refine mul_le_one' (hcle _) ?_
      rw [Pi.single_apply]; split_ifs <;> simp
  · rw [Matrix.det_permute, det_one_add_vmv, Valuation.map_mul, val_sign]
    simp [hc]
  · intro a
    show (u0 *ᵥ y) (Equiv.swap 0 i a.succ) = 0
    have hne : Equiv.swap 0 i a.succ ≠ i := by
      intro h
      have := congrArg (Equiv.swap 0 i) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      exact Fin.succ_ne_zero a this
    rw [hu0y]; simp only [hc, if_neg hne]; field_simp; ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (funext hc)`. Use `⟨(1 + Matrix.vecMulVec (x - Pi.single i 1) (Pi.single i 1)).submatrix id (Equiv.swap 0 i), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_permute', det_one_add_vmv]`. Simplify using `[hi]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `a`. Simplify using `[Matrix.submatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply]`.

Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma exists_h {n : ℕ} (x : Fin (n+1) → F) (hx : x ≠ 0) :
    ∃ h : Matrix (Fin (n+1)) (Fin (n+1)) F, h.det ≠ 0 ∧ ∀ a, h a 0 = x a := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  refine ⟨(1 + Matrix.vecMulVec (x - Pi.single i 1) (Pi.single i 1)).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', det_one_add_vmv]
    simp [hi]
    split_ifs <;> simp
  · intro a
    simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> simp_all

/- English proof (translation)
Establish `fin1 : ∀ c : F, {v : Place k F | ¬ v.1 c ≤ 1}.Finite`. Introduce `c`. Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Conclude with `(GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF c hc).1.subset fun v hv h1 => hv (le_of_eq h1)`.

Use `((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hd).1.union (Set.finite_iUnion fun p : Fin n × Fin n => fin1 (h p.1 p.2))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hv ⟨fun i j => hc.2 (i, j), hc.1⟩`.
-/
lemma unimod_ae [IsAlgClosed k] [CharZero k] (hF : IsFF k F) {n : ℕ} (h : Matrix (Fin n) (Fin n) F) (hd : h.det ≠ 0) :
    {v : Place k F | ¬ Unimod v h}.Finite := by
  have fin1 : ∀ c : F, {v : Place k F | ¬ v.1 c ≤ 1}.Finite := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF c hc).1.subset fun v hv h1 => hv (le_of_eq h1)
  refine ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hd).1.union (Set.finite_iUnion fun p : Fin n × Fin n => fin1 (h p.1 p.2))).subset ?_
  intro v hv
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
  by_contra hc; push_neg at hc
  exact hv ⟨fun i j => hc.2 (i, j), hc.1⟩

/- English proof (translation)
Use `⟨fun i j => (hρ p _).2 (hu.1 i j), ?_⟩` and prove the remaining obligations. Establish `e : (u.map (algebraMap F E)).det = algebraMap F E u.det` using `(RingHom.map_det _ _).symm`. Establish `hd0 : u.det ≠ 0` using `fun h0 => by`. Use `hu.2` as an intermediate fact. Rewrite `this` using `[h0, Valuation.map_zero]`.

Conclude with `zero_ne_one this`. Establish `h1 : p.1 (algebraMap F E u.det) ≤ 1` using `(hρ p _).2 hu.2.le`. Establish `h2 : p.1 (algebraMap F E u.det⁻¹) ≤ 1` using `(hρ p _).2 (by rw [map_inv₀, hu.2, inv_one])`. Establish `h3 : p.1 (algebraMap F E u.det⁻¹) * p.1 (algebraMap F E u.det) = 1`. Rewrite using `[← Valuation.map_mul, ← map_mul, inv_mul_cancel₀ hd0, map_one, Valuation.map_one]`.

Rewrite using `[e]`. Conclude with `eq_one_of_mul h2 h1 h3`.
-/
lemma unimod_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    (p : Place k E) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (hu : Unimod (ρ p) u) :
    Unimod p (u.map (algebraMap F E)) := by
  refine ⟨fun i j => (hρ p _).2 (hu.1 i j), ?_⟩
  have e : (u.map (algebraMap F E)).det = algebraMap F E u.det := (RingHom.map_det _ _).symm
  have hd0 : u.det ≠ 0 := fun h0 => by
    have := hu.2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have h1 : p.1 (algebraMap F E u.det) ≤ 1 := (hρ p _).2 hu.2.le
  have h2 : p.1 (algebraMap F E u.det⁻¹) ≤ 1 := (hρ p _).2 (by rw [map_inv₀, hu.2, inv_one])
  have h3 : p.1 (algebraMap F E u.det⁻¹) * p.1 (algebraMap F E u.det) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, inv_mul_cancel₀ hd0, map_one, Valuation.map_one]
  rw [e]; exact eq_one_of_mul h2 h1 h3

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hnrm, -⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k E p`. Simplify using `only [pullAd, Matrix.map_mul]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Simplify using `only [ordVec, hnrm _ _ _ (unimod_pull ρ hρ p _ (hu (ρ p)))]`.
-/
lemma ordVec_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    {n : ℕ} (u g h : Place k F → Matrix (Fin n) (Fin n) F) (hu : ∀ v, Unimod v (u v)) (p : Place k E) (w : Fin n → E) :
    ordVec p (pullAd ρ (fun v => u v * g v * h v) p *ᵥ w) = ordVec p (pullAd ρ g p *ᵥ ((h (ρ p)).map (algebraMap F E) *ᵥ w)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnrm, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k E p
  simp only [pullAd, Matrix.map_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [ordVec, hnrm _ _ _ (unimod_pull ρ hρ p _ (hu (ρ p)))]

end GlobalTheory.IwaFam

open Matrix in

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF r g hg x hx`. Take `⟨h, hdet, hcol⟩` from `GlobalTheory.IwaFam.exists_h x hx`. Establish `hy : ∀ v, g v *ᵥ x ≠ 0` using `fun v h0 => (hg.1 v) (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, h0⟩)`. Use `choose u hu hz using fun v => GlobalTheory.IwaFam.exists_u v (g v *ᵥ x) (hy v)`. Establish `hcol0 : ∀ v a, (u v * g v * h) a 0 = (u v *ᵥ (g v *ᵥ x)) a`.

Introduce `v a`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_apply]`. Simplify using `only [hcol]`. Both sides reduce to the same expression. Establish `hz' : ∀ v (i : Fin r), (u v * g v * h) i.succ 0 = 0` using `fun v i => by rw [hcol0]; exact hz v i`.

Establish `hdetA : ∀ v, (u v * g v * h).det = (u v * g v * h) 0 0 * ((u v * g v * h).submatrix Fin.succ Fin.succ).det`. Introduce `v`. Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Simplify using `[hz', Fin.succAbove_zero]`. Establish `hdu : ∀ v, (u v).det ≠ 0` using `fun v h0 => by`.

Use `(hu v).2` as an intermediate fact. Rewrite `this` using `[h0, Valuation.map_zero]`. Conclude with `zero_ne_one this`. Establish `hdA : ∀ v, (u v * g v * h).det ≠ 0` using `fun v => by`. Rewrite using `[Matrix.det_mul, Matrix.det_mul]`.

Conclude with `mul_ne_zero (mul_ne_zero (hdu v) (hg.1 v)) hdet`. Establish `h00 : ∀ v, (u v * g v * h) 0 0 ≠ 0` using `fun v h0 => hdA v (by rw [hdetA, h0, zero_mul])`. Establish `hdS : ∀ v, ((u v * g v * h).submatrix Fin.succ Fin.succ).det ≠ 0` using `fun v h0 => hdA v (by rw [hdetA, h0, mul_zero])`. Establish `hov : ∀ v, ordVec v (g v *ᵥ x) = ord v ((u v * g v * h) 0 0)`. Introduce `v`.

Take `⟨-, -, -, -, -, -, hmax, -, hnrm, -⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k F v`. Establish `hzne : u v *ᵥ (g v *ᵥ x) ≠ 0` using `fun h0 => hdu v (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hy v, h0⟩)`. Take `⟨i, hi, -, hoi, -⟩` from `hmax _ _ hzne`. Establish `hi0 : i = 0`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero => rfl`. Consider the case `succ j => exact absurd (hz v j) hi`. Substitute `hi0` using the available equality. Establish `e1 : ordVec v (g v *ᵥ x) = ordVec v (u v *ᵥ (g v *ᵥ x))`. Simplify using `only [ordVec, hnrm _ _ _ (hu v)]`.

Rewrite using `[e1, hoi, hcol0]`. Establish `hpt : ∀ v, ord v (g v).det + ord v h.det = ord v ((u v * g v * h) 0 0) + ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det`. Introduce `v`. Take `⟨hmul, -, -, hord1, -⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k F v`. Establish `e1` using `hmul _ _ (h00 v) (hdS v)`.

Rewrite `e1` using `[← hdetA, Matrix.det_mul, Matrix.det_mul, hmul _ _ (mul_ne_zero (hdu v) (hg.1 v)) hdet, hmul _ _ (hdu v) (hg.1 v), (hord1 _ (hdu v)).1 (hu v).2, zero_add]`. Conclude with `e1`. Establish `fg : (Function.support fun v => ord v (g v).det).Finite` using `(GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).1`. Establish `fh : (Function.support fun v : Place k F => ord v h.det).Finite`. Use `(GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).1.subset fun v hv h1 => hv ?_` and prove the remaining obligations.

Conclude with `((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.1 _ hdet).1 h1`. Establish `fc : (Function.support fun v => ord v ((u v * g v * h) 0 0)).Finite`. Use `((GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).2 x hx).1.subset fun v hv h1 => hv ?_` and prove the remaining obligations. Use `show ord v ((u v * g v * h) 0 0) = 0`. Rewrite using `[← hov, ordVec, h1]`.

Simplify using the standard rewrite rules. Establish `fd : (Function.support fun v => ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det).Finite`. Use `((fg.union fh).union fc).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hv`.

Use `hpt v` as an intermediate fact. Rewrite `this` using `[hc.1.1, hc.1.2, hc.2]`. Conclude with `hv (by linarith)`. Establish `hline : ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x`. Unfold `degLine`.

Conclude with `finsum_congr fun v => (hov v).symm`. Use `⟨h, u, hdet, hu, hz', ⟨hdA, ?_⟩, ⟨hdS, ?_⟩, ?_, hline, ?_⟩` and prove the remaining obligations. Use `((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv`.

Take `⟨-, -, -, -, -, -, -, -, -, hprod⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k F v`. Conclude with `hv ((hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1)`. Use `((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv`.

Take `⟨-, -, -, -, -, -, -, -, -, hprod⟩` from `GlobalTheory.T.functionFieldPlaceOrder_calculus k F v`. Establish `hA` using `(hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1`. Use `hv ⟨fun i j => hA.1 i.succ j.succ, ?_⟩` and prove the remaining obligations. Establish `e` using `hA.2`. Rewrite `e` using `[hdetA, Valuation.map_mul]`.

Conclude with `GlobalTheory.IwaFam.eq_one_of_mul (hA.1 0 0) (GlobalTheory.IwaFam.val_det_le_one v _ fun i j => hA.1 i.succ j.succ) e`. Unfold `deg`. Rewrite using `[← hline, ← finsum_add_distrib fc fd, ← add_zero (∑ᶠ v, ord v (g v).det), ← (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).2, ← finsum_add_distrib fg fh]`. Conclude with `finsum_congr hpt`. Introduce `b hb E _ _ _ _ _ ρ hρ w hw`.

Set `h'` to `h.map (algebraMap F E)`. Establish `hne : h' *ᵥ w ≠ 0` using `fun h0 => by`. Establish `e : h'.det = algebraMap F E h.det` using `(RingHom.map_det _ _).symm`. Conclude with `(map_ne_zero _).2 hdet (e ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, h0⟩)`. Establish `e : degLine (pullAd ρ fun v => u v * g v * h) w = degLine (pullAd ρ g) (h' *ᵥ w)`.

Unfold `degLine`. Conclude with `finsum_congr fun p => GlobalTheory.IwaFam.ordVec_pull ρ hρ u g (fun _ => h) hu p w`. Rewrite using `[e]`. Conclude with `hb E ρ hρ _ hne`.
-/
theorem GlobalTheory.iwasawa_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  intro k F _ _ _ _ _ hF r g hg x hx
  obtain ⟨h, hdet, hcol⟩ := GlobalTheory.IwaFam.exists_h x hx
  have hy : ∀ v, g v *ᵥ x ≠ 0 := fun v h0 => (hg.1 v) (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, h0⟩)
  choose u hu hz using fun v => GlobalTheory.IwaFam.exists_u v (g v *ᵥ x) (hy v)
  have hcol0 : ∀ v a, (u v * g v * h) a 0 = (u v *ᵥ (g v *ᵥ x)) a := by
    intro v a
    rw [Matrix.mulVec_mulVec, Matrix.mul_apply]
    simp only [hcol]
    rfl
  have hz' : ∀ v (i : Fin r), (u v * g v * h) i.succ 0 = 0 := fun v i => by rw [hcol0]; exact hz v i
  have hdetA : ∀ v, (u v * g v * h).det = (u v * g v * h) 0 0 * ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hz', Fin.succAbove_zero]
  have hdu : ∀ v, (u v).det ≠ 0 := fun v h0 => by
    have := (hu v).2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have hdA : ∀ v, (u v * g v * h).det ≠ 0 := fun v => by
    rw [Matrix.det_mul, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero (hdu v) (hg.1 v)) hdet
  have h00 : ∀ v, (u v * g v * h) 0 0 ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, zero_mul])
  have hdS : ∀ v, ((u v * g v * h).submatrix Fin.succ Fin.succ).det ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, mul_zero])

  have hov : ∀ v, ordVec v (g v *ᵥ x) = ord v ((u v * g v * h) 0 0) := by
    intro v
    obtain ⟨-, -, -, -, -, -, hmax, -, hnrm, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have hzne : u v *ᵥ (g v *ᵥ x) ≠ 0 := fun h0 => hdu v (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hy v, h0⟩)
    obtain ⟨i, hi, -, hoi, -⟩ := hmax _ _ hzne
    have hi0 : i = 0 := by
      induction i using Fin.cases with
      | zero => rfl
      | succ j => exact absurd (hz v j) hi
    subst hi0
    have e1 : ordVec v (g v *ᵥ x) = ordVec v (u v *ᵥ (g v *ᵥ x)) := by
      simp only [ordVec, hnrm _ _ _ (hu v)]
    rw [e1, hoi, hcol0]

  have hpt : ∀ v, ord v (g v).det + ord v h.det = ord v ((u v * g v * h) 0 0) + ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    obtain ⟨hmul, -, -, hord1, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have e1 := hmul _ _ (h00 v) (hdS v)
    rw [← hdetA, Matrix.det_mul, Matrix.det_mul, hmul _ _ (mul_ne_zero (hdu v) (hg.1 v)) hdet,
      hmul _ _ (hdu v) (hg.1 v), (hord1 _ (hdu v)).1 (hu v).2, zero_add] at e1
    exact e1
  have fg : (Function.support fun v => ord v (g v).det).Finite := (GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).1
  have fh : (Function.support fun v : Place k F => ord v h.det).Finite := by
    refine (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).1.subset fun v hv h1 => hv ?_
    exact ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.1 _ hdet).1 h1
  have fc : (Function.support fun v => ord v ((u v * g v * h) 0 0)).Finite := by
    refine ((GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).2 x hx).1.subset fun v hv h1 => hv ?_
    show ord v ((u v * g v * h) 0 0) = 0
    rw [← hov, ordVec, h1]; simp
  have fd : (Function.support fun v => ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det).Finite := by
    refine ((fg.union fh).union fc).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hv
    have := hpt v
    rw [hc.1.1, hc.1.2, hc.2] at this
    exact hv (by linarith)
  have hline : ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x := by
    unfold degLine; exact finsum_congr fun v => (hov v).symm
  refine ⟨h, u, hdet, hu, hz', ⟨hdA, ?_⟩, ⟨hdS, ?_⟩, ?_, hline, ?_⟩
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    exact hv ((hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1)
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have hA := (hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1
    refine hv ⟨fun i j => hA.1 i.succ j.succ, ?_⟩
    have e := hA.2
    rw [hdetA, Valuation.map_mul] at e
    exact GlobalTheory.IwaFam.eq_one_of_mul (hA.1 0 0)
      (GlobalTheory.IwaFam.val_det_le_one v _ fun i j => hA.1 i.succ j.succ) e
  · unfold deg
    rw [← hline, ← finsum_add_distrib fc fd, ← add_zero (∑ᶠ v, ord v (g v).det), ← (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).2,
      ← finsum_add_distrib fg fh]
    exact finsum_congr hpt
  · intro b hb E _ _ _ _ _ ρ hρ w hw
    let h' := h.map (algebraMap F E)
    have hne : h' *ᵥ w ≠ 0 := fun h0 => by
      have e : h'.det = algebraMap F E h.det := (RingHom.map_det _ _).symm
      exact (map_ne_zero _).2 hdet (e ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, h0⟩)
    have e : degLine (pullAd ρ fun v => u v * g v * h) w = degLine (pullAd ρ g) (h' *ᵥ w) := by
      unfold degLine
      exact finsum_congr fun p => GlobalTheory.IwaFam.ordVec_pull ρ hρ u g (fun _ => h) hu p w
    rw [e]
    exact hb E ρ hρ _ hne
