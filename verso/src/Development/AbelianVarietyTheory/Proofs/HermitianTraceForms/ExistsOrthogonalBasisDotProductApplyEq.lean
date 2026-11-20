import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.HermDiag

open Module Matrix

section Abstract

variable {E : Type*} [Field E] {c : E →+* E}

/- English proof (translation)
Use extensionality with `x y`. Assume the negation of the conclusion as `hne`. Establish `hne' : B x y ≠ 0` using `by simpa using hne`. Establish `h1 : B ((B x y)⁻¹ • x) y = 1`. Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne']`.

Establish `h1' : B y ((B x y)⁻¹ • x) = 1` using `by rw [← hB, h1, map_one]`. Establish `h3` using `h0 ((B x y)⁻¹ • x + y)`. Rewrite `h3` using `[map_add, LinearMap.map_add₂, LinearMap.map_add₂, h0, h0, h1, h1']`. Apply `h2` to reduce the goal to its premises. Take the linear combination `h3`.
-/
theorem eq_zero_of_apply_self_eq_zero {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (h0 : ∀ x, B x x = 0) : B = 0 := by
  ext x y
  by_contra hne
  have hne' : B x y ≠ 0 := by simpa using hne
  have h1 : B ((B x y)⁻¹ • x) y = 1 := by
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne']
  have h1' : B y ((B x y)⁻¹ • x) = 1 := by rw [← hB, h1, map_one]
  have h3 := h0 ((B x y)⁻¹ • x + y)
  rw [map_add, LinearMap.map_add₂, LinearMap.map_add₂, h0, h0, h1, h1'] at h3
  apply h2
  linear_combination h3

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (eq_zero_of_apply_self_eq_zero h2 hB h)`.
-/
theorem exists_apply_self_ne_zero {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hne : B ≠ 0) : ∃ x, B x x ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (eq_zero_of_apply_self_eq_zero h2 hB h)

/- English proof (translation)
Establish `hr : LinearMap.range (B.flip x) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `t`. Use `⟨(t / B x x) • x, ?_⟩` and prove the remaining obligations. Simplify using `[div_mul_cancel₀ _ hx]`.

Use `LinearMap.finrank_range_add_finrank_ker (B.flip x)` as an intermediate fact. Rewrite `this` using `[hr, finrank_top, finrank_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_ker_flip_add_one {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} {x : V} (hx : B x x ≠ 0) :
    finrank E (LinearMap.ker (B.flip x)) + 1 = finrank E V := by
  have hr : LinearMap.range (B.flip x) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨(t / B x x) • x, ?_⟩
    simp [div_mul_cancel₀ _ hx]
  have := LinearMap.finrank_range_add_finrank_ker (B.flip x)
  rw [hr, finrank_top, finrank_self] at this
  omega

/- English proof (translation)
Set `b : Basis (Fin (d + 1)) E V` to `Basis.mkFinCons x v' (by`. Introduce `t y hy hc`. Establish `hy' : B y x = 0` using `by simpa using hy`. Establish `h3 : B (t • x + y) x = 0` using `by rw [hc]; simp`. Rewrite `h3` using `[LinearMap.map_add, LinearMap.add_apply, hy', add_zero, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 h3).resolve_right hx)`. Use the proof step `(by`. Introduce `y`. Use `⟨-B y x / B x x, ?_⟩` and prove the remaining obligations. Simplify using `[div_mul_cancel₀ _ hx])`.

Establish `hk : ∀ i, B (v' i) x = 0` using `fun i => (v' i).prop`. Use `⟨b, by simp [b], ?_⟩` and prove the remaining obligations. Simplify using `only [b, Basis.coe_mkFinCons]`. Introduce `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]`. Conclude with `(hij rfl).elim`. Rewrite using `[← hB, hk, map_zero]`. Conclude with `hk i`. Conclude with `hv' i j (ne_of_apply_ne _ hij)`.
-/
theorem exists_orthogonal_basis_cons_of_ker {V : Type*} [AddCommGroup V] [Module E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) {x : V} (hx : B x x ≠ 0) {d : ℕ}
    (v' : Basis (Fin d) E (LinearMap.ker (B.flip x)))
    (hv' : ∀ i j, i ≠ j → B (v' i) (v' j) = 0) :
    ∃ v : Basis (Fin (d + 1)) E V, v 0 = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  let b : Basis (Fin (d + 1)) E V :=
    Basis.mkFinCons x v'
      (by
        intro t y hy hc
        have hy' : B y x = 0 := by simpa using hy
        have h3 : B (t • x + y) x = 0 := by rw [hc]; simp
        rw [LinearMap.map_add, LinearMap.add_apply, hy', add_zero, LinearMap.map_smul,
          LinearMap.smul_apply, smul_eq_mul] at h3
        exact (mul_eq_zero.1 h3).resolve_right hx)
      (by
        intro y
        refine ⟨-B y x / B x x, ?_⟩
        simp [div_mul_cancel₀ _ hx])
  have hk : ∀ i, B (v' i) x = 0 := fun i => (v' i).prop
  refine ⟨b, by simp [b], ?_⟩
  simp only [b, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [← hB, hk, map_zero]
  · exact hk i
  · exact hv' i j (ne_of_apply_ne _ hij)

universe u in

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `V _ _ _ B _ hd`. Conclude with `⟨basisOfFinrankZero hd, fun i => i.elim0⟩`. Consider the case `succ d ih`.

Introduce `V _ _ _ B hB hd`. Take `rfl | hne` from `eq_or_ne B 0`. Conclude with `⟨Module.finBasisOfFinrankEq E V hd, fun _ _ _ => rfl⟩`. Take `⟨x, hx⟩` from `exists_apply_self_ne_zero h2 hB hne`. Establish `hk` using `finrank_ker_flip_add_one hx`.

Take `⟨v', hv'⟩` from `ih (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x))) (fun y z => hB y z) (by omega)`. Take `⟨v, -, hv⟩` from `exists_orthogonal_basis_cons_of_ker hB hx v' hv'`. Conclude with `⟨v, hv⟩`.
-/
theorem exists_orthogonal_basis_fin (h2 : (2 : E) ≠ 0) (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (B : V →ₗ[E] V →ₛₗ[c] E), (∀ x y, c (B x y) = B y x) → finrank E V = d →
      ∃ v : Basis (Fin d) E V, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  induction d with
  | zero =>
    intro V _ _ _ B _ hd
    exact ⟨basisOfFinrankZero hd, fun i => i.elim0⟩
  | succ d ih =>
    intro V _ _ _ B hB hd
    obtain rfl | hne := eq_or_ne B 0
    · exact ⟨Module.finBasisOfFinrankEq E V hd, fun _ _ _ => rfl⟩
    obtain ⟨x, hx⟩ := exists_apply_self_ne_zero h2 hB hne
    have hk := finrank_ker_flip_add_one hx
    obtain ⟨v', hv'⟩ := ih
      (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x)))
      (fun y z => hB y z) (by omega)
    obtain ⟨v, -, hv⟩ := exists_orthogonal_basis_cons_of_ker hB hx v' hv'
    exact ⟨v, hv⟩

variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {n : Type*} [Fintype n]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_orthogonal_basis_fin h2 _ B hB hn`. Use `⟨v.reindex (Fintype.equivFin n).symm, fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `only [Basis.reindex_apply]`. Conclude with `hv _ _ (fun h => hij ((Equiv.injective _) h))`.
-/
theorem exists_orthogonal_basis (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) (hn : finrank E V = Fintype.card n) :
    ∃ v : Basis n E V, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 _ B hB hn
  refine ⟨v.reindex (Fintype.equivFin n).symm, fun i j hij => ?_⟩
  simp only [Basis.reindex_apply]
  exact hv _ _ (fun h => hij ((Equiv.injective _) h))

/- English proof (translation)
Establish `hk` using `finrank_ker_flip_add_one hx`. Take `⟨v', hv'⟩` from `exists_orthogonal_basis_fin h2 _ (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x))) (fun y z => hB y z) rfl`. Take `⟨v, hv0, hv⟩` from `exists_orthogonal_basis_cons_of_ker hB hx v' hv'`. Set `e₀ : n ≃ Fin (finrank E (LinearMap.ker (B.flip x)) + 1)` to `Fintype.equivFinOfCardEq (by omega)`. Set `e` to `e₀.trans (Equiv.swap (e₀ i₀) 0)`.

Establish `he : e i₀ = 0` using `by simp [e]`. Use `⟨v.reindex e.symm, ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.reindex_apply, Equiv.symm_symm, he, hv0]`. Simplify using `only [Basis.reindex_apply]`. Conclude with `hv _ _ (fun h => hij ((Equiv.injective _) h))`.
-/
theorem exists_orthogonal_basis_apply_eq (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) (hn : finrank E V = Fintype.card n) {x : V}
    (hx : B x x ≠ 0) (i₀ : n) :
    ∃ v : Basis n E V, v i₀ = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  classical
  have hk := finrank_ker_flip_add_one hx
  obtain ⟨v', hv'⟩ := exists_orthogonal_basis_fin h2 _
    (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x)))
    (fun y z => hB y z) rfl
  obtain ⟨v, hv0, hv⟩ := exists_orthogonal_basis_cons_of_ker hB hx v' hv'
  let e₀ : n ≃ Fin (finrank E (LinearMap.ker (B.flip x)) + 1) :=
    Fintype.equivFinOfCardEq (by omega)
  let e := e₀.trans (Equiv.swap (e₀ i₀) 0)
  have he : e i₀ = 0 := by simp [e]
  refine ⟨v.reindex e.symm, ?_, fun i j hij => ?_⟩
  · rw [Basis.reindex_apply, Equiv.symm_symm, he, hv0]
  · simp only [Basis.reindex_apply]
    exact hv _ _ (fun h => hij ((Equiv.injective _) h))

end Abstract

section MatrixForm

variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem dotProduct_mulVec_comp_eq_sum (c : E → E) (G : Matrix n n E) (x y : n → E) :
    x ⬝ᵥ G *ᵥ (c ∘ y) = ∑ a, ∑ b, x a * G a b * c (y b) := by
  simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem transpose_mul_mul_map_apply {m : Type*} (c : E → E) (G : Matrix n n E) (P : Matrix n m E)
    (a b : m) :
    (Pᵀ * G * P.map c) a b = (fun k => P k a) ⬝ᵥ G *ᵥ (c ∘ fun k => P k b) := by
  rw [Matrix.mul_assoc]
  rfl

/- English proof (translation)
Simplify using `only [dotProduct_mulVec_comp_eq_sum, map_sum, map_mul, hc, hG]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_dotProduct_mulVec_comp (hc : ∀ t, c (c t) = t) {G : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (x y : n → E) :
    c (x ⬝ᵥ G *ᵥ (c ∘ y)) = y ⬝ᵥ G *ᵥ (c ∘ x) := by
  simp only [dotProduct_mulVec_comp_eq_sum, map_sum, map_mul, hc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

variable [DecidableEq n]

/- English proof (translation)
Rewrite using `[Matrix.toLinearMapₛₗ₂'_apply, dotProduct_mulVec_comp_eq_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toLinearMapₛₗ₂'_eq_dotProduct (c : E →+* E) (G : Matrix n n E) (x y : n → E) :
    Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G x y = x ⬝ᵥ G *ᵥ (c ∘ y) := by
  rw [Matrix.toLinearMapₛₗ₂'_apply, dotProduct_mulVec_comp_eq_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_orthogonal_basis (n := n) h2 (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G) (fun x y => by`. Simplify using `only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])`. Use the proof step `(Module.finrank_fintype_fun_eq_card E)`. Conclude with `⟨v, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hv⟩`.
-/
theorem exists_orthogonal_basis_dotProduct (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) :
    ∃ v : Basis n E (n → E), ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0 := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis (n := n) h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (Module.finrank_fintype_fun_eq_card E)
  exact ⟨v, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hv⟩

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `exists_orthogonal_basis_apply_eq (n := n) h2 (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G) (fun x y => by`. Simplify using `only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])`. Use the proof step `(Module.finrank_fintype_fun_eq_card E) (x := x)`. Use the proof step `(by rwa [toLinearMapₛₗ₂'_eq_dotProduct]) i₀`. Conclude with `⟨v, hv0, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hv⟩`.
-/
theorem exists_orthogonal_basis_dotProduct_apply_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x : n → E}
    (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) (i₀ : n) :
    ∃ v : Basis n E (n → E), v i₀ = x ∧ ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_orthogonal_basis_apply_eq (n := n) h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (Module.finrank_fintype_fun_eq_card E) (x := x)
    (by rwa [toLinearMapₛₗ₂'_eq_dotProduct]) i₀
  exact ⟨v, hv0, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hv⟩

/- English proof (translation)
Establish `h : (Matrix.of fun k i => v i k) = (Pi.basisFun E n).toMatrix v`. Use extensionality with `k i`. Simplify using `[Basis.toMatrix_apply]`. Rewrite using `[h]`. Use `letI := (Pi.basisFun E n).invertibleToMatrix v`.

Conclude with `(Matrix.isUnit_det_of_invertible _).ne_zero`.
-/
theorem det_of_basis_ne_zero (v : Basis n E (n → E)) :
    (Matrix.of fun k i => v i k).det ≠ 0 := by
  have h : (Matrix.of fun k i => v i k) = (Pi.basisFun E n).toMatrix v := by
    ext k i
    simp [Basis.toMatrix_apply]
  rw [h]
  letI := (Pi.basisFun E n).invertibleToMatrix v
  exact (Matrix.isUnit_det_of_invertible _).ne_zero

/- English proof (translation)
Establish `h` using `congrArg Matrix.det hd`. Establish `hm : (P.map c).det = c P.det` using `(RingHom.map_det c P).symm`. Rewrite `h` using `[det_mul, det_mul, det_transpose, hm, det_diagonal]`. Establish `hne : ∏ i, d i ≠ 0`. Rewrite using `[← h]`.

Conclude with `mul_ne_zero (mul_ne_zero hP hG) ((map_ne_zero c).2 hP)`. Conclude with `Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i)`.
-/
theorem ne_zero_of_congr_diagonal {G P : Matrix n n E} {d : n → E} (hP : P.det ≠ 0)
    (hd : Pᵀ * G * P.map c = Matrix.diagonal d) (hG : G.det ≠ 0) (i : n) : d i ≠ 0 := by
  have h := congrArg Matrix.det hd
  have hm : (P.map c).det = c P.det := (RingHom.map_det c P).symm
  rw [det_mul, det_mul, det_transpose, hm, det_diagonal] at h
  have hne : ∏ i, d i ≠ 0 := by
    rw [← h]
    exact mul_ne_zero (mul_ne_zero hP hG) ((map_ne_zero c).2 hP)
  exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[transpose_mul_mul_map_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[diagonal_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[diagonal_apply_ne _ hij]`. Conclude with `hv i j hij`.
-/
theorem congr_diagonal_of_orthogonal {G : Matrix n n E} (c : E → E) (v : n → n → E)
    (hv : ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0) :
    (Matrix.of fun k i => v i k)ᵀ * G * (Matrix.of fun k i => v i k).map c =
      Matrix.diagonal fun i => v i ⬝ᵥ G *ᵥ (c ∘ v i) := by
  ext i j
  rw [transpose_mul_mul_map_apply]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
    rfl
  · rw [diagonal_apply_ne _ hij]
    exact hv i j hij

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_orthogonal_basis_dotProduct h2 hc hG`. Establish `hd` using `congr_diagonal_of_orthogonal c v hv`. Conclude with `⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _, ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd⟩`.
-/
theorem exists_congr_diagonal (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) :
    ∃ (P : Matrix n n E) (d : n → E), P.det ≠ 0 ∧ Pᵀ * G * P.map c = Matrix.diagonal d ∧
      (∀ i, c (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_dotProduct h2 hc hG
  have hd := congr_diagonal_of_orthogonal c v hv
  exact ⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _,
    ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd⟩

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `exists_orthogonal_basis_dotProduct_apply_eq h2 hc hG hx i₀`. Establish `hd` using `congr_diagonal_of_orthogonal c v hv`. Conclude with `⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _, ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd, fun k => by simp [hv0], by simp only [hv0]⟩`.
-/
theorem exists_congr_diagonal_col_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x : n → E}
    (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) (i₀ : n) :
    ∃ (P : Matrix n n E) (d : n → E), P.det ≠ 0 ∧ Pᵀ * G * P.map c = Matrix.diagonal d ∧
      (∀ i, c (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) ∧
      (∀ k, P k i₀ = x k) ∧ d i₀ = x ⬝ᵥ G *ᵥ (c ∘ x) := by
  obtain ⟨v, hv0, hv⟩ := exists_orthogonal_basis_dotProduct_apply_eq h2 hc hG hx i₀
  have hd := congr_diagonal_of_orthogonal c v hv
  exact ⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _,
    ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd, fun k => by simp [hv0],
    by simp only [hv0]⟩

end MatrixForm

section CM

open NumberField ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
The claim follows from `(dotProduct_mulVec_comp_eq_sum FD.cc G x y).symm`.
-/
theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    FD.herm G x y = x ⬝ᵥ G *ᵥ (FD.cc ∘ y) :=
  (dotProduct_mulVec_comp_eq_sum FD.cc G x y).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_complexConj_ringHom :
    ⇑((IsCMField.complexConj E : E →+* E)) = FD.cc := rfl

/- English proof (translation)
The claim follows from `exists_congr_diagonal (c := (IsCMField.complexConj E : E →+* E)) two_ne_zero (IsCMField.complexConj_apply_apply E) hG`.
-/
theorem exists_congr_diagonal_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    ∃ (P : Matrix (Fin r) (Fin r) E) (d : Fin r → E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = Matrix.diagonal d ∧
      (∀ i, FD.cc (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) :=
  exists_congr_diagonal (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG

/- English proof (translation)
Simplify using `only [herm_eq_dotProduct] at hx ⊢`. Conclude with `exists_congr_diagonal_col_eq (c := (IsCMField.complexConj E : E →+* E)) two_ne_zero (IsCMField.complexConj_apply_apply E) hG hx i₀`.
-/
theorem exists_congr_diagonal_herm_col_eq {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) {x : Fin r → E} (hx : FD.herm G x x ≠ 0) (i₀ : Fin r) :
    ∃ (P : Matrix (Fin r) (Fin r) E) (d : Fin r → E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = Matrix.diagonal d ∧
      (∀ i, FD.cc (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) ∧
      (∀ k, P k i₀ = x k) ∧ d i₀ = FD.herm G x x := by
  simp only [herm_eq_dotProduct] at hx ⊢
  exact exists_congr_diagonal_col_eq (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hx i₀

end CM

end GlobalTheory.HermDiag
