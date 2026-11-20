import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.TensorInd

section Paths

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]`. Conclude with `Fintype.sum_equiv e.symm _ _ (fun _ => rfl)`.
-/
theorem trace_reindex_eq {m : Type} [Fintype m] (e : n ≃ m) (A : Matrix n n ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `B a c`. Simplify using `[Fin.snoc]`.

Consider the case `succ k ih`. Introduce `B a c`. Rewrite using `[List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_apply]`. Rewrite using `[← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations.

Rewrite using `[← ih (B ∘ Nat.succ) x c, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations. Establish `hc : (Fin.consEquiv fun _ => n) (x, w) = Fin.cons x w` using `rfl`. Rewrite using `[Fin.prod_univ_succ, hc, ← Fin.cons_snoc_eq_snoc_cons]`. Simplify using `only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc, Function.comp_apply, Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one]`.
-/
theorem path_sum : ∀ (k : ℕ) (B : ℕ → Matrix n n ℂ) (a c : n),
    ∑ w : Fin k → n, ∏ i : Fin (k + 1),
      B i ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc)
        ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ)
      = ((List.range (k + 1)).map B).prod a c := by
  intro k
  induction k with
  | zero =>
    intro B a c
    simp [Fin.snoc]
  | succ k ih =>
    intro B a c
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← ih (B ∘ Nat.succ) x c, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hc : (Fin.consEquiv fun _ => n) (x, w) = Fin.cons x w := rfl
    rw [Fin.prod_univ_succ, hc, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc, Function.comp_apply,
      Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one]

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]`. Simplify using `only [Matrix.trace, Matrix.diag]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← path_sum k B a a]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations.

Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hc : (Fin.consEquiv fun _ => n) (a, w) = Fin.cons a w` using `rfl`. Establish `h1 : (Fin.cons a w : Fin (k + 1) → n) i = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => simp`.

Consider the case `succ j => rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]`. Establish `h2 : (Fin.cons a w : Fin (k + 1) → n) (i + 1) = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ`. Rewrite using `[Fin.cons_succ]`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last => rw [Fin.last_add_one, Fin.snoc_last, Fin.cons_zero]`.

Consider the case `cast j => rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]`. Rewrite using `[hc, h1, h2]`.
-/
theorem cyc_sum (k : ℕ) (B : ℕ → Matrix n n ℂ) :
    ∑ w : Fin (k + 1) → n, ∏ i : Fin (k + 1), B i (w i) (w (i + 1))
      = Matrix.trace ((List.range (k + 1)).map B).prod := by
  rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← path_sum k B a a]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hc : (Fin.consEquiv fun _ => n) (a, w) = Fin.cons a w := rfl
  have h1 : (Fin.cons a w : Fin (k + 1) → n) i
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc := by
    cases i using Fin.cases with
    | zero => simp
    | succ j => rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
  have h2 : (Fin.cons a w : Fin (k + 1) → n) (i + 1)
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ := by
    rw [Fin.cons_succ]
    cases i using Fin.lastCases with
    | last => rw [Fin.last_add_one, Fin.snoc_last, Fin.cons_zero]
    | cast j => rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]
  rw [hc, h1, h2]

end Paths

section Rep

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

def ker (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) (r : Γ) :
    Matrix (Γ → Fin d) (Γ → Fin d) ℂ :=
  fun u v => ∏ t, (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) (u t) (v (t * r))

/- English proof (translation)
Use extensionality with `u v`. Simplify using `only [ker, map_one, Units.val_one, mul_one]`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Take `⟨t, ht⟩` from `Function.ne_iff.1 h`. Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ t) (Matrix.one_apply_ne ht)`.
-/
theorem ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : ker ρ φ 1 1 = 1 := by
  ext u v
  simp only [ker, map_one, Units.val_one, mul_one]
  by_cases h : u = v
  · subst h
    simp
  · obtain ⟨t, ht⟩ := Function.ne_iff.1 h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (Matrix.one_apply_ne ht)

/- English proof (translation)
Use extensionality with `u v`. Simplify using `only [Matrix.mul_apply, ker]`. Establish `hre : ∀ w : Γ → Fin d, ∏ t, (ρ (φ t g₂) : Matrix (Fin d) (Fin d) ℂ) (w t) (v (t * r₂)) = ∏ t, (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) (w (t * r₁)) (v (t * r₁ * r₂))` using `fun w => (Fintype.prod_equiv (Equiv.mulRight r₁) _ _ (fun t => rfl)).symm`. Repeatedly rewrite using `[hre, ← Finset.prod_mul_distrib]`. Rewrite using `[← (Equiv.arrowCongr (Equiv.mulRight r₁) (Equiv.refl (Fin d))).sum_comp]`.

Simplify using `only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.coe_mulRight, Equiv.mulRight_symm, mul_inv_cancel_right, id]`. Use `(Fintype.prod_sum (fun t (j : Fin d) => (ρ (φ t g₁) : Matrix (Fin d) (Fin d) ℂ) (u t) j * (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) j (v (t * r₁ * r₂)))).symm.trans ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul (φ t), ← MulAut.mul_apply, ← map_mul φ, map_mul ρ, Units.val_mul, Matrix.mul_apply, mul_assoc]`.
-/
theorem ker_mul (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g₁ g₂ : G) (r₁ r₂ : Γ) :
    ker ρ φ g₁ r₁ * ker ρ φ g₂ r₂ = ker ρ φ (g₁ * φ r₁ g₂) (r₁ * r₂) := by
  ext u v
  simp only [Matrix.mul_apply, ker]
  have hre : ∀ w : Γ → Fin d, ∏ t, (ρ (φ t g₂) : Matrix (Fin d) (Fin d) ℂ) (w t) (v (t * r₂))
      = ∏ t, (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) (w (t * r₁)) (v (t * r₁ * r₂)) :=
    fun w => (Fintype.prod_equiv (Equiv.mulRight r₁) _ _ (fun t => rfl)).symm
  simp_rw [hre, ← Finset.prod_mul_distrib]
  rw [← (Equiv.arrowCongr (Equiv.mulRight r₁) (Equiv.refl (Fin d))).sum_comp]
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.coe_mulRight,
    Equiv.mulRight_symm, mul_inv_cancel_right, id]
  refine (Fintype.prod_sum (fun t (j : Fin d) =>
    (ρ (φ t g₁) : Matrix (Fin d) (Fin d) ℂ) (u t) j *
      (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) j (v (t * r₁ * r₂)))).symm.trans ?_
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [map_mul (φ t), ← MulAut.mul_apply, ← map_mul φ, map_mul ρ, Units.val_mul, Matrix.mul_apply, mul_assoc]

def tensRep (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : G ⋊[φ] Γ →* Matrix (Γ → Fin d) (Γ → Fin d) ℂ where
  toFun x := ker ρ φ x.left x.right
  map_one' := by simpa using ker_one ρ φ
  map_mul' x y := by rw [ker_mul]; simp

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, ker, mul_one]`. Rewrite using `[Fintype.prod_sum]`.
-/
theorem trace_ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) :
    Matrix.trace (ker ρ φ g 1) = ∏ t, Matrix.trace (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [Matrix.trace, Matrix.diag, ker, mul_one]
  rw [Fintype.prod_sum]

end Rep

end GlobalTheory.Shin.TensorInd

namespace GlobalTheory.Shin.TensorInd

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

/- English proof (translation)
Establish `hl : orderOf s = Nat.card Γ` using `orderOf_eq_card_of_forall_mem_zpowers hs`. Take `⟨k, hk⟩ : ∃ k, Nat.card Γ = k + 1` from `Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Γ)).ne'`. Rewrite `hl`, the goal using `[hk]`. Establish `hinj : Function.Injective (fun i : Fin (k + 1) => s ^ (i : ℕ))`. Introduce `i j hij`.

Use `pow_injOn_Iio_orderOf (x := s) (by rw [hl]; exact i.2) (by rw [hl]; exact j.2) hij` as an intermediate fact. Conclude with `Fin.ext this`. Establish `hbij : Function.Bijective (fun i : Fin (k + 1) => s ^ (i : ℕ))`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨hinj, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.card_fin, ← Nat.card_eq_fintype_card, hk]`. Set `e : Fin (k + 1) ≃ Γ` to `Equiv.ofBijective _ hbij`. Establish `he : ∀ i : Fin (k + 1), e i * s = e (i + 1)`. Introduce `i`. Use `show s ^ (i : ℕ) * s = s ^ ((i + 1 : Fin (k + 1)) : ℕ)`.

Establish `hv : ((i + 1 : Fin (k + 1)) : ℕ) = ((i : ℕ) + 1) % orderOf s`. Rewrite using `[hl, Fin.val_add_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Nat.mod_eq_of_lt]`. Use `Fin.val_lt_last h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hv, pow_mod_orderOf, pow_succ]`. Rewrite using `[← cyc_sum k (fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ))]`.

Simplify using `only [Matrix.trace, Matrix.diag, ker]`. Rewrite using `[← (Equiv.arrowCongr e (Equiv.refl (Fin d))).sum_comp]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations. Rewrite using `[← e.prod_comp]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Simplify using `only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, he, Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem trace_ker_gen (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (s : Γ)
    (hs : ∀ t : Γ, t ∈ Subgroup.zpowers s) (δ : G) :
    Matrix.trace (ker ρ φ δ s) = Matrix.trace (((List.range (Nat.card Γ)).map
      fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ)).prod) := by
  have hl : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  obtain ⟨k, hk⟩ : ∃ k, Nat.card Γ = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Γ)).ne'
  rw [hk] at hl ⊢
  have hinj : Function.Injective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    intro i j hij
    have := pow_injOn_Iio_orderOf (x := s) (by rw [hl]; exact i.2) (by rw [hl]; exact j.2) hij
    exact Fin.ext this
  have hbij : Function.Bijective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hk]
  let e : Fin (k + 1) ≃ Γ := Equiv.ofBijective _ hbij
  have he : ∀ i : Fin (k + 1), e i * s = e (i + 1) := by
    intro i
    show s ^ (i : ℕ) * s = s ^ ((i + 1 : Fin (k + 1)) : ℕ)
    have hv : ((i + 1 : Fin (k + 1)) : ℕ) = ((i : ℕ) + 1) % orderOf s := by
      rw [hl, Fin.val_add_one]
      split_ifs with h
      · subst h; simp
      · rw [Nat.mod_eq_of_lt]
        have := Fin.val_lt_last h
        omega
    rw [hv, pow_mod_orderOf, pow_succ]
  rw [← cyc_sum k (fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ))]
  simp only [Matrix.trace, Matrix.diag, ker]
  rw [← (Equiv.arrowCongr e (Equiv.refl (Fin d))).sum_comp]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, he, Equiv.symm_apply_apply]
  rfl

/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hs χ hχ`. Take `⟨d, ρ, hρ⟩` from `(matrixChar_iff_isChar G χ).2 hχ`. Set `e` to `Fintype.equivFin (Γ → Fin d)`. Set `R : G ⋊[φ] Γ →* GL (Fin (Fintype.card (Γ → Fin d))) ℂ` to `MonoidHom.toHomUnits (((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom).comp (tensRep ρ φ))`. Use `⟨fun x => Matrix.trace (tensRep ρ φ x), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `(matrixChar_iff_isChar _ _).1 ⟨_, R, fun x => ?_⟩ show _ = Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e (tensRep ρ φ x))` and prove the remaining obligations. Rewrite using `[Matrix.reindexAlgEquiv_apply, trace_reindex_eq]`. Introduce `g show Matrix.trace (ker ρ φ (inl g).left (inl g).right) = _`. Rewrite using `[left_inl, right_inl, trace_ker_one]`. Conclude with `Finset.prod_congr rfl (fun t _ => (hρ _).symm)`.

Introduce `δ show Matrix.trace (ker ρ φ (inl δ * inr s).left (inl δ * inr s).right) = _`. Establish `h1 : (inl δ * inr s : G ⋊[φ] Γ).left = δ` using `by simp`. Establish `h2 : (inl δ * inr s : G ⋊[φ] Γ).right = s` using `by simp`. Rewrite using `[h1, h2, trace_ker_gen ρ φ s hs δ, hρ, nrmG]`. Use `congr 1`.

Establish `hm` using `map_list_prod ((Units.coeHom (Matrix (Fin d) (Fin d) ℂ)).comp ρ) ((List.range (Nat.card Γ)).map fun i => φ (s ^ i) δ)`. Rewrite `hm` using `[List.map_map]`. Conclude with `hm.symm`.
-/
theorem exists_tensorInduction_char : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hs χ hχ
  obtain ⟨d, ρ, hρ⟩ := (matrixChar_iff_isChar G χ).2 hχ
  let e := Fintype.equivFin (Γ → Fin d)
  let R : G ⋊[φ] Γ →* GL (Fin (Fintype.card (Γ → Fin d))) ℂ := MonoidHom.toHomUnits
    (((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom).comp (tensRep ρ φ))
  refine ⟨fun x => Matrix.trace (tensRep ρ φ x), ?_, ?_, ?_⟩
  · refine (matrixChar_iff_isChar _ _).1 ⟨_, R, fun x => ?_⟩
    show _ = Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e (tensRep ρ φ x))
    rw [Matrix.reindexAlgEquiv_apply, trace_reindex_eq]
  · intro g
    show Matrix.trace (ker ρ φ (inl g).left (inl g).right) = _
    rw [left_inl, right_inl, trace_ker_one]
    exact Finset.prod_congr rfl (fun t _ => (hρ _).symm)
  · intro δ
    show Matrix.trace (ker ρ φ (inl δ * inr s).left (inl δ * inr s).right) = _
    have h1 : (inl δ * inr s : G ⋊[φ] Γ).left = δ := by simp
    have h2 : (inl δ * inr s : G ⋊[φ] Γ).right = s := by simp
    rw [h1, h2, trace_ker_gen ρ φ s hs δ, hρ, nrmG]
    congr 1
    have hm := map_list_prod ((Units.coeHom (Matrix (Fin d) (Fin d) ℂ)).comp ρ)
      ((List.range (Nat.card Γ)).map fun i => φ (s ^ i) δ)
    rw [List.map_map] at hm
    exact hm.symm

end GlobalTheory.Shin.TensorInd
