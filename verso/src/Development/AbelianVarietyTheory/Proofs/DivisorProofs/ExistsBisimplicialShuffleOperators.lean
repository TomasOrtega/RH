import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ.Shuf

/- English proof (translation)
Use `Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶ (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op)) (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶ (o …` as an intermediate fact. Simplify using `only [mul_one] at this`. Conclude with `this`.
-/
theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bop_id (n m : ℕ) : bop (𝟙 (SimplexCategory.mk n)) (𝟙 (SimplexCategory.mk m)) = 𝟙 (bo n m) := rfl

/- English proof (translation)
Use extensionality with `j`. Establish `hj : (j : ℕ) < n + 1` using `j.isLt`. Simplify using `only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]`. Express the relevant statement in the definitionally equal form `min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)`. Use linear arithmetic over natural numbers and integers.
-/
theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

/- English proof (translation)
Use extensionality with `k`. Establish `hk : (k : ℕ) < n + 1` using `k.isLt`. Simplify using `only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨i, j⟩ h`. Simplify using `only [Finset.mem_product, Finset.mem_range] at h`. Simplify using `only`.

Use `split_ifs with hji`. Simplify using `only`. Rewrite using `[fc_comp_fc n i j hji (by omega), ← add_smul]`. Take `⟨i', rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[show i' + 1 - 1 = i' by omega, pow_succ]`.

Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Simplify using `only`. Rewrite using `[fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]`. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Apply the tactic sequence `rintro ⟨i, j⟩ _ _ dsimp only split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega`. Introduce and unpack `⟨i, j⟩ h`. Simplify using `only [Finset.mem_product, Finset.mem_range] at h ⊢`. Apply the tactic sequence `split_ifs <;> simp only <;> omega`.

Introduce and unpack `⟨i, j⟩ _`. Distinguish the cases in `h : j < i`. Simplify using `only [h, if_true]`. Rewrite using `[if_neg (by omega)]`. Simplify using `only [Prod.mk.injEq, and_true, true_and]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [h, if_false]`. Rewrite using `[if_pos (by omega)]`. Simplify using `only [Prod.mk.injEq, and_true, true_and]`. Use linear arithmetic over natural numbers and integers.
-/
theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    dsimp only
    split_ifs with hji
    · dsimp only
      rw [fc_comp_fc n i j hji (by omega), ← add_smul]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show i' + 1 - 1 = i' by omega, pow_succ]
      ring_nf
      simp
    · dsimp only
      rw [fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]
      ring_nf
      simp
  · rintro ⟨i, j⟩ _ _
    dsimp only
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    split_ifs <;> simp only <;> omega
  · rintro ⟨i, j⟩ _
    by_cases h : j < i
    · simp only [h, if_true]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega
    · simp only [h, if_false]
      rw [if_pos (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega

/- English proof (translation)
Unfold `dH`. Distinguish the cases in `h1 : a = x + 1 ∧ b = y`. Distinguish the cases in `h2 : x = c + 1 ∧ y = d`. Take `⟨rfl, rfl⟩` from `h1`. Take `⟨rfl, rfl⟩` from `h2`.

Rewrite using `[if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]`. Simplify using `only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]`. Use `alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))` as an intermediate fact. Simplify `this` using `only [mul_comm]`. Rewrite using `[if_neg h2, comp_zero]`.

Rewrite using `[if_neg h1, zero_comp]`.
-/
theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

/- English proof (translation)
Unfold `dV`. Distinguish the cases in `h1 : a = x ∧ b = y + 1`. Distinguish the cases in `h2 : x = c ∧ y = d + 1`. Take `⟨rfl, rfl⟩` from `h1`. Take `⟨rfl, rfl⟩` from `h2`.

Rewrite using `[if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]`. Simplify using `only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]`. Use `alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)` as an intermediate fact. Simplify `this` using `only [mul_comm]`. Rewrite using `[if_neg h2, comp_zero]`.

Rewrite using `[if_neg h1, zero_comp]`.
-/
theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

/- English proof (translation)
Unfold `dH dV`. Rewrite using `[if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp, Preadditive.sum_comp]`. Simplify using `only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul, idc_self, Category.id_comp, Category.comp_id]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`.
-/
theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/- English proof (translation)
Substitute `hk` using the available equality. Establish `hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d = ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) + ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d)`. Introduce `x`. Simplify using `only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul, dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]`. Rewrite using `[add_comm]`.

Repeatedly rewrite using `[hsplit, Finset.sum_add_distrib]`. Establish `hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1)`. Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use linear arithmetic over natural numbers and integers. Establish `hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1)`.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]`. Simplify using `only`. Distinguish the cases in `h : a = c + 1 ∧ b = d + 1`.

Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[dH_comp_dV c d, ← add_smul, pow_succ]`. Simplify using the standard rewrite rules. Establish `e1 : dH a b c (d + 1) = 0` using `by unfold dH; rw [if_neg h]`. Establish `e2 : dV a b (c + 1) d = 0` using `by unfold dV; rw [if_neg h]`.

Rewrite using `[e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]`. Introduce and unpack `⟨x1, x2⟩ _ hx`. Establish `: dH x1 x2 c d = 0`. Unfold `dH`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hx rfl`. Simplify using `only`. Rewrite using `[this, comp_zero, smul_zero]`. Introduce and unpack `⟨x1, x2⟩ _ hx`.

Establish `: dV x1 x2 c d = 0`. Unfold `dV`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hx rfl`.

Simplify using `only`. Rewrite using `[this, comp_zero, smul_zero]`.
-/
theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  subst hk
  have hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d =
      ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) +
        ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d) := by
    intro x
    simp only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]
    rw [add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  have hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  rw [Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]
  · dsimp only
    by_cases h : a = c + 1 ∧ b = d + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [dH_comp_dV c d, ← add_smul, pow_succ]
      simp
    · have e1 : dH a b c (d + 1) = 0 := by unfold dH; rw [if_neg h]
      have e2 : dV a b (c + 1) d = 0 := by unfold dV; rw [if_neg h]
      rw [e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dH x1 x2 c d = 0 := by
      unfold dH; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dV x1 x2 c d = 0 := by
      unfold dV; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]

noncomputable def shufRec (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n : ℕ) :
    ∀ a b : ℕ, bo a b ⟶ bo n n :=
  Nat.rec (motive := fun n => ∀ a b : ℕ, bo a b ⟶ bo n n) (fun a b => idO a b 0 0)
    (fun n g a b => if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ g x.1 x.2) else 0) n

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shufRec_zero (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (a b : ℕ) :
    shufRec cone 0 a b = idO a b 0 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shufRec_succ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n a b : ℕ) :
    shufRec cone (n + 1) a b = if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ shufRec cone n x.1 x.2) else 0 := rfl

/- English proof (translation)
Take `⟨cone, ε, hε, h0, hs⟩` from `GlobalTheory.T.cone_contracting_homotopy`. Establish `hid : shufRec cone 0 0 0 = 𝟙 (bo 0 0)`. Rewrite using `[shufRec_zero]`. Rewrite using `[idO, if_pos ⟨rfl, rfl⟩, idc_self]`. Conclude with `bop_id 0 0`.

Use `⟨fun a b n => shufRec cone n a b, hid, ?_⟩` and prove the remaining obligations. Introduce `a b n`. Proceed by induction on `n generalizing a b with`. Consider the case `zero`. Introduce `hab`.

Simplify using `only`. Rewrite using `[shufRec_succ, if_pos hab, h0]`. Establish `hr : ε a b (∑ x ∈ Finset.HasAntidiagonal.antidiagonal 0, dT a b x.1 x.2 ≫ shufRec cone 0 x.1 x.2) = 0`. Rewrite using `[Finset.Nat.antidiagonal_zero, Finset.sum_singleton]`. Simplify using `only`.

Rewrite using `[hid, Category.comp_id]`. Take `⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)` from `by omega`. Simplify using `[dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]`. Simplify using `[dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]`. Rewrite using `[hr, zero_smul, sub_zero]`.

Consider the case `succ n ih`. Introduce `hab`. Simplify using `only at ih ⊢`. Rewrite using `[shufRec_succ, if_pos hab, hs]`. Establish `step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), (dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n = ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, (dT a b x.1 x.2 ≫ dT x.1 x.2 y.1 y.2) ≫ shufRec cone n y.1 y.2`.

Introduce `x hx`. Rewrite using `[Category.assoc, ih x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]`. Simplify using `only [Category.assoc]`. Establish `hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n = 0`. Rewrite using `[Preadditive.sum_comp, Finset.sum_congr rfl step, Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun y hy => ?_` and prove the remaining obligations. Rewrite using `[← Preadditive.sum_comp, dT_comp_dT a b y.1 y.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), zero_comp]`. Rewrite using `[hz, map_zero, sub_zero]`.
-/
theorem exists_shuffle : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧
    ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  obtain ⟨cone, ε, hε, h0, hs⟩ := GlobalTheory.T.cone_contracting_homotopy
  have hid : shufRec cone 0 0 0 = 𝟙 (bo 0 0) := by
    rw [shufRec_zero]
    rw [idO, if_pos ⟨rfl, rfl⟩, idc_self]
    exact bop_id 0 0
  refine ⟨fun a b n => shufRec cone n a b, hid, ?_⟩
  intro a b n
  induction n generalizing a b with
  | zero =>
    intro hab
    dsimp only
    rw [shufRec_succ, if_pos hab, h0]
    have hr : ε a b (∑ x ∈ Finset.HasAntidiagonal.antidiagonal 0, dT a b x.1 x.2 ≫ shufRec cone 0 x.1 x.2) = 0 := by
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      dsimp only
      rw [hid, Category.comp_id]
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
    rw [hr, zero_smul, sub_zero]
  | succ n ih =>
    intro hab
    dsimp only at ih ⊢
    rw [shufRec_succ, if_pos hab, hs]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
        (dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n =
          ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, (dT a b x.1 x.2 ≫ dT x.1 x.2 y.1 y.2) ≫
            shufRec cone n y.1 y.2 := by
      intro x hx
      rw [Category.assoc, ih x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
      simp only [Category.assoc]
    have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫
        dD (n + 1) n = 0 := by
      rw [Preadditive.sum_comp, Finset.sum_congr rfl step, Finset.sum_comm]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [← Preadditive.sum_comp, dT_comp_dT a b y.1 y.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), zero_comp]
    rw [hz, map_zero, sub_zero]

end GlobalTheory.EZ.Shuf
