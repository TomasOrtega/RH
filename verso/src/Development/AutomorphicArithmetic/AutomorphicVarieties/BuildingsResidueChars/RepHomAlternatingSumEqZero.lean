import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory UpperTheory.V.Af.BA in
private def repHomEvalLinearMap {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} (x : A) : (A ⟶ B) →ₗ[ℂ] B where
  toFun φ := φ.hom x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open CategoryTheory UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `Γ I _ _ K`. Establish `key : ∀ (p : ℕ) (t : K.Tup p), (K.alt p).hom (Finsupp.single t 1) = ((p + 1).factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin (p + 1)), ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ)`. Introduce `p t`. Use `show repHomEvalLinearMap (B := PC Γ (K.Tup p)) (Finsupp.single t (1 : ℂ)) (K.alt p) = _`. Simplify using `only [Cx.alt, map_smul, map_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `π _`. Use `congr 1`. Conclude with `Cx.reC_single K _ t 1`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `PC_ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[key 0 x]`. Establish `hre : K.re (id : Fin 1 → Fin 1) x = x` using `Subtype.ext rfl`.

Simplify using `[Fintype.sum_unique, hre]`. Introduce `p hp`. Apply `PC_ext` to reduce the goal to its premises. Introduce `t`. Rewrite using `[key p t]`.

Establish `hnt` using `hp t`. Simplify using `only [Function.Injective, not_forall] at hnt`. Take `⟨a, b, htab, hab⟩` from `hnt`. Establish `ht : ∀ y, Subtype.val t (Equiv.swap a b y) = Subtype.val t y`. Introduce `y`.

Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`. Rewrite using `[h1, htab]`. Rewrite using `[h2, htab]`. Both sides reduce to the same expression.

Use `set S := ∑ π : Equiv.Perm (Fin (p + 1)), ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) with hSdef`. Establish `hS : S = -S` using `by conv_lhs => rw [hSdef, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))]`. Rewrite using `[hSdef, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `π _`.

Establish `hre : K.re (⇑((Equiv.mulLeft (Equiv.swap a b)) π)) t = K.re π t` using `Subtype.ext (funext fun k => by simp [Cx.re, Equiv.Perm.mul_apply, ht])`. Rewrite using `[hre, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]`. Use `push_cast`. Rewrite using `[neg_one_mul, neg_smul]`. Establish `hS0 : S = 0` using `self_eq_neg.1 hS`.

Rewrite using `[hS0, smul_zero]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.rep_hom_alternating_sum_eq_zero :
    UpperTheory.V.Af.BA.AltZero := by
  intro Γ I _ _ K
  have key : ∀ (p : ℕ) (t : K.Tup p), (K.alt p).hom (Finsupp.single t 1) =
      ((p + 1).factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin (p + 1)),
        ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) := by
    intro p t
    show repHomEvalLinearMap (B := PC Γ (K.Tup p)) (Finsupp.single t (1 : ℂ)) (K.alt p) = _
    simp only [Cx.alt, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro π _
    congr 1
    exact Cx.reC_single K _ t 1
  refine ⟨?_, ?_⟩
  · apply PC_ext
    intro x
    rw [key 0 x]
    have hre : K.re (id : Fin 1 → Fin 1) x = x := Subtype.ext rfl
    simp [Fintype.sum_unique, hre]
  · intro p hp
    apply PC_ext
    intro t
    rw [key p t]
    have hnt := hp t
    simp only [Function.Injective, not_forall] at hnt
    obtain ⟨a, b, htab, hab⟩ := hnt
    have ht : ∀ y, Subtype.val t (Equiv.swap a b y) = Subtype.val t y := by
      intro y
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, htab]
      · rw [h2, htab]
      · rfl
    set S := ∑ π : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))]
      rw [hSdef, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro π _
      have hre : K.re (⇑((Equiv.mulLeft (Equiv.swap a b)) π)) t = K.re π t :=
        Subtype.ext (funext fun k => by simp [Cx.re, Equiv.Perm.mul_apply, ht])
      rw [hre, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      push_cast
      rw [neg_one_mul, neg_smul]
    have hS0 : S = 0 := self_eq_neg.1 hS
    rw [hS0, smul_zero]
    rfl
