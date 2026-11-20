import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Simplify using `[kun, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]`.
-/
private lemma kun_lof {k : Type} [Field k] (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (p : X ⟶ S k)
    (n a : ℤ) (h : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)) :
    kun l p p n (DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v)) =
      ext2 l p h u v := by
  simp [kun, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]

/- English proof (translation)
Introduce `l _ k _ d X p hb`. Use `⟨fun n => ?_, fun lam m n h => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `w -`. Take `⟨x, rfl⟩` from `(hb n).2 w`.

Proceed by induction on `x using DirectSum.induction_on with`. Consider the case `zero => simp`. Consider the case `of i t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul u v`. Rewrite using `[← DirectSum.lof_eq_of ℚ_[l], kun_lof l p n i (by omega) u v]`. Conclude with `Submodule.subset_span ⟨i, n - i, by omega, u, v, rfl⟩`. Consider the case `add s t hs ht`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ hs ht`. Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Set `e` to `LinearEquiv.ofBijective (kun l p p n) (hb n)`.

Establish `he : ∀ a (ha : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)), e.symm (ext2 l p ha u v) = DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v)`. Introduce `a ha u v`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, kun_lof]`. Use `⟨(DirectSum.toModule ℚ_[l] ℤ (V l X m) (fun i => if hi : i = 2 * (d : ℤ) then TensorProduct.lift ((LinearMap.lsmul ℚ_[l] (V l X m)).compl₁₂ (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] ℚ_[l]) lam hi.symm) (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] V l X m) LinearMap.id (s …` and prove the remaining obligations. Introduce `u v`.

Take `rfl : m = n - 2 * (d : ℤ)` from `by omega`. Simplify using `only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he, DirectSum.toModule_lof, dif_pos rfl]`. Simplify using `[TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply]`. Introduce `a b h' hbm u v`. Take `rfl : b = n - a` from `by omega`.

Establish `ha : a ≠ 2 * (d : ℤ)` using `by omega`. Simplify using `only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he, DirectSum.toModule_lof, dif_neg ha, LinearMap.zero_apply]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.kunL_holds :
    UpperTheory.Gal.KunnethLefschetz.KunL := by
  intro l _ k _ d X p hb
  refine ⟨fun n => ?_, fun lam m n h => ?_⟩
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨x, rfl⟩ := (hb n).2 w
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        rw [← DirectSum.lof_eq_of ℚ_[l], kun_lof l p n i (by omega) u v]
        exact Submodule.subset_span ⟨i, n - i, by omega, u, v, rfl⟩
      | add s t hs ht =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hs ht
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · let e := LinearEquiv.ofBijective (kun l p p n) (hb n)
    have he : ∀ a (ha : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)),
        e.symm (ext2 l p ha u v) = DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v) := by
      intro a ha u v
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, kun_lof]
    refine ⟨(DirectSum.toModule ℚ_[l] ℤ (V l X m) (fun i =>
        if hi : i = 2 * (d : ℤ) then
          TensorProduct.lift ((LinearMap.lsmul ℚ_[l] (V l X m)).compl₁₂
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] ℚ_[l]) lam hi.symm)
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] V l X m) LinearMap.id
              (show m = n - i by omega)))
        else 0)) ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
    · intro u v
      obtain rfl : m = n - 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_pos rfl]
      simp [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply]
    · intro a b h' hbm u v
      obtain rfl : b = n - a := by omega
      have ha : a ≠ 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_neg ha, LinearMap.zero_apply]
