import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Establish `hunit : ∀ y : Submonoid.powers a, IsUnit (Algebra.ofId O (FractionRing O) y)`. Introduce and unpack `⟨_, n, rfl⟩`. Rewrite using `[map_pow]`. Use `IsUnit.pow n (IsUnit.mk0 _ ?_)` and prove the remaining obligations. Rewrite using `[Algebra.ofId_apply]`.

Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)`. Set `f : Localization.Away a →ₐ[O] FractionRing O` to `IsLocalization.liftAlgHom (M := Submonoid.powers a) hunit`. Establish `hinj : Function.Injective f`. Establish `h` using `(IsLocalization.lift_injective_iff (M := Submonoid.powers a) (S := Localization.Away a) (g := algebraMap O (FractionRing O)) hunit).mpr ?_`. Conclude with `h`.

Introduce `x y`. Rewrite using `[(IsLocalization.injective (Localization.Away a) (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff, (IsFractionRing.injective O (FractionRing O)).eq_iff]`. Establish `hcl : IsIntegrallyClosedIn O (Localization.Away a)` using `f.isIntegrallyClosedIn hinj inferInstance`. Conclude with `IsIntegrallyClosedIn.algebraMap_eq_of_integral hx`.
-/
private theorem away_closed (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (a : O) (ha : a ≠ 0)
    (x : Localization.Away a) (hx : IsIntegral O x) : ∃ o : O, algebraMap O _ o = x := by
  classical
  have hunit : ∀ y : Submonoid.powers a, IsUnit (Algebra.ofId O (FractionRing O) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n (IsUnit.mk0 _ ?_)
    rw [Algebra.ofId_apply]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  let f : Localization.Away a →ₐ[O] FractionRing O :=
    IsLocalization.liftAlgHom (M := Submonoid.powers a) hunit
  have hinj : Function.Injective f := by
    have h := (IsLocalization.lift_injective_iff (M := Submonoid.powers a)
      (S := Localization.Away a) (g := algebraMap O (FractionRing O)) hunit).mpr ?_
    · exact h
    · intro x y
      rw [(IsLocalization.injective (Localization.Away a)
          (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
        (IsFractionRing.injective O (FractionRing O)).eq_iff]
  have hcl : IsIntegrallyClosedIn O (Localization.Away a) :=
    f.isIntegrallyClosedIn hinj inferInstance
  exact IsIntegrallyClosedIn.algebraMap_eq_of_integral hx

/- English proof (translation)
Introduce `l O R _ _ _ _ _ _ hl c hc`. Establish `hM : Algebra.algebraMapSubmonoid R (Submonoid.powers (l : O)) = Submonoid.powers (l : R)`. Rewrite using `[Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast]`. Use `haveI : IsLocalization (Submonoid.powers (l : R)) (R ⊗[O] Localization.Away (l : O)) := by`. Rewrite using `[← hM]`.

Use `infer_instance`. Set `e : (R ⊗[O] Localization.Away (l : O)) ≃ₐ[R] Localization.Away (l : R)` to `IsLocalization.algEquiv (Submonoid.powers (l : R)) _ _`. Establish `hc' : IsIntegral R (e.symm c)` using `hc.map e.symm`. Take `⟨s, hs⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := O) (S := R) (B := Localization.Away (l : O))).2 ⟨e.symm c, hc'⟩`. Establish `key : ∀ s : R ⊗[O] integralClosure O (Localization.Away (l : O)), ∃ r : R, algebraMap R (R ⊗[O] Localization.Away (l : O)) r = (TensorProduct.toIntegralClosure O R (Localization.Away (l : O)) s : R ⊗[O] Localization.Away (l : O))`.

Introduce `s`. Proceed by induction on `s with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul r y`. Take `⟨o, ho⟩` from `away_closed O (l : O) hl y.1 y.2`.

Use `⟨algebraMap O R o * r, ?_⟩` and prove the remaining obligations. Use `show _ = r ⊗ₜ[O] y.1`. Rewrite using `[← ho, Algebra.algebraMap_eq_smul_one (A := Localization.Away (l : O)), ← TensorProduct.smul_tmul, Algebra.smul_def]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`.

Take `⟨r1, h1⟩` from `hx`. Take `⟨r2, h2⟩` from `hy`. Conclude with `⟨r1 + r2, by simp only [map_add, h1, h2]; rfl⟩`. Take `⟨r, hr⟩` from `key s`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e.commutes r, hr, hs]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.crystallineComparison.smoothClosed_of :
    SmoothClosed := by
  intro l O R _ _ _ _ _ _ hl c hc
  classical
  have hM : Algebra.algebraMapSubmonoid R (Submonoid.powers (l : O)) = Submonoid.powers (l : R) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast]
  haveI : IsLocalization (Submonoid.powers (l : R)) (R ⊗[O] Localization.Away (l : O)) := by
    rw [← hM]
    infer_instance
  let e : (R ⊗[O] Localization.Away (l : O)) ≃ₐ[R] Localization.Away (l : R) :=
    IsLocalization.algEquiv (Submonoid.powers (l : R)) _ _
  have hc' : IsIntegral R (e.symm c) := hc.map e.symm
  obtain ⟨s, hs⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := O) (S := R)
    (B := Localization.Away (l : O))).2 ⟨e.symm c, hc'⟩
  have key : ∀ s : R ⊗[O] integralClosure O (Localization.Away (l : O)), ∃ r : R,
      algebraMap R (R ⊗[O] Localization.Away (l : O)) r =
        (TensorProduct.toIntegralClosure O R (Localization.Away (l : O)) s :
          R ⊗[O] Localization.Away (l : O)) := by
    intro s
    induction s with
    | zero => exact ⟨0, by simp⟩
    | tmul r y =>
      obtain ⟨o, ho⟩ := away_closed O (l : O) hl y.1 y.2
      refine ⟨algebraMap O R o * r, ?_⟩
      show _ = r ⊗ₜ[O] y.1
      rw [← ho, Algebra.algebraMap_eq_smul_one (A := Localization.Away (l : O)), ← TensorProduct.smul_tmul,
        Algebra.smul_def]
      rfl
    | add x y hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      exact ⟨r1 + r2, by simp only [map_add, h1, h2]; rfl⟩
  obtain ⟨r, hr⟩ := key s
  refine ⟨r, ?_⟩
  rw [← e.commutes r, hr, hs]
  simp
