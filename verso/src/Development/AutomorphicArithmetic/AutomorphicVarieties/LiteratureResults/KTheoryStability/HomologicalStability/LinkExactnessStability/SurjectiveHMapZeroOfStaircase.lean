import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStaircaseStepSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Staircase

/- English proof (translation)
Introduce `k G _ _ i C d hd hd0 hexC hexH`. Establish `ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0), Function.Exact u.hom v.hom → (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv) (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact`. Introduce `W X Y u v huv hex`. Establish `hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact` using `ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)`. Set `φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv) (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶ ShortComplex.mk (kernel.ι u) u (kernel.condition u)` to `{ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }`.

Establish `hinj : Function.Injective (kernel.ι v).hom` using `(Rep.mono_iff_injective _).mp inferInstance`. Use `{ exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS', mono_f := inferInstance, epi_g := ?_ }` and prove the remaining obligations. Rewrite using `[Rep.epi_iff_surjective]`. Introduce `z`. Establish `hz : v.hom ((kernel.ι v).hom z) = 0`.

Establish `h` using `congrArg (fun f => f.hom z) (kernel.condition v)`. Simplify using `using h`. Take `⟨y, hy⟩` from `(hex _).mp hz`. Use `⟨y, hinj ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)`.

Conclude with `h.trans hy`. Establish `epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom → Function.Surjective (hMap f 0).hom`. Introduce `X Y f hf`. Use `haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf`. Conclude with `(ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)`.

Establish `liftSurj : ∀ p, p + 1 ≤ i → Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom`. Introduce `p hp`. Conclude with `(Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g`. Establish `R : ∀ q p, p + 1 + q = i → Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom`. Introduce `q`.

Proceed by induction on `q with`. Consider the case `zero`. Introduce `p hp`. Conclude with `epi0 _ _ _ (liftSurj p (by omega))`. Consider the case `succ q ih`.

Introduce `p hp`. Establish `hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0`. Rewrite using `[← cancel_mono (kernel.ι (d (p + 1)))]`. Simplify using `[hd]`. Establish `hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) = d (p + 2)` using `kernel.lift_ι _ _ _`.

Establish `hE : Function.Exact (hMap (d (p + 3)) q).hom (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom`. Rewrite using `[hbι]`. Conclude with `hexH (p + 2) q (by omega) (by omega)`. Conclude with `homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p)) (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1))) (kernel.lift (d p) (d (p + 1)) (hd p)) _ (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q ( …`. Consider the cases of `i with`.

Consider the case `zero => exact epi0 _ _ _ hd0`. Consider the case `succ q`. Establish `ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0)) mono_f := inferInstance epi_g := (Rep.epi_iff_surjective _).mpr hd0 }`. Establish `hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0`. Rewrite using `[← cancel_mono (kernel.ι (d 0))]`.

Simplify using `[hd]`. Establish `hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1` using `kernel.lift_ι _ _ _`. Establish `hE : Function.Exact (hMap (d 2) q).hom (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom`. Rewrite using `[hbι]`. Conclude with `hexH 1 q (by omega) (by omega)`.

Conclude with `homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2) (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE`.
-/
theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hd0 hexC hexH
  have ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0),
      Function.Exact u.hom v.hom →
      (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact := by
    intro W X Y u v huv hex
    have hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)
    let φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶
        ShortComplex.mk (kernel.ι u) u (kernel.condition u) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }
    have hinj : Function.Injective (kernel.ι v).hom := (Rep.mono_iff_injective _).mp inferInstance
    refine { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS',
             mono_f := inferInstance, epi_g := ?_ }
    rw [Rep.epi_iff_surjective]
    intro z
    have hz : v.hom ((kernel.ι v).hom z) = 0 := by
      have h := congrArg (fun f => f.hom z) (kernel.condition v)
      simpa using h
    obtain ⟨y, hy⟩ := (hex _).mp hz
    refine ⟨y, hinj ?_⟩
    have h := congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)
    exact h.trans hy
  have epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom →
      Function.Surjective (hMap f 0).hom := by
    intro X Y f hf
    haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf
    exact (ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)
  have liftSurj : ∀ p, p + 1 ≤ i →
      Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom := by
    intro p hp
    exact (Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g
  have R : ∀ q p, p + 1 + q = i →
      Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom := by
    intro q
    induction q with
    | zero =>
      intro p hp
      exact epi0 _ _ _ (liftSurj p (by omega))
    | succ q ih =>
      intro p hp
      have hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0 := by
        rw [← cancel_mono (kernel.ι (d (p + 1)))]
        simp [hd]
      have hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) =
          d (p + 2) := kernel.lift_ι _ _ _
      have hE : Function.Exact (hMap (d (p + 3)) q).hom
          (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom := by
        rw [hbι]
        exact hexH (p + 2) q (by omega) (by omega)
      exact homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p))
        (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1)))
        (kernel.lift (d p) (d (p + 1)) (hd p)) _
        (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q (ih (p + 1) (by omega)) hE
  cases i with
  | zero => exact epi0 _ _ _ hd0
  | succ q =>
    have ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0))
        mono_f := inferInstance
        epi_g := (Rep.epi_iff_surjective _).mpr hd0 }
    have hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0 := by
      rw [← cancel_mono (kernel.ι (d 0))]
      simp [hd]
    have hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1 := kernel.lift_ι _ _ _
    have hE : Function.Exact (hMap (d 2) q).hom
        (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom := by
      rw [hbι]
      exact hexH 1 q (by omega) (by omega)
    exact homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2)
      (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE

end GlobalTheory.HomStab.Staircase

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.Staircase.main`.
-/
theorem _root_.GlobalTheory.T.surjective_hMap_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.Staircase.main
end
