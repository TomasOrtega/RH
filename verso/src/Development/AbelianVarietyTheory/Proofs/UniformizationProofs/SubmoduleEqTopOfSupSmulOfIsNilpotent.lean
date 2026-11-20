import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

/- English proof (translation)
Establish `key : ∀ n : ℕ, ⊤ ≤ N ⊔ J ^ n • (⊤ : Submodule A B)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, one_smul]`. Conclude with `le_sup_right`.

Consider the case `succ n ih`. Use `ih.trans (sup_le le_sup_left ((Submodule.smul_mono le_rfl h).trans ?_))` and prove the remaining obligations. Rewrite using `[Submodule.smul_sup, pow_succ, Submodule.mul_smul]`. Conclude with `sup_le_sup_right Submodule.smul_le_right _`. Take `⟨n, hn⟩` from `hJ`.

Use `key n` as an intermediate fact. Rewrite `this` using `[hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq]`. Conclude with `top_unique this`.
-/
theorem submodule_eq_top_of_sup_smul_of_isNilpotent {A B : Type} [CommRing A] [AddCommGroup B] [Module A B]
    {J : Ideal A} (hJ : IsNilpotent J) {N : Submodule A B} (h : ⊤ ≤ N ⊔ J • ⊤) : N = ⊤ := by
  have key : ∀ n : ℕ, ⊤ ≤ N ⊔ J ^ n • (⊤ : Submodule A B) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact le_sup_right
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ((Submodule.smul_mono le_rfl h).trans ?_))
      rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
      exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨n, hn⟩ := hJ
  have := key n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_unique this

/- English proof (translation)
Use `letI : Algebra A B := α.hom.toAlgebra`. Establish `hN : Subalgebra.toSubmodule (MvPolynomial.aeval (R` using `A) r).range = ⊤ := by`. Use `submodule_eq_top_of_sup_smul_of_isNilpotent hJ fun b _ => ?_` and prove the remaining obligations. Take `⟨p, hp⟩` from `hr (c'.hom b)`. Take `⟨q, rfl⟩` from `MvPolynomial.map_surjective β.hom hβ p`.

Establish `e : c'.hom (MvPolynomial.eval₂Hom α.hom r q) = c'.hom b`. Rewrite using `[← hp, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]`. Conclude with `congrArg (fun c => MvPolynomial.eval₂Hom c _ q) (congrArg CommRingCat.Hom.hom h.w)`. Establish `hk : b - MvPolynomial.eval₂Hom α.hom r q ∈ RingHom.ker c'.hom`. Rewrite using `[RingHom.mem_ker, map_sub, e, sub_self]`.

Rewrite `hk` using `[PrimeSection.ker_eq_map_of_isPushout h hβ]`. Use `Submodule.mem_sup.2 ⟨MvPolynomial.eval₂Hom α.hom r q, ⟨q, rfl⟩, _, ?_, add_sub_cancel _ _⟩` and prove the remaining obligations. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hk`. Introduce `b`.

Conclude with `(hN.ge (Submodule.mem_top : b ∈ ⊤) :)`.
-/
theorem surjective_eval₂Hom_of_isPushout {A B C P : CommRingCat.{0}} {α : A ⟶ B} {β : A ⟶ C} {c' : B ⟶ P}
    {d' : C ⟶ P} (h : IsPushout α β c' d') (hβ : Function.Surjective β) (hJ : IsNilpotent (RingHom.ker β.hom))
    {σ : Type} (r : σ → B) (hr : Function.Surjective (MvPolynomial.eval₂Hom d'.hom fun j => c'.hom (r j))) :
    Function.Surjective (MvPolynomial.eval₂Hom α.hom r) := by
  letI : Algebra A B := α.hom.toAlgebra
  have hN : Subalgebra.toSubmodule (MvPolynomial.aeval (R := A) r).range = ⊤ := by
    refine submodule_eq_top_of_sup_smul_of_isNilpotent hJ fun b _ => ?_
    obtain ⟨p, hp⟩ := hr (c'.hom b)
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective β.hom hβ p
    have e : c'.hom (MvPolynomial.eval₂Hom α.hom r q) = c'.hom b := by
      rw [← hp, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun c => MvPolynomial.eval₂Hom c _ q) (congrArg CommRingCat.Hom.hom h.w)
    have hk : b - MvPolynomial.eval₂Hom α.hom r q ∈ RingHom.ker c'.hom := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    rw [PrimeSection.ker_eq_map_of_isPushout h hβ] at hk
    refine Submodule.mem_sup.2 ⟨MvPolynomial.eval₂Hom α.hom r q, ⟨q, rfl⟩, _, ?_, add_sub_cancel _ _⟩
    rw [Ideal.smul_top_eq_map]
    exact hk
  intro b
  exact (hN.ge (Submodule.mem_top : b ∈ ⊤) :)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => by obtain ⟨n, hn⟩ := hJ have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g : Set R) := fun a ha => x.isPrime.mem_of_pow_mem n (by have := Ideal.pow_mem_pow ha n rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this rw [this] exact zero_mem _) rw [← range_comap_of_surjecti …`.
-/
theorem surjective_specMap_of_isNilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (g : R →+* R₀)
    (hg : Function.Surjective g) (hJ : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun x => by
  obtain ⟨n, hn⟩ := hJ
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g : Set R) := fun a ha =>
    x.isPrime.mem_of_pow_mem n (by
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _)
  rw [← range_comap_of_surjective _ g hg] at hx
  exact hx⟩

/- English proof (translation)
Introduce `R R₀ _ _ g hg hJ X X₀ f f₀ j₀ h H H₀ w n s s₀ hH hH₀ _ hs ⟨hcov, hva⟩`. Establish `hsurj : Surjective j₀` using `MorphismProperty.of_isPullback h.flip (surjective_specMap_of_isNilpotent g hg hJ)`. Establish `loc : ∀ i, nonzeroLocus (s₀ i) = j₀ ⁻¹ᵁ nonzeroLocus (s i)` using `fun i => by`. Use extensionality with `y`. Use `(mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (j₀ y)).symm)` and prove the remaining obligations.

Take `⟨j, hj⟩` from `exists_chart hH (j₀ y)`. Establish `e` using `hs i y j k hj hk`. Rewrite `e` using `[gs_stalkMap j₀ y _ hj]`. Conclude with `⟨j, hj, (isUnit_map_iff (j₀.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩`. Take `⟨k, hk⟩` from `exists_chart hH₀ y`.

Establish `e` using `hs i y j k hj hk`. Conclude with `⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap j₀ y _ hj _).symm.trans e)).mp (u.map _))⟩`. Use `⟨top_le_iff.1 fun x _ => ?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `j₀.surjective x`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (loc i).le hi⟩`. Take `⟨haff₀, r₀, hr₀, hs₀⟩` from `hva i`. Establish `haff : IsAffineOpen (nonzeroLocus (s i))` using `AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hJ (CommRingCat.ofHom g) hg rfl ((isPullback_morphismRestrict j₀ (nonzeroLocus (s i))).paste_vert h) (loc i ▸ haff₀ :)`. Establish `hr` using `fun j => ProjSpace.secRatio_spec (s i) (s j)`. Use `⟨haff, fun j => ProjSpace.secRatio (s i) (s j), hr, ?_⟩` and prove the remaining obligations.

Establish `e₀ : r₀ = fun j => (j₀.appLE _ _ (loc i).le).hom (ProjSpace.secRatio (s i) (s j))` using `funext fun j => by`. Use `(ProjSpace.eq_secRatio _ _ (hr₀ j)).trans (ProjSpace.eq_secRatio _ _ fun k => fn_ext fun y hy => ?_).symm` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_chart hH (j₀ y)`. Establish `hm : j₀ y ∈ nonzeroLocus (s i) ⊓ H.U l` using `⟨(loc i).le hy.1, hl⟩`. Establish `e` using `congrArg (gs j₀ y _) (hr j l)`.

Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`. Establish `e₁` using `hs j y l k hl hy.2`. Establish `e₂` using `hs i y l k hl hy.2`. Establish `e₃` using `(Geo.Tor.gw w (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))`. Conclude with `(gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE j₀ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))`.

Substitute `e₀` using the available equality. Establish `po` using `(isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top (UY := nonzeroLocus (s₀ i)) (by rw [loc]; simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)`. Establish `po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (nonzeroLocus (s i)) le_top) (CommRingCat.ofHom g) (j₀.appLE _ _ (loc i).le) ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f₀.appLE ⊤ (nonzeroLocus (s₀ i)) le_top)`. Use `po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)` and prove the remaining obligations. Rewrite using `[← Scheme.ΓSpecIso_naturality]`.

Use `congr 1`. Conclude with `surjective_eval₂Hom_of_isPushout po' hg hJ _ hs₀`.
-/
theorem veryAmpleBy_of_isNilpotent : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (g : R →+* R₀), Function.Surjective g → IsNilpotent (RingHom.ker g) → ∀ (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (j₀ : X₀ ⟶ X), IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g)) → ∀ (H : LB X) (H₀ : LB X₀) (w : LB.Iso H₀ (H.pull j₀)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s₀ : Fin (n + 1) → LB.Sec H₀), H.IsLB → H₀.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (j₀) z ∈ (H).U k → z ∈ (H₀).U k' → gs (j₀) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → VeryAmpleBy f₀ H₀ s₀ → VeryAmpleBy f H s := by
  intro R R₀ _ _ g hg hJ X X₀ f f₀ j₀ h H H₀ w n s s₀ hH hH₀ _ hs ⟨hcov, hva⟩
  have hsurj : Surjective j₀ :=
    MorphismProperty.of_isPullback h.flip (surjective_specMap_of_isNilpotent g hg hJ)
  have loc : ∀ i, nonzeroLocus (s₀ i) = j₀ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (j₀ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hH (j₀ y)
      have e := hs i y j k hj hk
      rw [gs_stalkMap j₀ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (j₀.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hH₀ y
      have e := hs i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap j₀ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨top_le_iff.1 fun x _ => ?_, fun i => ?_⟩
  · obtain ⟨y, rfl⟩ := j₀.surjective x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (loc i).le hi⟩
  obtain ⟨haff₀, r₀, hr₀, hs₀⟩ := hva i
  have haff : IsAffineOpen (nonzeroLocus (s i)) :=
    AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hJ (CommRingCat.ofHom g) hg rfl
      ((isPullback_morphismRestrict j₀ (nonzeroLocus (s i))).paste_vert h) (loc i ▸ haff₀ :)
  have hr := fun j => ProjSpace.secRatio_spec (s i) (s j)
  refine ⟨haff, fun j => ProjSpace.secRatio (s i) (s j), hr, ?_⟩
  have e₀ : r₀ = fun j => (j₀.appLE _ _ (loc i).le).hom (ProjSpace.secRatio (s i) (s j)) := funext fun j => by
    refine (ProjSpace.eq_secRatio _ _ (hr₀ j)).trans (ProjSpace.eq_secRatio _ _ fun k => fn_ext fun y hy => ?_).symm
    obtain ⟨l, hl⟩ := exists_chart hH (j₀ y)
    have hm : j₀ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs j₀ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs j y l k hl hy.2
    have e₂ := hs i y l k hl hy.2
    have e₃ := (Geo.Tor.gw w (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    exact (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE j₀ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  subst e₀
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
    (UY := nonzeroLocus (s₀ i)) (by rw [loc]; simp)).1
    (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (nonzeroLocus (s i)) le_top)
      (CommRingCat.ofHom g) (j₀.appLE _ _ (loc i).le)
      ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f₀.appLE ⊤ (nonzeroLocus (s₀ i)) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact surjective_eval₂Hom_of_isPushout po' hg hJ _ hs₀

end GlobalTheory.AbLaw
