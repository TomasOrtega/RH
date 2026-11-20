import Mathlib

namespace GlobalTheory.CompanionTheory.Semistable

open MvPolynomial

/- English proof (translation)
Set `P` to `MvPolynomial σ O`. Set `I : Ideal P` to `Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}`. Set `A` to `P ⧸ I`. Set `a : A` to `algebraMap O A ϖ`. Set `B` to `Localization.Away a`.

Set `C` to `MvPolynomial {j : σ // j ≠ i0} O`. Set `y : σ → C` to `fun i => if hi : i = i0 then 0 else MvPolynomial.X ⟨i, hi⟩`. Set `g : C` to `∏ i ∈ T.erase i0, y i`. Set `h : C` to `MvPolynomial.C ϖ * g`. Set `C'` to `Localization.Away h`.

Set `u : C'` to `IsLocalization.Away.invSelf h`. Establish `hu : algebraMap C C' h * u = 1` using `IsLocalization.Away.mul_invSelf h`. Establish `hh : IsUnit (algebraMap C C' h)` using `IsLocalization.Away.algebraMap_isUnit h`. Establish `e1 : algebraMap C C' h = algebraMap O C' ϖ * algebraMap C C' g`. Rewrite using `[IsScalarTower.algebraMap_apply O C C' ϖ, MvPolynomial.algebraMap_eq, ← map_mul]`.

Establish `hϖ' : IsUnit (algebraMap O C' ϖ)`. Rewrite `hh` using `[e1]`. Conclude with `isUnit_of_mul_isUnit_left hh`. Set `z : σ → C'` to `fun i => if i = i0 then algebraMap O C' ϖ ^ 2 * u else algebraMap C C' (y i)`. Establish `hzg : ∏ i ∈ T.erase i0, z i = algebraMap C C' g`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Simplify using `only [z, if_neg (Finset.ne_of_mem_erase hi)]`. Establish `hz : ∏ i ∈ T, z i = algebraMap O C' ϖ`. Rewrite using `[← Finset.mul_prod_erase T z hi0, hzg]`.

Simplify using `only [z, if_pos rfl]`. Take the linear combination `(algebraMap O C' ϖ) * hu - (algebraMap O C' ϖ * u) * e1`. Set `ψP : P →ₐ[O] C'` to `MvPolynomial.aeval z`. Establish `hψP : ∀ x ∈ I, ψP x = 0`. Introduce `x hx`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Establish `h3 : ∀ i, ψP (MvPolynomial.X i) = z i` using `fun i => MvPolynomial.aeval_X z i`. Establish `h4 : ψP (MvPolynomial.C ϖ) = algebraMap O C' ϖ` using `MvPolynomial.aeval_C z ϖ`. Establish `h5 : ψP ((∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ) = 0`. Rewrite using `[map_sub, map_prod, h4]`.

Simplify using `only [h3, hz, sub_self]`. Rewrite using `[map_mul, h5, mul_zero]`. Set `ψA : A →ₐ[O] C'` to `Ideal.Quotient.liftₐ I ψP hψP`. Establish `hψA : ∀ p : P, ψA (Ideal.Quotient.mk I p) = ψP p` using `fun p => rfl`. Establish `hunit1 : ∀ yy : Submonoid.powers a, IsUnit (ψA yy)`.

Introduce and unpack `⟨_, n, rfl⟩`. Use `show IsUnit (ψA (algebraMap O A ϖ ^ n))`. Rewrite using `[map_pow, AlgHom.commutes]`. Conclude with `hϖ'.pow n`. Set `ψ : B →ₐ[O] C'` to `IsLocalization.liftAlgHom (M := Submonoid.powers a) (S := B) (f := ψA) hunit1`.

Establish `hψ : ∀ x : A, ψ (algebraMap A B x) = ψA x` using `fun x => by first`. Consider the case `exact IsLocalization.lift_eq (M := Submonoid.powers a) (S := B) _ x`. Consider the case `simp [ψ, IsLocalization.liftAlgHom]`. Set `xB : σ → B` to `fun i => algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))`. Establish `hxB : ∏ i ∈ T, xB i = algebraMap O B ϖ`.

Establish `e : (Ideal.Quotient.mk I (∏ i ∈ T, MvPolynomial.X i)) = Ideal.Quotient.mk I (MvPolynomial.C ϖ)` using `Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)`. Simplify using `only [xB]`. Rewrite using `[← map_prod, ← map_prod, e, IsScalarTower.algebraMap_apply O A B]`. Both sides reduce to the same expression. Establish `hϖB : IsUnit (algebraMap O B ϖ)`.

Rewrite using `[IsScalarTower.algebraMap_apply O A B]`. Conclude with `IsLocalization.Away.algebraMap_isUnit a`. Establish `hxB' : xB i0 * ∏ i ∈ T.erase i0, xB i = algebraMap O B ϖ`. Rewrite using `[Finset.mul_prod_erase T xB hi0, hxB]`. Establish `hpB : IsUnit (∏ i ∈ T.erase i0, xB i)`.

Rewrite `hϖB` using `[← hxB']`. Conclude with `isUnit_of_mul_isUnit_right hϖB`. Set `χC : C →ₐ[O] B` to `MvPolynomial.aeval (fun j => xB j.1)`. Establish `hχX : ∀ j : {j : σ // j ≠ i0}, χC (MvPolynomial.X j) = xB j.1` using `fun j => MvPolynomial.aeval_X (fun j : {j : σ // j ≠ i0} => xB j.1) j`. Establish `hχy : ∀ i ∈ T.erase i0, χC (y i) = xB i`.

Introduce `i hi`. Establish `hne : i ≠ i0` using `Finset.ne_of_mem_erase hi`. Establish `hyi : y i = MvPolynomial.X ⟨i, hne⟩` using `dif_neg hne`. Rewrite using `[hyi, hχX ⟨i, hne⟩]`. Establish `hχh : χC h = algebraMap O B ϖ * ∏ i ∈ T.erase i0, xB i` using `by show χC (MvPolynomial.C ϖ * ∏ i ∈ T.erase i0, y i) = _`.

Rewrite using `[map_mul, map_prod]`. Establish `hC : χC (MvPolynomial.C ϖ) = algebraMap O B ϖ` using `MvPolynomial.aeval_C _ ϖ`. Rewrite using `[hC, Finset.prod_congr rfl hχy]`. Establish `hunit2 : ∀ yy : Submonoid.powers h, IsUnit (χC yy)`. Introduce and unpack `⟨_, n, rfl⟩`.

Use `show IsUnit (χC (h ^ n))`. Rewrite using `[map_pow, hχh]`. Conclude with `(hϖB.mul hpB).pow n`. Set `χ : C' →ₐ[O] B` to `IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := C') (f := χC) hunit2`. Establish `hχ : ∀ x : C, χ (algebraMap C C' x) = χC x` using `fun x => by first`.

Consider the case `exact IsLocalization.lift_eq (M := Submonoid.powers h) (S := C') _ x`. Consider the case `simp [χ, IsLocalization.liftAlgHom]`. Establish `hχu : χ (algebraMap C C' h) * χ u = 1` using `by rw [← map_mul, hu, map_one]`. Rewrite `hχu` using `[hχ, hχh]`. Establish `h1 : χ.comp ψ = AlgHom.id O B`.

Apply `IsLocalization.algHom_ext (Submonoid.powers a)` to reduce the goal to its premises. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use `show χ (ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) = algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))`.

Rewrite using `[hψ, hψA]`. Establish `hXi : ψP (MvPolynomial.X i) = z i` using `MvPolynomial.aeval_X z i`. Rewrite using `[hXi]`. Use `show χ (z i) = xB i`. Distinguish the cases in `hi : i = i0`.

Rewrite using `[hi]`. Establish `hz0 : z i0 = algebraMap O C' ϖ ^ 2 * u` using `if_pos rfl`. Rewrite using `[hz0, map_mul, map_pow, AlgHom.commutes]`. Take the linear combination `(χ u * algebraMap O B ϖ) * hxB'.symm + xB i0 * hχu`. Establish `hzi : z i = algebraMap C C' (y i)` using `if_neg hi`.

Establish `hyi : y i = MvPolynomial.X ⟨i, hi⟩` using `dif_neg hi`. Rewrite using `[hzi, hχ, hyi, hχX ⟨i, hi⟩]`. Establish `h2 : ψ.comp χ = AlgHom.id O C'`. Apply `IsLocalization.algHom_ext (Submonoid.powers h)` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `j`. Use `show ψ (χ (algebraMap C C' (MvPolynomial.X j))) = algebraMap C C' (MvPolynomial.X j)`. Rewrite using `[hχ]`. Rewrite using `[hχX j]`. Use `show ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X j.1))) = _`.

Rewrite using `[hψ, hψA]`. Establish `hXi : ψP (MvPolynomial.X j.1) = z j.1` using `MvPolynomial.aeval_X z j.1`. Establish `hzi : z j.1 = algebraMap C C' (y j.1)` using `if_neg j.2`. Establish `hyi : y j.1 = MvPolynomial.X ⟨j.1, j.2⟩` using `dif_neg j.2`. Rewrite using `[hXi, hzi, hyi]`.

Set `e : C' ≃ₐ[O] B` to `AlgEquiv.ofAlgHom χ ψ h1 h2`. Use `haveI : Algebra.FormallySmooth C C' := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers h)`. Use `haveI : Algebra.FormallySmooth O C' := Algebra.FormallySmooth.comp O C C'`. Use `haveI : Algebra.FormallySmooth O B := Algebra.FormallySmooth.of_equiv e`. Use `haveI : Algebra.FinitePresentation O A := Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)`.

Use `haveI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation a`. Use `haveI : Algebra.FinitePresentation O B := Algebra.FinitePresentation.trans O A B`. Use `haveI : Algebra.FinitePresentation O F := IsLocalization.Away.finitePresentation ϖ`. Set `φ` to `IsLocalization.Away.map F B (algebraMap O A) ϖ`. Use `letI : Algebra F B := φ.toAlgebra`.

Use `haveI : IsScalarTower O F B := IsScalarTower.of_algebraMap_eq (fun x => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply O A B]`. Conclude with `(IsLocalization.map_eq _ _).symm)`. Use `haveI : Algebra.FormallySmooth F B := Algebra.FormallySmooth.localization_base (Submonoid.powers ϖ)`. Use `haveI : Algebra.FinitePresentation F B := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O F B`.

Establish `hs : Algebra.Smooth F B` using `⟨inferInstance, inferInstance⟩`. Conclude with `hs`.
-/
theorem smooth_away_core (O : Type) [CommRing O] (ϖ : O) (σ : Type) [Finite σ] [DecidableEq σ]
    (T : Finset σ) (i0 : σ) (hi0 : i0 ∈ T) (F : Type) [Field F] [Algebra O F]
    [IsLocalization.Away ϖ F] :
    (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ))
      (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  classical
  let P := MvPolynomial σ O
  let I : Ideal P := Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}
  let A := P ⧸ I
  let a : A := algebraMap O A ϖ
  let B := Localization.Away a
  let C := MvPolynomial {j : σ // j ≠ i0} O
  let y : σ → C := fun i => if hi : i = i0 then 0 else MvPolynomial.X ⟨i, hi⟩
  let g : C := ∏ i ∈ T.erase i0, y i
  let h : C := MvPolynomial.C ϖ * g
  let C' := Localization.Away h
  let u : C' := IsLocalization.Away.invSelf h
  have hu : algebraMap C C' h * u = 1 := IsLocalization.Away.mul_invSelf h
  have hh : IsUnit (algebraMap C C' h) := IsLocalization.Away.algebraMap_isUnit h
  have e1 : algebraMap C C' h = algebraMap O C' ϖ * algebraMap C C' g := by
    rw [IsScalarTower.algebraMap_apply O C C' ϖ, MvPolynomial.algebraMap_eq, ← map_mul]
  have hϖ' : IsUnit (algebraMap O C' ϖ) := by
    rw [e1] at hh
    exact isUnit_of_mul_isUnit_left hh
  let z : σ → C' := fun i => if i = i0 then algebraMap O C' ϖ ^ 2 * u else algebraMap C C' (y i)
  have hzg : ∏ i ∈ T.erase i0, z i = algebraMap C C' g := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [z, if_neg (Finset.ne_of_mem_erase hi)]
  have hz : ∏ i ∈ T, z i = algebraMap O C' ϖ := by
    rw [← Finset.mul_prod_erase T z hi0, hzg]
    simp only [z, if_pos rfl]
    linear_combination (algebraMap O C' ϖ) * hu - (algebraMap O C' ϖ * u) * e1
  let ψP : P →ₐ[O] C' := MvPolynomial.aeval z
  have hψP : ∀ x ∈ I, ψP x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have h3 : ∀ i, ψP (MvPolynomial.X i) = z i := fun i => MvPolynomial.aeval_X z i
    have h4 : ψP (MvPolynomial.C ϖ) = algebraMap O C' ϖ := MvPolynomial.aeval_C z ϖ
    have h5 : ψP ((∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ) = 0 := by
      rw [map_sub, map_prod, h4]
      simp only [h3, hz, sub_self]
    rw [map_mul, h5, mul_zero]
  let ψA : A →ₐ[O] C' := Ideal.Quotient.liftₐ I ψP hψP
  have hψA : ∀ p : P, ψA (Ideal.Quotient.mk I p) = ψP p := fun p => rfl
  have hunit1 : ∀ yy : Submonoid.powers a, IsUnit (ψA yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (ψA (algebraMap O A ϖ ^ n))
    rw [map_pow, AlgHom.commutes]
    exact hϖ'.pow n
  let ψ : B →ₐ[O] C' := IsLocalization.liftAlgHom (M := Submonoid.powers a) (S := B) (f := ψA) hunit1
  have hψ : ∀ x : A, ψ (algebraMap A B x) = ψA x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers a) (S := B) _ x
    | simp [ψ, IsLocalization.liftAlgHom]
  let xB : σ → B := fun i => algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
  have hxB : ∏ i ∈ T, xB i = algebraMap O B ϖ := by
    have e : (Ideal.Quotient.mk I (∏ i ∈ T, MvPolynomial.X i)) =
        Ideal.Quotient.mk I (MvPolynomial.C ϖ) :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
    simp only [xB]
    rw [← map_prod, ← map_prod, e, IsScalarTower.algebraMap_apply O A B]
    rfl
  have hϖB : IsUnit (algebraMap O B ϖ) := by
    rw [IsScalarTower.algebraMap_apply O A B]
    exact IsLocalization.Away.algebraMap_isUnit a
  have hxB' : xB i0 * ∏ i ∈ T.erase i0, xB i = algebraMap O B ϖ := by
    rw [Finset.mul_prod_erase T xB hi0, hxB]
  have hpB : IsUnit (∏ i ∈ T.erase i0, xB i) := by
    rw [← hxB'] at hϖB
    exact isUnit_of_mul_isUnit_right hϖB
  let χC : C →ₐ[O] B := MvPolynomial.aeval (fun j => xB j.1)
  have hχX : ∀ j : {j : σ // j ≠ i0}, χC (MvPolynomial.X j) = xB j.1 := fun j =>
    MvPolynomial.aeval_X (fun j : {j : σ // j ≠ i0} => xB j.1) j
  have hχy : ∀ i ∈ T.erase i0, χC (y i) = xB i := by
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    have hyi : y i = MvPolynomial.X ⟨i, hne⟩ := dif_neg hne
    rw [hyi, hχX ⟨i, hne⟩]
  have hχh : χC h = algebraMap O B ϖ * ∏ i ∈ T.erase i0, xB i := by
    show χC (MvPolynomial.C ϖ * ∏ i ∈ T.erase i0, y i) = _
    rw [map_mul, map_prod]
    have hC : χC (MvPolynomial.C ϖ) = algebraMap O B ϖ := MvPolynomial.aeval_C _ ϖ
    rw [hC, Finset.prod_congr rfl hχy]
  have hunit2 : ∀ yy : Submonoid.powers h, IsUnit (χC yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (χC (h ^ n))
    rw [map_pow, hχh]
    exact (hϖB.mul hpB).pow n
  let χ : C' →ₐ[O] B := IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := C') (f := χC) hunit2
  have hχ : ∀ x : C, χ (algebraMap C C' x) = χC x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers h) (S := C') _ x
    | simp [χ, IsLocalization.liftAlgHom]
  have hχu : χ (algebraMap C C' h) * χ u = 1 := by rw [← map_mul, hu, map_one]
  rw [hχ, hχh] at hχu
  have h1 : χ.comp ψ = AlgHom.id O B := by
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show χ (ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) =
      algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X i) = z i := MvPolynomial.aeval_X z i
    rw [hXi]
    show χ (z i) = xB i
    by_cases hi : i = i0
    · rw [hi]
      have hz0 : z i0 = algebraMap O C' ϖ ^ 2 * u := if_pos rfl
      rw [hz0, map_mul, map_pow, AlgHom.commutes]
      linear_combination (χ u * algebraMap O B ϖ) * hxB'.symm + xB i0 * hχu
    · have hzi : z i = algebraMap C C' (y i) := if_neg hi
      have hyi : y i = MvPolynomial.X ⟨i, hi⟩ := dif_neg hi
      rw [hzi, hχ, hyi, hχX ⟨i, hi⟩]
  have h2 : ψ.comp χ = AlgHom.id O C' := by
    apply IsLocalization.algHom_ext (Submonoid.powers h)
    apply MvPolynomial.algHom_ext
    intro j
    show ψ (χ (algebraMap C C' (MvPolynomial.X j))) = algebraMap C C' (MvPolynomial.X j)
    rw [hχ]
    rw [hχX j]
    show ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X j.1))) = _
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X j.1) = z j.1 := MvPolynomial.aeval_X z j.1
    have hzi : z j.1 = algebraMap C C' (y j.1) := if_neg j.2
    have hyi : y j.1 = MvPolynomial.X ⟨j.1, j.2⟩ := dif_neg j.2
    rw [hXi, hzi, hyi]
  let e : C' ≃ₐ[O] B := AlgEquiv.ofAlgHom χ ψ h1 h2
  haveI : Algebra.FormallySmooth C C' := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers h)
  haveI : Algebra.FormallySmooth O C' := Algebra.FormallySmooth.comp O C C'
  haveI : Algebra.FormallySmooth O B := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.FinitePresentation O A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  haveI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation a
  haveI : Algebra.FinitePresentation O B := Algebra.FinitePresentation.trans O A B
  haveI : Algebra.FinitePresentation O F := IsLocalization.Away.finitePresentation ϖ
  let φ := IsLocalization.Away.map F B (algebraMap O A) ϖ
  letI : Algebra F B := φ.toAlgebra
  haveI : IsScalarTower O F B := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply O A B]
    exact (IsLocalization.map_eq _ _).symm)
  haveI : Algebra.FormallySmooth F B := Algebra.FormallySmooth.localization_base (Submonoid.powers ϖ)
  haveI : Algebra.FinitePresentation F B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O F B
  have hs : Algebra.Smooth F B := ⟨inferInstance, inferInstance⟩
  exact hs

/- English proof (translation)
Introduce `O _ _ _ ϖ _ m r hr1 hrm F _ _ _`. Conclude with `smooth_away_core O ϖ (Fin m) (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)) ⟨0, by omega⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (0 : ℕ) < r by omega⟩) F`.
-/
theorem smooth_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  intro O _ _ _ ϖ _ m r hr1 hrm F _ _ _
  exact smooth_away_core O ϖ (Fin m) (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)) ⟨0, by omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (0 : ℕ) < r by omega⟩) F

end GlobalTheory.CompanionTheory.Semistable
