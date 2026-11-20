import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlatStatement
open TensorProduct

namespace GlobalTheory.CompanionTheory.FinAlgFlat

/- English proof (translation)
Rewrite `h₁`, `h₂`, the goal using `[Algebra.isPushout_iff]`. Use `IsBaseChange.of_comp (R := R) (S := A) (T := B) (f := (IsScalarTower.toAlgHom R k T).toLinearMap) (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_` and prove the remaining obligations. Use `h₂ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[IsScalarTower.algebraMap_apply k T U]`.
-/
theorem isPushout_cancel (R k A B T U : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [CommRing U]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
    [Algebra A B] [Algebra A T] [Algebra A U] [Algebra B U] [Algebra k T] [Algebra k U]
    [Algebra T U]
    [IsScalarTower R A B] [IsScalarTower R A T] [IsScalarTower R A U] [IsScalarTower R B U]
    [IsScalarTower R k T] [IsScalarTower R k U] [IsScalarTower k T U] [IsScalarTower A T U]
    [IsScalarTower A B U]
    (h₁ : Algebra.IsPushout R A k T) (h₂ : Algebra.IsPushout R B k U) :
    Algebra.IsPushout A B T U := by
  rw [Algebra.isPushout_iff] at h₁ h₂ ⊢
  refine IsBaseChange.of_comp (R := R) (S := A) (T := B)
    (f := (IsScalarTower.toAlgHom R k T).toLinearMap)
    (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_
  convert h₂ using 1
  ext x
  simp [IsScalarTower.algebraMap_apply k T U]

noncomputable abbrev fibreMap (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    k ⊗[R] A →+* k ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R k) (IsScalarTower.toAlgHom R A B)).toRingHom

/- English proof (translation)
Use `letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra`. Use `letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra`. Use `letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra`. Use `letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra`. Use `haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl`.

Use `haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by`. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)`. Simplify using the standard rewrite rules. Use `haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by`. Rewrite using `[IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]`.

Both sides reduce to the same expression. Use `haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))`. Simplify using the standard rewrite rules. Establish `h` using `isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B) TensorProduct.isPushout' TensorProduct.isPushout'`.

Conclude with `(Algebra.isLocalization_iff_isPushout M B).mpr h.symm`.
-/
theorem fibreMap_isLocalization (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A]
    [CommRing B] [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI := (fibreMap R k A B).toAlgebra
    IsLocalization (M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      (k ⊗[R] B) := by
  letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra
  letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)
    simp
  haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]
    rfl
  haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))
    simp
  have h := isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B)
    TensorProduct.isPushout' TensorProduct.isPushout'
  exact (Algebra.isLocalization_iff_isPushout M B).mpr h.symm

end GlobalTheory.CompanionTheory.FinAlgFlat

namespace GlobalTheory.CompanionTheory.FinAlgFlat

/- English proof (translation)
Establish `hQA : (fibreMap R k Q An).Flat`. Establish `hl` using `fibreMap_isLocalization R k Q An N`. Use `letI := (fibreMap R k Q An).toAlgebra`. Conclude with `IsLocalization.flat (k ⊗[R] An) (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))`. Establish `e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) = (fibreMap R k Q An).comp (fibreMap R k P Q)`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a b`.

Simplify using `[← IsScalarTower.algebraMap_apply]`. Establish `hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat`. Rewrite using `[e]`. Conclude with `h.comp hQA`. Establish `hl` using `fibreMap_isLocalization R k P Bp M`.

Use `letI i1 := (fibreMap R k P Bp).toAlgebra`. Use `letI i2 := (fibreMap R k Bp An).toAlgebra`. Use `letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra`. Use `haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl`. Conclude with `(Module.flat_iff_of_isLocalization (k ⊗[R] Bp) (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA`.
-/
theorem fibreMap_flat_localize (R k P Q Bp An : Type*) [CommRing R] [CommRing k] [CommRing P]
    [CommRing Q] [CommRing Bp] [CommRing An] [Algebra R k] [Algebra R P] [Algebra R Q]
    [Algebra R Bp] [Algebra R An] [Algebra P Q] [Algebra P Bp] [Algebra P An] [Algebra Q An]
    [Algebra Bp An] [IsScalarTower R P Q] [IsScalarTower R P Bp] [IsScalarTower R Q An]
    [IsScalarTower R Bp An] [IsScalarTower P Q An] [IsScalarTower P Bp An]
    (M : Submonoid P) [IsLocalization M Bp] (N : Submonoid Q) [IsLocalization N An]
    (h : (fibreMap R k P Q).Flat) : (fibreMap R k Bp An).Flat := by
  have hQA : (fibreMap R k Q An).Flat := by
    have hl := fibreMap_isLocalization R k Q An N
    letI := (fibreMap R k Q An).toAlgebra
    exact IsLocalization.flat (k ⊗[R] An)
      (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))
  have e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) =
      (fibreMap R k Q An).comp (fibreMap R k P Q) := by
    refine RingHom.ext fun x => ?_
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      simp [← IsScalarTower.algebraMap_apply]
  have hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat := by
    rw [e]; exact h.comp hQA
  have hl := fibreMap_isLocalization R k P Bp M
  letI i1 := (fibreMap R k P Bp).toAlgebra
  letI i2 := (fibreMap R k Bp An).toAlgebra
  letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra
  haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl
  exact (Module.flat_iff_of_isLocalization (k ⊗[R] Bp)
    (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA

/- English proof (translation)
Use `haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q`. Use `haveI : Algebra.IsIntegral P Q := inferInstance`. Use `haveI : Algebra.IsIntegral R P := inferInstance`. Use `haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P`. Use `haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q`.

Set `p : Ideal P` to `n.comap (algebraMap P Q)`. Use `haveI hp : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n`. Establish `hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)`. Use `letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) := (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra`. Use `haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) := .of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]`. Conclude with `(Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm`. Use `haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) := .of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x, ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n), IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n), ← IsScalarTower.algebraMap_apply R P Q, ← IsScalarTower.algebraMap_ap …`. Use `haveI : IsNoetherianRing (Localization.AtPrime p) := IsLocalization.isNoetherianRing p.primeCompl _ inferInstance`.

Use `haveI : IsNoetherianRing (Localization.AtPrime n) := IsLocalization.isNoetherianRing n.primeCompl _ inferInstance`. Use `haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`. Establish `ham : a ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal a).mpr hnu`.

Rewrite `ham` using `[← hmR, Ideal.mem_comap]`. Establish `hm` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p (algebraMap R P a)).mpr ham`. Rewrite `hm` using `[← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hm ha`. Use `haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) := Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl`.

Establish `hfl : Module.Flat R (Localization.AtPrime n)` using `inferInstance`. Establish `hfib` using `fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p) (Localization.AtPrime n) p.primeCompl n.primeCompl h`. Establish `hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n)` using `GlobalTheory.T.module_flat_of_flat_and_fibre_flat R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib`. Conclude with `(Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl (Localization.AtPrime n)).mp hBA`.
-/
theorem flat_localization_of_fibre (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) (n : Ideal Q) [n.IsMaximal] :
    Module.Flat P (Localization.AtPrime n) := by
  haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q
  haveI : Algebra.IsIntegral P Q := inferInstance
  haveI : Algebra.IsIntegral R P := inferInstance
  haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q
  let p : Ideal P := n.comap (algebraMap P Q)
  haveI hp : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) :=
    (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra
  haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]
      exact (Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm
  haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x,
        ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n),
        IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n),
        ← IsScalarTower.algebraMap_apply R P Q,
        ← IsScalarTower.algebraMap_apply R Q (Localization.AtPrime n)]
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [← hmR, Ideal.mem_comap] at ham
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p
      (algebraMap R P a)).mpr ham
    rw [← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) :=
    Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl
  have hfl : Module.Flat R (Localization.AtPrime n) := inferInstance
  have hfib := fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p)
    (Localization.AtPrime n) p.primeCompl n.primeCompl h
  have hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n) :=
    GlobalTheory.T.module_flat_of_flat_and_fibre_flat R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime n)).mp hBA

/- English proof (translation)
The claim follows from `Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n) (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)`.
-/
theorem flat_of_fibreMap_flat (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) : Module.Flat P Q :=
  Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n)
    (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)

/- English proof (translation)
Introduce `R P Q _ _ _ _ _ _ _ _ _ _ φ h`. Use `letI : Algebra P Q := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm`. Establish `e : IsScalarTower.toAlgHom R P Q = φ` using `by ext; rfl`. Establish `h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat`.

Rewrite using `[fibreMap, e]`. Conclude with `h`. Conclude with `flat_of_fibreMap_flat R P Q h'`.
-/
theorem ringHom_flat_of_fibre_flat : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q),
    (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat →
      φ.toRingHom.Flat := by
  intro R P Q _ _ _ _ _ _ _ _ _ _ φ h
  letI : Algebra P Q := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : IsScalarTower.toAlgHom R P Q = φ := by ext; rfl
  have h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat := by
    rw [fibreMap, e]; exact h
  exact flat_of_fibreMap_flat R P Q h'

end GlobalTheory.CompanionTheory.FinAlgFlat
