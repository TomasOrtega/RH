import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

variable {F : Type} [Field F] [NumberField F]

noncomputable def classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    ClassGroup (𝓞 F) →* Circle where
  toFun c := AddChar.circleEquivComplex.symm ψ (Additive.ofMul c)
  map_one' := by
    rw [ofMul_one]
    exact AddChar.map_zero_eq_one _
  map_mul' a b := by
    rw [ofMul_mul]
    exact AddChar.map_add_eq_mul _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (c : ClassGroup (𝓞 F)) :
    (classCircle ψ c : ℂ) = ψ (Additive.ofMul c) := by
  rfl

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Establish `hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)))` using `IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)`. Establish `h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))` using `⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩`. Rewrite using `[ContinuousAt, map_one]`. Use `tendsto_nhds_of_eventually_eq ?_` and prove the remaining obligations.

Use `filter_upwards [hU.mem_nhds h1] with y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Establish `hx1 : IdeleGroup.toFractionalIdeal x = 1`. Rewrite using `[← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]`. Conclude with `hx`.

Rewrite using `[MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1, map_one, map_one]`.
-/
theorem continuous_comp_toClassGroup (φ : ClassGroup (𝓞 F) →* Circle) :
    Continuous (φ.comp (IdeleClassGroup.toClassGroup (K := F))) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))) :=
    IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)
  have h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)) :=
    ⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩
  rw [ContinuousAt, map_one]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hU.mem_nhds h1] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1,
    map_one, map_one]

noncomputable def classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) : HeckeCharacter F where
  toMonoidHom := (classCircle ψ).comp IdeleClassGroup.toClassGroup
  continuous_toFun := continuous_comp_toClassGroup _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem classHecke_toIdele (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (x : IdeleGroup F) :
    (classHecke ψ).toIdele x = classCircle ψ (IdeleGroup.toClassGroup x) :=
  rfl

/- English proof (translation)
Introduce `x hx`. Establish `h1 : IdeleGroup.toFractionalIdeal x = 1`. Rewrite using `[← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]`. Conclude with `hx`. Rewrite using `[MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]`.
-/
theorem standardOpenSubgroup_le_ker (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    standardOpenSubgroup F ≤ (classHecke ψ).toIdele.ker := by
  intro x hx
  have h1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]

/- English proof (translation)
Use `show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[Pi.zero_apply, multiplicity_eq_zero]`. Introduce `h`.

Conclude with `v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))`.
-/
theorem idealLevel_top : idealLevel (⊤ : Ideal (𝓞 F)) = finiteLevel 0 := by
  show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0
  congr 1
  funext v
  rw [Pi.zero_apply, multiplicity_eq_zero]
  intro h
  exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

/- English proof (translation)
Establish `hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥` using `top_ne_bot`. Establish `hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Apply `standardOpenSubgroup_le_ker ψ` to reduce the goal to its premises. Rewrite using `[mem_standardOpenSubgroup_iff_ord]`.

Introduce `v`. Rewrite `hz` using `[idealLevel_top]`. Apply `ord_eq_zero_of_mem_unitsLevel (n := 0)` to reduce the goal to its premises. Rewrite using `[← finiteComponent_toFinite, toFinite_ofFinite]`. Conclude with `Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)`.

Establish `hd` using `((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle`. Conclude with `top_le_iff.mp (Ideal.le_of_dvd hd)`.
-/
theorem conductor_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    (classHecke ψ).conductor = ⊤ := by
  have hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker := by
    rintro _ ⟨z, hz, rfl⟩
    apply standardOpenSubgroup_le_ker ψ
    rw [mem_standardOpenSubgroup_iff_ord]
    intro v
    rw [idealLevel_top] at hz
    apply ord_eq_zero_of_mem_unitsLevel (n := 0)
    rw [← finiteComponent_toFinite, toFinite_ofFinite]
    exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)
  have hd := ((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle
  exact top_le_iff.mp (Ideal.le_of_dvd hd)

/- English proof (translation)
Establish `hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (classHecke ψ).coeff v.asIdeal = ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩))`. Introduce `v`. Establish `hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor`. Rewrite using `[conductor_classHecke]`. Introduce `h`.

Conclude with `v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))`. Rewrite using `[HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]`. Take `⟨x, hx, hxI⟩` from `exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)`. Establish `heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) = FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩` using `Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])`. Rewrite using `[HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI, classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]`.

Use `UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥, (classHecke ψ).coeff I = ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ` and prove the remaining obligations. Introduce `h`. Conclude with `absurd Ideal.zero_eq_bot h`. Introduce `x hx hx0`. Take `rfl` from `Ideal.isUnit_iff.mp hx`.

Establish `h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1` using `Subtype.ext Ideal.one_eq_top.symm`. Rewrite using `[HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]`. Introduce `a p ha hp ih hpa`. Establish `ha' : a ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot]`.

Conclude with `ha`. Establish `hp0 : p ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot]`. Conclude with `hp.ne_zero`. Establish `hv` using `hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩`.

Establish `hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) = ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩` using `Subtype.ext rfl`. Rewrite using `[HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]`. Use `congr 1`.
-/
theorem coeff_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (classHecke ψ).coeff J =
      ψ (Additive.ofMul (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩)) := by
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (classHecke ψ).coeff v.asIdeal =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) := by
    intro v
    have hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor := by
      rw [conductor_classHecke]
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
    rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]
    obtain ⟨x, hx, hxI⟩ := exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)
    have heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
      Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])
    rw [HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI,
      classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥,
      (classHecke ψ).coeff I =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx hx0
    obtain rfl := Ideal.isUnit_iff.mp hx
    have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact ha
    have hp0 : p ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact hp.ne_zero
    have hv := hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩ :=
      Subtype.ext rfl
    rw [HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]
    congr 1

end GlobalTheory.CompanionTheory.PartialZeta
