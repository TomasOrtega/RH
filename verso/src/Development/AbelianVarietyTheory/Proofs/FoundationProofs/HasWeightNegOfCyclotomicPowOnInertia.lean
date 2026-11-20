import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ κ hκ e m hm h`. Establish `hcyc : Continuous (Loc.cyc l l)` using `cyclotomicCharacter.continuous l ℚ_[l] (Om l)`. Establish `ha : Continuous (algebraMap ℤ_[l] (Qbar l))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]`. Conclude with `(continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val`.

Establish `hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l))` using `Units.continuous_val.comp ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)`. Use `set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def`. Establish `hf : Continuous f`. Establish `: f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e`. Use function extensionality and compare the values at `σ`.

Simplify using `only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]`. Rewrite using `[this]`. Conclude with `hκ.mul (hA.pow e)`. Establish `hf1 : f 1 = 1` using `by simp [hf_def]`. Establish `hm0 : 0 < m` using `hm`.

Establish `hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite`. Use `Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_` and prove the remaining obligations. Conclude with `(Polynomial.mem_nthRoots hm0).2 hz.1`. Establish `ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ)` using `hfin.isClosed.isOpen_compl.preimage hf`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (fun hx => hx.2 hf1)`.

Use `⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩` and prove the remaining obligations. Establish `hgI' : g ∈ Loc.Iq l` using `hgI`. Establish `hpow : f g ^ m = 1`. Use `congrArg Units.val (h g hgI')` as an intermediate fact. Simplify `this` using `[hf_def, Units.val_pow_eq_pow_val]`.

Establish `hone : f g = 1`. Assume the negation of the conclusion as `hne`. Conclude with `hU hg ⟨hpow, hne⟩`. Establish `hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1` using `Units.ext hone`. Simplify using `only [MonoidHom.id_apply, zpow_neg]`.

Conclude with `eq_inv_of_mul_eq_one_left hu`.
-/
theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
