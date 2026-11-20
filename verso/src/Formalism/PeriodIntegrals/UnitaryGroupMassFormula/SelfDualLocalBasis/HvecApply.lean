import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.HformSumRight

open Matrix NumberField IsDedekindDomain

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

def hvec {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin m → E) where
  toFun y := fun i => hform σ J (x i) y
  map_add' y y' := by ext i; simp [hform_add_right]
  map_smul' c y := by ext i; simp [hform_smul_right]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hvec_apply {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (y : Fin n → E) (i : Fin m) :
    hvec σ J x y i = hform σ J (x i) y := rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ n σ J Lb T hfin hdual hT`. Assume the negation of the conclusion as `hne`. Establish `hlt : Module.finrank E (Submodule.span E (Lb : Set (Fin n → E))) < n`. Establish `h` using `Submodule.finrank_lt hne`. Rewrite `h` using `[Module.finrank_fin_fun]`. Then use the resulting hypothesis.

Set `b` to `Module.finBasis E (Submodule.span E (Lb : Set (Fin n → E)))`. Set `x : Fin (Module.finrank E (Submodule.span E (Lb : Set (Fin n → E)))) → Fin n → E` to `fun i => (b i : Fin n → E)`. Establish `hker : LinearMap.ker (hvec (σ : E →+* E) J x) ≠ ⊥`. Introduce `hbot`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (hvec (σ : E →+* E) J x)`.

Rewrite `h1` using `[hbot, finrank_bot, add_zero, Module.finrank_fin_fun]`. Establish `h2` using `Submodule.finrank_le (LinearMap.range (hvec (σ : E →+* E) J x))`. Rewrite `h2` using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hker`.

Apply `hy0` to reduce the goal to its premises. Use `hN F E n σ J Lb T hfin hdual hT y fun z hz => ?_` and prove the remaining obligations. Establish `hzV : z ∈ Submodule.span E (Lb : Set (Fin n → E))` using `Submodule.subset_span hz`. Establish `hz' : z = ∑ i, (b.repr ⟨z, hzV⟩ i) • x i`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨z, hzV⟩)`.

Rewrite `h` using `[Submodule.coe_sum]`. Conclude with `h.symm`. Rewrite using `[hz', hform_sum_left]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hform_smul_left]`.

Establish `hi : hform (σ : E →+* E) J (x i) y = 0`. Rewrite using `[← hvec_apply]`. Conclude with `congrFun (LinearMap.mem_ker.mp hy) i`. Rewrite using `[hi, mul_zero]`.
-/
theorem spanTop_of (hN : Nondeg) : SpanTop := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hdual hT
  by_contra hne
  have hlt : Module.finrank E (Submodule.span E (Lb : Set (Fin n → E))) < n := by
    have h := Submodule.finrank_lt hne
    rwa [Module.finrank_fin_fun] at h
  let b := Module.finBasis E (Submodule.span E (Lb : Set (Fin n → E)))
  let x : Fin (Module.finrank E (Submodule.span E (Lb : Set (Fin n → E)))) → Fin n → E :=
    fun i => (b i : Fin n → E)
  have hker : LinearMap.ker (hvec (σ : E →+* E) J x) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (hvec (σ : E →+* E) J x)
    rw [hbot, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_le (LinearMap.range (hvec (σ : E →+* E) J x))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  apply hy0
  refine hN F E n σ J Lb T hfin hdual hT y fun z hz => ?_
  have hzV : z ∈ Submodule.span E (Lb : Set (Fin n → E)) := Submodule.subset_span hz
  have hz' : z = ∑ i, (b.repr ⟨z, hzV⟩ i) • x i := by
    have h := congrArg Subtype.val (b.sum_repr ⟨z, hzV⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [hz', hform_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hform_smul_left]
  have hi : hform (σ : E →+* E) J (x i) y = 0 := by
    rw [← hvec_apply]
    exact congrFun (LinearMap.mem_ker.mp hy) i
  rw [hi, mul_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ n σ J x _ hnd`. Establish `hinj : Function.Injective (hvec (σ : E →+* E) J x)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Conclude with `hnd y fun i => by rw [← hvec_apply, hy]; rfl`.

Set `e` to `LinearEquiv.ofInjectiveEndo (hvec (σ : E →+* E) J x) hinj`. Establish `he : ∀ v, e v = hvec (σ : E →+* E) J x v` using `fun v => rfl`. Use `⟨fun j => e.symm (Pi.single j 1), fun i j => ?_, fun w => ⟨fun j => e w j, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hvec_apply, ← he, LinearEquiv.apply_symm_apply, Pi.single_apply]`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, LinearEquiv.apply_symm_apply]`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem dualBasis : DualBasis := by
  intro F E _ _ _ _ _ n σ J x _ hnd
  have hinj : Function.Injective (hvec (σ : E →+* E) J x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd y fun i => by rw [← hvec_apply, hy]; rfl
  let e := LinearEquiv.ofInjectiveEndo (hvec (σ : E →+* E) J x) hinj
  have he : ∀ v, e v = hvec (σ : E →+* E) J x v := fun v => rfl
  refine ⟨fun j => e.symm (Pi.single j 1), fun i j => ?_, fun w => ⟨fun j => e w j, ?_⟩⟩
  · rw [← hvec_apply, ← he, LinearEquiv.apply_symm_apply, Pi.single_apply]
  · apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]

end PI.SelfDualLoc.W
