import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    Representation LL ↥(GK K) ↥S where
  toFun g := (ρ g).restrict (hS g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : ↥(GK K)) (v : ↥S) : ((subRep ρ S hS g v : ↥S) : V) = ρ g v := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.Pst.DmapNonzero

open GlobalTheory.Pst.DmapNonzero in

/- English proof (translation)
Introduce `l _ P K LL _ _ _ hb V V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf hV hf0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `S : Submodule LL V` to `LinearMap.ker f`. Establish `hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S` using `fun g v hv => by`.

Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hf, hv, map_zero]`. Set `ρS` to `subRep ρ S hS`. Establish `hfS : ∀ g v, S.subtype (ρS g v) = ρ g (S.subtype v)` using `fun _ _ => rfl`. Use `haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans LL V`.

Use `haveI : FiniteDimensional ℚ_[l] ↥S := Module.Finite.of_injective (S.subtype.restrictScalars ℚ_[l]) S.injective_subtype`. Establish `hex : Function.Exact (S.subtype.restrictScalars ℚ_[l]) (f.restrictScalars ℚ_[l])`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨⟨v, h⟩, rfl⟩`. Introduce and unpack `⟨w, rfl⟩`. Conclude with `w.2`. Establish `hexT` using `Module.Flat.rTensor_exact (Bst P) hex`. Establish `hinj : Function.Injective ((S.subtype.restrictScalars ℚ_[l]).rTensor (Bst P))` using `Module.Flat.rTensor_preserves_injective_linearMap _ S.injective_subtype`.

Set `j` to `dmap P hfS`. Establish `hsurj : Function.Surjective j`. Introduce `y`. Establish `h0 : tensV P f (y : V ⊗[ℚ_[l]] Bst P) = 0` using `congrArg Subtype.val (hcon y)`. Rewrite `h0` using `[tensV_eq_rTensor]`.

Take `⟨z, hz⟩` from `(hexT _).mp h0`. Establish `hz' : tensV P S.subtype z = y` using `by rw [tensV_eq_rTensor]; exact hz`. Take `⟨K', hK'⟩` from `(mem_Dpst P ρ).mp y.2`. Establish `hzD : z ∈ Dpst P ρS`. Use `(mem_Dpst P ρS).mpr ⟨K', fun g hg => hinj ?_⟩` and prove the remaining obligations.

Rewrite using `[← tensV_eq_rTensor, ← tensV_eq_rTensor, tensV_stRep P ρS ρ S.subtype hfS, hz', hK' g hg]`. Conclude with `⟨⟨z, hzD⟩, Subtype.ext hz'⟩`. Set `jU : DpstUr P ρS →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ` to `{ toFun := fun x => toUr P ρ (j ((toUr P ρS).symm x)) map_add' := fun x y => by simp only [map_add] map_smul' := fun c x => dmap_mulD P hfS c ((toUr P ρS).symm x) }`. Establish `hjU : Function.Surjective jU` using `fun y => by`. Take `⟨x, hx⟩` from `hsurj ((toUr P ρ).symm y)`.

Use `⟨toUr P ρS x, ?_⟩` and prove the remaining obligations. Use `show toUr P ρ (j ((toUr P ρS).symm (toUr P ρS x))) = y`. Rewrite using `[AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]`. Establish `h1` using `jU.rank_le_of_surjective hjU`. Establish `h2` using `hb ↥S ρS`.

Establish `h3 : finrank ℚ_[l] ↥S < finrank ℚ_[l] V`. Establish `hne : S.restrictScalars ℚ_[l] ≠ ⊤`. Rewrite using `[Ne, Submodule.restrictScalars_eq_top_iff, LinearMap.ker_eq_top]`. Conclude with `hf0`. Conclude with `Submodule.finrank_lt hne`.

Establish `h4 : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = (finrank ℚ_[l] V : Cardinal)`. Rewrite using `[hV, Module.finrank_eq_rank]`. Establish `h5 : ((finrank ℚ_[l] V : ℕ) : Cardinal) ≤ (finrank ℚ_[l] ↥S : ℕ)` using `h4 ▸ h1.trans h2`. Conclude with `absurd (Nat.cast_le.mp h5) (not_le.mpr h3)`.
-/
theorem GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := by
  intro l _ P K LL _ _ _ hb V V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf hV hf0
  classical
  by_contra hcon
  push_neg at hcon
  let S : Submodule LL V := LinearMap.ker f
  have hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S := fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, map_zero]
  let ρS := subRep ρ S hS
  have hfS : ∀ g v, S.subtype (ρS g v) = ρ g (S.subtype v) := fun _ _ => rfl
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans LL V
  haveI : FiniteDimensional ℚ_[l] ↥S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℚ_[l]) S.injective_subtype

  have hex : Function.Exact (S.subtype.restrictScalars ℚ_[l]) (f.restrictScalars ℚ_[l]) := by
    intro v
    constructor
    · intro h; exact ⟨⟨v, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩; exact w.2
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((S.subtype.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ S.injective_subtype
  let j := dmap P hfS
  have hsurj : Function.Surjective j := by
    intro y
    have h0 : tensV P f (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val (hcon y)
    rw [tensV_eq_rTensor] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P S.subtype z = y := by rw [tensV_eq_rTensor]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρS := by
      refine (mem_Dpst P ρS).mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rTensor, ← tensV_eq_rTensor, tensV_stRep P ρS ρ S.subtype hfS, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  let jU : DpstUr P ρS →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x => toUr P ρ (j ((toUr P ρS).symm x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => dmap_mulD P hfS c ((toUr P ρS).symm x) }
  have hjU : Function.Surjective jU := fun y => by
    obtain ⟨x, hx⟩ := hsurj ((toUr P ρ).symm y)
    refine ⟨toUr P ρS x, ?_⟩
    show toUr P ρ (j ((toUr P ρS).symm (toUr P ρS x))) = y
    rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]
  have h1 := jU.rank_le_of_surjective hjU
  have h2 := hb ↥S ρS
  have h3 : finrank ℚ_[l] ↥S < finrank ℚ_[l] V := by
    have hne : S.restrictScalars ℚ_[l] ≠ ⊤ := by
      rw [Ne, Submodule.restrictScalars_eq_top_iff, LinearMap.ker_eq_top]
      exact hf0
    exact Submodule.finrank_lt hne
  have h4 : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = (finrank ℚ_[l] V : Cardinal) := by
    rw [hV, Module.finrank_eq_rank]
  have h5 : ((finrank ℚ_[l] V : ℕ) : Cardinal) ≤ (finrank ℚ_[l] ↥S : ℕ) := h4 ▸ h1.trans h2
  exact absurd (Nat.cast_le.mp h5) (not_le.mpr h3)
