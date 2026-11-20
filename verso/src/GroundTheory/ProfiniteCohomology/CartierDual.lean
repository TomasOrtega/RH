import Mathlib
import GroundTheory.ProfiniteCohomology.CartierDualDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section ULiftInt

attribute [-instance] ULift.smulLeft ULift.module

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module (ULift.{u} ℤ) A]
  [Module (ULift.{u} ℤ) B]

variable (A B) in

def uliftIntLinearEquivAddHom : (A →ₗ[ULift.{u} ℤ] B) ≃+ (A →+ B) where
  toFun f := f.toAddMonoidHom
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r a => by
        obtain ⟨k⟩ := r
        have h : (ULift.up k : ULift.{u} ℤ) = ((k : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [RingHom.id_apply, h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k a,
          Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k (g a)]
        exact map_zsmul g k a }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem uliftIntLinearEquivAddHom_apply (f : A →ₗ[ULift.{u} ℤ] B) (a : A) :
    uliftIntLinearEquivAddHom A B f a = f a :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uliftIntLinearEquivAddHom_symm_apply (g : A →+ B) (a : A) :
    (uliftIntLinearEquivAddHom A B).symm g a = g a :=
  rfl

end ULiftInt

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

section MonoidHom

variable (K L) in

def cartierDualEquivMonoidHom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) ≃ (Multiplicative M →* Lˣ) :=
  (uliftIntLinearEquivAddHom M (Additive Lˣ)).toEquiv.trans AddMonoidHom.toMultiplicativeLeft

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem cartierDualEquivMonoidHom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    cartierDualEquivMonoidHom K L M f (Multiplicative.ofAdd m) = Additive.toMul (f m) :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartierDualEquivMonoidHom_symm_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (φ : Multiplicative M →* Lˣ) (m : M) :
    (cartierDualEquivMonoidHom K L M).symm φ m = Additive.ofMul (φ (Multiplicative.ofAdd m)) :=
  rfl

end MonoidHom

section RootsOfUnity

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(cartierDualEquivMonoidHom K L M f (Multiplicative.ofAdd m)) ^ n = 1`. Rewrite using `[← map_pow, ← ofAdd_nsmul, hn m, ofAdd_zero, map_one]`.
-/
theorem cartierDual_pow_eq_one {M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)} {n : ℕ}
    (hn : ∀ m : M, n • m = 0) (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    (Additive.toMul (α := Lˣ) (f m)) ^ n = 1 := by
  change (cartierDualEquivMonoidHom K L M f (Multiplicative.ofAdd m)) ^ n = 1
  rw [← map_pow, ← ofAdd_nsmul, hn m, ofAdd_zero, map_one]

/- English proof (translation)
Use `⟨fun f g h => ?_, fun f₀ => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun h m` as an intermediate fact. Conclude with `Additive.toMul.injective (Subtype.ext (congrArg (Additive.toMul (α := Lˣ)) this))`. Set `f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L` to `f₀`.

Set `g : M →+ Additive (rootsOfUnity n L)` to `{ toFun := fun m => Additive.ofMul ⟨Additive.toMul (α := Lˣ) (f m), (mem_rootsOfUnity n _).2 (cartierDual_pow_eq_one hn f m)⟩ map_zero' := by`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Additive.toMul (α := Lˣ) (f 0) = 1`. Rewrite using `[map_zero]`.

Both sides reduce to the same expression. Use the proof step `map_add' := fun a b => by`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Additive.toMul (α := Lˣ) (f (a + b)) = Additive.toMul (α := Lˣ) (f a) * Additive.toMul (α := Lˣ) (f b)`.

Rewrite using `[map_add]`. Use `rfl }`. Use `⟨(uliftIntLinearEquivAddHom M (galRootsOfUnity.{u} K L n)).symm g, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem bijective_ihom_map_rootsOfUnityToUnits (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) {n : ℕ}
    (hn : ∀ m : M, n • m = 0) :
    Function.Bijective ((Rep.ihom M).map (rootsOfUnityToUnits K L n)).hom := by
  refine ⟨fun f g h => ?_, fun f₀ => ?_⟩
  · refine LinearMap.ext fun m => ?_
    have := LinearMap.congr_fun h m
    exact Additive.toMul.injective (Subtype.ext (congrArg (Additive.toMul (α := Lˣ)) this))
  · let f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f₀
    let g : M →+ Additive (rootsOfUnity n L) :=
      { toFun := fun m => Additive.ofMul
          ⟨Additive.toMul (α := Lˣ) (f m), (mem_rootsOfUnity n _).2 (cartierDual_pow_eq_one hn f m)⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          change Additive.toMul (α := Lˣ) (f 0) = 1
          rw [map_zero]
          rfl
        map_add' := fun a b => by
          apply Additive.toMul.injective
          apply Subtype.ext
          change Additive.toMul (α := Lˣ) (f (a + b)) =
            Additive.toMul (α := Lˣ) (f a) * Additive.toMul (α := Lˣ) (f b)
          rw [map_add]
          rfl }
    refine ⟨(uliftIntLinearEquivAddHom M (galRootsOfUnity.{u} K L n)).symm g, ?_⟩
    refine LinearMap.ext fun m => ?_
    rfl

variable (K L) in

def cartierDualIsoHomRootsOfUnityOfNsmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (n : ℕ)
    (hn : ∀ m : M, n • m = 0) :
    (Rep.ihom M).obj (galRootsOfUnity.{u} K L n) ≅ cartierDual K L M :=
  Rep.isoOfBijective ((Rep.ihom M).map (rootsOfUnityToUnits K L n))
    (bijective_ihom_map_rootsOfUnityToUnits M hn)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartierDualIsoHomRootsOfUnityOfNsmul_hom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    (n : ℕ) (hn : ∀ m : M, n • m = 0) (f : M →ₗ[ULift.{u} ℤ] galRootsOfUnity.{u} K L n) (m : M) :
    ((cartierDualIsoHomRootsOfUnityOfNsmul K L M n hn).hom.hom f :
      M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m = (rootsOfUnityToUnits K L n).hom (f m) :=
  rfl

variable (K L) in

def cartierDualIsoHomRootsOfUnity (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    (Rep.ihom M).obj (galRootsOfUnity.{u} K L (AddMonoid.exponent M)) ≅ cartierDual K L M :=
  cartierDualIsoHomRootsOfUnityOfNsmul K L M _ (AddMonoid.exponent_nsmul_eq_zero)

end RootsOfUnity

section Finite

variable (K L) in

instance finite_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] :
    Finite (cartierDual K L M) := by
  have : NeZero (AddMonoid.exponent M) := ⟨AddMonoid.exponent_ne_zero_of_finite⟩
  let F : (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) → M → rootsOfUnity (AddMonoid.exponent M) L :=
    fun f m => ⟨Additive.toMul (α := Lˣ) (f m), (mem_rootsOfUnity _ _).2
      (cartierDual_pow_eq_one AddMonoid.exponent_nsmul_eq_zero f m)⟩
  refine Finite.of_injective (β := M → rootsOfUnity (AddMonoid.exponent M) L) F fun f g h => ?_
  refine LinearMap.ext fun m => ?_
  have := congrArg (fun x : rootsOfUnity (AddMonoid.exponent M) L => (x : Lˣ)) (congrFun h m)
  exact Additive.toMul.injective this

instance finite_cartierDual_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] :
    Finite (cartierDual K L (cartierDual K L M)) :=
  have : Finite (cartierDual K L M) := finite_cartierDual K L M
  finite_cartierDual K L _

instance isDiscreteRep_cartierDual [Algebra.IsIntegral K L] (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] [IsDiscreteRep M] : IsDiscreteRep (cartierDual K L M) := by
  refine ⟨fun f => ?_⟩
  let f' : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
  refine Subgroup.isOpen_mono (H₁ := ⨅ m : M, stabilizer M.ρ m ⊓
      stabilizer (galUnits.{u} K L).ρ (f' m)) (fun σ hσ => ?_) ?_
  · rw [mem_stabilizer]
    refine LinearMap.ext fun m => ?_
    have hm := Subgroup.mem_iInf.1 hσ m
    rw [Subgroup.mem_inf, mem_stabilizer, mem_stabilizer] at hm
    change (galUnits.{u} K L).ρ σ (f' (M.ρ σ⁻¹ m)) = f' m
    have h1 : M.ρ σ⁻¹ m = m := by
      conv_lhs => rw [← hm.1]
      exact Representation.inv_self_apply _ _ _
    rw [h1, hm.2]
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun m => by
      rw [Subgroup.coe_inf]
      exact (isOpen_stabilizer M m).inter (isOpen_stabilizer (galUnits.{u} K L) (f' m))

/- English proof (translation)
Establish `: HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M))`. Rewrite using `[Monoid.exponent_multiplicative]` and apply the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    Nat.card (cartierDual K L M) = Nat.card M := by
  have : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M)) := by
    rwa [Monoid.exponent_multiplicative]
  calc Nat.card (cartierDual K L M) = Nat.card (Multiplicative M →* Lˣ) :=
        Nat.card_congr (cartierDualEquivMonoidHom K L M)
    _ = Nat.card (Multiplicative M) :=
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative M) L
    _ = Nat.card M := Nat.card_congr Multiplicative.toAdd

variable (K) in

/- English proof (translation)
Establish `hdvd : AddMonoid.exponent M ∣ Nat.card M` using `AddGroup.exponent_dvd_nat_card`. Establish `hK : (AddMonoid.exponent M : K) ≠ 0`. Take `⟨c, hc⟩` from `hdvd`. Introduce `h0`. Apply `h` to reduce the goal to its premises.

Rewrite using `[hc, Nat.cast_mul, h0, zero_mul]`. Establish `: NeZero (AddMonoid.exponent M : L)` using `⟨by`. Rewrite using `[← map_natCast (algebraMap K L)]`. Conclude with `(map_ne_zero (algebraMap K L)).2 hK⟩`. Use `infer_instance`.
-/
theorem hasEnoughRootsOfUnity_exponent_of_isSepClosed [IsSepClosed L] (M : Type*)
    [AddCommGroup M] [Finite M] (h : (Nat.card M : K) ≠ 0) :
    HasEnoughRootsOfUnity L (AddMonoid.exponent M) := by
  have hdvd : AddMonoid.exponent M ∣ Nat.card M := AddGroup.exponent_dvd_nat_card
  have hK : (AddMonoid.exponent M : K) ≠ 0 := by
    obtain ⟨c, hc⟩ := hdvd
    intro h0
    apply h
    rw [hc, Nat.cast_mul, h0, zero_mul]
  have : NeZero (AddMonoid.exponent M : L) := ⟨by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero (algebraMap K L)).2 hK⟩
  infer_instance

end Finite

section Pairing

variable (K L) [Algebra.IsIntegral K L]

def cartierPairingDiscrete (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M] [IsDiscreteRep M] :
    (⟨M ⊗ cartierDual K L M, (isDiscreteRep_apply _).2 inferInstance⟩ :
      DiscreteRep.{u} (ULift.{u} ℤ) Gal(L/K)) ⟶
      ⟨galUnits.{u} K L, (isDiscreteRep_apply _).2 inferInstance⟩ :=
  ObjectProperty.homMk (cartierPairing K L M)

variable {K L} in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartierPairingDiscrete_hom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [IsDiscreteRep M] : (cartierPairingDiscrete K L M).hom = cartierPairing K L M :=
  rfl

end Pairing

section Biduality

/- English proof (translation)
Establish `: HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M))`. Rewrite using `[Monoid.exponent_multiplicative]` and apply the resulting hypothesis. Assume the negation of the conclusion as `hm`. Establish `hm' : Multiplicative.ofAdd m ≠ 1` using `fun h1 => hm (Multiplicative.ofAdd.injective h1)`. Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative M) L hm'`.

Apply `hφ` to reduce the goal to its premises. Use `h ((cartierDualEquivMonoidHom K L M).symm φ)` as an intermediate fact. Rewrite `this` using `[cartierDualEquivMonoidHom_symm_apply]`. Conclude with `Additive.ofMul.injective this`.
-/
theorem eq_zero_of_forall_cartierDual_apply_eq_zero {M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)}
    [Finite M] [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] {m : M}
    (h : ∀ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L, f m = 0) : m = 0 := by
  have : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M)) := by
    rwa [Monoid.exponent_multiplicative]
  by_contra hm
  have hm' : Multiplicative.ofAdd m ≠ 1 := fun h1 => hm (Multiplicative.ofAdd.injective h1)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative M) L hm'
  apply hφ
  have := h ((cartierDualEquivMonoidHom K L M).symm φ)
  rw [cartierDualEquivMonoidHom_symm_apply] at this
  exact Additive.ofMul.injective this

/- English proof (translation)
Use `AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun f => ?_` and prove the remaining obligations. Set `f' : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L` to `f`. Express the relevant statement in the definitionally equal form `AddMonoid.exponent M • f' = 0`. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, ← map_nsmul, AddMonoid.exponent_nsmul_eq_zero, map_zero]`.

Both sides reduce to the same expression.
-/
theorem exponent_cartierDual_dvd (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    AddMonoid.exponent (cartierDual K L M) ∣ AddMonoid.exponent M := by
  refine AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun f => ?_
  let f' : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
  change AddMonoid.exponent M • f' = 0
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.smul_apply, ← map_nsmul, AddMonoid.exponent_nsmul_eq_zero, map_zero]
  rfl

/- English proof (translation)
Establish `: NeZero (AddMonoid.exponent M)` using `⟨AddMonoid.exponent_ne_zero_of_finite⟩`. Conclude with `HasEnoughRootsOfUnity.of_dvd L (exponent_cartierDual_dvd M)`.
-/
theorem hasEnoughRootsOfUnity_exponent_cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    HasEnoughRootsOfUnity L (AddMonoid.exponent (cartierDual K L M)) := by
  have : NeZero (AddMonoid.exponent M) := ⟨AddMonoid.exponent_ne_zero_of_finite⟩
  exact HasEnoughRootsOfUnity.of_dvd L (exponent_cartierDual_dvd M)

/- English proof (translation)
Use `hasEnoughRootsOfUnity_exponent_cartierDual (K := K) (L := L) M` as an intermediate fact. Establish `: Finite (cartierDual K L M)` using `finite_cartierDual K L M`. Establish `: Finite (cartierDual K L (cartierDual K L M))` using `finite_cartierDual K L _`. Rewrite using `[Nat.bijective_iff_injective_and_card, card_cartierDual, card_cartierDual]`. Use `⟨(injective_iff_map_eq_zero _).2 fun m hm => ?_, rfl⟩` and prove the remaining obligations.

Use `eq_zero_of_forall_cartierDual_apply_eq_zero (K := K) (L := L) fun f => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun hm f` as an intermediate fact. Conclude with `this`.
-/
theorem toCartierDualCartierDual_bijective (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    Function.Bijective (toCartierDualCartierDual K L M).hom := by
  have := hasEnoughRootsOfUnity_exponent_cartierDual (K := K) (L := L) M
  have : Finite (cartierDual K L M) := finite_cartierDual K L M
  have : Finite (cartierDual K L (cartierDual K L M)) := finite_cartierDual K L _
  rw [Nat.bijective_iff_injective_and_card, card_cartierDual, card_cartierDual]
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => ?_, rfl⟩
  refine eq_zero_of_forall_cartierDual_apply_eq_zero (K := K) (L := L) fun f => ?_
  have := LinearMap.congr_fun hm f
  exact this

variable (K L) in

def cartierBidualityIso (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    M ≅ cartierDual K L (cartierDual K L M) :=
  Rep.isoOfBijective (toCartierDualCartierDual K L M) (toCartierDualCartierDual_bijective M)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartierBidualityIso_hom (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [Finite M]
    [HasEnoughRootsOfUnity L (AddMonoid.exponent M)] :
    (cartierBidualityIso K L M).hom = toCartierDualCartierDual K L M :=
  rfl

variable (K L) in

def cartierBidualityIsoOfIsSepClosed [IsSepClosed L] (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
    [Finite M] (h : (Nat.card M : K) ≠ 0) : M ≅ cartierDual K L (cartierDual K L M) :=
  have := hasEnoughRootsOfUnity_exponent_of_isSepClosed K (L := L) M h
  cartierBidualityIso K L M

end Biduality

section Exact

attribute [local instance 3000] Submodule.Quotient.module

variable (K L) in

def cartierDualShortComplex (S : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K))) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :=
  ShortComplex.mk (cartierDualMap (K := K) (L := L) S.g) (cartierDualMap S.f) (by
    rw [← cartierDualMap_comp, S.zero]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    let f' : S.X₃ →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f
    refine LinearMap.ext fun a => ?_
    change f' ((0 : S.X₁ ⟶ S.X₃).hom a) = 0
    rw [Rep.zero_hom]
    exact map_zero f')

end Exact

section ZMod

/- English proof (translation)
Take `⟨z⟩` from `x`. Apply `ULift.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `n • z = 0`. Use `AddMonoid.exponent_nsmul_eq_zero z` as an intermediate fact. Rewrite `this` using `[ZMod.exponent]`. Then use the resulting hypothesis.
-/
theorem nsmul_zmodRep_eq_zero (G : Type*) [Monoid G] (n : ℕ) (x : zmodRep.{u} G n) : n • x = 0 := by
  obtain ⟨z⟩ := x
  apply ULift.ext
  change n • z = 0
  have := AddMonoid.exponent_nsmul_eq_zero z
  rwa [ZMod.exponent] at this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AddMonoid.exponent (ULift.{u} (ZMod n)) = n`. Rewrite using `[AddMonoid.exponent_eq_of_addEquiv AddEquiv.ulift, ZMod.exponent]`.
-/
theorem exponent_zmodRep (G : Type*) [Monoid G] (n : ℕ) :
    AddMonoid.exponent (zmodRep.{u} G n) = n := by
  change AddMonoid.exponent (ULift.{u} (ZMod n)) = n
  rw [AddMonoid.exponent_eq_of_addEquiv AddEquiv.ulift, ZMod.exponent]

instance finite_zmodRep (G : Type*) [Monoid G] (n : ℕ) [NeZero n] : Finite (zmodRep.{u} G n) :=
  inferInstanceAs (Finite (ULift.{u} (ZMod n)))

/- English proof (translation)
Apply `ULift.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(k : ZMod n) = k • (1 : ZMod n)`. Rewrite using `[zsmul_one]`.
-/
theorem zmodRep_eq_zsmul (G : Type*) [Monoid G] (n : ℕ) (k : ℤ) :
    (ULift.up (k : ZMod n) : zmodRep.{u} G n) = k • (ULift.up 1 : zmodRep.{u} G n) := by
  apply ULift.ext
  change (k : ZMod n) = k • (1 : ZMod n)
  rw [zsmul_one]

variable (K L) in

def cartierDualZModHom (n : ℕ) : cartierDual K L (zmodRep.{u} Gal(L/K) n) ⟶ galRootsOfUnity.{u} K L n :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (cartierDual K L (zmodRep.{u} Gal(L/K) n))
    (galRootsOfUnity.{u} K L n)).symm
    { toFun := fun f => Additive.ofMul ⟨Additive.toMul (α := Lˣ)
        ((f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (ULift.up 1)),
        (mem_rootsOfUnity _ _).2 (cartierDual_pow_eq_one (nsmul_zmodRep_eq_zero _ n) _ _)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }, fun σ => by
    refine LinearMap.ext fun f => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cartierDualZModHom_hom_apply (n : ℕ)
    (f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    ((Additive.toMul ((cartierDualZModHom K L n).hom f) : rootsOfUnity n L) : Lˣ) =
      Additive.toMul (α := Lˣ) (f (ULift.up 1)) :=
  rfl

/- English proof (translation)
Use `⟨fun f₀ g₀ h => ?_, fun x => ?_⟩` and prove the remaining obligations. Set `f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L` to `f₀`. Set `g : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L` to `g₀`. Establish `h1 : f (ULift.up 1) = g (ULift.up 1)`. Use `congrArg (fun y => ((Additive.toMul y : rootsOfUnity n L) : Lˣ)) h` as an intermediate fact.

Conclude with `Additive.toMul.injective this`. Express the relevant statement in the definitionally equal form `f = g`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨z⟩` from `x`. Rewrite using `[← ZMod.intCast_zmod_cast z, zmodRep_eq_zsmul Gal(L/K) n, map_zsmul, map_zsmul, h1]`.

Set `ζ : Lˣ` to `(Additive.toMul x : rootsOfUnity n L)`. Establish `hζ : ζ ^ n = 1` using `(mem_rootsOfUnity _ _).1 (Additive.toMul x).2`. Set `h₀ : ZMod n →+ Additive Lˣ` to `ZMod.lift n ⟨zmultiplesHom (Additive Lˣ) (Additive.ofMul ζ), by`. Rewrite using `[zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hζ, ofMul_one]⟩`. Use `⟨(uliftIntLinearEquivAddHom (zmodRep.{u} Gal(L/K) n) (galUnits.{u} K L)).symm (h₀.comp (AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom), ?_⟩` and prove the remaining obligations.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Additive.toMul (h₀ 1) = ζ`. Rewrite using `[← Int.cast_one, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul, toMul_ofMul]`.
-/
theorem cartierDualZModHom_bijective (n : ℕ) :
    Function.Bijective (cartierDualZModHom K L n).hom := by
  refine ⟨fun f₀ g₀ h => ?_, fun x => ?_⟩
  · let f : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L := f₀
    let g : zmodRep.{u} Gal(L/K) n →ₗ[ULift.{u} ℤ] galUnits.{u} K L := g₀
    have h1 : f (ULift.up 1) = g (ULift.up 1) := by
      have := congrArg (fun y => ((Additive.toMul y : rootsOfUnity n L) : Lˣ)) h
      exact Additive.toMul.injective this
    change f = g
    refine LinearMap.ext fun x => ?_
    obtain ⟨z⟩ := x
    rw [← ZMod.intCast_zmod_cast z, zmodRep_eq_zsmul Gal(L/K) n, map_zsmul, map_zsmul, h1]
  · let ζ : Lˣ := (Additive.toMul x : rootsOfUnity n L)
    have hζ : ζ ^ n = 1 := (mem_rootsOfUnity _ _).1 (Additive.toMul x).2
    let h₀ : ZMod n →+ Additive Lˣ := ZMod.lift n ⟨zmultiplesHom (Additive Lˣ) (Additive.ofMul ζ),
      by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hζ, ofMul_one]⟩
    refine ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} Gal(L/K) n) (galUnits.{u} K L)).symm
      (h₀.comp (AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change Additive.toMul (h₀ 1) = ζ
    rw [← Int.cast_one, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul, toMul_ofMul]

variable (K L) in

def cartierDualZModIso (n : ℕ) : cartierDual K L (zmodRep.{u} Gal(L/K) n) ≅ galRootsOfUnity.{u} K L n :=
  Rep.isoOfBijective (cartierDualZModHom K L n) (cartierDualZModHom_bijective n)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartierDualZModIso_hom (n : ℕ) : (cartierDualZModIso K L n).hom = cartierDualZModHom K L n :=
  rfl

variable (K L) in

def cartierDualRootsOfUnityIso (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity L n] :
    cartierDual K L (galRootsOfUnity.{u} K L n) ≅ zmodRep.{u} Gal(L/K) n :=
  have : HasEnoughRootsOfUnity L (AddMonoid.exponent (zmodRep.{u} Gal(L/K) n)) := by
    rwa [exponent_zmodRep]
  (cartierDualFunctor K L).mapIso (cartierDualZModIso K L n).op ≪≫
    (cartierBidualityIso K L (zmodRep.{u} Gal(L/K) n)).symm

variable (K L) in

def cartierDualRootsOfUnityIsoOfIsSepClosed [IsSepClosed L] (n : ℕ) (hn : (n : K) ≠ 0) :
    cartierDual K L (galRootsOfUnity.{u} K L n) ≅ zmodRep.{u} Gal(L/K) n :=
  have : NeZero (n : L) := ⟨by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero (algebraMap K L)).2 hn⟩
  have : NeZero n := ⟨fun h => hn (by rw [h, Nat.cast_zero])⟩
  cartierDualRootsOfUnityIso K L n

end ZMod

end GroundTheory.ProfCoh
