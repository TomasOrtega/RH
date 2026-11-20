import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance`. Use `haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩`. Conclude with `cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ (by rwa [pow_one])`.
-/
private theorem apply_eq_pow_cycMod_of_pow_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ ^ ((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  exact cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ
    (by rwa [pow_one])

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance`. Use `haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩`. Use `haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩`. Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω l`. Use `set K := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hK`. Use `haveI : IsCyclotomicExtension {l} ℚ K := by`. Use `hζ.intermediateField_adjoin_isCyclotomicExtension ℚ` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.

Conclude with `Subsingleton.elim _ _`. Use `haveI : NumberField K := IsCyclotomicExtension.numberField {l} ℚ K`. Use `haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)`. Set `σ` to `(IsCyclotomicExtension.Rat.galEquivZMod l K).symm u`. Set `ζK : K` to `⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩`.

Establish `hζK : ζK ^ l = 1` using `Subtype.ext (by simpa using hζ.pow_eq_one)`. Use `⟨σ.liftNormal Ω, ?_⟩` and prove the remaining obligations. Establish `h1 : (σ.liftNormal Ω) ζ = ζ ^ (u : ZMod l).val`. Establish `h2` using `σ.liftNormal_commutes Ω ζK`. Rewrite `h2` using `[IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq l K σ hζK, show IsCyclotomicExtension.Rat.galEquivZMod l K σ = u from MulEquiv.apply_symm_apply _ u]`.

Simplify `h2` using `[ζK]`. Establish `h3` using `apply_eq_pow_cycMod_of_pow_eq_one l Ω (σ.liftNormal Ω) ζ hζ.pow_eq_one`. Rewrite `h3` using `[h1]`. Establish `hc : (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1)).val < l`. Simplify `ZMod.val_lt (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1))` using `[pow_one]`.

Establish `h4` using `hζ.pow_inj (ZMod.val_lt (u : ZMod l)) hc h3`. Unfold `cyc1`. Rewrite using `[← h4, ZMod.natCast_zmod_val]`.
-/
private theorem cyc1_surjective (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (u : (ZMod l)ˣ) : ∃ s : G ℚ Ω, cyc1 l s = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  set K := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hK
  haveI : IsCyclotomicExtension {l} ℚ K := by
    convert hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    · rfl
    · exact Subsingleton.elim _ _
  haveI : NumberField K := IsCyclotomicExtension.numberField {l} ℚ K
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod l K).symm u
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζK : ζK ^ l = 1 := Subtype.ext (by simpa using hζ.pow_eq_one)
  refine ⟨σ.liftNormal Ω, ?_⟩
  have h1 : (σ.liftNormal Ω) ζ = ζ ^ (u : ZMod l).val := by
    have h2 := σ.liftNormal_commutes Ω ζK
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq l K σ hζK,
      show IsCyclotomicExtension.Rat.galEquivZMod l K σ = u from MulEquiv.apply_symm_apply _ u] at h2
    simpa [ζK] using h2
  have h3 := apply_eq_pow_cycMod_of_pow_eq_one l Ω (σ.liftNormal Ω) ζ hζ.pow_eq_one
  rw [h1] at h3
  have hc : (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1)).val < l := by
    simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1))
  have h4 := hζ.pow_inj (ZMod.val_lt (u : ZMod l)) hc h3
  unfold cyc1
  rw [← h4, ZMod.natCast_zmod_val]

/- English proof (translation)
Introduce `l _ Ω _ _ _ ι χ hχ`. Establish `key : ∀ s t : G ℚ Ω, cyc1 l s = cyc1 l t → χ s = χ t`. Introduce `s t hst`. Establish `hv : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val = (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val`. Establish `h1` using `congrArg ZMod.val hst`.

Unfold `cyc1 at h1`. Establish `hs : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val < l`. Simplify `ZMod.val_lt (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))` using `[pow_one]`. Establish `ht : (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val < l`. Simplify `ZMod.val_lt (cycMod ℚ Ω l 1 t : ZMod (l ^ 1))` using `[pow_one]`.

Rewrite `h1` using `[ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht]`. Conclude with `h1`. Establish `hfix : ∀ ζ : Ω, ζ ^ l = 1 → (t⁻¹ * s) ζ = ζ`. Introduce `ζ hζ`. Rewrite using `[AlgEquiv.mul_apply, apply_eq_pow_cycMod_of_pow_eq_one l Ω s ζ hζ, hv, ← apply_eq_pow_cycMod_of_pow_eq_one l Ω t ζ hζ]`.

Conclude with `t.symm_apply_apply ζ`. Establish `h1` using `hχ (t⁻¹ * s) hfix`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1.symm`. Establish `hd : l ∣ l ^ 1` using `by rw [pow_one]`.

Establish `hcast : ∀ s : G ℚ Ω, cyc1 l s = ZMod.cast (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))`. Introduce `s`. Unfold `cyc1`. Rewrite using `[ZMod.cast_eq_val]`. Establish `hone : cyc1 l (1 : G ℚ Ω) = 1`.

Rewrite using `[hcast, map_one, Units.val_one, ZMod.cast_one hd]`. Establish `hmul : ∀ s t : G ℚ Ω, cyc1 l (s * t) = cyc1 l s * cyc1 l t`. Introduce `s t`. Rewrite using `[hcast, hcast, hcast, map_mul, Units.val_mul, ZMod.cast_mul hd]`. Set `sec : (ZMod l)ˣ → G ℚ Ω` to `fun u => (cyc1_surjective l Ω u).choose`.

Establish `hsec : ∀ u, cyc1 l (sec u) = u` using `fun u => (cyc1_surjective l Ω u).choose_spec`. Set `f : (ZMod l)ˣ →* ℂˣ` to `{ toFun := fun u => Units.map ι.toMonoidHom (χ (sec u)) map_one' := by`. Rewrite using `[key (sec 1) 1 (by rw [hsec, hone, Units.val_one]), map_one, map_one]`. Use the proof step `map_mul' := by`. Introduce `u v`.

Rewrite using `[key (sec (u * v)) (sec u * sec v) (by rw [hsec, hmul, hsec, hsec, Units.val_mul]), map_mul, map_mul] }`. Use `⟨MulChar.ofUnitHom f, fun s => ?_⟩` and prove the remaining obligations. Set `w : (ZMod l)ˣ` to `Units.map (ZMod.castHom hd (ZMod l)).toMonoidHom (cycMod ℚ Ω l 1 s)`. Establish `hw : (w : ZMod l) = cyc1 l s`. Rewrite using `[hcast]`.

Both sides reduce to the same expression. Rewrite using `[← hw, MulChar.ofUnitHom_coe]`. Use `show (χ s : Formalism.ConjugateSelfDual.Qbar l) = ι.symm (ι (χ (sec w) : Formalism.ConjugateSelfDual.Qbar l))`. Rewrite using `[RingEquiv.symm_apply_apply, key s (sec w) (by rw [hsec, hw])]`.
-/
theorem UpperTheory.V.Z.Kato.Joint.psiEx :
    UpperTheory.V.Z.Kato.Joint.PsiEx := by
  intro l _ Ω _ _ _ ι χ hχ
  have key : ∀ s t : G ℚ Ω, cyc1 l s = cyc1 l t → χ s = χ t := by
    intro s t hst
    have hv : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val = (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val := by
      have h1 := congrArg ZMod.val hst
      unfold cyc1 at h1
      have hs : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))
      have ht : (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 t : ZMod (l ^ 1))
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h1
      exact h1
    have hfix : ∀ ζ : Ω, ζ ^ l = 1 → (t⁻¹ * s) ζ = ζ := by
      intro ζ hζ
      rw [AlgEquiv.mul_apply, apply_eq_pow_cycMod_of_pow_eq_one l Ω s ζ hζ, hv, ← apply_eq_pow_cycMod_of_pow_eq_one l Ω t ζ hζ]
      exact t.symm_apply_apply ζ
    have h1 := hχ (t⁻¹ * s) hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hd : l ∣ l ^ 1 := by rw [pow_one]
  have hcast : ∀ s : G ℚ Ω, cyc1 l s = ZMod.cast (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)) := by
    intro s
    unfold cyc1
    rw [ZMod.cast_eq_val]
  have hone : cyc1 l (1 : G ℚ Ω) = 1 := by
    rw [hcast, map_one, Units.val_one, ZMod.cast_one hd]
  have hmul : ∀ s t : G ℚ Ω, cyc1 l (s * t) = cyc1 l s * cyc1 l t := by
    intro s t
    rw [hcast, hcast, hcast, map_mul, Units.val_mul, ZMod.cast_mul hd]
  let sec : (ZMod l)ˣ → G ℚ Ω := fun u => (cyc1_surjective l Ω u).choose
  have hsec : ∀ u, cyc1 l (sec u) = u := fun u => (cyc1_surjective l Ω u).choose_spec
  let f : (ZMod l)ˣ →* ℂˣ :=
    { toFun := fun u => Units.map ι.toMonoidHom (χ (sec u))
      map_one' := by
        rw [key (sec 1) 1 (by rw [hsec, hone, Units.val_one]), map_one, map_one]
      map_mul' := by
        intro u v
        rw [key (sec (u * v)) (sec u * sec v) (by rw [hsec, hmul, hsec, hsec, Units.val_mul]),
          map_mul, map_mul] }
  refine ⟨MulChar.ofUnitHom f, fun s => ?_⟩
  let w : (ZMod l)ˣ := Units.map (ZMod.castHom hd (ZMod l)).toMonoidHom (cycMod ℚ Ω l 1 s)
  have hw : (w : ZMod l) = cyc1 l s := by
    rw [hcast]
    rfl
  rw [← hw, MulChar.ofUnitHom_coe]
  show (χ s : Formalism.ConjugateSelfDual.Qbar l) = ι.symm (ι (χ (sec w) : Formalism.ConjugateSelfDual.Qbar l))
  rw [RingEquiv.symm_apply_apply, key s (sec w) (by rw [hsec, hw])]
