import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

/- English proof (translation)
Use `haveI := v.isPrime`. Establish `h1` using `Ideal.ramificationIdx_pos v.asIdeal ℤ`. Establish `h2` using `Ideal.inertiaDeg_pos v.asIdeal ℤ`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)`. Rewrite `hsum` using `[NumberField.RingOfIntegers.rank, Module.finrank_self]`.

Establish `hle` using `Finset.single_le_sum (s := Finset.univ) (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) => q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨v.asIdeal, inferInstance, ⟨rfl⟩⟩)`. Rewrite `hle` using `[hsum]`. Conclude with `le_antisymm hle (Nat.mul_pos h1 h2)`.
-/
private theorem ef_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI := v.isPrime
  have h1 := Ideal.ramificationIdx_pos v.asIdeal ℤ
  have h2 := Ideal.inertiaDeg_pos v.asIdeal ℤ
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨v.asIdeal, inferInstance, ⟨rfl⟩⟩)
  rw [hsum] at hle
  exact le_antisymm hle (Nat.mul_pos h1 h2)

/- English proof (translation)
Use `haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective`. Set `T : Module.Dual k M →+ Module.Dual R M` to `{ toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R) map_zero' := by ext; simp map_add' := fun f f' => by ext; simp }`. Establish `hT : ∀ f m, T f m = Algebra.trace R k (f m)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective T`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `f hf`. Use extensionality with `m`. Use `(traceForm_nondegenerate R k).1 (f m) fun a => ?_` and prove the remaining obligations. Use `hT f (a • m)` as an intermediate fact. Rewrite `this` using `[hf, f.map_smul, smul_eq_mul, mul_comm]`.

Conclude with `this.symm`. Use `haveI : Finite (Module.Dual R M) := DFunLike.finite _`. Establish `hbij : Function.Bijective T` using `hinj.bijective_of_nat_card_le (by`. Rewrite using `[Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank])`. Use `Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)` and prove the remaining obligations.

Rewrite using `[Equiv.ofBijective_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hf g x`. Rewrite using `[hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Introduce `hf g x`.

Take `⟨g, rfl⟩` from `e.surjective g`. Establish `: f.comp (ρ (e g)) = (χ (e g) : k) • f` using `hinj (LinearMap.ext fun y => by`. Use `hf g y` as an intermediate fact. Rewrite `this` using `[hT, hT, h]`. Rewrite using `[hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul])`.

Conclude with `LinearMap.congr_fun this x`.
-/
private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (Loc.H0dual χ ρ) = Nat.card (Loc.H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hy g m`. Establish `e` using `congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e`.

Rewrite `e` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `e.symm`. Introduce `hy g`. Use `TDual.ext fun m => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]`.

Use `hy g (ρ g⁻¹ m)` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Conclude with `this.symm`.
-/
private theorem card_twDual {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) :
    Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id Γ))) = Nat.card (Loc.H0dual χ ρ) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    refine TDual.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

/- English proof (translation)
Introduce `hF hT hE0 Ω _ _ _ l _ p hp A hA k _ _ hc M _ _ _ _ _ ρ hρ`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨w, hw, hAw⟩` from `GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) A hA`. Establish `hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal` using `hw`. Establish `hl : l.Prime` using `Fact.out`.

Use `haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩`. Use `haveI : CharP k (l ^ 1) := by rwa [pow_one]`. Use `letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)`. Use `letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)`. Use `haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

Use `haveI : Finite M := Module.finite_of_finite k`. Set `ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F` to `ℚ) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ`. Establish `h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m` using `fun _ _ => rfl`. Establish `hρ' : ContAction ρ'` using `hρ`. Establish `e0 : H0 ρ ≃ H0 ρ'` using `Equiv.subtypeEquivRight fun _ => Iff.rfl`.

Establish `e1 : H1 ρ ≃ H1 ρ'` using `subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`. Establish `e2 : H2 ρ ≃ H2 ρ'` using `subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`. Take `⟨-, f1, f2, -⟩` from `hF ℚ Ω l 1 M A ρ' w one_pos hAw hρ'`. Take `⟨⟨inv⟩, -, -, -, hb⟩` from `hT ℚ Ω l 1 M A ρ' w one_pos hAw hρ'`. Establish `hE` using `hE0 ℚ Ω l 1 M A ρ' w one_pos hAw hρ'`.

Use `haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm`. Use `haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm`. Establish `hk : 1 < Nat.card k` using `Finite.one_lt_card`. Establish `hd : locDeg w = 1` using `ef_eq_one w`. Use `⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩` and prove the remaining obligations.

Apply `Nat.pow_right_injective hk beta_reduce` to reduce the goal to its premises. Rewrite using `[pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]`. Use `split_ifs with hvl`. Substitute `hvl` using the available equality. Establish `h1 : Nat.card (H1 ρ') = Nat.card (H0 ρ') * Nat.card (H2 ρ') * Nat.card M ^ locDeg w` using `hE.1 hw`.

Rewrite `h1` using `[hd, pow_one (Nat.card M)]`. Rewrite using `[← Module.natCard_eq_pow_finrank]`. Conclude with `h1`. Rewrite using `[pow_zero, mul_one]`. Use `hE.2 fun hlw => w.isPrime.ne_top ?_` and prove the remaining obligations.

Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hvl)).map (Int.castRingHom (𝓞 ℚ))`. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw)) (w.asIdeal.mul_mem_left _ (by simpa using hlw))`. Apply `Nat.pow_right_injective hk beta_reduce` to reduce the goal to its premises. Set `χ` to `(cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype`.

Use `haveI : Finite (Module.Dual k M) := DFunLike.finite _`. Use `haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))`. Set `B : Type` to `H0 ((twDual χ ρ').comp (MonoidHom.id _))`. Set `E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B` to `(Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv`. Use `haveI : Finite B := Subtype.finite`.

Use `haveI := hc`. Establish `hχ : ∀ g, ((((cycK Ω l k).comp (Dec (F` using `ℚ) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) = algebraMap (ZMod (l ^ 1)) k (χ g) := fun g => RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k) (algebraMap (ZMod (l ^ 1)) k)) _`. Rewrite using `[← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2, card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ, ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]`.
-/
theorem UpperTheory.V.X.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := ℚ) A) M), ContAction ρ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + (if p = l then finrank k M else 0) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) ρ) := by
  intro hF hT hE0 Ω _ _ _ l _ p hp A hA k _ _ hc M _ _ _ _ _ ρ hρ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) A hA
  have hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := hw
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := ℚ) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨-, f1, f2, -⟩ := hF ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hT ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hE0 ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hd : locDeg w = 1 := ef_eq_one w
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    split_ifs with hvl
    · subst hvl
      have h1 : Nat.card (H1 ρ') = Nat.card (H0 ρ') * Nat.card (H2 ρ') * Nat.card M ^ locDeg w := hE.1 hw
      rw [hd, pow_one (Nat.card M)] at h1
      rw [← Module.natCard_eq_pow_finrank]
      exact h1
    · rw [pow_zero, mul_one]
      refine hE.2 fun hlw => w.isPrime.ne_top ?_
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hvl)).map
        (Int.castRingHom (𝓞 ℚ))
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw))
        (w.asIdeal.mul_mem_left _ (by simpa using hlw))
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    haveI := hc
    have hχ : ∀ g, ((((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) =
        algebraMap (ZMod (l ^ 1)) k (χ g) := fun g =>
      RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
        (algebraMap (ZMod (l ^ 1)) k)) _
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ,
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
