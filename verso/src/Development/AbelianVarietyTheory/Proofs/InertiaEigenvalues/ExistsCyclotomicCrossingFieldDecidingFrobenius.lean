import Mathlib
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.ChebCross

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `(hζ.autToPow_spec F f).symm`. Introduce `h`. Rewrite `h` using `[← hζ.autToPow_spec F f]`.

Use `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h` as an intermediate fact. Conclude with `Units.ext (ZMod.val_injective m this)`.
-/
theorem autToPow_eq_iff {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (f : Ω ≃ₐ[F] Ω)
    (j : (ZMod m)ˣ) : hζ.autToPow F f = j ↔ f ζ = ζ ^ (j : ZMod m).val := by
  constructor
  · rintro rfl
    exact (hζ.autToPow_spec F f).symm
  · intro h
    rw [← hζ.autToPow_spec F f] at h
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h
    exact Units.ext (ZMod.val_injective m this)

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L`. Use `haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩`. Use `haveI : CharZero L := (algebraMap L Ω).charZero`. Establish `hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m` using `hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)`.

Establish `h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ`. Rewrite using `[← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]`. Take `⟨u, hu⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1`. Use `⟨u.restrictScalars F, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Conclude with `u.commutes ⟨x, hx⟩`. Rewrite using `[autToPow_eq_iff]`. Conclude with `hu`.
-/
theorem exists_fixing [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero L := (algebraMap L Ω).charZero
  have hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)
  have h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨u, hu⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1
  refine ⟨u.restrictScalars F, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact u.commutes ⟨x, hx⟩
  · rw [autToPow_eq_iff]
    exact hu

/- English proof (translation)
Use `haveI : CharZero Z := (algebraMap Z Ω).charZero`. Establish `hm : 0 < m` using `NeZero.pos m`. Establish `h0 : aeval ζ (cyclotomic m Z) = 0`. Rewrite using `[aeval_def, ← eval_map, map_cyclotomic]`. Conclude with `hζ.isRoot_cyclotomic hm`.

Establish `hint : IsIntegral Z ζ` using `⟨_, cyclotomic.monic m Z, h0⟩`. Establish `hdvd` using `minpoly.dvd Z ζ h0`. Establish `hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset`. Introduce `μ hμ`. Rewrite `hμ` using `[mem_primitiveRoots hm]`.

Take `⟨i, hi, hic, rfl⟩` from `(hζ.isPrimitiveRoot_iff).1 hμ`. Take `⟨u, hu, hj⟩` from `h (ZMod.unitOfCoprime i hic)`. Rewrite `hj` using `[autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi]`. Rewrite using `[Multiset.mem_toFinset, mem_aroots]`. Use `⟨minpoly.ne_zero hint, ?_⟩` and prove the remaining obligations.

Set `v : Ω ≃ₐ[Z] Ω` to `Z.fixingSubgroupEquiv ⟨u, hu⟩`. Establish `hv : v ζ = ζ ^ i` using `hj`. Rewrite using `[← hv, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree`. Rewrite using `[natDegree_cyclotomic, ← hζ.card_primitiveRoots]`.

Use `(Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)` and prove the remaining obligations. Use `(card_roots' _).trans ?_` and prove the remaining obligations. Conclude with `natDegree_map_le`. Use `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg` as an intermediate fact. Rewrite using `[this]`.

Conclude with `minpoly.irreducible hint`.
-/
theorem irreducible_of_onto [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by
  classical
  haveI : CharZero Z := (algebraMap Z Ω).charZero
  have hm : 0 < m := NeZero.pos m
  have h0 : aeval ζ (cyclotomic m Z) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm
  have hint : IsIntegral Z ζ := ⟨_, cyclotomic.monic m Z, h0⟩
  have hdvd := minpoly.dvd Z ζ h0
  have hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset := by
    intro μ hμ
    rw [mem_primitiveRoots hm] at hμ
    obtain ⟨i, hi, hic, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ
    obtain ⟨u, hu, hj⟩ := h (ZMod.unitOfCoprime i hic)
    rw [autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi] at hj
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    let v : Ω ≃ₐ[Z] Ω := Z.fixingSubgroupEquiv ⟨u, hu⟩
    have hv : v ζ = ζ ^ i := hj
    rw [← hv, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree := by
    rw [natDegree_cyclotomic, ← hζ.card_primitiveRoots]
    refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
    refine (card_roots' _).trans ?_
    exact natDegree_map_le
  have := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg
  rw [this]
  exact minpoly.irreducible hint

/- English proof (translation)
Set `ρ` to `AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M`. Establish `hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x` using `fun f x => AlgEquiv.restrictNormal_commutes f M x`. Establish `h1 : ρ σ ∈ Subgroup.zpowers (ρ h)`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)), IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρ]`. Rewrite `hσ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Use `hσ _ ⟨x.2, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce and unpack `f ⟨n, rfl⟩`. Use `hx (ρ (h ^ n)) ⟨n, by simp⟩` as an intermediate fact. Rewrite using `[← hρ, this]`.

Rewrite `h1` using `[← mem_powers_iff_mem_zpowers]`. Take `⟨k, hk⟩` from `h1`. Use `⟨k, fun x hx => ?_⟩` and prove the remaining obligations. Use `hρ σ ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[← hk]`.

Simplify using `only [← map_pow] at this`. Rewrite `this` using `[hρ]`. Conclude with `this.symm`.
-/
theorem exists_pow_eq_on (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by
  let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M
  have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x := fun f x =>
    AlgEquiv.restrictNormal_commutes f M x
  have h1 : ρ σ ∈ Subgroup.zpowers (ρ h) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply Subtype.ext
    rw [hρ]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine hσ _ ⟨x.2, ?_⟩
    change (x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨n, rfl⟩
    have := hx (ρ (h ^ n)) ⟨n, by simp⟩
    rw [← hρ, this]
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, fun x hx => ?_⟩
  have := hρ σ ⟨x, hx⟩
  rw [← hk] at this
  simp only [← map_pow] at this
  rw [hρ] at this
  exact this.symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr`. Use `haveI : Fact m.Prime := ⟨hm⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω m`.

Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := (ZMod m)ˣ)`. Take `⟨u, hu, hu'⟩` from `exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)`. Use `set h := u * g with hh`. Establish `hχ : hζ.autToPow F h = τ` using `by rw [hh, map_mul, hu']; simp`. Use `haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) := hζ.intermediateField_adjoin_isCyclotomicExtension F`.

Use `haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.finiteDimensional {m} F _`. Use `haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _`. Set `M : IntermediateField F Ω` to `L ⊔ IntermediateField.adjoin F {ζ}`. Use `haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _`. Use `haveI : IsGalois F M := { }`.

Establish `hζM : ζ ∈ M` using `(le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)`. Use `⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap (IntermediateField.inclusion_injective inf_le_left)`. Use `irreducible_of_onto _ hζ fun j => ?_` and prove the remaining obligations. Take `⟨n, rfl⟩` from `hτ j`.

Use `⟨h ^ n, ?_, by simp [hχ]⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩`. Introduce `σ hσ hσζ`.

Take `⟨k, hk⟩` from `exists_pow_eq_on M h σ hσ`. Establish `h1 : hζ.autToPow F (h ^ k) = τ`. Rewrite using `[autToPow_eq_iff, ← hk ζ hζM]`. Conclude with `hσζ ζ hζ.pow_eq_one`. Rewrite `h1` using `[map_pow, hχ]`.

Establish `hord : orderOf τ = m - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `hmod : k ≡ 1 [MOD m - 1]`. Rewrite using `[← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]`. Set `ρ` to `AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L`.

Establish `hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x` using `fun f x => AlgEquiv.restrictNormal_commutes f L x`. Establish `h2 : ρ σ = ρ (h ^ k)`. Use extensionality with `x`. Rewrite using `[hρ, hρ]`. Conclude with `hk _ ((le_sup_left : L ≤ M) x.2)`.

Establish `h3 : ρ h ^ k = ρ h` using `by conv_rhs => rw [← pow_one (ρ h)]`. Rewrite using `[pow_eq_pow_iff_modEq]`. Use `hmod.of_dvd (dvd_trans ?_ hdiv)` and prove the remaining obligations. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `orderOf_dvd_natCard _`.

Establish `h4 : ρ u = 1`. Rewrite `hu` using `[← IntermediateField.restrictNormalHom_ker]`. Conclude with `hu`. Rewrite using `[← IntermediateField.restrictNormalHom_ker]`. Express the relevant statement in the definitionally equal form `ρ (σ * g⁻¹) = 1`.

Rewrite using `[map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]`. Simplify using the standard rewrite rules.
-/
theorem cross : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  intro F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod m)ˣ)
  obtain ⟨u, hu, hu'⟩ := exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)
  set h := u * g with hh
  have hχ : hζ.autToPow F h = τ := by rw [hh, map_mul, hu']; simp
  haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} F _
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _
  let M : IntermediateField F Ω := L ⊔ IntermediateField.adjoin F {ζ}
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI : IsGalois F M := { }
  have hζM : ζ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)
  refine ⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  · refine irreducible_of_onto _ hζ fun j => ?_
    obtain ⟨n, rfl⟩ := hτ j
    refine ⟨h ^ n, ?_, by simp [hχ]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩
  · intro σ hσ hσζ
    obtain ⟨k, hk⟩ := exists_pow_eq_on M h σ hσ
    have h1 : hζ.autToPow F (h ^ k) = τ := by
      rw [autToPow_eq_iff, ← hk ζ hζM]
      exact hσζ ζ hζ.pow_eq_one
    rw [map_pow, hχ] at h1
    have hord : orderOf τ = m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmod : k ≡ 1 [MOD m - 1] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]
    let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L
    have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x := fun f x =>
      AlgEquiv.restrictNormal_commutes f L x
    have h2 : ρ σ = ρ (h ^ k) := by
      ext x
      rw [hρ, hρ]
      exact hk _ ((le_sup_left : L ≤ M) x.2)
    have h3 : ρ h ^ k = ρ h := by
      conv_rhs => rw [← pow_one (ρ h)]
      rw [pow_eq_pow_iff_modEq]
      refine hmod.of_dvd (dvd_trans ?_ hdiv)
      rw [← IsGalois.card_aut_eq_finrank]
      exact orderOf_dvd_natCard _
    have h4 : ρ u = 1 := by
      rw [← IntermediateField.restrictNormalHom_ker] at hu
      exact hu
    rw [← IntermediateField.restrictNormalHom_ker]
    change ρ (σ * g⁻¹) = 1
    rw [map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]
    simp

end GlobalTheory.ChebCross
