import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ValuationUnitNeZero

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Use `set Q := HeightOneSpectrum.equivOfRingEquiv e P with hQdef`. Establish `hQ : Q.asIdeal = P.asIdeal.map e`. Rewrite using `[hQdef, ← Ideal.comap_symm]`. Both sides reduce to the same expression. Establish `key : ∀ n : ℕ, Q.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) ↔ P.intValuation r ≤ WithZero.exp (-(n : ℤ))`.

Introduce `n`. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, hQ, ← Ideal.map_pow, Ideal.apply_mem_of_equiv_iff]`. Distinguish the cases in `hr : r = 0`. Simplify using `[hr]`. Establish `hr' : e r ≠ 0` using `by simpa using hr`.

Take `⟨m, hm⟩ : ∃ m : ℕ, Q.intValuation (e r) = WithZero.exp (-(m : ℤ))` from `⟨_, HeightOneSpectrum.intValuation_if_neg _ hr'⟩`. Take `⟨k, hk⟩ : ∃ k : ℕ, P.intValuation r = WithZero.exp (-(k : ℤ))` from `⟨_, HeightOneSpectrum.intValuation_if_neg _ hr⟩`. Rewrite `key`, the goal using `[hm, hk]`. Establish `h1` using `(key k).2 le_rfl`. Establish `h2` using `(key m).1 le_rfl`.

Rewrite `h1`, `h2` using `[WithZero.exp_le_exp]`. Establish `hmk : m = k` using `by omega`. Rewrite using `[hmk]`.
-/
private theorem intValuation_equivOfRingEquiv_apply {F : Type} [Field F] [NumberField F] (e : 𝓞 F ≃+* 𝓞 F)
    (P : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P with hQdef
  have hQ : Q.asIdeal = P.asIdeal.map e := by
    rw [hQdef, ← Ideal.comap_symm]
    rfl
  have key : ∀ n : ℕ, Q.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hQ, ← Ideal.map_pow, Ideal.apply_mem_of_equiv_iff]
  by_cases hr : r = 0
  · simp [hr]
  have hr' : e r ≠ 0 := by simpa using hr
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Q.intValuation (e r) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr'⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P.intValuation r = WithZero.exp (-(k : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr⟩
  rw [hm, hk] at key ⊢
  have h1 := (key k).2 le_rfl
  have h2 := (key m).1 le_rfl
  rw [WithZero.exp_le_exp] at h1 h2
  have hmk : m = k := by omega
  rw [hmk]

/- English proof (translation)
Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) x`. Establish `ha : σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ a)` using `rfl`. Establish `hb : σ (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ b)` using `rfl`. Rewrite using `[map_div₀, ha, hb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_equivOfRingEquiv_apply, intValuation_equivOfRingEquiv_ap …`.
-/
private theorem valuation_equivOfRingEquiv_mapRingEquiv_apply {F : Type} [Field F] [NumberField F] (σ : F ≃+* F)
    (P : HeightOneSpectrum (𝓞 F)) (x : F) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) P).valuation F (σ x) =
      P.valuation F x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ a) := rfl
  have hb : σ (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ b) := rfl
  rw [map_div₀, ha, hb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_equivOfRingEquiv_apply, intValuation_equivOfRingEquiv_apply]

/- English proof (translation)
Establish `h` using `valuation_equivOfRingEquiv_mapRingEquiv_apply γ.toRingEquiv P ((γ⁻¹ : Gal(F/L)) (α : F))`. Establish `e1 : γ.toRingEquiv ((γ⁻¹ : Gal(F/L)) (α : F)) = α`. Simplify using `[AlgEquiv.aut_inv]`. Rewrite `h` using `[e1]`. Simplify using `only [ordP, actP, actU, Units.coe_map]`.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private theorem ordP_actU_inv_eq_ordP_actP {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (γ : Gal(F/L)) (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)) :
    ordP P (actU γ⁻¹ α) = ordP (actP γ P) α := by
  have h := valuation_equivOfRingEquiv_mapRingEquiv_apply γ.toRingEquiv P ((γ⁻¹ : Gal(F/L)) (α : F))
  have e1 : γ.toRingEquiv ((γ⁻¹ : Gal(F/L)) (α : F)) = α := by
    simp [AlgEquiv.aut_inv]
  rw [e1] at h
  simp only [ordP, actP, actU, Units.coe_map]
  rw [h]
  rfl

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x ∈ P.asIdeal ↔ (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) ∈ P.asIdeal`. Establish `: (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x = (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Rewrite using `[← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, mul_inv_rev, AlgEquiv.mul_apply]`. Rewrite using `[this]`.
-/
private theorem actP_mul_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (σ τ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) : actP (σ * τ) P = actP σ (actP τ P) := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x ∈ P.asIdeal ↔
    (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
        ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, mul_inv_rev, AlgEquiv.mul_apply]
  rw [this]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x ∈ P.asIdeal ↔ x ∈ P.asIdeal`. Establish `: (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x = x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Rewrite using `[← AlgEquiv.aut_inv, inv_one, AlgEquiv.one_apply]`. Rewrite using `[this]`.
-/
private theorem actP_one_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (P : HeightOneSpectrum (𝓞 F)) : actP (1 : Gal(F/L)) P = P := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x ∈ P.asIdeal ↔ x ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x = x := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, inv_one, AlgEquiv.one_apply]
  rw [this]

/- English proof (translation)
Use `ext`. Simplify using `[actU]`.
-/
private theorem actU_mul' {L F : Type} [Field L] [Field F] [Algebra L F]
    (σ τ : Gal(F/L)) (α : Fˣ) : actU (σ * τ) α = actU σ (actU τ α) := by
  ext
  simp [actU]

/- English proof (translation)
Use `ext`. Simplify using `[actU]`.
-/
private theorem actU_one' {L F : Type} [Field L] [Field F] [Algebra L F] (α : Fˣ) :
    actU (1 : Gal(F/L)) α = α := by
  ext
  simp [actU]

/- English proof (translation)
Establish `hα : P.valuation F (α : F) ≠ 0` using `by simp`. Establish `hβ : P.valuation F (β : F) ≠ 0` using `by simp`. Simplify using `only [ordP, Units.val_mul, map_mul]`. Rewrite using `[WithZero.log_mul hα hβ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordP_mul' {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α β : Fˣ) : ordP P (α * β) = ordP P α + ordP P β := by
  have hα : P.valuation F (α : F) ≠ 0 := by simp
  have hβ : P.valuation F (β : F) ≠ 0 := by simp
  simp only [ordP, Units.val_mul, map_mul]
  rw [WithZero.log_mul hα hβ]
  ring

/- English proof (translation)
Establish `hw : P.valuation F (α : F) ≠ 0` using `by simp`. Use `conv_lhs => rw [← WithZero.exp_log hw]`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Simplify using `only [ordP]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem one_lt_valuation_iff_ordP_neg {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α : Fˣ) : 1 < P.valuation F (α : F) ↔ ordP P α < 0 := by
  have hw : P.valuation F (α : F) ≠ 0 := by simp
  conv_lhs => rw [← WithZero.exp_log hw]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [ordP]
  omega

/- English proof (translation)
Use `((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_` and prove the remaining obligations. Introduce `P hP`. Establish `hinv : ordP P α⁻¹ = -ordP P α`. Establish `h` using `ordP_mul' P α α⁻¹`. Establish `h1 : ordP P (1 : Fˣ) = 0` using `by simp [ordP]`.

Rewrite `h` using `[mul_inv_cancel, h1]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Set.mem_setOf_eq] at hP`. Break down `lt_or_gt_of_ne hP with h | h` into its components or cases. Use `left`.

Conclude with `(one_lt_valuation_iff_ordP_neg P α).2 h`. Use `right`. Conclude with `(one_lt_valuation_iff_ordP_neg P α⁻¹).2 (by omega)`.
-/
private theorem finite_setOf_ordP_ne_zero {F : Type} [Field F] [NumberField F] (α : Fˣ) :
    {P : HeightOneSpectrum (𝓞 F) | ordP P α ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_
  intro P hP
  have hinv : ordP P α⁻¹ = -ordP P α := by
    have h := ordP_mul' P α α⁻¹
    have h1 : ordP P (1 : Fˣ) = 0 := by simp [ordP]
    rw [mul_inv_cancel, h1] at h
    omega
  simp only [Set.mem_setOf_eq] at hP
  rcases lt_or_gt_of_ne hP with h | h
  · left
    exact (one_lt_valuation_iff_ordP_neg P α).2 h
  · right
    exact (one_lt_valuation_iff_ordP_neg P α⁻¹).2 (by omega)

/- English proof (translation)
Introduce `L F _ _ _ _ _ γ a ha`. Set `E` to `HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv γ.toRingEquiv)`. Set `g : Module.End ℤ (Additive Fˣ)` to `(MonoidHom.toAdditive (actU γ⁻¹)).toIntLinearMap`. Set `gI : Module.End ℤ (HeightOneSpectrum (𝓞 F) →₀ ℤ)` to `(Finsupp.domLCongr E.symm : (HeightOneSpectrum (𝓞 F) →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap`. Set `dA : Additive Fˣ →+ (HeightOneSpectrum (𝓞 F) →₀ ℤ)` to `{ toFun := fun y => Finsupp.ofSupportFinite (fun P => ordP P (Additive.toMul y)) (finite_setOf_ordP_ne_zero (Additive.toMul y)) map_zero' := by`.

Use extensionality with `P`. Simplify using `[Finsupp.ofSupportFinite_coe, ordP]`. Use the proof step `map_add' := by`. Introduce `y z`. Use extensionality with `P`.

Simplify using `[Finsupp.ofSupportFinite_coe, ordP_mul']`. Use `rfl }`. Establish `hg1 : ∀ α : Fˣ, g (Additive.ofMul α) = Additive.ofMul (actU γ⁻¹ α)` using `fun α => rfl`. Establish `hgI1 : ∀ (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)), (gI 𝔡) P = 𝔡 (actP γ P)`. Introduce `𝔡 P`.

Simplify using `[gI, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]`. Both sides reduce to the same expression. Establish `hd1 : ∀ (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)), (dA.toIntLinearMap (Additive.ofMul α)) P = ordP P α`. Introduce `α P`. Both sides reduce to the same expression.

Establish `hgk : ∀ (k : ℕ) (α : Fˣ), (g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `α`.

Rewrite using `[pow_zero, pow_zero, Module.End.one_apply, actU_one']`. Consider the case `succ k ih`. Introduce `α`. Rewrite using `[pow_succ, Module.End.mul_apply, hg1, ih, pow_succ, actU_mul']`. Establish `hgIk : ∀ (k : ℕ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)), ((gI ^ k) 𝔡) P = 𝔡 (actP (γ ^ k) P)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `𝔡 P`. Rewrite using `[pow_zero, pow_zero, Module.End.one_apply, actP_one_selmer_order_counts]`.

Consider the case `succ k ih`. Introduce `𝔡 P`. Rewrite using `[pow_succ', Module.End.mul_apply, hgI1, ih, pow_succ, actP_mul_selmer_order_counts]`. Establish `hn1 : γ⁻¹ ^ orderOf γ = 1` using `by rw [inv_pow, pow_orderOf_eq_one, inv_one]`. Establish `hn2 : γ ^ orderOf γ = 1` using `pow_orderOf_eq_one γ`.

Use `⟨⟨g, gI, dA.toIntLinearMap, orderOf γ, a, ?_, ?_, ?_, orderOf_pos γ, ha, ?_⟩, ⟨rfl, rfl, hg1, hgI1, hd1⟩⟩` and prove the remaining obligations. Introduce `y`. Use extensionality with `P`. Rewrite using `[hgI1]`. Express the relevant statement in the definitionally equal form `ordP P (actU γ⁻¹ (Additive.toMul y)) = ordP (actP γ P) (Additive.toMul y)`.

Conclude with `ordP_actU_inv_eq_ordP_actP γ (Additive.toMul y) P`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[Module.End.one_apply]`. Establish `h` using `hgk (orderOf γ) (Additive.toMul y)`.

Rewrite `h` using `[hn1, actU_one']`. Conclude with `h`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `𝔡`. Rewrite using `[Module.End.one_apply]`.

Use extensionality with `P`. Rewrite using `[hgIk, hn2, actP_one_selmer_order_counts]`. Introduce `m x hm hx`. Use extensionality with `P`. Establish `h` using `congrArg (fun f => f P) hx`.

Simplify using `only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero] at h`. Break down `h with h | h` into its components or cases. Conclude with `absurd h hm`. Simplify using `using h`.
-/
theorem UpperTheory.V.ZK.Ct.datEx :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ), 2 ≤ a → ∃ D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ), IsDat γ a D := by
  intro L F _ _ _ _ _ γ a ha
  let E := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv γ.toRingEquiv)
  let g : Module.End ℤ (Additive Fˣ) := (MonoidHom.toAdditive (actU γ⁻¹)).toIntLinearMap
  let gI : Module.End ℤ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    (Finsupp.domLCongr E.symm : (HeightOneSpectrum (𝓞 F) →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap
  let dA : Additive Fˣ →+ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    { toFun := fun y => Finsupp.ofSupportFinite (fun P => ordP P (Additive.toMul y))
        (finite_setOf_ordP_ne_zero (Additive.toMul y))
      map_zero' := by
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP]
      map_add' := by
        intro y z
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP_mul']
        rfl }
  have hg1 : ∀ α : Fˣ, g (Additive.ofMul α) = Additive.ofMul (actU γ⁻¹ α) := fun α => rfl
  have hgI1 : ∀ (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      (gI 𝔡) P = 𝔡 (actP γ P) := by
    intro 𝔡 P
    simp [gI, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]
    rfl
  have hd1 : ∀ (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)),
      (dA.toIntLinearMap (Additive.ofMul α)) P = ordP P α := by
    intro α P
    rfl
  have hgk : ∀ (k : ℕ) (α : Fˣ), (g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
    intro k
    induction k with
    | zero =>
      intro α
      rw [pow_zero, pow_zero, Module.End.one_apply, actU_one']
    | succ k ih =>
      intro α
      rw [pow_succ, Module.End.mul_apply, hg1, ih, pow_succ, actU_mul']
  have hgIk : ∀ (k : ℕ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      ((gI ^ k) 𝔡) P = 𝔡 (actP (γ ^ k) P) := by
    intro k
    induction k with
    | zero =>
      intro 𝔡 P
      rw [pow_zero, pow_zero, Module.End.one_apply, actP_one_selmer_order_counts]
    | succ k ih =>
      intro 𝔡 P
      rw [pow_succ', Module.End.mul_apply, hgI1, ih, pow_succ, actP_mul_selmer_order_counts]
  have hn1 : γ⁻¹ ^ orderOf γ = 1 := by rw [inv_pow, pow_orderOf_eq_one, inv_one]
  have hn2 : γ ^ orderOf γ = 1 := pow_orderOf_eq_one γ
  refine ⟨⟨g, gI, dA.toIntLinearMap, orderOf γ, a, ?_, ?_, ?_, orderOf_pos γ, ha, ?_⟩,
    ⟨rfl, rfl, hg1, hgI1, hd1⟩⟩
  · intro y
    ext P
    rw [hgI1]
    change ordP P (actU γ⁻¹ (Additive.toMul y)) = ordP (actP γ P) (Additive.toMul y)
    exact ordP_actU_inv_eq_ordP_actP γ (Additive.toMul y) P
  · apply LinearMap.ext
    intro y
    rw [Module.End.one_apply]
    have h := hgk (orderOf γ) (Additive.toMul y)
    rw [hn1, actU_one'] at h
    exact h
  · apply LinearMap.ext
    intro 𝔡
    rw [Module.End.one_apply]
    ext P
    rw [hgIk, hn2, actP_one_selmer_order_counts]
  · intro m x hm hx
    ext P
    have h := congrArg (fun f => f P) hx
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h hm
    · simpa using h
