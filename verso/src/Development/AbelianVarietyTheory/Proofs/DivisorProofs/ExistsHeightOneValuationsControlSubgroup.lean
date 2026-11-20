import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HtVal

/- English proof (translation)
Set `v0 : IsDedekindDomain.HeightOneSpectrum S` to `⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩`. Use `⟨(WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹, fun x => ?_⟩` and prove the remaining obligations. Establish `key : 0 ≤ Multiplicative.toAdd ((WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹ x) ↔ v0.valuation K x ≤ 1`. Simplify using `only [MonoidHom.inv_apply, MonoidHom.comp_apply, toAdd_inv, Left.nonneg_neg_iff]`. Generalize the expression as in `hu : WithZero.unitsWithZeroEquiv.toMonoidHom ((Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom) x) = u`.

Establish `hc : v0.valuation K x = (u : WithZero (Multiplicative ℤ))`. Rewrite using `[← hu, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, WithZero.coe_unitsWithZeroEquiv_eq_units_val]`. Both sides reduce to the same expression. Rewrite using `[hc, ← WithZero.coe_one (α := Multiplicative ℤ), WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_` and prove the remaining obligations. Establish `: v = v0` using `by ext1`. Conclude with `IsLocalRing.eq_maximalIdeal v.isMaximal`.

Rewrite using `[this]`. Conclude with `h`. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `v0.valuation_le_one y`.
-/
theorem dvr_val (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (K : Type) [Field K]
    [Algebra S K] [IsFractionRing S K] :
    ∃ w : Kˣ →* Multiplicative ℤ, ∀ x : Kˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔ (x : K) ∈ (algebraMap S K).range := by
  let v0 : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  refine ⟨(WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹, fun x => ?_⟩
  have key : 0 ≤ Multiplicative.toAdd ((WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹ x) ↔ v0.valuation K x ≤ 1 := by
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, toAdd_inv, Left.nonneg_neg_iff]
    generalize hu : WithZero.unitsWithZeroEquiv.toMonoidHom
      ((Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom) x) = u
    have hc : v0.valuation K x = (u : WithZero (Multiplicative ℤ)) := by
      rw [← hu, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
      rfl
    rw [hc, ← WithZero.coe_one (α := Multiplicative ℤ), WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]
  rw [key]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_
    have : v = v0 := by
      ext1
      exact IsLocalRing.eq_maximalIdeal v.isMaximal
    rw [this]; exact h
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact v0.valuation_le_one y

/- English proof (translation)
Use `haveI : IsDiscreteValuationRing (Localization.AtPrime P) := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1`. Take `⟨w, hw⟩` from `dvr_val (Localization.AtPrime P) (FractionRing R)`. Use `⟨w, fun x => (hw x).trans ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj P.primeCompl y`.

Use `⟨s, s.2, r, ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) hrs` as an intermediate fact. Simplify using `only [map_mul, ← IsScalarTower.algebraMap_apply] at this`. Rewrite using `[← this, hy, mul_comm]`. Introduce and unpack `⟨s, hs, r, hr⟩`.

Use `⟨IsLocalization.mk' (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl), ?_⟩` and prove the remaining obligations. Establish `hs0 : algebraMap R (FractionRing R) s ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]`. Introduce and unpack `rfl`. Conclude with `hs P.zero_mem`.

Apply `mul_left_cancel₀ hs0` to reduce the goal to its premises. Rewrite using `[← hr, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) s, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r, ← map_mul]`. Use `congr 1`. Rewrite using `[mul_comm]`. Conclude with `IsLocalization.mk'_spec (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl)`.
-/
theorem exists_val (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (h1 : P.height = 1) :
    ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔
        ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
  obtain ⟨w, hw⟩ := dvr_val (Localization.AtPrime P) (FractionRing R)
  refine ⟨w, fun x => (hw x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨s, s.2, r, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) hrs
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at this
    rw [← this, hy, mul_comm]
  · rintro ⟨s, hs, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl), ?_⟩
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
      rintro rfl; exact hs P.zero_mem
    apply mul_left_cancel₀ hs0
    rw [← hr, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) s,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r, ← map_mul]
    congr 1
    rw [mul_comm]
    exact IsLocalization.mk'_spec (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl)

/- English proof (translation)
Establish `h1 : (1 : R) ∉ P` using `fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hp : 0 ≤ Multiplicative.toAdd (w u)` using `(hw u).2 ⟨1, h1, a, by rw [map_one, one_mul, ha]⟩`. Establish `hn : 0 ≤ Multiplicative.toAdd (w u⁻¹)` using `(hw u⁻¹).2 ⟨a, haP, 1, by`. Rewrite using `[map_one, ← ha, Units.mul_inv]⟩`. Rewrite `hn` using `[map_inv, toAdd_inv]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem val_eq_zero_of_notMem (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsPrime]
    (w : (FractionRing R)ˣ →* Multiplicative ℤ)
    (hw : ∀ x : (FractionRing R)ˣ, 0 ≤ Multiplicative.toAdd (w x) ↔
      ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range)
    (u : (FractionRing R)ˣ) (a : R) (ha : (u : FractionRing R) = algebraMap R _ a) (haP : a ∉ P) :
    Multiplicative.toAdd (w u) = 0 := by
  have h1 : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hp : 0 ≤ Multiplicative.toAdd (w u) := (hw u).2 ⟨1, h1, a, by rw [map_one, one_mul, ha]⟩
  have hn : 0 ≤ Multiplicative.toAdd (w u⁻¹) := (hw u⁻¹).2 ⟨a, haP, 1, by
    rw [map_one, ← ha, Units.mul_inv]⟩
  rw [map_inv, toAdd_inv] at hn
  omega

/- English proof (translation)
Introduce `R _ _ _ _ J _ g`. Use `haveI := Fintype.ofFinite J`. Establish `key : ∀ P : Ideal R, P.IsPrime → P.height = 1 → ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ, 0 ≤ Multiplicative.toAdd (w x) ↔ ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range` using `fun P _ h1 => exists_val R P h1`. Use `choose W hW using key`. Establish `hsurj` using `fun j => IsLocalization.surj (nonZeroDivisors R) (g j : FractionRing R)`.

Use `choose nd hnd using hsurj`. Establish `hinj` using `IsFractionRing.injective R (FractionRing R)`. Establish `hd0 : ∀ j, ((nd j).2 : R) ≠ 0` using `fun j => nonZeroDivisors.coe_ne_zero _`. Establish `hn0 : ∀ j, (nd j).1 ≠ 0`. Introduce `j h`.

Use `hnd j` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `(mul_ne_zero (g j).ne_zero ((map_ne_zero_iff _ hinj).2 (hd0 j))) this`. Establish `hc0 : (∏ j, (nd j).1 * ((nd j).2 : R)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hn0 j) (hd0 j)`. Establish `hfin` using `ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one hc0`.

Set `T` to `hfin.toFinset`. Set `e` to `T.equivFin.symm`. Establish `hmemT : ∀ i : Fin T.card, (e i : Ideal R).IsPrime ∧ (e i : Ideal R).height = 1 ∧ (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ (e i : Ideal R)` using `fun i => hfin.mem_toFinset.1 (e i).2`. Use `⟨T.card, fun i => W (e i) (hmemT i).1 (hmemT i).2.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `i x r hx`.

Use `(hW _ _ _ x).2 ⟨1, fun h => (hmemT i).1.ne_top ((Ideal.eq_top_iff_one _).2 h), r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_mul, hx]`. Introduce `x hx hv`. Use `(fun h => ⟨h.choose, h.choose_spec.symm⟩) (ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (x : FractionRing R) ?_)` and prove the remaining obligations. Introduce `P hP h1`.

Distinguish the cases in `hcP : (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ P`. Take `⟨i, hi⟩` from `e.surjective ⟨P, hfin.mem_toFinset.2 ⟨hP, h1, hcP⟩⟩`. Establish `gen : ∀ (Q : Ideal R) (hQ : Q.IsPrime) (hQ1 : Q.height = 1), Q = P → 0 ≤ Multiplicative.toAdd (W Q hQ hQ1 x) → ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range`. Introduce and unpack `Q hQ hQ1 rfl h`. Conclude with `(hW Q hQ hQ1 x).1 h`.

Conclude with `gen _ _ _ (congrArg Subtype.val hi) (hv i)`. Establish `hnP : ∀ j, (nd j).1 ∉ P ∧ ((nd j).2 : R) ∉ P`. Introduce `j`. Take `⟨k, hk⟩ : (nd j).1 * ((nd j).2 : R) ∣ ∏ j, (nd j).1 * ((nd j).2 : R)` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ j)`. Use `⟨fun h => hcP ?_, fun h => hcP ?_⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Conclude with `P.mul_mem_right k (P.mul_mem_right _ h)`. Rewrite using `[hk]`. Conclude with `P.mul_mem_right k (P.mul_mem_left _ h)`. Establish `hker : Subgroup.closure (Set.range g) ≤ (W P hP h1).ker`.

Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Set `un : (FractionRing R)ˣ` to `Units.mk0 (algebraMap R _ (nd j).1) ((map_ne_zero_iff _ hinj).2 (hn0 j))`. Set `ud : (FractionRing R)ˣ` to `Units.mk0 (algebraMap R _ ((nd j).2 : R)) ((map_ne_zero_iff _ hinj).2 (hd0 j))`. Establish `hgu : g j = un * ud⁻¹`.

Rewrite using `[eq_mul_inv_iff_mul_eq]`. Conclude with `Units.ext (hnd j)`. Establish `hn` using `val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) un _ rfl (hnP j).1`. Establish `hd` using `val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) ud _ rfl (hnP j).2`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, hgu, map_mul, map_inv]`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[toAdd_mul, toAdd_inv, hn, hd, toAdd_one]`. Simplify using the standard rewrite rules. Establish `h0 : W P hP h1 x = 1` using `hker hx`. Conclude with `(hW P hP h1 x).1 (by rw [h0, toAdd_one])`.
-/
theorem exists_vals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  intro R _ _ _ _ J _ g
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
        0 ≤ Multiplicative.toAdd (w x) ↔
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range :=
    fun P _ h1 => exists_val R P h1
  choose W hW using key
  have hsurj := fun j => IsLocalization.surj (nonZeroDivisors R) (g j : FractionRing R)
  choose nd hnd using hsurj
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hd0 : ∀ j, ((nd j).2 : R) ≠ 0 := fun j => nonZeroDivisors.coe_ne_zero _
  have hn0 : ∀ j, (nd j).1 ≠ 0 := by
    intro j h
    have := hnd j
    rw [h, map_zero] at this
    exact (mul_ne_zero (g j).ne_zero ((map_ne_zero_iff _ hinj).2 (hd0 j))) this
  have hc0 : (∏ j, (nd j).1 * ((nd j).2 : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hn0 j) (hd0 j)
  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one hc0
  let T := hfin.toFinset
  let e := T.equivFin.symm
  have hmemT : ∀ i : Fin T.card, (e i : Ideal R).IsPrime ∧ (e i : Ideal R).height = 1 ∧
      (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ (e i : Ideal R) := fun i => hfin.mem_toFinset.1 (e i).2
  refine ⟨T.card, fun i => W (e i) (hmemT i).1 (hmemT i).2.1, ?_, ?_⟩
  · intro i x r hx
    refine (hW _ _ _ x).2 ⟨1, fun h => (hmemT i).1.ne_top ((Ideal.eq_top_iff_one _).2 h), r, ?_⟩
    rw [map_one, one_mul, hx]
  · intro x hx hv
    refine (fun h => ⟨h.choose, h.choose_spec.symm⟩)
      (ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (x : FractionRing R) ?_)
    intro P hP h1
    by_cases hcP : (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ P
    · obtain ⟨i, hi⟩ := e.surjective ⟨P, hfin.mem_toFinset.2 ⟨hP, h1, hcP⟩⟩
      have gen : ∀ (Q : Ideal R) (hQ : Q.IsPrime) (hQ1 : Q.height = 1), Q = P →
          0 ≤ Multiplicative.toAdd (W Q hQ hQ1 x) →
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
        rintro Q hQ hQ1 rfl h
        exact (hW Q hQ hQ1 x).1 h
      exact gen _ _ _ (congrArg Subtype.val hi) (hv i)
    · have hnP : ∀ j, (nd j).1 ∉ P ∧ ((nd j).2 : R) ∉ P := by
        intro j
        obtain ⟨k, hk⟩ : (nd j).1 * ((nd j).2 : R) ∣ ∏ j, (nd j).1 * ((nd j).2 : R) :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        refine ⟨fun h => hcP ?_, fun h => hcP ?_⟩
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_right _ h)
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_left _ h)
      have hker : Subgroup.closure (Set.range g) ≤ (W P hP h1).ker := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        let un : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ (nd j).1) ((map_ne_zero_iff _ hinj).2 (hn0 j))
        let ud : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ ((nd j).2 : R)) ((map_ne_zero_iff _ hinj).2 (hd0 j))
        have hgu : g j = un * ud⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact Units.ext (hnd j)
        have hn := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) un _ rfl (hnP j).1
        have hd := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) ud _ rfl (hnP j).2
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hgu, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hn, hd, toAdd_one]
        simp
      have h0 : W P hP h1 x = 1 := hker hx
      exact (hW P hP h1 x).1 (by rw [h0, toAdd_one])

end GlobalTheory.HtVal
