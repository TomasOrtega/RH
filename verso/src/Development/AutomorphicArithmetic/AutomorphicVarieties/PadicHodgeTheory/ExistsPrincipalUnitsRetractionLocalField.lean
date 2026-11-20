import GroundTheory.LocalFields.PrincipalUnitsRank

open GroundTheory.LocalField ValuativeRel Module Topology

/- English proof (translation)
Set `r : G →* U` to `{ toFun := fun y => s ⟨u y ^ m, hm y⟩ map_one' := by`. Establish `h : (⟨u 1 ^ m, hm 1⟩ : U) = 1` using `by ext; simp`. Rewrite using `[h, map_one]`. Use the proof step `map_mul' := by`. Introduce `x y`.

Establish `h : (⟨u (x * y) ^ m, hm (x * y)⟩ : U) = ⟨u x ^ m, hm x⟩ * ⟨u y ^ m, hm y⟩` using `by ext; simp [mul_pow]`. Rewrite using `[h, map_mul] }`. Establish `hr : ∀ y, r y = s ⟨u y ^ m, hm y⟩` using `fun y => rfl`. Establish `hfixr : ∀ x : U, r x = x`. Introduce `x`.

Establish `h : (⟨u x ^ m, hm x⟩ : U) = x ^ m` using `by ext; simp [hfix x x.2]`. Rewrite using `[hr, h, map_pow, hs]`. Use `⟨r, ?_, hfixr, ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_induced_rng]`. Set `f : G →* G` to `U.subtype.comp r`.

Establish `hf : ∀ y, f y = (r y : G)` using `fun y => rfl`. Establish `hc : Continuous f`. Apply `continuous_of_continuousAt_one f` to reduce the goal to its premises. Apply `continuousAt_id.congr` to reduce the goal to its premises. Use `filter_upwards [hU.mem_nhds U.one_mem] with x hx`.

Rewrite using `[hf, show x = ((⟨x, hx⟩ : U) : G) from rfl, hfixr]`. Both sides reduce to the same expression. Conclude with `hc`. Introduce `y`. Rewrite using `[hr, ← Subgroup.coe_pow, hs]`.
-/
private theorem UpperTheory.exists_continuous_retraction_power {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (u : G →* G) (m : ℕ)
    (hfix : ∀ x ∈ U, u x = x) (hm : ∀ y, u y ^ m ∈ U) (s : U →* U) (hs : ∀ x, s x ^ m = x) :
    ∃ r : G →* U, Continuous r ∧ (∀ x : U, r x = x) ∧ ∀ y, (r y : G) ^ m = u y ^ m := by
  let r : G →* U :=
    { toFun := fun y => s ⟨u y ^ m, hm y⟩
      map_one' := by
        have h : (⟨u 1 ^ m, hm 1⟩ : U) = 1 := by ext; simp
        rw [h, map_one]
      map_mul' := by
        intro x y
        have h : (⟨u (x * y) ^ m, hm (x * y)⟩ : U) = ⟨u x ^ m, hm x⟩ * ⟨u y ^ m, hm y⟩ := by
          ext; simp [mul_pow]
        rw [h, map_mul] }
  have hr : ∀ y, r y = s ⟨u y ^ m, hm y⟩ := fun y => rfl
  have hfixr : ∀ x : U, r x = x := by
    intro x
    have h : (⟨u x ^ m, hm x⟩ : U) = x ^ m := by ext; simp [hfix x x.2]
    rw [hr, h, map_pow, hs]
  refine ⟨r, ?_, hfixr, ?_⟩
  · rw [continuous_induced_rng]
    let f : G →* G := U.subtype.comp r
    have hf : ∀ y, f y = (r y : G) := fun y => rfl
    have hc : Continuous f := by
      apply continuous_of_continuousAt_one f
      apply continuousAt_id.congr
      filter_upwards [hU.mem_nhds U.one_mem] with x hx
      rw [hf, show x = ((⟨x, hx⟩ : U) : G) from rfl, hfixr]
      rfl
    exact hc
  · intro y
    rw [hr, ← Subgroup.coe_pow, hs]

/- English proof (translation)
Introduce `K _ _ _ _ l _ _`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]`. Use `haveI : Fintype 𝓀[K] := Fintype.ofFinite _`. Establish `hq : l ∣ Nat.card 𝓀[K]`.

Rewrite using `[← CharP.cast_eq_zero_iff 𝓀[K] l, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.cast_card_eq_zero 𝓀[K]`. Establish `hq1 : 1 ≤ Nat.card 𝓀[K]` using `Nat.card_pos`. Establish `hcop : Nat.Coprime (Nat.card 𝓀[K] - 1) l`. Rewrite using `[Nat.coprime_comm, hl.coprime_iff_not_dvd]`.

Introduce `h`. Establish `h2` using `Nat.dvd_sub hq h`. Rewrite `h2` using `[show Nat.card 𝓀[K] - (Nat.card 𝓀[K] - 1) = 1 by omega]`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp h2)`. Establish `bez : ∀ {M : Type} [CommGroup M] (t : M) (a b : ℕ), Nat.Coprime a b → ∃ A B : ℤ, t = (t ^ a) ^ A * (t ^ b) ^ B`.

Introduce `M _ t a b h`. Use `⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩` and prove the remaining obligations. Establish `h' : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1`. Rewrite using `[← Nat.gcd_eq_gcd_ab, h, Nat.cast_one]`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, h', zpow_one]`.

Establish `hidx : ∀ v : (𝒪[K])ˣ, v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1`. Introduce `v`. Rewrite using `[← index_unitFiltration_one]`. Conclude with `Subgroup.pow_index_mem _ v`. Establish `hdecomp : ∀ y : Kˣ, y = uniformizerUnit hϖ ^ ord (y : K) * unitsIncl K ((unitsEquivIntProd hϖ) y).2`.

Introduce `y`. Apply `(unitsEquivIntProd hϖ).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]`. Use `ext`. Simplify using `[unitsEquivIntProd_fst, ← ofAdd_zsmul]`.

Simplify using the standard rewrite rules. Establish `hinj : ∀ w : (𝒪[K])ˣ, unitsIncl K w = 1 → w = 1`. Introduce `w hw`. Establish `h` using `congrArg (fun z => ((unitsEquivIntProd hϖ) z).2) hw`. Simplify `h` using `[unitsEquivIntProd_unitsIncl]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨k, hk⟩` from `CommGroup.mem_primaryComponent.mp hy`. Establish `hord : ord (y : K) = 0`. Establish `h` using `congrArg (fun z => ((unitsEquivIntProd hϖ) z).1) hk`.

Simplify using `only [map_pow, Prod.pow_fst, map_one, Prod.fst_one, unitsEquivIntProd_fst] at h`. Rewrite `h` using `[← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `absurd h (by exact_mod_cast pow_ne_zero k hl.ne_zero)`. Conclude with `h`.

Use `set v := ((unitsEquivIntProd hϖ) y).2 with hvdef`. Establish `hyv : y = unitsIncl K v` using `by conv_lhs => rw [hdecomp y]`. Rewrite using `[hord, zpow_zero, one_mul]`. Establish `hvk : v ^ l ^ k = 1`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_pow, ← hyv, hk]`. Take `⟨A, B, hAB⟩` from `bez v (Nat.card 𝓀[K] - 1) (l ^ k) (Nat.Coprime.pow_right k hcop)`. Establish `hv : v ∈ unitFiltration K 1`. Rewrite using `[hAB, hvk, one_zpow, mul_one]`. Conclude with `zpow_mem (hidx v) A`.

Rewrite using `[hyv]`. Conclude with `Subgroup.mem_map_of_mem _ hv`. Set `u : Kˣ →* Kˣ` to `(unitsIncl K).comp ((MonoidHom.snd _ _).comp (unitsEquivIntProd hϖ).toMonoidHom)`. Establish `hu : ∀ y, u y = unitsIncl K ((unitsEquivIntProd hϖ) y).2` using `fun y => rfl`. Establish `hunit : IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l])`.

Rewrite using `[PadicInt.isUnit_iff]`. Apply `le_antisymm (PadicInt.norm_le_one _)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h : l ∣ Fintype.card 𝓀[K] - 1` using `by simpa using hlt`.

Rewrite `h` using `[← Nat.card_eq_fintype_card]`. Conclude with `(hl.coprime_iff_not_dvd.mp hcop.symm) h`. Take `⟨c, hc⟩ : ∃ c : ℤ_[l], ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l]) * c = 1` from `⟨_, hunit.mul_val_inv⟩`. Set `s : unitFiltrationUnits K 1 →* unitFiltrationUnits K 1` to `{ toFun := fun x => Additive.toMul (c • Additive.ofMul x) map_one' := by simp map_mul' := by intro x y; simp [smul_add] }`. Establish `hs : ∀ x, s x ^ (Nat.card 𝓀[K] - 1) = x`.

Introduce `x`. Use `show (Additive.toMul (c • Additive.ofMul x)) ^ (Nat.card 𝓀[K] - 1) = x`. Rewrite using `[← toMul_nsmul, ← natCast_smul l, smul_smul, hc, one_smul]`. Both sides reduce to the same expression. Establish `hm : ∀ y, u y ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltrationUnits K 1`.

Introduce `y`. Rewrite using `[hu, ← map_pow]`. Conclude with `Subgroup.mem_map_of_mem _ (hidx _)`. Establish `hfix : ∀ x ∈ unitFiltrationUnits K 1, u x = x`. Introduce `x hx`.

Take `⟨v, _, rfl⟩` from `Subgroup.mem_map.mp hx`. Rewrite using `[hu, unitsEquivIntProd_unitsIncl]`. Take `⟨r, hrc, hrfix, hrpow⟩` from `UpperTheory.exists_continuous_retraction_power _ (isOpen_unitFiltrationUnits 1) u (Nat.card 𝓀[K] - 1) hfix hm s hs`. Use `⟨r, hrc, hrfix, ?_⟩` and prove the remaining obligations. Introduce and unpack `n y ⟨a, ha⟩ ⟨w, hw⟩`.

Use `set t := u y * (r y : Kˣ)⁻¹ with htdef`. Establish `ht : t ^ (Nat.card 𝓀[K] - 1) = 1`. Rewrite using `[htdef, mul_pow, inv_pow, hrpow, mul_inv_cancel]`. Take `⟨A, B, hAB⟩` from `bez t (Nat.card 𝓀[K] - 1) (l ^ n) (Nat.Coprime.pow_right n hcop)`. Rewrite `hAB` using `[ht, one_zpow, one_mul]`.

Establish `hry : (r y : Kˣ) = (w : Kˣ) ^ (l ^ n)` using `by rw [hw]; rfl`. Establish `e1 : (uniformizerUnit hϖ ^ a) ^ (l ^ n) = uniformizerUnit hϖ ^ ord (y : K)`. Rewrite using `[ha, ← zpow_natCast, ← zpow_mul, mul_comm]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `e2 : (t ^ B) ^ (l ^ n) = t` using `by conv_rhs => rw [hAB]`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`. Use `⟨uniformizerUnit hϖ ^ a * t ^ B * (w : Kˣ), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow, e1, e2, ← hry, htdef, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, hu]`. Conclude with `hdecomp y`.
-/
theorem UpperTheory.exists_principal_units_retraction_localField :
    ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l], (∀ y ∈ CommGroup.primaryComponent Kˣ l, y ∈ GroundTheory.LocalField.unitFiltrationUnits K 1) ∧ ∃ r : Kˣ →* ↥(GroundTheory.LocalField.unitFiltrationUnits K 1), Continuous r ∧ (∀ u : ↥(GroundTheory.LocalField.unitFiltrationUnits K 1), r u = u) ∧ ∀ (n : ℕ) (y : Kˣ), (l : ℤ) ^ n ∣ GroundTheory.LocalField.ord (y : K) → (∃ w, r y = w ^ l ^ n) → ∃ z : Kˣ, y = z ^ l ^ n := by
  intro K _ _ _ _ l _ _
  have hl : l.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]
  haveI : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : l ∣ Nat.card 𝓀[K] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[K] l, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[K]
  have hq1 : 1 ≤ Nat.card 𝓀[K] := Nat.card_pos
  have hcop : Nat.Coprime (Nat.card 𝓀[K] - 1) l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro h
    have h2 := Nat.dvd_sub hq h
    rw [show Nat.card 𝓀[K] - (Nat.card 𝓀[K] - 1) = 1 by omega] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.mp h2)
  have bez : ∀ {M : Type} [CommGroup M] (t : M) (a b : ℕ), Nat.Coprime a b →
      ∃ A B : ℤ, t = (t ^ a) ^ A * (t ^ b) ^ B := by
    intro M _ t a b h
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    have h' : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, h, Nat.cast_one]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, h', zpow_one]
  have hidx : ∀ v : (𝒪[K])ˣ, v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 := by
    intro v
    rw [← index_unitFiltration_one]
    exact Subgroup.pow_index_mem _ v
  have hdecomp : ∀ y : Kˣ,
      y = uniformizerUnit hϖ ^ ord (y : K) * unitsIncl K ((unitsEquivIntProd hϖ) y).2 := by
    intro y
    apply (unitsEquivIntProd hϖ).injective
    rw [map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]
    ext
    · simp [unitsEquivIntProd_fst, ← ofAdd_zsmul]
    · simp
  have hinj : ∀ w : (𝒪[K])ˣ, unitsIncl K w = 1 → w = 1 := by
    intro w hw
    have h := congrArg (fun z => ((unitsEquivIntProd hϖ) z).2) hw
    simpa [unitsEquivIntProd_unitsIncl] using h
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp hy
    have hord : ord (y : K) = 0 := by
      have h := congrArg (fun z => ((unitsEquivIntProd hϖ) z).1) hk
      simp only [map_pow, Prod.pow_fst, map_one, Prod.fst_one, unitsEquivIntProd_fst] at h
      rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by exact_mod_cast pow_ne_zero k hl.ne_zero)
      · exact h
    set v := ((unitsEquivIntProd hϖ) y).2 with hvdef
    have hyv : y = unitsIncl K v := by
      conv_lhs => rw [hdecomp y]
      rw [hord, zpow_zero, one_mul]
    have hvk : v ^ l ^ k = 1 := by
      apply hinj
      rw [map_pow, ← hyv, hk]
    obtain ⟨A, B, hAB⟩ := bez v (Nat.card 𝓀[K] - 1) (l ^ k) (Nat.Coprime.pow_right k hcop)
    have hv : v ∈ unitFiltration K 1 := by
      rw [hAB, hvk, one_zpow, mul_one]
      exact zpow_mem (hidx v) A
    rw [hyv]
    exact Subgroup.mem_map_of_mem _ hv
  · let u : Kˣ →* Kˣ :=
      (unitsIncl K).comp ((MonoidHom.snd _ _).comp (unitsEquivIntProd hϖ).toMonoidHom)
    have hu : ∀ y, u y = unitsIncl K ((unitsEquivIntProd hϖ) y).2 := fun y => rfl
    have hunit : IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have h : l ∣ Fintype.card 𝓀[K] - 1 := by simpa using hlt
      rw [← Nat.card_eq_fintype_card] at h
      exact (hl.coprime_iff_not_dvd.mp hcop.symm) h
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l]) * c = 1 :=
      ⟨_, hunit.mul_val_inv⟩
    let s : unitFiltrationUnits K 1 →* unitFiltrationUnits K 1 :=
      { toFun := fun x => Additive.toMul (c • Additive.ofMul x)
        map_one' := by simp
        map_mul' := by intro x y; simp [smul_add] }
    have hs : ∀ x, s x ^ (Nat.card 𝓀[K] - 1) = x := by
      intro x
      show (Additive.toMul (c • Additive.ofMul x)) ^ (Nat.card 𝓀[K] - 1) = x
      rw [← toMul_nsmul, ← natCast_smul l, smul_smul, hc, one_smul]
      rfl
    have hm : ∀ y, u y ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltrationUnits K 1 := by
      intro y
      rw [hu, ← map_pow]
      exact Subgroup.mem_map_of_mem _ (hidx _)
    have hfix : ∀ x ∈ unitFiltrationUnits K 1, u x = x := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := Subgroup.mem_map.mp hx
      rw [hu, unitsEquivIntProd_unitsIncl]
    obtain ⟨r, hrc, hrfix, hrpow⟩ := UpperTheory.exists_continuous_retraction_power _ (isOpen_unitFiltrationUnits 1) u
      (Nat.card 𝓀[K] - 1) hfix hm s hs
    refine ⟨r, hrc, hrfix, ?_⟩
    rintro n y ⟨a, ha⟩ ⟨w, hw⟩
    set t := u y * (r y : Kˣ)⁻¹ with htdef
    have ht : t ^ (Nat.card 𝓀[K] - 1) = 1 := by
      rw [htdef, mul_pow, inv_pow, hrpow, mul_inv_cancel]
    obtain ⟨A, B, hAB⟩ := bez t (Nat.card 𝓀[K] - 1) (l ^ n) (Nat.Coprime.pow_right n hcop)
    rw [ht, one_zpow, one_mul] at hAB
    have hry : (r y : Kˣ) = (w : Kˣ) ^ (l ^ n) := by rw [hw]; rfl
    have e1 : (uniformizerUnit hϖ ^ a) ^ (l ^ n) = uniformizerUnit hϖ ^ ord (y : K) := by
      rw [ha, ← zpow_natCast, ← zpow_mul, mul_comm]
      push_cast
      rfl
    have e2 : (t ^ B) ^ (l ^ n) = t := by
      conv_rhs => rw [hAB]
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    refine ⟨uniformizerUnit hϖ ^ a * t ^ B * (w : Kˣ), ?_⟩
    rw [mul_pow, mul_pow, e1, e2, ← hry, htdef, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, hu]
    exact hdecomp y
