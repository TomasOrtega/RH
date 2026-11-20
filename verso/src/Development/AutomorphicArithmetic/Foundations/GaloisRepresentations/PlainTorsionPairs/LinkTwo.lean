import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open private exists_conj ne_top val_nat fin_nat eq_of_mem from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfMem
open private bu bu_val bu_open eq_of_ker dec_of from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfKer
open private pre_ex from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx

/- English proof (translation)
Establish `hle : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A`. Introduce `x`. Establish `h1 : IsIntegral ℤ (algebraMap L Ω x)` using `(RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ L Ω)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (h1.tower_top (A := A))`. Rewrite using `[← hy]`.

Conclude with `y.2`. Set `g : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring hle`. Establish `hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap g ↔ A.valuation (algebraMap L Ω x) < 1`. Introduce `x`. Rewrite using `[Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]`.

Both sides reduce to the same expression. Establish `hnb : (IsLocalRing.maximalIdeal A).comap g ≠ ⊥`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Introduce `hb`. Establish `hm : algebraMap (𝓞 (W.Lp L)) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap g`.

Rewrite using `[hmem]`. Establish `he : (algebraMap L Ω) ↑((algebraMap (𝓞 (W.Lp L)) (𝓞 L)) y) = (algebraMap (W.Lp L) Ω) ↑y` using `rfl`. Rewrite using `[he]`. Conclude with `(h y).mpr hy`. Rewrite `hm` using `[hb, Ideal.mem_bot]`.

Establish `e : ((algebraMap (𝓞 (W.Lp L)) (𝓞 L) y : 𝓞 L) : L) = algebraMap (W.Lp L) L (y : W.Lp L)` using `rfl`. Rewrite `e` using `[hm]`. Establish `e2 : (y : W.Lp L) = 0` using `(algebraMap (W.Lp L) L).injective (by rw [← e, map_zero]; rfl)`. Conclude with `hy0 (RingOfIntegers.ext (by rw [e2]; rfl))`. Use `⟨⟨(IsLocalRing.maximalIdeal A).comap g, Ideal.comap_isPrime _ _, hnb⟩, ?_⟩` and prove the remaining obligations.

Introduce `x`. Conclude with `(hmem x).symm`.
-/
private theorem exists_placeOver_of_placeOver_lp {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)) (h : IsPlaceOver A v) : ∃ w : W.Plc L, IsPlaceOver A w := by
  have hle : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap L Ω x) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ L Ω)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h1.tower_top (A := A))
    rw [← hy]
    exact y.2
  let g : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring hle
  have hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap g ↔ A.valuation (algebraMap L Ω x) < 1 := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hnb : (IsLocalRing.maximalIdeal A).comap g ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have hm : algebraMap (𝓞 (W.Lp L)) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap g := by
      rw [hmem]
      have he : (algebraMap L Ω) ↑((algebraMap (𝓞 (W.Lp L)) (𝓞 L)) y) = (algebraMap (W.Lp L) Ω) ↑y := rfl
      rw [he]
      exact (h y).mpr hy
    rw [hb, Ideal.mem_bot] at hm
    have e : ((algebraMap (𝓞 (W.Lp L)) (𝓞 L) y : 𝓞 L) : L) = algebraMap (W.Lp L) L (y : W.Lp L) := rfl
    rw [hm] at e
    have e2 : (y : W.Lp L) = 0 := (algebraMap (W.Lp L) L).injective (by rw [← e, map_zero]; rfl)
    exact hy0 (RingOfIntegers.ext (by rw [e2]; rfl))
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap g, Ideal.comap_isPrime _ _, hnb⟩, ?_⟩
  intro x
  exact (hmem x).symm

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ hl hunr S hSp hlS hSd A₀ hA₀ v₀ B p hp hp2 hpS hdisc hpv hnorm hB hBd`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `hpl : p ≠ l` using `fun e => hpS (e ▸ hlS)`. Establish `hlv₀ : ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v₀.asIdeal` using `fun h => hpl (eq_of_mem hp Fact.out hpv h)`. Set `Aof : W.Plc (W.Lp L) → ValuationSubring Ω` to `fun v => if h : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal then A₀ ⟨v, h⟩ else if v = v₀ then B else Classical.choose (exists_isPlaceOver Ω v)`.

Establish `hAof : ∀ v, IsPlaceOver (Aof v) v`. Introduce `v`. Simplify using `only [Aof]`. Use `split_ifs with h1 h2`. Conclude with `hA₀ _`.

Substitute `h2` using the available equality. Conclude with `hB`. Conclude with `Classical.choose_spec (exists_isPlaceOver Ω v)`. Establish `hA0 : Aof v₀ = B`. Simplify using `only [Aof, dif_neg hlv₀, if_true]`.

Set `wof : W.Plc (W.Lp L) → W.Plc L` to `fun v => Classical.choose (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))`. Establish `hwof : ∀ v, IsPlaceOver (Aof v) (wof v)` using `fun v => Classical.choose_spec (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))`. Establish `hStf : {v : W.Plc (W.Lp L) | ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite`. Use `(Set.Finite.biUnion S.finite_toSet fun q hq => fin_nat (k := W.Lp L) (hSp q hq).ne_zero).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨q, hq, hqv, -⟩`.

Conclude with `Set.mem_biUnion hq hqv`. Set `St` to `hStf.toFinset`. Establish `hSt : ∀ v, v ∈ St ↔ ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal` using `fun v => hStf.mem_toFinset`. Establish `hSt_l : ∀ u ∈ St, ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal`. Introduce `u hu`.

Take `⟨q, -, -, h⟩` from `(hSt u).mp hu`. Conclude with `h`. Establish `hv0 : v₀ ∉ St`. Introduce `hv`. Take `⟨q, hq, hqv, -⟩` from `(hSt v₀).mp hv`.

Take `rfl` from `eq_of_mem hp (hSp q hq) hpv hqv`. Conclude with `hpS hq`. Establish `hsplit : ∀ v : W.Plc (W.Lp L), ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v₀ → Dec (Aof v) ≤ (W.resP L Ω).range`. Introduce and unpack `v (h | h | rfl)`. Conclude with `hSd l hlS (Aof v) ((val_nat (hAof v) l).mpr h)`.

Take `⟨q, hq, hqv, -⟩` from `(hSt v).mp h`. Conclude with `hSd q hq (Aof v) ((val_nat (hAof v) q).mpr hqv)`. Rewrite using `[hA0]`. Conclude with `hBd`. Take `⟨c, hc⟩` from `exists_conj L Ω`.

Use `⟨W.HidaSetting.mk hl (fun A _ _ => hunr A) c hc wof Aof hwof hAof St hSt_l v₀ hv0 p hp hp2 hpl hdisc hnorm hsplit, rfl, ?_, hA0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v show Aof v.1 = A₀ v`. Simplify using `only [Aof, dif_pos v.2]`. Use `(((fin_nat (k := W.Lp L) hl0).union St.finite_toSet).union (Set.finite_singleton v₀)).subset ?_` and prove the remaining obligations. Introduce and unpack `v (h | h | h)`.

Conclude with `Or.inl (Or.inl h)`. Conclude with `Or.inl (Or.inr h)`. Conclude with `Or.inr h`. Introduce `q hq hlt`. Rewrite `hlt` using `[val_nat hB]`.

Take `rfl` from `eq_of_mem hp (hSp q hq) hpv hlt`. Conclude with `hpS hq`. Introduce `A v hAv hvS q hq hlt`. Rewrite `hlt` using `[val_nat hAv]`. Distinguish the cases in `hlv : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal`.

Conclude with `hvS (Or.inl hlv)`. Conclude with `hvS (Or.inr (Or.inl ((hSt v).mpr ⟨q, hq, hlt, hlv⟩)))`.
-/
theorem UpperTheory.Gal.projectedFormsSystemPart.mkSetP :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], l ≠ 2 → (∀ A : ValuationSubring Ω, Ine (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → l ∈ S → (∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ A₀ : W.Vl l L → ValuationSubring Ω, (∀ v, IsPlaceOver (A₀ v) v.1) → ∀ (v₀ : W.Plc (W.Lp L)) (B : ValuationSubring Ω) (p : ℕ), p.Prime → p ≠ 2 → p ∉ S → ¬ (p : ℤ) ∣ discr L → ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v₀.asIdeal → normV v₀ = p → IsPlaceOver B v₀ → Dec (F := W.Lp L) B ≤ (W.resP L Ω).range → ∃ s : W.HidaSetting l L Ω, s.p = p ∧ (∀ v : W.Vl l L, s.A v = A₀ v) ∧ s.A s.v0 = B ∧ s.S.Finite ∧ (∀ q ∈ S, ¬ B.valuation (q : Ω) < 1) ∧ ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ s.S → ∀ q ∈ S, ¬ A.valuation (q : Ω) < 1 := by
  intro l _ L Ω _ _ _ _ _ _ hl hunr S hSp hlS hSd A₀ hA₀ v₀ B p hp hp2 hpS hdisc hpv hnorm hB hBd
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hpl : p ≠ l := fun e => hpS (e ▸ hlS)
  have hlv₀ : ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v₀.asIdeal := fun h => hpl (eq_of_mem hp Fact.out hpv h)
  let Aof : W.Plc (W.Lp L) → ValuationSubring Ω := fun v =>
    if h : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal then A₀ ⟨v, h⟩
    else if v = v₀ then B else Classical.choose (exists_isPlaceOver Ω v)
  have hAof : ∀ v, IsPlaceOver (Aof v) v := by
    intro v
    simp only [Aof]
    split_ifs with h1 h2
    · exact hA₀ _
    · subst h2
      exact hB
    · exact Classical.choose_spec (exists_isPlaceOver Ω v)
  have hA0 : Aof v₀ = B := by
    simp only [Aof, dif_neg hlv₀, if_true]
  let wof : W.Plc (W.Lp L) → W.Plc L := fun v => Classical.choose (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))
  have hwof : ∀ v, IsPlaceOver (Aof v) (wof v) := fun v => Classical.choose_spec (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))
  have hStf : {v : W.Plc (W.Lp L) | ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧
      ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite := by
    refine (Set.Finite.biUnion S.finite_toSet fun q hq => fin_nat (k := W.Lp L) (hSp q hq).ne_zero).subset ?_
    rintro v ⟨q, hq, hqv, -⟩
    exact Set.mem_biUnion hq hqv
  let St := hStf.toFinset
  have hSt : ∀ v, v ∈ St ↔ ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal :=
    fun v => hStf.mem_toFinset
  have hSt_l : ∀ u ∈ St, ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal := by
    intro u hu
    obtain ⟨q, -, -, h⟩ := (hSt u).mp hu
    exact h
  have hv0 : v₀ ∉ St := by
    intro hv
    obtain ⟨q, hq, hqv, -⟩ := (hSt v₀).mp hv
    obtain rfl := eq_of_mem hp (hSp q hq) hpv hqv
    exact hpS hq
  have hsplit : ∀ v : W.Plc (W.Lp L), ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v₀ →
      Dec (Aof v) ≤ (W.resP L Ω).range := by
    rintro v (h | h | rfl)
    · exact hSd l hlS (Aof v) ((val_nat (hAof v) l).mpr h)
    · obtain ⟨q, hq, hqv, -⟩ := (hSt v).mp h
      exact hSd q hq (Aof v) ((val_nat (hAof v) q).mpr hqv)
    · rw [hA0]
      exact hBd
  obtain ⟨c, hc⟩ := exists_conj L Ω
  refine ⟨W.HidaSetting.mk hl (fun A _ _ => hunr A) c hc wof Aof hwof hAof St hSt_l v₀ hv0 p hp hp2 hpl hdisc hnorm
    hsplit, rfl, ?_, hA0, ?_, ?_, ?_⟩
  · intro v
    show Aof v.1 = A₀ v
    simp only [Aof, dif_pos v.2]
  · refine (((fin_nat (k := W.Lp L) hl0).union St.finite_toSet).union (Set.finite_singleton v₀)).subset ?_
    rintro v (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro q hq hlt
    rw [val_nat hB] at hlt
    obtain rfl := eq_of_mem hp (hSp q hq) hpv hlt
    exact hpS hq
  · intro A v hAv hvS q hq hlt
    rw [val_nat hAv] at hlt
    by_cases hlv : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact hvS (Or.inl hlv)
    · exact hvS (Or.inr (Or.inl ((hSt v).mpr ⟨q, hq, hlt, hlv⟩)))

/- English proof (translation)
Take `⟨h1, h2⟩` from `hs`. Use `⟨dec_of h h1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[h x]`. Conclude with `h2 x hx`.
-/
private theorem mem_ine_of_apply_eq_of_mem_ine {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [NumberField F] [NumberField F']
    [Algebra F Ω] [Algebra F' Ω] {A : ValuationSubring Ω} {σ : G F Ω} {τ : G F' Ω}
    (h : ∀ x : Ω, τ x = σ x) (hs : σ ∈ Ine A) : τ ∈ Ine A := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨dec_of h h1, fun x hx => ?_⟩
  rw [h x]
  exact h2 x hx

/- English proof (translation)
Introduce `σ hσ`. Take `⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩` from `galEq T`. Set `σ' : G ℚ Ω` to `σ.restrictScalars ℚ`. Establish `h1 : σ' ∈ Dec (F` using `ℚ) A := dec_of (fun x => rfl) hσ`. Establish `hK : σ' ∈ T.K.fixingSubgroup` using `hOk.split q hq A hA h1`.

Establish `hFix : ∀ x ∈ T.F, σ' x = x`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(hF x).mp hx`. Conclude with `σ.commutes y`. Establish `hLeq : T.L = T.F ⊔ T.K`.

Consider the cases of `T`. Use the matching hypothesis. Establish `hL : σ' ∈ T.L.fixingSubgroup`. Rewrite using `[hLeq, IntermediateField.fixingSubgroup_sup]`. Conclude with `⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hFix, hK⟩`.

Set `g : G T.L Ω` to `AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv) (fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hL x x.2)`. Rewrite using `[← hφL, hGal]`. Conclude with `⟨g, AlgEquiv.ext fun x => (hφ σ x).symm⟩`.
-/
private theorem dec_of_ok_of_valuation_lt_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (hOk : T.Ok) (q : ℕ) (hq : q ∈ D.S) (A : ValuationSubring Ω)
    (hA : A.valuation (q : Ω) < 1) : Dec (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
  intro σ hσ
  obtain ⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩ := galEq T
  let σ' : G ℚ Ω := σ.restrictScalars ℚ
  have h1 : σ' ∈ Dec (F := ℚ) A := dec_of (fun x => rfl) hσ
  have hK : σ' ∈ T.K.fixingSubgroup := hOk.split q hq A hA h1
  have hFix : ∀ x ∈ T.F, σ' x = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hF x).mp hx
    exact σ.commutes y
  have hLeq : T.L = T.F ⊔ T.K := by
    cases T
    assumption
  have hL : σ' ∈ T.L.fixingSubgroup := by
    rw [hLeq, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hFix, hK⟩
  let g : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv)
    (fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hL x x.2)
  rw [← hφL, hGal]
  exact ⟨g, AlgEquiv.ext fun x => (hφ σ x).symm⟩

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T hG hOk p₀ hp₀`. Take `⟨g₀, hg₁, hg₂⟩` from `gEx T hOk`. Take `⟨e, he⟩` from `placesEq T`. Take `⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩` from `galEq T`. Establish `hunr : ∀ A : ValuationSubring Ω, Ine (F` using `W.Lp T.L) A ≤ (W.resP T.L Ω).range := by`.

Introduce `A σ hσ`. Conclude with `(hφL σ).mp (hOk.unr A (mem_ine_of_apply_eq_of_mem_ine (hφ σ) hσ))`. Establish `hbf` using `barFacts hG`. Set `U : Subgroup (G T.L Ω)` to `(⨅ i : Fin 4, (bu T.L (chi D T.pr i)).ker) ⊓ (bu T.L D.om).ker`. Establish `hUo : IsOpen (U : Set (G T.L Ω))`.

Rewrite using `[Subgroup.coe_inf, Subgroup.coe_iInf]`. Use `(isOpen_iInter_of_finite fun i => bu_open T.L _ ?_).inter (bu_open T.L _ hbf.2.1)` and prove the remaining obligations. Unfold `chi`. Conclude with `hbf.1 _`. Set `M : ℕ` to `p₀ * 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs`.

Establish `hM : M ≠ 0`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero hp₀ two_ne_zero) ?_) ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr fun q hq => (hG.S_prime q hq).ne_zero`. Conclude with `Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero T.L)`. Take `⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBd, hU1, hU2⟩` from `v0Ex T.L Ω U hUo g₀ M hM`.

Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `hpM (((dvd_mul_left 2 p₀).mul_right _).mul_right _)`. Establish `hpS : p ∉ D.S` using `fun h => hpM ((((Finset.dvd_prod_of_mem (fun q => q) h).mul_left (p₀ * 2))).mul_right _)`. Establish `hdisc : ¬ (p : ℤ) ∣ NumberField.discr T.L` using `fun h => hpM ((Int.natCast_dvd.mp h).mul_left _)`.

Take `⟨s, hsp, hsA, hsv0, hSf, hBaway, hAway⟩` from `UpperTheory.Gal.projectedFormsSystemPart.mkSetP l T.L Ω hG.l_odd hunr D.S hG.S_prime hG.l_mem (fun q hq A hA => dec_of_ok_of_valuation_lt_one T hOk q hq A hA) (fun v => T.pl (e v)) he v B p hp hp2 hpS hdisc hpv hnorm hB hBd`. Establish `hchi : ∀ d ∈ Dec (s.A s.v0), ∀ i j : Fin 4, Raw.bar (chi D T.pr i) ((resQ T.L) d) = Raw.bar (chi D T.pr j) ((resQ T.L) d)`. Introduce `d hd i j`. Rewrite `hd` using `[hsv0]`. Take `⟨n, hn⟩` from `hU1 d hd`.

Establish `key : ∀ k : Fin 4, Raw.bar (chi D T.pr k) ((resQ T.L) d) = Raw.bar (chi D T.pr k) ((resQ T.L) g₀) ^ n`. Introduce `k`. Establish `hk` using `eq_of_ker (f := bu T.L (chi D T.pr k)) (Subgroup.mem_iInf.mp hn.1 k)`. Rewrite using `[← bu_val, ← bu_val, hk]`. Conclude with `(congrArg Units.val (map_zpow (bu T.L (chi D T.pr k)) g₀ n)).trans (Units.val_zpow_eq_zpow_val _ _)`.

Rewrite using `[key i, key j, hg₁ i j]`. Establish `hom : ∃ d ∈ Dec (s.A s.v0), Raw.bar D.om ((resQ T.L) d) ≠ 1`. Rewrite using `[hsv0]`. Take `⟨d, hd, hdU⟩` from `hU2`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations.

Establish `hk` using `eq_of_ker (f := bu T.L D.om) hdU.2`. Rewrite using `[← bu_val, hk, bu_val]`. Conclude with `hg₂`. Use `⟨SetD.mk s e hsA hSf (fun A w h1 h2 => hAway A w h1 h2) (by rw [hsv0]; exact hBaway) hchi hom (ccOf T s), ?_⟩` and prove the remaining obligations. Use `show ¬ s.p ∣ p₀`.

Rewrite using `[hsp]`. Introduce `h`. Conclude with `hpM (((h.mul_right 2).mul_right _).mul_right _)`.
-/
theorem UpperTheory.Gal.projectedFormsSystemPart.setAv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), D.Good → T.Ok → ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ Y : SetD T, ¬ Y.s.p ∣ p₀ := by
  intro Ω _ _ _ l _ c D T hG hOk p₀ hp₀
  obtain ⟨g₀, hg₁, hg₂⟩ := gEx T hOk
  obtain ⟨e, he⟩ := placesEq T
  obtain ⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩ := galEq T
  have hunr : ∀ A : ValuationSubring Ω, Ine (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro A σ hσ
    exact (hφL σ).mp (hOk.unr A (mem_ine_of_apply_eq_of_mem_ine (hφ σ) hσ))
  have hbf := barFacts hG
  let U : Subgroup (G T.L Ω) := (⨅ i : Fin 4, (bu T.L (chi D T.pr i)).ker) ⊓ (bu T.L D.om).ker
  have hUo : IsOpen (U : Set (G T.L Ω)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    refine (isOpen_iInter_of_finite fun i => bu_open T.L _ ?_).inter (bu_open T.L _ hbf.2.1)
    unfold chi
    exact hbf.1 _
  let M : ℕ := p₀ * 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs
  have hM : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hp₀ two_ne_zero) ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun q hq => (hG.S_prime q hq).ne_zero
    · exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero T.L)
  obtain ⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBd, hU1, hU2⟩ := v0Ex T.L Ω U hUo g₀ M hM
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM (((dvd_mul_left 2 p₀).mul_right _).mul_right _)
  have hpS : p ∉ D.S := fun h =>
    hpM ((((Finset.dvd_prod_of_mem (fun q => q) h).mul_left (p₀ * 2))).mul_right _)
  have hdisc : ¬ (p : ℤ) ∣ NumberField.discr T.L := fun h =>
    hpM ((Int.natCast_dvd.mp h).mul_left _)
  obtain ⟨s, hsp, hsA, hsv0, hSf, hBaway, hAway⟩ :=
    UpperTheory.Gal.projectedFormsSystemPart.mkSetP l T.L Ω hG.l_odd hunr D.S hG.S_prime hG.l_mem
      (fun q hq A hA => dec_of_ok_of_valuation_lt_one T hOk q hq A hA) (fun v => T.pl (e v)) he v B p hp hp2 hpS hdisc hpv hnorm hB hBd
  have hchi : ∀ d ∈ Dec (s.A s.v0), ∀ i j : Fin 4,
      Raw.bar (chi D T.pr i) ((resQ T.L) d) = Raw.bar (chi D T.pr j) ((resQ T.L) d) := by
    intro d hd i j
    rw [hsv0] at hd
    obtain ⟨n, hn⟩ := hU1 d hd
    have key : ∀ k : Fin 4, Raw.bar (chi D T.pr k) ((resQ T.L) d) = Raw.bar (chi D T.pr k) ((resQ T.L) g₀) ^ n := by
      intro k
      have hk := eq_of_ker (f := bu T.L (chi D T.pr k)) (Subgroup.mem_iInf.mp hn.1 k)
      rw [← bu_val, ← bu_val, hk]
      exact (congrArg Units.val (map_zpow (bu T.L (chi D T.pr k)) g₀ n)).trans (Units.val_zpow_eq_zpow_val _ _)
    rw [key i, key j, hg₁ i j]
  have hom : ∃ d ∈ Dec (s.A s.v0), Raw.bar D.om ((resQ T.L) d) ≠ 1 := by
    rw [hsv0]
    obtain ⟨d, hd, hdU⟩ := hU2
    refine ⟨d, hd, ?_⟩
    have hk := eq_of_ker (f := bu T.L D.om) hdU.2
    rw [← bu_val, hk, bu_val]
    exact hg₂
  refine ⟨SetD.mk s e hsA hSf (fun A w h1 h2 => hAway A w h1 h2) (by rw [hsv0]; exact hBaway) hchi hom (ccOf T s), ?_⟩
  show ¬ s.p ∣ p₀
  rw [hsp]
  intro h
  exact hpM (((h.mul_right 2).mul_right _).mul_right _)
