import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {i : k ≃+* k'}

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Establish `hb' : i b ≠ 0` using `fun e => hb (by simpa using e)`. Establish `e1` using `h.int (a / b)`.

Rewrite `e1` using `[map_div₀, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((valuation k').ne_zero_iff.2 hb')), div_le_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hb))]`. Conclude with `e1`.
-/
private theorem iso_le (h : IsoOk i) (a b : k) :
    valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b := by
  by_cases hb : b = 0
  · subst hb
    simp
  · have hb' : i b ≠ 0 := fun e => hb (by simpa using e)
    have e1 := h.int (a / b)
    rw [map_div₀, map_div₀, map_div₀,
      div_le_one₀ (zero_lt_iff.2 ((valuation k').ne_zero_iff.2 hb')),
      div_le_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hb))] at e1
    exact e1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simpa using (h.int (i.symm a)).symm⟩`.
-/
private theorem iso_symm (h : IsoOk i) : IsoOk i.symm :=
  ⟨fun a => by simpa using (h.int (i.symm a)).symm⟩

/- English proof (translation)
Establish `e` using `iso_le h 1 a`. Simplify using `only [map_one] at e`. Rewrite using `[← not_le, ← not_le, e]`.
-/
private theorem iso_lt (h : IsoOk i) (a : k) : valuation k' (i a) < 1 ↔ valuation k a < 1 := by
  have e := iso_le h 1 a
  simp only [map_one] at e
  rw [← not_le, ← not_le, e]

/- English proof (translation)
Establish `hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k`. Take `⟨x, hx⟩` from `valuation_surjective (uniformizer k)`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `uniformizer_ne_zero (R := k) (by simpa using hx.symm)`.

Conclude with `⟨Units.mk0 x hx0, hx⟩`. Conclude with `Classical.epsilon_spec hex`.
-/
private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (UpperTheory.V.Hi.unif k : k) = uniformizer k := by
  have hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, hx⟩
  exact Classical.epsilon_spec hex

/- English proof (translation)
The claim follows from `(inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing`.
-/
private theorem locO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsLocalRing 𝒪[k] :=
  (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing

attribute [local instance 5000] locO

private def intIso (h : IsoOk i) : 𝒪[k] ≃+* 𝒪[k'] where
  toFun x := ⟨i x, (h.int x).2 x.2⟩
  invFun y := ⟨i.symm y, (iso_symm h |>.int y).2 y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

/- English proof (translation)
Rewrite `hx`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun e => hx ((isUnit_map_iff (intIso h) x).1 e)`.
-/
private theorem intIso_max (h : IsoOk i) (x : 𝒪[k]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    intIso h x ∈ IsLocalRing.maximalIdeal 𝒪[k'] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun e => hx ((isUnit_map_iff (intIso h) x).1 e)

/- English proof (translation)
Establish `h1 : Ideal.map (intIso h : 𝒪[k] →+* 𝒪[k']) (IsLocalRing.maximalIdeal 𝒪[k]) ≤ IsLocalRing.maximalIdeal 𝒪[k']` using `Ideal.map_le_iff_le_comap.2 fun y hy => intIso_max h y hy`. Establish `h2` using `Ideal.mem_map_of_mem (intIso h : 𝒪[k] →+* 𝒪[k']) hx`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 c h2`.
-/
private theorem intIso_pow (h : IsoOk i) (c : ℕ) (x : 𝒪[k]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c) :
    intIso h x ∈ IsLocalRing.maximalIdeal 𝒪[k'] ^ c := by
  have h1 : Ideal.map (intIso h : 𝒪[k] →+* 𝒪[k']) (IsLocalRing.maximalIdeal 𝒪[k]) ≤
      IsLocalRing.maximalIdeal 𝒪[k'] :=
    Ideal.map_le_iff_le_comap.2 fun y hy => intIso_max h y hy
  have h2 := Ideal.mem_map_of_mem (intIso h : 𝒪[k] →+* 𝒪[k']) hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 c h2

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `ha`. Establish `hu1 : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c`. Establish `e` using `congrArg Units.val (MonoidHom.mem_ker.1 hu)`. Conclude with `Ideal.Quotient.eq.1 (by simpa using e)`. Use `⟨Units.map (intIso h : 𝒪[k] →* 𝒪[k']) u, ?_, ?_⟩` and prove the remaining obligations.

Use `MonoidHom.mem_ker.2 (Units.ext ?_)` and prove the remaining obligations. Establish `e` using `intIso_pow h c _ hu1`. Rewrite `e` using `[map_sub, map_one]`. Simplify using `using Ideal.Quotient.eq.2 e`. Conclude with `Units.ext rfl`.
-/
private theorem Uc_fwd (h : IsoOk i) (c : ℕ) (a : kˣ) (ha : a ∈ UpperTheory.V.Hi.Uc k c) :
    Units.map (i : k →* k') a ∈ UpperTheory.V.Hi.Uc k' c := by
  obtain ⟨u, hu, rfl⟩ := ha
  have hu1 : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c := by
    have e := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    exact Ideal.Quotient.eq.1 (by simpa using e)
  refine ⟨Units.map (intIso h : 𝒪[k] →* 𝒪[k']) u, ?_, ?_⟩
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    have e := intIso_pow h c _ hu1
    rw [map_sub, map_one] at e
    simpa using Ideal.Quotient.eq.2 e
  · exact Units.ext rfl

end SlopeTestRemainingChoices

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ i h`. Use `⟨iso_le h, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[val_unif k']`. Use `le_uniformizer_iff.2 ((iso_lt h _).2 ?_)` and prove the remaining obligations.

Rewrite using `[val_unif k]`. Conclude with `uniformizer_lt_one`. Establish `h1 : valuation k (i.symm (Hi.unif k' : k')) < 1`. Use `(iso_lt (iso_symm h) _).2 ?_` and prove the remaining obligations. Rewrite using `[val_unif k']`.

Conclude with `uniformizer_lt_one`. Establish `h2 : valuation k (i.symm (Hi.unif k' : k')) ≤ valuation k (Hi.unif k : k)`. Rewrite using `[val_unif k]`. Conclude with `le_uniformizer_iff.2 h1`. Simplify using `using (iso_le h _ _).2 h2`.

Introduce `a`. Express the relevant statement in the definitionally equal form `valuation k' (i (a : k)) = 1 ↔ valuation k (a : k) = 1`. Establish `e1` using `iso_le h (a : k) 1`. Establish `e2` using `iso_le h 1 (a : k)`. Simplify using `only [map_one] at e1 e2`.

Rewrite using `[le_antisymm_iff, le_antisymm_iff, e1, e2]`. Introduce `c a`. Use `⟨fun ha => ?_, Uc_fwd h c a⟩` and prove the remaining obligations. Establish `e` using `Uc_fwd (iso_symm h) c _ ha`. Establish `e' : Units.map (i.symm : k' →* k) (Units.map (i : k →* k') a) = a` using `Units.ext (by simp)`.

Rewrite `e` using `[e']`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.isoVal :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) ∧ valuation k' (i (Hi.unif k : k)) = valuation k' (Hi.unif k' : k') ∧ (∀ a : kˣ, Units.map (i : k →* k') a ∈ Hi.Uo k' ↔ a ∈ Hi.Uo k) ∧ ∀ (c : ℕ) (a : kˣ), Units.map (i : k →* k') a ∈ Hi.Uc k' c ↔ a ∈ Hi.Uc k c := by
  intro k k' _ _ _ _ _ _ _ _ i h
  refine ⟨iso_le h, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [val_unif k']
      refine le_uniformizer_iff.2 ((iso_lt h _).2 ?_)
      rw [val_unif k]
      exact uniformizer_lt_one
    · have h1 : valuation k (i.symm (Hi.unif k' : k')) < 1 := by
        refine (iso_lt (iso_symm h) _).2 ?_
        rw [val_unif k']
        exact uniformizer_lt_one
      have h2 : valuation k (i.symm (Hi.unif k' : k')) ≤ valuation k (Hi.unif k : k) := by
        rw [val_unif k]
        exact le_uniformizer_iff.2 h1
      simpa using (iso_le h _ _).2 h2
  · intro a
    change valuation k' (i (a : k)) = 1 ↔ valuation k (a : k) = 1
    have e1 := iso_le h (a : k) 1
    have e2 := iso_le h 1 (a : k)
    simp only [map_one] at e1 e2
    rw [le_antisymm_iff, le_antisymm_iff, e1, e2]
  · intro c a
    refine ⟨fun ha => ?_, Uc_fwd h c a⟩
    have e := Uc_fwd (iso_symm h) c _ ha
    have e' : Units.map (i.symm : k' →* k) (Units.map (i : k →* k') a) = a := Units.ext (by simp)
    rwa [e'] at e
