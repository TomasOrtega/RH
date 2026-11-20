import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

/- English proof (translation)
Establish `hN : U.Normal` using `inferInstance`. Establish `conj_eq : ∀ γ : G, U.map (MulAut.conj γ).toMonoidHom = U`. Introduce `γ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hN.conj_mem y hy γ`. Introduce `hx`. Use `⟨γ⁻¹ * x * γ, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hN.conj_mem x hx γ⁻¹`.

Simplify using `[mul_assoc]`. Establish `hrel : ∀ v, U.relIndex (MulAction.stabilizer G (p v)) = U.relIndex (U ⊔ MulAction.stabilizer G b)`. Introduce `v`. Take `⟨γ, hγ⟩` from `h1 v`. Rewrite using `[hγ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]`.

Establish `e` using `Subgroup.relIndex_map_map (MulAut.conj γ).toMonoidHom U (MulAction.stabilizer G b)`. Rewrite `e` using `[conj_eq γ]`. Establish `hker : (MulAut.conj γ).toMonoidHom.ker = ⊥` using `(MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)`. Rewrite using `[e, hker, sup_bot_eq, sup_bot_eq, Subgroup.relIndex_sup_left]`. Use `choose γ hγ using h1`.

Set `F : V → G ⧸ (U ⊔ MulAction.stabilizer G b)` to `fun v => QuotientGroup.mk (γ v)`. Establish `inj : Function.Injective F`. Introduce `v w hvw`. Establish `hm : (γ v)⁻¹ * γ w ∈ U ⊔ MulAction.stabilizer G b` using `QuotientGroup.eq.mp hvw`. Rewrite `hm` using `[← SetLike.mem_coe, Subgroup.normal_mul]`.

Take `⟨a, ha, c, hc, hac⟩` from `hm`. Establish `hac' : a * c = (γ v)⁻¹ * γ w` using `hac`. Establish `hw : γ w = γ v * a * c`. Rewrite using `[mul_assoc, hac', mul_inv_cancel_left]`. Establish `h₁ : γ w • b = (γ v * a * (γ v)⁻¹) • p v`.

Rewrite using `[hw, hγ v, mul_smul, MulAction.mem_stabilizer_iff.mp hc, ← mul_smul, inv_mul_cancel_right]`. Establish `h₂ : γ w • b = (1 : G) • p w` using `by rw [one_smul, hγ w]`. Establish `hu : γ v * a * (γ v)⁻¹ ∈ U` using `hN.conj_mem a ha (γ v)`. Conclude with `(h2 (γ w)).unique ⟨_, hu, h₁⟩ ⟨1, U.one_mem, h₂⟩`. Establish `surj : Function.Surjective F`.

Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g`. Take `⟨v, ⟨u, hu, e⟩, -⟩` from `h2 g`. Use `⟨v, QuotientGroup.eq.mpr ?_⟩` and prove the remaining obligations.

Establish `hsplit : (γ v)⁻¹ * g = ((γ v)⁻¹ * u * γ v) * ((γ v)⁻¹ * u⁻¹ * g)` using `by group`. Rewrite using `[hsplit]`. Use `Subgroup.mul_mem_sup ?_ ?_` and prove the remaining obligations. Simplify using `using hN.conj_mem u hu (γ v)⁻¹`. Rewrite using `[MulAction.mem_stabilizer_iff]`.

Rewrite `e` using `[hγ v]`. Simplify using `only [mul_smul, e, inv_smul_smul]`. Establish `hcard : Fintype.card V = (U ⊔ MulAction.stabilizer G b).index`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_eq_of_bijective F ⟨inj, surj⟩`.

Rewrite using `[Finset.sum_congr rfl (fun v _ => hrel v), Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, mul_comm, Subgroup.relIndex_mul_index le_sup_left]`.
-/
private theorem orbit_count {G X V : Type} [Group G] [MulAction G X] [Fintype V] (U : Subgroup G) [U.Normal]
    (hU : U.index ≠ 0) (b : X) (p : V → X) (h1 : ∀ v, ∃ γ : G, p v = γ • b)
    (h2 : ∀ g : G, ∃! v, ∃ u ∈ U, g • b = u • p v) :
    ∑ v, U.relIndex (MulAction.stabilizer G (p v)) = U.index := by
  classical
  have hN : U.Normal := inferInstance
  have conj_eq : ∀ γ : G, U.map (MulAut.conj γ).toMonoidHom = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy γ
    · intro hx
      refine ⟨γ⁻¹ * x * γ, ?_, ?_⟩
      · simpa using hN.conj_mem x hx γ⁻¹
      · simp [mul_assoc]
  have hrel : ∀ v, U.relIndex (MulAction.stabilizer G (p v)) =
      U.relIndex (U ⊔ MulAction.stabilizer G b) := by
    intro v
    obtain ⟨γ, hγ⟩ := h1 v
    rw [hγ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have e := Subgroup.relIndex_map_map (MulAut.conj γ).toMonoidHom U (MulAction.stabilizer G b)
    rw [conj_eq γ] at e
    have hker : (MulAut.conj γ).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)
    rw [e, hker, sup_bot_eq, sup_bot_eq, Subgroup.relIndex_sup_left]
  choose γ hγ using h1
  let F : V → G ⧸ (U ⊔ MulAction.stabilizer G b) := fun v => QuotientGroup.mk (γ v)
  have inj : Function.Injective F := by
    intro v w hvw
    have hm : (γ v)⁻¹ * γ w ∈ U ⊔ MulAction.stabilizer G b := QuotientGroup.eq.mp hvw
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hm
    obtain ⟨a, ha, c, hc, hac⟩ := hm
    have hac' : a * c = (γ v)⁻¹ * γ w := hac
    have hw : γ w = γ v * a * c := by
      rw [mul_assoc, hac', mul_inv_cancel_left]
    have h₁ : γ w • b = (γ v * a * (γ v)⁻¹) • p v := by
      rw [hw, hγ v, mul_smul, MulAction.mem_stabilizer_iff.mp hc, ← mul_smul, inv_mul_cancel_right]
    have h₂ : γ w • b = (1 : G) • p w := by rw [one_smul, hγ w]
    have hu : γ v * a * (γ v)⁻¹ ∈ U := hN.conj_mem a ha (γ v)
    exact (h2 (γ w)).unique ⟨_, hu, h₁⟩ ⟨1, U.one_mem, h₂⟩
  have surj : Function.Surjective F := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨v, ⟨u, hu, e⟩, -⟩ := h2 g
      refine ⟨v, QuotientGroup.eq.mpr ?_⟩
      have hsplit : (γ v)⁻¹ * g = ((γ v)⁻¹ * u * γ v) * ((γ v)⁻¹ * u⁻¹ * g) := by group
      rw [hsplit]
      refine Subgroup.mul_mem_sup ?_ ?_
      · simpa using hN.conj_mem u hu (γ v)⁻¹
      · rw [MulAction.mem_stabilizer_iff]
        rw [hγ v] at e
        simp only [mul_smul, e, inv_smul_smul]
  have hcard : Fintype.card V = (U ⊔ MulAction.stabilizer G b).index := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_eq_of_bijective F ⟨inj, surj⟩
  rw [Finset.sum_congr rfl (fun v _ => hrel v), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hcard, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

/- English proof (translation)
Unfold `upl`. Prove the components needed by the constructor for the conclusion. Introduce `n hn g x hx`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hy'⟩ : ∃ y ∈ maximalRealSubfield L, g⁻¹ (algebraMap L Ω x) = algebraMap L Ω y := by`. Use `⟨((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L) x, ?_, ?_⟩` and prove the remaining obligations.

Introduce `φ`. Conclude with `hx (φ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L).toRingHom)`. Conclude with `(AlgHom.restrictNormal_commutes (g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom L x).symm`. Establish `hn'` using `hn y hy`. Use `show (g * n * g⁻¹) (algebraMap L Ω x) = algebraMap L Ω x`.

Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', hn', ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.
-/
private theorem upl_normal (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] [IsAbelianGalois ℚ L] : (upl Ω L).Normal := by
  unfold upl
  constructor
  intro n hn g x hx
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ maximalRealSubfield L, g⁻¹ (algebraMap L Ω x) = algebraMap L Ω y := by
    refine ⟨((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L) x, ?_, ?_⟩
    · intro φ
      exact hx (φ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L).toRingHom)
    · exact (AlgHom.restrictNormal_commutes (g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom L x).symm
  have hn' := hn y hy
  show (g * n * g⁻¹) (algebraMap L Ω x) = algebraMap L Ω x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', hn', ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Unfold `cycMod cycZ`. Use `ext`. Simplify using `only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]`. Express the relevant statement in the definitionally equal form `PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l) ((MulSemiringAction.toRingAut (G ℚ Ω) Ω) s)).val = 1`.

Rewrite using `[cyclotomicCharacter.toZModPow]`. Use `symm`. Apply `modularCyclotomicCharacter.unique` to reduce the goal to its premises. Introduce `t ht`. Establish `hl1 : l ^ 1 ≠ 1` using `by rw [pow_one]; exact hl.out.one_lt.ne'`.

Rewrite using `[ZMod.val_one'' hl1, pow_one]`. Rewrite `ht` using `[pow_one]`. Take `⟨i, -, e⟩` from `(hζ.isUnit_unit hl.out.ne_zero).eq_pow_of_mem_rootsOfUnity ht`. Rewrite using `[← e]`. Simplify using `[hs]`.
-/
private theorem cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ l) {s : G ℚ Ω} (hs : s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  unfold cycMod cycZ
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
  change PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l) ((MulSemiringAction.toRingAut (G ℚ Ω) Ω) s)).val = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have hl1 : l ^ 1 ≠ 1 := by rw [pow_one]; exact hl.out.one_lt.ne'
  rw [ZMod.val_one'' hl1, pow_one]
  rw [pow_one] at ht
  obtain ⟨i, -, e⟩ := (hζ.isUnit_unit hl.out.ne_zero).eq_pow_of_mem_rootsOfUnity ht
  rw [← e]
  simp [hs]

/- English proof (translation)
Establish `key : ∀ (A : ValuationSubring Ω) (x : Ω), x ≠ 0 → (A.valuation x < 1 ↔ x⁻¹ ∉ A)`. Introduce `A x hx`. Rewrite using `[← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]`. Distinguish the cases in `hn : (n : Ω) = 0`. Rewrite using `[hn]`.

Generalize the expression as in `g • B = C`. Use `haveI : Nontrivial C.ValueGroup := ValuationRing.instNontrivialValueGroup C Ω`. Rewrite using `[map_zero]`. Conclude with `zero_lt_one`. Rewrite `h`, the goal using `[key _ _ hn]`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]`. Conclude with `h`.
-/
private theorem val_smul {Ω : Type} [Field Ω] [CharZero Ω] (g : G ℚ Ω) (B : ValuationSubring Ω) (n : ℕ)
    (h : B.valuation (n : Ω) < 1) : (g • B).valuation (n : Ω) < 1 := by
  have key : ∀ (A : ValuationSubring Ω) (x : Ω), x ≠ 0 → (A.valuation x < 1 ↔ x⁻¹ ∉ A) := by
    intro A x hx
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]
  by_cases hn : (n : Ω) = 0
  · rw [hn]
    generalize g • B = C
    haveI : Nontrivial C.ValueGroup := ValuationRing.instNontrivialValueGroup C Ω
    rw [map_zero]
    exact zero_lt_one
  rw [key _ _ hn] at h ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact h

set_option maxHeartbeats 400000 in
/- English proof (translation)
Unfold `UpperTheory.V.Pr.DegEq`. Introduce `Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k a`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : IsAbelianGalois ℚ L := k.ab`. Use `haveI : (upl Ω L).Normal := upl_normal Ω L`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hgal : galOf ℚ (W.Lp L) Ω = upl Ω L`. Use extensionality with `s`. Unfold `galOf upl`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Conclude with `h ⟨x, hx⟩`. Introduce `h x`. Conclude with `h x.1 x.2`. Establish `hidx : (upl Ω L).index = Module.finrank ℚ (W.Lp L)`.

Rewrite using `[← hgal]`. Conclude with `(galEmbTop ℚ (W.Lp L) Ω).2.2`. Rewrite using `[← hidx]`. Unfold `Fr.Frame.d`. Rewrite using `[Finset.sum_congr rfl (fun v _ => k.dv v)]`.

Use `orbit_count (upl Ω L) (by rw [hidx]; exact Module.finrank_pos.ne') B k.pl ?_ ?_` and prove the remaining obligations. Introduce `v`. Take `⟨γ, -, h⟩` from `k.pl_conj v`. Conclude with `⟨γ, h⟩`. Introduce `g`.

Conclude with `k.pl_all (g • B) (val_smul g B l hL.atl)`. Introduce and unpack `⟨ζ, hζ⟩`. Take `⟨g, hg⟩` from `k.mu a`. Apply `hg` to reduce the goal to its premises. Establish `hsD : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ Dec (k.pl a)` using `(k.j_range a _).mp ⟨g, rfl⟩`.

Take `⟨γ, -, hγ⟩` from `k.pl_conj a`. Establish `hM : B.valuation (M : Ω) < 1`. Take `⟨t, ht⟩` from `hL.dvd`. Establish `h1 : B.valuation ((N * t : ℕ) : Ω) ≤ 1` using `(B.valuation_le_one_iff _).mpr (natCast_mem B _)`. Rewrite using `[ht, mul_assoc, Nat.cast_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM' : (k.pl a).valuation (M : Ω) < 1`. Rewrite using `[hγ]`. Conclude with `val_smul γ B M hM`. Establish `hker : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ η.ker` using `k.split (k.pl a) hM' (Subgroup.mem_inf.mpr ⟨hsD, (k.j a g).2⟩)`.

Establish `hfix : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ galOf ℚ L Ω`. Rewrite using `[k.gal]`. Conclude with `Subgroup.mem_inf.mpr ⟨(k.j a g).2, hker⟩`. Unfold `galOf at hfix`. Conclude with `cycMod_one l (hζ.map_of_injective (algebraMap L Ω).injective) (hfix ζ)`.
-/
theorem UpperTheory.V.Pr.degEq :
    UpperTheory.V.Pr.DegEq := by
  unfold UpperTheory.V.Pr.DegEq
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k a
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAbelianGalois ℚ L := k.ab
  haveI : (upl Ω L).Normal := upl_normal Ω L
  refine ⟨?_, ?_⟩
  · have hgal : galOf ℚ (W.Lp L) Ω = upl Ω L := by
      ext s
      unfold galOf upl
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hidx : (upl Ω L).index = Module.finrank ℚ (W.Lp L) := by
      rw [← hgal]
      exact (galEmbTop ℚ (W.Lp L) Ω).2.2
    rw [← hidx]
    unfold Fr.Frame.d
    rw [Finset.sum_congr rfl (fun v _ => k.dv v)]
    refine orbit_count (upl Ω L) (by rw [hidx]; exact Module.finrank_pos.ne') B k.pl ?_ ?_
    · intro v
      obtain ⟨γ, -, h⟩ := k.pl_conj v
      exact ⟨γ, h⟩
    · intro g
      exact k.pl_all (g • B) (val_smul g B l hL.atl)
  · rintro ⟨ζ, hζ⟩
    obtain ⟨g, hg⟩ := k.mu a
    apply hg
    have hsD : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ Dec (k.pl a) := (k.j_range a _).mp ⟨g, rfl⟩
    obtain ⟨γ, -, hγ⟩ := k.pl_conj a
    have hM : B.valuation (M : Ω) < 1 := by
      obtain ⟨t, ht⟩ := hL.dvd
      have h1 : B.valuation ((N * t : ℕ) : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (natCast_mem B _)
      rw [ht, mul_assoc, Nat.cast_mul, map_mul]
      calc B.valuation (l : Ω) * B.valuation ((N * t : ℕ) : Ω) ≤ B.valuation (l : Ω) :=
            mul_le_of_le_one_right' h1
        _ < 1 := hL.atl
    have hM' : (k.pl a).valuation (M : Ω) < 1 := by
      rw [hγ]
      exact val_smul γ B M hM
    have hker : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ η.ker :=
      k.split (k.pl a) hM' (Subgroup.mem_inf.mpr ⟨hsD, (k.j a g).2⟩)
    have hfix : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      exact Subgroup.mem_inf.mpr ⟨(k.j a g).2, hker⟩
    unfold galOf at hfix
    exact cycMod_one l (hζ.map_of_injective (algebraMap L Ω).injective) (hfix ζ)
