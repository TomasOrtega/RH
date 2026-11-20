import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Reflect
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Establish `hbot : powR (C ⧸ H) l = ⊥` using `by show (powMonoidHom l : (C ⧸ H) →* (C ⧸ H)).range = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H c`.

Rewrite using `[Subgroup.mem_bot, powMonoidHom_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `hH ⟨c, rfl⟩`. Rewrite using `[(cardTors (C ⧸ H)).2 l, hbot, Subgroup.index_bot]`. Both sides reduce to the same expression.
-/
private theorem reflOdd_index {C : Type} [CommGroup C] [Finite C] (l : ℕ) [Fact l.Prime] (H : Subgroup C)
    (hH : powR C l ≤ H) : H.index = Nat.card (C ⧸ H →* Multiplicative (ZMod l)) := by
  have hbot : powR (C ⧸ H) l = ⊥ := by
    show (powMonoidHom l : (C ⧸ H) →* (C ⧸ H)).range = ⊥
    rw [eq_bot_iff]
    rintro _ ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H c =>
      rw [Subgroup.mem_bot, powMonoidHom_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hH ⟨c, rfl⟩
  rw [(cardTors (C ⧸ H)).2 l, hbot, Subgroup.index_bot]
  rfl

/- English proof (translation)
Use extensionality with `x`. Apply `(algebraMap K Ω).injective` to reduce the goal to its premises. Rewrite using `[← h x, ← h' x]`.
-/
private theorem reflOdd_uniq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {τ τ' : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) (h' : IsLift τ' σ) : τ = τ' := by
  ext x
  apply (algebraMap K Ω).injective
  rw [← h x, ← h' x]

/- English proof (translation)
Introduce `K _ _ _ l _ ζ hl2 hζ`. Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero l := ⟨hp.ne_zero⟩`. Use `haveI : Fact (1 < l) := ⟨hp.one_lt⟩`. Establish `hodd : Odd l` using `hp.odd_of_ne_two hl2`.

Take `⟨σ, hσ⟩` from `@exists_isConjOm K (AlgebraicClosure K) _ _ _ _ _`. Establish `hσl : IsLift (cE K) σ` using `hσ.isLift`. Establish `hchi : ∀ g : G K (AlgebraicClosure K), g (algebraMap K (AlgebraicClosure K) ζ) = (algebraMap K (AlgebraicClosure K) ζ) ^ (((1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ) g : (ZMod l)ˣ) : ZMod l).val`. Introduce `g`. Rewrite using `[MonoidHom.one_apply, Units.val_one, ZMod.val_one, pow_one]`.

Conclude with `g.commutes ζ`. Establish `hR` using `reflect K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) l 1 ζ 1 1 σ rfl hodd hζ hchi hσ`. Establish `hP` using `pullEq K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l) (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) one_ne_zero le_rfl (Or.inl (by infer_instance))`. Establish `hinj` using `(pullMem K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero).2 le_rfl`. Establish `heq` using `hP.2 (cE K) σ 1 hσl`.

Establish `hcardE` using `Nat.card_congr (Submodule.equivMapOfInjective _ hinj (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l))).toEquiv`. Rewrite `hcardE` using `[heq]`. Use `set H : Subgroup (Cl K) := powR (Cl K) l ⊔ difR (clMap (cE K)) with hH`. Establish `hidx` using `reflOdd_index l H le_sup_left`. Establish `hmk : ∀ c : Cl K, (QuotientGroup.mk (clMap (cE K) c) : Cl K ⧸ H) = QuotientGroup.mk c`.

Introduce `c`. Use `symm`. Rewrite using `[QuotientGroup.eq_iff_div_mem]`. Conclude with `le_sup_right (a := powR (Cl K) l) (⟨c, rfl⟩ : c / clMap (cE K) c ∈ difR (clMap (cE K)))`. Establish `hmem : ∀ φ : Cl K ⧸ H →* Multiplicative (ZMod l), (fun c : ClassGroup (𝓞 K) => Multiplicative.toAdd (φ (QuotientGroup.mk c))) ∈ ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l)`.

Introduce `φ`. Unfold `ClEig ClEq`. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `ClDual`. Use `⟨fun a b => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Simplify using `[QuotientGroup.mk_mul]`. Establish `hv' : ((1 : ℕ) : 𝓞 K) ∈ v.asIdeal` using `hv`. Rewrite `hv'` using `[Nat.cast_one]`. Conclude with `absurd ((Ideal.eq_top_iff_one _).mpr hv') v.isPrime.ne_top`. Unfold `clCond`.

Introduce `τ hτ c`. Establish `h1 : τ = RingEquiv.refl K` using `reflOdd_uniq hτ (fun x => g.commutes x)`. Substitute `h1` using the available equality. Rewrite using `[(clMapBasic K K K (RingEquiv.refl K) (RingEquiv.refl K)).1 c, scalRep_apply]`. Simplify using the standard rewrite rules.

Unfold `clCond`. Introduce `τ hτ c`. Establish `h1 : τ = cE K` using `reflOdd_uniq hτ hσl`. Substitute `h1` using the available equality. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, one_smul]`.

Rewrite using `[hmk c]`. Set `Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) → ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l)` to `fun φ => ⟨_, hmem φ⟩`. Establish `hΦ : Function.Injective Φ`. Introduce `φ₁ φ₂ h`. Use `MonoidHom.ext fun q => ?_` and prove the remaining obligations.

Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H c`. Use `congrFun (congrArg Subtype.val h) c` as an intermediate fact. Simplify `this` using `[Φ]`. Establish `h1 : H.index ≤ Nat.card (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l))` using `hidx ▸ Nat.card_le_card_of_injective Φ hΦ`.

Establish `h2 : Nat.card (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)).invariants ≤ l` using `(Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (Nat.card_zmod l).le`. Establish `h3 : Nat.card ↥((ClTw K l (1 * (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K)))) ≤ Nat.card ↥(minK (clMap (cE K)) ⊓ torK (Cl K) l : Subgroup (Cl K))`. Apply `Subgroup.card_le_of_le` to reduce the goal to its premises. Introduce `c hc`. Take `⟨hc1, hc2⟩` from `Subgroup.mem_inf.mp hc`.

Use `Subgroup.mem_inf.mpr ⟨hc2, ?_⟩` and prove the remaining obligations. Use `show c ∈ (powMonoidHom l : Cl K →* Cl K).ker`. Conclude with `hc1.1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.FW.reflOdd :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (l : ℕ) [Fact l.Prime] (ζ : K), l ≠ 2 → IsPrimitiveRoot ζ l → (powR (Cl K) l ⊔ difR (clMap (cE K))).index ≤ l * Nat.card (minK (clMap (cE K)) ⊓ torK (Cl K) l : Subgroup (Cl K)) := by
  intro K _ _ _ l _ ζ hl2 hζ
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : Fact (1 < l) := ⟨hp.one_lt⟩
  have hodd : Odd l := hp.odd_of_ne_two hl2
  obtain ⟨σ, hσ⟩ := @exists_isConjOm K (AlgebraicClosure K) _ _ _ _ _
  have hσl : IsLift (cE K) σ := hσ.isLift
  have hchi : ∀ g : G K (AlgebraicClosure K),
      g (algebraMap K (AlgebraicClosure K) ζ) =
        (algebraMap K (AlgebraicClosure K) ζ) ^
          (((1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ) g : (ZMod l)ˣ) : ZMod l).val := by
    intro g
    rw [MonoidHom.one_apply, Units.val_one, ZMod.val_one, pow_one]
    exact g.commutes ζ
  have hR := reflect K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) l 1 ζ 1 1 σ rfl hodd hζ hchi hσ
  have hP := pullEq K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l)
    (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) one_ne_zero le_rfl (Or.inl (by infer_instance))
  have hinj := (pullMem K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l)
    one_ne_zero).2 le_rfl
  have heq := hP.2 (cE K) σ 1 hσl
  have hcardE := Nat.card_congr (Submodule.equivMapOfInjective _ hinj
    (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l))).toEquiv
  rw [heq] at hcardE
  set H : Subgroup (Cl K) := powR (Cl K) l ⊔ difR (clMap (cE K)) with hH
  have hidx := reflOdd_index l H le_sup_left
  have hmk : ∀ c : Cl K, (QuotientGroup.mk (clMap (cE K) c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    symm
    rw [QuotientGroup.eq_iff_div_mem]
    exact le_sup_right (a := powR (Cl K) l) (⟨c, rfl⟩ : c / clMap (cE K) c ∈ difR (clMap (cE K)))
  have hmem : ∀ φ : Cl K ⧸ H →* Multiplicative (ZMod l),
      (fun c : ClassGroup (𝓞 K) => Multiplicative.toAdd (φ (QuotientGroup.mk c))) ∈
        ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l) := by
    intro φ
    unfold ClEig ClEq
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g => ?_⟩, ?_⟩
    · unfold ClDual
      refine ⟨fun a b => ?_, fun v hv => ?_⟩
      · simp [QuotientGroup.mk_mul]
      · have hv' : ((1 : ℕ) : 𝓞 K) ∈ v.asIdeal := hv
        rw [Nat.cast_one] at hv'
        exact absurd ((Ideal.eq_top_iff_one _).mpr hv') v.isPrime.ne_top
    · unfold clCond
      intro τ hτ c
      have h1 : τ = RingEquiv.refl K := reflOdd_uniq hτ (fun x => g.commutes x)
      subst h1
      rw [(clMapBasic K K K (RingEquiv.refl K) (RingEquiv.refl K)).1 c, scalRep_apply]
      simp
    · unfold clCond
      intro τ hτ c
      have h1 : τ = cE K := reflOdd_uniq hτ hσl
      subst h1
      simp only [LinearMap.smul_apply, LinearMap.id_apply, one_smul]
      rw [hmk c]
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) →
      ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l) :=
    fun φ => ⟨_, hmem φ⟩
  have hΦ : Function.Injective Φ := by
    intro φ₁ φ₂ h
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      have := congrFun (congrArg Subtype.val h) c
      simpa [Φ] using this
  have h1 : H.index ≤ Nat.card
      (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l)) :=
    hidx ▸ Nat.card_le_card_of_injective Φ hΦ
  have h2 : Nat.card (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)).invariants ≤ l :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (Nat.card_zmod l).le
  have h3 : Nat.card ↥((ClTw K l (1 * (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)⁻¹) ⊓ ClMinus (cE K) :
      Subgroup (ClassGroup (𝓞 K)))) ≤
      Nat.card ↥(minK (clMap (cE K)) ⊓ torK (Cl K) l : Subgroup (Cl K)) := by
    apply Subgroup.card_le_of_le
    intro c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hc2, ?_⟩
    show c ∈ (powMonoidHom l : Cl K →* Cl K).ker
    exact hc1.1
  calc H.index ≤ _ := h1
    _ = _ := hcardE
    _ ≤ _ := hR
    _ ≤ l * _ := Nat.mul_le_mul h2 h3
