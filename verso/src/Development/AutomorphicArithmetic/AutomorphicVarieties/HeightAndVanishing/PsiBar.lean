import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem cc_iff {Ω : Type} [Field Ω] [CharZero Ω] (σ : G ℚ Ω) : IsCC σ ↔ IsConjOm σ.toRingEquiv := Iff.rfl

private noncomputable def dirHom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    DirichletCharacter O N →* (G ℚ Ω →* Oˣ) :=
  MonoidHom.mk' (Chr.dirG ℚ Ω) fun χ χ' => by
    ext σ
    simp [Chr.dirG]

/- English proof (translation)
Introduce `χ χ' h`. Rewrite using `[← DirichletCharacter.toUnitHom_inj]`. Use extensionality with `u`. Take `⟨σ, rfl⟩` from `(Chr.clsOnto Ω N).1 u`. Conclude with `congrArg Units.val (DFunLike.congr_fun h σ)`.
-/
private theorem dirHom_inj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    Function.Injective (dirHom Ω O N) := by
  intro χ χ' h
  rw [← DirichletCharacter.toUnitHom_inj]
  ext u
  obtain ⟨σ, rfl⟩ := (Chr.clsOnto Ω N).1 u
  exact congrArg Units.val (DFunLike.congr_fun h σ)

/- English proof (translation)
Introduce `σ hσ`. Rewrite `hσ`, the goal using `[MonoidHom.mem_ker]`. Establish `hl : l.Prime` using `Fact.out`. Distinguish the cases in `hlN : l ∣ N`. Establish `hpos : 0 < orderOf ψ` using `orderOf_pos ψ`.

Establish `hord : ¬ l ∣ orderOf (th0 l ψ)` using `(partOrd _ l hl ψ hpos).2.2.1`. Establish `hord2 : ¬ l ∣ orderOf (comp l (th0 l ψ))` using `fun h => hord (dvd_trans h ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.1)`. Establish `hcond : (comp l (th0 l ψ)).conductor ∣ l` using `((compOrd O N (th0 l ψ) l hl).2.2.1 hord2).2`. Establish `hft : (comp l (th0 l ψ)).FactorsThrough l` using `DirichletCharacter.FactorsThrough.mono _ (DirichletCharacter.factorsThrough_conductor _) hcond hlN`. Establish `hk` using `(DirichletCharacter.factorsThrough_iff_ker_unitsMap hlN).1 hft`.

Establish `hmap : ZMod.unitsMap hlN (Chr.cls ℚ Ω N σ) = 1`. Use `DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) σ` as an intermediate fact. Rewrite `this` using `[MonoidHom.comp_apply]`. Rewrite using `[this, hσ]`. Conclude with `hk (MonoidHom.mem_ker.2 hmap)`.

Establish `h1 : comp l (th0 l ψ) = 1` using `((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.2.1 hlN`. Rewrite using `[h1]`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((MulChar.toUnitHom (1 : DirichletCharacter O N)) (Chr.cls ℚ Ω N σ) : O) = 1`. Rewrite using `[MulChar.coe_toUnitHom]`.

Simplify using the standard rewrite rules.
-/
private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) :
    (Chr.cls ℚ Ω l).ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  have hl : l.Prime := Fact.out
  by_cases hlN : l ∣ N
  · have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hord : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl ψ hpos).2.2.1
    have hord2 : ¬ l ∣ orderOf (comp l (th0 l ψ)) := fun h =>
      hord (dvd_trans h ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.1)
    have hcond : (comp l (th0 l ψ)).conductor ∣ l := ((compOrd O N (th0 l ψ) l hl).2.2.1 hord2).2
    have hft : (comp l (th0 l ψ)).FactorsThrough l :=
      DirichletCharacter.FactorsThrough.mono _ (DirichletCharacter.factorsThrough_conductor _) hcond hlN
    have hk := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hlN).1 hft
    have hmap : ZMod.unitsMap hlN (Chr.cls ℚ Ω N σ) = 1 := by
      have := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) σ
      rw [MonoidHom.comp_apply] at this
      rw [this, hσ]
    exact hk (MonoidHom.mem_ker.2 hmap)
  · have h1 : comp l (th0 l ψ) = 1 := ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.2.1 hlN
    rw [h1]
    apply Units.ext
    show ((MulChar.toUnitHom (1 : DirichletCharacter O N)) (Chr.cls ℚ Ω N σ) : O) = 1
    rw [MulChar.coe_toUnitHom]
    simp

/- English proof (translation)
Establish `hcyc : chiO ℚ Ω l O σ = -1`. Establish `h1 : cycZ ℚ Ω l σ = -1` using `IsConjOm.cyc (E := ℚ) h`. Simplify using `only [chiO, MonoidHom.comp_apply, h1]`. Use `ext`. Simplify using the standard rewrite rules.

Establish `hcls : Chr.cls ℚ Ω N σ = -1` using `(Chr.clsFacts ℚ Ω N).2.2.2.1 σ h`. Establish `hinv : ((-1 : Oˣ) ^ e)⁻¹ = (-1) ^ e` using `by rw [← inv_pow, inv_neg_one]`. Establish `hz : (chiO ℚ Ω l O ^ (e : ℤ)) σ = (-1) ^ e`. Rewrite using `[zpow_natCast, MonoidHom.pow_apply, hcyc]`. Simplify using `only [Chr.Psi, MonoidHom.mul_apply, hz, Chr.dirG, MonoidHom.comp_apply, hcls, PsiEven]`.

Rewrite using `[mul_eq_one_iff_eq_inv', hinv, ← Units.val_inj, MulChar.coe_toUnitHom]`. Simplify using the standard rewrite rules.
-/
private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv) :
    Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 ↔ PsiEven e ψ := by
  have hcyc : chiO ℚ Ω l O σ = -1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := IsConjOm.cyc (E := ℚ) h
    simp only [chiO, MonoidHom.comp_apply, h1]
    ext
    simp
  have hcls : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have hinv : ((-1 : Oˣ) ^ e)⁻¹ = (-1) ^ e := by rw [← inv_pow, inv_neg_one]
  have hz : (chiO ℚ Ω l O ^ (e : ℤ)) σ = (-1) ^ e := by
    rw [zpow_natCast, MonoidHom.pow_apply, hcyc]
  simp only [Chr.Psi, MonoidHom.mul_apply, hz, Chr.dirG, MonoidHom.comp_apply, hcls, PsiEven]
  rw [mul_eq_one_iff_eq_inv', hinv, ← Units.val_inj, MulChar.coe_toUnitHom]
  simp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c w hw N _ ψ`. Establish `hl : l.Prime` using `Fact.out`. Establish `cf` using `congrFacts Ω l c`. Establish `hmul : ∀ a a' : DirichletCharacter c.O N, Chr.dirG ℚ Ω (a * a') = Chr.dirG ℚ Ω a * Chr.dirG ℚ Ω a'` using `fun a a' => map_mul (dirHom Ω c.O N) a a'`. Establish `hpw : ∀ (a : DirichletCharacter c.O N) (n : ℕ), Chr.dirG ℚ Ω (a ^ n) = Chr.dirG ℚ Ω a ^ n` using `fun a n => map_pow (dirHom Ω c.O N) a n`.

Establish `hone : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1` using `map_one (dirHom Ω c.O N)`. Take `⟨_, hwc⟩` from `hw`. Establish `hfacts` using `(omT Ω l c).2 w ⟨‹_›, hwc⟩`. Establish `hker : w.ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker`. Rewrite using `[hfacts.2.1]`.

Conclude with `ker_le Ω l ψ`. Take `⟨b, hb, hbeq⟩` from `hfacts.2.2.2.2.2.2.2 _ hker`. Use `⟨⟨b, hb, hbeq, fun e => ?_⟩, ?_, orderOf_injective (dirHom Ω c.O N) (dirHom_inj Ω c.O N) ψ, fun ψ' => ⟨hmul ψ ψ', fun h => dirHom_inj Ω c.O N h⟩⟩` and prove the remaining obligations. Establish `hdec : ψ = comp l (th0 l ψ) * chiP l ψ * kap l ψ`. Rewrite using `[chiP, mul_comm (th0 l ψ), mul_inv_cancel_left, dirichletPrimeToLPart_mul_lPowerPart]`.

Establish `hψ' : Chr.dirG ℚ Ω ψ = w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * Chr.dirG ℚ Ω (kap l ψ)` using `by conv_lhs => rw [hdec]`. Rewrite using `[hmul, hmul, hbeq]`. Establish `hpos : 0 < orderOf ψ` using `orderOf_pos ψ`. Establish `hkord` using `(partOrd _ l hl ψ hpos).1`. Establish `hkap : Congr c (Chr.dirG ℚ Ω (kap l ψ)) 1`.

Apply `cf.2.2.1 _ ((orderOf ψ).factorization l)` to reduce the goal to its premises. Rewrite using `[← hpw, show kap l ψ = lPart l ψ from rfl, ← hkord, pow_orderOf_eq_one, hone]`. Establish `hcw : Congr c (chiO ℚ Ω l c.O) w` using `cf.1.symm hwc`. Establish `hpowc : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp only [pow_zero]`. Conclude with `cf.1.refl _`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `(cf.2.1 _ _ _ _ ih hcw).1`.

Establish `h2` using `(cf.2.1 _ _ _ _ (hpowc e) (cf.2.1 _ _ _ _ (cf.1.refl (w ^ b * Chr.dirG ℚ Ω (chiP l ψ))) hkap).1).1`. Use `show Congr c (chiO ℚ Ω l c.O ^ (e : ℤ) * Chr.dirG ℚ Ω ψ) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))`. Rewrite using `[zpow_natCast, hψ', show w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ) = w ^ e * (w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * 1) by rw [mul_one, pow_add, mul_assoc]]`. Conclude with `h2`. Introduce `e`.

Prove the components needed by the constructor for the conclusion. Introduce `hE σ hσ`. Conclude with `(psi_cc Ω l ψ e ((cc_iff σ).1 hσ)).2 hE`. Introduce `hall`. Take `⟨σ0, hσ0⟩` from `exists_isConjOm (E := ℚ) (Ω := Ω)`.

Set `σ : G ℚ Ω` to `AlgEquiv.ofRingEquiv (f := σ0) (fun q => by simp)`. Establish `hσ : IsConjOm σ.toRingEquiv` using `hσ0`. Conclude with `(psi_cc Ω l ψ e hσ).1 (hall σ ((cc_iff σ).2 hσ))`.
-/
theorem UpperTheory.V.HV.psiBar :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (w : G ℚ Ω →* c.Oˣ), IsOmT c w → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N),
      (∃ b < l - 1, Chr.dirG ℚ Ω (comp l (th0 l ψ)) = w ^ b ∧
        ∀ e : ℕ, Congr c (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))) ∧
      (∀ e : ℕ, PsiEven e ψ ↔ ∀ σ : G ℚ Ω, IsCC σ → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1) ∧
      orderOf (Chr.dirG ℚ Ω ψ) = orderOf ψ ∧
      ∀ ψ' : DirichletCharacter c.O N, Chr.dirG ℚ Ω (ψ * ψ') = Chr.dirG ℚ Ω ψ * Chr.dirG ℚ Ω ψ' ∧ (Chr.dirG ℚ Ω ψ = Chr.dirG ℚ Ω ψ' → ψ = ψ') := by
  intro Ω _ _ _ l _ c w hw N _ ψ
  have hl : l.Prime := Fact.out
  have cf := congrFacts Ω l c
  have hmul : ∀ a a' : DirichletCharacter c.O N,
      Chr.dirG ℚ Ω (a * a') = Chr.dirG ℚ Ω a * Chr.dirG ℚ Ω a' := fun a a' => map_mul (dirHom Ω c.O N) a a'
  have hpw : ∀ (a : DirichletCharacter c.O N) (n : ℕ),
      Chr.dirG ℚ Ω (a ^ n) = Chr.dirG ℚ Ω a ^ n := fun a n => map_pow (dirHom Ω c.O N) a n
  have hone : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := map_one (dirHom Ω c.O N)
  obtain ⟨_, hwc⟩ := hw
  have hfacts := (omT Ω l c).2 w ⟨‹_›, hwc⟩
  have hker : w.ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
    rw [hfacts.2.1]; exact ker_le Ω l ψ
  obtain ⟨b, hb, hbeq⟩ := hfacts.2.2.2.2.2.2.2 _ hker
  refine ⟨⟨b, hb, hbeq, fun e => ?_⟩, ?_, orderOf_injective (dirHom Ω c.O N) (dirHom_inj Ω c.O N) ψ,
    fun ψ' => ⟨hmul ψ ψ', fun h => dirHom_inj Ω c.O N h⟩⟩
  · have hdec : ψ = comp l (th0 l ψ) * chiP l ψ * kap l ψ := by
      rw [chiP, mul_comm (th0 l ψ), mul_inv_cancel_left, dirichletPrimeToLPart_mul_lPowerPart]
    have hψ' : Chr.dirG ℚ Ω ψ = w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * Chr.dirG ℚ Ω (kap l ψ) := by
      conv_lhs => rw [hdec]
      rw [hmul, hmul, hbeq]
    have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hkord := (partOrd _ l hl ψ hpos).1
    have hkap : Congr c (Chr.dirG ℚ Ω (kap l ψ)) 1 := by
      apply cf.2.2.1 _ ((orderOf ψ).factorization l)
      rw [← hpw, show kap l ψ = lPart l ψ from rfl, ← hkord, pow_orderOf_eq_one, hone]
    have hcw : Congr c (chiO ℚ Ω l c.O) w := cf.1.symm hwc
    have hpowc : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n) := by
      intro n
      induction n with
      | zero => simp only [pow_zero]; exact cf.1.refl _
      | succ n ih => rw [pow_succ, pow_succ]; exact (cf.2.1 _ _ _ _ ih hcw).1
    have h2 := (cf.2.1 _ _ _ _ (hpowc e)
      (cf.2.1 _ _ _ _ (cf.1.refl (w ^ b * Chr.dirG ℚ Ω (chiP l ψ))) hkap).1).1
    show Congr c (chiO ℚ Ω l c.O ^ (e : ℤ) * Chr.dirG ℚ Ω ψ) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))
    rw [zpow_natCast, hψ', show w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ)
      = w ^ e * (w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * 1) by rw [mul_one, pow_add, mul_assoc]]
    exact h2
  · intro e
    constructor
    · intro hE σ hσ
      exact (psi_cc Ω l ψ e ((cc_iff σ).1 hσ)).2 hE
    · intro hall
      obtain ⟨σ0, hσ0⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
      let σ : G ℚ Ω := AlgEquiv.ofRingEquiv (f := σ0) (fun q => by simp)
      have hσ : IsConjOm σ.toRingEquiv := hσ0
      exact (psi_cc Ω l ψ e hσ).1 (hall σ ((cc_iff σ).2 hσ))
