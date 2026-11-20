import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Apply `Units.ext` to reduce the goal to its premises. Use `show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1`. Rewrite using `[cyclotomicCharacter.toZModPow]`.

Use `symm`. Apply `modularCyclotomicCharacter.unique` to reduce the goal to its premises. Introduce `t ht`. Establish `ht' : (t : Ω) ^ l = 1`. Use `congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)` as an intermediate fact.

Simplify using `using this`. Establish `hl1 : l ^ 1 ≠ 1`. Use `hl.out.one_lt` as an intermediate fact. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[ZMod.val_one'' hl1, pow_one]`. Conclude with `hs _ ht'`.
-/
private theorem ax_cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  apply Units.ext
  show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ l = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)
    simpa using this
  have hl1 : l ^ 1 ≠ 1 := by
    have := hl.out.one_lt
    rw [pow_one]
    omega
  rw [ZMod.val_one'' hl1, pow_one]
  exact hs _ ht'

/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ`. Take `⟨a, hη, hbar⟩` from `hG.cyc`. Establish `hM` using `hG.M_ne`. Establish `hlM` using `hG.l_dvd`. Establish `hL : M ^ (a + 1) * Q ≠ 0` using `mul_ne_zero (pow_ne_zero _ hM) hQ`.

Take `⟨w, hw, hwgt, hw1⟩` from `Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL`. Establish `hMaL : M ^ a ∣ M ^ (a + 1) * Q` using `Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q`. Establish `hlL : l ∣ M ^ (a + 1) * Q` using `dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))`. Establish `hML : M ∣ M ^ (a + 1) * Q` using `dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)`. Establish `hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m`.

Introduce `m hm hwm`. Establish `h1` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm`. Establish `h2` using `Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm`. Use linear arithmetic over natural numbers and integers. Use `⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩` and prove the remaining obligations.

Introduce `B' hB' s hs`. Use `haveI := Fact.mk hw`. Establish `fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ`. Introduce `m hm`. Establish `hcop : m.Coprime w` using `((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm`.

Take `⟨k, hk⟩` from `UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs`. Introduce `ζ hζ`. Rewrite using `[hk ζ hζ]`. Establish `hwk : w ^ k ≡ 1 [MOD m]`. Use `(Nat.ModEq.of_dvd hm hw1).pow k` as an intermediate fact.

Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis. Rewrite using `[pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `hη s (fix _ hMaL)`. Conclude with `hbar s (fix _ hMaL)`.

Rewrite using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(Units.map _) ((cycMod ℚ Ω l 1) s) = 1`. Rewrite using `[ax_cycMod_one l (fix l hlL), map_one]`.
-/
theorem UpperTheory.V.Fr.auxw_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → ∃ w, FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨a, hη, hbar⟩ := hG.cyc
  have hM := hG.M_ne
  have hlM := hG.l_dvd
  have hL : M ^ (a + 1) * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hM) hQ
  obtain ⟨w, hw, hwgt, hw1⟩ := Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL
  have hMaL : M ^ a ∣ M ^ (a + 1) * Q := Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q
  have hlL : l ∣ M ^ (a + 1) * Q :=
    dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))
  have hML : M ∣ M ^ (a + 1) * Q := dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)
  have hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m := by
    intro m hm hwm
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm
    omega
  refine ⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩
  intro B' hB' s hs
  haveI := Fact.mk hw
  have fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ := by
    intro m hm
    have hcop : m.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs
    intro ζ hζ
    rw [hk ζ hζ]
    have hwk : w ^ k ≡ 1 [MOD m] := by
      have := (Nat.ModEq.of_dvd hm hw1).pow k
      rwa [one_pow] at this
    rw [pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact hη s (fix _ hMaL)
  · exact hbar s (fix _ hMaL)
  · rw [MonoidHom.mem_ker]
    change (Units.map _) ((cycMod ℚ Ω l 1) s) = 1
    rw [ax_cycMod_one l (fix l hlL), map_one]
