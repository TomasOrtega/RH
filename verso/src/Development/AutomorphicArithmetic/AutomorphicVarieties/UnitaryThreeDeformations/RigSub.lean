import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DyadicCharacterPowerNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_one (PadicInt.toZModPow n), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`.
-/
private theorem rs_dvd {l : ℕ} [Fact l.Prime] (n : ℕ) (a : ℤ_[l]) :
    PadicInt.toZModPow n a = 1 ↔ (l : ℤ_[l]) ^ n ∣ a - 1 := by
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow n), ← map_sub, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Use `(UpperTheory.V.Chr.clsFacts ℚ Ω (l ^ k)).2.2.1 σ 1 fun ζ hζ => ?_` and prove the remaining obligations. Establish `key` using `cyclotomicCharacter.spec (L := Ω) l (n := k) (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) ζ hζ`. Establish `h' : PadicInt.toZModPow k ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1` using `h`.

Rewrite `key` using `[h']`. Rewrite using `[Units.val_one]`. Conclude with `key`.
-/
private theorem rs_cls (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (k : ℕ)
    [NeZero (l ^ k)] (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (h : PadicInt.toZModPow k (cycZ ℚ Ω l σ : ℤ_[l]) = 1) :
    UpperTheory.V.Chr.cls ℚ Ω (l ^ k) σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω (l ^ k)).2.2.1 σ 1 fun ζ hζ => ?_
  have key := cyclotomicCharacter.spec (L := Ω) l (n := k)
    (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) ζ hζ
  have h' : PadicInt.toZModPow k ((cyclotomicCharacter Ω l
      (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := h
  rw [h'] at key
  rw [Units.val_one]
  exact key

/- English proof (translation)
Establish `key : ∀ x : O, IsUnit x ↔ IsLocalRing.residue O x ≠ 0` using `fun x => by`. Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Rewrite `h`, the goal using `[key]`. Establish `hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hO`. Use `haveI : CharP (IsLocalRing.ResidueField O) l := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hl.out hl0)`. Rewrite `h` using `[map_sub, map_one]`. Rewrite using `[map_sub, map_pow, map_one]`. Establish `e` using `sub_pow_char_pow (IsLocalRing.residue O y) 1 k (p := l)`.

Rewrite `e` using `[one_pow]`. Rewrite using `[← e]`. Conclude with `pow_ne_zero _ h`.
-/
private theorem rs_unit {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] (hO : ¬ IsUnit (l : O))
    (y : O) (k : ℕ) (h : IsUnit (y - 1)) : IsUnit (y ^ l ^ k - 1) := by
  have key : ∀ x : O, IsUnit x ↔ IsLocalRing.residue O x ≠ 0 := fun x => by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  rw [key] at h ⊢
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hO
  haveI : CharP (IsLocalRing.ResidueField O) l :=
    ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hl.out hl0)
  rw [map_sub, map_one] at h
  rw [map_sub, map_pow, map_one]
  have e := sub_pow_char_pow (IsLocalRing.residue O y) 1 k (p := l)
  rw [one_pow] at e
  rw [← e]
  exact pow_ne_zero _ h

/- English proof (translation)
Introduce `Ω iF iC iA l hl c N iN e ψ o₁ hD S A F hF`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Use `haveI : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.out.ne_zero⟩`. Take `⟨x, hx1, hx2, hx3⟩` from `UpperTheory.V.UnitaryThreeInertia.exists_sigma Ω c e ψ o₁ hD S A F hF F.vl (Set.mem_insert _ _)`.

Establish `hη : ∀ s : F.D F.vl, F.ηv F.vl s = UpperTheory.V.UnitaryThreeInertia.eta4 Ω (s : Formalism.ConjugateSelfDual.G ℚ Ω)` using `fun s => DFunLike.congr_fun hF.η _`. Establish `hΨ : ∀ s : F.D F.vl, F.Ψv F.vl s = UpperTheory.V.Chr.Psi l e (UpperTheory.V.Chr.dirG ℚ Ω ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω)` using `fun s => DFunLike.congr_fun hF.Ψ _`. Establish `hO : ¬ IsUnit (l : c.O)`. Introduce `hu`. Use `haveI := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1`.

Establish `h1 : IsUnit (algebraMap ℤ_[l] c.O (l : ℤ_[l]))` using `by rwa [map_natCast]`. Establish `h2` using `isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ h1`. Rewrite `h2` using `[PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one]`. Establish `h3 : (1 : ℝ) < l` using `by exact_mod_cast hl.out.one_lt`. Conclude with `absurd h2 (ne_of_gt h3)`.

Set `H : Subgroup (F.D F.vl)` to `(F.ηv F.vl).ker ⊓ ((UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ)).comp (F.D F.vl).subtype).ker`. Use `⟨H, inferInstance, ?_, inf_le_left, ?_, ?_⟩` and prove the remaining obligations. Set `K : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω)` to `(UpperTheory.V.Chr.cls ℚ Ω 4).ker ⊓ (UpperTheory.V.Chr.cls ℚ Ω N).ker`. Establish `hK : IsOpen (K : Set (Formalism.ConjugateSelfDual.G ℚ Ω))` using `(UpperTheory.V.Chr.clsFacts ℚ Ω 4).1.inter (UpperTheory.V.Chr.clsFacts ℚ Ω N).1`. Use `Subgroup.isOpen_mono (H₁ := K.comap (F.D F.vl).subtype) ?_ (by rw [Subgroup.coe_comap]; exact hK.preimage continuous_subtype_val)` and prove the remaining obligations.

Introduce `s hs`. Establish `hs'` using `Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hs)`. Establish `h4 : UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1` using `hs'.1`. Establish `hN : UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1` using `hs'.2`. Use `Subgroup.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker, hη] show MulChar.toUnitHom ZMod.χ₄ (UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1`. Rewrite using `[h4, map_one]`. Use `show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ) (UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1`. Rewrite using `[hN, map_one]`. Introduce `s hs hI`.

Establish `hs2 : UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1` using `(Subgroup.mem_inf.1 hs).2`. Establish `hI' : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (A F.vl)`. Establish `h0 : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ F.I F.vl` using `hI`. Rewrite `h0` using `[hF.I]`. Then use the resulting hypothesis. Establish `hv : (A F.vl).valuation (l : Ω) < 1`.

Use `(hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl` as an intermediate fact. Simplify using `using this`. Establish `hc` using `((UpperTheory.V.HV.compIne Ω N l hl.out (A F.vl) hv).2 c.O ψ).1 _ hI'`. Rewrite using `[hΨ, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, hc, hs2, mul_one]`. Use `first`.

Consider the case `exact MonoidHom.zpow_apply _ _ _`. Consider the case `simp [MonoidHom.zpow_apply, MonoidHom.pow_apply]`. Establish `hdx : (l : ℤ_[l]) ∣ ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1`. Establish `h1 : PadicInt.toZModPow 1 ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1` using `congrArg Units.val hx3`. Simplify using `using (rs_dvd 1 _).1 h1`.

Establish `hpow : (l : ℤ_[l]) ^ (N.factorization l + 1) ∣ ((cycZ ℚ Ω l ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1`. Rewrite using `[Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val]`. Use `dvd_sub_pow_of_dvd_sub hdx (N.factorization l)` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis. Establish `hg : UpperTheory.V.Chr.cls ℚ Ω (l ^ N.factorization l) ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) = 1` using `rs_cls Ω l (N.factorization l) _ ((rs_dvd _ _).2 (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) hpow))`.

Establish `hpr : UpperTheory.V.HV.proj l N (UpperTheory.V.Chr.cls ℚ Ω N ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1`. Rewrite using `[← MonoidHom.mem_ker, (UpperTheory.V.HV.projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker]`. Establish `hc` using `DFunLike.congr_fun ((UpperTheory.V.Chr.clsFacts ℚ Ω N).2.1 (l ^ N.factorization l) (Nat.ordProj_dvd N l)) ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)`. Rewrite `hc` using `[MonoidHom.comp_apply]`. Rewrite using `[hc]`.

Conclude with `hg`. Use `⟨x ^ l ^ N.factorization l, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, map_pow, hx1, one_pow]`. Use `show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ) (UpperTheory.V.Chr.cls ℚ Ω N ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1`. Simplify using `only [UpperTheory.V.HV.comp, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.comp_apply, hpr, map_one]`.

Rewrite using `[map_pow, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]`. Conclude with `rs_unit hO _ _ hx2`. Rewrite using `[PadicInt.norm_lt_one_iff_dvd]`. Conclude with `dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _)) hpow`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.rig_sub :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F → ∃ H : Subgroup (F.D F.vl), H.Normal ∧ IsOpen (H : Set (F.D F.vl)) ∧ H ≤ (F.ηv F.vl).ker ∧ (∀ s ∈ H, s ∈ F.Iv F.vl → F.Ψv F.vl s = UpperTheory.V.Base.chiO ℚ Ω l c.O (s : Formalism.ConjugateSelfDual.G ℚ Ω) ^ (e : ℤ)) ∧ ∃ g ∈ H, IsUnit ((F.Ψv F.vl g : c.O) ^ 2 - 1) ∧ ‖((cycZ ℚ Ω l (g : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  intro Ω iF iC iA l hl c N iN e ψ o₁ hD S A F hF
  haveI := c.dvr
  haveI := c.fin
  haveI : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    UpperTheory.V.UnitaryThreeInertia.exists_sigma Ω c e ψ o₁ hD S A F hF F.vl (Set.mem_insert _ _)
  have hη : ∀ s : F.D F.vl, F.ηv F.vl s = UpperTheory.V.UnitaryThreeInertia.eta4 Ω (s : Formalism.ConjugateSelfDual.G ℚ Ω) :=
    fun s => DFunLike.congr_fun hF.η _
  have hΨ : ∀ s : F.D F.vl, F.Ψv F.vl s =
      UpperTheory.V.Chr.Psi l e (UpperTheory.V.Chr.dirG ℚ Ω ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω) :=
    fun s => DFunLike.congr_fun hF.Ψ _
  have hO : ¬ IsUnit (l : c.O) := by
    intro hu
    haveI := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    have h1 : IsUnit (algebraMap ℤ_[l] c.O (l : ℤ_[l])) := by rwa [map_natCast]
    have h2 := isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ h1
    rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one] at h2
    have h3 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    exact absurd h2 (ne_of_gt h3)
  let H : Subgroup (F.D F.vl) := (F.ηv F.vl).ker ⊓
    ((UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ)).comp (F.D F.vl).subtype).ker
  refine ⟨H, inferInstance, ?_, inf_le_left, ?_, ?_⟩
  · let K : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω) := (UpperTheory.V.Chr.cls ℚ Ω 4).ker ⊓ (UpperTheory.V.Chr.cls ℚ Ω N).ker
    have hK : IsOpen (K : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) :=
      (UpperTheory.V.Chr.clsFacts ℚ Ω 4).1.inter (UpperTheory.V.Chr.clsFacts ℚ Ω N).1
    refine Subgroup.isOpen_mono (H₁ := K.comap (F.D F.vl).subtype) ?_
      (by rw [Subgroup.coe_comap]; exact hK.preimage continuous_subtype_val)
    intro s hs
    have hs' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hs)
    have h4 : UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 := hs'.1
    have hN : UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 := hs'.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, hη]
      show MulChar.toUnitHom ZMod.χ₄ (UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      rw [h4, map_one]
    · show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ) (UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      rw [hN, map_one]
  · intro s hs hI
    have hs2 : UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 :=
      (Subgroup.mem_inf.1 hs).2
    have hI' : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (A F.vl) := by
      have h0 : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ F.I F.vl := hI
      rwa [hF.I] at h0
    have hv : (A F.vl).valuation (l : Ω) < 1 := by
      have := (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
      simpa using this
    have hc := ((UpperTheory.V.HV.compIne Ω N l hl.out (A F.vl) hv).2 c.O ψ).1 _ hI'
    rw [hΨ, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, hc, hs2, mul_one]
    first
      | exact MonoidHom.zpow_apply _ _ _
      | simp [MonoidHom.zpow_apply, MonoidHom.pow_apply]
  · have hdx : (l : ℤ_[l]) ∣ ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      have h1 : PadicInt.toZModPow 1 ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
        congrArg Units.val hx3
      simpa using (rs_dvd 1 _).1 h1
    have hpow : (l : ℤ_[l]) ^ (N.factorization l + 1) ∣
        ((cycZ ℚ Ω l ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      rw [Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val]
      have := dvd_sub_pow_of_dvd_sub hdx (N.factorization l)
      rwa [one_pow] at this
    have hg : UpperTheory.V.Chr.cls ℚ Ω (l ^ N.factorization l)
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 :=
      rs_cls Ω l (N.factorization l) _
        ((rs_dvd _ _).2 (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) hpow))
    have hpr : UpperTheory.V.HV.proj l N (UpperTheory.V.Chr.cls ℚ Ω N
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1 := by
      rw [← MonoidHom.mem_ker, (UpperTheory.V.HV.projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker]
      have hc := DFunLike.congr_fun
        ((UpperTheory.V.Chr.clsFacts ℚ Ω N).2.1 (l ^ N.factorization l) (Nat.ordProj_dvd N l))
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)
      rw [MonoidHom.comp_apply] at hc
      rw [hc]
      exact hg
    refine ⟨x ^ l ^ N.factorization l, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_pow, hx1, one_pow]
    · show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ)
        (UpperTheory.V.Chr.cls ℚ Ω N ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      simp only [UpperTheory.V.HV.comp, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply, MonoidHom.comp_apply, hpr, map_one]
    · rw [map_pow, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]
      exact rs_unit hO _ _ hx2
    · rw [PadicInt.norm_lt_one_iff_dvd]
      exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _)) hpow
