import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Rewrite using `[← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]`. Conclude with `Nat.prime_iff_prime_int.mp hl`.
-/
private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : Pl where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

/- English proof (translation)
Establish `hI : (Ideal.span {((n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ 0`. Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hn` after adjusting the coercions. Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Simplify using `only [Set.mem_setOf_eq] at hv ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hv`.
-/
private theorem fin_above {n : ℕ} (hn : n ≠ 0) : {v : Pl | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {((n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact hv

/- English proof (translation)
Take `⟨hopen, -, -, -, hine⟩` from `Chr.clsFacts ℚ Ω M`. Take `⟨-, -, -, hpl⟩` from `Kum.placeDict ℚ Ω`. Establish `hle : NS Ω S ≤ (Chr.cls ℚ Ω M).ker`. Apply `Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises.

Introduce `σ hσ`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at hσ`. Take `⟨v, hv, A, hA, hσA⟩` from `hσ`. Establish `hn : ¬ A.valuation ((M : ℕ) : Ω) < 1`. Rewrite using `[hpl A v M hA]`.

Conclude with `hS v hv`. Conclude with `hine A hn hσA`. Conclude with `⟨QuotientGroup.lift (NS Ω S) (Chr.cls ℚ Ω M) hle, QuotientGroup.lift_comp_mk' _ _ _⟩`.
-/
private theorem cls_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (S : Set Pl)
    (hS : ∀ v ∉ S, ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ μ : GS Ω S →* (ZMod M)ˣ, μ.comp (toGS Ω S) = Chr.cls ℚ Ω M := by
  obtain ⟨hopen, -, -, -, hine⟩ := Chr.clsFacts ℚ Ω M
  obtain ⟨-, -, -, hpl⟩ := Kum.placeDict ℚ Ω
  have hle : NS Ω S ≤ (Chr.cls ℚ Ω M).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hn : ¬ A.valuation ((M : ℕ) : Ω) < 1 := by
      rw [hpl A v M hA]
      exact hS v hv
    exact hine A hn hσA
  exact ⟨QuotientGroup.lift (NS Ω S) (Chr.cls ℚ Ω M) hle, QuotientGroup.lift_comp_mk' _ _ _⟩

/- English proof (translation)
Take `⟨σ, j, hj⟩` from `exists_isConjOm (E := ℚ) (Ω := Ω)`. Conclude with `⟨AlgEquiv.ofRingEquiv (f := σ) (fun q => by simp), j, fun x => hj x⟩`.
-/
private theorem cc_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, j, hj⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) (fun q => by simp), j, fun x => hj x⟩

end

/- English proof (translation)
Introduce `Ω _ _ _ l _ c N _ e ψ o₁ hd`. Establish `hl : l.Prime` using `Fact.out`. Establish `hlN : l * N ≠ 0` using `Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)`. Use `set S : Finset Pl := (fin_above hlN).toFinset with hSdef`. Establish `hmem : ∀ v : Pl, v ∈ S ↔ (((l * N : ℕ)) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal` using `fun v => Set.Finite.mem_toFinset _`.

Establish `hout : ∀ m : ℕ, m ∣ l * N → ∀ v ∉ (S : Set Pl), ((m : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal`. Introduce `m hm v hv hmv`. Apply `hv` to reduce the goal to its premises. Rewrite using `[Finset.mem_coe, hmem]`. Take `⟨k, hk⟩` from `hm`.

Rewrite using `[hk, Nat.cast_mul]`. Conclude with `v.asIdeal.mul_mem_right _ hmv`. Establish `h4 : ∀ v ∉ (S : Set Pl), ((4 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal`. Introduce `v hv h4v`. Establish `h2 : ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal`.

Establish `h22 : ((4 : ℕ) : NumberField.RingOfIntegers ℚ) = ((2 : ℕ) : NumberField.RingOfIntegers ℚ) * ((2 : ℕ) : NumberField.RingOfIntegers ℚ)`. Rewrite using `[← Nat.cast_mul]`. Rewrite `h4v` using `[h22]`. Apply the tactic sequence `rcases v.isPrime.mem_or_mem h4v with h | h <;> exact h`. Conclude with `hout 2 (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hd.N_even) l) v hv h2`.

Take `⟨μN, hμN⟩` from `cls_exists Ω N (S : Set Pl) (hout N (dvd_mul_left N l))`. Take `⟨μ4, hμ4⟩` from `cls_exists Ω 4 (S : Set Pl) h4`. Take `⟨χl, hχl⟩` from `Formalism.GaloisCohomology.chi_exists (F := ℚ) (Ω := Ω) l (S : Set Pl) (hout l (dvd_mul_right l N))`. Take `⟨σ, hσ⟩` from `cc_exists Ω`. Set `A : S → ValuationSubring Ω` to `fun v => Classical.choose (exists_isPlaceOver Ω (v : Pl))`.

Establish `hA` using `fun v : S => Classical.choose_spec (exists_isPlaceOver Ω (v : Pl))`. Establish `hvl : vQ hl ∈ S`. Rewrite using `[hmem]`. Conclude with `Ideal.mem_span_singleton.mpr ⟨(N : NumberField.RingOfIntegers ℚ), by push_cast; ring⟩`. Set `F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S` to `{ π := toGS Ω (S : Set Pl) η := (MulChar.toUnitHom ZMod.χ₄).comp μ4 Ψ := ((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e * (MulChar.toUnitHom ψ).comp μN c := toGS Ω (S : Set Pl) σ D := fun v => Dec (A v) I := fun v => Ine (A v) vl := ⟨vQ hl, hvl⟩ Sb := {v | ∃ p ∈ …`.

Use `⟨S, A, F, ?_⟩` and prove the remaining obligations. Use `⟨hmem, hA, rfl, ?_, ?_, ⟨σ, hσ, rfl⟩, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩` and prove the remaining obligations. Use `show ((MulChar.toUnitHom ZMod.χ₄).comp μ4).comp (toGS Ω (S : Set Pl)) = eta4 Ω`. Rewrite using `[MonoidHom.comp_assoc, hμ4]`. Unfold `eta4 UpperTheory.V.Chr.dirG`.

Both sides reduce to the same expression. Use `show (((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e * (MulChar.toUnitHom ψ).comp μN).comp (toGS Ω (S : Set Pl)) = _`. Unfold `UpperTheory.V.Chr.Psi UpperTheory.V.Chr.dirG UpperTheory.V.Base.chiO`. Rewrite using `[← hχl, ← hμN]`. Use extensionality with `τ`.

Simplify using the standard rewrite rules. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.exists_hostFrame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∃ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hd
  have hl : l.Prime := Fact.out
  have hlN : l * N ≠ 0 := Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)
  set S : Finset Pl := (fin_above hlN).toFinset with hSdef
  have hmem : ∀ v : Pl, v ∈ S ↔ (((l * N : ℕ)) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    fun v => Set.Finite.mem_toFinset _
  have hout : ∀ m : ℕ, m ∣ l * N → ∀ v ∉ (S : Set Pl),
      ((m : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro m hm v hv hmv
    apply hv
    rw [Finset.mem_coe, hmem]
    obtain ⟨k, hk⟩ := hm
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hmv
  have h4 : ∀ v ∉ (S : Set Pl), ((4 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro v hv h4v
    have h2 : ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
      have h22 : ((4 : ℕ) : NumberField.RingOfIntegers ℚ) =
          ((2 : ℕ) : NumberField.RingOfIntegers ℚ) * ((2 : ℕ) : NumberField.RingOfIntegers ℚ) := by
        rw [← Nat.cast_mul]
      rw [h22] at h4v
      rcases v.isPrime.mem_or_mem h4v with h | h <;> exact h
    exact hout 2 (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hd.N_even) l) v hv h2
  obtain ⟨μN, hμN⟩ := cls_exists Ω N (S : Set Pl) (hout N (dvd_mul_left N l))
  obtain ⟨μ4, hμ4⟩ := cls_exists Ω 4 (S : Set Pl) h4
  obtain ⟨χl, hχl⟩ :=
    Formalism.GaloisCohomology.chi_exists (F := ℚ) (Ω := Ω) l (S : Set Pl) (hout l (dvd_mul_right l N))
  obtain ⟨σ, hσ⟩ := cc_exists Ω
  let A : S → ValuationSubring Ω := fun v => Classical.choose (exists_isPlaceOver Ω (v : Pl))
  have hA := fun v : S => Classical.choose_spec (exists_isPlaceOver Ω (v : Pl))
  have hvl : vQ hl ∈ S := by
    rw [hmem]
    exact Ideal.mem_span_singleton.mpr ⟨(N : NumberField.RingOfIntegers ℚ), by push_cast; ring⟩
  let F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S :=
    { π := toGS Ω (S : Set Pl)
      η := (MulChar.toUnitHom ZMod.χ₄).comp μ4
      Ψ := ((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN
      c := toGS Ω (S : Set Pl) σ
      D := fun v => Dec (A v)
      I := fun v => Ine (A v)
      vl := ⟨vQ hl, hvl⟩
      Sb := {v | ∃ p ∈ Sb l ψ, (p : NumberField.RingOfIntegers ℚ) ∈ (v : Pl).asIdeal} }
  refine ⟨S, A, F, ?_⟩
  refine ⟨hmem, hA, rfl, ?_, ?_, ⟨σ, hσ, rfl⟩, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩
  · show ((MulChar.toUnitHom ZMod.χ₄).comp μ4).comp (toGS Ω (S : Set Pl)) = eta4 Ω
    rw [MonoidHom.comp_assoc, hμ4]
    unfold eta4 UpperTheory.V.Chr.dirG
    rfl
  · show (((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN).comp (toGS Ω (S : Set Pl)) = _
    unfold UpperTheory.V.Chr.Psi UpperTheory.V.Chr.dirG UpperTheory.V.Base.chiO
    rw [← hχl, ← hμN]
    ext τ
    simp
  · exact Ideal.mem_span_singleton_self _
