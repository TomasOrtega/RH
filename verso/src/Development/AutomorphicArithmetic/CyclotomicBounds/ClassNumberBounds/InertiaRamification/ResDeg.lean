import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Decomp
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `h : K.relIndex (Subgroup.zpowers u) = orderOf (QuotientGroup.mk' K u)`. Rewrite using `[← Nat.card_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']`. Rewrite using `[Subgroup.relIndex_sup_right, h, orderOf_dvd_iff_pow_eq_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`.
-/
private theorem relIndex_zpowers_dvd_iff {G : Type*} [CommGroup G] (K : Subgroup G) (u : G)
    (k : ℕ) : K.relIndex (Subgroup.zpowers u ⊔ K) ∣ k ↔ u ^ k ∈ K := by
  have h : K.relIndex (Subgroup.zpowers u) = orderOf (QuotientGroup.mk' K u) := by
    rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.relIndex_ker,
      QuotientGroup.ker_mk']
  rw [Subgroup.relIndex_sup_right, h, orderOf_dvd_iff_pow_eq_one, ← map_pow,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [NeZero N] in
/- English proof (translation)
Simplify using `only [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, ← Units.val_eq_one, MulChar.coe_toUnitHom]`.
-/
private theorem mem_charKer_iff' (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  simp only [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, ← Units.val_eq_one,
    MulChar.coe_toUnitHom]

/- English proof (translation)
Take `⟨h1, h2⟩` from `localPart_eq_one_iff l ψ`. Rewrite using `[← h2, h1, mem_annihilator_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, fun u hu => h u (Subgroup.mem_sup_left hu)⟩` and prove the remaining obligations.

Rewrite using `[← (annihilator_charKer X ⊥).1, mem_annihilator_iff]`. Conclude with `fun u hu => h u (Subgroup.mem_sup_right hu)`. Introduce and unpack `⟨hX, hI⟩ u hu`. Take `⟨a, ha, b, hb, rfl⟩` from `Subgroup.mem_sup.1 hu`. Rewrite using `[Units.val_mul, map_mul, hI a ha, (mem_charKer_iff' X b).1 hb ψ hX, one_mul]`.
-/
private theorem mem_annihilator_inertia_sup (X : Subgroup (DirichletCharacter ℂ N))
    (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ ((inertiaUnits N l ⊔ charKer X : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) ↔
      ψ ∈ X ∧ ¬ l ∣ ψ.conductor := by
  obtain ⟨h1, h2⟩ := localPart_eq_one_iff l ψ
  rw [← h2, h1, mem_annihilator_iff]
  constructor
  · intro h
    refine ⟨?_, fun u hu => h u (Subgroup.mem_sup_left hu)⟩
    rw [← (annihilator_charKer X ⊥).1, mem_annihilator_iff]
    exact fun u hu => h u (Subgroup.mem_sup_right hu)
  · rintro ⟨hX, hI⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [Units.val_mul, map_mul, hI a ha, (mem_charKer_iff' X b).1 hb ψ hX, one_mul]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Take `⟨u, hu⟩` from `ZMod.unitsMap_surjective (Nat.ordCompl_dvd N l) (ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl (NeZero.ne N)))`. Use `⟨u, ?_, fun ψ hψ => ?_⟩` and prove the remaining obligations. Unfold `decompUnits inertiaUnits`. Rewrite using `[← hu, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq]`.

Establish `hc : ψ.conductor ∣ ordCompl[l] N` using `Nat.dvd_ordCompl_of_dvd_not_dvd ψ.conductor_dvd_level hψ`. Establish `hu' : (ZMod.cast (u : ZMod N) : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N))`. Use `congrArg Units.val hu` as an intermediate fact. Rewrite `this` using `[ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]`. Then use the resulting hypothesis. Establish `h2 : (ZMod.cast (u : ZMod N) : ZMod ψ.conductor) = (l : ZMod ψ.conductor)`.

Establish `e` using `congrArg (fun f : ZMod N →+* ZMod ψ.conductor => f (u : ZMod N)) (ZMod.castHom_comp hc (Nat.ordCompl_dvd N l))`. Simplify using `only [RingHom.comp_apply] at e`. Rewrite `e` using `[ZMod.castHom_apply (h := Nat.ordCompl_dvd N l), hu', map_natCast, ZMod.castHom_apply]`. Conclude with `e.symm`. Rewrite using `[← h2, ← changeLevel_eq_cast_of_dvd _ ψ.conductor_dvd_level, changeLevel_primitiveCharacter]`.
-/
private theorem exists_frobUnit :
    ∃ u : (ZMod N)ˣ, decompUnits N l = Subgroup.zpowers u ⊔ inertiaUnits N l ∧
      ∀ ψ : DirichletCharacter ℂ N, ¬ l ∣ ψ.conductor →
        ψ (u : ZMod N) = ψ.primitiveCharacter (l : ZMod ψ.conductor) := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Nat.ordCompl_dvd N l)
    (ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl (NeZero.ne N)))
  refine ⟨u, ?_, fun ψ hψ => ?_⟩
  · unfold decompUnits inertiaUnits
    rw [← hu, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq]
  · have hc : ψ.conductor ∣ ordCompl[l] N :=
      Nat.dvd_ordCompl_of_dvd_not_dvd ψ.conductor_dvd_level hψ
    have hu' : (ZMod.cast (u : ZMod N) : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N)) := by
      have := congrArg Units.val hu
      rwa [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at this
    have h2 : (ZMod.cast (u : ZMod N) : ZMod ψ.conductor) = (l : ZMod ψ.conductor) := by
      have e := congrArg (fun f : ZMod N →+* ZMod ψ.conductor => f (u : ZMod N))
        (ZMod.castHom_comp hc (Nat.ordCompl_dvd N l))
      simp only [RingHom.comp_apply] at e
      rw [ZMod.castHom_apply (h := Nat.ordCompl_dvd N l), hu', map_natCast,
        ZMod.castHom_apply] at e
      exact e.symm
    rw [← h2, ← changeLevel_eq_cast_of_dvd _ ψ.conductor_dvd_level, changeLevel_primitiveCharacter]

/- English proof (translation)
Unfold `resDeg`. Rewrite using `[hu, sup_assoc, relIndex_zpowers_dvd_iff, ← (annihilator_charKer ⊥ (inertiaUnits N l ⊔ charKer X)).2.1, mem_charKer_iff']`. Simplify using `only [mem_annihilator_inertia_sup, Units.val_pow_eq_pow_val, map_pow, and_imp]`.
-/
private theorem resDeg_dvd_iff_unit {u : (ZMod N)ˣ}
    (hu : decompUnits N l = Subgroup.zpowers u ⊔ inertiaUnits N l)
    (X : Subgroup (DirichletCharacter ℂ N)) (k : ℕ) :
    resDeg l X ∣ k ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor → ψ (u : ZMod N) ^ k = 1 := by
  unfold resDeg
  rw [hu, sup_assoc, relIndex_zpowers_dvd_iff,
    ← (annihilator_charKer ⊥ (inertiaUnits N l ⊔ charKer X)).2.1, mem_charKer_iff']
  simp only [mem_annihilator_inertia_sup, Units.val_pow_eq_pow_val, map_pow, and_imp]

/- English proof (translation)
Establish `hX1 : ∀ ψ ∈ X, localPart N l ψ = 1` using `fun ψ h => (localPart_eq_one_iff l ψ).2.2 (hX ψ h)`. Establish `hmap : (X ⊔ Y).map (localPart N l) = Y.map (localPart N l)`. Rewrite using `[Subgroup.map_sup, (Subgroup.map_eq_bot_iff X).2 (fun ψ h => hX1 ψ h), bot_sup_eq]`. Use `⟨?_, by unfold ramIdx; rw [hmap], by unfold vd; rw [hmap]⟩` and prove the remaining obligations. Take `⟨u, hu, -⟩` from `exists_frobUnit (N := N) l`.

Establish `key : ∀ k, resDeg l (X ⊔ Y) ∣ k ↔ Nat.lcm (resDeg l X) (resDeg l Y) ∣ k`. Introduce `k`. Rewrite using `[Nat.lcm_dvd_iff, resDeg_dvd_iff_unit l hu, resDeg_dvd_iff_unit l hu, resDeg_dvd_iff_unit l hu]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨fun ψ hψ => h ψ (Subgroup.mem_sup_left hψ), fun ψ hψ => h ψ (Subgroup.mem_sup_right hψ)⟩`.

Introduce and unpack `⟨h1, h2⟩ ψ hψ hc`. Take `⟨a, ha, b, hb, rfl⟩` from `Subgroup.mem_sup.1 hψ`. Establish `hb' : ¬ l ∣ b.conductor`. Use `(localPart_eq_one_iff l (a * b)).2.2 hc` as an intermediate fact. Rewrite `this` using `[map_mul, hX1 a ha, one_mul]`.

Conclude with `(localPart_eq_one_iff l b).2.1 this`. Rewrite using `[MulChar.mul_apply, mul_pow, h1 a ha (hX a ha), h2 b hb hb', one_mul]`. Conclude with `Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)`.
-/
theorem resDeg_sup (X Y : Subgroup (DirichletCharacter ℂ N)) (hX : ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) :
    resDeg l (X ⊔ Y) = Nat.lcm (resDeg l X) (resDeg l Y) ∧ ramIdx l (X ⊔ Y) = ramIdx l Y ∧
      vd l (X ⊔ Y) = vd l Y := by
  have hX1 : ∀ ψ ∈ X, localPart N l ψ = 1 := fun ψ h => (localPart_eq_one_iff l ψ).2.2 (hX ψ h)
  have hmap : (X ⊔ Y).map (localPart N l) = Y.map (localPart N l) := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff X).2 (fun ψ h => hX1 ψ h), bot_sup_eq]
  refine ⟨?_, by unfold ramIdx; rw [hmap], by unfold vd; rw [hmap]⟩
  obtain ⟨u, hu, -⟩ := exists_frobUnit (N := N) l
  have key : ∀ k, resDeg l (X ⊔ Y) ∣ k ↔ Nat.lcm (resDeg l X) (resDeg l Y) ∣ k := by
    intro k
    rw [Nat.lcm_dvd_iff, resDeg_dvd_iff_unit l hu, resDeg_dvd_iff_unit l hu,
      resDeg_dvd_iff_unit l hu]
    constructor
    · exact fun h => ⟨fun ψ hψ => h ψ (Subgroup.mem_sup_left hψ),
        fun ψ hψ => h ψ (Subgroup.mem_sup_right hψ)⟩
    · rintro ⟨h1, h2⟩ ψ hψ hc
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hψ
      have hb' : ¬ l ∣ b.conductor := by
        have := (localPart_eq_one_iff l (a * b)).2.2 hc
        rw [map_mul, hX1 a ha, one_mul] at this
        exact (localPart_eq_one_iff l b).2.1 this
      rw [MulChar.mul_apply, mul_pow, h1 a ha (hX a ha), h2 b hb hb', one_mul]
  exact Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)

/- English proof (translation)
Take `⟨u, hu, hv⟩` from `exists_frobUnit (N := N) l`. Establish `key : ∀ k, resDeg l (Subgroup.zpowers χ) ∣ k ↔ orderOf (χ (u : ZMod N)) ∣ k`. Introduce `k`. Rewrite using `[resDeg_dvd_iff_unit l hu, orderOf_dvd_iff_pow_eq_one]`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun h => h χ (Subgroup.mem_zpowers χ) hχ`. Introduce `h ψ hψ _`. Take `⟨m, rfl⟩` from `mem_powers_iff_mem_zpowers.2 hψ`. Use `show (χ ^ m) (u : ZMod N) ^ k = 1`. Rewrite using `[MulChar.pow_apply_coe, ← pow_mul, mul_comm, pow_mul, h, one_pow]`.

Rewrite using `[← hv χ hχ]`. Conclude with `Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)`.
-/
theorem resDeg_zpowers (χ : DirichletCharacter ℂ N) (hχ : ¬ l ∣ χ.conductor) :
    resDeg l (Subgroup.zpowers χ) = orderOf (χ.primitiveCharacter (l : ZMod χ.conductor)) := by
  obtain ⟨u, hu, hv⟩ := exists_frobUnit (N := N) l
  have key : ∀ k, resDeg l (Subgroup.zpowers χ) ∣ k ↔ orderOf (χ (u : ZMod N)) ∣ k := by
    intro k
    rw [resDeg_dvd_iff_unit l hu, orderOf_dvd_iff_pow_eq_one]
    constructor
    · exact fun h => h χ (Subgroup.mem_zpowers χ) hχ
    · intro h ψ hψ _
      obtain ⟨m, rfl⟩ := mem_powers_iff_mem_zpowers.2 hψ
      show (χ ^ m) (u : ZMod N) ^ k = 1
      rw [MulChar.pow_apply_coe, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  rw [← hv χ hχ]
  exact Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)

end KStar.Ram
