import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.IsImagQuad
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Duality

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Establish `h1 : ψ ∈ condDvd N m ↔ ψ.FactorsThrough (Nat.gcd N m)`. Rewrite using `[factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left N m), condDvd, mem_annihilator_iff]`. Use `⟨fun h x hx => ?_, fun h x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Conclude with `h x hx`.

Use `h hx` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Then use the resulting hypothesis. Rewrite using `[h1, ← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left N m), Nat.dvd_gcd_iff]`. Conclude with `⟨fun h => h.2, fun h => ⟨ψ.conductor_dvd_level, h⟩⟩`.
-/
private theorem mem_conductorDvd_iff (m : ℕ) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ condDvd N m ↔ ψ.conductor ∣ m := by
  have h1 : ψ ∈ condDvd N m ↔ ψ.FactorsThrough (Nat.gcd N m) := by
    rw [factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left N m), condDvd, mem_annihilator_iff]
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact h x hx
    · have := h hx
      rwa [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at this
  rw [h1, ← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left N m),
    Nat.dvd_gcd_iff]
  exact ⟨fun h => h.2, fun h => ⟨ψ.conductor_dvd_level, h⟩⟩

/- English proof (translation)
Rewrite using `[fieldCond, Finset.lcm_dvd_iff]`. Use `⟨fun h ψ hψ => (mem_conductorDvd_iff m ψ).2 (h ψ ?_), fun h ψ hψ => (mem_conductorDvd_iff m ψ).1 (h ?_)⟩` and prove the remaining obligations. Simplify using `using hψ`. Simplify using `using hψ`.
-/
private theorem fieldConductor_dvd_iff (X : Subgroup (DirichletCharacter ℂ N)) (m : ℕ) :
    fieldCond X ∣ m ↔ X ≤ condDvd N m := by
  rw [fieldCond, Finset.lcm_dvd_iff]
  refine ⟨fun h ψ hψ => (mem_conductorDvd_iff m ψ).2 (h ψ ?_), fun h ψ hψ =>
    (mem_conductorDvd_iff m ψ).1 (h ?_)⟩
  · simpa using hψ
  · simpa using hψ

/- English proof (translation)
Use `⟨mem_conductorDvd_iff m ψ, fun hm => ?_⟩` and prove the remaining obligations. Establish `: NeZero m` using `⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hm))⟩`. Establish `h : condDvd N m = (changeLevel (R` using `ℂ) hm).range := by`. Use extensionality with `χ`. Rewrite using `[mem_conductorDvd_iff, ← mem_conductorSet_iff_conductor_dvd _ hm, mem_conductorSet_iff, MonoidHom.mem_range]`.

Use `⟨fun ⟨_, χ₀, h⟩ => ⟨χ₀, h.symm⟩, fun ⟨χ₀, h⟩ => ⟨hm, χ₀, h.symm⟩⟩` and prove the remaining obligations. Rewrite using `[h, ← card_eq_totient_of_hasEnoughRootsOfUnity ℂ m]`. Conclude with `(Nat.card_congr (MonoidHom.ofInjective (changeLevel_injective hm)).toEquiv).symm`.
-/
theorem mem_condDvd_iff (m : ℕ) (ψ : DirichletCharacter ℂ N) :
    (ψ ∈ condDvd N m ↔ ψ.conductor ∣ m) ∧ (m ∣ N → Nat.card (condDvd N m) = Nat.totient m) := by
  refine ⟨mem_conductorDvd_iff m ψ, fun hm => ?_⟩
  have : NeZero m := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hm))⟩
  have h : condDvd N m = (changeLevel (R := ℂ) hm).range := by
    ext χ
    rw [mem_conductorDvd_iff, ← mem_conductorSet_iff_conductor_dvd _ hm, mem_conductorSet_iff,
      MonoidHom.mem_range]
    refine ⟨fun ⟨_, χ₀, h⟩ => ⟨χ₀, h.symm⟩, fun ⟨χ₀, h⟩ => ⟨hm, χ₀, h.symm⟩⟩
  rw [h, ← card_eq_totient_of_hasEnoughRootsOfUnity ℂ m]
  exact (Nat.card_congr (MonoidHom.ofInjective (changeLevel_injective hm)).toEquiv).symm

/- English proof (translation)
Establish `hmem : ∀ ψ, ψ ∈ evenPart X ↔ ψ ∈ X ∧ ψ.Even`. Introduce `ψ`. Rewrite using `[evenPart, Subgroup.mem_inf, mem_annihilator_iff]`. Simplify using `[DirichletCharacter.Even]`. Use `⟨hmem, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨ψ, hψ, hodd⟩`. Establish `hle : evenPart X ≤ X` using `inf_le_left`. Establish `hidx : ((evenPart X).subgroupOf X).index = 2`. Rewrite using `[Subgroup.index_eq_two_iff]`. Use `⟨⟨ψ, hψ⟩, fun b => ?_⟩` and prove the remaining obligations.

Establish `hψ' : ψ (-1) = -1` using `hodd`. Establish `e1 : b * ⟨ψ, hψ⟩ ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Odd`. Rewrite using `[Subgroup.mem_subgroupOf, hmem]`. Simplify using `only [SetLike.coe_mem, true_and, DirichletCharacter.Even, DirichletCharacter.Odd]`. Rewrite using `[Subgroup.coe_mul, MulChar.mul_apply, hψ', mul_neg, mul_one, neg_eq_iff_eq_neg]`.

Establish `e2 : b ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Even`. Rewrite using `[Subgroup.mem_subgroupOf, hmem]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2]`. Break down `(b : DirichletCharacter ℂ N).even_or_odd with h | h` into its components or cases.

Conclude with `Or.inr ⟨h, h.not_odd⟩`. Conclude with `Or.inl ⟨h, h.not_even⟩`. Rewrite using `[← Subgroup.index_mul_card ((evenPart X).subgroupOf X), hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]`.
-/
theorem card_evenPart (X : Subgroup (DirichletCharacter ℂ N)) :
    (∀ ψ, ψ ∈ evenPart X ↔ ψ ∈ X ∧ ψ.Even) ∧
      ((∃ ψ ∈ X, ψ.Odd) → Nat.card X = 2 * Nat.card (evenPart X)) := by
  have hmem : ∀ ψ, ψ ∈ evenPart X ↔ ψ ∈ X ∧ ψ.Even := by
    intro ψ
    rw [evenPart, Subgroup.mem_inf, mem_annihilator_iff]
    simp [DirichletCharacter.Even]
  refine ⟨hmem, ?_⟩
  rintro ⟨ψ, hψ, hodd⟩
  have hle : evenPart X ≤ X := inf_le_left
  have hidx : ((evenPart X).subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨ψ, hψ⟩, fun b => ?_⟩
    have hψ' : ψ (-1) = -1 := hodd
    have e1 : b * ⟨ψ, hψ⟩ ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Odd := by
      rw [Subgroup.mem_subgroupOf, hmem]
      simp only [SetLike.coe_mem, true_and, DirichletCharacter.Even, DirichletCharacter.Odd]
      rw [Subgroup.coe_mul, MulChar.mul_apply, hψ', mul_neg, mul_one, neg_eq_iff_eq_neg]
    have e2 : b ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Even := by
      rw [Subgroup.mem_subgroupOf, hmem]
      simp
    rw [e1, e2]
    rcases (b : DirichletCharacter ℂ N).even_or_odd with h | h
    · exact Or.inr ⟨h, h.not_odd⟩
    · exact Or.inl ⟨h, h.not_even⟩
  rw [← Subgroup.index_mul_card ((evenPart X).subgroupOf X), hidx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

/- English proof (translation)
Use `⟨?_, ?_, fieldConductor_dvd_iff X⟩` and prove the remaining obligations. Use `Nat.dvd_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[fieldConductor_dvd_iff, sup_le_iff, ← fieldConductor_dvd_iff, ← fieldConductor_dvd_iff]`. Conclude with `⟨Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _⟩`. Rewrite using `[Nat.lcm_dvd_iff, fieldConductor_dvd_iff, fieldConductor_dvd_iff, ← sup_le_iff, ← fieldConductor_dvd_iff]`.

Use `Nat.dvd_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[fieldConductor_dvd_iff, Subgroup.zpowers_le, mem_conductorDvd_iff]`. Rewrite using `[← mem_conductorDvd_iff, ← Subgroup.zpowers_le, ← fieldConductor_dvd_iff]`.
-/
theorem fieldCond_sup (X Y : Subgroup (DirichletCharacter ℂ N)) (χ : DirichletCharacter ℂ N) :
    fieldCond (X ⊔ Y) = Nat.lcm (fieldCond X) (fieldCond Y) ∧
      fieldCond (Subgroup.zpowers χ) = χ.conductor ∧
      ∀ m, fieldCond X ∣ m ↔ X ≤ condDvd N m := by
  refine ⟨?_, ?_, fieldConductor_dvd_iff X⟩
  · refine Nat.dvd_antisymm ?_ ?_
    · rw [fieldConductor_dvd_iff, sup_le_iff, ← fieldConductor_dvd_iff, ← fieldConductor_dvd_iff]
      exact ⟨Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _⟩
    · rw [Nat.lcm_dvd_iff, fieldConductor_dvd_iff, fieldConductor_dvd_iff, ← sup_le_iff,
        ← fieldConductor_dvd_iff]
  · refine Nat.dvd_antisymm ?_ ?_
    · rw [fieldConductor_dvd_iff, Subgroup.zpowers_le, mem_conductorDvd_iff]
    · rw [← mem_conductorDvd_iff, ← Subgroup.zpowers_le, ← fieldConductor_dvd_iff]

end KStar.Ram
