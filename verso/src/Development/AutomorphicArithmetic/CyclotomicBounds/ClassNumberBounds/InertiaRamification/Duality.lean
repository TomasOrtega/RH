import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem annihilator_eq_iso (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
  ext χ
  simp [mem_annihilator_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem charKer_eq_iso (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer X =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ).symm (OrderDual.toDual X) := by
  ext m
  simp [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem card_annihilator_eq (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  rw [annihilator_eq_iso, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem annihilator_charKer (X : Subgroup (DirichletCharacter ℂ N)) (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X ∧
      charKer (annihilator ℂ (H : Set (ZMod N)ˣ)) = H ∧ Nat.card X = (charKer X).index := by
  have h1 : annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X := by
    rw [charKer_eq_iso, annihilator_eq_iso, OrderIso.apply_symm_apply]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · rw [annihilator_eq_iso, charKer_eq_iso]
    simp
  · rw [← card_annihilator_eq, h1]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem ramIdx_eq_ramIdxUnits (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X = ramIdxUnits l (charKer X) := by
  obtain ⟨h1, -, h3⟩ := annihilator_charKer X ⊥
  have hk : (localPart N l).ker ⊓ X =
      annihilator ℂ ((inertiaUnits N l ⊔ charKer X : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) := by
    rw [annihilator_eq_iso, OrderIso.map_sup, ofDual_sup, ← annihilator_eq_iso,
      ← annihilator_eq_iso, h1]
    congr 1
    ext ψ
    rw [MonoidHom.mem_ker, (localPart_eq_one_iff l ψ).1, mem_annihilator_iff]
    rfl
  have hc : Nat.card ((localPart N l).ker ⊓ X : Subgroup _) =
      (inertiaUnits N l ⊔ charKer X).index := by
    rw [hk, card_annihilator_eq]
  have e1 : Nat.card ((localPart N l).ker ⊓ X : Subgroup _) * ramIdx l X = Nat.card X := by
    unfold ramIdx
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, Subgroup.relIndex,
      ← Subgroup.card_mul_index (((localPart N l).ker ⊓ X).subgroupOf X),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  have e2 : ramIdxUnits l (charKer X) * (inertiaUnits N l ⊔ charKer X).index =
      (charKer X).index := by
    unfold ramIdxUnits
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.relIndex_sup_right,
      Subgroup.relIndex_mul_index le_sup_right]
  have hpos : 0 < (inertiaUnits N l ⊔ charKer X).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [mul_comm _ (ramIdxUnits _ _), e2, ← hc, e1, h3]

end KStar.Ram
