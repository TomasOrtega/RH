import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use extensionality with `χ`. Simplify using `[mem_annihilator_iff]`.
-/
private theorem annihilator_eq_iso (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
  ext χ
  simp [mem_annihilator_iff]

/- English proof (translation)
Use extensionality with `m`. Simplify using `[charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]`.
-/
private theorem charKer_eq_iso (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer X =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ).symm (OrderDual.toDual X) := by
  ext m
  simp [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]

/- English proof (translation)
Rewrite using `[annihilator_eq_iso, MulChar.card_subgroupOrderIsoSubgroupMulChar]`. Both sides reduce to the same expression.
-/
private theorem card_annihilator_eq (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  rw [annihilator_eq_iso, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

/- English proof (translation)
Establish `h1 : annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X`. Rewrite using `[charKer_eq_iso, annihilator_eq_iso, OrderIso.apply_symm_apply]`. Both sides reduce to the same expression. Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[annihilator_eq_iso, charKer_eq_iso]`.

Simplify using the standard rewrite rules. Rewrite using `[← card_annihilator_eq, h1]`.
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
Take `⟨h1, -, h3⟩` from `annihilator_charKer X ⊥`. Establish `hk : (localPart N l).ker ⊓ X = annihilator ℂ ((inertiaUnits N l ⊔ charKer X : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ)`. Rewrite using `[annihilator_eq_iso, OrderIso.map_sup, ofDual_sup, ← annihilator_eq_iso, ← annihilator_eq_iso, h1]`. Use `congr 1`. Use extensionality with `ψ`.

Rewrite using `[MonoidHom.mem_ker, (localPart_eq_one_iff l ψ).1, mem_annihilator_iff]`. Both sides reduce to the same expression. Establish `hc : Nat.card ((localPart N l).ker ⊓ X : Subgroup _) = (inertiaUnits N l ⊔ charKer X).index`. Rewrite using `[hk, card_annihilator_eq]`. Establish `e1 : Nat.card ((localPart N l).ker ⊓ X : Subgroup _) * ramIdx l X = Nat.card X`.

Unfold `ramIdx`. Rewrite using `[← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, Subgroup.relIndex, ← Subgroup.card_mul_index (((localPart N l).ker ⊓ X).subgroupOf X), Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]`. Establish `e2 : ramIdxUnits l (charKer X) * (inertiaUnits N l ⊔ charKer X).index = (charKer X).index`. Unfold `ramIdxUnits`. Rewrite using `[← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.relIndex_sup_right, Subgroup.relIndex_mul_index le_sup_right]`.

Establish `hpos : 0 < (inertiaUnits N l ⊔ charKer X).index` using `Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite`. Apply `Nat.eq_of_mul_eq_mul_left hpos` to reduce the goal to its premises. Rewrite using `[mul_comm _ (ramIdxUnits _ _), e2, ← hc, e1, h3]`.
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
