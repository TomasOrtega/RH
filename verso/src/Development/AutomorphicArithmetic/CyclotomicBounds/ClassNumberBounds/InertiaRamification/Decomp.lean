import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.IsImagQuad
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Duality

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Introduce `u hu`. Unfold `inertiaUnits at hu`. Unfold `decompUnits`. Rewrite `hu` using `[MonoidHom.mem_ker]`. Rewrite using `[Subgroup.mem_comap, hu]`.

Conclude with `Subgroup.one_mem _`.
-/
private lemma inertia_le_decomp : inertiaUnits N l ≤ decompUnits N l := by
  intro u hu
  unfold inertiaUnits at hu
  unfold decompUnits
  rw [MonoidHom.mem_ker] at hu
  rw [Subgroup.mem_comap, hu]
  exact Subgroup.one_mem _

/- English proof (translation)
Rewrite using `[Subgroup.relIndex_eq_one]`. Conclude with `sup_le le_rfl ((Subgroup.zpowers_le).2 h)`.
-/
private lemma relIndex_sup_zpowers_of_mem {G : Type*} [CommGroup G] (A : Subgroup G) (c : G)
    (h : c ∈ A) : A.relIndex (A ⊔ Subgroup.zpowers c) = 1 := by
  rw [Subgroup.relIndex_eq_one]
  exact sup_le le_rfl ((Subgroup.zpowers_le).2 h)

/- English proof (translation)
Rewrite using `[Subgroup.relIndex_sup_left, Subgroup.relIndex_eq_two_iff_exists_notMem_and]`. Use `⟨c, Subgroup.mem_zpowers c, h, ?_⟩` and prove the remaining obligations. Introduce and unpack `b ⟨k, rfl⟩`. Establish `h2 : c ^ (2 : ℤ) = 1` using `by rw [zpow_two, hc]`. Break down `Int.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases.

Use `right`. Simplify using `only [zpow_mul, h2, one_zpow]`. Conclude with `A.one_mem`. Use `left`. Simplify using `only [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, hc]`.

Conclude with `A.one_mem`.
-/
private lemma relIndex_sup_zpowers_of_notMem {G : Type*} [CommGroup G] (A : Subgroup G) (c : G)
    (hc : c * c = 1) (h : c ∉ A) : A.relIndex (A ⊔ Subgroup.zpowers c) = 2 := by
  rw [Subgroup.relIndex_sup_left, Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨c, Subgroup.mem_zpowers c, h, ?_⟩
  rintro b ⟨k, rfl⟩
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, hc]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · right
    simp only [zpow_mul, h2, one_zpow]
    exact A.one_mem
  · left
    simp only [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, hc]
    exact A.one_mem

omit [NeZero N] in
/- English proof (translation)
Unfold `charKer`. Simplify using `only [Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`.
-/
private lemma mem_charKer_iff' (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  unfold charKer
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
    Units.val_one]

/- English proof (translation)
Establish `key : evenPart X = annihilator ℂ ((charKer X ⊔ Subgroup.zpowers (-1) : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ)`. Use extensionality with `ψ`. Establish `h1 : ψ ∈ X ↔ charKer X ≤ (MulChar.toUnitHom ψ).ker` using `by conv_lhs => rw [← (annihilator_charKer X ⊥).1]`. Rewrite using `[mem_annihilator_iff]`. Use `forall_congr' fun u => ?_` and prove the remaining obligations.

Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Establish `h2 : ∀ K : Subgroup (ZMod N)ˣ, ψ ∈ annihilator ℂ (K : Set (ZMod N)ˣ) ↔ K ≤ (MulChar.toUnitHom ψ).ker`. Introduce `K`. Rewrite using `[mem_annihilator_iff]`. Use `forall_congr' fun u => ?_` and prove the remaining obligations.

Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Unfold `evenPart`. Rewrite using `[h2, sup_le_iff, Subgroup.mem_inf, h1, Subgroup.zpowers_le, mem_annihilator_iff]`. Simplify using `only [Set.mem_singleton_iff, forall_eq]`. Simplify using `only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`.

Rewrite using `[key]`. Conclude with `(annihilator_charKer X _).2.1`.
-/
private lemma charKer_evenPart' (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer (evenPart X) = charKer X ⊔ Subgroup.zpowers (-1) := by
  have key : evenPart X =
      annihilator ℂ ((charKer X ⊔ Subgroup.zpowers (-1) : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) := by
    ext ψ
    have h1 : ψ ∈ X ↔ charKer X ≤ (MulChar.toUnitHom ψ).ker := by
      conv_lhs => rw [← (annihilator_charKer X ⊥).1]
      rw [mem_annihilator_iff]
      refine forall_congr' fun u => ?_
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
        Units.val_one]
    have h2 : ∀ K : Subgroup (ZMod N)ˣ, ψ ∈ annihilator ℂ (K : Set (ZMod N)ˣ) ↔
        K ≤ (MulChar.toUnitHom ψ).ker := by
      intro K
      rw [mem_annihilator_iff]
      refine forall_congr' fun u => ?_
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
        Units.val_one]
    unfold evenPart
    rw [h2, sup_le_iff, Subgroup.mem_inf, h1, Subgroup.zpowers_le, mem_annihilator_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  rw [key]
  exact (annihilator_charKer X _).2.1

/- English proof (translation)
Rewrite using `[ramIdx_eq_ramIdxUnits, ramIdxUnits, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_sup_right]`.
-/
private lemma ramIdx_eq_relIndex' (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X = (charKer X).relIndex (inertiaUnits N l ⊔ charKer X) := by
  rw [ramIdx_eq_ramIdxUnits, ramIdxUnits, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
    Subgroup.relIndex_sup_right]

/- English proof (translation)
Use `⟨inertia_le_decomp l, ?_⟩` and prove the remaining obligations. Unfold `SplitsFor`. Rewrite using `[← mem_subgroupOfPrimitiveMapToOne_iff]`. Simplify using `only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff, Set.mem_singleton_iff, forall_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨χ, hχ, rfl⟩ u hu`. Unfold `decompUnits at hu`. Rewrite `hu` using `[Subgroup.mem_comap]`. Take `⟨k, hk⟩` from `hu`. Establish `h1 : MulChar.toUnitHom χ (ZMod.unitOfCoprime l (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N))) = 1`.

Rewrite using `[Units.ext_iff, MulChar.coe_toUnitHom, hχ, Units.val_one]`. Rewrite using `[← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, ← hk]`. Simplify using `only [map_zpow, h1, one_zpow, Units.val_one]`. Introduce `h`. Establish `hf : ψ.FactorsThrough (ordCompl[l] N)`.

Rewrite using `[factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N l)]`. Introduce `u hu`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Conclude with `h u (inertia_le_decomp l hu)`. Take `⟨hd, χ, rfl⟩` from `hf`.

Use `⟨χ, ?_, rfl⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime l (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)))`. Establish `hmem : u ∈ decompUnits N l`. Unfold `decompUnits`. Rewrite using `[Subgroup.mem_comap, hu]`.

Conclude with `Subgroup.mem_zpowers _`. Use `h u hmem` as an intermediate fact. Rewrite `this` using `[← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, hu, MulChar.coe_toUnitHom]`. Conclude with `this`.
-/
theorem splitsFor_iff (ψ : DirichletCharacter ℂ N) :
    inertiaUnits N l ≤ decompUnits N l ∧
      (SplitsFor l ψ ↔ ∀ u ∈ decompUnits N l, ψ (u : ZMod N) = 1) := by
  refine ⟨inertia_le_decomp l, ?_⟩
  unfold SplitsFor
  rw [← mem_subgroupOfPrimitiveMapToOne_iff]
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨χ, hχ, rfl⟩ u hu
    unfold decompUnits at hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨k, hk⟩ := hu
    have h1 : MulChar.toUnitHom χ (ZMod.unitOfCoprime l
        (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N))) = 1 := by
      rw [Units.ext_iff, MulChar.coe_toUnitHom, hχ, Units.val_one]
    rw [← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, ← hk]
    simp only [map_zpow, h1, one_zpow, Units.val_one]
  · intro h
    have hf : ψ.FactorsThrough (ordCompl[l] N) := by
      rw [factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N l)]
      intro u hu
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact h u (inertia_le_decomp l hu)
    obtain ⟨hd, χ, rfl⟩ := hf
    refine ⟨χ, ?_, rfl⟩
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime l
        (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)))
    have hmem : u ∈ decompUnits N l := by
      unfold decompUnits
      rw [Subgroup.mem_comap, hu]
      exact Subgroup.mem_zpowers _
    have := h u hmem
    rw [← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, hu,
      MulChar.coe_toUnitHom] at this
    exact this

/- English proof (translation)
Establish `h : inertiaUnits N l ⊔ charKer X ≤ decompUnits N l ⊔ charKer X` using `sup_le_sup_right (inertia_le_decomp l) _`. Rewrite using `[ramIdx_eq_relIndex', resDeg, numPlaces, Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right h, Subgroup.relIndex_mul_index le_sup_right, (annihilator_charKer X ⊥).2.2]`.
-/
theorem ramIdx_mul_resDeg_mul_numPlaces (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X * resDeg l X * numPlaces l X = Nat.card X := by
  have h : inertiaUnits N l ⊔ charKer X ≤ decompUnits N l ⊔ charKer X :=
    sup_le_sup_right (inertia_le_decomp l) _
  rw [ramIdx_eq_relIndex', resDeg, numPlaces,
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right h,
    Subgroup.relIndex_mul_index le_sup_right, (annihilator_charKer X ⊥).2.2]

/- English proof (translation)
Establish `hc : (-1 : (ZMod N)ˣ) * (-1) = 1` using `by simp`. Prove the components needed by the constructor for the conclusion. Unfold `numPlaces ConjIn`. Rewrite using `[charKer_evenPart', ← sup_assoc]`. Use `set A := decompUnits N l ⊔ charKer X`.

Establish `h1` using `Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ Subgroup.zpowers (-1))`. Establish `h0 : (A ⊔ Subgroup.zpowers (-1)).index ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Distinguish the cases in `h : (-1 : (ZMod N)ˣ) ∈ A`. Rewrite `h1` using `[relIndex_sup_zpowers_of_mem A _ h]`. Simplify using `only [h, not_true_eq_false, iff_false]`.

Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[relIndex_sup_zpowers_of_notMem A _ hc h]`. Simplify using `only [h, not_false_eq_true, iff_true]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨ψ, hψ, hodd⟩`.

Establish `hH : (-1 : (ZMod N)ˣ) ∉ charKer X`. Introduce `h`. Use `(mem_charKer_iff' X _).1 h ψ hψ` as an intermediate fact. Use `ψ.not_even_and_odd ⟨?_, hodd⟩` and prove the remaining obligations. Simplify `this` using `[DirichletCharacter.Even]`.

Unfold `ConjIn`. Rewrite using `[ramIdx_eq_relIndex', ramIdx_eq_relIndex', charKer_evenPart', ← sup_assoc]`. Use `set H := charKer X`. Use `set A := inertiaUnits N l ⊔ H with hA`. Establish `hHA : H ≤ A` using `le_sup_right`.

Establish `h1` using `Subgroup.relIndex_mul_relIndex H A (A ⊔ Subgroup.zpowers (-1)) hHA le_sup_left`. Establish `h2` using `Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers (-1)) (A ⊔ Subgroup.zpowers (-1)) le_sup_left (sup_le_sup_right hHA _)`. Rewrite `h2` using `[relIndex_sup_zpowers_of_notMem H _ hc hH]`. Establish `h0 : (H ⊔ Subgroup.zpowers (-1)).relIndex (A ⊔ Subgroup.zpowers (-1)) ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Distinguish the cases in `h : (-1 : (ZMod N)ˣ) ∈ A`.

Rewrite `h1` using `[relIndex_sup_zpowers_of_mem A _ h]`. Simplify using `only [h, not_true_eq_false, iff_false]`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[relIndex_sup_zpowers_of_notMem A _ hc h]`. Simplify using `only [h, not_false_eq_true, iff_true]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem conjIn_iff (X : Subgroup (DirichletCharacter ℂ N)) :
    (numPlaces l X = 2 * numPlaces l (evenPart X) ↔ ¬ ConjIn X (decompUnits N l)) ∧
      ((∃ ψ ∈ X, ψ.Odd) →
        (ramIdx l X = ramIdx l (evenPart X) ↔ ¬ ConjIn X (inertiaUnits N l))) := by
  have hc : (-1 : (ZMod N)ˣ) * (-1) = 1 := by simp
  constructor
  · unfold numPlaces ConjIn
    rw [charKer_evenPart', ← sup_assoc]
    set A := decompUnits N l ⊔ charKer X
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ Subgroup.zpowers (-1))
    have h0 : (A ⊔ Subgroup.zpowers (-1)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_cases h : (-1 : (ZMod N)ˣ) ∈ A
    · rw [relIndex_sup_zpowers_of_mem A _ h] at h1
      simp only [h, not_true_eq_false, iff_false]
      omega
    · rw [relIndex_sup_zpowers_of_notMem A _ hc h] at h1
      simp only [h, not_false_eq_true, iff_true]
      omega
  · rintro ⟨ψ, hψ, hodd⟩
    have hH : (-1 : (ZMod N)ˣ) ∉ charKer X := by
      intro h
      have := (mem_charKer_iff' X _).1 h ψ hψ
      refine ψ.not_even_and_odd ⟨?_, hodd⟩
      simpa [DirichletCharacter.Even] using this
    unfold ConjIn
    rw [ramIdx_eq_relIndex', ramIdx_eq_relIndex', charKer_evenPart', ← sup_assoc]
    set H := charKer X
    set A := inertiaUnits N l ⊔ H with hA
    have hHA : H ≤ A := le_sup_right
    have h1 := Subgroup.relIndex_mul_relIndex H A (A ⊔ Subgroup.zpowers (-1)) hHA le_sup_left
    have h2 := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers (-1))
      (A ⊔ Subgroup.zpowers (-1)) le_sup_left (sup_le_sup_right hHA _)
    rw [relIndex_sup_zpowers_of_notMem H _ hc hH] at h2
    have h0 : (H ⊔ Subgroup.zpowers (-1)).relIndex (A ⊔ Subgroup.zpowers (-1)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    by_cases h : (-1 : (ZMod N)ˣ) ∈ A
    · rw [relIndex_sup_zpowers_of_mem A _ h] at h1
      simp only [h, not_true_eq_false, iff_false]
      omega
    · rw [relIndex_sup_zpowers_of_notMem A _ hc h] at h1
      simp only [h, not_false_eq_true, iff_true]
      omega

end KStar.Ram
