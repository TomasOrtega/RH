import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicImage

namespace GroundTheory.Global

open NumberField IntermediateField IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield RationalSymbol _root_.GroundTheory.Global.Cyclotomic

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : L.1, @IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α} = ⊤ := by`. Establish `e : IntermediateField.algebra' L.1 = DivisionRing.toRatAlgebra` using `Subsingleton.elim _ _`. Rewrite using `[e]`. Conclude with `Field.exists_primitive_element ℚ L.1`. Establish `hdir : Directed (· ≤ ·) fun m : ℕ+ ↦ K.1 ⊔ rootsOfUnityField m` using `fun m n ↦ ⟨m * n, sup_le_sup_left (rootsOfUnityField_le_mul m n) _, sup_le_sup_left (by rw [mul_comm]; exact rootsOfUnityField_le_mul n m) _⟩`.

Establish `hmem : (α : ℚ̄) ∈ ⨆ m : ℕ+, K.1 ⊔ rootsOfUnityField m`. Rewrite using `[← sup_iSup, ← maxCyclotomic_eq_iSup]`. Conclude with `hL α.2`. Rewrite `hmem` using `[← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion]`. Take `⟨m, hm⟩` from `hmem`.

Use `⟨m, fun y hy ↦ ?_⟩` and prove the remaining obligations. Establish `hy' : y ∈ (@IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α}).map L.1.val` using `⟨⟨y, hy⟩, by rw [hα]; trivial, rfl⟩`. Rewrite `hy'` using `[adjoin_map, Set.image_singleton]`. Conclude with `adjoin_simple_le_iff.2 hm hy'`.
-/
theorem exists_le_sup_rootsOfUnityField (K L : FiniteSubfield) (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) :
    ∃ m : ℕ+, L.1 ≤ K.1 ⊔ rootsOfUnityField m := by
  obtain ⟨α, hα⟩ : ∃ α : L.1,
      @IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α} = ⊤ := by
    have e : IntermediateField.algebra' L.1 = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    rw [e]
    exact Field.exists_primitive_element ℚ L.1
  have hdir : Directed (· ≤ ·) fun m : ℕ+ ↦ K.1 ⊔ rootsOfUnityField m := fun m n ↦
    ⟨m * n, sup_le_sup_left (rootsOfUnityField_le_mul m n) _,
      sup_le_sup_left (by rw [mul_comm]; exact rootsOfUnityField_le_mul n m) _⟩
  have hmem : (α : ℚ̄) ∈ ⨆ m : ℕ+, K.1 ⊔ rootsOfUnityField m := by
    rw [← sup_iSup, ← maxCyclotomic_eq_iSup]
    exact hL α.2
  rw [← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, fun y hy ↦ ?_⟩
  have hy' : y ∈ (@IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α}).map
      L.1.val :=
    ⟨⟨y, hy⟩, by rw [hα]; trivial, rfl⟩
  rw [adjoin_map, Set.image_singleton] at hy'
  exact adjoin_simple_le_iff.2 hm hy'

/- English proof (translation)
The claim follows from `fun z hz ↦ (coe_cycRestrict_apply g ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩).symm`.
-/
theorem agreesOn_cycRestrict (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) : AgreesOn m g (cycRestrict g) :=
  fun z hz ↦ (coe_cycRestrict_apply g ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩).symm

variable (K L : FiniteSubfield) [Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

instance isGalois_of_fact : IsGalois K.1 L.1 :=
  isGalois_of_normal

omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] in

/- English proof (translation)
The claim follows from `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`.
-/
theorem isScalarTower_of_le (E : FiniteSubfield) [Fact (K ≤ E)] [Fact (L ≤ E)] :
    IsScalarTower K.1 L.1 E.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_le_sup_rootsOfUnityField K L hL`. Establish `: Fact (L ≤ compositum K (layer m))` using `⟨hm⟩`. Use `isScalarTower_of_le K L (compositum K (layer m))` as an intermediate fact. Establish `h1 : ((1 : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (diagonal K.1 a))`. Rewrite using `[ideleNorm_diagonal, range_diagonal_le_ker_layer m ⟨_, rfl⟩]`.

Conclude with `map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) (rootsOfUnityField m))`. Establish `hE` using `restrictHom_eq_ideleSymbol K (layer m) 1 (diagonal K.1 a) h1`. Rewrite `hE` using `[map_one]`. Rewrite using `[← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]`. Conclude with `map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := (compositum K (layer m)).1) L.1)`.
-/
theorem ideleSymbol_diagonal_eq_one_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) (a : K.1ˣ) :
    ideleSymbol K.1 L.1 (diagonal K.1 a) = 1 := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((1 : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (diagonal K.1 a)) := by
    rw [ideleNorm_diagonal, range_diagonal_le_ker_layer m ⟨_, rfl⟩]
    exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) (rootsOfUnityField m))
  have hE := restrictHom_eq_ideleSymbol K (layer m) 1 (diagonal K.1 a) h1
  rw [map_one] at hE
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := (compositum K (layer m)).1) L.1)

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_le_sup_rootsOfUnityField K L hL`. Establish `: Fact (L ≤ compositum K (layer m))` using `⟨hm⟩`. Use `isScalarTower_of_le K L (compositum K (layer m))` as an intermediate fact. Establish `h1 : ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)).restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x)`. Establish `h` using `agreesOn_cycRestrict m (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)`.

Rewrite `h` using `[hg, agreesOn_cycSymbol_iff, layerSymbol_mk]`. Conclude with `h`. Establish `hE` using `restrictHom_eq_ideleSymbol K (layer m) g x h1`. Rewrite using `[← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]`. Use `AlgEquiv.ext fun y ↦ Subtype.ext ?_` and prove the remaining obligations.

Conclude with `(congrArg Subtype.val (AlgEquiv.restrictNormal_commutes (restrictHom (E := compositum K (layer m)) g) L.1 y)).symm`.
-/
theorem restrictHom_eq_ideleSymbol_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic)
    (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K (IdeleClassGroup.mk K.1 x)) :
    restrictHom (E := L) g = ideleSymbol K.1 L.1 x := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x) := by
    have h := agreesOn_cycRestrict m (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    rw [hg, agreesOn_cycSymbol_iff, layerSymbol_mk] at h
    exact h
  have hE := restrictHom_eq_ideleSymbol K (layer m) g x h1
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  exact (congrArg Subtype.val
    (AlgEquiv.restrictNormal_commutes (restrictHom (E := compositum K (layer m)) g) L.1 y)).symm

end CyclotomicSymbol

end

end GroundTheory.Global
