import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem UpperTheory.V.KT.fe_lift {X : Type} (s : Set X) (c : X →₀ ℤ)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) :
    ∃ f : {t // t ∈ s} →₀ ℤ, Finsupp.mapDomain Subtype.val f = c := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h
  rw [← h] at hc
  obtain ⟨f, -, hf⟩ := hc
  exact ⟨f, hf⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.KT.fe_mem {X : Type} (s : Set X) (f : {t // t ∈ s} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val f ∈ Finsupp.supported ℤ ℤ s := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe] at h
  rw [← h]
  exact Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem UpperTheory.V.KT.fe_comm {I : Type} (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S)
    (p : ℕ) (f : {t : Fin (p + 1) → I // t ∈ S (p + 1)} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val
      (KH.faceD (fun (i : Fin (p + 1)) (t : {t : Fin (p + 1) → I // t ∈ S (p + 1)}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin p → I // t ∈ S p})) f) =
      ConeExtensionAcyclic.bd I p (Finsupp.mapDomain Subtype.val f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add]
  | single t c =>
    rw [KH.faceD_single, Finsupp.mapDomain_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    rw [← Finsupp.lmapDomain_apply ℤ ℤ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [mul_comm]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.KT.fe_aug {I : Type} (s : Set (Fin 1 → I)) (f : {t // t ∈ s} →₀ ℤ) :
    ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val f) =
      Finsupp.single (Fin.elim0 : Fin 0 → I) (KH.aug _ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.single_add]
  | single t c =>
    rw [Finsupp.mapDomain_single, KH.aug_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    funext k
    exact Fin.elim0 k

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KT.faceexact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S), S 0 = Set.univ → ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
    KH.FaceExactTo (fun p => {t : Fin (p + 1) → I // t ∈ S (p + 1)})
      (fun p i t => ⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩) m := by
  intro I S hS hS0 hA m
  obtain ⟨hA0, hAn⟩ := hA
  have inj : ∀ n, Function.Injective (Finsupp.mapDomain (M := ℤ) (Subtype.val : {t : Fin n → I // t ∈ S n} → (Fin n → I))) :=
    fun n => Finsupp.mapDomain_injective Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · have hc : Finsupp.single (Fin.elim0 : Fin 0 → I) (1 : ℤ) ∈ Finsupp.supported ℤ ℤ (S 0) := by
      rw [hS0, Finsupp.supported_univ]
      exact Submodule.mem_top
    obtain ⟨b, hb, hbc⟩ := hA0 _ hc
    obtain ⟨f, rfl⟩ := fe_lift (S 1) b hb
    rw [fe_aug] at hbc
    have h1 : KH.aug _ f = 1 := Finsupp.single_injective _ hbc
    intro n
    exact ⟨n • f, by rw [map_zsmul, h1, smul_eq_mul, mul_one]⟩
  · intro y
    constructor
    · intro hy
      have hc := fe_mem (S 1) y
      have hbd : ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [fe_aug, hy, Finsupp.single_zero]
      obtain ⟨b, hb, hbc⟩ := hAn 0 _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S 2) b hb
      refine ⟨g, inj 1 ?_⟩
      rw [fe_comm S hS 1 g, hbc]
    · rintro ⟨g, rfl⟩
      have h := fe_aug (S 1) (KH.faceD (fun (i : Fin 2) (t : {t : Fin 2 → I // t ∈ S 2}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin 1 → I // t ∈ S 1})) g)
      rw [fe_comm S hS 1 g, ConeExtensionAcyclic.bd_bd] at h
      exact Finsupp.single_eq_zero.mp h.symm
  · intro p _ y
    constructor
    · intro hy
      have hc := fe_mem (S (p + 2)) y
      have hbd : ConeExtensionAcyclic.bd I (p + 1) (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [← fe_comm S hS (p + 1) y, hy, Finsupp.mapDomain_zero]
      obtain ⟨b, hb, hbc⟩ := hAn (p + 1) _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S (p + 3)) b hb
      refine ⟨g, inj (p + 2) ?_⟩
      rw [fe_comm S hS (p + 2) g, hbc]
    · rintro ⟨g, rfl⟩
      apply inj (p + 1)
      rw [fe_comm S hS (p + 1), fe_comm S hS (p + 2) g, ConeExtensionAcyclic.bd_bd, Finsupp.mapDomain_zero]
