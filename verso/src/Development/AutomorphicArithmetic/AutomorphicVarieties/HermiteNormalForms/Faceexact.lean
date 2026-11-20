import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Establish `h` using `Finsupp.lmapDomain_supported ℤ ℤ (Subtype.val : {t // t ∈ s} → X) Set.univ`. Rewrite `h` using `[Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]`. Rewrite `hc` using `[← h]`. Take `⟨f, -, hf⟩` from `hc`. Conclude with `⟨f, hf⟩`.
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
Establish `h` using `Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ`. Rewrite `h` using `[Set.image_univ, Subtype.range_coe]`. Rewrite using `[← h]`. Conclude with `Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])`.
-/
private theorem UpperTheory.V.KT.fe_mem {X : Type} (s : Set X) (f : {t // t ∈ s} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val f ∈ Finsupp.supported ℤ ℤ s := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe] at h
  rw [← h]
  exact Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[map_add, Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add]`. Consider the case `single t c`.

Rewrite using `[KH.faceD_single, Finsupp.mapDomain_single]`. Simplify using `only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]`. Rewrite using `[← Finsupp.lmapDomain_apply ℤ ℤ, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`.

Simplify using `only [Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[mul_comm]`.
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
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.single_add]`. Consider the case `single t c`.

Rewrite using `[Finsupp.mapDomain_single, KH.aug_single]`. Simplify using `only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single]`. Rewrite using `[Fin.sum_univ_one]`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Conclude with `Fin.elim0 k`.
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
Introduce `I S hS hS0 hA m`. Take `⟨hA0, hAn⟩` from `hA`. Establish `inj : ∀ n, Function.Injective (Finsupp.mapDomain (M` using `ℤ) (Subtype.val : {t : Fin n → I // t ∈ S n} → (Fin n → I))) := fun n => Finsupp.mapDomain_injective Subtype.val_injective`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Finsupp.single (Fin.elim0 : Fin 0 → I) (1 : ℤ) ∈ Finsupp.supported ℤ ℤ (S 0)`.

Rewrite using `[hS0, Finsupp.supported_univ]`. Conclude with `Submodule.mem_top`. Take `⟨b, hb, hbc⟩` from `hA0 _ hc`. Take `⟨f, rfl⟩` from `fe_lift (S 1) b hb`. Rewrite `hbc` using `[fe_aug]`.

Establish `h1 : KH.aug _ f = 1` using `Finsupp.single_injective _ hbc`. Introduce `n`. Conclude with `⟨n • f, by rw [map_zsmul, h1, smul_eq_mul, mul_one]⟩`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Establish `hc` using `fe_mem (S 1) y`. Establish `hbd : ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val y) = 0`. Rewrite using `[fe_aug, hy, Finsupp.single_zero]`. Take `⟨b, hb, hbc⟩` from `hAn 0 _ hc hbd`.

Take `⟨g, rfl⟩` from `fe_lift (S 2) b hb`. Use `⟨g, inj 1 ?_⟩` and prove the remaining obligations. Rewrite using `[fe_comm S hS 1 g, hbc]`. Introduce and unpack `⟨g, rfl⟩`. Establish `h` using `fe_aug (S 1) (KH.faceD (fun (i : Fin 2) (t : {t : Fin 2 → I // t ∈ S 2}) => (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin 1 → I // t ∈ S 1})) g)`.

Rewrite `h` using `[fe_comm S hS 1 g, ConeExtensionAcyclic.bd_bd]`. Conclude with `Finsupp.single_eq_zero.mp h.symm`. Introduce `p _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hc` using `fe_mem (S (p + 2)) y`. Establish `hbd : ConeExtensionAcyclic.bd I (p + 1) (Finsupp.mapDomain Subtype.val y) = 0`. Rewrite using `[← fe_comm S hS (p + 1) y, hy, Finsupp.mapDomain_zero]`. Take `⟨b, hb, hbc⟩` from `hAn (p + 1) _ hc hbd`. Take `⟨g, rfl⟩` from `fe_lift (S (p + 3)) b hb`.

Use `⟨g, inj (p + 2) ?_⟩` and prove the remaining obligations. Rewrite using `[fe_comm S hS (p + 2) g, hbc]`. Introduce and unpack `⟨g, rfl⟩`. Apply `inj (p + 1)` to reduce the goal to its premises. Rewrite using `[fe_comm S hS (p + 1), fe_comm S hS (p + 2) g, ConeExtensionAcyclic.bd_bd, Finsupp.mapDomain_zero]`.
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
