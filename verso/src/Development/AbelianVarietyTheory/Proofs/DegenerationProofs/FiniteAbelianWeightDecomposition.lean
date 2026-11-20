import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharSumInv

open Module
open TensorProduct

namespace GlobalTheory

namespace FiniteAbelianWeights

variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]

/- English proof (translation)
Simplify using `[Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_weightSpace_iff {ι : Type} (f : ι → M →ₗ[o] M) (a : ι → o) (x : M) :
    x ∈ (⨅ t, LinearMap.ker (f t - a t • LinearMap.id)) ↔ ∀ t, f t x = a t • x := by
  simp [Submodule.mem_iInf, sub_eq_zero]

noncomputable def avg [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) : M →ₗ[o] M :=
  u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • ρ t

variable [Fintype T] (ρ : Representation o T M) (u : o)

/- English proof (translation)
Simplify using `[avg, LinearMap.sum_apply]`.
-/
theorem avg_apply (c : T →* oˣ) (x : M) :
    avg ρ u c x = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • ρ t x := by
  simp [avg, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `only [avg_apply, map_smul, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_comm s t, map_mul, Module.End.mul_apply]`.
-/
theorem comm_avg (c : T →* oˣ) (s : T) (x : M) : ρ s (avg ρ u c x) = avg ρ u c (ρ s x) := by
  simp only [avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, mul_comm s t, map_mul, Module.End.mul_apply]

/- English proof (translation)
Simplify using `only [avg_apply, map_smul, map_sum]`. Rewrite using `[smul_comm]`. Use `congr 1`. Rewrite using `[Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]`. Use `congr 1`. Rewrite using `[← Units.val_mul]`. Use `congr 1`. Rewrite using `[mul_inv, mul_inv_cancel_left]`.
-/
theorem apply_avg (c : T →* oˣ) (s : T) (x : M) :
    ρ s (avg ρ u c x) = (c s : o) • avg ρ u c x := by
  simp only [avg_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
  congr 1
  rw [← Units.val_mul]
  congr 1
  rw [mul_inv, mul_inv_cancel_left]

/- English proof (translation)
Simplify using `only [avg_apply, hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]`. Rewrite using `[← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]`.
-/
theorem avg_of_weight (hu : u * (Fintype.card T : o) = 1) (c : T →* oˣ) (x : M)
    (hx : ∀ t, ρ t x = (c t : o) • x) : avg ρ u c x = x := by
  simp only [avg_apply, hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]

/- English proof (translation)
Simplify using `only [avg_apply, hx, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `h` using `sum_hom_units_eq_zero ((Units.coeHom o).comp (c⁻¹ * d)) (by`. Introduce `h`. Apply `hcd` to reduce the goal to its premises.

Use extensionality with `t`. Use `DFunLike.congr_fun h t` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply, MonoidHom.one_apply, Units.val_eq_one, inv_mul_eq_one] at this`. Rewrite using `[this])`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply, Units.val_mul] at h`.

Rewrite using `[h, zero_smul, smul_zero]`.
-/
theorem avg_of_weight_ne [IsDomain o] (c d : T →* oˣ) (hcd : d ≠ c) (x : M)
    (hx : ∀ t, ρ t x = (d t : o) • x) : avg ρ u c x = 0 := by
  simp only [avg_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have h := sum_hom_units_eq_zero ((Units.coeHom o).comp (c⁻¹ * d)) (by
    intro h
    apply hcd
    ext t
    have := DFunLike.congr_fun h t
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply,
      MonoidHom.one_apply, Units.val_eq_one, inv_mul_eq_one] at this
    rw [this])
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply,
    Units.val_mul] at h
  rw [h, zero_smul, smul_zero]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CharacterSumInverse.main`. Consider the case `exact _root_.GlobalTheory.CharacterSumInverse.main`. Consider the case `(apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CharacterSumInverse.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CharacterSumInverse.main ..)`.
-/
theorem sum_avg [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)]
    (hu : u * (Fintype.card T : o) = 1) (x : M) : ∑ c : T →* oˣ, avg ρ u c x = x := by
  first
  | exact @_root_.GlobalTheory.CharacterSumInverse.main
  | exact _root_.GlobalTheory.CharacterSumInverse.main
  | (apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharacterSumInverse.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharacterSumInverse.main ..)

/- English proof (translation)
Establish `h : ∀ y : A ⊗[o] M, (avg ρ u c).baseChange A y = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • (ρ t).baseChange A y`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m => simp [avg_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]`.

Consider the case `add y z hy hz => simp only [map_add, hy, hz, smul_add, Finset.sum_add_distrib]`. Rewrite using `[h]`. Simplify using `only [hx, algebraMap_smul, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]`. Rewrite using `[← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]`.
-/
theorem baseChange_avg_of_weight (hu : u * (Fintype.card T : o) = 1) (A : Type) [CommRing A]
    [Algebra o A] (c : T →* oˣ) (x : A ⊗[o] M)
    (hx : ∀ t, (ρ t).baseChange A x = algebraMap o A (c t) • x) :
    (avg ρ u c).baseChange A x = x := by
  have h : ∀ y : A ⊗[o] M, (avg ρ u c).baseChange A y
      = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • (ρ t).baseChange A y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [avg_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    | add y z hy hz => simp only [map_add, hy, hz, smul_add, Finset.sum_add_distrib]
  rw [h]
  simp only [hx, algebraMap_smul, smul_smul, Units.inv_mul, one_smul, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]

end FiniteAbelianWeights

open FiniteAbelianWeights in

/- English proof (translation)
Introduce `o _ _ N ζ hN hNu hζ T _ _ hT M _ _ ρ _`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hunit : ∀ (G : Type) [CommGroup G] [Fintype G], (∀ g : G, g ^ N = 1) → ∃ u : o, u * (Fintype.card G : o) = 1`. Introduce `G _ _ hG`. Establish `h1` using `card_dvd_exponent_pow_rank' G hG`.

Rewrite `h1` using `[Nat.card_eq_fintype_card]`. Establish `h2 : (Fintype.card G : o) ∣ (N : o) ^ Group.rank G`. Conclude with `Nat.cast_dvd_cast (α := o) h1` after adjusting the coercions. Conclude with `(isUnit_of_dvd_unit h2 (hNu.pow _)).exists_left_inv`. Use `haveI : HasEnoughRootsOfUnity o N := ⟨⟨ζ, hζ⟩, inferInstance⟩`.

Use `haveI : HasEnoughRootsOfUnity o (Monoid.exponent T) := HasEnoughRootsOfUnity.of_dvd o (Monoid.exponent_dvd_of_forall_pow_eq_one hT)`. Establish `hfin : Finite (T →* oˣ)` using `Finite.of_equiv T (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity T o).some.toEquiv.symm`. Use `haveI := Fintype.ofFinite T`. Use `haveI := Fintype.ofFinite (T →* oˣ)`. Take `⟨u, hu⟩` from `hunit T hT`.

Establish `hmem : ∀ (c : T →* oˣ) (x : M), avg ρ u c x ∈ ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)` using `fun c x => (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).2 fun t => apply_avg ρ u c t x`. Use `⟨hfin, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Prove the components needed by the constructor for the conclusion. Introduce `c`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Establish `hle : (⨆ d, ⨆ (_ : d ≠ c), ⨅ t, LinearMap.ker (ρ t - (d t : o) • LinearMap.id)) ≤ LinearMap.ker (avg ρ u c)`. Use `iSup₂_le fun d hd y hy => ?_` and prove the remaining obligations. Conclude with `avg_of_weight_ne ρ u c d hd y ((mem_weightSpace_iff (fun t => ρ t) (fun t => (d t : o)) _).1 hy)`.

Establish `h0 : avg ρ u c x = 0` using `hle hx'`. Rewrite `h0` using `[avg_of_weight ρ u hu c x ((mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx)]`. Then use the resulting hypothesis. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[← sum_avg ρ u hu x]`.

Conclude with `Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hmem c x)`. Introduce `T' c'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx'` using `(mem_weightSpace_iff (fun t : T' => ρ t) (fun t => (c' t : o)) _).1 hx`.

Rewrite using `[← sum_avg ρ u hu x]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c.comp T'.subtype = c'`. Conclude with `Submodule.mem_iSup_of_mem (⟨c, hc⟩ : {c : T →* oˣ // c.comp T'.subtype = c'}) (hmem c x)`. Use `haveI := Fintype.ofFinite T'`.

Take `⟨v, hv⟩` from `hunit T' fun g => Subtype.ext (by simpa using hT g)`. Set `ρ' : Representation o T' M` to `ρ.comp T'.subtype`. Establish `h1 : avg ρ' v c' (avg ρ u c x) = avg ρ u c x` using `avg_of_weight ρ' v hv c' _ fun t => by`. Express the relevant statement in the definitionally equal form `ρ t (avg ρ u c x) = _`. Rewrite using `[comm_avg, hx' t, map_smul]`.

Establish `h2 : avg ρ' v c' (avg ρ u c x) = 0` using `avg_of_weight_ne ρ' v c' (c.comp T'.subtype) hc _ fun t => apply_avg ρ u c t x`. Rewrite using `[← h1, h2]`. Conclude with `Submodule.zero_mem _`. Use `iSup_le fun c x hx => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `c`.

Establish `hx'` using `(mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx`. Conclude with `(mem_weightSpace_iff (fun t : T' => ρ t) (fun t => (c.comp T'.subtype t : o)) _).2 fun t => hx' t`. Introduce `A _ _ c`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx'` using `(mem_weightSpace_iff (fun t => (ρ t).baseChange A) (fun t => algebraMap o A (c t)) _).1 hx`. Rewrite using `[← baseChange_avg_of_weight ρ u hu A c x hx']`. Use `clear hx hx'`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a m`. Rewrite using `[LinearMap.baseChange_tmul]`. Conclude with `Submodule.tmul_mem_baseChange_of_mem a (hmem c m)`. Consider the case `add y z hy hz`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Establish `hm'` using `(mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hm`. Use `(mem_weightSpace_iff (fun t => (ρ t).baseChange A) (fun t => algebraMap o A (c t)) _).2 fun t => ?_` and prove the remaining obligations.

Simplify using `only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hm', algebraMap_smul, TensorProduct.tmul_smul]`.
-/
theorem finiteAbelian_weightDecomposition :
    ∀ (o : Type) [CommRing o] [IsDomain o] (N : ℕ) (ζ : o), 0 < N → IsUnit (N : o) →
    IsPrimitiveRoot ζ N → ∀ (T : Type) [CommGroup T] [Finite T], (∀ t : T, t ^ N = 1) →
    ∀ (M : Type) [AddCommGroup M] [Module o M] (ρ : Representation o T M)
      [DecidableEq (T →* oˣ)],
      Finite (T →* oˣ) ∧
      DirectSum.IsInternal
        (fun c : T →* oˣ => ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)) ∧
      (∀ (T' : Subgroup T) (c' : T' →* oˣ),
        (⨅ t : T', LinearMap.ker (ρ t - (c' t : o) • LinearMap.id)) =
          ⨆ c : {c : T →* oˣ // c.comp T'.subtype = c'},
            ⨅ t, LinearMap.ker (ρ t - (c.1 t : o) • LinearMap.id)) ∧
      ∀ (A : Type) [CommRing A] [Algebra o A] (c : T →* oˣ),
        (⨅ t, LinearMap.ker ((ρ t).baseChange A - (algebraMap o A (c t)) • LinearMap.id)) =
          (⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)).baseChange A := by
  intro o _ _ N ζ hN hNu hζ T _ _ hT M _ _ ρ _
  classical
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ (G : Type) [CommGroup G] [Fintype G], (∀ g : G, g ^ N = 1) →
      ∃ u : o, u * (Fintype.card G : o) = 1 := by
    intro G _ _ hG
    have h1 := card_dvd_exponent_pow_rank' G hG
    rw [Nat.card_eq_fintype_card] at h1
    have h2 : (Fintype.card G : o) ∣ (N : o) ^ Group.rank G := by
      exact_mod_cast Nat.cast_dvd_cast (α := o) h1
    exact (isUnit_of_dvd_unit h2 (hNu.pow _)).exists_left_inv
  haveI : HasEnoughRootsOfUnity o N := ⟨⟨ζ, hζ⟩, inferInstance⟩
  haveI : HasEnoughRootsOfUnity o (Monoid.exponent T) :=
    HasEnoughRootsOfUnity.of_dvd o (Monoid.exponent_dvd_of_forall_pow_eq_one hT)
  have hfin : Finite (T →* oˣ) :=
    Finite.of_equiv T (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity T o).some.toEquiv.symm
  haveI := Fintype.ofFinite T
  haveI := Fintype.ofFinite (T →* oˣ)
  obtain ⟨u, hu⟩ := hunit T hT
  have hmem : ∀ (c : T →* oˣ) (x : M),
      avg ρ u c x ∈ ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id) := fun c x =>
    (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).2 fun t => apply_avg ρ u c t x
  refine ⟨hfin, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro c
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have hle : (⨆ d, ⨆ (_ : d ≠ c), ⨅ t, LinearMap.ker (ρ t - (d t : o) • LinearMap.id)) ≤
          LinearMap.ker (avg ρ u c) := by
        refine iSup₂_le fun d hd y hy => ?_
        exact avg_of_weight_ne ρ u c d hd y
          ((mem_weightSpace_iff (fun t => ρ t) (fun t => (d t : o)) _).1 hy)
      have h0 : avg ρ u c x = 0 := hle hx'
      rwa [avg_of_weight ρ u hu c x
        ((mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx)] at h0
    · rw [eq_top_iff]
      intro x _
      rw [← sum_avg ρ u hu x]
      exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hmem c x)
  · intro T' c'
    apply le_antisymm
    · intro x hx
      have hx' := (mem_weightSpace_iff (fun t : T' => ρ t) (fun t => (c' t : o)) _).1 hx
      rw [← sum_avg ρ u hu x]
      refine Submodule.sum_mem _ fun c _ => ?_
      by_cases hc : c.comp T'.subtype = c'
      · exact Submodule.mem_iSup_of_mem
          (⟨c, hc⟩ : {c : T →* oˣ // c.comp T'.subtype = c'}) (hmem c x)
      · haveI := Fintype.ofFinite T'
        obtain ⟨v, hv⟩ := hunit T' fun g => Subtype.ext (by simpa using hT g)
        let ρ' : Representation o T' M := ρ.comp T'.subtype
        have h1 : avg ρ' v c' (avg ρ u c x) = avg ρ u c x :=
          avg_of_weight ρ' v hv c' _ fun t => by
            change ρ t (avg ρ u c x) = _
            rw [comm_avg, hx' t, map_smul]
        have h2 : avg ρ' v c' (avg ρ u c x) = 0 :=
          avg_of_weight_ne ρ' v c' (c.comp T'.subtype) hc _ fun t => apply_avg ρ u c t x
        rw [← h1, h2]
        exact Submodule.zero_mem _
    · refine iSup_le fun c x hx => ?_
      obtain ⟨c, rfl⟩ := c
      have hx' := (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx
      exact (mem_weightSpace_iff (fun t : T' => ρ t)
        (fun t => (c.comp T'.subtype t : o)) _).2 fun t => hx' t
  · intro A _ _ c
    apply le_antisymm
    · intro x hx
      have hx' := (mem_weightSpace_iff (fun t => (ρ t).baseChange A)
        (fun t => algebraMap o A (c t)) _).1 hx
      rw [← baseChange_avg_of_weight ρ u hu A c x hx']
      clear hx hx'
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a m =>
        rw [LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a (hmem c m)
      | add y z hy hz =>
        rw [map_add]
        exact Submodule.add_mem _ hy hz
    · rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      have hm' := (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hm
      refine (mem_weightSpace_iff (fun t => (ρ t).baseChange A)
        (fun t => algebraMap o A (c t)) _).2 fun t => ?_
      simp only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hm', algebraMap_smul,
        TensorProduct.tmul_smul]

end GlobalTheory
