import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSMulRegularCokerDualMapOfExactFibres
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function

namespace GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R F`. Establish `hid : 𝟙 (ModuleCat.of R (F →ₗ[R] M)) = ∑ i, (ModuleCat.ofHom (LinearMap.applyₗ (b i)) : ModuleCat.of R (F →ₗ[R] M) ⟶ ModuleCat.of R M) ≫ (ModuleCat.ofHom (LinearMap.smulRightₗ (b.coord i)) : ModuleCat.of R M ⟶ ModuleCat.of R (F →ₗ[R] M))`. Use extensionality with `f x`. Simplify using `only [ModuleCat.hom_sum, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply, ← map_smul, ← map_sum, …`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations.

Rewrite using `[← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, @Subsingleton.elim _ h (x.comp _ _) 0, Ext.zero_comp]`.
-/
theorem extZero_hom (M : Type) [AddCommGroup M] [Module R M] (n : ℕ) (h : ExtZero (R := R) M n)
    (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F] :
    ExtZero (R := R) (F →ₗ[R] M) n := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 (ModuleCat.of R (F →ₗ[R] M)) = ∑ i,
      (ModuleCat.ofHom (LinearMap.applyₗ (b i)) : ModuleCat.of R (F →ₗ[R] M) ⟶ ModuleCat.of R M) ≫
      (ModuleCat.ofHom (LinearMap.smulRightₗ (b.coord i)) : ModuleCat.of R M ⟶ ModuleCat.of R (F →ₗ[R] M)) := by
    ext f x
    simp only [ModuleCat.hom_sum, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, ← map_smul, ← map_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    @Subsingleton.elim _ h (x.comp _ _) 0, Ext.zero_comp]

/- English proof (translation)
Take `⟨xs, h, hd⟩` from `exists_ofList_eq_maximalIdeal_length_eq (R ⧸ N)`. Establish `hreg` using `isRegular_of_ofList_eq_maximalIdeal h hd.le`. Establish `hlen : g ≤ xs.length`. Rewrite `hg` using `[← hd]`. Conclude with `hg` after adjusting the coercions.

Set `σ` to `Function.surjInv (Ideal.Quotient.mk_surjective (I := N))`. Establish `hσ : ∀ a, Ideal.Quotient.mk _ (σ a) = a` using `Function.surjInv_eq _`. Establish `hmap : (xs.map σ).map (algebraMap R (R ⧸ N)) = xs`. Rewrite using `[List.map_map]`. Conclude with `List.map_id'' hσ xs`.

Establish `h1 : RingTheory.Sequence.IsRegular (R ⧸ N) (xs.map σ)`. Rewrite `hreg` using `[← hmap]`. Conclude with `((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_left_iff.mpr <| List.forall₂_same.mpr fun r _ => algebraMap_smul _ r).1 hreg`. Use `ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ h1 j (by simp; omega)` and prove the remaining obligations. Rewrite using `[Module.support_eq_zeroLocus, Ideal.annihilator_quotient]`.

Use `lt_top_iff_ne_top.2 (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)).symm` and prove the remaining obligations. Introduce `r hr`. Take `⟨x, hx, rfl⟩` from `List.mem_map.mp hr`. Establish `hx' : x ∈ maximalIdeal _` using `h ▸ Ideal.subset_span hx`. Rewrite `hx'`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `fun hu => hx' (hσ x ▸ hu.map (Ideal.Quotient.mk _))`.
-/
theorem extZero_quotient [IsNoetherianRing R] (N : Ideal R) [IsRegularLocalRing (R ⧸ N)] (g : ℕ)
    (hg : (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ N)) (j : ℕ) (hj : j < g) : ExtZero (R := R) (R ⧸ N) j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq (R ⧸ N)
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : g ≤ xs.length := by
    rw [← hd] at hg
    exact_mod_cast hg
  let σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := N))
  have hσ : ∀ a, Ideal.Quotient.mk _ (σ a) = a := Function.surjInv_eq _
  have hmap : (xs.map σ).map (algebraMap R (R ⧸ N)) = xs := by
    rw [List.map_map]
    exact List.map_id'' hσ xs
  have h1 : RingTheory.Sequence.IsRegular (R ⧸ N) (xs.map σ) := by
    rw [← hmap] at hreg
    exact ((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
      List.forall₂_same.mpr fun r _ => algebraMap_smul _ r).1 hreg
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ h1 j
    (by simp; omega)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · refine lt_top_iff_ne_top.2 (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' : x ∈ maximalIdeal _ := h ▸ Ideal.subset_span hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
    exact fun hu => hx' (hσ x ▸ hu.map (Ideal.Quotient.mk _))

/- English proof (translation)
Establish `hfree` using `fun i => (hF i).1`. Establish `hfin` using `fun i => (hF i).2`. Set `δ` to `fun i j => LinearMap.lcomp R M (C.d i j).hom`. Establish `hDext : ∀ i, ∀ j < g, ExtZero (R` using `R) (C.X i →ₗ[R] M) j := fun i j hj => extZero_hom M j (hE j hj) _`. Establish `hdd : ∀ i j k f, δ i j (δ j k f) = 0` using `fun i j k f => by`.

Use extensionality with `x`. Simplify using `[δ, d_d_apply]`. Establish `hloc : ∀ i, ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧ ∀ f, δ (i - 1) i f = 0 → s • f ∈ LinearMap.range (δ i (i + 1))`. Introduce `i p hp hpm`. Distinguish the cases in `hNp : N ≤ p`.

Take `⟨K, _, φ, hφ, hK⟩` from `hex p hp hNp`. Take `⟨t, ht, k₀, k₁, hk⟩` from `exists_homotopy C hF n hn p (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i`. Use `⟨t, ht, fun f hf => ⟨f ∘ₗ k₁, LinearMap.ext fun x => ?_⟩⟩` and prove the remaining obligations. Establish `h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0` using `LinearMap.congr_fun hf (k₀ x)`. Establish `h2` using `congrArg f (hk x)`.

Rewrite `h2` using `[map_add, h1, zero_add, map_smul]`. Conclude with `h2`. Take `⟨s, hs, hsp⟩` from `Set.not_subset.mp hNp`. Conclude with `⟨s, hsp, fun f _ => ⟨0, by ext x; simp [hM s hs]⟩⟩`. Establish `key : ∀ k i, i + k = g → LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1)) ∧ ∀ j < i, ExtZero (R` using `R) ((C.X i →ₗ[R] M) ⧸ LinearMap.range (δ i (i + 1))) j := by`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce and unpack `i rfl`. Take `⟨K, _, φ, hφ, hK⟩` from `hex (maximalIdeal R) inferInstance hN`.

Take `⟨s, t, hst⟩` from `exists_homotopy_of_forall_exact_residueField (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom) (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by`. Conclude with `exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1) (hK _ (Or.inr (by omega)))`. Establish `hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x` using `fun x => by simpa [d_d_apply] using LinearMap.congr_fun hst ((C.d i (i + 1)).hom x)`. Set `ι` to `(LinearMap.range (δ i (i + 1))).liftQ (LinearMap.id - δ i (i + 1) ∘ₗ LinearMap.lcomp R M s) (by`. Introduce and unpack `_ ⟨f, rfl⟩`.

Use extensionality with `x`. Simplify using `[δ, hds])`. Establish `hι : (LinearMap.range (δ i (i + 1))).mkQ ∘ₗ ι = LinearMap.id`. Use `Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)` and prove the remaining obligations. Use `(Submodule.Quotient.eq _).2 ⟨-(f ∘ₗ s), ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `[ι, δ]`. Use `⟨fun f hf => ⟨f ∘ₗ t, LinearMap.ext fun x => ?_⟩, fun j hj => extZero_retract ι _ hι j (hDext i j hj)⟩` and prove the remaining obligations. Establish `h1 : f ((C.d i (i + 1)).hom (s x)) = 0` using `LinearMap.congr_fun hf (s x)`. Establish `h2` using `congrArg f (LinearMap.congr_fun hst x)`.

Simplify `h2` using `[h1, δ]`. Consider the case `succ k ih`. Introduce `i hi`. Take `⟨-, h2⟩` from `ih (i + 1) (by omega)`. Establish `hker : LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1))` using `fun x hx => by`.

Use `(Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero (h2 0 (by omega)) _ fun p hp hm => ?_)` and prove the remaining obligations. Take `⟨s, hs, hs'⟩` from `hloc (i + 1) p hp hm`. Conclude with `⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' x hx)⟩`. Establish `hle : LinearMap.range (δ (i + 1) (i + 1 + 1)) ≤ LinearMap.ker (δ i (i + 1))`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `hdd _ _ _ y`. Conclude with `⟨hker, fun j hj => extZero_coker ((LinearMap.range (δ (i + 1) (i + 1 + 1))).liftQ _ hle) (LinearMap.range (δ i (i + 1))).mkQ (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker)) (Submodule.mkQ_surjective _) (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.ra …`. Conclude with `(key g 0 (zero_add g)).1`.
-/
theorem exact_hom_one [IsNoetherianRing R] (N : Ideal R) (hN : N ≤ maximalIdeal R) (M : Type) [AddCommGroup M]
    [Module R M] (hM : ∀ s ∈ N, ∀ x : M, s • x = 0) (g : ℕ) (hE : ∀ j < g, ExtZero (R := R) M j)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : Ideal R, p.IsPrime → N ≤ p → ∃ (K : Type) (_ : Field K) (φ : R →+* K),
      RingHom.ker φ = p ∧ ∀ i, (p ≠ maximalIdeal R ∨ g < i) →
        (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    LinearMap.ker (LinearMap.lcomp R M (C.d 0 1).hom) ≤ LinearMap.range (LinearMap.lcomp R M (C.d 1 2).hom) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let δ := fun i j => LinearMap.lcomp R M (C.d i j).hom
  have hDext : ∀ i, ∀ j < g, ExtZero (R := R) (C.X i →ₗ[R] M) j := fun i j hj => extZero_hom M j (hE j hj) _
  have hdd : ∀ i j k f, δ i j (δ j k f) = 0 := fun i j k f => by
    ext x
    simp [δ, d_d_apply]
  have hloc : ∀ i, ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧
      ∀ f, δ (i - 1) i f = 0 → s • f ∈ LinearMap.range (δ i (i + 1)) := by
    intro i p hp hpm
    by_cases hNp : N ≤ p
    · obtain ⟨K, _, φ, hφ, hK⟩ := hex p hp hNp
      obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
        (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
      refine ⟨t, ht, fun f hf => ⟨f ∘ₗ k₁, LinearMap.ext fun x => ?_⟩⟩
      have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
      have h2 := congrArg f (hk x)
      rw [map_add, h1, zero_add, map_smul] at h2
      exact h2
    · obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hNp
      exact ⟨s, hsp, fun f _ => ⟨0, by ext x; simp [hM s hs]⟩⟩
  have key : ∀ k i, i + k = g →
      LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1)) ∧
      ∀ j < i, ExtZero (R := R) ((C.X i →ₗ[R] M) ⧸ LinearMap.range (δ i (i + 1))) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨K, _, φ, hφ, hK⟩ := hex (maximalIdeal R) inferInstance hN
      obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
        (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
        (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
          exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
            (hK _ (Or.inr (by omega)))
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using LinearMap.congr_fun hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (δ i (i + 1))).liftQ
        (LinearMap.id - δ i (i + 1) ∘ₗ LinearMap.lcomp R M s) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [δ, hds])
      have hι : (LinearMap.range (δ i (i + 1))).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-(f ∘ₗ s), ?_⟩
        ext x
        simp [ι, δ]
      refine ⟨fun f hf => ⟨f ∘ₗ t, LinearMap.ext fun x => ?_⟩,
        fun j hj => extZero_retract ι _ hι j (hDext i j hj)⟩
      have h1 : f ((C.d i (i + 1)).hom (s x)) = 0 := LinearMap.congr_fun hf (s x)
      have h2 := congrArg f (LinearMap.congr_fun hst x)
      simpa [h1, δ] using h2
    | succ k ih =>
      intro i hi
      obtain ⟨-, h2⟩ := ih (i + 1) (by omega)
      have hker : LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1)) := fun x hx => by
        refine (Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero (h2 0 (by omega)) _ fun p hp hm => ?_)
        obtain ⟨s, hs, hs'⟩ := hloc (i + 1) p hp hm
        exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' x hx)⟩
      have hle : LinearMap.range (δ (i + 1) (i + 1 + 1)) ≤ LinearMap.ker (δ i (i + 1)) := by
        rintro _ ⟨y, rfl⟩
        exact hdd _ _ _ y
      exact ⟨hker, fun j hj =>
        extZero_coker ((LinearMap.range (δ (i + 1) (i + 1 + 1))).liftQ _ hle) (LinearMap.range (δ i (i + 1))).mkQ
          (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker))
          (Submodule.mkQ_surjective _)
          (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
          (h2 _ (by omega)) (hDext i j (by omega))⟩
  exact (key g 0 (zero_add g)).1

omit [IsLocalRing R] in

/- English proof (translation)
Rewrite using `[← (Module.Free.chooseBasis R F).sum_dual_apply_smul_coord f]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hf _) trivial`.
-/
theorem mem_smul_top_of_forall_mem (N : Ideal R) {F : Type} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (f : Module.Dual R F) (hf : ∀ x, f x ∈ N) : f ∈ N • (⊤ : Submodule R (Module.Dual R F)) := by
  classical
  rw [← (Module.Free.chooseBasis R F).sum_dual_apply_smul_coord f]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hf _) trivial

omit [IsLocalRing R] in

/- English proof (translation)
Use `set N := (maximalIdeal A).map (algebraMap A R) with hN`. Set `Z` to `LinearMap.range a.dualMap`. Establish `flat : Module.Flat A (Module.Dual R F₀)` using `Module.Flat.trans A R _`. Establish `hinj : Injective ((Z.subtype.restrictScalars A).rTensor (A ⧸ maximalIdeal A))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `t ht`. Take `⟨z, hz⟩` from `TensorProduct.mk_surjective A Z (A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective (TensorProduct.comm A _ _ t)`. Take `rfl : z ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = t` from `(TensorProduct.comm A _ _).injective hz`. Take `⟨_, y, rfl⟩` from `z`. Establish `h1 : a.dualMap y ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₀))`.

Use `congrArg (TensorProduct.tensorQuotEquivQuotSMul (Module.Dual R F₀) (maximalIdeal A)) ht` as an intermediate fact. Rewrite `this` using `[map_zero]`. Use `(Submodule.Quotient.mk_eq_zero _).1 (Eq.trans ?_ this)` and prove the remaining obligations. Conclude with `((TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ _ 1).trans (congrArg _ (one_smul _ _))).symm`. Establish `h2 : ∀ x, a.dualMap y x ∈ N` using `fun x => by`.

Use `Submodule.smul_induction_on (p := fun u : Module.Dual R F₀ => u x ∈ N) h1 (fun r hr u _ => ?_) fun u v hu hv => add_mem hu hv` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Algebra.smul_def]`. Conclude with `N.mul_mem_right _ (Ideal.mem_map_of_mem _ hr)`. Take `⟨w, hw⟩` from `hex (x := N.mkQ ∘ₗ y) (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 (h2 x))`. Take `⟨w', hw'⟩` from `Module.projective_lifting_property N.mkQ w N.mkQ_surjective`.

Establish `h3 : y - w' ∘ₗ b ∈ N • (⊤ : Submodule R (Module.Dual R F₁))` using `mem_smul_top_of_forall_mem N _ fun x => (Submodule.Quotient.eq _).1 ((LinearMap.congr_fun hw x).symm.trans (LinearMap.congr_fun hw' (b x)).symm)`. Establish `h4 : y - w' ∘ₗ b ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₁))`. Rewrite using `[← Submodule.restrictScalars_top A R, ← Ideal.smul_restrictScalars]`. Conclude with `h3`. Establish `h5 : (⟨a.dualMap y, y, rfl⟩ : Z) = a.dualMap.rangeRestrict (y - w' ∘ₗ b)`.

Use extensionality with `x`. Simplify using `[hab]`. Rewrite using `[h5]`. Use `Submodule.smul_induction_on (p := fun u => a.dualMap.rangeRestrict u ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = 0) h4 (fun r hr u _ => ?_) fun u v hu hv => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, smul_tmul, ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr, tmul_zero]`.

Rewrite using `[map_add, add_tmul, hu, hv, add_zero]`. Establish `h6` using `lTensor_injective_of_exact_of_exact_of_rTensor_injective (f₁ := Z.subtype.restrictScalars A) (f₂ := (e.toLinearMap ∘ₗ Z.mkQ).restrictScalars A) (g₁ := (maximalIdeal A).subtype) (g₂ := (maximalIdeal A).mkQ) (fun x => by`. Use `e.map_eq_zero_iff.trans ((Submodule.Quotient.mk_eq_zero _).trans ?_)` and prove the remaining obligations. Conclude with `⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)`. Use the proof step `(e.surjective.comp Z.mkQ_surjective) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) hinj`.

Use the proof step `(Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _))`. Establish `: Module.Finite A (R ⧸ I)` using `Module.Finite.of_surjective (Algebra.linearMap A (R ⧸ I)) hs`. Establish `: Module.FinitePresentation A (R ⧸ I)` using `Module.finitePresentation_of_finite A _`. Establish `: Module.Free A (R ⧸ I)` using `Module.free_of_maximalIdeal_rTensor_injective ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).1 h6)`. Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 hI`.

Conclude with `FaithfulSMul.algebraMap_injective A (R ⧸ I)`.
-/
theorem injective_of_exact {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra A R] [Module.Flat A R]
    {F₀ F₁ F₂ : Type} [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
    [Module.Free R F₀] [Module.Finite R F₀] [Module.Free R F₁] [Module.Finite R F₁] [Module.Free R F₂]
    (a : F₀ →ₗ[R] F₁) (b : F₁ →ₗ[R] F₂) (hab : ∀ x, b (a x) = 0)
    (hex : LinearMap.ker (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) a) ≤
      LinearMap.range (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) b))
    (I : Ideal R) (hI : I ≠ ⊤) (e : (Module.Dual R F₀ ⧸ LinearMap.range a.dualMap) ≃ₗ[R] R ⧸ I)
    (hs : Surjective (algebraMap A (R ⧸ I))) : Injective (algebraMap A (R ⧸ I)) := by
  set N := (maximalIdeal A).map (algebraMap A R) with hN
  let Z := LinearMap.range a.dualMap
  have flat : Module.Flat A (Module.Dual R F₀) := Module.Flat.trans A R _
  have hinj : Injective ((Z.subtype.restrictScalars A).rTensor (A ⧸ maximalIdeal A)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨z, hz⟩ := TensorProduct.mk_surjective A Z (A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective
      (TensorProduct.comm A _ _ t)
    obtain rfl : z ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = t := (TensorProduct.comm A _ _).injective hz
    obtain ⟨_, y, rfl⟩ := z
    have h1 : a.dualMap y ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₀)) := by
      have := congrArg (TensorProduct.tensorQuotEquivQuotSMul (Module.Dual R F₀) (maximalIdeal A)) ht
      rw [map_zero] at this
      refine (Submodule.Quotient.mk_eq_zero _).1 (Eq.trans ?_ this)
      exact ((TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ _ 1).trans (congrArg _ (one_smul _ _))).symm
    have h2 : ∀ x, a.dualMap y x ∈ N := fun x => by
      refine Submodule.smul_induction_on (p := fun u : Module.Dual R F₀ => u x ∈ N) h1 (fun r hr u _ => ?_)
        fun u v hu hv => add_mem hu hv
      rw [LinearMap.smul_apply, Algebra.smul_def]
      exact N.mul_mem_right _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨w, hw⟩ := hex (x := N.mkQ ∘ₗ y) (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 (h2 x))
    obtain ⟨w', hw'⟩ := Module.projective_lifting_property N.mkQ w N.mkQ_surjective
    have h3 : y - w' ∘ₗ b ∈ N • (⊤ : Submodule R (Module.Dual R F₁)) :=
      mem_smul_top_of_forall_mem N _ fun x => (Submodule.Quotient.eq _).1
        ((LinearMap.congr_fun hw x).symm.trans (LinearMap.congr_fun hw' (b x)).symm)
    have h4 : y - w' ∘ₗ b ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₁)) := by
      rw [← Submodule.restrictScalars_top A R, ← Ideal.smul_restrictScalars]
      exact h3
    have h5 : (⟨a.dualMap y, y, rfl⟩ : Z) = a.dualMap.rangeRestrict (y - w' ∘ₗ b) := by
      ext x
      simp [hab]
    rw [h5]
    refine Submodule.smul_induction_on
      (p := fun u => a.dualMap.rangeRestrict u ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = 0) h4 (fun r hr u _ => ?_)
        fun u v hu hv => ?_
    · rw [LinearMap.map_smul_of_tower, smul_tmul, ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 hr, tmul_zero]
    · rw [map_add, add_tmul, hu, hv, add_zero]
  have h6 := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := Z.subtype.restrictScalars A) (f₂ := (e.toLinearMap ∘ₗ Z.mkQ).restrictScalars A)
    (g₁ := (maximalIdeal A).subtype) (g₂ := (maximalIdeal A).mkQ)
    (fun x => by
      refine e.map_eq_zero_iff.trans ((Submodule.Quotient.mk_eq_zero _).trans ?_)
      exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
    (e.surjective.comp Z.mkQ_surjective) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) hinj
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _))
  have : Module.Finite A (R ⧸ I) := Module.Finite.of_surjective (Algebra.linearMap A (R ⧸ I)) hs
  have : Module.FinitePresentation A (R ⧸ I) := Module.finitePresentation_of_finite A _
  have : Module.Free A (R ⧸ I) :=
    Module.free_of_maximalIdeal_rTensor_injective ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).1 h6)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact FaithfulSMul.algebraMap_injective A (R ⧸ I)

omit [IsLocalRing R] in

/- English proof (translation)
Use `letI := Ideal.Quotient.field (maximalIdeal A)`. Set `k` to `A ⧸ maximalIdeal A`. Set `T'` to `k ⊗[A] T`. Set `π : T →+* T'` to `Algebra.TensorProduct.includeRight.toRingHom`. Establish `hπ : Surjective π` using `Algebra.TensorProduct.includeRight_surjective _ Ideal.Quotient.mk_surjective`.

Establish `hker : RingHom.ker π = (maximalIdeal A).map (algebraMap A T)`. Use extensionality with `t`. Rewrite using `[RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal A)).injective, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]`. Both sides reduce to the same expression. Establish `hq' : (q.map π).IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (hker ▸ hm)`.

Establish `hc : (q.map π).comap π = q`. Rewrite using `[Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.2 hm]`. Establish `hsub : q.primeCompl.map π = (q.map π).primeCompl`. Use `Ideal.map_primeCompl_comap_of_surjective π hπ (q.map π)` as an intermediate fact. Simplify `this` using `only [hc]`.

Set `S` to `Localization.AtPrime (q.map π)`. Establish `hk` using `IsLocalization.ker_map (S := R) S π hsub`. Rewrite `hk` using `[hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Establish `hsurj : Surjective (IsLocalization.map (S` using `R) S π (hsub ▸ q.primeCompl.le_comap_map)) := by`. Establish `: IsLocalization (q.primeCompl.map π) S` using `by rw [hsub]; infer_instance`.

Conclude with `IsLocalization.map_surjective_of_surjective q.primeCompl R S hπ`. Establish `e` using `(RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hk)`. Establish `hss : Algebra.IsStandardSmoothOfRelativeDimension g k T'` using `inferInstance`. Establish `: Algebra.IsStandardSmooth k T'` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g`. Establish `hreg : IsRegularRing T'` using `isRegularRing_of_smooth k T'`.

Use `isRegularRing_iff.mp hreg (q.map π)` as an intermediate fact. Use `⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩` and prove the remaining obligations. Rewrite using `[← ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height (q.map π) S]`. Establish `hf : (algebraMap k T').IsStandardSmoothOfRelativeDimension g` using `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hss`. Take `⟨φ, hφC, hφ⟩` from `hf.exists_etale_mvPolynomial`.

Use `algebraize [φ]`. Use `haveI : IsScalarTower k (MvPolynomial (Fin g) k) T' := IsScalarTower.of_algebraMap_eq' hφC.symm`. Use `haveI hp := SmoothDim.isMaximal_under_of_finiteType k (MvPolynomial (Fin g) k) T' (q.map π)`. Establish `h1` using `ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k g ((q.map π).under (MvPolynomial (Fin g) k))`. Use `letI := Ideal.Quotient.field ((q.map π).under (MvPolynomial (Fin g) k))`.

Rewrite `h1` using `[ringKrullDim_eq_zero_of_field, add_zero]`. Establish `h2 : ((q.map π).under (MvPolynomial (Fin g) k)).height ≤ (q.map π).height`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown ((q.map π).under (MvPolynomial (Fin g) k)) (q.map π)]`. Conclude with `le_self_add`. Rewrite using `[← h1]`.

Conclude with `WithBot.coe_le_coe.mpr h2`.
-/
theorem regular_fibre {A T : Type} [CommRing A] [IsLocalRing A] [CommRing T] [Algebra A T] (g : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g A T] (q : Ideal T) [hq : q.IsMaximal]
    (hm : (maximalIdeal A).map (algebraMap A T) ≤ q) [Algebra T R] [IsLocalization.AtPrime R q] [Algebra A R]
    [IsScalarTower A T R] :
    IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  letI := Ideal.Quotient.field (maximalIdeal A)
  let k := A ⧸ maximalIdeal A
  let T' := k ⊗[A] T
  let π : T →+* T' := Algebra.TensorProduct.includeRight.toRingHom
  have hπ : Surjective π := Algebra.TensorProduct.includeRight_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (maximalIdeal A).map (algebraMap A T) := by
    ext t
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal A)).injective,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    rfl
  have hq' : (q.map π).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (hker ▸ hm)
  have hc : (q.map π).comap π = q := by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.2 hm]
  have hsub : q.primeCompl.map π = (q.map π).primeCompl := by
    have := Ideal.map_primeCompl_comap_of_surjective π hπ (q.map π)
    simpa only [hc] using this
  let S := Localization.AtPrime (q.map π)
  have hk := IsLocalization.ker_map (S := R) S π hsub
  rw [hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hk
  have hsurj : Surjective (IsLocalization.map (S := R) S π (hsub ▸ q.primeCompl.le_comap_map)) := by
    have : IsLocalization (q.primeCompl.map π) S := by rw [hsub]; infer_instance
    exact IsLocalization.map_surjective_of_surjective q.primeCompl R S hπ
  have e := (RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hk)
  have hss : Algebra.IsStandardSmoothOfRelativeDimension g k T' := inferInstance
  have : Algebra.IsStandardSmooth k T' := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hreg : IsRegularRing T' := isRegularRing_of_smooth k T'
  have := isRegularRing_iff.mp hreg (q.map π)
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height (q.map π) S]
  have hf : (algebraMap k T').IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hss
  obtain ⟨φ, hφC, hφ⟩ := hf.exists_etale_mvPolynomial
  algebraize [φ]
  haveI : IsScalarTower k (MvPolynomial (Fin g) k) T' := IsScalarTower.of_algebraMap_eq' hφC.symm
  haveI hp := SmoothDim.isMaximal_under_of_finiteType k (MvPolynomial (Fin g) k) T' (q.map π)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k g
    ((q.map π).under (MvPolynomial (Fin g) k))
  letI := Ideal.Quotient.field ((q.map π).under (MvPolynomial (Fin g) k))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  have h2 : ((q.map π).under (MvPolynomial (Fin g) k)).height ≤ (q.map π).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      ((q.map π).under (MvPolynomial (Fin g) k)) (q.map π)]
    exact le_self_add
  rw [← h1]
  exact WithBot.coe_le_coe.mpr h2

omit [IsLocalRing R] in
open AlgebraicGeometry in

/- English proof (translation)
Use `set x := p (closedPoint K) with hx`. Take `⟨U, hU, V, hV, hxV, e, hs⟩` from `hf.exists_isStandardSmoothOfRelativeDimension x`. Take `rfl : U = ⊤` from `(closedPoint_mem_iff U).1 (hc ▸ e hxV)`. Set `ψ : CommRingCat.of A ⟶ Γ(X, V)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ V e`. Use `letI : Algebra A Γ(X, V) := ψ.hom.toAlgebra`.

Establish `hψ : ψ.hom.IsStandardSmoothOfRelativeDimension g` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv hs`. Establish `hss : Algebra.IsStandardSmoothOfRelativeDimension g A Γ(X, V)` using `hψ`. Establish `: Algebra.IsStandardSmooth A Γ(X, V)` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g`. Establish `hV' : hV.fromSpec ≫ f = Spec.map ψ`. Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`.

Set `R : Type` to `X.presheaf.stalk x`. Use `letI : Algebra Γ(X, V) R := X.presheaf.algebra_section_stalk ⟨x, hxV⟩`. Establish `hloc : IsLocalization.AtPrime R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal` using `hV.isLocalization_stalk ⟨x, hxV⟩`. Use `letI : Algebra A R := ((algebraMap Γ(X, V) R).comp (algebraMap A Γ(X, V))).toAlgebra`. Establish `: IsScalarTower A Γ(X, V) R` using `IsScalarTower.of_algebraMap_eq' rfl`.

Establish `hq` using `hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hp`. Establish `: IsNoetherianRing Γ(X, V)` using `Algebra.FiniteType.isNoetherianRing A _`. Establish `hm : (maximalIdeal A).map (algebraMap A Γ(X, V)) ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal`. Establish `h₁ : Spec.map ψ (hV.primeIdealOf ⟨x, hxV⟩) = closedPoint A`. Rewrite using `[← hV']`.

Conclude with `(congrArg f (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)).trans hc`. Conclude with `Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h₁).ge`. Establish `: Module.Flat Γ(X, V) R` using `IsLocalization.flat R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl`. Use `⟨R, inferInstance, inferInstance, IsLocalization.isNoetherianRing (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl R inferInstance, inferInstance, X.fromSpecStalk x, (Scheme.stalkClosedPointTo p).hom, Module.Flat.trans A Γ(X, V) R, inferInstanceAs (IsPreimmersion (X.fromSpecStalk x) …` and prove the remaining obligations. Rewrite using `[← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Category.assoc, hV', ← Spec.map_comp]`.

Both sides reduce to the same expression.
-/
theorem exists_localRing {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) {K : Type} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : IsClosed {p (closedPoint K)}) (hc : f (p (closedPoint K)) = closedPoint A) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra A R)
      (ξ : Spec (CommRingCat.of R) ⟶ X) (g₀ : R →+* K), Module.Flat A R ∧ IsPreimmersion ξ ∧
      ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧ IsLocalHom g₀ ∧
      Spec.map (CommRingCat.ofHom g₀) ≫ ξ = p ∧ IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  set x := p (closedPoint K) with hx
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : U = ⊤ := (closedPoint_mem_iff U).1 (hc ▸ e hxV)
  let ψ : CommRingCat.of A ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ V e
  letI : Algebra A Γ(X, V) := ψ.hom.toAlgebra
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv hs
  have hss : Algebra.IsStandardSmoothOfRelativeDimension g A Γ(X, V) := hψ
  have : Algebra.IsStandardSmooth A Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hV' : hV.fromSpec ≫ f = Spec.map ψ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp]
  let R : Type := X.presheaf.stalk x
  letI : Algebra Γ(X, V) R := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hloc : IsLocalization.AtPrime R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  letI : Algebra A R := ((algebraMap Γ(X, V) R).comp (algebraMap A Γ(X, V))).toAlgebra
  have : IsScalarTower A Γ(X, V) R := IsScalarTower.of_algebraMap_eq' rfl
  have hq := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hp
  have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing A _
  have hm : (maximalIdeal A).map (algebraMap A Γ(X, V)) ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    have h₁ : Spec.map ψ (hV.primeIdealOf ⟨x, hxV⟩) = closedPoint A := by
      rw [← hV']
      exact (congrArg f (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)).trans hc
    exact Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h₁).ge
  have : Module.Flat Γ(X, V) R := IsLocalization.flat R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  refine ⟨R, inferInstance, inferInstance,
    IsLocalization.isNoetherianRing (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl R inferInstance, inferInstance,
    X.fromSpecStalk x, (Scheme.stalkClosedPointTo p).hom, Module.Flat.trans A Γ(X, V) R,
    inferInstanceAs (IsPreimmersion (X.fromSpecStalk x)), ?_, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p, regular_fibre g _ hm⟩
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Category.assoc, hV', ← Spec.map_comp]
  rfl

end GlobalTheory.FibreAcyclic
