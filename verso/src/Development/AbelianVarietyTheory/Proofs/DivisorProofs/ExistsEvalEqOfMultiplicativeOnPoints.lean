import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorEqZeroOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupLikeIntegralOfFiniteFree
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hli : LinearIndependent C (fun x : A →ₐ[O] C => x.toLinearMap)` using `linearIndependent_algHom_toLinearMap O A C`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination C (fun x : A →ₐ[O] C => x.toLinearMap)) (LinearMap.ker_eq_bot.mpr hli)`. Set `l : (A →ₗ[O] C) →ₗ[C] C` to `Finsupp.linearCombination C κ ∘ₗ g`. Establish `hl : ∀ x : A →ₐ[O] C, l x.toLinearMap = κ x`. Introduce `x`.

Use `LinearMap.congr_fun hg (Finsupp.single x 1)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul, LinearMap.id_apply] at this`. Simplify using `only [l, LinearMap.comp_apply, this, Finsupp.linearCombination_single, one_smul]`. Set `B` to `Module.Free.chooseBasis O A`. Set `c` to `fun i => l (Algebra.linearMap O C ∘ₗ B.coord i)`.

Establish `hc : ∀ f : A →ₗ[O] C, l f = ∑ i, f (B i) * c i`. Introduce `f`. Establish `: f = ∑ i, f (B i) • (Algebra.linearMap O C ∘ₗ B.coord i)`. Use `B.ext fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `i _ hij`. Simplify using `[Finsupp.single_apply, hij.symm]`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [this]`.

Simplify using `only [map_sum, map_smul, smul_eq_mul, c]`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c`. Use `choose o ho using hd`. Use `⟨d, ∑ i, o i • B i, nonZeroDivisors.coe_ne_zero d, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hl, hc, Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, ho, Algebra.smul_def]`. Simplify using `only [AlgHom.toLinearMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_smul_fun_eq_eval_points (O C A : Type) [CommRing O] [IsDomain O] [Field C]
    [Algebra O C] [IsFractionRing O C] [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Free O A] (κ : (A →ₐ[O] C) → C) :
    ∃ (d : O) (a : A), d ≠ 0 ∧ ∀ x : A →ₐ[O] C, x a = algebraMap O C d * κ x := by
  classical
  have hli : LinearIndependent C (fun x : A →ₐ[O] C => x.toLinearMap) :=
    linearIndependent_algHom_toLinearMap O A C
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination C (fun x : A →ₐ[O] C => x.toLinearMap))
    (LinearMap.ker_eq_bot.mpr hli)
  let l : (A →ₗ[O] C) →ₗ[C] C := Finsupp.linearCombination C κ ∘ₗ g
  have hl : ∀ x : A →ₐ[O] C, l x.toLinearMap = κ x := by
    intro x
    have := LinearMap.congr_fun hg (Finsupp.single x 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at this
    simp only [l, LinearMap.comp_apply, this, Finsupp.linearCombination_single, one_smul]
  let B := Module.Free.chooseBasis O A
  let c := fun i => l (Algebra.linearMap O C ∘ₗ B.coord i)
  have hc : ∀ f : A →ₗ[O] C, l f = ∑ i, f (B i) * c i := by
    intro f
    have : f = ∑ i, f (B i) • (Algebra.linearMap O C ∘ₗ B.coord i) := by
      refine B.ext fun j => ?_
      rw [LinearMap.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Finsupp.single_apply, hij.symm]
      · simp
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, smul_eq_mul, c]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose o ho using hd
  refine ⟨d, ∑ i, o i • B i, nonZeroDivisors.coe_ne_zero d, fun x => ?_⟩
  rw [← hl, hc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho, Algebra.smul_def]
  simp only [AlgHom.toLinearMap_apply]
  ring

open scoped TensorProduct in
/- English proof (translation)
Use `haveI : IsArtinianRing V := IsArtinianRing.of_finite C V`. Establish `hmem : v ∈ (⊥ : Ideal V).jacobson`. Rewrite using `[Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `m ⟨-, hm⟩`. Use `letI : Field (V ⧸ m) := Ideal.Quotient.field m`.

Establish `hsurj : Function.Surjective (algebraMap C (V ⧸ m))` using `IsSepClosed.algebraMap_surjective C _`. Set `eqv : C ≃ₐ[C] V ⧸ m` to `AlgEquiv.ofBijective (Algebra.ofId C (V ⧸ m)) ⟨(algebraMap C (V ⧸ m)).injective, hsurj⟩`. Establish `h` using `hv (eqv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m))`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe] at h`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ eqv.symm.injective).mp h)`.

Rewrite `hmem` using `[IsArtinianRing.jacobson_eq_radical]`. Take `⟨n, hn⟩` from `hmem`. Conclude with `IsReduced.eq_zero v ⟨n, by simpa using hn⟩`.
-/
private lemma eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced {C V : Type} [Field C] [IsAlgClosed C] [CommRing V]
    [Algebra C V] [Module.Finite C V] [IsReduced V] (v : V) (hv : ∀ z : V →ₐ[C] C, z v = 0) :
    v = 0 := by
  haveI : IsArtinianRing V := IsArtinianRing.of_finite C V
  have hmem : v ∈ (⊥ : Ideal V).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    letI : Field (V ⧸ m) := Ideal.Quotient.field m
    have hsurj : Function.Surjective (algebraMap C (V ⧸ m)) := IsSepClosed.algebraMap_surjective C _
    let eqv : C ≃ₐ[C] V ⧸ m := AlgEquiv.ofBijective (Algebra.ofId C (V ⧸ m))
      ⟨(algebraMap C (V ⧸ m)).injective, hsurj⟩
    have h := hv (eqv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ eqv.symm.injective).mp h)
  rw [IsArtinianRing.jacobson_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero v ⟨n, by simpa using hn⟩

open scoped TensorProduct in
/- English proof (translation)
Establish `hsep : ∀ z' : V →ₐ[C] C, z' ≠ z → ∃ a : V, z a ≠ z' a`. Introduce `z' hz'`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hz' (AlgHom.ext fun a => (h a).symm)`.

Set `u : (V →ₐ[C] C) → V` to `fun z' => if h : z' ≠ z then (z (hsep z' h).choose - z' (hsep z' h).choose)⁻¹ • ((hsep z' h).choose - algebraMap C V (z' (hsep z' h).choose)) else 1`. Establish `hu : ∀ z', z (u z') = 1`. Introduce `z'`. Distinguish the cases in `h : z' ≠ z`. Simplify using `only [u, dif_pos h, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]`.

Conclude with `inv_mul_cancel₀ (sub_ne_zero.mpr (hsep z' h).choose_spec)`. Simplify using `only [u]`. Rewrite using `[dif_neg h, map_one]`. Establish `hu' : ∀ z', z' ≠ z → z' (u z') = 0`. Introduce `z' h`.

Simplify using `only [u]`. Rewrite using `[dif_pos h]`. Simplify using the standard rewrite rules. Use `⟨∏ z' ∈ Finset.univ.erase z, u z', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_eq_one fun z' _ => hu z'`. Introduce `z' hz'`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hz', Finset.mem_univ _⟩) (hu' z' hz')`.
-/
private lemma exists_eq_one_and_eq_zero_of_ne_algHom {C V : Type} [Field C] [CommRing V] [Algebra C V]
    [Fintype (V →ₐ[C] C)] (z : V →ₐ[C] C) :
    ∃ w : V, z w = 1 ∧ ∀ z' : V →ₐ[C] C, z' ≠ z → z' w = 0 := by
  have hsep : ∀ z' : V →ₐ[C] C, z' ≠ z → ∃ a : V, z a ≠ z' a := by
    intro z' hz'
    by_contra h
    push_neg at h
    exact hz' (AlgHom.ext fun a => (h a).symm)
  classical
  let u : (V →ₐ[C] C) → V := fun z' =>
    if h : z' ≠ z then
      (z (hsep z' h).choose - z' (hsep z' h).choose)⁻¹ •
        ((hsep z' h).choose - algebraMap C V (z' (hsep z' h).choose))
    else 1
  have hu : ∀ z', z (u z') = 1 := by
    intro z'
    by_cases h : z' ≠ z
    · simp only [u, dif_pos h, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, smul_eq_mul]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep z' h).choose_spec)
    · simp only [u]
      rw [dif_neg h, map_one]
  have hu' : ∀ z', z' ≠ z → z' (u z') = 0 := by
    intro z' h
    simp only [u]
    rw [dif_pos h]
    simp
  refine ⟨∏ z' ∈ Finset.univ.erase z, u z', ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z' _ => hu z'
  · intro z' hz'
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hz', Finset.mem_univ _⟩) (hu' z' hz')

open scoped TensorProduct in
/- English proof (translation)
Establish `e1 : ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j = ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) - (∑ i, c i * X i) * ∑ j, c j * Y j`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]`. Use `congr 1`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[e1, h, sub_self]`.
-/
private lemma sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq {C ι : Type} [Field C] [Fintype ι] (c X Y : ι → C)
    (M : ι → ι → ι → C)
    (h : ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) = (∑ i, c i * X i) * ∑ j, c j * Y j) :
    ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j = 0 := by
  have e1 : ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j =
      ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) - (∑ i, c i * X i) * ∑ j, c j * Y j := by
    simp only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    congr 1
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, h, sub_self]

open scoped TensorProduct in

/- English proof (translation)
Introduce `O C A _ _ _ _ _ _ _ _ _ _ _ hred Δ ε κ hmul _`. Set `e` to `Module.Free.chooseBasis O A`. Set `eC : Module.Basis (Module.Free.ChooseBasisIndex O A) C (C ⊗[O] A)` to `Algebra.TensorProduct.basis C e`. Set `ext : (A →ₐ[O] C) → (C ⊗[O] A →ₐ[C] C)` to `fun x => Algebra.TensorProduct.lift (Algebra.ofId C C) x (fun _ _ => Commute.all _ _)`. Set `res : (C ⊗[O] A →ₐ[C] C) → (A →ₐ[O] C)` to `fun z => (z.restrictScalars O).comp Algebra.TensorProduct.includeRight`.

Establish `hres : ∀ x, res (ext x) = x`. Introduce `x`. Use extensionality with `a`. Simplify using `[res, ext]`. Establish `hevC : ∀ (z : C ⊗[O] A →ₐ[C] C) (a : Module.Free.ChooseBasisIndex O A → C), z (∑ i, a i • eC i) = ∑ i, a i * res z (e i)`.

Introduce `z a`. Simplify using `[eC, res, map_sum, Algebra.TensorProduct.basis_apply]`. Establish `hcoord : ∀ a : Module.Free.ChooseBasisIndex O A → C, (∀ x : A →ₐ[O] C, ∑ i, a i * x (e i) = 0) → a = 0`. Introduce `a ha`. Establish `hv : ∑ i, a i • eC i = 0`.

Use `eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced (C := C) _ fun z => ?_` and prove the remaining obligations. Rewrite using `[hevC]`. Conclude with `ha (res z)`. Use function extensionality and compare the values at `i`. Establish `hi` using `congrArg (fun v => eC.repr v i) hv`.

Simplify `hi` using `[Finsupp.single_apply]`. Use `haveI : Finite (C ⊗[O] A →ₐ[C] C) := (linearIndependent_toLinearMap C (C ⊗[O] A) C).finite`. Use `letI : Fintype (C ⊗[O] A →ₐ[C] C) := Fintype.ofFinite _`. Use `choose w hw1 hw0 using fun z : C ⊗[O] A →ₐ[C] C => exists_eq_one_and_eq_zero_of_ne_algHom z`. Set `b' : C ⊗[O] A` to `∑ z, κ (res z) • w z`.

Set `c` to `eC.repr b'`. Establish `hval : ∀ x, κ x = ∑ i, c i * x (e i)`. Introduce `x`. Establish `h1 : ext x b' = κ x`. Simplify using `only [b', map_sum, map_smul, smul_eq_mul]`.

Rewrite using `[Finset.sum_eq_single (ext x)]`. Rewrite using `[hw1, mul_one, hres]`. Introduce `z _ hz`. Rewrite using `[hw0 z (ext x) (Ne.symm hz), mul_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[← h1]`. Use `conv_lhs => rw [← eC.sum_repr b']`. Rewrite using `[hevC, hres]`. Set `m : Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A → O` to `fun k i j => (e.tensorProduct e).repr (Δ (e k)) (i, j)`. Establish `hprod : ∀ (x y : A →ₐ[O] C) k, (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (Δ (e k)) = ∑ i, ∑ j, algebraMap O C (m k i j) * (x (e i) * y (e j))`.

Introduce `x y k`. Use `conv_lhs => rw [← (e.tensorProduct e).sum_repr (Δ (e k))]`. Simplify using `only [map_sum, map_smul, Module.Basis.tensorProduct_apply, Algebra.smul_def, Fintype.sum_prod_type, map_mul, AlgHom.commutes, Algebra.TensorProduct.lift_tmul, m]`. Establish `key : ∀ x y : A →ₐ[O] C, ∑ j, (∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i)) * y (e j) = 0`. Introduce `x y`.

Establish `h` using `hmul x y`. Simplify using `only [hval, AlgHom.comp_apply, hprod] at h`. Conclude with `sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq c (fun i => x (e i)) (fun j => y (e j)) (fun k i j => algebraMap O C (m k i j)) h`. Establish `hrel : ∀ i j, c i * c j = ∑ k, c k * algebraMap O C (m k i j)`. Establish `h1 : ∀ j, ∀ x : A →ₐ[O] C, ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i) = 0`.

Introduce `j x`. Conclude with `congrFun (hcoord (fun j => ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i)) (key x)) j`. Introduce `i j`. Establish `h2` using `congrFun (hcoord (fun i => ∑ k, c k * algebraMap O C (m k i j) - c i * c j) (h1 j)) i`. Conclude with `(sub_eq_zero.mp h2).symm`.

Set `M : Submodule O C` to `Submodule.span O (insert 1 (Set.range c))`. Establish `hcM : ∀ i, c i ∈ M` using `fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)`. Establish `hoM : (1 : C) ∈ M` using `Submodule.subset_span (Set.mem_insert 1 _)`. Establish `hMM : M * M ≤ M`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨s, hs, t, ht, rfl⟩`. Apply the tactic sequence `rcases hs with rfl | ⟨i, rfl⟩ <;> rcases ht with rfl | ⟨j, rfl⟩ <;> dsimp only`. Rewrite using `[one_mul]`. Conclude with `hoM`. Rewrite using `[one_mul]`.

Conclude with `hcM j`. Rewrite using `[mul_one]`. Conclude with `hcM i`. Rewrite using `[hrel]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (hcM k)`. Set `S : Subalgebra O C` to `M.toSubalgebra hoM fun u v hu hv => hMM (Submodule.mul_mem_mul hu hv)`. Establish `hfg : (Subalgebra.toSubmodule S).FG` using `Submodule.fg_span ((Set.finite_range c).insert 1)`. Establish `hint : ∀ i, ∃ o : O, algebraMap O C o = c i` using `fun i => IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_mem_of_fg S hfg _ (hcM i))`.

Use `choose o ho using hint`. Use `⟨∑ i, o i • e i, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hval, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, ho]`.
-/
theorem _root_.GlobalTheory.exists_eval_eq_of_multiplicative_on_points : ∀ (O C A : Type) [CommRing O] [IsDomain O] [Field C] [IsAlgClosed C] [Algebra O C] [IsFractionRing O C] [IsIntegrallyClosed O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Free O A], IsReduced (C ⊗[O] A) → ∀ (Δ : A →ₐ[O] A ⊗[O] A) (ε : A →ₐ[O] O) (κ : (A →ₐ[O] C) → C), (∀ x y : A →ₐ[O] C, κ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) = κ x * κ y) → κ ((Algebra.ofId O C).comp ε) = 1 → ∃ b : A, ∀ x : A →ₐ[O] C, x b = κ x := by
  intro O C A _ _ _ _ _ _ _ _ _ _ _ hred Δ ε κ hmul _
  classical
  let e := Module.Free.chooseBasis O A
  let eC : Module.Basis (Module.Free.ChooseBasisIndex O A) C (C ⊗[O] A) :=
    Algebra.TensorProduct.basis C e
  let ext : (A →ₐ[O] C) → (C ⊗[O] A →ₐ[C] C) := fun x =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) x (fun _ _ => Commute.all _ _)
  let res : (C ⊗[O] A →ₐ[C] C) → (A →ₐ[O] C) := fun z =>
    (z.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hres : ∀ x, res (ext x) = x := by
    intro x
    ext a
    simp [res, ext]
  have hevC : ∀ (z : C ⊗[O] A →ₐ[C] C) (a : Module.Free.ChooseBasisIndex O A → C),
      z (∑ i, a i • eC i) = ∑ i, a i * res z (e i) := by
    intro z a
    simp [eC, res, map_sum, Algebra.TensorProduct.basis_apply]
  have hcoord : ∀ a : Module.Free.ChooseBasisIndex O A → C,
      (∀ x : A →ₐ[O] C, ∑ i, a i * x (e i) = 0) → a = 0 := by
    intro a ha
    have hv : ∑ i, a i • eC i = 0 := by
      refine eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced (C := C) _ fun z => ?_
      rw [hevC]
      exact ha (res z)
    funext i
    have hi := congrArg (fun v => eC.repr v i) hv
    simpa [Finsupp.single_apply] using hi
  haveI : Finite (C ⊗[O] A →ₐ[C] C) := (linearIndependent_toLinearMap C (C ⊗[O] A) C).finite
  letI : Fintype (C ⊗[O] A →ₐ[C] C) := Fintype.ofFinite _
  choose w hw1 hw0 using fun z : C ⊗[O] A →ₐ[C] C => exists_eq_one_and_eq_zero_of_ne_algHom z
  let b' : C ⊗[O] A := ∑ z, κ (res z) • w z
  let c := eC.repr b'
  have hval : ∀ x, κ x = ∑ i, c i * x (e i) := by
    intro x
    have h1 : ext x b' = κ x := by
      simp only [b', map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single (ext x)]
      · rw [hw1, mul_one, hres]
      · intro z _ hz
        rw [hw0 z (ext x) (Ne.symm hz), mul_zero]
      · simp
    rw [← h1]
    conv_lhs => rw [← eC.sum_repr b']
    rw [hevC, hres]
  let m : Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A →
      Module.Free.ChooseBasisIndex O A → O := fun k i j => (e.tensorProduct e).repr (Δ (e k)) (i, j)
  have hprod : ∀ (x y : A →ₐ[O] C) k,
      (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (Δ (e k)) =
        ∑ i, ∑ j, algebraMap O C (m k i j) * (x (e i) * y (e j)) := by
    intro x y k
    conv_lhs => rw [← (e.tensorProduct e).sum_repr (Δ (e k))]
    simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply,
      Algebra.smul_def, Fintype.sum_prod_type, map_mul, AlgHom.commutes,
      Algebra.TensorProduct.lift_tmul, m]
  have key : ∀ x y : A →ₐ[O] C, ∑ j, (∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
      x (e i)) * y (e j) = 0 := by
    intro x y
    have h := hmul x y
    simp only [hval, AlgHom.comp_apply, hprod] at h
    exact sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq c (fun i => x (e i)) (fun j => y (e j))
      (fun k i j => algebraMap O C (m k i j)) h
  have hrel : ∀ i j, c i * c j = ∑ k, c k * algebraMap O C (m k i j) := by
    have h1 : ∀ j, ∀ x : A →ₐ[O] C,
        ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i) = 0 := by
      intro j x
      exact congrFun (hcoord (fun j => ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
        x (e i)) (key x)) j
    intro i j
    have h2 := congrFun (hcoord (fun i => ∑ k, c k * algebraMap O C (m k i j) - c i * c j) (h1 j)) i
    exact (sub_eq_zero.mp h2).symm
  let M : Submodule O C := Submodule.span O (insert 1 (Set.range c))
  have hcM : ∀ i, c i ∈ M := fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)
  have hoM : (1 : C) ∈ M := Submodule.subset_span (Set.mem_insert 1 _)
  have hMM : M * M ≤ M := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    rcases hs with rfl | ⟨i, rfl⟩ <;> rcases ht with rfl | ⟨j, rfl⟩ <;> dsimp only
    · rw [one_mul]
      exact hoM
    · rw [one_mul]
      exact hcM j
    · rw [mul_one]
      exact hcM i
    · rw [hrel]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hcM k)
  let S : Subalgebra O C :=
    M.toSubalgebra hoM fun u v hu hv => hMM (Submodule.mul_mem_mul hu hv)
  have hfg : (Subalgebra.toSubmodule S).FG := Submodule.fg_span ((Set.finite_range c).insert 1)
  have hint : ∀ i, ∃ o : O, algebraMap O C o = c i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_mem_of_fg S hfg _ (hcM i))
  choose o ho using hint
  refine ⟨∑ i, o i • e i, fun x => ?_⟩
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho]

end GlobalTheory
