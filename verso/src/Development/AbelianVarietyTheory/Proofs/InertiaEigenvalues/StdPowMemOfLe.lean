import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulMemIff

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Introduce `i`. Rewrite using `[Pi.basisFun_apply, Pi.single_apply]`. Use `split_ifs`. Conclude with `⟨1, map_one _⟩`. Conclude with `⟨0, map_zero _⟩`.

Consider the case `zero => intro i`. Conclude with `⟨0, map_zero _⟩`. Consider the case `add y z _ _ hy hz => intro i`. Conclude with `add_mem (hy i) (hz i)`. Consider the case `smul a y _ hy`.

Introduce `i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem ⟨a, rfl⟩ (hy i)`. Introduce `hx choose a ha using hx`. Establish `: x = ∑ i, a i • Pi.basisFun K (Fin r) i`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def, ha]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_std {x : Fin r → K} :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔
      ∀ i, x i ∈ (algebraMap O K).range := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz => intro i; exact add_mem (hy i) (hz i)
    | smul a y _ hy =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def]
      exact mul_mem ⟨a, rfl⟩ (hy i)
  · intro hx
    choose a ha using hx
    have : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
      funext j
      simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Establish `e1 : (fun i => cK (g.mulVec x i)) = (g.map cK).mulVec (fun i => cK (x i))`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec cK.toRingHom g x i`. Unfold `hf`. Rewrite using `[e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]`.
-/
theorem hf_mulVec (cK : K ≃+* K) (J g : Matrix (Fin r) (Fin r) K)
    (hU : (g.map cK).transpose * J * g = J) (x y : Fin r → K) :
    hf cK J (g.mulVec x) (g.mulVec y) = hf cK J x y := by
  have e1 : (fun i => cK (g.mulVec x i)) = (g.map cK).mulVec (fun i => cK (x i)) := by
    funext i
    exact RingHom.map_mulVec cK.toRingHom g x i
  unfold hf
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hU]

/- English proof (translation)
Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Rewrite `hx`, `hy` using `[mem_std]`. Unfold `hf`.

Simplify using `only [dotProduct, Matrix.mulVec, Matrix.map_apply]`. Use `Subring.sum_mem _ fun i _ => mul_mem (conj_mem_range c cK hcK (hx i)) ?_` and prove the remaining obligations. Conclude with `Subring.sum_mem _ fun j _ => mul_mem ⟨_, rfl⟩ (hy j)`. Introduce `h`. Rewrite using `[mem_std]`.

Use `set w : Fin r → K := Matrix.vecMul (fun i => cK (x i)) (J.map (algebraMap O K)) with hw`. Establish `hwR : ∀ j, w j ∈ (algebraMap O K).range`. Introduce `j`. Establish `hej : Pi.single j (1 : K) ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))` using `Submodule.subset_span ⟨j, Pi.basisFun_apply K (Fin r) j⟩`. Use `h _ hej` as an intermediate fact.

Unfold `hf at this`. Rewrite `this` using `[Matrix.dotProduct_mulVec, dotProduct_single, mul_one]`. Then use the resulting hypothesis. Establish `hJJ : J.map (algebraMap O K) * J⁻¹.map (algebraMap O K) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hx' : (fun i => cK (x i)) = Matrix.vecMul w (J⁻¹.map (algebraMap O K))`.

Rewrite using `[hw, Matrix.vecMul_vecMul, hJJ, Matrix.vecMul_one]`. Introduce `i`. Establish `hi : cK (x i) ∈ (algebraMap O K).range`. Rewrite using `[show cK (x i) = (fun i => cK (x i)) i from rfl, hx']`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.map_apply]`.

Conclude with `Subring.sum_mem _ fun j _ => mul_mem (hwR j) ⟨_, rfl⟩`. Rewrite using `[← hc2 (x i)]`. Conclude with `conj_mem_range c cK hcK hi`.
-/
theorem std_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) O) (hJ : IsUnit J.det) :
    IsSD cK (J.map (algebraMap O K)) (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) := by
  classical
  intro x
  constructor
  · intro hx y hy
    rw [mem_std] at hx hy
    unfold hf
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem (conj_mem_range c cK hcK (hx i)) ?_
    exact Subring.sum_mem _ fun j _ => mul_mem ⟨_, rfl⟩ (hy j)
  · intro h
    rw [mem_std]
    set w : Fin r → K := Matrix.vecMul (fun i => cK (x i)) (J.map (algebraMap O K)) with hw
    have hwR : ∀ j, w j ∈ (algebraMap O K).range := by
      intro j
      have hej : Pi.single j (1 : K) ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) :=
        Submodule.subset_span ⟨j, Pi.basisFun_apply K (Fin r) j⟩
      have := h _ hej
      unfold hf at this
      rwa [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    have hJJ : J.map (algebraMap O K) * J⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    have hx' : (fun i => cK (x i)) = Matrix.vecMul w (J⁻¹.map (algebraMap O K)) := by
      rw [hw, Matrix.vecMul_vecMul, hJJ, Matrix.vecMul_one]
    intro i
    have hi : cK (x i) ∈ (algebraMap O K).range := by
      rw [show cK (x i) = (fun i => cK (x i)) i from rfl, hx']
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
      exact Subring.sum_mem _ fun j _ => mul_mem (hwR j) ⟨_, rfl⟩
    rw [← hc2 (x i)]
    exact conj_mem_range c cK hcK hi

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) y`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ`. Use `⟨k, u * a, ?_⟩` and prove the remaining obligations. Establish `hb' : algebraMap O K b ≠ 0`.

Introduce `h; exact hb0 (IsFractionRing.injective O K (by simpa using h))`. Rewrite using `[← hu, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) (y : K) :
    ∃ k : ℕ, algebraMap O K (ϖ ^ k) * y ∈ (algebraMap O K).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨k, u * a, ?_⟩
  have hb' : algebraMap O K b ≠ 0 := by
    intro h; exact hb0 (IsFractionRing.injective O K (by simpa using h))
  rw [← hu, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Rewrite using `[mem_std]`. Introduce `i`. Establish `hle : k i ≤ ∑ j, k j` using `Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← Nat.sub_add_cancel hle, pow_add, map_mul, mul_assoc]`. Conclude with `mul_mem ⟨_, rfl⟩ (hk i)`.
-/
theorem std_pow_mem_of_le {ϖ : O} {x : Fin r → K} {k : Fin r → ℕ}
    (hk : ∀ i, algebraMap O K (ϖ ^ k i) * x i ∈ (algebraMap O K).range) :
    (ϖ ^ (∑ i, k i)) • x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  rw [mem_std]
  intro i
  have hle : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Pi.smul_apply, Algebra.smul_def, ← Nat.sub_add_cancel hle, pow_add, map_mul, mul_assoc]
  exact mul_mem ⟨_, rfl⟩ (hk i)

/- English proof (translation)
Use `set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r)))`. Establish `hex : ∀ (x : L0.toAddSubgroup) (i : Fin r), ∃ a : O, algebraMap O K a = (x : Fin r → K) i` using `fun x i => mem_std.1 x.2 i`. Use `choose a ha using hex`. Establish `hadd : ∀ x y i, a (x + y) i = a x i + a y i`. Introduce `x y i`.

Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_add, ha, ha, ha]`. Both sides reduce to the same expression. Set `ψ : L0.toAddSubgroup →+ (Fin r → IsLocalRing.ResidueField O)` to `AddMonoidHom.mk' (fun x i => IsLocalRing.residue O (a x i)) (by`. Introduce `x y`.

Use function extensionality and compare the values at `i`. Simplify using `[hadd])`. Establish `hker : (L0.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf L0.toAddSubgroup = ψ.ker`. Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]`.

Express the relevant statement in the definitionally equal form `(x : Fin r → K) ∈ L0.map _ ↔ (fun i => IsLocalRing.residue O (a x i)) = 0`. Rewrite using `[funext_iff]`. Simplify using `only [Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩ i`.

Take `⟨b, hb⟩` from `mem_std.1 hy i`. Use `⟨b, IsFractionRing.injective O K ?_⟩` and prove the remaining obligations. Rewrite using `[ha, ← hyx, map_mul, hb]`. Simplify using `[Algebra.smul_def]`. Introduce `h choose b hb using h`.

Use `⟨fun i => algebraMap O K (b i), mem_std.2 fun i => ⟨b i, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show (ϖ • (fun i => algebraMap O K (b i))) i = (x : Fin r → K) i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← map_mul, ← hb, ha]`. Establish `hsurj : Function.Surjective ψ`.

Introduce `z`. Use `choose b hb using fun i => IsLocalRing.residue_surjective (z i)`. Establish `hm : (fun i => algebraMap O K (b i)) ∈ L0.toAddSubgroup` using `mem_std.2 fun i => ⟨b i, rfl⟩`. Use `⟨⟨_, hm⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `IsLocalRing.residue O (a ⟨_, hm⟩ i) = z i`. Establish `: a ⟨_, hm⟩ i = b i` using `IsFractionRing.injective O K (by rw [ha])`. Rewrite using `[this, hb]`. Unfold `idx`. Rewrite using `[AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]`.
-/
theorem idx_std {ϖ : O} (hϖ : Irreducible ϖ) :
    idx ϖ (Submodule.span O (Set.range (Pi.basisFun K (Fin r))) : Submodule O (Fin r → K)) =
      Nat.card (IsLocalRing.ResidueField O) ^ r := by
  classical
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r)))
  have hex : ∀ (x : L0.toAddSubgroup) (i : Fin r), ∃ a : O, algebraMap O K a = (x : Fin r → K) i :=
    fun x i => mem_std.1 x.2 i
  choose a ha using hex
  have hadd : ∀ x y i, a (x + y) i = a x i + a y i := by
    intro x y i
    apply IsFractionRing.injective O K
    rw [map_add, ha, ha, ha]; rfl
  let ψ : L0.toAddSubgroup →+ (Fin r → IsLocalRing.ResidueField O) :=
    AddMonoidHom.mk' (fun x i => IsLocalRing.residue O (a x i)) (by
      intro x y; funext i; simp [hadd])
  have hker : (L0.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
      L0.toAddSubgroup = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (x : Fin r → K) ∈ L0.map _ ↔ (fun i => IsLocalRing.residue O (a x i)) = 0
    rw [funext_iff]
    simp only [Pi.zero_apply, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy, hyx⟩ i
      obtain ⟨b, hb⟩ := mem_std.1 hy i
      refine ⟨b, IsFractionRing.injective O K ?_⟩
      rw [ha, ← hyx, map_mul, hb]
      simp [Algebra.smul_def]
    · intro h
      choose b hb using h
      refine ⟨fun i => algebraMap O K (b i), mem_std.2 fun i => ⟨b i, rfl⟩, ?_⟩
      funext i
      show (ϖ • (fun i => algebraMap O K (b i))) i = (x : Fin r → K) i
      rw [Pi.smul_apply, Algebra.smul_def, ← map_mul, ← hb, ha]
  have hsurj : Function.Surjective ψ := by
    intro z
    choose b hb using fun i => IsLocalRing.residue_surjective (z i)
    have hm : (fun i => algebraMap O K (b i)) ∈ L0.toAddSubgroup := mem_std.2 fun i => ⟨b i, rfl⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    funext i
    change IsLocalRing.residue O (a ⟨_, hm⟩ i) = z i
    have : a ⟨_, hm⟩ i = b i := IsFractionRing.injective O K (by rw [ha])
    rw [this, hb]
  unfold idx
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

end GlobalTheory.HermNbr
