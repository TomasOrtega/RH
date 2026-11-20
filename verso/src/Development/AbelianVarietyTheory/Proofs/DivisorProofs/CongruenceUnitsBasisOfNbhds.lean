import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongOpen

variable (L : Type) [Field L] [NumberField L]

local notation "A" => FiniteAdeleRing (𝓞 ℚ) ℚ

/- English proof (translation)
Use `letI : Algebra A (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra`. Rewrite using `[Algebra.smul_def]`. Use `show (Algebra.TensorProduct.includeRight a : AfE ℚ L) * _ = _`. Rewrite using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem rsmul_tmul (a y : A) (x : L) :
    letI : Algebra A (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    a • (x ⊗ₜ[ℚ] y : AfE ℚ L) = x ⊗ₜ (a * y) := by
  letI : Algebra A (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.smul_def]
  show (Algebra.TensorProduct.includeRight a : AfE ℚ L) * _ = _
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable {L} {d : ℕ} (b : Module.Basis (Fin d) ℤ (𝓞 L))

def coordSub : AddSubgroup (AfE ℚ L) where
  carrier := {t | ∃ z : Fin d → A, (∀ i, z i ∈ intAd ℚ) ∧ ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i = t}
  zero_mem' := ⟨0, fun _ => zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', fun i => add_mem (hz i) (hz' i), by
      simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, fun i => neg_mem (hz i), by simp [TensorProduct.tmul_neg]⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coordSub {t : AfE ℚ L} :
    t ∈ coordSub b ↔ ∃ z : Fin d → A, (∀ i, z i ∈ intAd ℚ) ∧ ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i = t :=
  Iff.rfl

/- English proof (translation)
Use `⟨fun i => ((b.repr x i : ℤ) : A) * y, fun i => mul_mem (intCast_mem _ _) hy, ?_⟩` and prove the remaining obligations. Establish `hx : ((x : 𝓞 L) : L) = ∑ i, ((b.repr x i : ℚ)) • ((b i : 𝓞 L) : L)` using `by conv_lhs => rw [← b.sum_repr x]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, Algebra.smul_def, map_intCast]`.

Rewrite using `[hx, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e2 : (((b.repr x i : ℤ) : A) * y) = ((b.repr x i : ℚ)) • y`. Rewrite using `[Algebra.smul_def, map_intCast]`. Use `show _ ⊗ₜ[ℚ] (((b.repr x i : ℤ) : A) * y) = _`.

Rewrite using `[e2, TensorProduct.smul_tmul]`.
-/
theorem tmul_mem (x : 𝓞 L) {y : A} (hy : y ∈ intAd ℚ) :
    ((x : L) ⊗ₜ[ℚ] y : AfE ℚ L) ∈ coordSub b := by
  refine ⟨fun i => ((b.repr x i : ℤ) : A) * y, fun i => mul_mem (intCast_mem _ _) hy, ?_⟩
  have hx : ((x : 𝓞 L) : L) = ∑ i, ((b.repr x i : ℚ)) • ((b i : 𝓞 L) : L) := by
    conv_lhs => rw [← b.sum_repr x]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, Algebra.smul_def, map_intCast]
  rw [hx, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : (((b.repr x i : ℤ) : A) * y) = ((b.repr x i : ℚ)) • y := by
    rw [Algebra.smul_def, map_intCast]
  show _ ⊗ₜ[ℚ] (((b.repr x i : ℤ) : A) * y) = _
  rw [e2, TensorProduct.smul_tmul]

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `hs`. Take `⟨z', hz', rfl⟩` from `ht`. Rewrite using `[Finset.sum_mul_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`.

Use `tmul_mem b (b i * b j) (mul_mem (hz i) (hz' j))` as an intermediate fact. Simplify using `using this`.
-/
theorem mul_mem' {s t : AfE ℚ L} (hs : s ∈ coordSub b) (ht : t ∈ coordSub b) : s * t ∈ coordSub b := by
  obtain ⟨z, hz, rfl⟩ := hs
  obtain ⟨z', hz', rfl⟩ := ht
  rw [Finset.sum_mul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  have := tmul_mem b (b i * b j) (mul_mem (hz i) (hz' j))
  simpa using this

def coordRing : Subring (AfE ℚ L) :=
  { coordSub b with
    one_mem' := by
      have := tmul_mem b (1 : 𝓞 L) (one_mem (intAd ℚ))
      simpa [Algebra.TensorProduct.one_def] using this
    mul_mem' := fun hs ht => mul_mem' b hs ht }

/- English proof (translation)
Use `show Subring.closure _ ≤ _`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Conclude with `tmul_mem b a (one_mem _)`. Use `tmul_mem b (1 : 𝓞 L) hy` as an intermediate fact.

Conclude with `(by simpa using this : _ ∈ coordSub b)`.
-/
theorem rInt_le : RInt ℚ L ≤ coordRing b := by
  show Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact tmul_mem b a (one_mem _)
  · have := tmul_mem b (1 : 𝓞 L) hy
    exact (by simpa using this : _ ∈ coordSub b)

end GlobalTheory.CongOpen

namespace GlobalTheory.CongOpen

/- English proof (translation)
Introduce `L _ _`. Use `letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra`. Use `letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)`. Introduce `V hV h1`. Use `haveI hMT : IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := ⟨rfl⟩`.

Use `haveI : ContinuousAdd (AfE ℚ L) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)`. Use `haveI : ContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := IsModuleTopology.toContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)`. Take `⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ (𝓞 L))` from `⟨_, ⟨(RingOfIntegers.basis L).reindex (Fintype.equivFin _)⟩⟩`. Set `φ : (Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ) → AfE ℚ L` to `fun z => ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i`. Establish `hφs : ∀ z, φ z = ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))`.

Introduce `z`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[rsmul_tmul, mul_one]`. Establish `hφc : Continuous φ`. Establish `: φ = fun z => ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))` using `funext hφs`.

Rewrite using `[this]`. Conclude with `continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const`. Establish `hφn : ∀ (n : ℕ) z, φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z) = (n : AfE ℚ L) * φ z`. Introduce `n z`. Rewrite using `[hφs, hφs, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_smul, Algebra.smul_def (n : FiniteAdeleRing (𝓞 ℚ) ℚ), map_natCast]`. Establish `hV1 : V ∈ 𝓝 (1 : (AfE ℚ L)ˣ)` using `hV.mem_nhds h1`. Rewrite `hV1` using `[Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, map_one]`. Take `⟨O, hO, hOV⟩` from `Filter.mem_comap.1 hV1`.

Take `⟨W₁, hW₁, W₂, hW₂, hW⟩` from `mem_nhds_prod_iff.1 hO`. Establish `hW₂' : MulOpposite.op ⁻¹' W₂ ∈ 𝓝 (1 : AfE ℚ L)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW₂`. Establish `hU : (fun z => 1 + φ z) ⁻¹' (W₁ ∩ MulOpposite.op ⁻¹' W₂) ∈ 𝓝 (0 : Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ)`. Use `(continuous_const.add hφc).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Establish `h0 : 1 + φ 0 = 1` using `by simp [φ]`.

Use `show _ ∈ 𝓝 (1 + φ 0)`. Rewrite using `[h0]`. Conclude with `inter_mem hW₁ hW₂'`. Take `⟨n, hn, hnU⟩` from `GlobalTheory.SWQ.FinAnnih.exists_nat_smul_mem _ hU`. Use `⟨n, hn, fun u hu => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ w : RInt ℚ L, (w : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)} → ((w : AfE ℚ L)) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂`. Introduce `w hw`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hw`. Take `⟨z, hz, hza⟩` from `(mem_coordSub b).1 (rInt_le b a.2)`. Establish `hwe : (w : AfE ℚ L) = 1 + φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z)`.

Rewrite using `[hφn]`. Use `congrArg (fun t : RInt ℚ L => (t : AfE ℚ L)) ha` as an intermediate fact. Move the coercions through the operations in `at this`. Use `show _ = 1 + (n : AfE ℚ L) * (∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i)`. Rewrite using `[hza, mul_comm, this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hwe]`. Conclude with `hnU z hz`. Take `⟨u', hu', rfl⟩` from `Subgroup.mem_map.1 hu`. Rewrite `hu'` using `[mem_kerRed]`.

Establish `hinv : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)}`. Establish `e : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 = -((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) * ((u' : RInt ℚ L) - 1)`. Rewrite using `[mul_sub, neg_mul, Units.inv_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_left _ _ hu'`. Apply `hOV` to reduce the goal to its premises. Rewrite using `[Set.mem_preimage, Units.embedProduct_apply]`. Use `hW ⟨(key _ hu').1, ?_⟩` and prove the remaining obligations. Use `(key _ hinv).2` as an intermediate fact.

Simplify `this` using `[Units.coe_map, map_inv]`.
-/
theorem exists_congN_subset : ∀ (L : Type) [Field L] [NumberField L],
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ V : Set (AfE ℚ L)ˣ, IsOpen V → (1 : (AfE ℚ L)ˣ) ∈ V → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ congN ℚ L N, u ∈ V := by
  intro L _ _
  letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  intro V hV h1
  haveI hMT : IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := ⟨rfl⟩
  haveI : ContinuousAdd (AfE ℚ L) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  haveI : ContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) :=
    IsModuleTopology.toContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ (𝓞 L)) :=
    ⟨_, ⟨(RingOfIntegers.basis L).reindex (Fintype.equivFin _)⟩⟩
  let φ : (Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ) → AfE ℚ L := fun z => ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i
  have hφs : ∀ z, φ z = ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rsmul_tmul, mul_one]
  have hφc : Continuous φ := by
    have : φ = fun z => ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := funext hφs
    rw [this]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hφn : ∀ (n : ℕ) z, φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z) = (n : AfE ℚ L) * φ z := by
    intro n z
    rw [hφs, hφs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, Algebra.smul_def (n : FiniteAdeleRing (𝓞 ℚ) ℚ), map_natCast]

  have hV1 : V ∈ 𝓝 (1 : (AfE ℚ L)ˣ) := hV.mem_nhds h1
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, map_one] at hV1
  obtain ⟨O, hO, hOV⟩ := Filter.mem_comap.1 hV1
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hO
  have hW₂' : MulOpposite.op ⁻¹' W₂ ∈ 𝓝 (1 : AfE ℚ L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW₂
  have hU : (fun z => 1 + φ z) ⁻¹' (W₁ ∩ MulOpposite.op ⁻¹' W₂) ∈ 𝓝 (0 : Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine (continuous_const.add hφc).continuousAt.preimage_mem_nhds ?_
    have h0 : 1 + φ 0 = 1 := by simp [φ]
    show _ ∈ 𝓝 (1 + φ 0)
    rw [h0]
    exact inter_mem hW₁ hW₂'
  obtain ⟨n, hn, hnU⟩ := GlobalTheory.SWQ.FinAnnih.exists_nat_smul_mem _ hU
  refine ⟨n, hn, fun u hu => ?_⟩

  have key : ∀ w : RInt ℚ L, (w : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)} →
      ((w : AfE ℚ L)) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    intro w hw
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hw
    obtain ⟨z, hz, hza⟩ := (mem_coordSub b).1 (rInt_le b a.2)
    have hwe : (w : AfE ℚ L) = 1 + φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z) := by
      rw [hφn]
      have := congrArg (fun t : RInt ℚ L => (t : AfE ℚ L)) ha
      push_cast at this
      show _ = 1 + (n : AfE ℚ L) * (∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i)
      rw [hza, mul_comm, this]
      ring
    rw [hwe]
    exact hnU z hz
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  rw [mem_kerRed] at hu'
  have hinv : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)} := by
    have e : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 =
        -((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) * ((u' : RInt ℚ L) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hu'
  apply hOV
  rw [Set.mem_preimage, Units.embedProduct_apply]
  refine hW ⟨(key _ hu').1, ?_⟩
  have := (key _ hinv).2
  simpa [Units.coe_map, map_inv] using this

end GlobalTheory.CongOpen
