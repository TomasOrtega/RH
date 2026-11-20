import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FrameDet

open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory

/- English proof (translation)
Set `g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B)` to `{ toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩ map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hg : Function.Surjective g` using `fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩`. Establish `hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g = AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i)`. Use extensionality with `v`. Simplify using `[g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`.

Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]`. Repeatedly rewrite using `[AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]`. Use `Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)` and prove the remaining obligations. Rewrite using `[QuotientAddGroup.leftRel_pi]`.
-/
theorem relIndex_pi_pi {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

section Pseudo

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : I ≠ 0`. Introduce and unpack `rfl`. Conclude with `one_ne_zero (le_antisymm hI (FractionalIdeal.zero_le _))`. Set `u` to `Units.mk0 I h0`. Set `e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Free.ChooseBasisIndex ℤ u` to `Fintype.equivOfCardEq (by`.

Rewrite using `[← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank])`. Establish `h1` using `det_basisOfFractionalIdeal_eq_absNorm K u e`. Establish `hle : (1 : Submodule (𝓞 K) K) ≤ I`. Rewrite using `[← FractionalIdeal.coe_one (S := nonZeroDivisors (𝓞 K))]`. Conclude with `hI`.

Establish `h2` using `AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hle) (integralBasis K) ((basisOfFractionalIdeal K u).reindex e.symm) (by`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure]`. Use extensionality with `x`. Rewrite using `[Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_span_integralBasis, Submodule.mem_one]`. Use the proof step `rfl) (by`.

Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, Basis.range_reindex]`. Use extensionality with `x`. Rewrite using `[Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_span_basisOfFractionalIdeal]`. Use the proof step `rfl)`. Establish `h3 : FractionalIdeal.absNorm I = _` using `h1.symm`.

Rewrite using `[idxN, h2, h3, ← abs_mul, mul_comm, Basis.det_mul_det, Basis.det_self, abs_one]`.
-/
theorem idxN_one_mul_absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : 1 ≤ I) :
    (idxN (I : Submodule (𝓞 K) K) (1 : Submodule (𝓞 K) K) : ℚ) * FractionalIdeal.absNorm I = 1 := by
  have h0 : I ≠ 0 := by
    rintro rfl
    exact one_ne_zero (le_antisymm hI (FractionalIdeal.zero_le _))
  let u := Units.mk0 I h0
  let e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Free.ChooseBasisIndex ℤ u :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank])
  have h1 := det_basisOfFractionalIdeal_eq_absNorm K u e
  have hle : (1 : Submodule (𝓞 K) K) ≤ I := by
    rw [← FractionalIdeal.coe_one (S := nonZeroDivisors (𝓞 K))]
    exact hI
  have h2 := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hle) (integralBasis K)
    ((basisOfFractionalIdeal K u).reindex e.symm) (by
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      ext x
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_span_integralBasis, Submodule.mem_one]
      rfl) (by
      rw [← Submodule.span_int_eq_addSubgroupClosure, Basis.range_reindex]
      ext x
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_span_basisOfFractionalIdeal]
      rfl)
  have h3 : FractionalIdeal.absNorm I = _ := h1.symm
  rw [idxN, h2, h3, ← abs_mul, mul_comm, Basis.det_mul_det, Basis.det_self, abs_one]

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Use `⟨Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun K ι).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩ j -`. Rewrite using `[Pi.basisFun_apply, Pi.single_apply]`.

Use `split_ifs`. Conclude with `hI j (FractionalIdeal.one_mem_one _)`. Conclude with `zero_mem _`.
-/
theorem isLattice_pi (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : ∀ i, 1 ≤ I i) :
    Submodule.IsLattice K (Submodule.pi Set.univ fun i => (I i : Submodule (𝓞 K) K)) := by
  refine ⟨Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩ j -
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact hI j (FractionalIdeal.one_mem_one _)
  · exact zero_mem _

variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

noncomputable def pseudo (v : ι → V) (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) V :=
  (Submodule.pi Set.univ fun i => (I i : Submodule (𝓞 K) K)).map
    ((Fintype.linearCombination K v).restrictScalars (𝓞 K))

omit [StarRing K] in
/- English proof (translation)
Use `⟨Pi.single i x, fun j _ => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`. Simplify using `[hj]`.
-/
theorem smul_mem_pseudo (v : ι → V) (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (i : ι) {x : K}
    (hx : x ∈ I i) : x • v i ∈ pseudo v I := by
  refine ⟨Pi.single i x, fun j _ => ?_, by simp⟩
  by_cases hj : j = i
  · subst hj
    simpa using hx
  · simp [hj]

omit [StarRing K] in
/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[LinearMap.restrictScalars_apply, Fintype.linearCombination_apply]`. Conclude with `N.sum_mem fun i _ => hN i _ (hx i (Set.mem_univ i))`.
-/
theorem pseudo_le (v : ι → V) (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {N : Submodule (𝓞 K) V}
    (hN : ∀ i, ∀ x ∈ I i, x • v i ∈ N) : pseudo v I ≤ N := by
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.restrictScalars_apply, Fintype.linearCombination_apply]
  exact N.sum_mem fun i _ => hN i _ (hx i (Set.mem_univ i))

/- English proof (translation)
Use `set G : Matrix ι ι K := Matrix.of fun i j => h (v i) (v j) with hGd`. Use `set φ := Fintype.linearCombination K v with hφ`. Set `h' : (ι → K) →ₗ⋆[K] (ι → K) →ₗ[K] K` to `(h.comp φ).compl₂ φ`. Establish `hh : ∀ x y, h' x y = h (φ x) (φ y)` using `fun _ _ => rfl`. Establish `hx : ∀ y x, h' y x = ∑ i, star (y i) * (G *ᵥ x) i` using `fun y x => by`.

Simplify using `only [hh, hφ, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, mulVec, dotProduct, hGd, Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hx1 : ∀ i x, h' (Pi.single i 1) x = (G *ᵥ x) i` using `fun i x => by`. Apply the tactic sequence `rw [hx, Finset.sum_eq_single i] <;> simp +contextual [Pi.single_apply]`.

Establish `hs' : h'.IsSymm` using `⟨fun x y => hs.eq _ _⟩`. Establish `hr : ∀ x, (∀ y, h' y x = 0) → x = 0` using `fun x H => Matrix.eq_zero_of_mulVec_eq_zero hG (funext fun i => by rw [← hx1, H]; rfl)`. Establish `hn' : h'.Nondegenerate` using `⟨fun x H => hr x fun y => RowPerp.swap_zero hs' (H y), hr⟩`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Conclude with `fun x H => hr x fun y => by rw [hh, H, map_zero]`. Use `set P := Submodule.pi Set.univ fun i => (I i : Submodule (𝓞 K) K) with hP`. Use `set P₀ := Submodule.pi Set.univ fun _ : ι => ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) with hP₀`. Establish `hPl : Submodule.IsLattice K P` using `isLattice_pi I hI`. Establish `hP₀l : Submodule.IsLattice K P₀` using `isLattice_pi _ fun _ => le_rfl`.

Establish `hle : P₀ ≤ P` using `fun x H i hi => hI i (H i hi)`. Establish `hPi : IsIntLat h' P` using `⟨hPl, fun x a y b => hint _ ⟨x, a, rfl⟩ _ ⟨y, b, rfl⟩⟩`. Establish `hP₀i : IsIntLat h' P₀` using `⟨hP₀l, fun x a y b => hPi.2 x (hle a) y (hle b)⟩`. Establish `e1` using `((DiscOrder.main K _ h' hK hs' hn' P₀ hP₀i).2.2.1 P hPi hle).2`. Establish `n0` using `(DiscOrder.main K _ h' hK hs' hn' P hPi).1`.

Establish `e2 : idxN P P₀ = ∏ i, idxN (I i : Submodule (𝓞 K) K) 1`. Rewrite using `[← FractionalIdeal.coe_one (S := nonZeroDivisors (𝓞 K))]`. Conclude with `relIndex_pi_pi (fun _ => ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) fun i => (I i : Submodule (𝓞 K) K).toAddSubgroup`. Establish `e3 : (discN h' P₀ : ℚ) = |Algebra.norm ℚ G.det|`. Establish `hd : LinearMap.det (Matrix.toLin' G) ≠ 0` using `by rwa [LinearMap.det_toLin']`.

Establish `hm : ∀ x, x ∈ dual h' P₀ ↔ G *ᵥ x ∈ P₀` using `fun x => by`. Rewrite using `[dualBasic_mem_dual]`. Use `⟨fun H i _ => ?_, fun H y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[FractionalIdeal.coe_one, ← hx1]`. Use `H _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `FractionalIdeal.one_mem_one _`. Conclude with `zero_mem _`. Rewrite using `[hx]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `(FractionalIdeal.mem_one_iff _).1 (hy i (Set.mem_univ i))`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 (H i (Set.mem_univ i))`. Take `⟨t, ht⟩` from `star_algebraMap_ringOfIntegers_mem_range a`. Conclude with `Submodule.mem_one.2 ⟨t * b, by rw [map_mul, ht, ha, hb]⟩`.

Establish `hg : gmap ((Matrix.toLin' G).equivOfDetNeZero hd) (dual h' P₀) = P₀`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(hm y).1 hy`.

Introduce `H`. Take `⟨y, rfl⟩` from `((Matrix.toLin' G).equivOfDetNeZero hd).surjective x`. Conclude with `⟨y, (hm y).2 H, rfl⟩`. Establish `hl` using `(dualLattice (𝓞 K) K _ h' hs' hn' star_algebraMap_ringOfIntegers_mem_range P₀ hP₀l).1`. Use `GlobalTheory.DegCnt.FixDisc.idx_gmap hl hl _ le_rfl (hg.le.trans fun x a => (dualBasic_mem_dual _ _ _).2 fun y b => hP₀i.2 y b x a)` as an intermediate fact.

Rewrite `this` using `[hg, idxN_eq_one.2 le_rfl]`. Rewrite using `[discN, this, ← LinearMap.det_toLin' G]`. Simplify using the standard rewrite rules. Establish `e4 : idxN (dualInH h (pseudo v I)) (pseudo v I) = discN h' P`. Establish `a : (pseudo v I).toAddSubgroup = P.toAddSubgroup.map φ.toAddMonoidHom` using `rfl`.

Establish `c : Submodule.span K (pseudo v I : Set V) = LinearMap.range φ`. Express the relevant statement in the definitionally equal form `Submodule.span K (φ '' P) = _`. Rewrite using `[← Submodule.map_span, hPl.span_eq_top, Submodule.map_top]`. Establish `b : (dualInH h (pseudo v I)).toAddSubgroup = (dual h' P).toAddSubgroup.map φ.toAddMonoidHom`. Rewrite using `[dualInH, c]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, y, rfl⟩`. Conclude with `⟨y, (dualBasic_mem_dual _ _ _).2 fun z hz => (dualBasic_mem_dual _ _ _).1 h1 _ ⟨z, hz, rfl⟩, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Use `⟨(dualBasic_mem_dual _ _ _).2 ?_, y, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `(dualBasic_mem_dual _ _ _).1 hy z hz`. Rewrite using `[idxN, a, b, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`. Both sides reduce to the same expression.

Establish `hd : pseudo v I ≤ dualInH h (pseudo v I)` using `fun x a => ⟨(dualBasic_mem_dual _ _ _).2 fun y b => hint y b x a, Submodule.subset_span a⟩`. Rewrite using `[latDetH, DetAgree.genIdxH_eq_idxN hd (e4 ▸ n0), Real.sq_sqrt (Nat.cast_nonneg _), e4, ← e3, e1, e2]`. Establish `e5 : ((∏ i, idxN (I i : Submodule (𝓞 K) K) 1 : ℕ) : ℚ) * ∏ i, FractionalIdeal.absNorm (I i) = 1`. Rewrite using `[Nat.cast_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun i _ => idxN_one_mul_absNorm _ (hI i)`.

Rewrite using `[Nat.cast_mul, Nat.cast_pow, mul_assoc, ← mul_pow, e5]`. Simplify using the standard rewrite rules.
-/
theorem latDetH_pseudo [DecidableEq ι] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (v : ι → V)
    (hG : (Matrix.of fun i j => h (v i) (v j)).det ≠ 0)
    (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : ∀ i, 1 ≤ I i)
    (hint : IsIntegralLat h (pseudo v I)) :
    latDetH h (pseudo v I) ^ 2 = ((|Algebra.norm ℚ (Matrix.of fun i j => h (v i) (v j)).det| *
      (∏ i, FractionalIdeal.absNorm (I i)) ^ 2 : ℚ) : ℝ) := by
  set G : Matrix ι ι K := Matrix.of fun i j => h (v i) (v j) with hGd
  set φ := Fintype.linearCombination K v with hφ
  let h' : (ι → K) →ₗ⋆[K] (ι → K) →ₗ[K] K := (h.comp φ).compl₂ φ
  have hh : ∀ x y, h' x y = h (φ x) (φ y) := fun _ _ => rfl
  have hx : ∀ y x, h' y x = ∑ i, star (y i) * (G *ᵥ x) i := fun y x => by
    simp only [hh, hφ, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, mulVec, dotProduct, hGd,
      Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hx1 : ∀ i x, h' (Pi.single i 1) x = (G *ᵥ x) i := fun i x => by
    rw [hx, Finset.sum_eq_single i] <;> simp +contextual [Pi.single_apply]
  have hs' : h'.IsSymm := ⟨fun x y => hs.eq _ _⟩
  have hr : ∀ x, (∀ y, h' y x = 0) → x = 0 := fun x H =>
    Matrix.eq_zero_of_mulVec_eq_zero hG (funext fun i => by rw [← hx1, H]; rfl)
  have hn' : h'.Nondegenerate := ⟨fun x H => hr x fun y => RowPerp.swap_zero hs' (H y), hr⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun x H => hr x fun y => by rw [hh, H, map_zero]
  set P := Submodule.pi Set.univ fun i => (I i : Submodule (𝓞 K) K) with hP
  set P₀ := Submodule.pi Set.univ fun _ : ι =>
    ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) with hP₀
  have hPl : Submodule.IsLattice K P := isLattice_pi I hI
  have hP₀l : Submodule.IsLattice K P₀ := isLattice_pi _ fun _ => le_rfl
  have hle : P₀ ≤ P := fun x H i hi => hI i (H i hi)
  have hPi : IsIntLat h' P := ⟨hPl, fun x a y b => hint _ ⟨x, a, rfl⟩ _ ⟨y, b, rfl⟩⟩
  have hP₀i : IsIntLat h' P₀ := ⟨hP₀l, fun x a y b => hPi.2 x (hle a) y (hle b)⟩
  have e1 := ((DiscOrder.main K _ h' hK hs' hn' P₀ hP₀i).2.2.1 P hPi hle).2
  have n0 := (DiscOrder.main K _ h' hK hs' hn' P hPi).1
  have e2 : idxN P P₀ = ∏ i, idxN (I i : Submodule (𝓞 K) K) 1 := by
    rw [← FractionalIdeal.coe_one (S := nonZeroDivisors (𝓞 K))]
    exact relIndex_pi_pi
      (fun _ => ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup)
      fun i => (I i : Submodule (𝓞 K) K).toAddSubgroup
  have e3 : (discN h' P₀ : ℚ) = |Algebra.norm ℚ G.det| := by
    have hd : LinearMap.det (Matrix.toLin' G) ≠ 0 := by rwa [LinearMap.det_toLin']
    have hm : ∀ x, x ∈ dual h' P₀ ↔ G *ᵥ x ∈ P₀ := fun x => by
      rw [dualBasic_mem_dual]
      refine ⟨fun H i _ => ?_, fun H y hy => ?_⟩
      · rw [FractionalIdeal.coe_one, ← hx1]
        refine H _ fun j _ => ?_
        rw [Pi.single_apply]
        split_ifs
        · exact FractionalIdeal.one_mem_one _
        · exact zero_mem _
      · rw [hx]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 (hy i (Set.mem_univ i))
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 (H i (Set.mem_univ i))
        obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range a
        exact Submodule.mem_one.2 ⟨t * b, by rw [map_mul, ht, ha, hb]⟩
    have hg : gmap ((Matrix.toLin' G).equivOfDetNeZero hd) (dual h' P₀) = P₀ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hm y).1 hy
      · intro H
        obtain ⟨y, rfl⟩ := ((Matrix.toLin' G).equivOfDetNeZero hd).surjective x
        exact ⟨y, (hm y).2 H, rfl⟩
    have hl := (dualLattice (𝓞 K) K _ h' hs' hn' star_algebraMap_ringOfIntegers_mem_range P₀ hP₀l).1
    have := GlobalTheory.DegCnt.FixDisc.idx_gmap hl hl _ le_rfl (hg.le.trans fun x a =>
      (dualBasic_mem_dual _ _ _).2 fun y b => hP₀i.2 y b x a)
    rw [hg, idxN_eq_one.2 le_rfl] at this
    rw [discN, this, ← LinearMap.det_toLin' G]
    simp
  have e4 : idxN (dualInH h (pseudo v I)) (pseudo v I) = discN h' P := by
    have a : (pseudo v I).toAddSubgroup = P.toAddSubgroup.map φ.toAddMonoidHom := rfl
    have c : Submodule.span K (pseudo v I : Set V) = LinearMap.range φ := by
      change Submodule.span K (φ '' P) = _
      rw [← Submodule.map_span, hPl.span_eq_top, Submodule.map_top]
    have b : (dualInH h (pseudo v I)).toAddSubgroup = (dual h' P).toAddSubgroup.map φ.toAddMonoidHom := by
      rw [dualInH, c]
      ext x
      constructor
      · rintro ⟨h1, y, rfl⟩
        exact ⟨y, (dualBasic_mem_dual _ _ _).2 fun z hz => (dualBasic_mem_dual _ _ _).1 h1 _ ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨(dualBasic_mem_dual _ _ _).2 ?_, y, rfl⟩
        rintro _ ⟨z, hz, rfl⟩
        exact (dualBasic_mem_dual _ _ _).1 hy z hz
    rw [idxN, a, b, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    rfl
  have hd : pseudo v I ≤ dualInH h (pseudo v I) := fun x a =>
    ⟨(dualBasic_mem_dual _ _ _).2 fun y b => hint y b x a, Submodule.subset_span a⟩
  rw [latDetH, DetAgree.genIdxH_eq_idxN hd (e4 ▸ n0), Real.sq_sqrt (Nat.cast_nonneg _), e4, ← e3, e1, e2]
  have e5 : ((∏ i, idxN (I i : Submodule (𝓞 K) K) 1 : ℕ) : ℚ) * ∏ i, FractionalIdeal.absNorm (I i) = 1 := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => idxN_one_mul_absNorm _ (hI i)
  rw [Nat.cast_mul, Nat.cast_pow, mul_assoc, ← mul_pow, e5]
  simp

end Pseudo

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Apply the tactic sequence `induction a using Fin.lastCases <;> induction b using Fin.lastCases`. Simplify using `[FlagG.fvec, F.z_norm]`. Name the introduced variables `b`. Simplify using `[FlagG.fvec, Formalism.MainNotions.hT_swap_zero (F.z_orth b), diagonal_apply, (Fin.castSucc_ne_last b).symm]`. Name the introduced variables `a`.

Simplify using `[FlagG.fvec, F.z_orth a, diagonal_apply, Fin.castSucc_ne_last]`. Name the introduced variables `a b`. Simplify using `[FlagG.fvec, F.e_iso a b, diagonal_apply, Fin.castSucc_ne_last]`.
-/
theorem hT_fvec (F : FlagG S r T) (a b : Fin (r + 1)) :
    S.hT (F.fvec a) (F.fvec b) = diagonal (fun a => if a = Fin.last r then -T else 0) a b := by
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp [FlagG.fvec, F.z_norm]
  · rename_i b
    simp [FlagG.fvec, Formalism.MainNotions.hT_swap_zero (F.z_orth b), diagonal_apply, (Fin.castSucc_ne_last b).symm]
  · rename_i a
    simp [FlagG.fvec, F.z_orth a, diagonal_apply, Fin.castSucc_ne_last]
  · rename_i a b
    simp [FlagG.fvec, F.e_iso a b, diagonal_apply, Fin.castSucc_ne_last]

/- English proof (translation)
Rewrite using `[Dl, leadMinorE, dif_pos le_rfl]`. Use `congr 1`.
-/
theorem Dl_succ (F : FlagG S r T) (F' : FlagG S r T') : Dl F F' (r + 1) = (Zhat F F').det := by
  rw [Dl, leadMinorE, dif_pos le_rfl]
  congr 1

/- English proof (translation)
Rewrite using `[Dl, leadMinorE, dif_pos (Nat.le_succ r)]`. Use `congr 1`.
-/
theorem Dl_self (F : FlagG S r T) (F' : FlagG S r T') :
    Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Dl, leadMinorE, dif_pos (Nat.le_succ r)]
  congr 1

/- English proof (translation)
Establish `e : (Matrix.of fun i j => S.hT (Sum.elim F.fvec F'.fvec i) (Sum.elim F.fvec F'.fvec j)) = fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) (Zhat F F') (Zhat F F')ᴴ (diagonal fun a => if a = Fin.last r then -T' else 0)`. Use extensionality with `(a | a) (b | b)`. Conclude with `hT_fvec F a b`. Both sides reduce to the same expression. Conclude with `(S.herm.eq _ _).symm`.

Conclude with `hT_fvec F' a b`. Rewrite using `[e, GlobalTheory.SA.TransvG.det_fromBlocks_last, ← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose, Gflag, Dl_succ, Dl_self]`.
-/
theorem det_gram (F : FlagG S r T) (F' : FlagG S r T') :
    (Matrix.of fun i j => S.hT (Sum.elim F.fvec F'.fvec i) (Sum.elim F.fvec F'.fvec j)).det =
      (-1) ^ (r + 1) * Gflag F F' := by
  have e : (Matrix.of fun i j => S.hT (Sum.elim F.fvec F'.fvec i) (Sum.elim F.fvec F'.fvec j)) =
      fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) (Zhat F F') (Zhat F F')ᴴ
        (diagonal fun a => if a = Fin.last r then -T' else 0) := by
    ext (a | a) (b | b)
    · exact hT_fvec F a b
    · rfl
    · exact (S.herm.eq _ _).symm
    · exact hT_fvec F' a b
  rw [e, GlobalTheory.SA.TransvG.det_fromBlocks_last, ← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose,
    Gflag, Dl_succ, Dl_self]

/- English proof (translation)
Use `set Z := Zhat F F' with hZ`. Set `c : Fin (r + 1) → E` to `fun b => Z.adjugate b (Fin.last r)`. Use `set y := ∑ b, c b • F'.fvec b with hy`. Establish `h1 : ∀ a, S.hT (F.fvec a) y = if a = Fin.last r then Z.det else 0` using `fun a => by`. Use `congrFun (congrFun (Matrix.mul_adjugate Z) a) (Fin.last r)` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]`. Rewrite using `[hy, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, mul_ite, mul_one, mul_zero] at this ⊢`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`.

Establish `hc : c (Fin.last r) = Dl F F' r`. Rewrite using `[Dl_self]`. Simplify using `only [c, adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]`. Simplify using `[hZ]`. Establish `h2 : S.hT y y = -T' * (Dl F F' r * star (Dl F F' r))`.

Simplify using `only [hy, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hT_fvec, diagonal_apply, starRingEnd_apply, RingHom.id_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : S.hT F.z y = Z.det` using `by simpa [FlagG.fvec] using h1 (Fin.last r)`. Establish `h4 : S.hT y F.z = star Z.det` using `by rw [← h3]; exact (S.herm.eq _ _).symm`. Use `⟨y + (Z.det / T) • F.z, (Formalism.MainNotions.mem_orth_iff _ _).2 (Formalism.MainNotions.hT_zero_of_mem_Xplus F (fun a => ?_) ?_), ?_⟩` and prove the remaining obligations.

Use `h1 a.castSucc` as an intermediate fact. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc, Fin.castSucc_ne_last, if_false] at this`. Rewrite using `[map_add, map_smul, this, F.z_orth, smul_zero, add_zero]`. Rewrite using `[map_add, map_smul, h3, F.z_norm, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, h2, h3, h4, F.z_norm, starRingEnd_apply, RingHom.id_apply, star_div₀, hs, Gflag, Dl_succ, ← hZ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_norm_eq (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hs : star T = T) :
    ∃ w ∈ orth S F.Xplus, T * S.hT w w = Gflag F F' := by
  set Z := Zhat F F' with hZ
  let c : Fin (r + 1) → E := fun b => Z.adjugate b (Fin.last r)
  set y := ∑ b, c b • F'.fvec b with hy
  have h1 : ∀ a, S.hT (F.fvec a) y = if a = Fin.last r then Z.det else 0 := fun a => by
    have := congrFun (congrFun (Matrix.mul_adjugate Z) a) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at this
    rw [hy, map_sum]
    simp only [map_smul, smul_eq_mul, mul_ite, mul_one, mul_zero] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hc : c (Fin.last r) = Dl F F' r := by
    rw [Dl_self]
    simp only [c, adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]
    simp [hZ]
  have h2 : S.hT y y = -T' * (Dl F F' r * star (Dl F F' r)) := by
    simp only [hy, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hT_fvec,
      diagonal_apply, starRingEnd_apply, RingHom.id_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hc]
    ring
  have h3 : S.hT F.z y = Z.det := by simpa [FlagG.fvec] using h1 (Fin.last r)
  have h4 : S.hT y F.z = star Z.det := by rw [← h3]; exact (S.herm.eq _ _).symm
  refine ⟨y + (Z.det / T) • F.z, (Formalism.MainNotions.mem_orth_iff _ _).2 (Formalism.MainNotions.hT_zero_of_mem_Xplus F (fun a => ?_) ?_), ?_⟩
  · have := h1 a.castSucc
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.castSucc_ne_last, if_false] at this
    rw [map_add, map_smul, this, F.z_orth, smul_zero, add_zero]
  · rw [map_add, map_smul, h3, F.z_norm, smul_eq_mul]
    field_simp
    ring
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, h2, h3, h4,
      F.z_norm, starRingEnd_apply, RingHom.id_apply, star_div₀, hs, Gflag, Dl_succ, ← hZ]
    field_simp
    ring

end Flags

/- English proof (translation)
Establish `h : frameExp r (r + 1) = frameExp r r`. Rewrite using `[frameExp, Finset.sum_Icc_succ_top (by omega), Nat.sub_self, add_zero, frameExp]`. Use `⟨?_, h⟩` and prove the remaining obligations. Rewrite using `[← h, frameExp, Fin.sum_univ_eq_sum_range (fun a => r - a), Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add' (fun a => r + 1 - a) 0 (r + 1) 1]`. Conclude with `Finset.sum_congr rfl fun a _ => by omega`.
-/
theorem sum_frameExp (r : ℕ) : ∑ a : Fin (r + 1), (r - a.val) = frameExp r r ∧ frameExp r (r + 1) = frameExp r r := by
  have h : frameExp r (r + 1) = frameExp r r := by
    rw [frameExp, Finset.sum_Icc_succ_top (by omega), Nat.sub_self, add_zero, frameExp]
  refine ⟨?_, h⟩
  rw [← h, frameExp, Fin.sum_univ_eq_sum_range (fun a => r - a), Finset.range_eq_Ico,
    ← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add' (fun a => r + 1 - a) 0 (r + 1) 1]
  exact Finset.sum_congr rfl fun a _ => by omega

variable (D : D7)

noncomputable def coefI (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

/- English proof (translation)
Rewrite using `[coefI, _root_.zpow_neg, ← _root_.zpow_natCast, Nat.cast_sub (Nat.le_of_lt_succ a.2)]`.
-/
theorem coefI_eq (a : Fin (D.R.rS + 1)) : coefI D a = (ddS D ^ (D.R.rS - a.val))⁻¹ := by
  rw [coefI, _root_.zpow_neg, ← _root_.zpow_natCast, Nat.cast_sub (Nat.le_of_lt_succ a.2)]

/- English proof (translation)
Establish `h0 : ddS D ≠ 0` using `fun e => by`. Use `RealPlaces.absNorm_ddS D` as an intermediate fact. Rewrite `this` using `[e, map_zero, Rat.cast_zero]`. Conclude with `(pow_pos (one_pos.trans_le (RealPlaces.one_le_rdE D)) _).ne this`. Establish `h1 : ddS D ≤ 1` using `FractionalIdeal.coeIdeal_le_one`.

Rewrite using `[coefI_eq]`. Conclude with `(one_le_inv₀ (pow_pos (pos_iff_ne_zero.2 h0) _)).2 (pow_le_one₀ (FractionalIdeal.zero_le _) h1)`.
-/
theorem one_le_coefI (a : Fin (D.R.rS + 1)) : 1 ≤ coefI D a := by
  have h0 : ddS D ≠ 0 := fun e => by
    have := RealPlaces.absNorm_ddS D
    rw [e, map_zero, Rat.cast_zero] at this
    exact (pow_pos (one_pos.trans_le (RealPlaces.one_le_rdE D)) _).ne this
  have h1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  rw [coefI_eq]
  exact (one_le_inv₀ (pow_pos (pos_iff_ne_zero.2 h0) _)).2 (pow_le_one₀ (FractionalIdeal.zero_le _) h1)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Simplify `h a.castSucc x hx` using `[FlagG.fvec]`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`.

Simplify `h (Fin.last _) 1 (one_le_coefI D _ (FractionalIdeal.one_mem_one _))` using `[FlagG.fvec]`.
-/
theorem XS_sup_le {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {N : LatV D}
    (h : ∀ a, ∀ x ∈ coefI D a, x • F.fvec a ∈ N) : XS D F ≤ N ∧ Submodule.span (𝓞 D.host.E) {F.z} ≤ N := by
  constructor
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    simpa [FlagG.fvec] using h a.castSucc x hx
  · rw [Submodule.span_singleton_le_iff_mem]
    simpa [FlagG.fvec] using h (Fin.last _) 1 (one_le_coefI D _ (FractionalIdeal.one_mem_one _))

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases`. Rewrite `hx` using `[coefI_eq, Fin.val_last, Nat.sub_self, pow_zero, inv_one]`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Rewrite using `[algebraMap_smul]`. Use `Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations.

Simplify using `[FlagG.fvec]`. Name the introduced variables `a`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, by simp [FlagG.fvec]⟩)`.
-/
theorem smul_fvec_mem {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) {x : D.host.E}
    (hx : x ∈ coefI D a) : x • F.fvec a ∈ XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z} := by
  induction a using Fin.lastCases
  · rw [coefI_eq, Fin.val_last, Nat.sub_self, pow_zero, inv_one] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    rw [algebraMap_smul]
    refine Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_)
    simp [FlagG.fvec]
  · rename_i a
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, by simp [FlagG.fvec]⟩)

/- English proof (translation)
Introduce `D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz Λ hΛ F' hF' _`. Establish `hT : Tu D u ≠ 0` using `hH.2.1.2.1.ne_zero`. Take `⟨-, ⟨-, hu, hl, -⟩, hX⟩` from `hΛ`. Take `⟨⟨hl', -, hG⟩, -, hX'⟩` from `hF'`. Use `set G := Gflag F0 F'.fl with hGd`.

Establish `hG : G ≠ 0` using `hG`. Establish `hU : UU Λ (lf D F0) F' = pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D))`. Rewrite using `[UU, hX, hX', hl'.2, sup_assoc]`. Use `le_antisymm ?_ (pseudo_le _ _ ?_)` and prove the remaining obligations. Establish `a` using `XS_sup_le D F0 fun a x hx => smul_mem_pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D)) (Sum.inl a) hx`.

Establish `b` using `XS_sup_le D F'.fl fun a x hx => smul_mem_pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D)) (Sum.inr a) hx`. Conclude with `sup_le (sup_le a.1 a.2) (sup_le b.1 b.2)`. Introduce and unpack `(a | a) x hx`. Conclude with `Submodule.mem_sup_left (smul_fvec_mem D F0 a hx)`. Conclude with `Submodule.mem_sup_right (smul_fvec_mem D F'.fl a hx)`.

Establish `hle : UU Λ (lf D F0) F' ≤ Λ`. Rewrite using `[UU, hl'.2]`. Conclude with `sup_le (sup_le (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hl.1)) inf_le_left) ((Submodule.span_singleton_le_iff_mem _ _).2 hl'.1)`. Establish `hint : IsIntegralLat (hS D).hT (UU Λ (lf D F0) F')` using `fun x hx y hy => (dualBasic_mem_dual _ _ _).1 (hu.ge (hle hy)) x (hle hx)`. Apply the tactic sequence `have key := latDetH_pseudo D.sp.cm.cmUnram (hS D).hT (hS D).herm (Sum.elim F0.fvec F'.fl.fvec) (by rw [det_gram]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hG) (Sum.elim (coefI D) (coefI D)) (by rintro (a | a) <;> exact one_le_coefI D a) (hU ▸ hint)`.

Rewrite `key` using `[← hU, det_gram, ← hGd]`. Take `⟨hcard, -, -, -, hrd, hstar, hnorm, -, hdd, -⟩` from `GlobalTheory.real_places_facts D`. Take `⟨s1, s2⟩` from `sum_frameExp D.R.rS`. Use `set s := frameExp D.R.rS D.R.rS with hs`. Establish `hrd0 : 0 < D.host.rdE` using `one_pos.trans_le hrd`.

Establish `hpos : ∀ τ : D.host.E →+* ℂ, 0 ≤ (τ G).re` using `fun τ => by`. Take `⟨w, hw, e⟩` from `exists_norm_eq F0 F'.fl (Nat.cast_ne_zero.2 hT) (star_natCast _)`. Establish `hW` using `(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1`. Take `⟨_, ⟨p, rfl⟩, x, hx, rfl⟩` from `Submodule.mem_sup.1 (hW.ge hw)`. Establish `a1` using `(Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)`.

Establish `a2` using `Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (hW.le (Submodule.mem_sup_left ⟨p, rfl⟩)) x (Submodule.mem_sup_left hx))`. Rewrite `e` using `[map_add (VS D).hT, LinearMap.add_apply, a1, add_zero, map_add, a2, add_zero, D.sp.iXY_isom 0 (lt_of_lt_of_le (by norm_num) D.R.two_le_m)]`. Rewrite using `[hGd, ← e, map_mul, map_natCast, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]`. Use `mul_nonneg (Nat.cast_nonneg _) ?_` and prove the remaining obligations. Distinguish the cases in `hp : p = 0`.

Simplify using `[hp]`. Conclude with `((RowPerp.main D u F0 he hz).1.1 τ p hp).le`. Establish `hGz : ∀ τ, Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ = ‖embS D τ G‖ * (D.host.rdE ^ (4 * s))⁻¹` using `fun τ => by`. Establish `e : embS D τ G = ((‖embS D τ (Dl F0 F'.fl (D.R.rS + 1))‖ ^ 2 - (Tu D u : ℝ) * (Tu D u' : ℝ) * ‖embS D τ (Dl F0 F'.fl D.R.rS)‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [hGd, Gflag, map_sub, map_mul, map_natCast, hstar, Complex.mul_conj']`.

Use `push_cast`. Both sides reduce to the same expression. Establish `h0` using `hpos (embS D τ)`. Rewrite `h0` using `[e, Complex.ofReal_re]`. Establish `e2 : D.host.rdE ^ (-(2 * (s : ℝ))) = (D.host.rdE ^ (2 * s))⁻¹`.

Rewrite using `[Real.rpow_neg hrd0.le, ← Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e, Complex.norm_real, Real.norm_of_nonneg h0, Gz, absDl, absDl, absReal, absReal, s2, ← hs, e2]`. Express the relevant statement in the definitionally equal form `(‖embS D τ (Dl F0 F'.fl (D.R.rS + 1))‖ * _) ^ 2 - _ * (‖embS D τ (Dl F0 F'.fl D.R.rS)‖ * _) ^ 2 = _`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hGz]`. Use `(pow_left_inj₀ (Real.sqrt_nonneg _) (Finset.prod_nonneg fun τ _ => by positivity) two_ne_zero).1 (key.trans ?_)` and prove the remaining obligations. Establish `e3 : ∏ a, FractionalIdeal.absNorm (coefI D a) = (FractionalIdeal.absNorm (ddS D) ^ s)⁻¹`. Simplify using `only [coefI_eq, map_inv₀, map_pow, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, s1]`.

Establish `e4 : |Algebra.norm ℚ ((-1) ^ (D.R.rS + 1) * G)| = |Algebra.norm ℚ G|`. Rewrite using `[map_mul, map_pow, abs_mul, abs_pow, ← map_one (algebraMap ℚ D.host.E), ← map_neg, Algebra.norm_algebraMap]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_mul_distrib, mul_pow, ← Finset.prod_pow (f := fun τ => ‖embS D τ G‖), hnorm, Finset.prod_const, Finset.card_univ, hcard, e4, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, e3]`.

Use `push_cast`. Rewrite using `[hdd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → NG Λ (lf D F0) F' = ∏ τ, Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz Λ hΛ F' hF' _
  have hT : Tu D u ≠ 0 := hH.2.1.2.1.ne_zero
  obtain ⟨-, ⟨-, hu, hl, -⟩, hX⟩ := hΛ
  obtain ⟨⟨hl', -, hG⟩, -, hX'⟩ := hF'
  set G := Gflag F0 F'.fl with hGd
  have hG : G ≠ 0 := hG
  have hU : UU Λ (lf D F0) F' = pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D)) := by
    rw [UU, hX, hX', hl'.2, sup_assoc]
    refine le_antisymm ?_ (pseudo_le _ _ ?_)
    · have a := XS_sup_le D F0 fun a x hx =>
        smul_mem_pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D)) (Sum.inl a) hx
      have b := XS_sup_le D F'.fl fun a x hx =>
        smul_mem_pseudo (Sum.elim F0.fvec F'.fl.fvec) (Sum.elim (coefI D) (coefI D)) (Sum.inr a) hx
      exact sup_le (sup_le a.1 a.2) (sup_le b.1 b.2)
    · rintro (a | a) x hx
      · exact Submodule.mem_sup_left (smul_fvec_mem D F0 a hx)
      · exact Submodule.mem_sup_right (smul_fvec_mem D F'.fl a hx)
  have hle : UU Λ (lf D F0) F' ≤ Λ := by
    rw [UU, hl'.2]
    exact sup_le (sup_le (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hl.1)) inf_le_left)
      ((Submodule.span_singleton_le_iff_mem _ _).2 hl'.1)
  have hint : IsIntegralLat (hS D).hT (UU Λ (lf D F0) F') := fun x hx y hy =>
    (dualBasic_mem_dual _ _ _).1 (hu.ge (hle hy)) x (hle hx)
  have key := latDetH_pseudo D.sp.cm.cmUnram (hS D).hT (hS D).herm (Sum.elim F0.fvec F'.fl.fvec)
    (by rw [det_gram]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hG)
    (Sum.elim (coefI D) (coefI D)) (by rintro (a | a) <;> exact one_le_coefI D a) (hU ▸ hint)
  rw [← hU, det_gram, ← hGd] at key
  obtain ⟨hcard, -, -, -, hrd, hstar, hnorm, -, hdd, -⟩ := GlobalTheory.real_places_facts D
  obtain ⟨s1, s2⟩ := sum_frameExp D.R.rS
  set s := frameExp D.R.rS D.R.rS with hs
  have hrd0 : 0 < D.host.rdE := one_pos.trans_le hrd
  have hpos : ∀ τ : D.host.E →+* ℂ, 0 ≤ (τ G).re := fun τ => by
    obtain ⟨w, hw, e⟩ := exists_norm_eq F0 F'.fl (Nat.cast_ne_zero.2 hT) (star_natCast _)
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    obtain ⟨_, ⟨p, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.ge hw)
    have a1 := (Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)
    have a2 := Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1
      (hW.le (Submodule.mem_sup_left ⟨p, rfl⟩)) x (Submodule.mem_sup_left hx))
    rw [map_add (VS D).hT, LinearMap.add_apply, a1, add_zero, map_add, a2, add_zero,
      D.sp.iXY_isom 0 (lt_of_lt_of_le (by norm_num) D.R.two_le_m)] at e
    rw [hGd, ← e, map_mul, map_natCast, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    by_cases hp : p = 0
    · simp [hp]
    · exact ((RowPerp.main D u F0 he hz).1.1 τ p hp).le
  have hGz : ∀ τ, Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ =
      ‖embS D τ G‖ * (D.host.rdE ^ (4 * s))⁻¹ := fun τ => by
    have e : embS D τ G = ((‖embS D τ (Dl F0 F'.fl (D.R.rS + 1))‖ ^ 2 -
        (Tu D u : ℝ) * (Tu D u' : ℝ) * ‖embS D τ (Dl F0 F'.fl D.R.rS)‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hGd, Gflag, map_sub, map_mul, map_natCast, hstar, Complex.mul_conj']
      push_cast
      rfl
    have h0 := hpos (embS D τ)
    rw [e, Complex.ofReal_re] at h0
    have e2 : D.host.rdE ^ (-(2 * (s : ℝ))) = (D.host.rdE ^ (2 * s))⁻¹ := by
      rw [Real.rpow_neg hrd0.le, ← Real.rpow_natCast]
      push_cast
      rfl
    rw [e, Complex.norm_real, Real.norm_of_nonneg h0, Gz, absDl, absDl, absReal, absReal, s2, ← hs, e2]
    change (‖embS D τ (Dl F0 F'.fl (D.R.rS + 1))‖ * _) ^ 2 - _ * (‖embS D τ (Dl F0 F'.fl D.R.rS)‖ * _) ^ 2 = _
    ring
  simp only [hGz]
  refine (pow_left_inj₀ (Real.sqrt_nonneg _) (Finset.prod_nonneg fun τ _ => by positivity) two_ne_zero).1
    (key.trans ?_)
  have e3 : ∏ a, FractionalIdeal.absNorm (coefI D a) = (FractionalIdeal.absNorm (ddS D) ^ s)⁻¹ := by
    simp only [coefI_eq, map_inv₀, map_pow, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, s1]
  have e4 : |Algebra.norm ℚ ((-1) ^ (D.R.rS + 1) * G)| = |Algebra.norm ℚ G| := by
    rw [map_mul, map_pow, abs_mul, abs_pow, ← map_one (algebraMap ℚ D.host.E), ← map_neg,
      Algebra.norm_algebraMap]
    simp
  rw [Finset.prod_mul_distrib, mul_pow, ← Finset.prod_pow (f := fun τ => ‖embS D τ G‖), hnorm, Finset.prod_const,
    Finset.card_univ, hcard, e4, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, e3]
  push_cast
  rw [hdd]
  ring

end GlobalTheory.LoopC.FrameDet
