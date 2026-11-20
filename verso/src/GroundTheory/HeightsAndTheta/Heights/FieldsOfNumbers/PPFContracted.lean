import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace PFContracted

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def blockDeg (k : K) : (Σ k, ι k) → ℕ := fun v => blockWeight ι v k

/- English proof (translation)
Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockDeg]`.
-/
theorem weight_blockDeg (k : K) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockDeg (ι := ι) k) d = Finsupp.weight (blockWeight ι) d k := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockDeg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h m r hr`. Conclude with `(mem_iff_weightedHomogeneousComponent_mem F w h r).mp hr m`. Introduce `h m r hr`. Use `h m r hr` as an intermediate fact.

Rewrite `this` using `[← weightedDecomposition.decompose'_apply]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_iff {M : Type*} [AddCommMonoid M] [DecidableEq M] (w : (Σ k, ι k) → M)
    (I : Ideal (MRing ι F)) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F w) ↔
      ∀ (m : M), ∀ r ∈ I, weightedHomogeneousComponent w m r ∈ I := by
  constructor
  · intro h m r hr
    exact (mem_iff_weightedHomogeneousComponent_mem F w h r).mp hr m
  · intro h m r hr
    have := h m r hr
    rwa [← weightedDecomposition.decompose'_apply] at this

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, weight_blockDeg]`. Distinguish the cases in `hd : coeff d p = 0`. Apply the tactic sequence `split_ifs <;> simp [hd]`. Establish `hw : Finsupp.weight (blockWeight ι) d = b` using `hp hd`.

Rewrite using `[hw]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem component_blockDeg_of_isMultiHomog {p : MRing ι F} {b : K → ℕ} (hp : IsMultiHomog p b)
    (k : K) (n : ℕ) :
    weightedHomogeneousComponent (blockDeg k) n p = if b k = n then p else 0 := by
  ext d
  rw [coeff_weightedHomogeneousComponent, weight_blockDeg]
  by_cases hd : coeff d p = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    rw [hw]
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) r, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp r), map_sum]`. Use `Ideal.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[component_blockDeg_of_isMultiHomog (weightedHomogeneousComponent_isWeightedHomogeneous b r)]`. Use `split_ifs`. Conclude with `hI r hr b`.

Conclude with `I.zero_mem`.
-/
theorem blockDeg_component_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) (k : K) (n : ℕ)
    {r : MRing ι F} (hr : r ∈ I) : weightedHomogeneousComponent (blockDeg k) n r ∈ I := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) r,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp r), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [component_blockDeg_of_isMultiHomog (weightedHomogeneousComponent_isWeightedHomogeneous b r)]
  split_ifs
  · exact hI r hr b
  · exact I.zero_mem

/- English proof (translation)
Introduce `r hr b`. Set `G : Finset K → MRing ι F` to `fun T => ∑ d ∈ r.support.filter (fun d => ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k), monomial d (coeff d r)`. Establish `hG : ∀ T d, coeff d (G T) = if ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k then coeff d r else 0`. Introduce `T d`. Simplify using `only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, mem_support_iff]`.

Apply the tactic sequence `by_cases hc : coeff d r = 0 <;> simp [hc]`. Establish `hmem : ∀ T, G T ∈ I`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`.

Establish `: G ∅ = r`. Use extensionality with `d`. Rewrite using `[hG]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `hr`. Consider the case `insert k T hk ih`. Establish `: G (insert k T) = weightedHomogeneousComponent (blockDeg k) (b k) (G T)`. Use extensionality with `d`. Rewrite using `[hG, coeff_weightedHomogeneousComponent, hG, weight_blockDeg]`.

Simplify using `only [Finset.forall_mem_insert, ite_and]`. Rewrite using `[this]`. Conclude with `h k (b k) _ ih`. Establish `: G Finset.univ = weightedHomogeneousComponent (blockWeight ι) b r`. Use extensionality with `d`.

Rewrite using `[hG, coeff_weightedHomogeneousComponent]`. Distinguish the cases in `hw : Finsupp.weight (blockWeight ι) d = b`. Simplify using `[hw]`. Rewrite using `[if_neg hw, if_neg]`. Conclude with `fun h => hw (funext fun k => h k (Finset.mem_univ k))`.

Rewrite using `[← this]`. Conclude with `hmem _`.
-/
theorem isMultiHomogIdeal_of_blockDeg [Fintype K] {I : Ideal (MRing ι F)}
    (h : ∀ (k : K) (n : ℕ), ∀ r ∈ I, weightedHomogeneousComponent (blockDeg k) n r ∈ I) :
    IsMultiHomogIdeal I := by
  classical
  intro r hr b
  let G : Finset K → MRing ι F := fun T =>
    ∑ d ∈ r.support.filter (fun d => ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k),
      monomial d (coeff d r)
  have hG : ∀ T d, coeff d (G T) =
      if ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k then coeff d r else 0 := by
    intro T d
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
      mem_support_iff]
    by_cases hc : coeff d r = 0 <;> simp [hc]
  have hmem : ∀ T, G T ∈ I := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : G ∅ = r := by
        ext d
        rw [hG]
        simp
      rw [this]
      exact hr
    | insert k T hk ih =>
      have : G (insert k T) = weightedHomogeneousComponent (blockDeg k) (b k) (G T) := by
        ext d
        rw [hG, coeff_weightedHomogeneousComponent, hG, weight_blockDeg]
        simp only [Finset.forall_mem_insert, ite_and]
      rw [this]
      exact h k (b k) _ ih
  have : G Finset.univ = weightedHomogeneousComponent (blockWeight ι) b r := by
    ext d
    rw [hG, coeff_weightedHomogeneousComponent]
    by_cases hw : Finsupp.weight (blockWeight ι) d = b
    · simp [hw]
    · rw [if_neg hw, if_neg]
      exact fun h => hw (funext fun k => h k (Finset.mem_univ k))
  rw [← this]
  exact hmem _

/- English proof (translation)
Use `isMultiHomogIdeal_of_blockDeg fun k n r hr => ?_` and prove the remaining obligations. Establish `hIk : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι` using `ι) k)) := (isHomogeneous_iff _ I).mpr fun n r hr => blockDeg_component_mem hI k n hr`. Establish `hcore : (W.homogeneousCore (weightedHomogeneousSubmodule F (blockDeg (ι` using `ι) k))).toIdeal.IsPrime := hW.1.1.homogeneousCore`. Establish `hle : I ≤ (W.homogeneousCore (weightedHomogeneousSubmodule F (blockDeg (ι` using `ι) k))).toIdeal := hIk.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)`. Establish `heq : (W.homogeneousCore (weightedHomogeneousSubmodule F (blockDeg (ι` using `ι) k))).toIdeal = W := le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) (hW.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))`.

Establish `hWk : W.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι` using `ι) k)) := by`. Rewrite using `[Ideal.IsHomogeneous.iff_eq]`. Conclude with `heq`. Conclude with `(isHomogeneous_iff _ W).mp hWk n r hr`.
-/
theorem isMultiHomogIdeal_of_mem_minimalPrimes [Fintype K] {I W : Ideal (MRing ι F)}
    (hI : IsMultiHomogIdeal I) (hW : W ∈ I.minimalPrimes) : IsMultiHomogIdeal W := by
  refine isMultiHomogIdeal_of_blockDeg fun k n r hr => ?_
  have hIk : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) :=
    (isHomogeneous_iff _ I).mpr fun n r hr => blockDeg_component_mem hI k n hr
  have hcore : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal.IsPrime :=
    hW.1.1.homogeneousCore
  have hle : I ≤ (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal :=
    hIk.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have heq : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hW.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hWk : W.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  exact (isHomogeneous_iff _ W).mp hWk n r hr

/- English proof (translation)
Establish `hI' : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι))` using `(isHomogeneous_iff (blockWeight ι) I).mpr fun m r hr => hI r hr m`. Establish `: (I ⊔ Ideal.span {f}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι))` using `hI'.sup (Ideal.homogeneous_span _ _ fun x hx => by`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `⟨c, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩)`.

Introduce `r hr b`. Conclude with `(isHomogeneous_iff _ _).mp this b r hr`.
-/
theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {f : MRing ι F} {c : K → ℕ} (hf : IsMultiHomog f c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {f}) := by
  classical
  have hI' : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    (isHomogeneous_iff (blockWeight ι) I).mpr fun m r hr => hI r hr m
  have : (I ⊔ Ideal.span {f}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    hI'.sup (Ideal.homogeneous_span _ _ fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨c, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩)
  intro r hr b
  exact (isHomogeneous_iff _ _).mp this b r hr

end Homog

section Dim

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

/- English proof (translation)
Establish `h1` using `card_le_ringKrullDim hQ hrel`. Establish `h2` using `ringKrullDim_lt_top Q`. Choose the witnesses or unpack the hypotheses as in `⟨D, hD⟩ : ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by`. Consider the cases of `h : ringKrullDim (MRing ι F ⧸ Q) with`. Consider the case `bot`.

Rewrite `h1` using `[h]`. Conclude with `absurd h1 (by simp)`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

Rewrite `h2` using `[h]`. Conclude with `absurd h2 (by simp)`. Consider the case `coe D => exact ⟨D, rfl⟩`. Use `⟨D, ?_, hD⟩` and prove the remaining obligations. Rewrite `h1` using `[hD]`.

Conclude with `h1` after adjusting the coercions.
-/
theorem exists_ringKrullDim_eq [Fintype K] [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι F)}
    [Q.IsPrime] (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q)
    (hrel : IsRelevant Q) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 := card_le_ringKrullDim hQ hrel
  have h2 := ringKrullDim_lt_top Q
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
    cases h : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [h] at h1
      exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [h] at h2
        exact absurd h2 (by simp)
      | coe D => exact ⟨D, rfl⟩
  refine ⟨D, ?_, hD⟩
  rw [hD] at h1
  exact_mod_cast h1

/- English proof (translation)
Rewrite using `[relDim, hD]`. Both sides reduce to the same expression.
-/
theorem relDim_eq_int [Fintype K] {Q : Ideal (MRing ι F)} {D : ℕ}
    (hD : ringKrullDim (MRing ι F ⧸ Q) = D) :
    relDim Q = ((((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  rw [relDim, hD]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem natCast_withBot_withTop (n : ℕ) :
    ((n : ℕ) : WithBot (WithTop ℤ)) = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl

end Dim

section Contract

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]

/- English proof (translation)
Establish `: (rename (blockIncl j ι')).comp (killBlocks (F` using `F) T) = (killBlocks (T.map j)).comp (rename (blockIncl j ι')) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, killBlocks_X, blockIncl, Finset.mem_map', apply_ite (rename (blockIncl j ι')), map_zero]`. Conclude with `AlgHom.congr_fun this q`.
-/
theorem rename_killBlocks (j : K ↪ K') (ι' : K' → Type*) (T : Finset K)
    (q : MRing (fun k => ι' (j k)) F) :
    rename (blockIncl j ι') (killBlocks T q) = killBlocks (T.map j) (rename (blockIncl j ι') q) := by
  have : (rename (blockIncl j ι')).comp (killBlocks (F := F) T) =
      (killBlocks (T.map j)).comp (rename (blockIncl j ι')) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, killBlocks_X, blockIncl, Finset.mem_map',
      apply_ite (rename (blockIncl j ι')), map_zero]
  exact AlgHom.congr_fun this q

/- English proof (translation)
Express the relevant statement in the definitionally equal form `rename (blockIncl j ι') (killBlocks T q) ∈ P'`. Rewrite using `[rename_killBlocks]`. Conclude with `killBlocks_mem_of_isMultiHomogIdeal hP' _ hq`.
-/
theorem contractPrime_killStable (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (hP' : IsMultiHomogIdeal P') (T : Finset K) (q : MRing (fun k => ι' (j k)) F)
    (hq : q ∈ contractPrime j P') : killBlocks T q ∈ contractPrime j P' := by
  change rename (blockIncl j ι') (killBlocks T q) ∈ P'
  rw [rename_killBlocks]
  exact killBlocks_mem_of_isMultiHomogIdeal hP' _ hq

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `h (j k)`. Use `⟨i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'`. Rewrite using `[rename_X]`.

Conclude with `hi`.
-/
theorem contractPrime_isRelevant (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (h : IsRelevant P') : IsRelevant (contractPrime j P') := by
  intro k
  obtain ⟨i, hi⟩ := h (j k)
  refine ⟨i, ?_⟩
  change rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
  rw [rename_X]
  exact hi

end Contract

/- English proof (translation)
Unfold `eventualValue`. Use `split_ifs with hc`. Take `⟨m, h1, h2⟩` from `(hc.choose_spec.and h).exists`. Rewrite using `[← h1, h2]`. Both sides reduce to the same expression.
-/
theorem eventualValue_eq_zero {K : Type*} {f : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, h1, h2⟩ := (hc.choose_spec.and h).exists
    rw [← h1, h2]
  · rfl

section Main

variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]

def pullNat (e : K → ℕ) : K' → ℕ := ∑ κ, e κ • (Pi.single (j κ) 1 : K' → ℕ)

/- English proof (translation)
Distinguish the cases in `h : ∃ κ, j κ = k'`. Take `⟨κ, rfl⟩` from `h`. Rewrite using `[j.injective.extend_apply]`. Simplify using `[pullNat, Finset.sum_apply, Pi.single_apply, j.injective.eq_iff]`. Rewrite using `[Function.extend_apply' _ _ _ h]`.

Simplify using `only [pullNat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]`. Rewrite using `[Finset.sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `κ _`. Rewrite using `[if_neg (fun hk => h ⟨κ, hk.symm⟩), mul_zero]`.
-/
theorem pullNat_apply (e : K → ℕ) (k' : K') :
    (pullNat K K' j e k' : ℤ) = Function.extend j (fun κ => (e κ : ℤ)) 0 k' := by
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply]
    simp [pullNat, Finset.sum_apply, Pi.single_apply, j.injective.eq_iff]
  · rw [Function.extend_apply' _ _ _ h]
    simp only [pullNat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_zero]
    · simp
    · intro κ _
      rw [if_neg (fun hk => h ⟨κ, hk.symm⟩), mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `k'`. Rewrite using `[pullNat_apply, pullNat_apply, pullDeg]`. Distinguish the cases in `h : ∃ κ, j κ = k'`. Take `⟨κ, rfl⟩` from `h`. Rewrite using `[j.injective.extend_apply, j.injective.extend_apply, j.injective.extend_apply]`.

Conclude with `Int.toNat_sub_toNat_neg (b κ)`. Rewrite using `[Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]`. Simplify using the standard rewrite rules.
-/
theorem pullNat_sub (b : K → ℤ) :
    (fun k' => (pullNat K K' j (fun κ => (b κ).toNat) k' : ℤ) -
      pullNat K K' j (fun κ => (-b κ).toNat) k') = pullDeg j b := by
  funext k'
  rw [pullNat_apply, pullNat_apply, pullDeg]
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply, j.injective.extend_apply, j.injective.extend_apply]
    exact Int.toNat_sub_toNat_neg (b κ)
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h,
      Function.extend_apply' _ _ _ h]
    simp

variable {F K K' j ι'}

def monoSmall (i : ∀ k', ι' k') (e : K → ℕ) : MRing (fun k => ι' (j k)) F :=
  ∏ κ, X ⟨κ, i (j κ)⟩ ^ e κ

/- English proof (translation)
Simplify using `[monoSmall, map_prod, blockIncl]`.
-/
theorem rename_monoSmall (i : ∀ k', ι' k') (e : K → ℕ) :
    rename (blockIncl j ι') (monoSmall (F := F) i e) = ∏ κ, X ⟨j κ, i (j κ)⟩ ^ e κ := by
  simp [monoSmall, map_prod, blockIncl]

/- English proof (translation)
Rewrite using `[rename_monoSmall]`. Use `IsWeightedHomogeneous.prod Finset.univ (fun κ => (X ⟨j κ, i (j κ)⟩ : MRing ι' F) ^ e κ) (fun κ => e κ • blockWeight ι' ⟨j κ, i (j κ)⟩) (fun κ _ => (isWeightedHomogeneous_X F (blockWeight ι') _).pow (e κ))` as an intermediate fact. Conclude with `this`.
-/
theorem isMultiHomog_rename_monoSmall (i : ∀ k', ι' k') (e : K → ℕ) :
    IsMultiHomog (rename (blockIncl j ι') (monoSmall (F := F) i e)) (pullNat K K' j e) := by
  rw [rename_monoSmall]
  have := IsWeightedHomogeneous.prod Finset.univ
    (fun κ => (X ⟨j κ, i (j κ)⟩ : MRing ι' F) ^ e κ)
    (fun κ => e κ • blockWeight ι' ⟨j κ, i (j κ)⟩)
    (fun κ _ => (isWeightedHomogeneous_X F (blockWeight ι') _).pow (e κ))
  exact this

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `P' hP' D D0 _ _ hD0 hlt bs`. Use `hP'.isPrime` as an intermediate fact.

Take `⟨D1, hc, hD1⟩` from `exists_ringKrullDim_eq (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)`. Rewrite `hD1` using `[hD0]`. Establish `: D0 = D1` using `by exact_mod_cast hD1`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`.

Introduce `P' hP' D D0 hD hDle hD0 hlt bs`. Use `hP'.isPrime` as an intermediate fact. Take `⟨D', hc', hD'⟩` from `exists_ringKrullDim_eq (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant`. Rewrite `hD'` using `[hD]`. Establish `hDD : D = D'` using `by exact_mod_cast hD'`.

Substitute `hDD` using the available equality. Distinguish the cases in `hlow : D - Fintype.card K' < k + 1`. Establish `hrel : relDim P' = ((D - Fintype.card K' : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[relDim_eq_int hD, natCast_withBot_withTop]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Conclude with `eventualValue_eq_zero ((h1 F K' ι' P' hP'.multiHomog hP'.relevant _ hrel).2 (k + 1) hlow _)`. Establish `hrel : relDim P' = ((k + 1 : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[relDim_eq_int hD, natCast_withBot_withTop]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Use `choose i hi using hP'.relevant`. Use `set b := bs (Fin.last k)`. Use `set ep : K → ℕ := fun κ => (b κ).toNat`. Use `set em : K → ℕ := fun κ => (-b κ).toNat`.

Establish `hnotmem : ∀ e : K → ℕ, rename (blockIncl j ι') (monoSmall (F` using `F) i e) ∉ P' := by`. Introduce `e hmem`. Rewrite `hmem` using `[rename_monoSmall]`. Take `⟨κ, -, hκ⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hP'.isPrime)).mp hmem`. Conclude with `hi (j κ) (hP'.isPrime.mem_of_pow_mem _ hκ)`.

Establish `hzero : ∀ (e : K → ℕ) (W : Ideal (MRing ι' F)), W ∈ (P' ⊔ Ideal.span {rename (blockIncl j ι') (monoSmall (F` using `F) i e)}).minimalPrimes → IsRelevant W → intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by`. Introduce `e W hmin hWrel`. Establish `hWp : W.IsPrime` using `hmin.1.1`. Establish `hWh : IsMultiHomogIdeal W` using `isMultiHomogIdeal_of_mem_minimalPrimes (isMultiHomogIdeal_sup_span hP'.multiHomog (isMultiHomog_rename_monoSmall i e)) hmin`. Establish `hPW : P' ≤ W` using `le_sup_left.trans hmin.1.2`.

Establish `hfW : rename (blockIncl j ι') (monoSmall (F` using `F) i e) ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)`. Take `⟨DW, -, hDW⟩` from `exists_ringKrullDim_eq (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hWh T hq) hWrel`. Take `⟨DW0, -, hDW0⟩` from `exists_ringKrullDim_eq (contractPrime_killStable j ι' hWh) (contractPrime_isRelevant j ι' hWrel)`. Establish `hdrop` using `ringKrullDim_add_one_le hPW (hnotmem e) hfW`. Rewrite `hdrop` using `[hDW, hD]`.

Establish `hdrop' : DW + 1 ≤ D` using `by exact_mod_cast hdrop`. Establish `hdrop0` using `ringKrullDim_add_one_le (P := contractPrime j P') (Q := contractPrime j W) (Ideal.comap_mono hPW) (f := monoSmall i e) (hnotmem e) hfW`. Rewrite `hdrop0` using `[hDW0, hD0]`. Establish `hdrop0' : DW0 + 1 ≤ D0` using `by exact_mod_cast hdrop0`. Conclude with `ih W ⟨hWp, hWh, hWrel⟩ DW DW0 hDW (by omega) hDW0 (by omega) _`.

Establish `hsupp : ∀ (g : MRing ι' F) (W : Ideal (MRing ι' F)), divCycle P' g W ≠ 0 → W ∈ (P' ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W`. Introduce `g W h`. Unfold `divCycle at h`. Use `split_ifs at h with hc`. Conclude with `hc`.

Conclude with `absurd rfl h`. Establish `hcut` using `h2 F K' ι' P' hP' k hrel _ _ _ _ (isMultiHomog_rename_monoSmall i ep) (isMultiHomog_rename_monoSmall i em) (hnotmem ep) (hnotmem em) (fun x : Fin k => pullDeg j (bs x.castSucc))`. Rewrite `hcut` using `[pullNat_sub]`. Establish `hsplit : (fun x => pullDeg j (bs x)) = Fin.snoc (α` using `fun _ => K' → ℤ) (fun x : Fin k => pullDeg j (bs x.castSucc)) (pullDeg j b) := by`. Use function extensionality and compare the values at `x`.

Use `Fin.lastCases ?_ (fun y => ?_) x` and prove the remaining obligations. Simplify using `[b]`. Simplify using the standard rewrite rules. Rewrite using `[hsplit, hcut]`. Establish `hterm : ∀ W, ratDiv P' (rename (blockIncl j ι') (monoSmall (F` using `F) i ep)) (rename (blockIncl j ι') (monoSmall (F := F) i em)) W * intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by`.

Introduce `W`. Distinguish the cases in `hA : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i ep)) W = 0`. Distinguish the cases in `hB : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i em)) W = 0`. Simplify using `[ratDiv, hA, hB]`. Take `⟨hm, hr⟩` from `hsupp _ W hB`.

Rewrite using `[hzero em W hm hr, mul_zero]`. Take `⟨hm, hr⟩` from `hsupp _ W hA`. Rewrite using `[hzero ep W hm hr, mul_zero]`. Simplify using `only [cycEval, hterm, finsum_zero]`.
-/
theorem key (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ D D0 : ℕ,
      ringKrullDim (MRing ι' F ⧸ P') = D → D ≤ n + Fintype.card K' →
      ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') = D0 →
      D0 < n + Fintype.card K →
      ∀ bs : Fin n → K → ℤ, intNum F P' (fun i => pullDeg j (bs i)) = 0 := by
  intro n
  induction n with
  | zero =>
    intro P' hP' D D0 _ _ hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D1, hc, hD1⟩ := exists_ringKrullDim_eq
      (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
    rw [hD0] at hD1
    have : D0 = D1 := by exact_mod_cast hD1
    omega
  | succ k ih =>
    intro P' hP' D D0 hD hDle hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D', hc', hD'⟩ := exists_ringKrullDim_eq
      (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
    rw [hD] at hD'
    have hDD : D = D' := by exact_mod_cast hD'
    subst hDD
    by_cases hlow : D - Fintype.card K' < k + 1
    · have hrel : relDim P' = ((D - Fintype.card K' : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      exact eventualValue_eq_zero
        ((h1 F K' ι' P' hP'.multiHomog hP'.relevant _ hrel).2 (k + 1) hlow _)
    · have hrel : relDim P' = ((k + 1 : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      choose i hi using hP'.relevant
      set b := bs (Fin.last k)
      set ep : K → ℕ := fun κ => (b κ).toNat
      set em : K → ℕ := fun κ => (-b κ).toNat
      have hnotmem : ∀ e : K → ℕ, rename (blockIncl j ι') (monoSmall (F := F) i e) ∉ P' := by
        intro e hmem
        rw [rename_monoSmall] at hmem
        obtain ⟨κ, -, hκ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP'.isPrime)).mp hmem
        exact hi (j κ) (hP'.isPrime.mem_of_pow_mem _ hκ)

      have hzero : ∀ (e : K → ℕ) (W : Ideal (MRing ι' F)),
          W ∈ (P' ⊔ Ideal.span {rename (blockIncl j ι') (monoSmall (F := F) i e)}).minimalPrimes →
          IsRelevant W → intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro e W hmin hWrel
        have hWp : W.IsPrime := hmin.1.1
        have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes
          (isMultiHomogIdeal_sup_span hP'.multiHomog (isMultiHomog_rename_monoSmall i e)) hmin
        have hPW : P' ≤ W := le_sup_left.trans hmin.1.2
        have hfW : rename (blockIncl j ι') (monoSmall (F := F) i e) ∈ W :=
          (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
        obtain ⟨DW, -, hDW⟩ := exists_ringKrullDim_eq
          (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hWh T hq) hWrel
        obtain ⟨DW0, -, hDW0⟩ := exists_ringKrullDim_eq
          (contractPrime_killStable j ι' hWh) (contractPrime_isRelevant j ι' hWrel)
        have hdrop := ringKrullDim_add_one_le hPW (hnotmem e) hfW
        rw [hDW, hD] at hdrop
        have hdrop' : DW + 1 ≤ D := by exact_mod_cast hdrop
        have hdrop0 := ringKrullDim_add_one_le (P := contractPrime j P') (Q := contractPrime j W)
          (Ideal.comap_mono hPW) (f := monoSmall i e) (hnotmem e) hfW
        rw [hDW0, hD0] at hdrop0
        have hdrop0' : DW0 + 1 ≤ D0 := by exact_mod_cast hdrop0
        exact ih W ⟨hWp, hWh, hWrel⟩ DW DW0 hDW (by omega) hDW0 (by omega) _
      have hsupp : ∀ (g : MRing ι' F) (W : Ideal (MRing ι' F)), divCycle P' g W ≠ 0 →
          W ∈ (P' ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W := by
        intro g W h
        unfold divCycle at h
        split_ifs at h with hc
        · exact hc
        · exact absurd rfl h
      have hcut := h2 F K' ι' P' hP' k hrel _ _ _ _ (isMultiHomog_rename_monoSmall i ep)
        (isMultiHomog_rename_monoSmall i em) (hnotmem ep) (hnotmem em)
        (fun x : Fin k => pullDeg j (bs x.castSucc))
      rw [pullNat_sub] at hcut
      have hsplit : (fun x => pullDeg j (bs x)) = Fin.snoc (α := fun _ => K' → ℤ)
          (fun x : Fin k => pullDeg j (bs x.castSucc)) (pullDeg j b) := by
        funext x
        refine Fin.lastCases ?_ (fun y => ?_) x
        · simp [b]
        · simp
      rw [hsplit, hcut]
      have hterm : ∀ W, ratDiv P' (rename (blockIncl j ι') (monoSmall (F := F) i ep))
          (rename (blockIncl j ι') (monoSmall (F := F) i em)) W *
            intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro W
        by_cases hA : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i ep)) W = 0
        · by_cases hB : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i em)) W = 0
          · simp [ratDiv, hA, hB]
          · obtain ⟨hm, hr⟩ := hsupp _ W hB
            rw [hzero em W hm hr, mul_zero]
        · obtain ⟨hm, hr⟩ := hsupp _ W hA
          rw [hzero ep W hm hr, mul_zero]
      simp only [cycEval, hterm, finsum_zero]

end Main

end PFContracted

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n hrel hlt bs`. Use `hP'.isPrime` as an intermediate fact. Take `⟨D, -, hD⟩` from `PFContracted.exists_ringKrullDim_eq (fun T q hq => PFContracted.killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant`. Take `⟨D0, -, hD0⟩` from `PFContracted.exists_ringKrullDim_eq (PFContracted.contractPrime_killStable j ι' hP'.multiHomog) (PFContracted.contractPrime_isRelevant j ι' hP'.relevant)`. Rewrite `hrel` using `[PFContracted.relDim_eq_int hD, PFContracted.natCast_withBot_withTop]`.

Rewrite `hlt` using `[PFContracted.relDim_eq_int hD0, PFContracted.natCast_withBot_withTop]`. Establish `e1 : (D : ℤ) - Fintype.card K' = n` using `WithTop.coe_inj.mp (WithBot.coe_inj.mp hrel)`. Establish `e2 : (D0 : ℤ) - Fintype.card K < n` using `WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt)`. Conclude with `PFContracted.key h1 h2 n P' hP' D D0 hD (by omega) hD0 (by omega) bs`.
-/
theorem PFContracted.proof (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ProjectionFormulaContracted.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hrel hlt bs
  have := hP'.isPrime
  obtain ⟨D, -, hD⟩ := PFContracted.exists_ringKrullDim_eq
    (fun T q hq => PFContracted.killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq)
    hP'.relevant
  obtain ⟨D0, -, hD0⟩ := PFContracted.exists_ringKrullDim_eq
    (PFContracted.contractPrime_killStable j ι' hP'.multiHomog)
    (PFContracted.contractPrime_isRelevant j ι' hP'.relevant)
  rw [PFContracted.relDim_eq_int hD, PFContracted.natCast_withBot_withTop] at hrel
  rw [PFContracted.relDim_eq_int hD0, PFContracted.natCast_withBot_withTop] at hlt
  have e1 : (D : ℤ) - Fintype.card K' = n := WithTop.coe_inj.mp (WithBot.coe_inj.mp hrel)
  have e2 : (D0 : ℤ) - Fintype.card K < n := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt)
  exact PFContracted.key h1 h2 n P' hP' D D0 hD (by omega) hD0 (by omega) bs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
