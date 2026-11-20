import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

noncomputable section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult Filter ContinuousLinearMap Module.End
open scoped InnerProductSpace Topology

namespace GlobalTheory.DiscreteSum

section Compact

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/- English proof (translation)
Establish `h0 : 0 ≤ hsNormSq T` using `tsum_nonneg fun _ => sq_nonneg _`. Rewrite using `[← Real.le_sqrt (norm_nonneg _) h0]`. Use `opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_` and prove the remaining obligations. Use `abs_le_of_sq_le_sq' ?_ (by positivity) |>.2` and prove the remaining obligations. Rewrite using `[mul_pow, Real.sq_sqrt h0]`.

Use `hasSum_le (fun j => ?_) (hasSum_norm_inner_sq (stdBasis K) (T x)) ((hasSum_adjoint (stdBasis H) (stdBasis K) (h.hasSum (stdBasis H))).mul_right (‖x‖ ^ 2))` and prove the remaining obligations. Rewrite using `[← adjoint_inner_left, ← mul_pow]`. Use `gcongr`. Conclude with `norm_inner_le_norm _ _`.
-/
theorem norm_sq_le_hsNormSq {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) : ‖T‖ ^ 2 ≤ hsNormSq T := by
  have h0 : 0 ≤ hsNormSq T := tsum_nonneg fun _ => sq_nonneg _
  rw [← Real.le_sqrt (norm_nonneg _) h0]
  refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, Real.sq_sqrt h0]
  refine hasSum_le (fun j => ?_) (hasSum_norm_inner_sq (stdBasis K) (T x))
    ((hasSum_adjoint (stdBasis H) (stdBasis K) (h.hasSum (stdBasis H))).mul_right (‖x‖ ^ 2))
  rw [← adjoint_inner_left, ← mul_pow]
  gcongr
  exact norm_inner_le_norm _ _

/- English proof (translation)
Set `e` to `stdBasis H`. Set `P : Finset (stdIndex H) → (H →L[ℂ] K)` to `fun s => ∑ i ∈ s, InnerProductSpace.rankOne ℂ (T (e i)) (e i)`. Establish `hP : ∀ s j, (T - P s) (e j) = if j ∈ s then 0 else T (e j)` using `fun s j => by`. Use `orthonormal_iff_ite.1 e.orthonormal` as an intermediate fact. Simplify using `only [P, sub_apply, sum_apply, InnerProductSpace.rankOne_apply, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hs : ∀ s, HasSum (fun j => ‖(T - P s) (e j)‖ ^ 2) (∑' j : {j // j ∉ s}, ‖T (e j)‖ ^ 2)` using `fun s => by`. Use `(hasSum_subtype_iff_indicator (s := {j | j ∉ s})).1 (Summable.subtype h {j | j ∉ s}).hasSum` as an intermediate fact. Use `this.congr_fun fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hj : j ∈ s <;> simp [hP, hj, e]`.

Use `isCompactOperator_of_tendsto (l := atTop) (F := P) ?_ (.of_forall fun s => ?_)` and prove the remaining obligations. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `ht` using `(tendsto_tsum_compl_atTop_zero fun j => ‖T (e j)‖ ^ 2).sqrt`. Rewrite `ht` using `[Real.sqrt_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) ht` and prove the remaining obligations.

Rewrite using `[norm_sub_rev]`. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Conclude with `(norm_sq_le_hsNormSq (hs s).summable).trans (hs s).tsum_eq.le`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact isCompactOperator_zero`.

Consider the case `insert i s hi ih`. Simplify using `only [P, Finset.sum_insert hi]`. Conclude with `((isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton ℂ (T (e i)))).comp_clm (innerSL ℂ (e i))).add ih`.
-/
theorem isCompactOperator_of_isHilbertSchmidt {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) : IsCompactOperator T := by
  classical
  let e := stdBasis H
  let P : Finset (stdIndex H) → (H →L[ℂ] K) := fun s => ∑ i ∈ s, InnerProductSpace.rankOne ℂ (T (e i)) (e i)
  have hP : ∀ s j, (T - P s) (e j) = if j ∈ s then 0 else T (e j) := fun s j => by
    have := orthonormal_iff_ite.1 e.orthonormal
    simp only [P, sub_apply, sum_apply, InnerProductSpace.rankOne_apply, this,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
    split_ifs <;> simp
  have hs : ∀ s, HasSum (fun j => ‖(T - P s) (e j)‖ ^ 2) (∑' j : {j // j ∉ s}, ‖T (e j)‖ ^ 2) := fun s => by
    have := (hasSum_subtype_iff_indicator (s := {j | j ∉ s})).1 (Summable.subtype h {j | j ∉ s}).hasSum
    refine this.congr_fun fun j => ?_
    by_cases hj : j ∈ s <;> simp [hP, hj, e]
  refine isCompactOperator_of_tendsto (l := atTop) (F := P) ?_ (.of_forall fun s => ?_)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (tendsto_tsum_compl_atTop_zero fun j => ‖T (e j)‖ ^ 2).sqrt
    rw [Real.sqrt_zero] at ht
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) ht
    rw [norm_sub_rev]
    refine Real.le_sqrt_of_sq_le ?_
    exact (norm_sq_le_hsNormSq (hs s).summable).trans (hs s).tsum_eq.le
  · induction s using Finset.induction_on with
    | empty => exact isCompactOperator_zero
    | insert i s hi ih =>
      simp only [P, Finset.sum_insert hi]
      exact ((isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton ℂ (T (e i)))).comp_clm
        (innerSL ℂ (e i))).add ih

end Compact

variable {G K H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsDiscreteSum (ρ : G →* (K →L[ℂ] K)) : Prop :=
  (∃ (ι : Type) (W : ι → Submodule ℂ K), (∀ i, IsIrredSubrep ρ (W i)) ∧
    IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) ∧
  ∀ R : IrrU G, multIn R.π ρ ⊤ < Cardinal.aleph0

variable {ρ : G →* (K →L[ℂ] K)} {π : G →* (H →L[ℂ] H)} {W : Submodule ℂ K}

/- English proof (translation)
The claim follows from `mem_homIn_top.2 fun g x => ext_inner_left ℂ fun y => by rw [adjoint_inner_right, ← inv_inv g, ← hρ.inner_apply_left, ← hπ.inner_apply_left, adjoint_inner_right, hT.2]`.
-/
theorem adjoint_mem_homIn [CompleteSpace H] (hπ : IsUnitaryRep π) (hρ : IsUnitaryRep ρ) {T : H →L[ℂ] K}
    (hT : T ∈ homIn π ρ ⊤) : adjoint T ∈ homIn ρ π ⊤ :=
  mem_homIn_top.2 fun g x => ext_inner_left ℂ fun y => by
    rw [adjoint_inner_right, ← inv_inv g, ← hρ.inner_apply_left, ← hπ.inner_apply_left, adjoint_inner_right,
      hT.2]

def EnoughCompact (ρ : G →* (K →L[ℂ] K)) : Prop :=
  ∀ v : K, v ≠ 0 → ∃ A : K →L[ℂ] K, IsCompactOperator A ∧ (∀ S ∈ homIn ρ ρ ⊤, ∀ x, A (S x) = S (A x)) ∧ A v ≠ 0

/- English proof (translation)
Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Take `⟨A, hA, hc, hAv⟩` from `h v hv0`. Use `hW.completeSpace` as an intermediate fact. Set `T` to `adjoint A ∘L A`. Establish `hTc : IsCompactOperator T` using `hA.clm_comp (adjoint A)`.

Establish `hTs : T.IsSymmetric` using `fun x y => by simp [T, adjoint_inner_left, adjoint_inner_right]`. Establish `hTS : ∀ S ∈ homIn ρ ρ ⊤, ∀ x, T (S x) = S (T x)` using `fun S hS x => ext_inner_left ℂ fun y => by`. Simplify using `only [T, comp_apply]`. Rewrite using `[hc S hS, adjoint_inner_right, ← adjoint_inner_left, ← hc _ (adjoint_mem_homIn hρ hρ hS), ← adjoint_inner_right, adjoint_inner_left]`. Establish `hP : W.starProjection ∈ homIn ρ ρ ⊤` using `mem_homIn_top.2 (hW.starProjection_apply hρ)`.

Establish `hTW : ∀ x ∈ W, T x ∈ W` using `fun x hx => by`. Rewrite using `[← Submodule.starProjection_eq_self_iff.2 hx, hTS _ hP]`. Conclude with `W.starProjection_apply_mem _`. Establish `hne : T.restrict hTW ≠ 0` using `fun e => hAv (by`. Establish `: T v = 0` using `by simpa using congrArg (fun B : W →L[ℂ] W => (B ⟨v, hv⟩ : K)) e`.

Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), ← adjoint_inner_right, show adjoint A (A v) = 0 from this, inner_zero_right])`. Establish `h1 : IsCompactOperator (T.restrict hTW)` using `IsCompactOperator.restrict' (f := T.toLinearMap) hTc hTW`. Establish `h2 : (T.restrict hTW).IsSymmetric` using `fun x y => hTs x y`. Take `⟨c, hc1, hc0⟩ : ∃ c, HasEigenvalue (T.restrict hTW : Module.End ℂ W) c ∧ c ≠ 0` from `by by_contra! hn`. Conclude with `hne ((eq_zero_of_forall_hasEigenvalue_eq_zero h1 h2).1 hn)`.

Take `⟨x, hx, hx0⟩` from `hc1.exists_hasEigenvector`. Use `⟨eigenspace T.toLinearMap c, finite_dimensional_eigenspace hTc c hc0, fun S hS y hy => ?_, (Submodule.ne_bot_iff _).2 ⟨x, ⟨x.2, ?_⟩, fun e => hx0 (Subtype.ext e)⟩⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[mem_eigenspace_iff]`. Conclude with `(hTS S hS y).trans ((congrArg S hy).trans (map_smul S c y))`. Conclude with `mem_eigenspace_iff.2 (congrArg Subtype.val (mem_eigenspace_iff.1 hx))`.
-/
theorem EnoughCompact.exists_finiteDimensional (hρ : IsUnitaryRep ρ) (h : EnoughCompact ρ) (hW : IsSubrep ρ W)
    (h0 : W ≠ ⊥) : ∃ E : Submodule ℂ K, FiniteDimensional ℂ E ∧ (∀ S ∈ homIn ρ ρ ⊤, ∀ x ∈ E, S x ∈ E) ∧ W ⊓ E ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨A, hA, hc, hAv⟩ := h v hv0
  have := hW.completeSpace
  let T := adjoint A ∘L A
  have hTc : IsCompactOperator T := hA.clm_comp (adjoint A)
  have hTs : T.IsSymmetric := fun x y => by simp [T, adjoint_inner_left, adjoint_inner_right]
  have hTS : ∀ S ∈ homIn ρ ρ ⊤, ∀ x, T (S x) = S (T x) := fun S hS x => ext_inner_left ℂ fun y => by
    simp only [T, comp_apply]
    rw [hc S hS, adjoint_inner_right, ← adjoint_inner_left, ← hc _ (adjoint_mem_homIn hρ hρ hS), ← adjoint_inner_right,
      adjoint_inner_left]
  have hP : W.starProjection ∈ homIn ρ ρ ⊤ := mem_homIn_top.2 (hW.starProjection_apply hρ)
  have hTW : ∀ x ∈ W, T x ∈ W := fun x hx => by
    rw [← Submodule.starProjection_eq_self_iff.2 hx, hTS _ hP]
    exact W.starProjection_apply_mem _
  have hne : T.restrict hTW ≠ 0 := fun e => hAv (by
    have : T v = 0 := by simpa using congrArg (fun B : W →L[ℂ] W => (B ⟨v, hv⟩ : K)) e
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← adjoint_inner_right, show adjoint A (A v) = 0 from this, inner_zero_right])
  have h1 : IsCompactOperator (T.restrict hTW) := IsCompactOperator.restrict' (f := T.toLinearMap) hTc hTW
  have h2 : (T.restrict hTW).IsSymmetric := fun x y => hTs x y
  obtain ⟨c, hc1, hc0⟩ : ∃ c, HasEigenvalue (T.restrict hTW : Module.End ℂ W) c ∧ c ≠ 0 := by
    by_contra! hn
    exact hne ((eq_zero_of_forall_hasEigenvalue_eq_zero h1 h2).1 hn)
  obtain ⟨x, hx, hx0⟩ := hc1.exists_hasEigenvector
  refine ⟨eigenspace T.toLinearMap c, finite_dimensional_eigenspace hTc c hc0, fun S hS y hy => ?_,
    (Submodule.ne_bot_iff _).2 ⟨x, ⟨x.2, ?_⟩, fun e => hx0 (Subtype.ext e)⟩⟩
  · rw [mem_eigenspace_iff] at hy ⊢
    exact (hTS S hS y).trans ((congrArg S hy).trans (map_smul S c y))
  · exact mem_eigenspace_iff.2 (congrArg Subtype.val (mem_eigenspace_iff.1 hx))

/- English proof (translation)
Take `⟨E, hE, hS, hWE⟩` from `h.exists_finiteDimensional hρ hW h0`. Take `⟨U, ⟨hU, hUW, hUE⟩, hmin⟩` from `exists_minimalFor_of_wellFoundedLT (fun U => IsSubrep ρ U ∧ U ≤ W ∧ U ⊓ E ≠ ⊥) (fun U => Module.finrank ℂ ↥(U ⊓ E)) ⟨W, hW, le_rfl, hWE⟩`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hUE`. Set `X` to `sInf {Y | IsSubrep ρ Y ∧ x ∈ Y}`. Establish `hX : IsSubrep ρ X` using `⟨by`.

Rewrite using `[Submodule.coe_sInf]`. Conclude with `isClosed_biInter fun Y hY => hY.1.1,`. Use `fun g v hv => Submodule.mem_sInf.2 fun Y hY => hY.1.2 g v (Submodule.mem_sInf.1 hv Y hY)⟩`. Establish `hxX : x ∈ X` using `Submodule.mem_sInf.2 fun Y hY => hY.2`. Establish `hXU : X ≤ U` using `sInf_le ⟨hU, hx.1⟩`.

Use `⟨X, hXU.trans hUW, hX, (Submodule.ne_bot_iff _).2 ⟨x, hxX, hx0⟩, fun Y hYX hY => ?_⟩` and prove the remaining obligations. Use `hY.completeSpace` as an intermediate fact. Distinguish the cases in `hy : Y.starProjection x = 0`. Establish `: X ≤ Yᗮ` using `sInf_le ⟨hY.orthogonal hρ, (Submodule.starProjection_apply_eq_zero_iff _).1 hy⟩`. Conclude with `.inl (le_bot_iff.1 ((le_inf le_rfl (hYX.trans this)).trans (Submodule.inf_orthogonal_eq_bot _).le))`.

Establish `h1 : Y ⊓ E ≠ ⊥` using `(Submodule.ne_bot_iff _).2 ⟨_, ⟨Y.starProjection_apply_mem x, hS _ (mem_homIn_top.2 (hY.starProjection_apply hρ)) x hx.2⟩, hy⟩`. Establish `h2 : Y ⊓ E ≤ U ⊓ E` using `inf_le_inf_right _ (hYX.trans hXU)`. Establish `: FiniteDimensional ℂ ↥(U ⊓ E)` using `Submodule.finiteDimensional_of_le inf_le_right`. Establish `h3` using `Submodule.eq_of_le_of_finrank_le h2 (hmin ⟨hY, hYX.trans (hXU.trans hUW), h1⟩ (Submodule.finrank_mono h2))`. Conclude with `.inr (le_antisymm hYX (sInf_le ⟨hY, (h3 ▸ hx : x ∈ Y ⊓ E).1⟩))`.
-/
theorem EnoughCompact.exists_irred_le (hρ : IsUnitaryRep ρ) (h : EnoughCompact ρ) (hW : IsSubrep ρ W) (h0 : W ≠ ⊥) :
    ∃ X ≤ W, IsIrredSubrep ρ X := by
  obtain ⟨E, hE, hS, hWE⟩ := h.exists_finiteDimensional hρ hW h0
  obtain ⟨U, ⟨hU, hUW, hUE⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun U => IsSubrep ρ U ∧ U ≤ W ∧ U ⊓ E ≠ ⊥) (fun U => Module.finrank ℂ ↥(U ⊓ E)) ⟨W, hW, le_rfl, hWE⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUE
  let X := sInf {Y | IsSubrep ρ Y ∧ x ∈ Y}
  have hX : IsSubrep ρ X := ⟨by
    rw [Submodule.coe_sInf]
    exact isClosed_biInter fun Y hY => hY.1.1,
    fun g v hv => Submodule.mem_sInf.2 fun Y hY => hY.1.2 g v (Submodule.mem_sInf.1 hv Y hY)⟩
  have hxX : x ∈ X := Submodule.mem_sInf.2 fun Y hY => hY.2
  have hXU : X ≤ U := sInf_le ⟨hU, hx.1⟩
  refine ⟨X, hXU.trans hUW, hX, (Submodule.ne_bot_iff _).2 ⟨x, hxX, hx0⟩, fun Y hYX hY => ?_⟩
  have := hY.completeSpace
  by_cases hy : Y.starProjection x = 0
  · have : X ≤ Yᗮ := sInf_le ⟨hY.orthogonal hρ, (Submodule.starProjection_apply_eq_zero_iff _).1 hy⟩
    exact .inl (le_bot_iff.1 ((le_inf le_rfl (hYX.trans this)).trans (Submodule.inf_orthogonal_eq_bot _).le))
  · have h1 : Y ⊓ E ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨_, ⟨Y.starProjection_apply_mem x,
      hS _ (mem_homIn_top.2 (hY.starProjection_apply hρ)) x hx.2⟩, hy⟩
    have h2 : Y ⊓ E ≤ U ⊓ E := inf_le_inf_right _ (hYX.trans hXU)
    have : FiniteDimensional ℂ ↥(U ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right
    have h3 := Submodule.eq_of_le_of_finrank_le h2
      (hmin ⟨hY, hYX.trans (hXU.trans hUW), h1⟩ (Submodule.finrank_mono h2))
    exact .inr (le_antisymm hYX (sInf_le ⟨hY, (h3 ▸ hx : x ∈ Y ⊓ E).1⟩))

/- English proof (translation)
Take `⟨S, hS⟩` from `zorn_subset {S : Set (Submodule ℂ K) | (∀ X ∈ S, IsIrredSubrep ρ X) ∧ S.Pairwise (· ⟂ ·)} fun c hc hch => ⟨⋃₀ c, ⟨fun X ⟨S, hS, hX⟩ => (hc hS).1 X hX, (Set.pairwise_sUnion hch.directedOn).2 fun S hS => (hc hS).2⟩, fun S hS => Set.subset_sUnion_of_mem hS⟩`. Establish `: ∀ i : S, CompleteSpace i.1` using `fun i => (hS.prop.1 i i.2).1.completeSpace`. Use `⟨S, Subtype.val, fun i => hS.prop.1 i i.2, .mkInternal _ (OrthogonalFamily.of_pairwise fun i j hij => hS.prop.2 i.2 j.2 (Subtype.val_injective.ne hij)) ?_⟩` and prove the remaining obligations. Rewrite using `[← sSup_eq_iSup', top_le_iff, ← Submodule.orthogonal_eq_bot_iff]`. Assume the negation of the conclusion as `h0`.

Take `⟨X, hX, hi⟩` from `h _ ((isSubrep_closure_sSup fun Y hY => (hS.prop.1 Y hY).1).orthogonal hρ) h0`. Establish `ho : ∀ Y ∈ S, X ⟂ Y` using `fun Y hY => hX.trans (Submodule.orthogonal_le ((le_sSup hY).trans (Submodule.le_topologicalClosure _)))`. Establish `hXS : X ∈ S` using `hS.eq_of_subset (t := insert X S) ⟨by rintro Y (rfl | hY); exacts [hi, hS.prop.1 Y hY], hS.prop.2.insert fun Y hY _ => ⟨ho Y hY, (ho Y hY).symm⟩⟩ (Set.subset_insert _ _) ▸ Set.mem_insert _ _`. Conclude with `hi.2.1 (Submodule.isOrtho_self.1 (ho X hXS))`.
-/
theorem exists_isHilbertSum (hρ : IsUnitaryRep ρ) (h : ∀ W, IsSubrep ρ W → W ≠ ⊥ → ∃ X ≤ W, IsIrredSubrep ρ X) :
    ∃ (ι : Type) (W : ι → Submodule ℂ K), (∀ i, IsIrredSubrep ρ (W i)) ∧
      IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ := by
  obtain ⟨S, hS⟩ := zorn_subset {S : Set (Submodule ℂ K) | (∀ X ∈ S, IsIrredSubrep ρ X) ∧ S.Pairwise (· ⟂ ·)}
    fun c hc hch => ⟨⋃₀ c, ⟨fun X ⟨S, hS, hX⟩ => (hc hS).1 X hX,
      (Set.pairwise_sUnion hch.directedOn).2 fun S hS => (hc hS).2⟩, fun S hS => Set.subset_sUnion_of_mem hS⟩
  have : ∀ i : S, CompleteSpace i.1 := fun i => (hS.prop.1 i i.2).1.completeSpace
  refine ⟨S, Subtype.val, fun i => hS.prop.1 i i.2, .mkInternal _
    (OrthogonalFamily.of_pairwise fun i j hij => hS.prop.2 i.2 j.2 (Subtype.val_injective.ne hij)) ?_⟩
  rw [← sSup_eq_iSup', top_le_iff, ← Submodule.orthogonal_eq_bot_iff]
  by_contra h0
  obtain ⟨X, hX, hi⟩ := h _ ((isSubrep_closure_sSup fun Y hY => (hS.prop.1 Y hY).1).orthogonal hρ) h0
  have ho : ∀ Y ∈ S, X ⟂ Y := fun Y hY =>
    hX.trans (Submodule.orthogonal_le ((le_sSup hY).trans (Submodule.le_topologicalClosure _)))
  have hXS : X ∈ S := hS.eq_of_subset (t := insert X S) ⟨by rintro Y (rfl | hY); exacts [hi, hS.prop.1 Y hY],
    hS.prop.2.insert fun Y hY _ => ⟨ho Y hY, (ho Y hY).symm⟩⟩ (Set.subset_insert _ _) ▸ Set.mem_insert _ _
  exact hi.2.1 (Submodule.isOrtho_self.1 (ho X hXS))

/- English proof (translation)
Rewrite using `[multIn_lt_aleph0_iff]`. Distinguish the cases in `h0 : homIn π ρ ⊤ = ⊥`. Rewrite using `[h0]`. Use `infer_instance`. Use `hπ.complete` as an intermediate fact.

Take `⟨T, hT, hT0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Establish `hc` using `(isCopy_range hπ hρ hT hT0).isIrredSubrep hπ.irred`. Take `⟨E, hE, hS, hWE⟩` from `h.exists_finiteDimensional hρ hc.1 hc.2.1`. Take `⟨_, ⟨⟨u, rfl⟩, hu⟩, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hWE`. Establish `hv : adjoint T (T u) ≠ 0` using `fun e => hu0 (by`.

Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ)]`. Conclude with `(adjoint_inner_right T u (T u)).symm.trans ((congrArg _ e).trans (inner_zero_right _)))`. Set `L : homIn π ρ ⊤ →ₗ[ℂ] E` to `{ toFun := fun S => ⟨S.1 (adjoint T (T u)), hS (S.1 ∘L adjoint T) (mem_homIn_top.2 fun g x => by`. Rewrite using `[comp_apply, (adjoint_mem_homIn hπ.unitary hρ hT).2, S.2.2, comp_apply]) _ hu⟩`. Use the proof step `map_add' := fun _ _ => rfl`.

Use the proof step `map_smul' := fun _ _ => rfl }`. Use `Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun S e => Subtype.ext (ContinuousLinearMap.ext fun x => norm_eq_zero.1 ?_))` and prove the remaining obligations. Establish `h1` using `norm_apply_eq hπ hρ S.2 (adjoint T (T u))`. Rewrite `h1` using `[show S.1 (adjoint T (T u)) = 0 from congrArg Subtype.val e, norm_zero, eq_comm, mul_eq_zero]`. Rewrite using `[norm_apply_eq hπ hρ S.2 x, h1.resolve_right (norm_ne_zero_iff.2 hv), zero_mul]`.
-/
theorem EnoughCompact.multIn_lt (hρ : IsUnitaryRep ρ) (h : EnoughCompact ρ) (hπ : IsIrrUnitary π) :
    multIn π ρ ⊤ < Cardinal.aleph0 := by
  rw [multIn_lt_aleph0_iff]
  by_cases h0 : homIn π ρ ⊤ = ⊥
  · rw [h0]; infer_instance
  have := hπ.complete
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hc := (isCopy_range hπ hρ hT hT0).isIrredSubrep hπ.irred
  obtain ⟨E, hE, hS, hWE⟩ := h.exists_finiteDimensional hρ hc.1 hc.2.1
  obtain ⟨_, ⟨⟨u, rfl⟩, hu⟩, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWE
  have hv : adjoint T (T u) ≠ 0 := fun e => hu0 (by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    exact (adjoint_inner_right T u (T u)).symm.trans ((congrArg _ e).trans (inner_zero_right _)))
  let L : homIn π ρ ⊤ →ₗ[ℂ] E :=
    { toFun := fun S => ⟨S.1 (adjoint T (T u)), hS (S.1 ∘L adjoint T) (mem_homIn_top.2 fun g x => by
        rw [comp_apply, (adjoint_mem_homIn hπ.unitary hρ hT).2, S.2.2, comp_apply]) _ hu⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun S e => Subtype.ext (ContinuousLinearMap.ext fun x => norm_eq_zero.1 ?_))
  have h1 := norm_apply_eq hπ hρ S.2 (adjoint T (T u))
  rw [show S.1 (adjoint T (T u)) = 0 from congrArg Subtype.val e, norm_zero, eq_comm, mul_eq_zero] at h1
  rw [norm_apply_eq hπ hρ S.2 x, h1.resolve_right (norm_ne_zero_iff.2 hv), zero_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_isHilbertSum hρ fun _ => h.exists_irred_le hρ, fun R => h.multIn_lt hρ R.isIrr⟩`.
-/
theorem EnoughCompact.isDiscreteSum (hρ : IsUnitaryRep ρ) (h : EnoughCompact ρ) : IsDiscreteSum ρ :=
  ⟨exists_isHilbertSum hρ fun _ => h.exists_irred_le hρ, fun R => h.multIn_lt hρ R.isIrr⟩

omit [TopologicalSpace G] in

/- English proof (translation)
Establish `h1` using `(hs.hasSum_linearIsometryEquiv_symm (hs.linearIsometryEquiv x)).mapL (innerSL ℂ x)`. Rewrite `h1` using `[LinearIsometryEquiv.symm_apply_apply]`. Use `(inner_self_eq_zero (𝕜 := ℂ)).1 (h1.unique (hasSum_zero.congr_fun fun i => ?_))` and prove the remaining obligations. Conclude with `inner_eq_zero_symm.1 (h i _ (Subtype.prop _))`.
-/
theorem eq_zero_of_isHilbertSum {ι : Type} {W : ι → Submodule ℂ K}
    (hs : IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) {x : K} (h : ∀ i, ∀ y ∈ W i, ⟪y, x⟫_ℂ = 0) :
    x = 0 := by
  have h1 := (hs.hasSum_linearIsometryEquiv_symm (hs.linearIsometryEquiv x)).mapL (innerSL ℂ x)
  rw [LinearIsometryEquiv.symm_apply_apply] at h1
  refine (inner_self_eq_zero (𝕜 := ℂ)).1 (h1.unique (hasSum_zero.congr_fun fun i => ?_))
  exact inner_eq_zero_symm.1 (h i _ (Subtype.prop _))

/- English proof (translation)
Take `⟨ι, W, hW, hs⟩` from `h.1`. Use `(isSubrep_disc (π := ρ)).completeSpace` as an intermediate fact. Rewrite using `[← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]`. Conclude with `fun x hx => eq_zero_of_isHilbertSum hs fun i y hy => hx y ((hW i).le_disc hy)`.
-/
theorem IsDiscreteSum.disc_eq_top (h : IsDiscreteSum ρ) : disc ρ = ⊤ := by
  obtain ⟨ι, W, hW, hs⟩ := h.1
  have := (isSubrep_disc (π := ρ)).completeSpace
  rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
  exact fun x hx => eq_zero_of_isHilbertSum hs fun i y hy => hx y ((hW i).le_disc hy)

/- English proof (translation)
Use `hπ.complete` as an intermediate fact. Use `hπ.irred.1` as an intermediate fact. Use `multIn_lt_aleph0_iff.1 hm` as an intermediate fact. Use `choose e he hr using fun i : {i | IsCopy π ρ (W i)} => isCopy_iff.1 i.2`. Set `b : {i | IsCopy π ρ (W i)} → homIn π ρ ⊤` to `fun i => ⟨(e i).toContinuousLinearMap, mem_homIn_top.2 (he i)⟩`.

Establish `hmem : ∀ (i : {i | IsCopy π ρ (W i)}) x, e i x ∈ W i` using `fun i x => hr i ▸ ⟨x, rfl⟩`. Establish `ho : Orthonormal ℂ fun i => e i (unitVec H)` using `⟨fun i => by rw [(e i).norm_map, norm_unitVec], fun i j hij => hs.OrthogonalFamily (Subtype.val_injective.ne hij) ⟨_, hmem i _⟩ ⟨_, hmem j _⟩⟩`. Establish `hl : LinearIndependent ℂ b` using `.of_comp ((ContinuousLinearMap.apply ℂ K (unitVec H)).toLinearMap ∘ₗ (homIn π ρ ⊤).subtype) ho.linearIndependent`. Establish `hfin : Finite {i | IsCopy π ρ (W i)}` using `hl.finite`. Use `Fintype.ofFinite {i | IsCopy π ρ (W i)}` as an intermediate fact.

Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range b)` using `fun T _ => by`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨fun i => be T.1 (b i).1, (sub_eq_zero.1 (Subtype.ext (ContinuousLinearMap.ext fun x => ?_))).symm⟩` and prove the remaining obligations. Use `set S := T - ∑ i, be T.1 (b i).1 • b i with hS`. Use `eq_zero_of_isHilbertSum hs fun j y hy => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : IsCopy π ρ (W j)`. Take `⟨z, rfl⟩ : y ∈ LinearMap.range (e ⟨j, hj⟩).toLinearMap` from `(hr ⟨j, hj⟩).symm ▸ hy`. Use `(inner_eq_be hπ hρ S.2 (b ⟨j, hj⟩).2 x z).trans (mul_eq_zero_of_left ?_ _)` and prove the remaining obligations. Establish `h1 : S.1 (unitVec H) = T.1 (unitVec H) - ∑ i, be T.1 (b i).1 • e i (unitVec H)` using `by simp [hS, b]`. Rewrite using `[be_def, h1, inner_sub_right, sub_eq_zero]`.

Conclude with `(ho.inner_right_fintype (fun i => be T.1 (b i).1) ⟨j, hj⟩).symm`. Conclude with `inner_eq_zero_of_not_uEquiv hπ (isIrrUnitary_rep hρ (hW j)) hρ (fun h => hj ⟨_, h⟩) S.2 (S := (W j).subtypeL) (U' := ⊤) (mem_homIn_top.2 fun _ _ => rfl) x ⟨y, hy⟩`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[multIn, ← (Module.Basis.mk hl hsp).mk_eq_rank'', Set.cast_ncard hfin]`.
-/
theorem multIn_eq_ncard (hρ : IsUnitaryRep ρ) (hπ : IsIrrUnitary π) (hm : multIn π ρ ⊤ < Cardinal.aleph0) {ι : Type}
    {W : ι → Submodule ℂ K} (hW : ∀ i, IsIrredSubrep ρ (W i))
    (hs : IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) :
    {i | IsCopy π ρ (W i)}.Finite ∧ multIn π ρ ⊤ = {i | IsCopy π ρ (W i)}.ncard := by
  classical
  have := hπ.complete
  have := hπ.irred.1
  have := multIn_lt_aleph0_iff.1 hm
  choose e he hr using fun i : {i | IsCopy π ρ (W i)} => isCopy_iff.1 i.2
  let b : {i | IsCopy π ρ (W i)} → homIn π ρ ⊤ := fun i => ⟨(e i).toContinuousLinearMap, mem_homIn_top.2 (he i)⟩
  have hmem : ∀ (i : {i | IsCopy π ρ (W i)}) x, e i x ∈ W i := fun i x => hr i ▸ ⟨x, rfl⟩
  have ho : Orthonormal ℂ fun i => e i (unitVec H) :=
    ⟨fun i => by rw [(e i).norm_map, norm_unitVec], fun i j hij =>
      hs.OrthogonalFamily (Subtype.val_injective.ne hij) ⟨_, hmem i _⟩ ⟨_, hmem j _⟩⟩
  have hl : LinearIndependent ℂ b :=
    .of_comp ((ContinuousLinearMap.apply ℂ K (unitVec H)).toLinearMap ∘ₗ (homIn π ρ ⊤).subtype) ho.linearIndependent
  have hfin : Finite {i | IsCopy π ρ (W i)} := hl.finite
  have := Fintype.ofFinite {i | IsCopy π ρ (W i)}
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range b) := fun T _ => by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => be T.1 (b i).1, (sub_eq_zero.1 (Subtype.ext (ContinuousLinearMap.ext fun x => ?_))).symm⟩
    set S := T - ∑ i, be T.1 (b i).1 • b i with hS
    refine eq_zero_of_isHilbertSum hs fun j y hy => ?_
    by_cases hj : IsCopy π ρ (W j)
    · obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (e ⟨j, hj⟩).toLinearMap := (hr ⟨j, hj⟩).symm ▸ hy
      refine (inner_eq_be hπ hρ S.2 (b ⟨j, hj⟩).2 x z).trans (mul_eq_zero_of_left ?_ _)
      have h1 : S.1 (unitVec H) = T.1 (unitVec H) - ∑ i, be T.1 (b i).1 • e i (unitVec H) := by simp [hS, b]
      rw [be_def, h1, inner_sub_right, sub_eq_zero]
      exact (ho.inner_right_fintype (fun i => be T.1 (b i).1) ⟨j, hj⟩).symm
    · exact inner_eq_zero_of_not_uEquiv hπ (isIrrUnitary_rep hρ (hW j)) hρ (fun h => hj ⟨_, h⟩) S.2
        (S := (W j).subtypeL) (U' := ⊤) (mem_homIn_top.2 fun _ _ => rfl) x ⟨y, hy⟩
  refine ⟨hfin, ?_⟩
  rw [multIn, ← (Module.Basis.mk hl hsp).mk_eq_rank'', Set.cast_ncard hfin]

/- English proof (translation)
Establish `hc : Continuous fun g => (⟪v, ρ g v⟫_ℂ).re` using `Complex.continuous_re.comp (continuous_const.inner (hρ.continuous_apply v))`. Establish `h1 : 0 < (⟪v, ρ 1 v⟫_ℂ).re` using `by simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv`. Use `⟨_, (isOpen_lt continuous_const hc).mem_nhds h1, fun φ hφ hs h0 hφ1 hN e => ?_⟩` and prove the remaining obligations. Establish `hf : Continuous fun g => (φ g : ℂ)` using `by fun_prop`. Establish `hfs : HasCompactSupport fun g => (φ g : ℂ)` using `hs.comp_left (g := Complex.ofReal) rfl`.

Establish `h2` using `hρ.inner_repOp (μ := μ) hf hfs v v`. Rewrite `h2` using `[e, inner_zero_right]`. Establish `h3` using `integral_re (𝕜 := ℂ) (μ := μ) ((hf.mul (continuous_const.inner (𝕜 := ℂ) (f := fun _ => v) (hρ.continuous_apply v))).integrable_of_hasCompactSupport hfs.mul_right)`. Use `((hφ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hs.mul_right (fun g => ?_) (mul_ne_zero hφ1 h1.ne')).ne' ?_` and prove the remaining obligations. Distinguish the cases in `hg : φ g = 0`.

Simplify using `[hg]`. Conclude with `mul_nonneg (h0 g) (hN hg).le`. Simplify `h3` using `[← h2]`.
-/
theorem exists_nhds_repOp_ne_zero [MeasurableSpace G] [OpensMeasurableSpace G] (μ : MeasureTheory.Measure G)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (hρ : IsUnitaryRep ρ) {v : K} (hv : v ≠ 0) :
    ∃ N ∈ 𝓝 (1 : G), ∀ φ : G → ℝ, Continuous φ → HasCompactSupport φ → 0 ≤ φ → φ 1 ≠ 0 → Function.support φ ⊆ N →
      repOp ρ μ (fun g => (φ g : ℂ)) v ≠ 0 := by
  have hc : Continuous fun g => (⟪v, ρ g v⟫_ℂ).re := Complex.continuous_re.comp
    (continuous_const.inner (hρ.continuous_apply v))
  have h1 : 0 < (⟪v, ρ 1 v⟫_ℂ).re := by simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv
  refine ⟨_, (isOpen_lt continuous_const hc).mem_nhds h1, fun φ hφ hs h0 hφ1 hN e => ?_⟩
  have hf : Continuous fun g => (φ g : ℂ) := by fun_prop
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hs.comp_left (g := Complex.ofReal) rfl
  have h2 := hρ.inner_repOp (μ := μ) hf hfs v v
  rw [e, inner_zero_right] at h2
  have h3 := integral_re (𝕜 := ℂ) (μ := μ) ((hf.mul (continuous_const.inner (𝕜 := ℂ) (f := fun _ => v)
    (hρ.continuous_apply v))).integrable_of_hasCompactSupport hfs.mul_right)
  refine ((hφ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hs.mul_right (fun g => ?_)
    (mul_ne_zero hφ1 h1.ne')).ne' ?_
  · by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (h0 g) (hN hg).le
  · simpa [← h2] using h3

end GlobalTheory.DiscreteSum

end
