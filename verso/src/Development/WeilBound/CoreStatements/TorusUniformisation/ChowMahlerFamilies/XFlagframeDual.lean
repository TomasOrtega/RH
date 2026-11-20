import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_dual

/- English proof (translation)
Establish `hM : (w.toMatrix u).BlockTriangular id` using `fun i j hij => h j i hij`. Establish `hMN : w.toMatrix u * u.toMatrix w = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip w u`. Use `haveI : Invertible (w.toMatrix u) := ⟨u.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip u w, hMN⟩`. Establish `hinv : (w.toMatrix u)⁻¹ = u.toMatrix w` using `Matrix.inv_eq_right_inv hMN`. Establish `hN : (u.toMatrix w).BlockTriangular id` using `hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM`.

Use `⟨fun i j hij => hN hij, fun i => ?_⟩` and prove the remaining obligations. Establish `hii` using `congrFun (congrFun hMN i) i`. Rewrite `hii` using `[Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i]`. Simplify using `only [Module.Basis.toMatrix_apply] at hii`. Conclude with `eq_inv_of_mul_eq_one_right hii`.

Introduce `k _ hki`. Break down `lt_or_gt_of_ne hki with hk | hk` into its components or cases. Rewrite using `[hM hk, zero_mul]`. Rewrite using `[hN hk, mul_zero]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem tri_inv {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {N : ℕ}
    (w u : Module.Basis (Fin N) Ω V) (h : ∀ i j, i < j → w.repr (u i) j = 0) :
    (∀ i j, i < j → u.repr (w i) j = 0) ∧ ∀ i, u.repr (w i) i = (w.repr (u i) i)⁻¹ := by
  have hM : (w.toMatrix u).BlockTriangular id := fun i j hij => h j i hij
  have hMN : w.toMatrix u * u.toMatrix w = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w u
  haveI : Invertible (w.toMatrix u) := ⟨u.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip u w, hMN⟩
  have hinv : (w.toMatrix u)⁻¹ = u.toMatrix w := Matrix.inv_eq_right_inv hMN
  have hN : (u.toMatrix w).BlockTriangular id := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨fun i j hij => hN hij, fun i => ?_⟩
  have hii := congrFun (congrFun hMN i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at hii
  · simp only [Module.Basis.toMatrix_apply] at hii
    exact eq_inv_of_mul_eq_one_right hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hM hk, zero_mul]
    · rw [hN hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Establish `hy` using `congrArg (β (w j.rev)) (w₁.sum_repr y)`. Rewrite `hy` using `[map_sum]`. Simplify using `only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.rev_inj] at hy`. Rewrite using `[← hy]`. Simplify using the standard rewrite rules.
-/
theorem repr_of_pair {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (w : Fin N → V) (w₁ : Module.Basis (Fin N) Ω V₁)
    (h : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (y : V₁) (j : Fin N) :
    w₁.repr y j = β (w j.rev) y := by
  have hy := congrArg (β (w j.rev)) (w₁.sum_repr y)
  rw [map_sum] at hy
  simp only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.rev_inj] at hy
  rw [← hy]
  simp

/- English proof (translation)
Set `e` to `LinearEquiv.ofBijective β.flip hβ`. Use `⟨(u.dualBasis.reindex Fin.revPerm).map e.symm, fun v j => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.map_apply, Module.Basis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]`. Express the relevant statement in the definitionally equal form `e (e.symm (u.dualBasis j.rev)) v = _`. Simplify using the standard rewrite rules.
-/
theorem exists_dual {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (hβ : Function.Bijective β.flip) (u : Module.Basis (Fin N) Ω V) :
    ∃ u₁ : Module.Basis (Fin N) Ω V₁, ∀ v j, β v (u₁ j) = u.repr v j.rev := by
  let e := LinearEquiv.ofBijective β.flip hβ
  refine ⟨(u.dualBasis.reindex Fin.revPerm).map e.symm, fun v j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]
  change e (e.symm (u.dualBasis j.rev)) v = _
  simp

end PositivityTheory.Xgn.A_flagframe_dual

/- English proof (translation)
Introduce `O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hD w b hE w₁ hw₁`. Use `⟨fun c hc j => ?_⟩` and prove the remaining obligations. Establish `hne : ∀ k, x ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)`. Set `m : Fin N → Ω` to `fun i => ∏ k, x ⟨k, c k⟩ ^ b i k`. Establish `hm : ∀ i, m i ≠ 0` using `fun i => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hne k)`.

Establish `hinvm : ∀ i, ∏ k, x ⟨k, c k⟩ ^ (-b i) k = (m i)⁻¹`. Introduce `i`. Simplify using `only [m, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]`. Establish `hgr` using `hE.graded c hc`. Establish `hex : ∀ i, ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = m i`.

Introduce `i`. Establish `hmem : m i ∈ degLat O x (b i) c` using `⟨1, one_mem _, (one_mul _).symm⟩`. Rewrite `hmem` using `[← hgr i]`. Conclude with `hmem`. Use `choose e he1 he2 he3 using hex`.

Establish `hP : (w.toMatrix e).BlockTriangular id` using `fun i j hij => he2 j i hij`. Establish `hdet : IsUnit (w.det e)`. Rewrite using `[Module.Basis.det_apply, Matrix.det_of_upperTriangular hP]`. Use `(Finset.prod_ne_zero_iff.mpr fun i _ => ?_).isUnit` and prove the remaining obligations. Rewrite using `[Module.Basis.toMatrix_apply, he3]`.

Conclude with `hm i`. Establish `hbasis` using `(Module.Basis.is_basis_iff_det w).mpr hdet`. Set `eb : Module.Basis (Fin N) Ω V` to `Module.Basis.mk hbasis.1 hbasis.2.ge`. Establish `heb : ∀ i, eb i = e i` using `fun i => Module.Basis.mk_apply _ _ _`. Establish `htri` using `A_flagframe_dual.tri_inv w eb (by`.

Introduce `i k hik`. Rewrite using `[heb]`. Conclude with `he2 i k hik)`. Establish `hrep : ∀ y k, w₁.repr y k = β (w k.rev) y` using `fun y k => A_flagframe_dual.repr_of_pair β w w₁ hw₁ y k`. Establish `hstep : ∀ n : ℕ, ∀ v ∈ E.lat c, (∀ k : Fin N, n ≤ k.val → w.repr v k = 0) → ∀ k, eb.repr v k ∈ chartRing O (mseg x) c`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `v _ hz k`. Establish `hv0 : v = 0` using `w.ext_elem fun i => by rw [hz i (Nat.zero_le _), map_zero]; rfl`.

Rewrite using `[hv0, map_zero]`. Conclude with `zero_mem _`. Consider the case `succ n ih`. Introduce `v hv hz k`. Distinguish the cases in `hn : n < N`.

Set `i : Fin N` to `⟨n, hn⟩`. Establish `hmem : w.repr v i ∈ degLat O x (b i) c`. Rewrite using `[← hgr i]`. Conclude with `⟨v, hv, fun j hij => hz j hij, rfl⟩`. Take `⟨α, hα, hs⟩` from `hmem`.

Establish `hv' : v - α • e i ∈ E.lat c` using `sub_mem hv (E.stable c α hα (e i) (he1 i))`. Establish `hz' : ∀ k : Fin N, n ≤ k.val → w.repr (v - α • e i) k = 0`. Introduce `k hk`. Rewrite using `[map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]`. Break down `Nat.lt_or_eq_of_le hk with hk | hk` into its components or cases.

Establish `hik : i < k` using `hk`. Rewrite using `[hz k hk, he2 i k hik, mul_zero, sub_zero]`. Establish `hik : k = i` using `Fin.ext hk.symm`. Rewrite using `[hik, hs, he3]`. Conclude with `sub_self _`.

Establish `h1` using `ih _ hv' hz' k`. Establish `h2 : eb.repr v k = eb.repr (v - α • e i) k + α * eb.repr (e i) k`. Rewrite using `[map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Use `add_mem h1 (mul_mem hα ?_)` and prove the remaining obligations. Rewrite using `[← heb, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Conclude with `ih v hv (fun k hk => absurd k.isLt (by omega)) k`. Establish `hcoef : ∀ v ∈ E.lat c, ∀ k, eb.repr v k ∈ chartRing O (mseg x) c` using `fun v hv => hstep N v hv (fun k hk => absurd k.isLt (by omega))`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w', hw', hz, rfl⟩`.

Establish `key : β (e j.rev) w' = m j.rev * w₁.repr w' j` using `by conv_lhs => rw [← w.sum_repr (e j.rev)]`. Rewrite using `[map_sum, LinearMap.sum_apply, Finset.sum_eq_single j.rev]`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul, he3, hrep w' j]`. Introduce `k _ hk`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Establish `hjk : j < k.rev` using `Fin.lt_rev_iff.mp hk`. Establish `hb : β (w k) w' = w₁.repr w' k.rev` using `by rw [hrep, Fin.rev_rev]`. Rewrite using `[hb, hz _ hjk, mul_zero]`. Rewrite using `[he2 _ _ hk, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨β (e j.rev) w', (hD.2 c hc w').1 hw' (e j.rev) (he1 _), ?_⟩` and prove the remaining obligations. Use `show w₁.repr w' j = β (e j.rev) w' * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k`. Rewrite using `[key, hinvm, mul_comm (m j.rev), mul_assoc, mul_inv_cancel₀ (hm _), mul_one]`.

Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨f, hf⟩` from `hD.1.2 (a • eb.coord j.rev)`. Establish `hfv : ∀ v, β v f = a * eb.repr v j.rev`. Introduce `v`. Use `LinearMap.congr_fun hf v` as an intermediate fact.

Simplify using `using this`. Use `⟨f, (hD.2 c hc f).2 fun v hv => ?_, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfv]`. Conclude with `mul_mem ha (hcoef v hv _)`. Rewrite using `[hrep, hfv, htri.1 _ _ (Fin.rev_lt_rev.mpr hk), mul_zero]`.

Use `show w₁.repr f j = a * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k`. Rewrite using `[hrep, hfv, htri.2, heb, he3, hinvm]`.
-/
theorem PositivityTheory.Xgn.t_flagframe_dual : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hD w b hE w₁ hw₁
  refine ⟨fun c hc j => ?_⟩
  have hne : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  let m : Fin N → Ω := fun i => ∏ k, x ⟨k, c k⟩ ^ b i k
  have hm : ∀ i, m i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hne k)
  have hinvm : ∀ i, ∏ k, x ⟨k, c k⟩ ^ (-b i) k = (m i)⁻¹ := by
    intro i
    simp only [m, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  have hgr := hE.graded c hc
  have hex : ∀ i, ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = m i := by
    intro i
    have hmem : m i ∈ degLat O x (b i) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hgr i] at hmem
    exact hmem
  choose e he1 he2 he3 using hex
  have hP : (w.toMatrix e).BlockTriangular id := fun i j hij => he2 j i hij
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular hP]
    refine (Finset.prod_ne_zero_iff.mpr fun i _ => ?_).isUnit
    rw [Module.Basis.toMatrix_apply, he3]
    exact hm i
  have hbasis := (Module.Basis.is_basis_iff_det w).mpr hdet
  let eb : Module.Basis (Fin N) Ω V := Module.Basis.mk hbasis.1 hbasis.2.ge
  have heb : ∀ i, eb i = e i := fun i => Module.Basis.mk_apply _ _ _
  have htri := A_flagframe_dual.tri_inv w eb (by
    intro i k hik
    rw [heb]
    exact he2 i k hik)
  have hrep : ∀ y k, w₁.repr y k = β (w k.rev) y :=
    fun y k => A_flagframe_dual.repr_of_pair β w w₁ hw₁ y k
  have hstep : ∀ n : ℕ, ∀ v ∈ E.lat c, (∀ k : Fin N, n ≤ k.val → w.repr v k = 0) →
      ∀ k, eb.repr v k ∈ chartRing O (mseg x) c := by
    intro n
    induction n with
    | zero =>
      intro v _ hz k
      have hv0 : v = 0 := w.ext_elem fun i => by rw [hz i (Nat.zero_le _), map_zero]; rfl
      rw [hv0, map_zero]
      exact zero_mem _
    | succ n ih =>
      intro v hv hz k
      by_cases hn : n < N
      · let i : Fin N := ⟨n, hn⟩
        have hmem : w.repr v i ∈ degLat O x (b i) c := by
          rw [← hgr i]
          exact ⟨v, hv, fun j hij => hz j hij, rfl⟩
        obtain ⟨α, hα, hs⟩ := hmem
        have hv' : v - α • e i ∈ E.lat c := sub_mem hv (E.stable c α hα (e i) (he1 i))
        have hz' : ∀ k : Fin N, n ≤ k.val → w.repr (v - α • e i) k = 0 := by
          intro k hk
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          rcases Nat.lt_or_eq_of_le hk with hk | hk
          · have hik : i < k := hk
            rw [hz k hk, he2 i k hik, mul_zero, sub_zero]
          · have hik : k = i := Fin.ext hk.symm
            rw [hik, hs, he3]
            exact sub_self _
        have h1 := ih _ hv' hz' k
        have h2 : eb.repr v k = eb.repr (v - α • e i) k + α * eb.repr (e i) k := by
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          ring
        rw [h2]
        refine add_mem h1 (mul_mem hα ?_)
        rw [← heb, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · exact ih v hv (fun k hk => absurd k.isLt (by omega)) k
  have hcoef : ∀ v ∈ E.lat c, ∀ k, eb.repr v k ∈ chartRing O (mseg x) c :=
    fun v hv => hstep N v hv (fun k hk => absurd k.isLt (by omega))
  ext s
  constructor
  · rintro ⟨w', hw', hz, rfl⟩
    have key : β (e j.rev) w' = m j.rev * w₁.repr w' j := by
      conv_lhs => rw [← w.sum_repr (e j.rev)]
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, he3, hrep w' j]
      · intro k _ hk
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rcases lt_or_gt_of_ne hk with hk | hk
        · have hjk : j < k.rev := Fin.lt_rev_iff.mp hk
          have hb : β (w k) w' = w₁.repr w' k.rev := by rw [hrep, Fin.rev_rev]
          rw [hb, hz _ hjk, mul_zero]
        · rw [he2 _ _ hk, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    refine ⟨β (e j.rev) w', (hD.2 c hc w').1 hw' (e j.rev) (he1 _), ?_⟩
    show w₁.repr w' j = β (e j.rev) w' * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
    rw [key, hinvm, mul_comm (m j.rev), mul_assoc, mul_inv_cancel₀ (hm _), mul_one]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, hf⟩ := hD.1.2 (a • eb.coord j.rev)
    have hfv : ∀ v, β v f = a * eb.repr v j.rev := by
      intro v
      have := LinearMap.congr_fun hf v
      simpa using this
    refine ⟨f, (hD.2 c hc f).2 fun v hv => ?_, fun k hk => ?_, ?_⟩
    · rw [hfv]
      exact mul_mem ha (hcoef v hv _)
    · rw [hrep, hfv, htri.1 _ _ (Fin.rev_lt_rev.mpr hk), mul_zero]
    · show w₁.repr f j = a * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
      rw [hrep, hfv, htri.2, heb, he3, hinvm]
