import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeOfGaloisStable

open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt GlobalTheory.SlopeGalois
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeDifferent

/- English proof (translation)
Establish `hz : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥`. Unfold `Formalism.HN.zl`. Use extensionality with `y`. Simplify using the standard rewrite rules. Unfold `Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope Formalism.F.rk`.

Rewrite using `[hz]`. Simplify using the standard rewrite rules.
-/
theorem muDef_bot {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    Formalism.HN.muDef b X (⊥ : Submodule (𝓞 K) V) = -Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  have hz : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := by
    unfold Formalism.HN.zl
    ext y
    simp
  unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope Formalism.F.rk
  rw [hz]
  simp

/- English proof (translation)
Unfold `slope_sq`. Use `letI : StarRing K := starRingOfComm`. Rewrite using `[dif_pos hN]`. Conclude with `muDef_bot _ _`.
-/
theorem slope_sq_bot {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} (hN : HasGram N) :
    slope_sq N (⊥ : Submodule (𝓞 K) V) = -Real.log 2 + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  unfold slope_sq
  letI : StarRing K := starRingOfComm
  rw [dif_pos hN]
  exact muDef_bot _ _

/- English proof (translation)
Establish `hdisc : (discr K').natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero K')`. Establish `hlogK : 0 ≤ Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ)`. Establish `: 0 ≤ Real.log |(discr K : ℝ)|` using `by rw [Real.log_abs]; exact Real.log_intCast_nonneg _`. Check the signs of the components of the expression. Establish `hlogK' : 0 ≤ Real.log |(discr K' : ℝ)| / (Module.finrank ℚ K' : ℝ)`.

Establish `: 0 ≤ Real.log |(discr K' : ℝ)|` using `by rw [Real.log_abs]; exact Real.log_intCast_nonneg _`. Check the signs of the components of the expression. Distinguish the cases in `h0 : M = ⊥`. Establish `hL0 : L = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Establish `h1 : ι x ∈ M` using `hιM x hx`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hne`.

Establish `h2 : LinearIndependent K (fun _ : Fin 1 => x)` using `linearIndependent_unique_iff.2 fun h => hne h`. Conclude with `(hli 1 _ h2).ne_zero 0 h1`. Rewrite using `[h0, hL0, slope_sq_bot hGr, slope_sq_bot hGr']`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨⟨n, ⟨b, X⟩, hG⟩⟩` from `hGr`.

Take `⟨⟨n', ⟨b', X'⟩, hG'⟩⟩` from `hGr'`. Establish `hsM : (M : Set V') ⊆ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V))`. Introduce `x hx`. Establish `hne : differentIdeal ℤ (𝓞 K') ≠ ⊥` using `fun h => hdisc (by`. Rewrite using `[← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])`.

Take `⟨δ, hδ, hδ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `h1` using `hDiff δ hδ x hx`. Establish `h2 : δ • x ∈ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V))`. Establish `h3 : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≤ (Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V))).restrictScalars (𝓞 K')` using `Submodule.span_le.2 (fun y hy => Submodule.subset_span (Set.image_mono Submodule.subset_span hy))`. Conclude with `h3 h1`.

Establish `hδK : (δ : K') ≠ 0` using `fun h => hδ0 (RingOfIntegers.coe_eq_zero_iff.1 h)`. Establish `h4 : x = (δ : K')⁻¹ • (δ : K') • x` using `by rw [smul_smul, inv_mul_cancel₀ hδK, one_smul]`. Rewrite using `[h4]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h5 : (δ : K') • x = δ • x` using `algebraMap_smul K' δ x`.

Rewrite using `[h5]`. Conclude with `h2`. Use `letI : StarRing K := starRingOfComm`. Use `letI : StarRing K' := starRingOfComm`. Use `haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'`.

Use `haveI : Module.Finite K V := Module.Finite.of_basis b`. Use `haveI : Module.Finite K' V' := Module.Finite.of_basis b'`. Use `haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'`. Use `letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))`. Use `haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩`.

Set `l : L →ₗ[𝓞 K] V'` to `{ toFun := fun x => ι x map_add' := fun x y => by simp map_smul' := fun a x => by show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x`. Rewrite using `[← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]`. Use `rfl }`. Establish `hr : Set.range l = ι '' (L : Set V)`. Use extensionality with `y`.

Simplify using `[l]`. Establish `hL : L.FG` using `by haveI : Module.Finite (𝓞 K') M := Module.Finite.iff_fg.2 hM haveI : Module.Finite (𝓞 K) M := Module.Finite.trans (𝓞 K') M`. Set `l' : L →ₗ[𝓞 K] M` to `{ toFun := fun x => ⟨l x, hιM x x.2⟩ map_add' := fun x y => Subtype.ext (l.map_add x y) map_smul' := fun a x => Subtype.ext (l.map_smul a x) }`. Use `Module.Finite.iff_fg.1 (Module.Finite.of_injective l' ((injective_iff_map_eq_zero _).2 fun x hx => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h1 : LinearIndependent K (fun _ : Fin 1 => (x : V))` using `linearIndependent_unique_iff.2 fun h => hne (Subtype.ext h)`. Conclude with `(hli 1 _ h1).ne_zero 0 (congrArg Subtype.val hx)`. Use `set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'`. Establish `hL'M : L' ≤ M` using `Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hιM x hx)`. Take `⟨e, heL, hsp, he⟩` from `Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)`.

Establish `hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V))` using `rfl`. Generalize the expression as in `finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj`. Establish `he'` using `hli j e he`. Establish `hspM : Submodule.span K' (M : Set V') = Submodule.span K' (Set.range fun k => ι (e k))`. Use `le_antisymm (Submodule.span_le.2 (hsM.trans (Submodule.span_le.2 ?_))) (Submodule.span_mono ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ hx)`. Rewrite using `[map_sum]`. Conclude with `Submodule.sum_mem _ fun k _ => by`. Rewrite using `[map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hιM _ (heL k)`. Establish `hj' : Formalism.HN.rkK M = j`. Rewrite using `[Formalism.HN.rkK, hspM, finrank_span_eq_card he', Fintype.card_fin]`.

Establish `hj0` using `Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b' M h0`. Rewrite `hj0` using `[hj']`. Establish `hD : differentIdeal ℤ (𝓞 K') • M ≤ L'` using `Submodule.smul_le.2 fun δ hδ x hx => hDiff δ hδ x hx`. Establish `hdisc : (discr K').natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero K')`. Establish `hDi` using `Formalism.HN.DualPolygon.twist_index M hM (differentIdeal ℤ (𝓞 K')) fun h => hdisc (by`.

Rewrite using `[← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])`. Rewrite `hDi` using `[absNorm_differentIdeal K' (𝓞 K'), show finrank K' (Submodule.span K' (M : Set V')) = j from hj']`. Establish `hMi : L'.toAddSubgroup.relIndex M.toAddSubgroup ≤ (discr K').natAbs ^ j`. Rewrite using `[← hDi]`. Conclude with `AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).2 hD) (by rw [hDi]; exact pow_ne_zero _ hdisc)`.

Take `⟨i1, g1, m1⟩` from `rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj`. Establish `hFL' : Submodule.span (𝓞 K') (Set.range fun k => ι (e k)) ≤ L'` using `Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)`. Take `⟨i2, g2, m2⟩` from `rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' M hM (hFL'.trans hL'M) hj'`. Set `eL : Fin j → L` to `fun k => ⟨e k, heL k⟩`. Establish `hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup`.

Establish `: Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Use extensionality with `x`. Rewrite using `[this]`.

Conclude with `⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩`. Establish `hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))`. Rewrite using `[AddSubgroup.relIndex, hsub]`. Both sides reduce to the same expression. Rewrite `i1`, `m1` using `[hidx]`.

Use `haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1`. Establish `hidx'` using `relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K')) (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K) (fun x hx => by`. Establish `h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0`. Use `congrArg Subtype.val hx` as an intermediate fact. Rewrite `this`, the goal using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `this`. Conclude with `Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))`. Use the proof step `(fun x => by`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `(Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)`.

Rewrite `hidx'` using `[card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr]`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hFL') ((Submodule.toAddSubgroup_le _ _).2 hL'M)`. Rewrite `hmul` using `[show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _ from hidx']`. Establish `hlog : Real.log ((Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≤ finrank K K' * Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))) + j * Real.log |(discr K' : ℝ)|`. Rewrite using `[← Real.log_pow, ← Real.log_pow, ← Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 i1)) (pow_ne_zero _ (abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero K')))), ← Int.cast_abs, ← Nat.cast_natAbs]`.

Use `Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero i2) ?_` and prove the remaining obligations. Rewrite using `[← hmul]`. Conclude with `Nat.mul_le_mul_left _ hMi` after adjusting the coercions. Establish `hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤ ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re` using `Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)`. Rewrite `hs` using `[sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re]`.

Establish `hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K`. Simplify `sum_comap K K' fun _ => 1` using `[Formalism.HN.nPl]`. Establish `hf' : (0 : ℝ) < Formalism.HN.nPl K'` using `lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm`. Establish `hn : (finrank ℚ K' : ℝ) = 2 * Formalism.HN.nPl K'`. Simplify `sum_mk K' fun _ => 1` using `[Formalism.HN.nPl, Embeddings.card]`.

Establish `hjp : (0 : ℝ) < j` using `by exact_mod_cast Nat.pos_of_ne_zero hj0`. Rewrite using `[slope_sq_eq hG hL, slope_sq_eq hG' hM]`. Use `le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp` and prove the remaining obligations. Establish `m4` using `congrArg ((finrank K K' : ℝ) * ·) m1`. Establish `h5 : (Formalism.HN.nPl K' : ℝ) * (j * (2 * (Real.log |(discr K' : ℝ)| / finrank ℚ K'))) = j * Real.log |(discr K' : ℝ)|`.

Rewrite using `[hn]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_sub, mul_sub, h5, m2, hf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_sq_sub_le_of_different_smul {K K' V V' : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
    (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V)
    (M : Submodule (𝓞 K') V') (hGr : HasGram N) (hGr' : HasGram N')
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    (hM : M.FG) (hN : ∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) (hιM : ∀ x ∈ L, ι x ∈ M)
    (hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 K'), ∀ g ∈ M, δ • g ∈ Submodule.span (𝓞 K') (ι '' (L : Set V))) :
    slope_sq N' M - 2 * (Real.log |(discr K' : ℝ)| / Module.finrank ℚ K') ≤ slope_sq N L := by
  have hdisc : (discr K').natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K')
  have hlogK : 0 ≤ Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
    have : 0 ≤ Real.log |(discr K : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
    positivity
  have hlogK' : 0 ≤ Real.log |(discr K' : ℝ)| / (Module.finrank ℚ K' : ℝ) := by
    have : 0 ≤ Real.log |(discr K' : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
    positivity
  by_cases h0 : M = ⊥
  · have hL0 : L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : ι x ∈ M := hιM x hx
      rw [h0, Submodule.mem_bot] at h1
      rw [Submodule.mem_bot]
      by_contra hne
      have h2 : LinearIndependent K (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 fun h => hne h
      exact (hli 1 _ h2).ne_zero 0 h1
    rw [h0, hL0, slope_sq_bot hGr, slope_sq_bot hGr']
    linarith
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hGr
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hGr'
  have hsM : (M : Set V') ⊆ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V)) := by
    intro x hx
    have hne : differentIdeal ℤ (𝓞 K') ≠ ⊥ := fun h => hdisc (by
      rw [← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])
    obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hDiff δ hδ x hx
    have h2 : δ • x ∈ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V)) := by
      have h3 : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≤
          (Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V))).restrictScalars (𝓞 K') :=
        Submodule.span_le.2 (fun y hy => Submodule.subset_span (Set.image_mono Submodule.subset_span hy))
      exact h3 h1
    have hδK : (δ : K') ≠ 0 := fun h => hδ0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    have h4 : x = (δ : K')⁻¹ • (δ : K') • x := by rw [smul_smul, inv_mul_cancel₀ hδK, one_smul]
    rw [h4]
    refine Submodule.smul_mem _ _ ?_
    have h5 : (δ : K') • x = δ • x := algebraMap_smul K' δ x
    rw [h5]
    exact h2
  classical
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K V := Module.Finite.of_basis b
  haveI : Module.Finite K' V' := Module.Finite.of_basis b'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))
  haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let l : L →ₗ[𝓞 K] V' :=
    { toFun := fun x => ι x
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x
        rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
        rfl }
  have hr : Set.range l = ι '' (L : Set V) := by
    ext y; simp [l]
  have hL : L.FG := by
    haveI : Module.Finite (𝓞 K') M := Module.Finite.iff_fg.2 hM
    haveI : Module.Finite (𝓞 K) M := Module.Finite.trans (𝓞 K') M
    let l' : L →ₗ[𝓞 K] M :=
      { toFun := fun x => ⟨l x, hιM x x.2⟩
        map_add' := fun x y => Subtype.ext (l.map_add x y)
        map_smul' := fun a x => Subtype.ext (l.map_smul a x) }
    refine Module.Finite.iff_fg.1 (Module.Finite.of_injective l' ((injective_iff_map_eq_zero _).2 fun x hx => ?_))
    by_contra hne
    have h1 : LinearIndependent K (fun _ : Fin 1 => (x : V)) :=
      linearIndependent_unique_iff.2 fun h => hne (Subtype.ext h)
    exact (hli 1 _ h1).ne_zero 0 (congrArg Subtype.val hx)
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'
  have hL'M : L' ≤ M := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hιM x hx)
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V)) := rfl
  generalize finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  have he' := hli j e he
  have hspM : Submodule.span K' (M : Set V') = Submodule.span K' (Set.range fun k => ι (e k)) := by
    refine le_antisymm (Submodule.span_le.2 (hsM.trans (Submodule.span_le.2 ?_))) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ hx)
      rw [map_sum]
      exact Submodule.sum_mem _ fun k _ => by
        rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rintro _ ⟨k, rfl⟩; exact hιM _ (heL k)
  have hj' : Formalism.HN.rkK M = j := by
    rw [Formalism.HN.rkK, hspM, finrank_span_eq_card he', Fintype.card_fin]
  have hj0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b' M h0
  rw [hj'] at hj0
  have hD : differentIdeal ℤ (𝓞 K') • M ≤ L' := Submodule.smul_le.2 fun δ hδ x hx => hDiff δ hδ x hx
  have hdisc : (discr K').natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K')
  have hDi := Formalism.HN.DualPolygon.twist_index M hM (differentIdeal ℤ (𝓞 K')) fun h => hdisc (by
    rw [← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])
  rw [absNorm_differentIdeal K' (𝓞 K'), show finrank K' (Submodule.span K' (M : Set V')) = j from hj'] at hDi
  have hMi : L'.toAddSubgroup.relIndex M.toAddSubgroup ≤ (discr K').natAbs ^ j := by
    rw [← hDi]
    exact AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).2 hD)
      (by rw [hDi]; exact pow_ne_zero _ hdisc)
  obtain ⟨i1, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hFL' : Submodule.span (𝓞 K') (Set.range fun k => ι (e k)) ≤ L' :=
    Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)
  obtain ⟨i2, g2, m2⟩ := rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' M hM (hFL'.trans hL'M) hj'
  let eL : Fin j → L := fun k => ⟨e k, heL k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  rw [hidx] at i1 m1
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  have hidx' := relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr] at hidx'
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hFL')
    ((Submodule.toAddSubgroup_le _ _).2 hL'M)
  rw [show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _
    from hidx'] at hmul
  have hlog : Real.log ((Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex
      M.toAddSubgroup : ℝ) ≤ finrank K K' * Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))) +
        j * Real.log |(discr K' : ℝ)| := by
    rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 i1))
      (pow_ne_zero _ (abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero K')))), ← Int.cast_abs, ← Nat.cast_natAbs]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero i2) ?_
    rw [← hmul]
    exact_mod_cast Nat.mul_le_mul_left _ hMi
  have hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re :=
    Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)
  rw [sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re] at hs
  have hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K := by
    simpa [Formalism.HN.nPl] using sum_comap K K' fun _ => 1
  have hf' : (0 : ℝ) < Formalism.HN.nPl K' := lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm
  have hn : (finrank ℚ K' : ℝ) = 2 * Formalism.HN.nPl K' := by
    simpa [Formalism.HN.nPl, Embeddings.card] using sum_mk K' fun _ => 1
  have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
  rw [slope_sq_eq hG hL, slope_sq_eq hG' hM]
  refine le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp
  have m4 := congrArg ((finrank K K' : ℝ) * ·) m1
  have h5 : (Formalism.HN.nPl K' : ℝ) * (j * (2 * (Real.log |(discr K' : ℝ)| / finrank ℚ K'))) =
      j * Real.log |(discr K' : ℝ)| := by
    rw [hn]; field_simp
  rw [mul_sub, mul_sub, h5, m2, hf]
  linarith

end GlobalTheory.SlopeDifferent
