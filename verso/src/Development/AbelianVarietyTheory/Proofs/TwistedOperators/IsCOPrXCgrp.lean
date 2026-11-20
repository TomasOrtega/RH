import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.PrCompactOpen

/- English proof (translation)
Establish `h1 : f 1 = 1`. Establish `e : f 1 * f 1 = f 1 * 1` using `by rw [mul_one, ← hm, one_mul]`. Conclude with `mul_left_cancel₀ (hp 1).ne' e`. Establish `hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m`. Introduce `x m`.

Proceed by induction on `m with`. Consider the case `zero => simp [h1]`. Consider the case `succ m ih => rw [pow_succ, hm, ih, pow_succ]`. Take `⟨B, hB⟩` from `(hP.image hc).bddAbove`. Establish `hle : ∀ x ∈ P, f x ≤ 1`.

Introduce `x hx`. Assume the negation of the conclusion as `hlt`. Establish `hlt` using `not_le.mp hlt`. Take `⟨m, hm'⟩` from `((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists`. Establish `: f (x ^ m) ≤ B` using `hB ⟨x ^ m, P.pow_mem hx m, rfl⟩`.

Rewrite `this` using `[hpow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod : f g * f g⁻¹ = 1` using `by rw [← hm, mul_inv_cancel, h1]`. Establish `a` using `hle g hg`. Establish `b` using `hle g⁻¹ (P.inv_mem hg)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]`.
-/
theorem eq_one_of_isCompact {G : Type} [Group G] [TopologicalSpace G] (f : G → ℝ)
    (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x * f y) (hp : ∀ x, 0 < f x)
    {P : Subgroup G} (hP : IsCompact (P : Set G)) {g : G} (hg : g ∈ P) : f g = 1 := by
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hm, one_mul]
    exact mul_left_cancel₀ (hp 1).ne' e
  have hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih, pow_succ]
  obtain ⟨B, hB⟩ := (hP.image hc).bddAbove
  have hle : ∀ x ∈ P, f x ≤ 1 := by
    intro x hx
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨m, hm'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists
    have : f (x ^ m) ≤ B := hB ⟨x ^ m, P.pow_mem hx m, rfl⟩
    rw [hpow] at this
    linarith
  have hprod : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, h1]
  have a := hle g hg
  have b := hle g⁻¹ (P.inv_mem hg)
  nlinarith [mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]

/- English proof (translation)
Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Establish `key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) → IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)}`. Introduce `F hF`. Establish `e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r → (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s}`. Use extensionality with `x`.

Simplify using `only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))`. Establish `hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k))`. Establish `e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) = {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹}`.

Use extensionality with `x`. Conclude with `GlobalTheory.RootEx.VolN.mem_R_iff`. Rewrite using `[e]`. Conclude with `(key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)`. Establish `hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨h⁻¹ * x * h, hx, by group⟩`. Introduce and unpack `⟨y, hy, rfl⟩ show h⁻¹ * (h * y * h⁻¹) * h ∈ J`.

Establish `e : h⁻¹ * (h * y * h⁻¹) * h = y` using `by group`. Rewrite using `[e]`. Conclude with `hy`. Establish `hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) = {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _)`. Use extensionality with `x`.

Conclude with `GlobalTheory.StepData.mem_Cgrp.trans and_comm`. Establish `hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k))`. Rewrite using `[hCset, hconj]`. Conclude with `(hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl`. Establish `hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k))`.

Apply `Subgroup.isOpen_of_mem_nhds` to reduce the goal to its premises. Establish `hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J}` using `hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)`. Establish `h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J}` using `by show h⁻¹ * embX c 1 * h ∈ J`. Rewrite using `[map_one, mul_one, inv_mul_cancel]`. Conclude with `J.one_mem`.

Use `Filter.mem_of_superset (hV.mem_nhds h1V) ?_` and prove the remaining obligations. Introduce `g hg`. Use `GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)`.

Rewrite using `[one_mul]`. Conclude with `hg`. Establish `hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A → Continuous (fun r => (A r).toBlocks₁₁)` using `fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _`. Establish `hΦ : Continuous (fun r : GL (n ⊕ Fin c) k => ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁, MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁))` using `(hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))`. Establish `himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) = (fun r : GL (n ⊕ Fin c) k => ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁, MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) '' (Cgrp J h : Set (GL (n ⊕ Fin …`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Take `⟨u, hu, huC⟩` from `GlobalTheory.StepData.mem_prX.mp hg`. Use `⟨u * embX c g, huC, ?_⟩` and prove the remaining obligations.

Establish `hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹` using `by rw [_root_.mul_inv_rev, map_inv]`. Simplify using `only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu), Units.embedProduct_apply]`. Introduce and unpack `⟨r, hr, rfl⟩`. Take `⟨hrR, -⟩` from `GlobalTheory.StepData.mem_Cgrp.mp hr`. Take `⟨x, u, hu, rfl⟩` from `GlobalTheory.RootEx.Radical.exists_of_mem_R hrR`.

Use `⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹, GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩` and prove the remaining obligations. Establish `hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹` using `by rw [_root_.mul_inv_rev, map_inv]`. Simplify using `only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu), Units.embedProduct_apply]`. Establish `hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k))`. Rewrite using `[Units.isEmbedding_embedProduct.isCompact_iff, himg]`.

Conclude with `hCc.image hΦ`. Use `⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g)`. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) = fun g : GL n k => (g : Matrix n n k).det`.

Use function extensionality and compare the values at `g`. Conclude with `Matrix.GeneralLinearGroup.val_det_apply g`. Rewrite using `[e]`. Conclude with `Units.continuous_val.matrix_det`. Establish `e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) = fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det`.

Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[e]`. Conclude with `Units.continuous_coe_inv.matrix_det`. Establish `h1` using `eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g)) ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet) (fun x y => by`.

Simplify using `only [map_mul]`. Conclude with `GlobalTheory.SplitWeil.nabs_mul k _ _)`. Use the proof step `(fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg`. Use `⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩` and prove the remaining obligations. Use `show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1`.

Rewrite using `[h1, _root_.one_zpow]`.
-/
theorem isCO_prX_Cgrp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : IsCO J) (h : GL (n ⊕ Fin c) k) :
    IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h),
      valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  have key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) →
      IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} := by
    intro F hF
    have e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r →
        (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]
    rw [e]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const
      (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))
  have hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k)) := by
    have e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) =
        {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹} := by
      ext x
      exact GlobalTheory.RootEx.VolN.mem_R_iff
    rw [e]
    exact (key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)
  have hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show h⁻¹ * (h * y * h⁻¹) * h ∈ J
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e]
      exact hy
  have hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _) := by
    ext x
    exact GlobalTheory.StepData.mem_Cgrp.trans and_comm
  have hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    rw [hCset, hconj]
    exact (hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl
  have hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k)) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J} :=
      hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)
    have h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J} := by
      show h⁻¹ * embX c 1 * h ∈ J
      rw [map_one, mul_one, inv_mul_cancel]
      exact J.one_mem
    refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
    intro g hg
    refine GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩
    · rw [one_mul]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · rw [one_mul]
      exact hg
  have hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A →
      Continuous (fun r => (A r).toBlocks₁₁) :=
    fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _
  have hΦ : Continuous (fun r : GL (n ⊕ Fin c) k =>
      ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
        MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) :=
    (hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))
  have himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) =
      (fun r : GL (n ⊕ Fin c) k =>
        ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
          MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) ''
        (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, huC⟩ := GlobalTheory.StepData.mem_prX.mp hg
      refine ⟨u * embX c g, huC, ?_⟩
      have hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, -⟩ := GlobalTheory.StepData.mem_Cgrp.mp hr
      obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hrR
      refine ⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹,
        GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩
      have hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
  have hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k)) := by
    rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
    exact hCc.image hΦ
  refine ⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩
  have hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) =
          fun g : GL n k => (g : Matrix n n k).det := by
        funext g
        exact Matrix.GeneralLinearGroup.val_det_apply g
      rw [e]
      exact Units.continuous_val.matrix_det
    · have e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
          fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [e]
      exact Units.continuous_coe_inv.matrix_det
  have h1 := eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g))
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet)
    (fun x y => by
      simp only [map_mul]
      exact GlobalTheory.SplitWeil.nabs_mul k _ _)
    (fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg
  refine ⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩
  show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1
  rw [h1, _root_.one_zpow]

end GlobalTheory.PrCompactOpen
