import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank

/- English proof (translation)
Introduce `H V _ _ _ ρ θ h`. Establish `hq : ∀ (g : H) (t : V), (twRel ρ θ).mkQ (ρ g t) = (θ g : ℂ) • (twRel ρ θ).mkQ t`. Introduce `g t`. Rewrite using `[← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.subset_span ⟨g, t, rfl⟩`.

Establish `hspan : ∀ t w : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) → ∃ s : ℂ, (twRel ρ θ).mkQ w = s • (twRel ρ θ).mkQ t`. Introduce `t w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`.

Conclude with `⟨θ g, hq g t⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨u, hu⟩` from `hy`.

Conclude with `⟨s + u, by rw [map_add, hs, hu, add_smul]⟩`. Consider the case `smul c x _ hx`. Take `⟨s, hs⟩` from `hx`. Conclude with `⟨c * s, by rw [map_smul, hs, mul_smul]⟩`. Distinguish the cases in `h0 : ∀ w : V, (twRel ρ θ).mkQ w = 0`.

Use `haveI : Subsingleton (V ⧸ twRel ρ θ) := ⟨fun p q => by`. Take `⟨w, rfl⟩` from `(twRel ρ θ).mkQ_surjective p`. Take `⟨w', rfl⟩` from `(twRel ρ θ).mkQ_surjective q`. Rewrite using `[h0, h0]⟩`. Use `infer_instance`.

Use `push Not at h0`. Take `⟨w₀, hw₀⟩` from `h0`. Use `⟨⟨{(twRel ρ θ).mkQ w₀}, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `z _`.

Take `⟨w, rfl⟩` from `(twRel ρ θ).mkQ_surjective z`. Take `⟨t, ht, ht'⟩` from `h w w₀`. Take `⟨s, hs⟩` from `hspan t w ht`. Take `⟨s₀, hs₀⟩` from `hspan t w₀ ht'`. Establish `hne : s₀ ≠ 0` using `fun e => hw₀ (by rw [hs₀, e, zero_smul])`.

Establish `: (twRel ρ θ).mkQ w = (s / s₀) • (twRel ρ θ).mkQ w₀`. Rewrite using `[hs, hs₀, smul_smul, div_mul_cancel₀ _ hne]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`.
-/
theorem finite_coinv_of_common_generator : ∀ (H V : Type) [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (θ : H →* ℂˣ), (∀ w w' : V, ∃ t : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) ∧ w' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t)) → Module.Finite ℂ (V ⧸ twRel ρ θ) := by
  intro H V _ _ _ ρ θ h
  have hq : ∀ (g : H) (t : V), (twRel ρ θ).mkQ (ρ g t) = (θ g : ℂ) • (twRel ρ θ).mkQ t := by
    intro g t
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨g, t, rfl⟩
  have hspan : ∀ t w : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) →
      ∃ s : ℂ, (twRel ρ θ).mkQ w = s • (twRel ρ θ).mkQ t := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨θ g, hq g t⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      exact ⟨s + u, by rw [map_add, hs, hu, add_smul]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨c * s, by rw [map_smul, hs, mul_smul]⟩
  by_cases h0 : ∀ w : V, (twRel ρ θ).mkQ w = 0
  · haveI : Subsingleton (V ⧸ twRel ρ θ) := ⟨fun p q => by
      obtain ⟨w, rfl⟩ := (twRel ρ θ).mkQ_surjective p
      obtain ⟨w', rfl⟩ := (twRel ρ θ).mkQ_surjective q
      rw [h0, h0]⟩
    infer_instance
  · push Not at h0
    obtain ⟨w₀, hw₀⟩ := h0
    refine ⟨⟨{(twRel ρ θ).mkQ w₀}, ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := (twRel ρ θ).mkQ_surjective z
    obtain ⟨t, ht, ht'⟩ := h w w₀
    obtain ⟨s, hs⟩ := hspan t w ht
    obtain ⟨s₀, hs₀⟩ := hspan t w₀ ht'
    have hne : s₀ ≠ 0 := fun e => hw₀ (by rw [hs₀, e, zero_smul])
    have : (twRel ρ θ).mkQ w = (s / s₀) • (twRel ρ θ).mkQ w₀ := by
      rw [hs, hs₀, smul_smul, div_mul_cancel₀ _ hne]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/- English proof (translation)
Introduce `H X _ _ _ _ _ _ f`. Establish `hc : IsCompact (tsupport f.1)` using `f.2.2`. Establish `hl : IsLocallyConstant fun p : H × X => f.1 (p.1 • p.2) - f.1 p.2` using `(f.2.1.comp_continuous (continuous_fst.smul continuous_snd)).comp₂ (f.2.1.comp_continuous continuous_snd) (· - ·)`. Establish `hS : IsOpen {p : H × X | f.1 (p.1 • p.2) = f.1 p.2}`. Use `hl.isOpen_fiber 0` as an intermediate fact.

Simplify `this` using `only [sub_eq_zero]`. Establish `hsub : ({1} : Set H) ×ˢ tsupport f.1 ⊆ {p : H × X | f.1 (p.1 • p.2) = f.1 p.2}`. Introduce and unpack `⟨g, x⟩ ⟨hg, -⟩`. Establish `: g = 1` using `hg`. Simplify using `[this]`.

Take `⟨U, W, hU, hW, h1, hCW, hUW⟩` from `generalized_tube_lemma isCompact_singleton hc hS hsub`. Establish `h1U : (1 : H) ∈ U` using `h1 rfl`. Use `⟨U ∩ (fun g : H => g⁻¹) ⁻¹' U, Filter.inter_mem (hU.mem_nhds h1U) (continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds h1U)), ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hg'⟩ x`. Distinguish the cases in `hx : x ∈ W`.

Conclude with `hUW (show (g, x) ∈ U ×ˢ W from ⟨hg, hx⟩)`. Distinguish the cases in `hgx : g • x ∈ W`. Establish `h2 : f.1 (g⁻¹ • g • x) = f.1 (g • x)` using `hUW (show (g⁻¹, g • x) ∈ U ×ˢ W from ⟨hg', hgx⟩)`. Rewrite `h2` using `[inv_smul_smul]`. Conclude with `h2.symm`.

Rewrite using `[image_eq_zero_of_notMem_tsupport fun h => hgx (hCW h), image_eq_zero_of_notMem_tsupport fun h => hx (hCW h)]`.
-/
theorem exists_nhds_smul_invariant : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X] (f : SB X), ∃ U ∈ 𝓝 (1 : H), ∀ g ∈ U, ∀ x : X, f.1 (g • x) = f.1 x := by
  intro H X _ _ _ _ _ _ f
  have hc : IsCompact (tsupport f.1) := f.2.2
  have hl : IsLocallyConstant fun p : H × X => f.1 (p.1 • p.2) - f.1 p.2 :=
    (f.2.1.comp_continuous (continuous_fst.smul continuous_snd)).comp₂
      (f.2.1.comp_continuous continuous_snd) (· - ·)
  have hS : IsOpen {p : H × X | f.1 (p.1 • p.2) = f.1 p.2} := by
    have := hl.isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hsub : ({1} : Set H) ×ˢ tsupport f.1 ⊆ {p : H × X | f.1 (p.1 • p.2) = f.1 p.2} := by
    rintro ⟨g, x⟩ ⟨hg, -⟩
    have : g = 1 := hg
    simp [this]
  obtain ⟨U, W, hU, hW, h1, hCW, hUW⟩ := generalized_tube_lemma isCompact_singleton hc hS hsub
  have h1U : (1 : H) ∈ U := h1 rfl
  refine ⟨U ∩ (fun g : H => g⁻¹) ⁻¹' U, Filter.inter_mem (hU.mem_nhds h1U)
    (continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds h1U)), ?_⟩
  rintro g ⟨hg, hg'⟩ x
  by_cases hx : x ∈ W
  · exact hUW (show (g, x) ∈ U ×ˢ W from ⟨hg, hx⟩)
  by_cases hgx : g • x ∈ W
  · have h2 : f.1 (g⁻¹ • g • x) = f.1 (g • x) := hUW (show (g⁻¹, g • x) ∈ U ×ˢ W from ⟨hg', hgx⟩)
    rw [inv_smul_smul] at h2
    exact h2.symm
  · rw [image_eq_zero_of_notMem_tsupport fun h => hgx (hCW h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hCW h)]

/- English proof (translation)
Introduce `H _ _ _ _ _ K hKc hKo U hU`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc`. Establish `hVo : IsOpen ((Subtype.val : K → H) ⁻¹' interior U)` using `isOpen_interior.preimage continuous_subtype_val`. Establish `h1 : (1 : K) ∈ (Subtype.val : K → H) ⁻¹' interior U` using `mem_interior_iff_mem_nhds.2 hU`. Take `⟨M, hM⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1`.

Use `⟨M.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hKo.isOpenEmbedding_subtypeVal.isOpenMap _ M.isOpen'`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `interior_subset (hM hm)`. Introduce and unpack `κ hκ _ ⟨m, hm, rfl⟩`.

Conclude with `⟨⟨κ, hκ⟩ * m * (⟨κ, hκ⟩ : K)⁻¹, M.isNormal'.conj_mem m hm _, by simp⟩`.
-/
theorem exists_level_subset : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [TotallyDisconnectedSpace H] (K : Subgroup H), IsCompact (K : Set H) → IsOpen (K : Set H) → ∀ U ∈ 𝓝 (1 : H), ∃ N : Subgroup H, IsOpen (N : Set H) ∧ N ≤ K ∧ (N : Set H) ⊆ U ∧ ∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N := by
  intro H _ _ _ _ _ K hKc hKo U hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hVo : IsOpen ((Subtype.val : K → H) ⁻¹' interior U) := isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : K) ∈ (Subtype.val : K → H) ⁻¹' interior U := mem_interior_iff_mem_nhds.2 hU
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1
  refine ⟨M.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ M.isOpen'
  · rintro _ ⟨m, hm, rfl⟩
    exact interior_subset (hM hm)
  · rintro κ hκ _ ⟨m, hm, rfl⟩
    exact ⟨⟨κ, hκ⟩ * m * (⟨κ, hκ⟩ : K)⁻¹, M.isNormal'.conj_mem m hm _, by simp⟩

/- English proof (translation)
Use `⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.mono f.2.2 fun x hx => ?_⟩` and prove the remaining obligations. Establish `hf` using `(IsLocallyConstant.iff_eventually_eq _).1 f.2.1 x`. Distinguish the cases in `hx : x ∈ Y`. Use `filter_upwards [hY.isOpen.mem_nhds hx, hf] with y hy e`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]`.

Use `filter_upwards [hY.compl.isOpen.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Distinguish the cases in `h : x ∈ Y`. Rewrite `hx` using `[Function.mem_support, Set.indicator_of_mem h]`. Conclude with `hx`.

Conclude with `absurd (Set.indicator_of_notMem h _) hx`.
-/
theorem indicator_mem_SB_of_isClopen {X : Type} [TopologicalSpace X] {Y : Set X} (hY : IsClopen Y) (f : SB X) :
    Y.indicator f.1 ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.mono f.2.2 fun x hx => ?_⟩
  · have hf := (IsLocallyConstant.iff_eventually_eq _).1 f.2.1 x
    by_cases hx : x ∈ Y
    · filter_upwards [hY.isOpen.mem_nhds hx, hf] with y hy e
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
    · filter_upwards [hY.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · by_cases h : x ∈ Y
    · rw [Function.mem_support, Set.indicator_of_mem h] at hx
      exact hx
    · exact absurd (Set.indicator_of_notMem h _) hx

/- English proof (translation)
Introduce `X _ Y hY f`. Use `⟨⟨_, indicator_mem_SB_of_isClopen hY f⟩, ⟨_, indicator_mem_SB_of_isClopen hY.compl f⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun x => ?_) show f.1 x = Y.indicator f.1 x + Yᶜ.indicator f.1 x` and prove the remaining obligations. Apply the tactic sequence `by_cases h : x ∈ Y <;> simp [h]`. Introduce `x hx`.

Establish `hx' : Y.indicator f.1 x ≠ 0` using `hx`. Distinguish the cases in `h : x ∈ Y`. Conclude with `⟨h, by simpa [h] using hx'⟩`. Conclude with `absurd (Set.indicator_of_notMem h _) hx'`. Introduce `x hx`.

Establish `hx' : Yᶜ.indicator f.1 x ≠ 0` using `hx`. Distinguish the cases in `h : x ∈ Y`. Conclude with `absurd (Set.indicator_of_notMem (by simpa using h) _) hx'`. Conclude with `⟨h, by simpa [h] using hx'⟩`.
-/
theorem exists_clopen_cut : ∀ (X : Type) [TopologicalSpace X] (Y : Set X), IsClopen Y → ∀ f : SB X, ∃ f₁ f₂ : SB X, f = f₁ + f₂ ∧ (∀ x, f₁.1 x ≠ 0 → x ∈ Y ∧ f.1 x ≠ 0) ∧ (∀ x, f₂.1 x ≠ 0 → x ∉ Y ∧ f.1 x ≠ 0) := by
  intro X _ Y hY f
  refine ⟨⟨_, indicator_mem_SB_of_isClopen hY f⟩, ⟨_, indicator_mem_SB_of_isClopen hY.compl f⟩, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun x => ?_)
    show f.1 x = Y.indicator f.1 x + Yᶜ.indicator f.1 x
    by_cases h : x ∈ Y <;> simp [h]
  · intro x hx
    have hx' : Y.indicator f.1 x ≠ 0 := hx
    by_cases h : x ∈ Y
    · exact ⟨h, by simpa [h] using hx'⟩
    · exact absurd (Set.indicator_of_notMem h _) hx'
  · intro x hx
    have hx' : Yᶜ.indicator f.1 x ≠ 0 := hx
    by_cases h : x ∈ Y
    · exact absurd (Set.indicator_of_notMem (by simpa using h) _) hx'
    · exact ⟨h, by simpa [h] using hx'⟩

section Matrices

variable {k a c d : Type} [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k c c d a e x hx`. Establish `hr : (x * g.val).rank = Fintype.card c`. Rewrite using `[rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 g.isUnit)]`. Conclude with `hx`. Establish `h` using `GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k c c d a e (x * g.val) hr hg`.

Establish `hu : IsUnit ((x * g.val).submatrix id fun i => e (.inl i))` using `mulVec_injective_iff_isUnit.1 fun v w hvw => sub_eq_zero.1 (h _ (by rw [mulVec_sub, hvw, sub_self]))`. Use `set u : Matrix c c k := (x * g.val).submatrix id fun i => e (.inl i) with hudef`. Establish `hud : IsUnit u.det` using `(isUnit_iff_isUnit_det _).1 hu`. Establish `hD : IsUnit (reindex e e (fromBlocks u⁻¹ 0 0 (1 : Matrix d d k))).det`. Rewrite using `[det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]`.

Conclude with `(isUnit_iff_isUnit_det _).1 (isUnit_nonsing_inv_iff.2 hu)`. Take `⟨G, hG⟩` from `(isUnit_iff_isUnit_det _).2 hD`. Use `⟨g * G, fun i s => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, hG, mul_apply_of_cols e hg]`. Break down `s with j | j` into its components or cases.

Use `congrFun (congrFun (mul_nonsing_inv u hud) i) j` as an intermediate fact. Rewrite `this` using `[mul_apply]`. Simplify `this` using `[hudef]`. Simplify using the standard rewrite rules.
-/
theorem exists_gl_mul_eq_base (e : c ⊕ d ≃ a) (x : Matrix c a k) (hx : x.rank = Fintype.card c) :
    ∃ g : GL a k, ∀ i s, (x * g.val) i (e s) = Sum.elim (fun j => (1 : Matrix c c k) i j) (fun _ => 0) s := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k c c d a e x hx
  have hr : (x * g.val).rank = Fintype.card c := by
    rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 g.isUnit)]
    exact hx
  have h := GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k c c d a e (x * g.val) hr hg
  have hu : IsUnit ((x * g.val).submatrix id fun i => e (.inl i)) :=
    mulVec_injective_iff_isUnit.1 fun v w hvw => sub_eq_zero.1 (h _ (by rw [mulVec_sub, hvw, sub_self]))
  set u : Matrix c c k := (x * g.val).submatrix id fun i => e (.inl i) with hudef
  have hud : IsUnit u.det := (isUnit_iff_isUnit_det _).1 hu
  have hD : IsUnit (reindex e e (fromBlocks u⁻¹ 0 0 (1 : Matrix d d k))).det := by
    rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]
    exact (isUnit_iff_isUnit_det _).1 (isUnit_nonsing_inv_iff.2 hu)
  obtain ⟨G, hG⟩ := (isUnit_iff_isUnit_det _).2 hD
  refine ⟨g * G, fun i s => ?_⟩
  rw [Units.val_mul, ← Matrix.mul_assoc, hG, mul_apply_of_cols e hg]
  rcases s with j | j
  · have := congrFun (congrFun (mul_nonsing_inv u hud) i) j
    rw [mul_apply] at this
    simpa [hudef] using this
  · simp

end Matrices

/- English proof (translation)
Introduce `k a c _ _ _ _ _ x y hx hy`. Establish `hle : Fintype.card c ≤ Fintype.card a` using `hx ▸ rank_le_card_width x`. Establish `e : c ⊕ Fin (Fintype.card a - Fintype.card c) ≃ a` using `Fintype.equivOfCardEq (by simp; omega)`. Take `⟨gx, hgx⟩` from `exists_gl_mul_eq_base e x hx`. Take `⟨gy, hgy⟩` from `exists_gl_mul_eq_base e y hy`.

Establish `h : x * gx.val = y * gy.val`. Use extensionality with `i l`. Take `⟨s, rfl⟩` from `e.surjective l`. Rewrite using `[hgx, hgy]`. Use `⟨gx * gy⁻¹, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Use `_ = x * (gx * gy⁻¹).val := by rw [← h, Units.val_mul, Matrix.mul_assoc]`.
-/
theorem exists_gl_eq_mul_of_rank : ∀ (k a c : Type) [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (x y : Matrix c a k), x.rank = Fintype.card c → y.rank = Fintype.card c → ∃ g : GL a k, y = x * g.val := by
  intro k a c _ _ _ _ _ x y hx hy
  have hle : Fintype.card c ≤ Fintype.card a := hx ▸ rank_le_card_width x
  have e : c ⊕ Fin (Fintype.card a - Fintype.card c) ≃ a := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨gx, hgx⟩ := exists_gl_mul_eq_base e x hx
  obtain ⟨gy, hgy⟩ := exists_gl_mul_eq_base e y hy
  have h : x * gx.val = y * gy.val := by
    ext i l
    obtain ⟨s, rfl⟩ := e.surjective l
    rw [hgx, hgy]
  refine ⟨gx * gy⁻¹, ?_⟩
  calc y = (y * gy.val) * (gy⁻¹).val := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = x * (gx * gy⁻¹).val := by rw [← h, Units.val_mul, Matrix.mul_assoc]

section Orbit

variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]

/- English proof (translation)
Establish `h : Submodule.span ℂ (Set.range fun h : H => ρ h t) ≤ (Submodule.span ℂ (Set.range fun h : H => ρ h t)).comap (ρ g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by simp [map_mul]⟩`. Conclude with `h hw`.
-/
theorem translate_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (t : V) (g : H)
    {w : V} (hw : w ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t)) :
    ρ g w ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t) := by
  have h : Submodule.span ℂ (Set.range fun h : H => ρ h t) ≤
      (Submodule.span ℂ (Set.range fun h : H => ρ h t)).comap (ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
  exact h hw

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `translate_mem_span ρ t h hv`.
-/
theorem span_translates_le {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) {t v : V}
    (hv : v ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t)) :
    Submodule.span ℂ (Set.range fun h : H => ρ h v) ≤ Submodule.span ℂ (Set.range fun h : H => ρ h t) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span ρ t h hv

abbrev orb (N : Subgroup H) (x₀ : X) : Set X := (fun n : H => n • x₀) '' (N : Set H)

def IsLevel (K N : Subgroup H) : Prop :=
  IsOpen (N : Set H) ∧ N ≤ K ∧ ∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simpa using h.1.inter h'.1, inf_le_left.trans h.2.1, fun κ hκ n hn => ⟨h.2.2 κ hκ n hn.1, h'.2.2 κ hκ n hn.2⟩⟩`.
-/
theorem IsLevel.inf {K N N' : Subgroup H} (h : IsLevel K N) (h' : IsLevel K N') : IsLevel K (N ⊓ N') :=
  ⟨by simpa using h.1.inter h'.1, inf_le_left.trans h.2.1,
    fun κ hκ n hn => ⟨h.2.2 κ hκ n hn.1, h'.2.2 κ hκ n hn.2⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, le_rfl, fun _ hκ _ hn => K.mul_mem (K.mul_mem hκ hn) (K.inv_mem hκ)⟩`.
-/
theorem isLevel_self {K : Subgroup H} (h : IsOpen (K : Set H)) : IsLevel K K :=
  ⟨h, le_rfl, fun _ hκ _ hn => K.mul_mem (K.mul_mem hκ hn) (K.inv_mem hκ)⟩

def Reached (ρ : Representation ℂ H (SB X)) (K : Subgroup H) (x₀ : X) (f : SB X) : Prop :=
  ∃ N : Subgroup H, IsLevel K N ∧ ∃ v : SB X, (∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x) ∧
    f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v)

/- English proof (translation)
Establish `hc : IsCompact (N : Set H)` using `hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hN.1) hN.2.1`. Establish `hc' : IsCompact (orb N x₀)` using `hc.image (continuous_id.smul continuous_const)`. Conclude with `⟨⟨_, GlobalTheory.SBExtend.indicator_mem_SB hc' ⟨hc'.isClosed, hopen x₀ _ hN.1⟩⟩, fun _ => rfl⟩`.
-/
theorem exists_indicator_orb [T2Space X] [ContinuousSMul H X] (hopen : ∀ x : X, IsOpenMap fun g : H => g • x)
    {K N : Subgroup H} (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (x₀ : X) :
    ∃ v : SB X, ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x := by
  have hc : IsCompact (N : Set H) :=
    hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hN.1) hN.2.1
  have hc' : IsCompact (orb N x₀) := hc.image (continuous_id.smul continuous_const)
  exact ⟨⟨_, GlobalTheory.SBExtend.indicator_mem_SB hc' ⟨hc'.isClosed, hopen x₀ _ hN.1⟩⟩, fun _ => rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, e⟩`. Use `⟨n⁻¹ * m, N.mul_mem (N.inv_mem hn) hm, ?_⟩` and prove the remaining obligations. Use `show (n⁻¹ * m) • x₀ = x`. Rewrite using `[mul_smul]`.

Establish `e' : m • x₀ = n • x` using `e`. Rewrite using `[e', inv_smul_smul]`. Introduce and unpack `⟨m, hm, e⟩`. Use `⟨n * m, N.mul_mem hn hm, ?_⟩` and prove the remaining obligations. Establish `e' : m • x₀ = x` using `e`.

Use `show (n * m) • x₀ = n • x`. Rewrite using `[mul_smul, e']`.
-/
theorem orb_smul_mem_iff {N : Subgroup H} {x₀ x : X} {n : H} (hn : n ∈ N) :
    n • x ∈ orb N x₀ ↔ x ∈ orb N x₀ := by
  constructor
  · rintro ⟨m, hm, e⟩
    refine ⟨n⁻¹ * m, N.mul_mem (N.inv_mem hn) hm, ?_⟩
    show (n⁻¹ * m) • x₀ = x
    rw [mul_smul]
    have e' : m • x₀ = n • x := e
    rw [e', inv_smul_smul]
  · rintro ⟨m, hm, e⟩
    refine ⟨n * m, N.mul_mem hn hm, ?_⟩
    have e' : m • x₀ = x := e
    show (n * m) • x₀ = n • x
    rw [mul_smul, e']

/- English proof (translation)
Introduce `H X _ _ _ _ _ ρ hρ K N hK hN hNK hnorm x₀ v f hv hinv hsupp`. Take `⟨T, hTK, hT⟩` from `hK.elim_nhds_subcover (fun κ : H => (fun n : H => κ * n) '' (N : Set H)) (fun κ _ => ((Homeomorph.mulLeft κ).isOpenMap _ hN).mem_nhds ⟨1, N.one_mem, mul_one κ⟩)`. Establish `hu : ∀ (τ : H) (x : X), (ρ τ v).1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) (τ⁻¹ • x)` using `fun τ x => by`. Rewrite using `[hρ, hv]`. Establish `key : ∀ (T : Finset H), (∀ τ ∈ T, τ ∈ K) → ∀ f : SB X, (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) → (∀ x, f.1 x ≠ 0 → ∃ τ ∈ T, τ⁻¹ • x ∈ orb N x₀) → f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v)`.

Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_ f _ hf`. Establish `: f = 0` using `Subtype.ext (funext fun x => by`.

Assume the negation of the conclusion as `h`. Take `⟨τ, hτ, -⟩` from `hf x h`. Simplify using `at hτ)`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `insert τ T _ ih`. Introduce `hTK f hfi hf`. Establish `hτ : τ ∈ K` using `hTK τ (Finset.mem_insert_self _ _)`. Establish `hst : ∀ n ∈ N, ∀ x, τ⁻¹ • n • x ∈ orb N x₀ ↔ τ⁻¹ • x ∈ orb N x₀` using `fun n hn x => by`. Establish `hm : τ⁻¹ * n * τ⁻¹⁻¹ ∈ N` using `hnorm _ (K.inv_mem hτ) n hn`.

Rewrite `hm` using `[inv_inv]`. Establish `e : τ⁻¹ • n • x = (τ⁻¹ * n * τ) • τ⁻¹ • x`. Simplify using `only [mul_smul, smul_inv_smul]`. Rewrite using `[e, orb_smul_mem_iff hm]`. Establish `hval : ∀ x, τ⁻¹ • x ∈ orb N x₀ → f.1 x = f.1 (τ • x₀)`.

Introduce and unpack `x ⟨n, hn, e⟩`. Establish `e' : n • x₀ = τ⁻¹ • x` using `e`. Establish `hm : τ * n * τ⁻¹ ∈ N` using `hnorm τ hτ n hn`. Establish `e2 : x = (τ * n * τ⁻¹) • τ • x₀`. Simplify using `only [mul_smul, inv_smul_smul, e', smul_inv_smul]`.

Rewrite using `[e2, hfi _ hm]`. Establish `hu1 : ∀ x, τ⁻¹ • x ∈ orb N x₀ → (ρ τ v).1 x = 1` using `fun x hx => by`. Rewrite using `[hu, Set.indicator_of_mem hx]`. Establish `hu0 : ∀ x, τ⁻¹ • x ∉ orb N x₀ → (ρ τ v).1 x = 0` using `fun x hx => by`. Rewrite using `[hu, Set.indicator_of_notMem hx]`.

Establish `hv' : ∀ x, (f - f.1 (τ • x₀) • ρ τ v).1 x = f.1 x - f.1 (τ • x₀) * (ρ τ v).1 x` using `fun _ => rfl`. Establish `hm` using `ih (fun σ hσ => hTK σ (Finset.mem_insert_of_mem hσ)) (f - f.1 (τ • x₀) • ρ τ v) (fun n hn x => by`. Rewrite using `[hv', hv', hfi n hn x]`. Distinguish the cases in `hx : τ⁻¹ • x ∈ orb N x₀`. Rewrite using `[hu1 _ ((hst n hn x).2 hx), hu1 _ hx]`.

Rewrite using `[hu0 _ (fun h => hx ((hst n hn x).1 h)), hu0 _ hx])`. Use the proof step `(fun x hx => by`. Rewrite `hx` using `[hv']`. Distinguish the cases in `hxτ : τ⁻¹ • x ∈ orb N x₀`. Rewrite `hx` using `[hu1 _ hxτ, hval x hxτ, mul_one, sub_self]`.

Conclude with `absurd rfl hx`. Rewrite `hx` using `[hu0 _ hxτ, mul_zero, sub_zero]`. Take `⟨σ, hσ, hm⟩` from `hf x hx`. Break down `Finset.mem_insert.1 hσ with rfl | hσ` into its components or cases. Conclude with `absurd hm hxτ`.

Conclude with `⟨σ, hσ, hm⟩)`. Establish `e : f = (f - f.1 (τ • x₀) • ρ τ v) + f.1 (τ • x₀) • ρ τ v` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ hm (Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ, rfl⟩))`. Use `key T hTK f hinv fun x hx => ?_` and prove the remaining obligations.

Take `⟨κ, hκ, rfl⟩` from `hsupp x hx`. Take `⟨τ, hτ, hm⟩` from `Set.mem_iUnion₂.1 (hT hκ)`. Take `⟨n, hn, rfl⟩` from `hm`. Use `⟨τ, hτ, n, hn, ?_⟩` and prove the remaining obligations. Use `show n • x₀ = τ⁻¹ • (τ * n) • x₀`.

Rewrite using `[mul_smul, inv_smul_smul]`.
-/
theorem mem_span_translates_of_level : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] (ρ : Representation ℂ H (SB X)), (∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) → ∀ (K N : Subgroup H), IsCompact (K : Set H) → IsOpen (N : Set H) → N ≤ K → (∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N) → ∀ (x₀ : X) (v f : SB X), (∀ x, v.1 x = ((fun n : H => n • x₀) '' (N : Set H)).indicator (fun _ => (1 : ℂ)) x) → (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) → (∀ x, f.1 x ≠ 0 → x ∈ (fun κ : H => κ • x₀) '' (K : Set H)) → f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
  intro H X _ _ _ _ _ ρ hρ K N hK hN hNK hnorm x₀ v f hv hinv hsupp
  classical
  obtain ⟨T, hTK, hT⟩ := hK.elim_nhds_subcover (fun κ : H => (fun n : H => κ * n) '' (N : Set H)) (fun κ _ =>
    ((Homeomorph.mulLeft κ).isOpenMap _ hN).mem_nhds ⟨1, N.one_mem, mul_one κ⟩)
  have hu : ∀ (τ : H) (x : X), (ρ τ v).1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) (τ⁻¹ • x) := fun τ x => by
    rw [hρ, hv]
  have key : ∀ (T : Finset H), (∀ τ ∈ T, τ ∈ K) → ∀ f : SB X, (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) →
      (∀ x, f.1 x ≠ 0 → ∃ τ ∈ T, τ⁻¹ • x ∈ orb N x₀) →
      f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ f _ hf
      have : f = 0 := Subtype.ext (funext fun x => by
        by_contra h
        obtain ⟨τ, hτ, -⟩ := hf x h
        simp at hτ)
      rw [this]
      exact Submodule.zero_mem _
    | insert τ T _ ih =>
      intro hTK f hfi hf
      have hτ : τ ∈ K := hTK τ (Finset.mem_insert_self _ _)
      have hst : ∀ n ∈ N, ∀ x, τ⁻¹ • n • x ∈ orb N x₀ ↔ τ⁻¹ • x ∈ orb N x₀ := fun n hn x => by
        have hm : τ⁻¹ * n * τ⁻¹⁻¹ ∈ N := hnorm _ (K.inv_mem hτ) n hn
        rw [inv_inv] at hm
        have e : τ⁻¹ • n • x = (τ⁻¹ * n * τ) • τ⁻¹ • x := by
          simp only [mul_smul, smul_inv_smul]
        rw [e, orb_smul_mem_iff hm]
      have hval : ∀ x, τ⁻¹ • x ∈ orb N x₀ → f.1 x = f.1 (τ • x₀) := by
        rintro x ⟨n, hn, e⟩
        have e' : n • x₀ = τ⁻¹ • x := e
        have hm : τ * n * τ⁻¹ ∈ N := hnorm τ hτ n hn
        have e2 : x = (τ * n * τ⁻¹) • τ • x₀ := by
          simp only [mul_smul, inv_smul_smul, e', smul_inv_smul]
        rw [e2, hfi _ hm]
      have hu1 : ∀ x, τ⁻¹ • x ∈ orb N x₀ → (ρ τ v).1 x = 1 := fun x hx => by
        rw [hu, Set.indicator_of_mem hx]
      have hu0 : ∀ x, τ⁻¹ • x ∉ orb N x₀ → (ρ τ v).1 x = 0 := fun x hx => by
        rw [hu, Set.indicator_of_notMem hx]
      have hv' : ∀ x, (f - f.1 (τ • x₀) • ρ τ v).1 x = f.1 x - f.1 (τ • x₀) * (ρ τ v).1 x := fun _ => rfl
      have hm := ih (fun σ hσ => hTK σ (Finset.mem_insert_of_mem hσ)) (f - f.1 (τ • x₀) • ρ τ v)
        (fun n hn x => by
          rw [hv', hv', hfi n hn x]
          by_cases hx : τ⁻¹ • x ∈ orb N x₀
          · rw [hu1 _ ((hst n hn x).2 hx), hu1 _ hx]
          · rw [hu0 _ (fun h => hx ((hst n hn x).1 h)), hu0 _ hx])
        (fun x hx => by
          rw [hv'] at hx
          by_cases hxτ : τ⁻¹ • x ∈ orb N x₀
          · rw [hu1 _ hxτ, hval x hxτ, mul_one, sub_self] at hx
            exact absurd rfl hx
          · rw [hu0 _ hxτ, mul_zero, sub_zero] at hx
            obtain ⟨σ, hσ, hm⟩ := hf x hx
            rcases Finset.mem_insert.1 hσ with rfl | hσ
            · exact absurd hm hxτ
            · exact ⟨σ, hσ, hm⟩)
      have e : f = (f - f.1 (τ • x₀) • ρ τ v) + f.1 (τ • x₀) • ρ τ v := by abel
      rw [e]
      exact Submodule.add_mem _ hm (Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ, rfl⟩))
  refine key T hTK f hinv fun x hx => ?_
  obtain ⟨κ, hκ, rfl⟩ := hsupp x hx
  obtain ⟨τ, hτ, hm⟩ := Set.mem_iUnion₂.1 (hT hκ)
  obtain ⟨n, hn, rfl⟩ := hm
  refine ⟨τ, hτ, n, hn, ?_⟩
  show n • x₀ = τ⁻¹ • (τ * n) • x₀
  rw [mul_smul, inv_smul_smul]

/- English proof (translation)
Use `span_translates_le ρ (mem_span_translates_of_level H X ρ hρ K N' hK hN'.1 hN'.2.1 hN'.2.2 x₀ v' v hv' (fun n hn x => ?_) fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[hv, hv]`. Simplify using `only [Set.indicator, orb_smul_mem_iff (hle hn)]`. Rewrite `hx` using `[hv]`. Establish `: x ∈ orb N x₀`.

Assume the negation of the conclusion as `h`. Conclude with `hx (Set.indicator_of_notMem h _)`. Take `⟨n, hn, e⟩` from `this`. Conclude with `⟨n, hN.2.1 hn, e⟩`.
-/
theorem span_le_of_level (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) {K N N' : Subgroup H}
    (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (hN' : IsLevel K N') (hle : N' ≤ N) (x₀ : X) {v v' : SB X}
    (hv : ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x)
    (hv' : ∀ x, v'.1 x = (orb N' x₀).indicator (fun _ => (1 : ℂ)) x) :
    Submodule.span ℂ (Set.range fun g : H => ρ g v) ≤ Submodule.span ℂ (Set.range fun g : H => ρ g v') := by
  classical
  refine span_translates_le ρ (mem_span_translates_of_level H X ρ hρ K N' hK hN'.1 hN'.2.1 hN'.2.2 x₀ v' v hv' (fun n hn x => ?_) fun x hx => ?_)
  · rw [hv, hv]
    simp only [Set.indicator, orb_smul_mem_iff (hle hn)]
  · rw [hv] at hx
    have : x ∈ orb N x₀ := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    obtain ⟨n, hn, e⟩ := this
    exact ⟨n, hN.2.1 hn, e⟩

variable [T2Space X] [ContinuousSMul H X]

/- English proof (translation)
Take `⟨N, hN, v, hv, hf⟩` from `h`. Take `⟨N', hN', v', hv', hf'⟩` from `h'`. Take `⟨u, hu⟩` from `exists_indicator_orb hopen hK (hN.inf hN') x₀`. Conclude with `⟨_, hN.inf hN', u, hu, span_le_of_level ρ hρ hK hN (hN.inf hN') inf_le_left x₀ hv hu hf, span_le_of_level ρ hρ hK hN' (hN.inf hN') inf_le_right x₀ hv' hu hf'⟩`.
-/
theorem Reached.add {ρ : Representation ℂ H (SB X)}
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H)) {x₀ : X}
    {f f' : SB X} (h : Reached ρ K x₀ f) (h' : Reached ρ K x₀ f') :
    ∃ N : Subgroup H, IsLevel K N ∧ ∃ v : SB X, (∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x) ∧
      f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) ∧ f' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
  obtain ⟨N, hN, v, hv, hf⟩ := h
  obtain ⟨N', hN', v', hv', hf'⟩ := h'
  obtain ⟨u, hu⟩ := exists_indicator_orb hopen hK (hN.inf hN') x₀
  exact ⟨_, hN.inf hN', u, hu, span_le_of_level ρ hρ hK hN (hN.inf hN') inf_le_left x₀ hv hu hf,
    span_le_of_level ρ hρ hK hN' (hN.inf hN') inf_le_right x₀ hv' hu hf'⟩

/- English proof (translation)
Take `⟨U, hU, hUf⟩` from `exists_nhds_smul_invariant H X f`. Take `⟨N, hNo, hNK, hNU, hNn⟩` from `exists_level_subset H K hK hKo U hU`. Establish `hN : IsLevel K N` using `⟨hNo, hNK, hNn⟩`. Take `⟨v, hv⟩` from `exists_indicator_orb hopen hK hN x₀`. Conclude with `⟨N, hN, v, hv, mem_span_translates_of_level H X ρ hρ K N hK hNo hNK hNn x₀ v f hv (fun n hn x => hUf n (hNU hn) x) hf⟩`.
-/
theorem reached_of_support [T2Space H] [TotallyDisconnectedSpace H] (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (x₀ : X) (f : SB X) (hf : ∀ x, f.1 x ≠ 0 → x ∈ orb K x₀) :
    Reached ρ K x₀ f := by
  obtain ⟨U, hU, hUf⟩ := exists_nhds_smul_invariant H X f
  obtain ⟨N, hNo, hNK, hNU, hNn⟩ := exists_level_subset H K hK hKo U hU
  have hN : IsLevel K N := ⟨hNo, hNK, hNn⟩
  obtain ⟨v, hv⟩ := exists_indicator_orb hopen hK hN x₀
  exact ⟨N, hN, v, hv, mem_span_translates_of_level H X ρ hρ K N hK hNo hNK hNn x₀ v f hv (fun n hn x => hUf n (hNU hn) x) hf⟩

/- English proof (translation)
Establish `hYc : IsCompact (orb K x₀)` using `hK.image (continuous_id.smul continuous_const)`. Establish `hY : IsClopen (orb K x₀)` using `⟨hYc.isClosed, hopen x₀ _ hKo⟩`. Establish `hZ : ∀ g : H, IsClopen {x : X | g⁻¹ • x ∈ orb K x₀}` using `fun g => hY.preimage (continuous_const_smul g⁻¹)`. Establish `key : ∀ (T : Finset H) (f : SB X), (∀ x, f.1 x ≠ 0 → ∃ g ∈ T, g⁻¹ • x ∈ orb K x₀) → Reached ρ K x₀ f`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`. Use `reached_of_support ρ hρ hopen hK hKo x₀ f fun x hx => ?_` and prove the remaining obligations. Take `⟨g, hg, -⟩` from `hf x hx`.

Simplify using `at hg`. Consider the case `insert g T hg ih`. Introduce `f hf`. Take `⟨f₁, f₂, e, h₁, h₂⟩` from `exists_clopen_cut X _ (hZ g) f`. Establish `r₁ : Reached ρ K x₀ f₁`.

Take `⟨N, hN, v, hv, hm⟩` from `reached_of_support ρ hρ hopen hK hKo x₀ (ρ g⁻¹ f₁) (fun x hx => by`. Rewrite `hx` using `[hρ, inv_inv]`. Simplify using `using (h₁ _ hx).1)`. Use `⟨N, hN, v, hv, ?_⟩` and prove the remaining obligations. Use `translate_mem_span ρ v g hm` as an intermediate fact.

Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Establish `r₂ : Reached ρ K x₀ f₂` using `ih f₂ fun x hx => by`. Take `⟨hx₁, hx₂⟩` from `h₂ x hx`. Take `⟨g', hg', hm⟩` from `hf x hx₂`. Break down `Finset.mem_insert.1 hg' with rfl | hg'` into its components or cases.

Conclude with `absurd hm hx₁`. Conclude with `⟨g', hg', hm⟩`. Take `⟨N, hN, v, hv, m₁, m₂⟩` from `r₁.add hρ hopen hK r₂`. Conclude with `⟨N, hN, v, hv, e ▸ Submodule.add_mem _ m₁ m₂⟩`. Take `⟨T, hT⟩` from `f.2.2.elim_finite_subcover (fun g : H => {x : X | g⁻¹ • x ∈ orb K x₀}) (fun g => (hZ g).isOpen) (fun x _ => by`.

Take `⟨g, hg⟩` from `MulAction.exists_smul_eq H x₀ x`. Conclude with `Set.mem_iUnion.2 ⟨g, 1, K.one_mem, by show (1 : H) • x₀ = g⁻¹ • x`. Rewrite using `[one_smul, ← hg, inv_smul_smul]⟩)`. Conclude with `key T f fun x hx => by`. Simplify using `using hT (subset_tsupport _ hx)`.
-/
theorem reached_all [T2Space H] [TotallyDisconnectedSpace H] [MulAction.IsPretransitive H X]
    (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (x₀ : X) (f : SB X) : Reached ρ K x₀ f := by
  classical
  have hYc : IsCompact (orb K x₀) := hK.image (continuous_id.smul continuous_const)
  have hY : IsClopen (orb K x₀) := ⟨hYc.isClosed, hopen x₀ _ hKo⟩
  have hZ : ∀ g : H, IsClopen {x : X | g⁻¹ • x ∈ orb K x₀} := fun g =>
    hY.preimage (continuous_const_smul g⁻¹)
  have key : ∀ (T : Finset H) (f : SB X), (∀ x, f.1 x ≠ 0 → ∃ g ∈ T, g⁻¹ • x ∈ orb K x₀) →
      Reached ρ K x₀ f := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro f hf
      refine reached_of_support ρ hρ hopen hK hKo x₀ f fun x hx => ?_
      obtain ⟨g, hg, -⟩ := hf x hx
      simp at hg
    | insert g T hg ih =>
      intro f hf
      obtain ⟨f₁, f₂, e, h₁, h₂⟩ := exists_clopen_cut X _ (hZ g) f
      have r₁ : Reached ρ K x₀ f₁ := by
        obtain ⟨N, hN, v, hv, hm⟩ := reached_of_support ρ hρ hopen hK hKo x₀ (ρ g⁻¹ f₁) (fun x hx => by
          rw [hρ, inv_inv] at hx
          simpa using (h₁ _ hx).1)
        refine ⟨N, hN, v, hv, ?_⟩
        have := translate_mem_span ρ v g hm
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
      have r₂ : Reached ρ K x₀ f₂ := ih f₂ fun x hx => by
        obtain ⟨hx₁, hx₂⟩ := h₂ x hx
        obtain ⟨g', hg', hm⟩ := hf x hx₂
        rcases Finset.mem_insert.1 hg' with rfl | hg'
        · exact absurd hm hx₁
        · exact ⟨g', hg', hm⟩
      obtain ⟨N, hN, v, hv, m₁, m₂⟩ := r₁.add hρ hopen hK r₂
      exact ⟨N, hN, v, hv, e ▸ Submodule.add_mem _ m₁ m₂⟩
  obtain ⟨T, hT⟩ := f.2.2.elim_finite_subcover (fun g : H => {x : X | g⁻¹ • x ∈ orb K x₀})
    (fun g => (hZ g).isOpen) (fun x _ => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H x₀ x
      exact Set.mem_iUnion.2 ⟨g, 1, K.one_mem, by
        show (1 : H) • x₀ = g⁻¹ • x
        rw [one_smul, ← hg, inv_smul_smul]⟩)
  exact key T f fun x hx => by
    simpa using hT (subset_tsupport _ hx)

/- English proof (translation)
Distinguish the cases in `hX : Nonempty X`. Take `⟨x₀⟩` from `hX`. Take `⟨_, _, t, _, h, h'⟩` from `(reached_all ρ hρ hopen hK hKo x₀ w).add hρ hopen hK (reached_all ρ hρ hopen hK hKo x₀ w')`. Conclude with `⟨t, h, h'⟩`. Use `haveI : IsEmpty X := not_nonempty_iff.1 hX`.

Establish `h0 : ∀ u : SB X, u = 0` using `fun u => Subtype.ext (funext fun x => isEmptyElim x)`. Conclude with `⟨0, by rw [h0 w]; exact Submodule.zero_mem _, by rw [h0 w']; exact Submodule.zero_mem _⟩`.
-/
theorem exists_common_generator [T2Space H] [TotallyDisconnectedSpace H] [MulAction.IsPretransitive H X]
    (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (w w' : SB X) :
    ∃ t : SB X, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) ∧
      w' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) := by
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    obtain ⟨_, _, t, _, h, h'⟩ := (reached_all ρ hρ hopen hK hKo x₀ w).add hρ hopen hK
      (reached_all ρ hρ hopen hK hKo x₀ w')
    exact ⟨t, h, h'⟩
  · haveI : IsEmpty X := not_nonempty_iff.1 hX
    have h0 : ∀ u : SB X, u = 0 := fun u => Subtype.ext (funext fun x => isEmptyElim x)
    exact ⟨0, by rw [h0 w]; exact Submodule.zero_mem _, by rw [h0 w']; exact Submodule.zero_mem _⟩

end Orbit

section Stratum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]

@[reducible] def rMul (κ : ℕ) : MulAction (GL a k) (RankIn k a c {κ}) where
  smul g x := rAct {κ} x g⁻¹
  one_smul x := by
    show rAct {κ} x 1⁻¹ = x
    rw [inv_one, rAct_one]
  mul_smul g h x := by
    show rAct {κ} x (g * h)⁻¹ = rAct {κ} (rAct {κ} x h⁻¹) g⁻¹
    rw [_root_.mul_inv_rev, rAct_mul]

/- English proof (translation)
Use `Continuous.subtype_mk (f := fun p : GL a k × RankIn k a c {κ} => act p.2.1 (p.1⁻¹, 1)) ?_ _` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul (Units.continuous_coe_inv.comp continuous_fst)`.
-/
theorem continuous_rAct_inv (κ : ℕ) :
    Continuous fun p : GL a k × RankIn k a c {κ} => rAct {κ} p.2 p.1⁻¹ := by
  refine Continuous.subtype_mk (f := fun p : GL a k × RankIn k a c {κ} => act p.2.1 (p.1⁻¹, 1)) ?_ _
  exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul
    (Units.continuous_coe_inv.comp continuous_fst)

/- English proof (translation)
Take `⟨_, _⟩` from `SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `: NonarchimedeanAddGroup k` using `⟨fun V hV => by`. Take `⟨s, hs⟩` from `SplitWeil.exists_cball_subset hV`. Conclude with `⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩`. Establish `: TotallyDisconnectedSpace k` using `inferInstance`.

Establish `: TotallyDisconnectedSpace (Matrix a a k)` using `inferInstanceAs (TotallyDisconnectedSpace (a → a → k))`. Establish `: LocallyCompactSpace (Matrix c a k)` using `inferInstanceAs (LocallyCompactSpace (c → a → k))`. Use `haveI : TotallyDisconnectedSpace (GL a k) := ⟨(isTotallyDisconnected_of_image (f := fun g : GL a k => g.val) SplitFlip.isEmbedding_val_GL.continuous.continuousOn SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩`. Use `letI := rMul (k := k) (a := a) (c := c) κ`. Establish `hsm : ∀ (g : GL a k) (x : RankIn k a c {κ}), g • x = rAct {κ} x g⁻¹` using `fun _ _ => rfl`.

Use `haveI : ContinuousSMul (GL a k) (RankIn k a c {κ}) := ⟨continuous_rAct_inv κ⟩`. Use `haveI : MulAction.IsPretransitive (GL a k) (RankIn k a c {κ}) := ⟨fun x y => by`. Take `⟨g, hg⟩` from `exists_gl_eq_mul_of_rank k a c x.1 y.1 (x.2.trans hκ) (y.2.trans hκ)`. Use `⟨g⁻¹, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, inv_inv, rAct_val, hg]⟩`.

Establish `hXo : IsOpen {x : Matrix c a k | x.rank ∈ ({κ} : Set ℕ)}`. Use `isOpen_le_rank (k := k) (a := a) (b := c) κ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Conclude with `⟨fun h => h.ge, fun h => le_antisymm ((Matrix.rank_le_card_height x).trans hκ.ge) h⟩`.

Use `haveI : LocallyCompactSpace (RankIn k a c {κ}) := hXo.locallyCompactSpace`. Establish `hop : ∀ x : RankIn k a c {κ}, IsOpenMap fun g : GL a k => g • x` using `fun x => isOpenMap_smul_of_sigmaCompact x`. Establish `hρ : ∀ (g : GL a k) (f : SB (RankIn k a c {κ})) (x : RankIn k a c {κ}), (rightRep (k` using `k) a c κ g f).1 x = f.1 (g⁻¹ • x) := by`. Introduce `g f x`. Use `show _ = f.1 (rAct {κ} x g⁻¹⁻¹)`.

Rewrite using `[inv_inv]`. Both sides reduce to the same expression. Conclude with `finite_coinv_of_common_generator _ _ _ _ (exists_common_generator (rightRep (k := k) a c κ) hρ hop SplitFlip.isCompact_KO SplitFlip.isOpen_KO)`.
-/
theorem fullRank_finite (κ : ℕ) (hκ : κ = Fintype.card c) (θ : GL a k →* ℂˣ) :
    Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix a a k) := inferInstanceAs (TotallyDisconnectedSpace (a → a → k))
  have : LocallyCompactSpace (Matrix c a k) := inferInstanceAs (LocallyCompactSpace (c → a → k))
  haveI : TotallyDisconnectedSpace (GL a k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL a k => g.val) SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  letI := rMul (k := k) (a := a) (c := c) κ
  have hsm : ∀ (g : GL a k) (x : RankIn k a c {κ}), g • x = rAct {κ} x g⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (GL a k) (RankIn k a c {κ}) := ⟨continuous_rAct_inv κ⟩
  haveI : MulAction.IsPretransitive (GL a k) (RankIn k a c {κ}) := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a c x.1 y.1 (x.2.trans hκ) (y.2.trans hκ)
    refine ⟨g⁻¹, Subtype.ext ?_⟩
    rw [hsm, inv_inv, rAct_val, hg]⟩
  have hXo : IsOpen {x : Matrix c a k | x.rank ∈ ({κ} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := a) (b := c) κ using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm ((Matrix.rank_le_card_height x).trans hκ.ge) h⟩
  haveI : LocallyCompactSpace (RankIn k a c {κ}) := hXo.locallyCompactSpace
  have hop : ∀ x : RankIn k a c {κ}, IsOpenMap fun g : GL a k => g • x :=
    fun x => isOpenMap_smul_of_sigmaCompact x
  have hρ : ∀ (g : GL a k) (f : SB (RankIn k a c {κ})) (x : RankIn k a c {κ}),
      (rightRep (k := k) a c κ g f).1 x = f.1 (g⁻¹ • x) := by
    intro g f x
    show _ = f.1 (rAct {κ} x g⁻¹⁻¹)
    rw [inv_inv]
    rfl
  exact finite_coinv_of_common_generator _ _ _ _ (exists_common_generator (rightRep (k := k) a c κ) hρ hop SplitFlip.isCompact_KO SplitFlip.isOpen_KO)

end Stratum

/- English proof (translation)
Introduce `k _ _ _ _ a c _ _ _ _ κ hκ θ`. Conclude with `fullRank_finite κ hκ θ`.
-/
theorem finite_coinv_rightRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (κ : ℕ), κ = Fintype.card c → ∀ θ : GL a k →* ℂˣ, Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  intro k _ _ _ _ a c _ _ _ _ κ hκ θ
  exact fullRank_finite κ hκ θ

end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
