import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Establish `hp : Z.starProjection x ∈ Z` using `Submodule.starProjection_apply_mem Z x`. Apply `Submodule.eq_starProjection_of_mem_orthogonal (hZ _ hp)` to reduce the goal to its premises. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `z hz`. Establish `hxo : x - Z.starProjection x ∈ Zᗮ` using `Submodule.sub_starProjection_mem_orthogonal x`.

Establish `hsym : ⟪z, T (x - Z.starProjection x)⟫_ℂ = ⟪T z, x - Z.starProjection x⟫_ℂ`. Use `ContinuousLinearMap.adjoint_inner_left T (x - Z.starProjection x) z` as an intermediate fact. Rewrite using `[← this, ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]`. Rewrite using `[← map_sub, hsym]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hxo _ (hZ z hz)`.
-/
private lemma proj_comm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hZ : ∀ z ∈ Z, T z ∈ Z) (x : H) : Z.starProjection (T x) = T (Z.starProjection x) := by
  have hp : Z.starProjection x ∈ Z := Submodule.starProjection_apply_mem Z x
  apply Submodule.eq_starProjection_of_mem_orthogonal (hZ _ hp)
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hxo : x - Z.starProjection x ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hsym : ⟪z, T (x - Z.starProjection x)⟫_ℂ = ⟪T z, x - Z.starProjection x⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left T (x - Z.starProjection x) z
    rw [← this, ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
  rw [← map_sub, hsym]
  exact (Submodule.mem_orthogonal _ _).1 hxo _ (hZ z hz)

end UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Introduce `Γ G H _ _ _ _ _ _ π V m ι E A U h i y hy`. Take `⟨hcl, hinv, hirr⟩` from `UpperTheory.ConvolutionTheory.L1.cutIrr Γ G H π V m ι E A U h`. Establish `hmemVE : ∀ w, w ∈ eigIn V E 1 ↔ w ∈ V ∧ E w = w`. Introduce `w`. Simplify using `[eigIn, Module.End.mem_eigenspace_iff, Submodule.mem_inf]`.

Establish `hmemZ : ∀ (k : Fin (m + 1)) w, w ∈ eigIn (eigIn V E 1) (A k) y ↔ w ∈ eigIn V E 1 ∧ A k w = (y : ℂ) • w`. Introduce `k w`. Simplify using `only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]`. Both sides reduce to the same expression. Establish `hsa : ∀ k, IsSelfAdjoint (A k)` using `fun k => ((ContinuousLinearMap.nonneg_iff_isPositive _).1 (h.A_pos k)).isSelfAdjoint`.

Establish `hAVE : ∀ j, ∀ w ∈ eigIn V E 1, A j w ∈ eigIn V E 1`. Introduce `j w hw`. Take `⟨hwV, hwE⟩` from `(hmemVE w).1 hw`. Use `(hmemVE _).2 ⟨h.A_mem j w hwV, ?_⟩` and prove the remaining obligations. Rewrite using `[← h.A_E, hwE]`.

Establish `hstep : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ → eigIn (eigIn V E 1) (A (j + 1)) y ≠ ⊥`. Introduce `j hj`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hj`. Take `⟨hvE, hvA⟩` from `(hmemZ j v).1 hv`. Take `⟨hvV, hvE'⟩` from `(hmemVE v).1 hvE`.

Establish `hvm : v ∈ V.map (U : H →ₗ[ℂ] H)` using `by rw [h.U_mem]; exact hvV`. Take `⟨u, hu, rfl⟩` from `hvm`. Establish `hU : ∀ a b : H, U a = U b → a = b` using `fun a b hab => U.injective hab`. Use `(Submodule.ne_bot_iff _).2 ⟨u, (hmemZ _ u).2 ⟨(hmemVE u).2 ⟨hu, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `hU` to reduce the goal to its premises.

Rewrite using `[h.U_E]`. Conclude with `hvE'`. Apply `hU` to reduce the goal to its premises. Rewrite using `[h.U_A, map_smul]`. Conclude with `hvA`.

Introduce and unpack `rfl`. Conclude with `hv0 (by simp)`. Establish `hall : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥`. Establish `ht : ∀ t : Fin (m + 1), eigIn (eigIn V E 1) (A (i + t)) y ≠ ⊥`. Introduce `t`.

Proceed by induction on `t using Fin.induction with`. Consider the case `zero => simpa using hy`. Consider the case `succ t ih`. Rewrite using `[← Fin.coeSucc_eq_succ, ← add_assoc]`. Conclude with `hstep _ ih`.

Introduce `j`. Use `ht (j - i)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hS : ∀ S : Finset (Fin (m + 1)), ∃ w ∈ eigIn V E 1, w ≠ 0 ∧ ∀ j ∈ S, A j w = (y : ℂ) • w`. Introduce `S`.

Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Establish `hne : eigIn V E 1 ≠ ⊥`. Introduce `hb`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 (hall i)`.

Use `((hmemZ i v).1 hv).1` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `hv0 (by simpa using this)`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Conclude with `⟨v, hv, hv0, by simp⟩`.

Consider the case `insert k S hk ih`. Take `⟨w₀, hw₀, hw₀0, hw₀A⟩` from `ih`. Assume the negation of the conclusion as `hno`. Establish `hno' : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → A k w = (y : ℂ) • w → w = 0`. Introduce `w hw hwS hwk`.

Assume the negation of the conclusion as `hw0`. Conclude with `hno ⟨w, hw, hw0, fun j hj => by`. Break down `Finset.mem_insert.1 hj with rfl | hj` into its components or cases. Conclude with `hwk`. Conclude with `hwS j hj⟩`.

Use `set Z := eigIn (eigIn V E 1) (A k) y with hZdef`. Establish `hZcl : IsClosed (Z : Set H)`. Establish `h2 : IsClosed {w : H | A k w = (y : ℂ) • w}` using `isClosed_eq (A k).continuous (continuous_const_smul _)`. Establish `: (Z : Set H) = (eigIn V E 1 : Set H) ∩ {w : H | A k w = (y : ℂ) • w}`. Use extensionality with `w`.

Conclude with `hmemZ k w`. Rewrite using `[this]`. Conclude with `hcl.inter h2`. Use `haveI : CompleteSpace Z := hZcl.completeSpace_coe`. Establish `hZA : ∀ j, ∀ z ∈ Z, A j z ∈ Z`.

Introduce `j z hz`. Take `⟨hzVE, hzA⟩` from `(hmemZ k z).1 hz`. Use `(hmemZ k _).2 ⟨hAVE j z hzVE, ?_⟩` and prove the remaining obligations. Rewrite using `[h.A_A, hzA, map_smul]`. Establish `hZπ : ∀ j, j ≠ k → ∀ g, ∀ z ∈ Z, π (ι j g) z ∈ Z`.

Introduce `j hj g z hz`. Take `⟨hzVE, hzA⟩` from `(hmemZ k z).1 hz`. Use `(hmemZ k _).2 ⟨hinv j g z hzVE, ?_⟩` and prove the remaining obligations. Rewrite using `[h.A_ι k j (Ne.symm hj), hzA, map_smul]`. Establish `hNo : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → w ∈ Zᗮ`.

Introduce `w hw hwS`. Rewrite using `[← Submodule.starProjection_apply_eq_zero_iff]`. Establish `hp : Z.starProjection w ∈ Z` using `Submodule.starProjection_apply_mem Z w`. Take `⟨hpVE, hpA⟩` from `(hmemZ k _).1 hp`. Use `hno' _ hpVE (fun j hj => ?_) hpA` and prove the remaining obligations.

Rewrite using `[← proj_comm Z (A j) (hsa j) (hZA j), hwS j hj, map_smul]`. Set `M : Submodule ℂ H` to `{ carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ} add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (ha.2 g) (hb.2 g)⟩`. Use the proof step `zero_mem' := ⟨Submodule.zero_mem _, fun g => by`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ c (ha.2 g)⟩ }`.

Establish `hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ` using `fun w => Iff.rfl`. Establish `hMle : M ≤ eigIn V E 1` using `fun w hw => hw.1`. Establish `hMcl : IsClosed (M : Set H)`. Establish `: (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, (π (ι k g)) ⁻¹' (Zᗮ : Set H)`. Use extensionality with `w`.

Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `hMmem w`. Rewrite using `[this]`. Conclude with `hcl.inter (isClosed_iInter fun g => (Submodule.isClosed_orthogonal Z).preimage (π (ι k g)).continuous)`. Establish `hMinv : ∀ j g, ∀ v ∈ M, π (ι j g) v ∈ M`.

Introduce `j g v hv`. Use `(hMmem _).2 ⟨hinv j g v hv.1, fun g' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Rewrite using `[← π.map_mul_apply, ← map_mul]`.

Conclude with `hv.2 _`. Rewrite using `[← π.map_mul_apply, ((h.ι_comm k j (Ne.symm hjk)) g' g).eq, π.map_mul_apply]`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `z hz`. Rewrite using `[π.inner_map_right, ← map_inv]`.

Conclude with `(Submodule.mem_orthogonal _ _).1 (hv.2 g') _ (hZπ j hjk _ z hz)`. Establish `hw₀M : w₀ ∈ M`. Use `(hMmem _).2 ⟨hw₀, fun g => hNo _ (hinv k g w₀ hw₀) fun j hj => ?_⟩` and prove the remaining obligations. Establish `hjk : j ≠ k` using `fun e => hk (e ▸ hj)`. Rewrite using `[h.A_ι j k hjk, hw₀A j hj, map_smul]`.

Establish `hMtop : M = eigIn V E 1`. Break down `hirr M hMle hMcl hMinv with hb | he` into its components or cases. It suffices to derive a contradiction. Rewrite `hw₀M` using `[hb]`. Conclude with `hw₀0 (by simpa using hw₀M)`.

Conclude with `he`. Take `⟨z, hz, hz0⟩` from `(Submodule.ne_bot_iff _).1 (hall k)`. Establish `hzM : z ∈ M`. Rewrite using `[hMtop]`. Conclude with `((hmemZ k z).1 hz).1`.

Establish `hzo` using `hzM.2 1`. Rewrite `hzo` using `[map_one, π.map_one_apply]`. Use `(Submodule.mem_orthogonal _ _).1 hzo z hz` as an intermediate fact. Conclude with `hz0 (inner_self_eq_zero.1 this)`. Take `⟨w, hw, hw0, hwA⟩` from `hS Finset.univ`.

Use `(Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩` and prove the remaining obligations. Simplify using `only [jointEig, Submodule.mem_iInf]`. Conclude with `fun j => (hmemZ j w).2 ⟨hw, hwA j (Finset.mem_univ j)⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.jointNe :
    UpperTheory.ConvolutionTheory.L1.JointNe := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h i y hy
  obtain ⟨hcl, hinv, hirr⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr Γ G H π V m ι E A U h
  have hmemVE : ∀ w, w ∈ eigIn V E 1 ↔ w ∈ V ∧ E w = w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff, Submodule.mem_inf]
  have hmemZ : ∀ (k : Fin (m + 1)) w, w ∈ eigIn (eigIn V E 1) (A k) y ↔
      w ∈ eigIn V E 1 ∧ A k w = (y : ℂ) • w := by
    intro k w
    simp only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    rfl
  have hsa : ∀ k, IsSelfAdjoint (A k) := fun k =>
    ((ContinuousLinearMap.nonneg_iff_isPositive _).1 (h.A_pos k)).isSelfAdjoint
  have hAVE : ∀ j, ∀ w ∈ eigIn V E 1, A j w ∈ eigIn V E 1 := by
    intro j w hw
    obtain ⟨hwV, hwE⟩ := (hmemVE w).1 hw
    refine (hmemVE _).2 ⟨h.A_mem j w hwV, ?_⟩
    rw [← h.A_E, hwE]

  have hstep : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ → eigIn (eigIn V E 1) (A (j + 1)) y ≠ ⊥ := by
    intro j hj
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hj
    obtain ⟨hvE, hvA⟩ := (hmemZ j v).1 hv
    obtain ⟨hvV, hvE'⟩ := (hmemVE v).1 hvE
    have hvm : v ∈ V.map (U : H →ₗ[ℂ] H) := by rw [h.U_mem]; exact hvV
    obtain ⟨u, hu, rfl⟩ := hvm
    have hU : ∀ a b : H, U a = U b → a = b := fun a b hab => U.injective hab
    refine (Submodule.ne_bot_iff _).2 ⟨u, (hmemZ _ u).2 ⟨(hmemVE u).2 ⟨hu, ?_⟩, ?_⟩, ?_⟩
    · apply hU
      rw [h.U_E]
      exact hvE'
    · apply hU
      rw [h.U_A, map_smul]
      exact hvA
    · rintro rfl
      exact hv0 (by simp)
  have hall : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ := by
    have ht : ∀ t : Fin (m + 1), eigIn (eigIn V E 1) (A (i + t)) y ≠ ⊥ := by
      intro t
      induction t using Fin.induction with
      | zero => simpa using hy
      | succ t ih =>
        rw [← Fin.coeSucc_eq_succ, ← add_assoc]
        exact hstep _ ih
    intro j
    have := ht (j - i)
    rwa [add_sub_cancel] at this

  have hS : ∀ S : Finset (Fin (m + 1)), ∃ w ∈ eigIn V E 1, w ≠ 0 ∧ ∀ j ∈ S, A j w = (y : ℂ) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hne : eigIn V E 1 ≠ ⊥ := by
        intro hb
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (hall i)
        have := ((hmemZ i v).1 hv).1
        rw [hb] at this
        exact hv0 (by simpa using this)
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨v, hv, hv0, by simp⟩
    | insert k S hk ih =>
      obtain ⟨w₀, hw₀, hw₀0, hw₀A⟩ := ih
      by_contra hno
      have hno' : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → A k w = (y : ℂ) • w → w = 0 := by
        intro w hw hwS hwk
        by_contra hw0
        exact hno ⟨w, hw, hw0, fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact hwk
          · exact hwS j hj⟩
      set Z := eigIn (eigIn V E 1) (A k) y with hZdef
      have hZcl : IsClosed (Z : Set H) := by
        have h2 : IsClosed {w : H | A k w = (y : ℂ) • w} :=
          isClosed_eq (A k).continuous (continuous_const_smul _)
        have : (Z : Set H) = (eigIn V E 1 : Set H) ∩ {w : H | A k w = (y : ℂ) • w} := by
          ext w
          exact hmemZ k w
        rw [this]
        exact hcl.inter h2
      haveI : CompleteSpace Z := hZcl.completeSpace_coe
      have hZA : ∀ j, ∀ z ∈ Z, A j z ∈ Z := by
        intro j z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hAVE j z hzVE, ?_⟩
        rw [h.A_A, hzA, map_smul]
      have hZπ : ∀ j, j ≠ k → ∀ g, ∀ z ∈ Z, π (ι j g) z ∈ Z := by
        intro j hj g z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hinv j g z hzVE, ?_⟩
        rw [h.A_ι k j (Ne.symm hj), hzA, map_smul]

      have hNo : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → w ∈ Zᗮ := by
        intro w hw hwS
        rw [← Submodule.starProjection_apply_eq_zero_iff]
        have hp : Z.starProjection w ∈ Z := Submodule.starProjection_apply_mem Z w
        obtain ⟨hpVE, hpA⟩ := (hmemZ k _).1 hp
        refine hno' _ hpVE (fun j hj => ?_) hpA
        rw [← proj_comm Z (A j) (hsa j) (hZA j), hwS j hj, map_smul]
      let M : Submodule ℂ H :=
        { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ}
          add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
            rw [map_add]; exact Submodule.add_mem _ (ha.2 g) (hb.2 g)⟩
          zero_mem' := ⟨Submodule.zero_mem _, fun g => by
            rw [map_zero]; exact Submodule.zero_mem _⟩
          smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
            rw [map_smul]; exact Submodule.smul_mem _ c (ha.2 g)⟩ }
      have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ := fun w => Iff.rfl
      have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
      have hMcl : IsClosed (M : Set H) := by
        have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, (π (ι k g)) ⁻¹' (Zᗮ : Set H) := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
          exact hMmem w
        rw [this]
        exact hcl.inter (isClosed_iInter fun g =>
          (Submodule.isClosed_orthogonal Z).preimage (π (ι k g)).continuous)
      have hMinv : ∀ j g, ∀ v ∈ M, π (ι j g) v ∈ M := by
        intro j g v hv
        refine (hMmem _).2 ⟨hinv j g v hv.1, fun g' => ?_⟩
        by_cases hjk : j = k
        · subst hjk
          rw [← π.map_mul_apply, ← map_mul]
          exact hv.2 _
        · rw [← π.map_mul_apply, ((h.ι_comm k j (Ne.symm hjk)) g' g).eq, π.map_mul_apply]
          rw [Submodule.mem_orthogonal]
          intro z hz
          rw [π.inner_map_right, ← map_inv]
          exact (Submodule.mem_orthogonal _ _).1 (hv.2 g') _ (hZπ j hjk _ z hz)
      have hw₀M : w₀ ∈ M := by
        refine (hMmem _).2 ⟨hw₀, fun g => hNo _ (hinv k g w₀ hw₀) fun j hj => ?_⟩
        have hjk : j ≠ k := fun e => hk (e ▸ hj)
        rw [h.A_ι j k hjk, hw₀A j hj, map_smul]
      have hMtop : M = eigIn V E 1 := by
        rcases hirr M hMle hMcl hMinv with hb | he
        · exfalso
          rw [hb] at hw₀M
          exact hw₀0 (by simpa using hw₀M)
        · exact he
      obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 (hall k)
      have hzM : z ∈ M := by
        rw [hMtop]
        exact ((hmemZ k z).1 hz).1
      have hzo := hzM.2 1
      rw [map_one, π.map_one_apply] at hzo
      have := (Submodule.mem_orthogonal _ _).1 hzo z hz
      exact hz0 (inner_self_eq_zero.1 this)
  obtain ⟨w, hw, hw0, hwA⟩ := hS Finset.univ
  refine (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩
  simp only [jointEig, Submodule.mem_iInf]
  exact fun j => (hmemZ j w).2 ⟨hw, hwA j (Finset.mem_univ j)⟩
