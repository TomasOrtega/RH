import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProjectionToLeviStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSectionLeviEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOfIwasawaContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedFunctionL2PositiveStatement

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.IndNonzero

/- English proof (translation)
Take `⟨u, hu, m, hm, x, t, ht, rfl⟩` from `exists_langlands_decomp hW hj hp`. Take `⟨h, -, h1, hK, hh⟩` from `exists_height hW hj`. Establish `hx : x = 0`. Establish `e1` using `hh u hu m hm x t ht 1`. Establish `e2` using `hK 1 _ hk`.

Rewrite `e1` using `[mul_one]`. Rewrite `e2` using `[one_mul]`. Rewrite `e1` using `[e2, h1, add_zero]`. Conclude with `e1.symm`. Substitute `hx` using the available equality.

Establish `ht1 : t = 1` using `(existsUnique_isSplit hW 0).unique ht isSplit_one`. Substitute `ht1` using the available equality. Rewrite `hk`, the goal using `[mul_one]`. Establish `hk' : u * m ∈ maxK ε` using `by rw [← KG_eq]; exact hk`. Rewrite using `[GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW u hu m hm.1 hk', one_mul]`.

Conclude with `hm`.
-/
theorem mem_leviOne_of_mem_parab_KG {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) {p : UJ ε} (hp : p ∈ parab ε W) (hk : p ∈ KG ε) :
    p ∈ leviOne ε W := by
  obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
  obtain ⟨h, -, h1, hK, hh⟩ := exists_height hW hj
  have hx : x = 0 := by
    have e1 := hh u hu m hm x t ht 1
    have e2 := hK 1 _ hk
    rw [mul_one] at e1
    rw [one_mul] at e2
    rw [e2, h1, add_zero] at e1
    exact e1.symm
  subst hx
  have ht1 : t = 1 := (existsUnique_isSplit hW 0).unique ht isSplit_one
  subst ht1
  rw [mul_one] at hk ⊢
  have hk' : u * m ∈ maxK ε := by rw [← KG_eq]; exact hk
  rw [GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW u hu m hm.1 hk', one_mul]
  exact hm

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Establish `h1 : ContinuousAt (fun x => σ (mf x) (wf x0)) x0` using `((hσ.2.2 (wf x0)).comp_continuous hm hS).continuousAt`. Rewrite `h1`, the goal using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`. Establish `h2 : Filter.Tendsto (fun x => ‖wf x - wf x0‖) (nhds x0) (nhds 0)` using `tendsto_iff_norm_sub_tendsto_zero.1 hw.continuousAt`.

Use `squeeze_zero (g := fun x => ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ + ‖wf x - wf x0‖) (fun _ => norm_nonneg _) (fun x => ?_) (by have := h1.add h2; rwa [add_zero] at this)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Use `_ ≤ ‖σ (mf x) (wf x - wf x0)‖ + ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ := norm_add_le _ _`. Use `_ = _ := by rw [hσ.2.1 _ (hS x)]; ring`.
-/
theorem continuous_apply_of_isURepOn {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℂ)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}
    (hσ : IsURepOn S σ) {X : Type} [TopologicalSpace X] {mf : X → Matrix (Fin n) (Fin n) ℂ} {wf : X → V}
    (hm : Continuous mf) (hS : ∀ x, mf x ∈ S) (hw : Continuous wf) : Continuous fun x => σ (mf x) (wf x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have h1 : ContinuousAt (fun x => σ (mf x) (wf x0)) x0 :=
    ((hσ.2.2 (wf x0)).comp_continuous hm hS).continuousAt
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
  have h2 : Filter.Tendsto (fun x => ‖wf x - wf x0‖) (nhds x0) (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hw.continuousAt
  refine squeeze_zero (g := fun x => ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ + ‖wf x - wf x0‖)
    (fun _ => norm_nonneg _) (fun x => ?_) (by have := h1.add h2; rwa [add_zero] at this)
  calc ‖σ (mf x) (wf x) - σ (mf x0) (wf x0)‖
      = ‖σ (mf x) (wf x - wf x0) + (σ (mf x) (wf x0) - σ (mf x0) (wf x0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖σ (mf x) (wf x - wf x0)‖ + ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ := norm_add_le _ _
    _ = _ := by rw [hσ.2.1 _ (hS x)]; ring

end GlobalTheory.IndNonzero

namespace GlobalTheory.IndNonzero

/- English proof (translation)
Take `⟨hU, -⟩` from `D.temp.2.2`. Establish `hW` using `D.flag`. Establish `hj` using `D.pos`. Take `⟨φ, hφc, hφ1, hφm⟩` from `GlobalTheory.T.continuous_section_levi_equivariant n ε D`. Take `⟨μ, hμc, hμM, hμmul, hμs⟩` from `GlobalTheory.T.parabolic_projection_to_levi n D.a ε D.j D.W hW hj`.

Establish `hPK` using `fun p hp hk => mem_leviOne_of_mem_parab_KG hW hj (p := p) hp hk`. Establish `hσmul : ∀ m ∈ leviOne ε D.W, ∀ m' ∈ leviOne ε D.W, ∀ w, D.σ (uMat (m * m')) w = D.σ (uMat m) (D.σ (uMat m') w)`. Introduce `m hm m' hm' w`. Rewrite using `[uMat_mul, hU.1.2 _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩]`. Both sides reduce to the same expression.

Establish `h1N : (1 : UJ ε) ∈ flagN ε D.W` using `⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩`. Establish `hμid : ∀ m ∈ leviOne ε D.W, μ m = m` using `fun m hm => by`. Simplify using `using (hμs 1 h1N m hm 0 1 isSplit_one).2`. Establish `dec : ∀ g : UJ ε, ∃ p ∈ parab ε D.W, ∃ k ∈ KG ε, g = p * k` using `fun g => by`. Take `⟨k, hk, hp⟩` from `GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g`.

Use `⟨g * k⁻¹, hp, k, ?_, by group⟩` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, KG_eq]`. Conclude with `hk`. Establish `wd : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, ∀ p' ∈ parab ε D.W, ∀ k' ∈ KG ε, p * k = p' * k' → D.σ (uMat (μ p)) (φ k) = D.σ (uMat (μ p')) (φ k')`. Introduce `p hp k hk p' hp' k' hk' e`.

Establish `hck : p'⁻¹ * p = k' * k⁻¹`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]`. Establish `hcP : p'⁻¹ * p ∈ parab ε D.W` using `mul_mem (inv_mem hp') hp`. Establish `hcK : p'⁻¹ * p ∈ KG ε` using `hck ▸ mul_mem hk' (inv_mem hk)`. Establish `hcM` using `hPK _ hcP hcK`.

Establish `h1 : μ p = μ p' * (p'⁻¹ * p)` using `by conv_lhs => rw [show p = p' * (p'⁻¹ * p) by group]`. Rewrite using `[hμmul p' hp' _ hcP, hμid _ hcM]`. Establish `h2 : φ k' = D.σ (uMat (p'⁻¹ * p)) (φ k)`. Rewrite using `[← hφm _ hcM hcK, hck, inv_mul_cancel_right]`. Rewrite using `[h1, hσmul _ (hμM p' hp') _ hcM, h2]`.

Use `choose pp hpp kk hkk hpk using dec`. Set `F : UJ ε → D.V` to `fun g => D.σ (uMat (μ (pp g))) (φ (kk g))`. Establish `hF : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, F (p * k) = D.σ (uMat (μ p)) (φ k)` using `fun p hp k hk => wd _ (hpp _) _ (hkk _) p hp k hk (hpk (p * k)).symm`. Establish `hFc : Continuous F`. Use `GlobalTheory.T.continuous_of_iwasawa_continuous n D.a ε D.j D.W hW D.V F ?_` and prove the remaining obligations.

Establish `: (fun q : parab ε D.W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) = fun q => D.σ (uMat (μ q.1)) (φ q.2)` using `funext fun q => hF _ q.1.2 _ q.2.2`. Rewrite using `[this]`. Use `continuous_apply_of_isURepOn hU (mf := fun q : parab ε D.W × KG ε => uMat (μ q.1)) (wf := fun q => φ q.2) ?_ ?_ ?_` and prove the remaining obligations. Conclude with `continuous_uMat.comp ((hμc.comp_continuous continuous_subtype_val fun p => p.2).comp continuous_fst)`. Conclude with `fun q => ⟨μ q.1, hμM _ q.1.2, rfl⟩`.

Conclude with `hφc.comp (continuous_subtype_val.comp continuous_snd)`. Use `⟨F, hFc, ?_, fun u hu m hm x t ht g => ?_⟩` and prove the remaining obligations. Use `hF 1 (one_mem _) 1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, hμid 1 (one_mem _), uMat_one, hU.1.1, ContinuousLinearMap.one_apply]`.

Conclude with `hφ1`. Take `⟨hP, hμ⟩` from `hμs u hu m hm x t ht`. Establish `e : u * m * t * pp g * kk g = u * m * t * g` using `by rw [mul_assoc (u * m * t), ← hpk g]`. Rewrite using `[← e, hF _ (mul_mem hP (hpp g)) _ (hkk g), hμmul _ hP _ (hpp g), hμ, hσmul _ hm _ (hμM _ (hpp g))]`.
-/
theorem exists_equivariant {n : ℕ} {ε : Fin n → Bool} (D : Datum ε) :
    ∃ F : UJ ε → D.V, Continuous F ∧ F 1 ≠ 0 ∧ ∀ u ∈ flagN ε D.W, ∀ m ∈ leviOne ε D.W, ∀ x t,
      IsSplit ε D.W x t → ∀ g, F (u * m * t * g) = D.σ (uMat m) (F g) := by
  classical
  obtain ⟨hU, -⟩ := D.temp.2.2
  have hW := D.flag
  have hj := D.pos
  obtain ⟨φ, hφc, hφ1, hφm⟩ := GlobalTheory.T.continuous_section_levi_equivariant n ε D
  obtain ⟨μ, hμc, hμM, hμmul, hμs⟩ := GlobalTheory.T.parabolic_projection_to_levi n D.a ε D.j D.W hW hj
  have hPK := fun p hp hk => mem_leviOne_of_mem_parab_KG hW hj (p := p) hp hk
  have hσmul : ∀ m ∈ leviOne ε D.W, ∀ m' ∈ leviOne ε D.W, ∀ w,
      D.σ (uMat (m * m')) w = D.σ (uMat m) (D.σ (uMat m') w) := by
    intro m hm m' hm' w
    rw [uMat_mul, hU.1.2 _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩]
    rfl
  have h1N : (1 : UJ ε) ∈ flagN ε D.W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  have hμid : ∀ m ∈ leviOne ε D.W, μ m = m := fun m hm => by
    simpa using (hμs 1 h1N m hm 0 1 isSplit_one).2
  have dec : ∀ g : UJ ε, ∃ p ∈ parab ε D.W, ∃ k ∈ KG ε, g = p * k := fun g => by
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    refine ⟨g * k⁻¹, hp, k, ?_, by group⟩
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have wd : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, ∀ p' ∈ parab ε D.W, ∀ k' ∈ KG ε, p * k = p' * k' →
      D.σ (uMat (μ p)) (φ k) = D.σ (uMat (μ p')) (φ k') := by
    intro p hp k hk p' hp' k' hk' e
    have hck : p'⁻¹ * p = k' * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hcP : p'⁻¹ * p ∈ parab ε D.W := mul_mem (inv_mem hp') hp
    have hcK : p'⁻¹ * p ∈ KG ε := hck ▸ mul_mem hk' (inv_mem hk)
    have hcM := hPK _ hcP hcK
    have h1 : μ p = μ p' * (p'⁻¹ * p) := by
      conv_lhs => rw [show p = p' * (p'⁻¹ * p) by group]
      rw [hμmul p' hp' _ hcP, hμid _ hcM]
    have h2 : φ k' = D.σ (uMat (p'⁻¹ * p)) (φ k) := by
      rw [← hφm _ hcM hcK, hck, inv_mul_cancel_right]
    rw [h1, hσmul _ (hμM p' hp') _ hcM, h2]
  choose pp hpp kk hkk hpk using dec
  let F : UJ ε → D.V := fun g => D.σ (uMat (μ (pp g))) (φ (kk g))
  have hF : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, F (p * k) = D.σ (uMat (μ p)) (φ k) := fun p hp k hk =>
    wd _ (hpp _) _ (hkk _) p hp k hk (hpk (p * k)).symm
  have hFc : Continuous F := by
    refine GlobalTheory.T.continuous_of_iwasawa_continuous n D.a ε D.j D.W hW D.V F ?_
    have : (fun q : parab ε D.W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) =
        fun q => D.σ (uMat (μ q.1)) (φ q.2) := funext fun q => hF _ q.1.2 _ q.2.2
    rw [this]
    refine continuous_apply_of_isURepOn hU (mf := fun q : parab ε D.W × KG ε => uMat (μ q.1)) (wf := fun q => φ q.2) ?_ ?_ ?_
    · exact continuous_uMat.comp ((hμc.comp_continuous continuous_subtype_val fun p => p.2).comp continuous_fst)
    · exact fun q => ⟨μ q.1, hμM _ q.1.2, rfl⟩
    · exact hφc.comp (continuous_subtype_val.comp continuous_snd)
  refine ⟨F, hFc, ?_, fun u hu m hm x t ht g => ?_⟩
  · have := hF 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    rw [this, hμid 1 (one_mem _), uMat_one, hU.1.1, ContinuousLinearMap.one_apply]
    exact hφ1
  · obtain ⟨hP, hμ⟩ := hμs u hu m hm x t ht
    have e : u * m * t * pp g * kk g = u * m * t * g := by rw [mul_assoc (u * m * t), ← hpk g]
    rw [← e, hF _ (mul_mem hP (hpp g)) _ (hkk g), hμmul _ hP _ (hpp g), hμ, hσmul _ hm _ (hμM _ (hpp g))]

/- English proof (translation)
Introduce `n ε I`. Take `⟨F, hFc, hF1, hFl⟩` from `exists_equivariant I.toDatum`. Take `⟨e, he, he1, -⟩` from `exists_spherical I.flag I.pos I.s`. Establish `hf : (fun g => e g • F g) ∈ I.fns`. Rewrite using `[mem_indFun_top]`.

Use `⟨(mem_indFun_top.1 he).1.smul hFc, fun u hu m hm x t ht g => ?_⟩` and prove the remaining obligations. Use `(mem_indFun_top.1 he).2 u hu m hm x t ht g` as an intermediate fact. Simplify using `only [ContinuousLinearMap.one_apply, smul_eq_mul] at this`. Rewrite using `[this, hFl u hu m hm x t ht g, map_smul, smul_smul]`. Establish `hpos` using `GlobalTheory.T.induced_function_l2_positive n ε I.toDatum _ hf 1 (by simpa [he1] using hF1)`.

Establish `hι : I.ι ⟨_, hf⟩ ≠ 0`. Introduce `h0`. Use `I.model.norm_sq ⟨_, hf⟩` as an intermediate fact. Rewrite `this` using `[h0, norm_zero, zero_pow two_ne_zero]`. Conclude with `hpos.ne this`.

Conclude with `nontrivial_of_ne _ _ hι`.
-/
theorem indModule_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  intro n ε I
  obtain ⟨F, hFc, hF1, hFl⟩ := exists_equivariant I.toDatum
  obtain ⟨e, he, he1, -⟩ := exists_spherical I.flag I.pos I.s
  have hf : (fun g => e g • F g) ∈ I.fns := by
    rw [mem_indFun_top]
    refine ⟨(mem_indFun_top.1 he).1.smul hFc, fun u hu m hm x t ht g => ?_⟩
    have := (mem_indFun_top.1 he).2 u hu m hm x t ht g
    simp only [ContinuousLinearMap.one_apply, smul_eq_mul] at this
    rw [this, hFl u hu m hm x t ht g, map_smul, smul_smul]
  have hpos := GlobalTheory.T.induced_function_l2_positive n ε I.toDatum _ hf 1 (by simpa [he1] using hF1)
  have hι : I.ι ⟨_, hf⟩ ≠ 0 := by
    intro h0
    have := I.model.norm_sq ⟨_, hf⟩
    rw [h0, norm_zero, zero_pow two_ne_zero] at this
    exact hpos.ne this
  exact nontrivial_of_ne _ _ hι

end GlobalTheory.IndNonzero
