import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hz` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0`.

Apply `LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))` to reduce the goal to its premises. Introduce and unpack `w ⟨v, rfl⟩`. Simplify using `[hne v]`.
-/
theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_tprod_ne_zero_of_cc z hz`. Establish `d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) = ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)` using `by rw [h.pure, h'.pure]`. Establish `dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0`. Introduce `h0`. Use `h.posD _ hv` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `e1` using `h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)`. Establish `e2` using `h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)`. Rewrite `e2` using `[e1, ← d]`.

Conclude with `mul_right_cancel₀ dne e2`.
-/
theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

/- English proof (translation)
Proceed by induction on `hR with`. Consider the case `zero`. Introduce `_`. Use `⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩` and prove the remaining obligations. Conclude with `ip_unique h h₀ u hu.1 y u`.

Consider the case `@step k s Θ _ s' hs' p hp ih`. Introduce `hk`. Take `⟨hsk, ih⟩` from `ih (by omega)`. Use `⟨hs', fun ipD' ip' h' => ?_⟩` and prove the remaining obligations. Take `⟨ipD, ip, hm⟩` from `hMet c hc k (by omega) s hsk`.

Take `⟨x, hx, hxp⟩` from `ih ipD ip hm`. Take `⟨x', hx', hx'p⟩` from `hSU hgap c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp (hL k (by omega))`. Use `⟨x', fun y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx', hx]`. Both sides reduce to the same expression.

Rewrite using `[chainPar_succ]`. Conclude with `hx'p`.
-/
theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) (hgap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ D.R.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU hgap c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

/- English proof (translation)
Consider the cases of `hR with`. Consider the case `zero => exact hs₀`. Consider the case `step _ hs' _ _ => exact hs'`.
-/
theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

/- English proof (translation)
Introduce `D hMet hPB hCL hSU hgap c hc s₀ hs₀ k hk s Θ hR`. Use `⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩` and prove the remaining obligations. Establish `hb` using `hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu`. Establish `hr : s₀.V.rank = D.R.r` using `by rw [hs₀.rank]; simp [Formalism.BasicNotions.Ranks.rankY]`. Rewrite `hb` using `[hr]`.

Conclude with `(thetaChain_upward_induction_fixed_metric hMet hSU hgap hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h`.
-/
theorem chainUp_of : ∀ D : D7, MetEx D → ParBoundW D → ChainLW D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU hgap c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = D.R.r := by rw [hs₀.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hgap hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

end GlobalTheory.ChainOnto

end
