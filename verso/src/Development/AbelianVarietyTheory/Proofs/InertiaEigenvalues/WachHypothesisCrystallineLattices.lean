import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.WachHyp

/- English proof (translation)
Introduce `e`. Apply `h` to reduce the goal to its premises. Unfold `FildR DdRE`. Rewrite using `[inf_right_comm, e, inf_right_comm]`.
-/
theorem jump_mem (S : LocalSituation.Sit) (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (h : IsJumpV S.PD T.ρ τ a) : a ∈ LocalSituation.Jset S T := by
  intro e
  apply h
  unfold FildR DdRE
  rw [inf_right_comm, e, inf_right_comm]

/- English proof (translation)
Introduce `τ i _ a ha`. Conclude with `Set.mem_Icc.2 (hj a (jump_mem S Y τ a ha))`.
-/
theorem jumpsLet_const (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    DeltaInvariantLattices.JumpsLet S.W Y (fun _ => M0) (fun _ => h0) := by
  intro τ i _ a ha
  exact Set.mem_Icc.2 (hj a (jump_mem S Y τ a ha))

/- English proof (translation)
Take `⟨⟨⟨r, b, hbN, huniq, hRW⟩, -⟩, -⟩` from `he Y hY`. Set `v : Fin r → ↥(S.W.N Y)` to `fun j => ⟨b j, hbN j⟩`. Establish `hli : LinearIndependent (LetA S.O S.n) v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Establish `h0 : ((∑ j, g j • v j : ↥(S.W.N Y)) : S.W.DD Y) = 0` using `by rw [hg]; rfl`. Establish `h0' : (0 : S.W.DD Y) = ∑ j, g j • b j`. Rewrite using `[← h0]`. Simplify using `[v]`. Take `⟨a, -, ha⟩` from `huniq 0 (S.W.N Y).zero_mem`.

Establish `e1` using `ha g h0'`. Establish `e2` using `ha (fun _ => 0) (by simp)`. Introduce `j`. Rewrite using `[e1, ← e2]`. Establish `hsp : ⊤ ≤ Submodule.span (LetA S.O S.n) (Set.range v)`.

Introduce and unpack `⟨x, hx⟩ -`. Take `⟨a, ha, -⟩` from `huniq x hx`. Establish `: (⟨x, hx⟩ : ↥(S.W.N Y)) = ∑ j, a j • v j`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[v, ha]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Use `⟨Fin r, inferInstance, Module.Basis.mk hli hsp, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.mk_apply, v]`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc`. Take `⟨a, -, ha⟩` from `hRW 0`. Establish `e1` using `ha c hc.symm`. Establish `e2` using `ha (fun _ => 0) (by simp)`. Introduce `j`.

Rewrite using `[e1, ← e2]`. Simplify using `only [Module.Basis.mk_apply, v]`. Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Take `⟨c, hc, -⟩` from `hRW y`.

Rewrite using `[hc]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`.
-/
theorem nBasis (S : LocalSituation.Sit) (E : S.Comparison₂) (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O)
    (hY : IsCrys S.PD Y.ρ) : LocalSituation.NBasis S E Y (S.W.N Y) := by
  obtain ⟨⟨⟨r, b, hbN, huniq, hRW⟩, -⟩, -⟩ := he Y hY
  let v : Fin r → ↥(S.W.N Y) := fun j => ⟨b j, hbN j⟩
  have hli : LinearIndependent (LetA S.O S.n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ((∑ j, g j • v j : ↥(S.W.N Y)) : S.W.DD Y) = 0 := by rw [hg]; rfl
    have h0' : (0 : S.W.DD Y) = ∑ j, g j • b j := by
      rw [← h0]; simp [v]
    obtain ⟨a, -, ha⟩ := huniq 0 (S.W.N Y).zero_mem
    have e1 := ha g h0'
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  have hsp : ⊤ ≤ Submodule.span (LetA S.O S.n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(S.W.N Y)) = ∑ j, a j • v j := by
      apply Subtype.ext
      simp [v, ha]
    rw [this]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Fin r, inferInstance, Module.Basis.mk hli hsp, ?_, ?_⟩
  · simp only [Module.Basis.mk_apply, v]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨a, -, ha⟩ := hRW 0
    have e1 := ha c hc.symm
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  · simp only [Module.Basis.mk_apply, v]
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, hc, -⟩ := hRW y
    rw [hc]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/- English proof (translation)
Establish `hf` using `h1 Y hY`. Establish `hp` using `h5 Y (fun _ => M0) (fun _ => h0) hY (jumpsLet_const S Y M0 h0 hj)`. Establish `hNl : ∀ i, S.W.Nl Y i ≤ S.W.N Y` using `fun i => by`. Rewrite using `[hf.1]`. Conclude with `le_iSup (fun j => S.W.Nl Y j) i`.

Use `⟨nBasis S E he Y hY, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[hf.1]`. Use `Submodule.iSup_induction (fun j => S.W.Nl Y j) (motive := fun x => S.W.Q ^ M0 • S.W.φD Y x ∈ S.W.N Y) hx ?_ ?_ ?_` and prove the remaining obligations. Introduce `j y hy`.

Conclude with `hp.1 (j + 1) y (by simpa using hy)`. Simplify using the standard rewrite rules. Introduce `y z hy hz`. Simplify using `only [map_add, smul_add]`. Conclude with `add_mem hy hz`.

Introduce `y hy`. Rewrite `hy` using `[hf.1]`. Use `Submodule.iSup_induction (fun j => S.W.Nl Y j) (motive := fun y => S.W.Q ^ h0 • y ∈ LocalSituation.phiSpan S Y (S.W.N Y)) hy ?_ ?_ ?_` and prove the remaining obligations. Introduce `j y hy`. Conclude with `Submodule.span_mono (Set.image_mono (hNl (j - 1))) (hp.2.1 j y hy)`.

Simplify using the standard rewrite rules. Introduce `y z hy hz`. Simplify using `only [smul_add]`. Conclude with `add_mem hy hz`. Introduce `g _ x hx`.

Conclude with `S.W.N_Γ Y _ x hx`. Introduce `g _ x hx`. Take `⟨y, hy, e⟩` from `S.W.N_π Y (S.W.resΓ g) x hx`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul (Ideal.subset_span rfl) hy`.

Introduce `f x hx`. Conclude with `S.W.map_N f hY hY x hx`.
-/
theorem wClauses (S : LocalSituation.Sit) (E : S.Comparison₂) (h1 : DeltaInvariantLattices.WachLatticeFree S.W) (h5 : DeltaInvariantLattices.P5W S.W)
    (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (hY : IsCrys S.PD Y.ρ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    LocalSituation.WClauses S E Y M0 h0 (S.W.N Y) := by
  have hf := h1 Y hY
  have hp := h5 Y (fun _ => M0) (fun _ => h0) hY (jumpsLet_const S Y M0 h0 hj)
  have hNl : ∀ i, S.W.Nl Y i ≤ S.W.N Y := fun i => by
    rw [hf.1]; exact le_iSup (fun j => S.W.Nl Y j) i
  refine ⟨nBasis S E he Y hY, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hf.1] at hx
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun x => S.W.Q ^ M0 • S.W.φD Y x ∈ S.W.N Y) hx ?_ ?_ ?_
    · intro j y hy
      exact hp.1 (j + 1) y (by simpa using hy)
    · simp
    · intro y z hy hz
      simp only [map_add, smul_add]
      exact add_mem hy hz
  · intro y hy
    rw [hf.1] at hy
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun y => S.W.Q ^ h0 • y ∈ LocalSituation.phiSpan S Y (S.W.N Y)) hy ?_ ?_ ?_
    · intro j y hy
      exact Submodule.span_mono (Set.image_mono (hNl (j - 1))) (hp.2.1 j y hy)
    · simp
    · intro y z hy hz
      simp only [smul_add]
      exact add_mem hy hz
  · intro g _ x hx
    exact S.W.N_Γ Y _ x hx
  · intro g _ x hx
    obtain ⟨y, hy, e⟩ := S.W.N_π Y (S.W.resΓ g) x hx
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hy
  · intro f x hx
    exact S.W.map_N f hY hY x hx

/- English proof (translation)
Introduce `D HW F Cm hU hE hC l _ K s LL h Y M0 h0 hY hj`. Establish `hT` using `hU.1 l K s LL h`. Conclude with `LocalSituation.HypW_of_rec (hC l K s LL h Y hY) hj (wClauses _ _ hT.1 hT.2.2.2.2.1 (hE.1 l K s LL h) Y M0 h0 hY hj)`.
-/
theorem hypW_crystalline : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  intro D HW F Cm hU hE hC l _ K s LL h Y M0 h0 hY hj
  have hT := hU.1 l K s LL h
  exact LocalSituation.HypW_of_rec (hC l K s LL h Y hY) hj
    (wClauses _ _ hT.1 hT.2.2.2.2.1 (hE.1 l K s LL h) Y M0 h0 hY hj)

end GlobalTheory.WachHyp
