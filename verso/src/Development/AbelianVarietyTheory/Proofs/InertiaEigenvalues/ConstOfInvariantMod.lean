import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilInv

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Take `⟨Θ⟩` from `GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite `hg`, the goal using `[zero_add]`. Take `⟨y, hy, ey⟩` from `GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by`.

Establish `h` using `(theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg ⟨g, hg'⟩)`. Rewrite using `[P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 he), GlobalTheory.MemLoc.locAinf_actC] at h)` and apply the resulting hypothesis. Use `⟨⟨y, hy⟩, alg_mem_fil_zero K _, ?_⟩` and prove the remaining obligations. Rewrite using `[theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]`. Conclude with `(Θ.θ_Om y).symm`.

Take `⟨κ, -, -, h0, h⟩` from `graded_invariants TT Θ K n e he hg`. Rewrite `h` using `[h0 hn]`. Conclude with `⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rwa [map_zero]⟩`.
-/
theorem graded_const (TT : LocTied l P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil n ∧
      e - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil (n + 1) := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  by_cases hn : n = 0
  · subst hn
    rw [zero_add] at hg ⊢
    obtain ⟨y, hy, ey⟩ := GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by
      have h := (theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg ⟨g, hg'⟩)
      rwa [P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 he), GlobalTheory.MemLoc.locAinf_actC] at h)
    refine ⟨⟨y, hy⟩, alg_mem_fil_zero K _, ?_⟩
    rw [theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]
    exact (Θ.θ_Om y).symm
  · obtain ⟨κ, -, -, h0, h⟩ := graded_invariants TT Θ K n e he hg
    rw [h0 hn] at h
    exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rwa [map_zero]⟩

/- English proof (translation)
Introduce `l _ P AI TT K a b x hx hg`. Establish `hFa : Antitone fun a => (P.PD K).Fil a` using `antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a`. Establish `h0 : ∀ m, m ≤ a → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m` using `fun m hm => ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact hFa hm hx⟩`. Break down `le_total b a with hba | hab` into its components or cases. Conclude with `h0 b hba`.

Establish `key : ∀ m, a ≤ m → m ≤ b → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m`. Introduce `m hm`. Proceed by induction on `m, hm using Int.le_induction with`. Consider the case `base => exact fun _ => h0 a le_rfl`. Consider the case `succ m hm ih`.

Introduce `hmb`. Take `⟨c, hc, hxc⟩` from `ih (by omega)`. Take `⟨d, hd, hxd⟩` from `graded_const TT K m _ hxc (fun g => by`. Rewrite using `[map_sub, AlgEquiv.commutes, sub_sub_sub_cancel_right]`. Conclude with `hFa hmb (hg g))`.

Use `⟨c + d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hc (hFa hm hd)`. Rewrite using `[map_add, ← sub_sub]` and apply the resulting hypothesis. Conclude with `key b hab le_rfl`.
-/
theorem const_of_invariant_mod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a → (∀ g, (P.PD K).actdR g x - x ∈ (P.PD K).Fil b) → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil b := by
  intro l _ P AI TT K a b x hx hg
  have hFa : Antitone fun a => (P.PD K).Fil a :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have h0 : ∀ m, m ≤ a → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := fun m hm =>
    ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact hFa hm hx⟩
  rcases le_total b a with hba | hab
  · exact h0 b hba
  have key : ∀ m, a ≤ m → m ≤ b → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := by
    intro m hm
    induction m, hm using Int.le_induction with
    | base => exact fun _ => h0 a le_rfl
    | succ m hm ih =>
      intro hmb
      obtain ⟨c, hc, hxc⟩ := ih (by omega)
      obtain ⟨d, hd, hxd⟩ := graded_const TT K m _ hxc (fun g => by
        rw [map_sub, AlgEquiv.commutes, sub_sub_sub_cancel_right]
        exact hFa hmb (hg g))
      refine ⟨c + d, ?_, ?_⟩
      · rw [map_add]
        exact Submodule.add_mem _ hc (hFa hm hd)
      · rwa [map_add, ← sub_sub]
  exact key b hab le_rfl

end GlobalTheory.FilInv
