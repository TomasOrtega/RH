import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in

/- English proof (translation)
Introduce `D X kv hg hEw hs m j`. Establish `hm` using `m.2`. Establish `hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2)` using `fun c hc => wInt_of_zmod X kv.1 hg hc`. Establish `hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2)`. Introduce `v hv`.

Rewrite using `[Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]`. Conclude with `hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)`. Establish `hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈ wInt X (D.naut.plGw kv.1 kv.2)`. Introduce `l`. Establish `h` using `Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)`.

Rewrite `h` using `[map_sub, apply_ite (sigA X.B.I), map_zero]`. Rewrite using `[Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]`. Distinguish the cases in `hl : l = m`. Simplify using `only [hl, if_true] at h ⊢`. Use `add_mem (hZ _ h) hs` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hl, if_false] at h ⊢`. Simplify using `using hZ _ h`. Unfold `symVec epsW`.

Rewrite using `[if_neg hEw]`. Unfold `GlobalTheory.SeeConjRead.flagV`. Distinguish the cases in `h1 : j.1 < D.R.rS`. Rewrite using `[dif_pos h1, if_neg (by omega), sub_zero]`. Conclude with `hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1`.

Rewrite using `[dif_neg h1]`. Distinguish the cases in `h2 : j.1 < D.R.rS + D.R.k`. Rewrite using `[dif_pos h2]`. Establish `e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val`. Apply the tactic sequence `rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega`.

Use `hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)` as an intermediate fact. Distinguish the cases in `h' : j.val = D.R.rS + D.R.k - 1 - m.val`. Rewrite using `[if_pos h']`. Rewrite `this` using `[if_pos (e.2 h')]`. Then use the resulting hypothesis. Rewrite using `[if_neg h']`.

Rewrite `this` using `[if_neg (fun hh => h' (e.1 hh))]`. Then use the resulting hypothesis. Rewrite using `[dif_neg h2]`. Distinguish the cases in `h4 : j.1 = D.R.rS + D.R.k`. Rewrite using `[dif_pos h4, if_neg (by omega), sub_zero]`. Conclude with `hS _ (X.weightVectorsIntegral m).1`.

Rewrite using `[dif_neg h4]`. Distinguish the cases in `h3 : j.1 < 2 * D.R.rS + D.R.k + 1`. Rewrite using `[dif_pos h3, if_neg (by omega), sub_zero]`. Conclude with `hS _ ((X.weightVectorsIntegral m).2.2 _).2.1`. Rewrite using `[dif_neg h3, if_neg (by omega), sub_zero, hA_zero_right']`.

Conclude with `zero_mem _`.
-/
theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, if_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, if_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [if_neg hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dif_neg h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [if_pos h']; rwa [if_pos (e.2 h')] at this
    · rw [if_neg h']; rwa [if_neg (fun hh => h' (e.1 hh))] at this
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4, if_neg (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dif_neg h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
