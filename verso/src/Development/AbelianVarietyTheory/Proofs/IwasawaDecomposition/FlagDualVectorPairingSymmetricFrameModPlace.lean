import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

/- English proof (translation)
Introduce `D X w k hg a j`. Establish `hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i))`. Introduce `i`. Unfold `GlobalTheory.Mem.SymFrame.epsW`. Use `split_ifs`.

Conclude with `((X.weightVectorsIntegral _).2.2 a).2.1`. Conclude with `((X.weightVectorsIntegral _).2.2 a).2.2.2`. Use `wInt_of_zmod X k hg ?_` and prove the remaining obligations. Establish `ha` using `a.2`. Establish `hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1` using `rfl`.

Unfold `GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV`. Distinguish the cases in `h1 : j.1 < D.R.rS`. Rewrite using `[dif_pos h1]`. Establish `h` using `Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2`. Rewrite `h` using `[map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]`.

Distinguish the cases in `e : j = GlobalTheory.Mem.SymChar.Resid.posE D a`. Rewrite using `[if_pos e]`. Rewrite `h` using `[if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one]`. Then use the resulting hypothesis. Rewrite using `[if_neg e]`. Rewrite `h` using `[if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))), map_zero]`. Then use the resulting hypothesis.

Rewrite using `[dif_neg h1]`. Establish `hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[hpos]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg hne, sub_zero]`. Distinguish the cases in `h2 : j.1 < D.R.rS + D.R.k`. Rewrite using `[dif_pos h2]`. Conclude with `hW _`. Rewrite using `[dif_neg h2]`.

Distinguish the cases in `h4 : j.1 = D.R.rS + D.R.k`. Rewrite using `[dif_pos h4]`. Conclude with `(X.formsAtZero.2 a).2`. Rewrite using `[dif_neg h4]`. Distinguish the cases in `h3 : j.1 < 2 * D.R.rS + D.R.k + 1`.

Rewrite using `[dif_pos h3]`. Conclude with `(X.gramIntegral a _).2.1`. Rewrite using `[dif_neg h3, hA_zero_right']`. Conclude with `⟨0, zero_mem _, by simp⟩`.
-/
theorem hA_symVec_sub_ite_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg a j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 a).2.1
    · exact ((X.weightVectorsIntegral _).2.2 a).2.2.2
  refine wInt_of_zmod X k hg ?_
  have ha := a.2
  have hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1 := rfl
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1]
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2
    rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm] at h
    by_cases e : j = GlobalTheory.Mem.SymChar.Resid.posE D a
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))),
        map_zero] at h
  rw [dif_neg h1]
  have hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a := fun e => by
    have := congrArg Fin.val e; rw [hpos] at this; omega
  rw [if_neg hne, sub_zero]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2]; exact hW _
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4]; exact (X.formsAtZero.2 a).2
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3]; exact (X.gramIntegral a _).2.1
  · rw [dif_neg h3, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
