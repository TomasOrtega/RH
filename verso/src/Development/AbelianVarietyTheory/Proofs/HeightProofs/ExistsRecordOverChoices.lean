import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExOfPublished
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfTzRat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBaseOfRich
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ErrorDataOfNormGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsStagesWithDeltaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages

noncomputable section

namespace GlobalTheory.FinalJoin2

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
open GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.Pj Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.RunJoin
open GlobalTheory.Mem
open GlobalTheory.EX.OB

/- English proof (translation)
Use `⟨Real.exp (N * y + 2 * Real.log G), Real.exp_pos _, le_of_eq ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, div_one, ← Real.exp_mul, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.log_exp]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_window_start (N y G : ℝ) (hN : 0 < N) (hG : 0 < G) : ∃ Ds : ℝ, 0 < Ds ∧
    y ≤ Real.log ((Ds / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / N) * G ^ (-(2 : ℝ) / N)) := by
  refine ⟨Real.exp (N * y + 2 * Real.log G), Real.exp_pos _, le_of_eq ?_⟩
  rw [Nat.cast_one, div_one, ← Real.exp_mul, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.log_exp]
  field_simp
  ring

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨x0, hx0⟩` from `GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch`. Use `⟨x0, ?_⟩` and prove the remaining obligations. Introduce `s P q1 a b c Lv hs hx hP hG`. Take `⟨F, hfd, hrich, hsz⟩` from `exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)`. Take `⟨B, hB, hF, -⟩` from `exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)`.

Establish `hxp : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `hDel : (0 : ℚ) < (Delv s cD : ℚ)`. Establish `: 0 < Delv s cD` using `Nat.ceil_pos.2 (by positivity)`. Conclude with `this` after adjusting the coercions. Establish `hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK` using `(StdFrameObj.coordPre P Lv).level_split`.

Establish `key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧ (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1), (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧ ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.h …`. Introduce and unpack `Q rfl`. Use `⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩` and prove the remaining obligations. Establish `h' : l + 1 < P.R.k - 1` using `h`. Establish `a1` using `(hP.hc w).1 τ ⟨l, by omega⟩`.

Establish `a2` using `(hP.hc w).1 τ ⟨l + 1, h'⟩`. Use `(congrArg₂ (· - ·) a1 a2).trans ?_` and prove the remaining obligations. Establish `: P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1` using `by omega`. Simplify using `only [this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨letter, k1, k2, k3⟩` from `key B.toPre hB`. Take `⟨X, rfl, e1, e2, e3, e4⟩` from `GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3`. Use `clear key k1 k2 k3 letter`. Establish `hJ : JointQ X.toD7` using `jointQ_of_small_field X F (hB ▸ hrich) ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF`.

Establish `hE : Nonempty (ErrX X.toD7)` using `GlobalTheory.T.error_data_of_norm_generators X ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧ (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)`. Use `clear hF hrich hsz`. Take `⟨B, Cc, W, V, S, N, Gj⟩` from `X`. Consider the cases of `B`. Simplify using `only at hB`.

Substitute `hB` using the available equality. Use `set D := Stages.toD7 _ with hD`. Use `⟨D, hJ, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩` and prove the remaining obligations. Take `⟨L, l1, -, -, l4⟩` from `hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2 hP.card e2 (fun u => by`. Establish `e : (D.mem u).A.GamP = Lv.GamP` using `Cc.A_GamP u`.

Rewrite using `[e, hG, GamS, Real.log_exp]`. Use the proof step `rfl)`. Use the proof step `(fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4`. Conclude with `⟨L, l1, l4⟩`.
-/
theorem exists_record_over_choices (hR : GlobalTheory.NT.RayField) (eps cD ch : ℝ) (C : FC) (h0 : 0 < eps) (h1 : eps < 1 / 52)
    (hC : Std C) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ)
      (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P), s.eps = eps → x0 ≤ s.x →
      ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R →
      ∃ D : D7, JointQ D ∧ Nonempty (ErrX D) ∧ DV.KapDef D ∧ HostArith D.host ∧
        ∃ L : SizeData₂ D, L.sc = s ∧ Val C cD ch L := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv hs hx hP hG
  obtain ⟨F, hfd, hrich, hsz⟩ := exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)
  obtain ⟨B, hB, hF, -⟩ := exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hDel : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < Delv s cD := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (StdFrameObj.coordPre P Lv).level_split
  have key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1),
        (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧
      ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.hcW w τ).u ⟨l + 1, by omega⟩ =
        (Q.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv s cD : ℚ) else 0) := by
    rintro Q rfl
    refine ⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩
    have h' : l + 1 < P.R.k - 1 := h
    have a1 := (hP.hc w).1 τ ⟨l, by omega⟩
    have a2 := (hP.hc w).1 τ ⟨l + 1, h'⟩
    refine (congrArg₂ (· - ·) a1 a2).trans ?_
    have : P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1 := by omega
    simp only [this]
    push_cast
    ring
  obtain ⟨letter, k1, k2, k3⟩ := key B.toPre hB
  obtain ⟨X, rfl, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3
  clear key k1 k2 k3 letter
  have hJ : JointQ X.toD7 := jointQ_of_small_field X F (hB ▸ hrich)
    ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF
  have hE : Nonempty (ErrX X.toD7) := GlobalTheory.T.error_data_of_norm_generators X
    ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)
  clear hF hrich hsz
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  refine ⟨D, hJ, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩
  obtain ⟨L, l1, -, -, l4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2
    hP.card e2 (fun u => by
      have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
      rw [e, hG, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4
  exact ⟨L, l1, l4⟩

end GlobalTheory.FinalJoin2

end
