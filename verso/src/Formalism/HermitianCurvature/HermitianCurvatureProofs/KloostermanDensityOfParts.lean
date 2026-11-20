import Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniHeadLastPart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerAveragingInputOfSliceData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragingVanishes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting

open Matrix MeasureTheory Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ.Asm

section decay

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Take `⟨hs, hc, _⟩` from `hΨ`. Take `⟨R, hR⟩` from `hc.isCompact.isBounded.exists_norm_le`. Establish `hM : ∀ i : ℕ, ∃ M : ℝ, ∀ Z, ‖iteratedFDeriv ℝ i Ψ Z‖ ≤ M` using `fun i => (hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support (hc.iteratedFDeriv i)`. Use `choose M hM using hM`. Use `set Mt : ℝ := ∑ i ∈ Finset.range (q + 1), max (M i) 0 with hMt`.

Establish `hMt0 : 0 ≤ Mt` using `Finset.sum_nonneg fun i _ => le_max_right _ _`. Establish `hMi : ∀ i ≤ q, M i ≤ Mt` using `fun i hi => le_trans (le_max_left _ _) (Finset.single_le_sum (f := fun i => max (M i) 0) (fun i _ => le_max_right _ _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))`. Use `set R' : ℝ := max R 0`. Use `⟨Mt * (1 + R') ^ E, hs.of_le (by exact_mod_cast le_top), fun i hi Z => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hZ : Z ∈ tsupport Ψ`.

Establish `hZR : ‖Z‖ ≤ R'` using `le_trans (hR Z hZ) (le_max_left _ _)`. Establish `h1 : 0 < 1 + ‖Z‖` using `by positivity`. Establish `h2 : (1 + ‖Z‖) ^ E ≤ (1 + R') ^ E` using `Real.rpow_le_rpow h1.le (by linarith) hE`. Establish `h3 : 0 < (1 + ‖Z‖) ^ E` using `Real.rpow_pos_of_pos h1 E`. Rewrite using `[Real.rpow_neg h1.le]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (inv_nonneg.2 h3.le)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left h2 hMt0`. Establish `h0 : iteratedFDeriv ℝ i Ψ Z = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hZ (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))`. Rewrite using `[h0, norm_zero]`. Establish `: 0 < 1 + ‖Z‖` using `by positivity`. Check the signs of the components of the expression.
-/
theorem decayAll_of_cls {n : ℕ} (Ψ : G.Mat n → V) (hΨ : KCls Ψ) (q : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, U.DecayAll q (fun _ => E) K Ψ := by
  obtain ⟨hs, hc, _⟩ := hΨ
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  have hM : ∀ i : ℕ, ∃ M : ℝ, ∀ Z, ‖iteratedFDeriv ℝ i Ψ Z‖ ≤ M := fun i =>
    (hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  choose M hM using hM
  set Mt : ℝ := ∑ i ∈ Finset.range (q + 1), max (M i) 0 with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hMi : ∀ i ≤ q, M i ≤ Mt := fun i hi =>
    le_trans (le_max_left _ _) (Finset.single_le_sum (f := fun i => max (M i) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  set R' : ℝ := max R 0
  refine ⟨Mt * (1 + R') ^ E, hs.of_le (by exact_mod_cast le_top), fun i hi Z => ?_⟩
  by_cases hZ : Z ∈ tsupport Ψ
  · have hZR : ‖Z‖ ≤ R' := le_trans (hR Z hZ) (le_max_left _ _)
    have h1 : 0 < 1 + ‖Z‖ := by positivity
    have h2 : (1 + ‖Z‖) ^ E ≤ (1 + R') ^ E := Real.rpow_le_rpow h1.le (by linarith) hE
    have h3 : 0 < (1 + ‖Z‖) ^ E := Real.rpow_pos_of_pos h1 E
    rw [Real.rpow_neg h1.le]
    calc ‖iteratedFDeriv ℝ i Ψ Z‖ ≤ Mt := le_trans (hM i Z) (hMi i hi)
      _ = Mt * (1 + ‖Z‖) ^ E * ((1 + ‖Z‖) ^ E)⁻¹ := by field_simp
      _ ≤ Mt * (1 + R') ^ E * ((1 + ‖Z‖) ^ E)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 h3.le)
          exact mul_le_mul_of_nonneg_left h2 hMt0
  · have h0 : iteratedFDeriv ℝ i Ψ Z = 0 := by
      by_contra hne
      exact hZ (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
    rw [h0, norm_zero]
    have : 0 < 1 + ‖Z‖ := by positivity
    positivity

end decay

section points

/- English proof (translation)
Simplify using `[D.ptSize, List.map_append, List.sum_append]`.
-/
theorem ptSize_append (h rest : C.LPt) : D.ptSize (h ++ rest) = D.ptSize h + D.ptSize rest := by
  simp [D.ptSize, List.map_append, List.sum_append]

/- English proof (translation)
Simplify using `[D.ptSize]`.
-/
theorem ptSize_single (b : ℕ × ℂ) : D.ptSize [b] = b.1 := by simp [D.ptSize]

/- English proof (translation)
Proceed by induction on `h generalizing a b with`. Consider the case `nil => simp [D.ptSize]`. Consider the case `cons x h ih`. Take `⟨s, t⟩` from `x`. Establish `hS : D.ptSize ((s, t) :: h) = s + D.ptSize h` using `by simp [D.ptSize]`.

Rewrite using `[hS]`. Simplify using `only [List.cons_append, D.ptEntry]`. Rewrite using `[ih]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)`.
-/
theorem ptEntry_append (h rest : C.LPt) (a b : ℕ) :
    D.ptEntry (h ++ rest) a b =
      if a < D.ptSize h ∧ b < D.ptSize h then D.ptEntry h a b
      else if D.ptSize h ≤ a ∧ D.ptSize h ≤ b then D.ptEntry rest (a - D.ptSize h) (b - D.ptSize h) else 0 := by
  induction h generalizing a b with
  | nil => simp [D.ptSize]
  | cons x h ih =>
    obtain ⟨s, t⟩ := x
    have hS : D.ptSize ((s, t) :: h) = s + D.ptSize h := by simp [D.ptSize]
    rw [hS]
    simp only [List.cons_append, D.ptEntry]
    rw [ih]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)

/- English proof (translation)
Use extensionality with `i j`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`.

Rewrite using `[Dx2.SL.b_cc]`. Simplify using `only [D.ptMatN]`. Rewrite using `[ptEntry_append, if_pos ⟨by simp, by simp⟩]; rfl`. Consider the case `right j`. Rewrite using `[Dx2.SL.b_cn]`.

Simplify using `only [D.ptMatN, Matrix.zero_apply]`. Rewrite using `[ptEntry_append, if_neg (by simp), if_neg (by simp)]`. Consider the case `right i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`.

Rewrite using `[Dx2.SL.b_nc]`. Simplify using `only [D.ptMatN, Matrix.zero_apply]`. Rewrite using `[ptEntry_append, if_neg (by simp), if_neg (by simp)]`. Consider the case `right j`. Rewrite using `[Dx2.SL.b_nn]`.

Simplify using `only [D.ptMatN]`. Rewrite using `[ptEntry_append, if_neg (by simp), if_pos ⟨by simp, by simp⟩]`. Simplify using the standard rewrite rules.
-/
theorem ptMatN_append (h rest : C.LPt) :
    D.ptMatN (h ++ rest) (D.ptSize h + D.ptSize rest) =
      U.blk2 (D.ptMatN h (D.ptSize h)) 0 0 (D.ptMatN rest (D.ptSize rest)) := by
  ext i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_cc]; simp only [D.ptMatN]
      rw [ptEntry_append, if_pos ⟨by simp, by simp⟩]; rfl
    | right j =>
      rw [Dx2.SL.b_cn]; simp only [D.ptMatN, Matrix.zero_apply]
      rw [ptEntry_append, if_neg (by simp), if_neg (by simp)]
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_nc]; simp only [D.ptMatN, Matrix.zero_apply]
      rw [ptEntry_append, if_neg (by simp), if_neg (by simp)]
    | right j =>
      rw [Dx2.SL.b_nn]; simp only [D.ptMatN]
      rw [ptEntry_append, if_neg (by simp), if_pos ⟨by simp, by simp⟩]
      simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [D.ptMatN, D.ptEntry, G.ptLong, G.wMat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[if_pos ⟨i.isLt, j.isLt⟩]`. Establish `: (j = i.rev) ↔ (i.val + j.val + 1 = s)`. Rewrite using `[Fin.ext_iff, Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : i.val + j.val + 1 = s`. Rewrite using `[if_pos h, if_pos (this.2 h), mul_one]`. Rewrite using `[if_neg h, if_neg (fun e => h (this.1 e)), mul_zero]`.
-/
theorem ptMatN_long (s : ℕ) (t : ℂ) : D.ptMatN [(s, t)] s = G.ptLong s t := by
  ext i j
  simp only [D.ptMatN, D.ptEntry, G.ptLong, G.wMat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [if_pos ⟨i.isLt, j.isLt⟩]
  have : (j = i.rev) ↔ (i.val + j.val + 1 = s) := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  by_cases h : i.val + j.val + 1 = s
  · rw [if_pos h, if_pos (this.2 h), mul_one]
  · rw [if_neg h, if_neg (fun e => h (this.1 e)), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `hi : i.val = 0` using `by omega`. Establish `hj : j.val = 0` using `by omega`. Simplify using `[D.ptMatN, D.ptEntry, hi]`.
-/
theorem ptMatN_one (c : ℂ) : D.ptMatN [(1, c)] 1 = Matrix.of fun _ _ => c := by
  ext i j
  have hi : i.val = 0 := by omega
  have hj : j.val = 0 := by omega
  simp [D.ptMatN, D.ptEntry, hi]

/- English proof (translation)
Use extensionality with `i j`. Establish `: i = j` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Simplify using `[U.hMat, U.wP]`.
-/
theorem hMat_one_single (c : ℂ) : U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c) = Matrix.of fun _ _ => c := by
  ext i j
  have : i = j := Subsingleton.elim _ _
  subst this
  simp [U.hMat, U.wP]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply, G.ptLong, G.wMat, Matrix.smul_apply, smul_eq_mul, Fin.revPerm_apply]`. Distinguish the cases in `h : i.rev = j`. Rewrite using `[if_pos h, if_pos h.symm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg h, if_neg (fun e => h e.symm)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hMat_rev (n : ℕ) (t : ℂ) : U.hMat (Fin.revPerm : Equiv.Perm (Fin n)) (fun _ => t) = G.ptLong n t := by
  ext i j
  simp only [U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply, G.ptLong, G.wMat, Matrix.smul_apply,
    smul_eq_mul, Fin.revPerm_apply]
  by_cases h : i.rev = j
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun e => h e.symm)]; ring

/- English proof (translation)
Unfold `G.ptBlock G.blk U.blk2 G.ptLong`. Use `congr 2`.
-/
theorem ptBlock_eq (n : ℕ) (t c : ℂ) :
    G.ptBlock n t c = U.blk2 (G.ptLong n t) 0 0 (Matrix.of fun _ _ => c) := by
  unfold G.ptBlock G.blk U.blk2 G.ptLong
  congr 2

/- English proof (translation)
Establish `h` using `ptMatN_append [(m + 1, t)] [(1, c)]`. Establish `e1 : D.ptMatN [(m + 1, t)] (D.ptSize [(m + 1, t)]) = G.ptLong (m + 1) t` using `ptMatN_long (m + 1) t`. Establish `e2 : D.ptMatN [(1, c)] (D.ptSize [(1, c)]) = Matrix.of fun _ _ => c` using `ptMatN_one c`. Rewrite `h` using `[e1, e2]`. Rewrite using `[ptBlock_eq]`.

Conclude with `h`.
-/
theorem ptMatN_block (m : ℕ) (t c : ℂ) :
    D.ptMatN [(m + 1, t), (1, c)] (m + 1 + 1) = G.ptBlock (m + 1) t c := by
  have h := ptMatN_append [(m + 1, t)] [(1, c)]
  have e1 : D.ptMatN [(m + 1, t)] (D.ptSize [(m + 1, t)]) = G.ptLong (m + 1) t := ptMatN_long (m + 1) t
  have e2 : D.ptMatN [(1, c)] (D.ptSize [(1, c)]) = Matrix.of fun _ _ => c := ptMatN_one c
  rw [e1, e2] at h
  rw [ptBlock_eq]; exact h

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `nil => intro i hi`. Simplify using `[D.ptSize] at hi`. Consider the case `cons x a ih`. Take `⟨s, t⟩` from `x`.

Introduce `i hi`. Simplify using `only [D.ptScal]`. Establish `hS : D.ptSize ((s, t) :: a) = s + D.ptSize a` using `by simp [D.ptSize]`. Use `split_ifs with h`. Conclude with `(ha (s, t) List.mem_cons_self).2`.

Conclude with `ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ (by omega)`.
-/
theorem ptScal_ne (a : C.LPt) (ha : ∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) : ∀ i < D.ptSize a, D.ptScal a i ≠ 0 := by
  induction a with
  | nil => intro i hi; simp [D.ptSize] at hi
  | cons x a ih =>
    obtain ⟨s, t⟩ := x
    intro i hi
    simp only [D.ptScal]
    have hS : D.ptSize ((s, t) :: a) = s + D.ptSize a := by simp [D.ptSize]
    split_ifs with h
    · exact (ha (s, t) List.mem_cons_self).2
    · exact ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ (by omega)

/- English proof (translation)
Use `⟨D.ptPerm a, D.ptDiag a, fun i => ptScal_ne a ha i i.isLt, ?_⟩` and prove the remaining obligations. Conclude with `((Formalism.FourierDecayAlt.P.ptPerm_spec a (D.ptSize a) ⟨ha, rfl⟩).2.2).symm`.
-/
theorem exists_hMat (a : C.LPt) (ha : ∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin (D.ptSize a))) (d : Fin (D.ptSize a) → ℂ), (∀ i, d i ≠ 0) ∧
      U.hMat σ d = D.ptMatN a (D.ptSize a) := by
  refine ⟨D.ptPerm a, D.ptDiag a, fun i => ptScal_ne a ha i i.isLt, ?_⟩
  exact ((Formalism.FourierDecayAlt.P.ptPerm_spec a (D.ptSize a) ⟨ha, rfl⟩).2.2).symm

end points

section one

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/- English proof (translation)
Establish `: IsEmpty (U.LW σ)` using `⟨fun q => by`. Take `⟨⟨a, b⟩, h, _⟩` from `q`. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Establish `hb : b = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality.

Substitute `hb` using the available equality. Conclude with `lt_irrefl _ h⟩`. Establish `: IsEmpty (G.UT 1)` using `⟨fun q => by`. Take `⟨⟨a, b⟩, h⟩` from `q`. Establish `ha : a = 0` using `Subsingleton.elim _ _`.

Establish `hb : b = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality. Substitute `hb` using the available equality. Conclude with `lt_irrefl _ h⟩`. Establish `hs : Subsingleton (U.XiH 1 0 σ)` using `by unfold U.XiH; infer_instance`.

Establish `hvol : (volume : Measure (U.XiH 1 0 σ)) Set.univ = 1`. Unfold `U.XiH`. Rewrite using `[Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, Measure.volume_eq_prod, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]`. Simplify using `[MeasureTheory.volume_pi, Measure.pi_univ]`. Set `η0 : U.XiH 1 0 σ` to `((fun i => i.elim0, fun _ j => j.elim0), (fun q => isEmptyElim q, fun q => isEmptyElim q))`.

Unfold `U.PhiTop U.muXiH`. Establish `hf : (fun η : U.XiH 1 0 σ => U.psiH β σ η • Φ (U.ZjH σ d η (fun x => x.elim0))) = fun _ => U.psiH β σ η0 • Φ (U.ZjH σ d η0 (fun x => x.elim0))` using `funext fun η => by rw [Subsingleton.elim η η0]`. Rewrite using `[hf, integral_const]`. Simplify using `only [Measure.real, hvol, ENNReal.toReal_one, one_smul]`. Establish `hpsi : U.psiH β σ η0 = 1` using `by simp [U.psiH, U.subS, U.supS, U.cornerA, U.cornerB, G.psi]`.

Simplify using `only [hpsi, one_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i j`. Establish `hi : i = Fin.castAdd 0 0` using `Fin.ext (by have := i.isLt; simp)`. Establish `hj : j = Fin.castAdd 0 0` using `Fin.ext (by have := j.isLt; simp)`.

Substitute `hi` using the available equality. Substitute `hj` using the available equality. Establish `hσ : σ = 1` using `Subsingleton.elim _ _`. Substitute `hσ` using the available equality. Rewrite using `[U.ZjH, Formalism.FourierDecayAlt.P.level_z_affine, Dx2.SL.b_cc]`.

Simplify using `[U.headH, U.lowW, G.upper, U.wP, Matrix.mul_apply, G.strictUpper]`.
-/
theorem phiTop_one (β : ℂ) (σ : Equiv.Perm (Fin 1)) (d : Fin 1 → ℂ) (Φ : G.Mat 1 → V) :
    U.PhiTop (p := 1) (s := 0) β σ d Φ (fun x => x.elim0) = Φ (fun _ _ => d 0) := by
  have : IsEmpty (U.LW σ) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h, _⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb; exact lt_irrefl _ h⟩
  have : IsEmpty (G.UT 1) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb; exact lt_irrefl _ h⟩
  have hs : Subsingleton (U.XiH 1 0 σ) := by unfold U.XiH; infer_instance
  have hvol : (volume : Measure (U.XiH 1 0 σ)) Set.univ = 1 := by
    unfold U.XiH
    rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, Measure.volume_eq_prod,
      Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [MeasureTheory.volume_pi, Measure.pi_univ]
  let η0 : U.XiH 1 0 σ := ((fun i => i.elim0, fun _ j => j.elim0), (fun q => isEmptyElim q, fun q => isEmptyElim q))
  unfold U.PhiTop U.muXiH
  have hf : (fun η : U.XiH 1 0 σ => U.psiH β σ η • Φ (U.ZjH σ d η (fun x => x.elim0))) =
      fun _ => U.psiH β σ η0 • Φ (U.ZjH σ d η0 (fun x => x.elim0)) := funext fun η => by rw [Subsingleton.elim η η0]
  rw [hf, integral_const]
  simp only [Measure.real, hvol, ENNReal.toReal_one, one_smul]
  have hpsi : U.psiH β σ η0 = 1 := by simp [U.psiH, U.subS, U.supS, U.cornerA, U.cornerB, G.psi]
  simp only [hpsi, one_smul]
  congr 1
  funext i j
  have hi : i = Fin.castAdd 0 0 := Fin.ext (by have := i.isLt; simp)
  have hj : j = Fin.castAdd 0 0 := Fin.ext (by have := j.isLt; simp)
  subst hi; subst hj
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  rw [U.ZjH, Formalism.FourierDecayAlt.P.level_z_affine, Dx2.SL.b_cc]
  simp [U.headH, U.lowW, G.upper, U.wP, Matrix.mul_apply, G.strictUpper]

end one

section germ

/- English proof (translation)
Take `⟨C₁, C₂, hUG⟩` from `Formalism.FourierDecayAlt.P.germ_expansion_top_level`. Use `set Nr : ℝ := ((p + (m + 1 + 1) : ℕ) : ℝ) with hNr`. Establish `hN0 : 0 < 5 * Nr` using `by rw [hNr]; positivity`. Use `set A : ℝ := (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 with hA`. Use `set E : ℝ := 5 * Nr * (|A| + 2 * Nr ^ 2 + 1) with hEdef`.

Establish `hEq : E / (5 * Nr) = |A| + 2 * Nr ^ 2 + 1`. Establish `hNr0 : Nr ≠ 0` using `by intro h0; rw [h0] at hN0; simp at hN0`. Rewrite using `[hEdef]`. Clear the denominators using the available nonvanishing facts. Establish `hE0 : 0 ≤ E` using `by rw [hEdef]; positivity`.

Establish `hE : ∀ i ≤ C₂ * (m + 2) ^ 2, A ≤ (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) ∧ 2 * ((p + (m + 1 + 1) : ℕ) : ℝ) ^ 2 < (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ))`. Introduce `i _`. Simplify using `only`. Rewrite using `[← hNr, hEq]`. Prove the components needed by the constructor for the conclusion.

Use `le_abs_self A` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg Nr]`. Use `abs_nonneg A` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set Dd : ℂ := (-1) ^ (m + 3) * t0 ^ (m + 2) with hDd`.

Establish `hDd0 : Dd ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht0)`. Establish `hK0 : (0 : ℂ) ∉ ({Dd} : Set ℂ)` using `fun h => hDd0 (Set.mem_singleton_iff.1 h).symm`. Take `⟨Cst, hC⟩` from `hUG p m β hβ σh dh hdh (fun _ => E) A le_rfl hE {Dd} isCompact_singleton hK0`. Take `⟨K, hK⟩` from `decayAll_of_cls Ψ hΨ (C₂ * (m + 2) ^ 2) E hE0`. Use `set Φ := U.PhiTop (p := p) (s := m + 1 + 1) β σh dh Ψ with hΦ`.

Establish `hz0 : t0 ^ (m + 2) = (-1) ^ (m + 3) * Dd`. Rewrite using `[hDd, ← mul_assoc, ← pow_add]`. Establish `: ((-1 : ℂ)) ^ (m + 3 + (m + 3)) = 1`. Rewrite using `[← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[this, one_mul]`. Establish `hbound : ∀ x : ℂ, x ≠ 0 → ‖G.mainTerm β m (fun _ => 1) Φ x⁻¹ Dd‖ ≤ Cst * K * ‖x‖⁻¹`. Introduce `x hx`. Establish `ht : x⁻¹ ≠ 0` using `inv_ne_zero hx`. Establish `hct : Dd / x⁻¹ ^ (m + 1) * x⁻¹ ^ (m + 1) = Dd` using `div_mul_cancel₀ _ (pow_ne_zero _ ht)`.

Establish `hc : Dd / x⁻¹ ^ (m + 1) ≠ 0` using `div_ne_zero hDd0 (pow_ne_zero _ ht)`. Establish `hb` using `hC V Ψ K hK x⁻¹ (Dd / x⁻¹ ^ (m + 1)) ht (by rw [hct]; exact Set.mem_singleton _)`. Unfold `G.remainder at hb`. Rewrite `hb` using `[← hΦ, hvan _ _ ht hc, smul_zero, zero_sub, norm_neg, hct, norm_inv]`. Conclude with `hb`.

Establish `hs : 0 < m + 2` using `by omega`. Establish `hm2 : ((m : ℂ) + 2) ≠ 0`. Establish `h : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h]; exact_mod_cast (by omega : m + 2 ≠ 0)`. Use `set R := G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd) with hRdef`.

Establish `hz₀ : t0 ∈ R` using `(Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).2 hz0`. Set `e : Fin R.card ≃ R` to `R.equivFin.symm`. Set `w : Fin R.card → ℂ` to `fun i => ((m : ℂ) + 2) * (e i : ℂ)`. Establish `hw : Function.Injective w`. Introduce `i j hij`.

Establish `h1 : (e i : ℂ) = (e j : ℂ)` using `mul_left_cancel₀ hm2 hij`. Conclude with `e.injective (Subtype.ext h1)`. Use `set κ : ℂ := ((m : ℂ) + 2)⁻¹ * ((‖t0‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) with hκ`. Establish `hκne : κ ≠ 0`. Use `mul_ne_zero (inv_ne_zero hm2) ?_` and prove the remaining obligations.

Conclude with `pow_ne_zero _ (norm_ne_zero_iff.2 ht0)` after adjusting the coercions. Establish `hκpos : 0 < ‖κ‖` using `norm_pos_iff.2 hκne`. Establish `havg` using `Formalism.FourierDecayAlt.P.averaging_vanishes β hβ V (normSeminorm ℂ V) R.card w (fun i => G.OmLong β (m + 1) Φ (e i)) (‖κ‖⁻¹ * (Cst * K)) 1 hw (by`. Introduce `x hx`. Establish `hxpos : 0 < ‖x‖` using `lt_of_lt_of_le one_pos hx`.

Establish `hx0 : x ≠ 0` using `norm_pos_iff.1 hxpos`. Establish `hb` using `hbound x hx0`. Rewrite `hb` using `[Formalism.FourierDecayAlt.P.germ_leading_term_root_sum β m Φ x⁻¹ Dd t0 hz0, norm_smul]`. Establish `hsum : (∑ j : Fin R.card, G.psi β (w j * x) • G.OmLong β (m + 1) Φ (e j)) = ∑ z ∈ R, G.psi β (((m : ℂ) + 2) * z / x⁻¹) • G.OmLong β (m + 1) Φ z`. Rewrite using `[← Finset.sum_coe_sort R, ← Equiv.sum_comp e]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [w, div_inv_eq_mul]`. Simplify using `only [coe_normSeminorm]`. Rewrite using `[hsum]`. Establish `h3 : ‖∑ z ∈ R, G.psi β (((m : ℂ) + 2) * z / x⁻¹) • G.OmLong β (m + 1) Φ z‖ ≤ ‖κ‖⁻¹ * (Cst * K * ‖x‖⁻¹)`.

Rewrite using `[le_inv_mul_iff₀ hκpos]`. Conclude with `hb`. Use `le_trans h3 (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Use the proof step `ring)`.

Establish `h0` using `havg (e.symm ⟨t0, hz₀⟩)`. Simplify using `only [coe_normSeminorm, Equiv.apply_symm_apply, norm_eq_zero] at h0`. Conclude with `h0`.
-/
theorem germ_step (β : ℂ) (hβ : β ≠ 0) (p m : ℕ) (σh : Equiv.Perm (Fin p)) (dh : Fin p → ℂ)
    (hdh : ∀ i, dh i ≠ 0) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + (m + 1 + 1)) → V) (hΨ : KCls Ψ)
    (hvan : ∀ t c : ℂ, t ≠ 0 → c ≠ 0 →
      G.OmBlock β (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) β σh dh Ψ) t c = 0)
    (t0 : ℂ) (ht0 : t0 ≠ 0) :
    G.OmLong β (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) β σh dh Ψ) t0 = 0 := by
  obtain ⟨C₁, C₂, hUG⟩ := Formalism.FourierDecayAlt.P.germ_expansion_top_level
  set Nr : ℝ := ((p + (m + 1 + 1) : ℕ) : ℝ) with hNr
  have hN0 : 0 < 5 * Nr := by rw [hNr]; positivity
  set A : ℝ := (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 with hA
  set E : ℝ := 5 * Nr * (|A| + 2 * Nr ^ 2 + 1) with hEdef
  have hEq : E / (5 * Nr) = |A| + 2 * Nr ^ 2 + 1 := by
    have hNr0 : Nr ≠ 0 := by intro h0; rw [h0] at hN0; simp at hN0
    rw [hEdef]; field_simp
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hE : ∀ i ≤ C₂ * (m + 2) ^ 2, A ≤ (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) ∧
      2 * ((p + (m + 1 + 1) : ℕ) : ℝ) ^ 2 < (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) := by
    intro i _
    simp only
    rw [← hNr, hEq]
    constructor
    · have := le_abs_self A; nlinarith [sq_nonneg Nr]
    · have := abs_nonneg A; linarith
  set Dd : ℂ := (-1) ^ (m + 3) * t0 ^ (m + 2) with hDd
  have hDd0 : Dd ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht0)
  have hK0 : (0 : ℂ) ∉ ({Dd} : Set ℂ) := fun h => hDd0 (Set.mem_singleton_iff.1 h).symm
  obtain ⟨Cst, hC⟩ := hUG p m β hβ σh dh hdh (fun _ => E) A le_rfl hE {Dd} isCompact_singleton hK0
  obtain ⟨K, hK⟩ := decayAll_of_cls Ψ hΨ (C₂ * (m + 2) ^ 2) E hE0
  set Φ := U.PhiTop (p := p) (s := m + 1 + 1) β σh dh Ψ with hΦ
  have hz0 : t0 ^ (m + 2) = (-1) ^ (m + 3) * Dd := by
    rw [hDd, ← mul_assoc, ← pow_add]
    have : ((-1 : ℂ)) ^ (m + 3 + (m + 3)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, one_mul]

  have hbound : ∀ x : ℂ, x ≠ 0 → ‖G.mainTerm β m (fun _ => 1) Φ x⁻¹ Dd‖ ≤ Cst * K * ‖x‖⁻¹ := by
    intro x hx
    have ht : x⁻¹ ≠ 0 := inv_ne_zero hx
    have hct : Dd / x⁻¹ ^ (m + 1) * x⁻¹ ^ (m + 1) = Dd := div_mul_cancel₀ _ (pow_ne_zero _ ht)
    have hc : Dd / x⁻¹ ^ (m + 1) ≠ 0 := div_ne_zero hDd0 (pow_ne_zero _ ht)
    have hb := hC V Ψ K hK x⁻¹ (Dd / x⁻¹ ^ (m + 1)) ht (by rw [hct]; exact Set.mem_singleton _)
    unfold G.remainder at hb
    rw [← hΦ, hvan _ _ ht hc, smul_zero, zero_sub, norm_neg, hct, norm_inv] at hb
    exact hb

  have hs : 0 < m + 2 := by omega
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by
    have h : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [h]; exact_mod_cast (by omega : m + 2 ≠ 0)
  set R := G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd) with hRdef
  have hz₀ : t0 ∈ R := (Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).2 hz0
  let e : Fin R.card ≃ R := R.equivFin.symm
  let w : Fin R.card → ℂ := fun i => ((m : ℂ) + 2) * (e i : ℂ)
  have hw : Function.Injective w := by
    intro i j hij
    have h1 : (e i : ℂ) = (e j : ℂ) := mul_left_cancel₀ hm2 hij
    exact e.injective (Subtype.ext h1)
  set κ : ℂ := ((m : ℂ) + 2)⁻¹ * ((‖t0‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) with hκ
  have hκne : κ ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero hm2) ?_
    exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.2 ht0)
  have hκpos : 0 < ‖κ‖ := norm_pos_iff.2 hκne
  have havg := Formalism.FourierDecayAlt.P.averaging_vanishes β hβ V (normSeminorm ℂ V) R.card w
    (fun i => G.OmLong β (m + 1) Φ (e i)) (‖κ‖⁻¹ * (Cst * K)) 1 hw (by
      intro x hx
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
      have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
      have hb := hbound x hx0
      rw [Formalism.FourierDecayAlt.P.germ_leading_term_root_sum β m Φ x⁻¹ Dd t0 hz0, norm_smul] at hb
      have hsum : (∑ j : Fin R.card, G.psi β (w j * x) • G.OmLong β (m + 1) Φ (e j)) =
          ∑ z ∈ R, G.psi β (((m : ℂ) + 2) * z / x⁻¹) • G.OmLong β (m + 1) Φ z := by
        rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [w, div_inv_eq_mul]
      simp only [coe_normSeminorm]
      rw [hsum]
      have h3 : ‖∑ z ∈ R, G.psi β (((m : ℂ) + 2) * z / x⁻¹) • G.OmLong β (m + 1) Φ z‖ ≤
          ‖κ‖⁻¹ * (Cst * K * ‖x‖⁻¹) := by
        rw [le_inv_mul_iff₀ hκpos]; exact hb
      refine le_trans h3 (le_of_eq ?_)
      rw [div_eq_mul_inv]; ring)
  have h0 := havg (e.symm ⟨t0, hz₀⟩)
  simp only [coe_normSeminorm, Equiv.apply_symm_apply, norm_eq_zero] at h0
  exact h0

end germ

section main

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ Ψ hΨ hbig`. Establish `hone : ∀ (h : C.LPt) (c : ℂ) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt (h ++ [(1, c)]) n → U.hMat σ d = D.ptMatN (h ++ [(1, c)]) n → U.PhiTop (p` using `n) (s := 0) β σ d Ψ (fun x => x.elim0) = 0 := by`.

Introduce `h c σ d ha hM`. Take `⟨hab, hsz⟩` from `ha`. Establish `hn : D.ptSize h + 1 = n` using `by rw [← hsz, ptSize_append]; simp [D.ptSize]`. Substitute `hn` using the available equality. Establish `hc : c ≠ 0` using `(hab (1, c) (by simp)).2`.

Establish `hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0` using `fun b hb => hab b (List.mem_append_left _ hb)`. Take `⟨σh, dh, hdh, hMh⟩` from `exists_hMat h hh`. Take `⟨Ψc, hΨc, hfr⟩` from `hFr β (D.ptSize h) V Ψ hΨ c hc`. Establish `hMb : U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c) = D.ptMatN [(1, c)] (D.ptSize [(1, c)])`. Rewrite using `[hMat_one_single]`.

Conclude with `(ptMatN_one c).symm`. Establish `hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c))`. Rewrite using `[hM, hMh, hMb]`. Conclude with `ptMatN_append h [(1, c)]`. Rewrite using `[hFub β (D.ptSize h) 1 σ d σh dh 1 (fun _ => c) V Ψ hdh (fun _ => hc) hM' hΨ, phiTop_one]`.

Use `(hfr σh dh hdh).trans ?_` and prove the remaining obligations. Use `ih (D.ptSize h) (by omega) V Ψc hΨc ?_ h σh dh ⟨hh, rfl⟩ hMh` and prove the remaining obligations. Introduce `d' hd'`. Establish `hsig : Fub.sigQ (1 : Equiv.Perm (Fin (D.ptSize h))) (1 : Equiv.Perm (Fin 1)) = 1`. Use extensionality with `i`.

Simplify using `[Fub.sigQ]`. Establish `hdQ : ∀ i : Fin (D.ptSize h + 1), Fub.dQ d' (fun _ : Fin 1 => c) i ≠ 0`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left j => simp only [Fub.dQ, Fin.addCases_left]`.

Conclude with `hd' j`. Consider the case `right j => simp only [Fub.dQ, Fin.addCases_right]`. Conclude with `hc`. Combine the equalities or inequalities in the displayed calculation. Introduce `a σ d ha hM`.

Break down `List.eq_nil_or_concat a with rfl | ⟨h, ⟨s, t⟩, rfl⟩` into its components or cases. Establish `hn : n = 0` using `by have := ha.2; simp [D.ptSize] at this; omega`. Substitute `hn` using the available equality. Establish `hσ : σ = 1` using `Subsingleton.elim _ _`. Substitute `hσ` using the available equality.

Conclude with `hbig d (fun i => i.elim0)`. Simplify using `only [List.concat_eq_append] at ha hM`. Take `⟨hab, hsz⟩` from `ha`. Establish `hs1 : 1 ≤ s` using `(hab (s, t) (by simp)).1`. Establish `ht : t ≠ 0` using `(hab (s, t) (by simp)).2`.

Break down `Nat.lt_or_ge s 2 with hs | hs` into its components or cases. Establish `: s = 1` using `by omega`. Substitute `this` using the available equality. Conclude with `hone h t σ d ⟨hab, hsz⟩ hM`. Take `⟨m, rfl⟩ : ∃ m, s = m + 1 + 1` from `⟨s - 2, by omega⟩`.

Establish `hn : D.ptSize h + (m + 1 + 1) = n` using `by rw [← hsz, ptSize_append]; simp [D.ptSize]`. Substitute `hn` using the available equality. Establish `hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0` using `fun b hb => hab b (List.mem_append_left _ hb)`. Take `⟨σh, dh, hdh, hMh⟩` from `exists_hMat h hh`. Establish `hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1 + 1))) (fun _ => t) = D.ptMatN [(m + 1 + 1, t)] (D.ptSize [(m + 1 + 1, t)])`.

Rewrite using `[hMat_rev]`. Conclude with `(ptMatN_long (m + 1 + 1) t).symm`. Establish `hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => t))`. Rewrite using `[hM, hMh, hMb]`. Conclude with `ptMatN_append h [(m + 1 + 1, t)]`.

Rewrite using `[hFub β (D.ptSize h) (m + 1 + 1) σ d σh dh Fin.revPerm (fun _ => t) V Ψ hdh (fun _ => ht) hM' hΨ]`. Take `⟨κ, hκ, hL⟩` from `hOL β hβ (m + 1)`. Establish `hz` using `hL Fin.revPerm (fun _ => t) t V (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) β σh dh Ψ) ht (hMat_rev _ t)`. Establish `h0` using `germ_step β hβ (D.ptSize h) m σh dh hdh V Ψ hΨ ?_ t ht`. Rewrite `hz` using `[h0]`.

Conclude with `(smul_eq_zero.1 hz.symm).resolve_left hκ`. Introduce `t' c' ht' hc'`. Take `⟨κB, _, hB⟩` from `hOB β hβ (m + 1)`. Establish `hbl : U.hMat (Fub.sigQ (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (1 : Equiv.Perm (Fin 1))) (Fub.dQ (fun _ => t') (fun _ => c')) = G.ptBlock (m + 1) t' c'`. Rewrite using `[Fub.hMat_sigQ, hMat_rev, hMat_one_single, ptBlock_eq]`.

Establish `hdb : ∀ i, Fub.dQ (fun _ : Fin (m + 1) => t') (fun _ : Fin 1 => c') i ≠ 0`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left j => simp only [Fub.dQ, Fin.addCases_left]`. Conclude with `ht'`.

Consider the case `right j => simp only [Fub.dQ, Fin.addCases_right]`. Conclude with `hc'`. Rewrite using `[hB _ _ t' c' V _ ht' hc' hbl, ← hFub β (D.ptSize h) (m + 1 + 1) _ _ σh dh _ _ V Ψ hdh hdb (Fub.hMat_sigQ _ _ _ _) hΨ]`. Establish `hpt : U.hMat (Fub.sigQ σh (Fub.sigQ (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (1 : Equiv.Perm (Fin 1)))) (Fub.dQ dh (Fub.dQ (fun _ => t') (fun _ => c'))) = D.ptMatN ((h ++ [(m + 1, t')]) ++ [(1, c')]) (D.ptSize h + (m + 1 + 1))`. Rewrite using `[Fub.hMat_sigQ, hbl, hMh, ← ptMatN_block, List.append_assoc]`.

Conclude with `(ptMatN_append h [(m + 1, t'), (1, c')]).symm`. Rewrite using `[hone (h ++ [(m + 1, t')]) c' _ _ ⟨?_, ?_⟩ hpt, smul_zero]`. Introduce `b hb`. Simplify using `only [List.mem_append, List.mem_singleton] at hb`. Break down `hb with (hb | rfl) | rfl` into its components or cases.

Conclude with `hh b hb`. Conclude with `⟨by omega, ht'⟩`. Conclude with `⟨le_rfl, hc'⟩`. Rewrite using `[ptSize_append, ptSize_append]`. Simplify using `[D.ptSize]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem main (hFub : FubTop) (hFr : FreezeLast) (hOL : OmLongTop) (hOB : OmBlockTop) (β : ℂ) (hβ : β ≠ 0) :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat n → V), KCls Ψ →
    (∀ d : Fin n → ℂ, (∀ a, d a ≠ 0) → U.PhiTop (p := n) (s := 0) β 1 d Ψ (fun x => x.elim0) = 0) →
    ∀ (a : C.LPt) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt a n → U.hMat σ d = D.ptMatN a n →
      U.PhiTop (p := n) (s := 0) β σ d Ψ (fun x => x.elim0) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Ψ hΨ hbig

  have hone : ∀ (h : C.LPt) (c : ℂ) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt (h ++ [(1, c)]) n →
      U.hMat σ d = D.ptMatN (h ++ [(1, c)]) n → U.PhiTop (p := n) (s := 0) β σ d Ψ (fun x => x.elim0) = 0 := by
    intro h c σ d ha hM
    obtain ⟨hab, hsz⟩ := ha
    have hn : D.ptSize h + 1 = n := by rw [← hsz, ptSize_append]; simp [D.ptSize]
    subst hn
    have hc : c ≠ 0 := (hab (1, c) (by simp)).2
    have hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0 := fun b hb => hab b (List.mem_append_left _ hb)
    obtain ⟨σh, dh, hdh, hMh⟩ := exists_hMat h hh
    obtain ⟨Ψc, hΨc, hfr⟩ := hFr β (D.ptSize h) V Ψ hΨ c hc
    have hMb : U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c) = D.ptMatN [(1, c)] (D.ptSize [(1, c)]) := by
      rw [hMat_one_single]; exact (ptMatN_one c).symm
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c)) := by
      rw [hM, hMh, hMb]; exact ptMatN_append h [(1, c)]
    rw [hFub β (D.ptSize h) 1 σ d σh dh 1 (fun _ => c) V Ψ hdh (fun _ => hc) hM' hΨ, phiTop_one]
    refine (hfr σh dh hdh).trans ?_
    refine ih (D.ptSize h) (by omega) V Ψc hΨc ?_ h σh dh ⟨hh, rfl⟩ hMh
    intro d' hd'
    have hsig : Fub.sigQ (1 : Equiv.Perm (Fin (D.ptSize h))) (1 : Equiv.Perm (Fin 1)) = 1 := by
      ext i; simp [Fub.sigQ]
    have hdQ : ∀ i : Fin (D.ptSize h + 1), Fub.dQ d' (fun _ : Fin 1 => c) i ≠ 0 := by
      intro i
      induction i using Fin.addCases with
      | left j => simp only [Fub.dQ, Fin.addCases_left]; exact hd' j
      | right j => simp only [Fub.dQ, Fin.addCases_right]; exact hc
    calc U.PhiTop (p := D.ptSize h) (s := 0) β 1 d' Ψc (fun x => x.elim0)
        = U.PhiTop (p := D.ptSize h) (s := 1) β 1 d' Ψ (fun _ _ => c) := (hfr 1 d' hd').symm
      _ = U.PhiTop (p := 1) (s := 0) β 1 (fun _ => c) (U.PhiTop (p := D.ptSize h) (s := 1) β 1 d' Ψ)
            (fun x => x.elim0) := (phiTop_one β 1 (fun _ => c) _).symm
      _ = U.PhiTop (p := D.ptSize h + 1) (s := 0) β (Fub.sigQ 1 1) (Fub.dQ d' (fun _ => c)) Ψ (fun x => x.elim0) :=
          (hFub β (D.ptSize h) 1 (Fub.sigQ 1 1) (Fub.dQ d' (fun _ => c)) 1 d' 1 (fun _ => c) V Ψ hd' (fun _ => hc)
            (Fub.hMat_sigQ 1 1 d' (fun _ => c)) hΨ).symm
      _ = 0 := by rw [hsig]; exact hbig _ hdQ
  intro a σ d ha hM
  rcases List.eq_nil_or_concat a with rfl | ⟨h, ⟨s, t⟩, rfl⟩
  · have hn : n = 0 := by have := ha.2; simp [D.ptSize] at this; omega
    subst hn
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst hσ
    exact hbig d (fun i => i.elim0)
  · simp only [List.concat_eq_append] at ha hM
    obtain ⟨hab, hsz⟩ := ha
    have hs1 : 1 ≤ s := (hab (s, t) (by simp)).1
    have ht : t ≠ 0 := (hab (s, t) (by simp)).2
    rcases Nat.lt_or_ge s 2 with hs | hs
    · have : s = 1 := by omega
      subst this
      exact hone h t σ d ⟨hab, hsz⟩ hM
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 + 1 := ⟨s - 2, by omega⟩
      have hn : D.ptSize h + (m + 1 + 1) = n := by rw [← hsz, ptSize_append]; simp [D.ptSize]
      subst hn
      have hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0 := fun b hb => hab b (List.mem_append_left _ hb)
      obtain ⟨σh, dh, hdh, hMh⟩ := exists_hMat h hh
      have hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1 + 1))) (fun _ => t) =
          D.ptMatN [(m + 1 + 1, t)] (D.ptSize [(m + 1 + 1, t)]) := by
        rw [hMat_rev]; exact (ptMatN_long (m + 1 + 1) t).symm
      have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => t)) := by
        rw [hM, hMh, hMb]; exact ptMatN_append h [(m + 1 + 1, t)]
      rw [hFub β (D.ptSize h) (m + 1 + 1) σ d σh dh Fin.revPerm (fun _ => t) V Ψ hdh (fun _ => ht) hM' hΨ]
      obtain ⟨κ, hκ, hL⟩ := hOL β hβ (m + 1)
      have hz := hL Fin.revPerm (fun _ => t) t V (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) β σh dh Ψ) ht
        (hMat_rev _ t)
      have h0 := germ_step β hβ (D.ptSize h) m σh dh hdh V Ψ hΨ ?_ t ht
      · rw [h0] at hz
        exact (smul_eq_zero.1 hz.symm).resolve_left hκ
      · intro t' c' ht' hc'
        obtain ⟨κB, _, hB⟩ := hOB β hβ (m + 1)
        have hbl : U.hMat (Fub.sigQ (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (1 : Equiv.Perm (Fin 1)))
            (Fub.dQ (fun _ => t') (fun _ => c')) = G.ptBlock (m + 1) t' c' := by
          rw [Fub.hMat_sigQ, hMat_rev, hMat_one_single, ptBlock_eq]
        have hdb : ∀ i, Fub.dQ (fun _ : Fin (m + 1) => t') (fun _ : Fin 1 => c') i ≠ 0 := by
          intro i
          induction i using Fin.addCases with
          | left j => simp only [Fub.dQ, Fin.addCases_left]; exact ht'
          | right j => simp only [Fub.dQ, Fin.addCases_right]; exact hc'
        rw [hB _ _ t' c' V _ ht' hc' hbl,
          ← hFub β (D.ptSize h) (m + 1 + 1) _ _ σh dh _ _ V Ψ hdh hdb (Fub.hMat_sigQ _ _ _ _) hΨ]
        have hpt : U.hMat (Fub.sigQ σh (Fub.sigQ (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (1 : Equiv.Perm (Fin 1))))
            (Fub.dQ dh (Fub.dQ (fun _ => t') (fun _ => c'))) =
            D.ptMatN ((h ++ [(m + 1, t')]) ++ [(1, c')]) (D.ptSize h + (m + 1 + 1)) := by
          rw [Fub.hMat_sigQ, hbl, hMh, ← ptMatN_block, List.append_assoc]
          exact (ptMatN_append h [(m + 1, t'), (1, c')]).symm
        rw [hone (h ++ [(m + 1, t')]) c' _ _ ⟨?_, ?_⟩ hpt, smul_zero]
        · intro b hb
          simp only [List.mem_append, List.mem_singleton] at hb
          rcases hb with (hb | rfl) | rfl
          · exact hh b hb
          · exact ⟨by omega, ht'⟩
          · exact ⟨le_rfl, hc'⟩
        · rw [ptSize_append, ptSize_append]; simp [D.ptSize]; omega

end main

/- English proof (translation)
Introduce `hFub hFr hOL hOB n V _ _ _ Ψ hs hc hdet hbig a σ d ha hM`. Conclude with `main hFub hFr hOL hOB U.betaU Formalism.FourierDecayAlt.P.scale_matching.2.1 n V Ψ ⟨hs, hc, hdet⟩ hbig a σ d ha hM`.
-/
theorem kloosterman_density_of_parts : KloostDensOfParts := by
  intro hFub hFr hOL hOB n V _ _ _ Ψ hs hc hdet hbig a σ d ha hM
  exact main hFub hFr hOL hOB U.betaU Formalism.FourierDecayAlt.P.scale_matching.2.1 n V Ψ ⟨hs, hc, hdet⟩ hbig a σ d ha hM

end Formalism.FourierDecayAlt.P.PBJ.Asm
