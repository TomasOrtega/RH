import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Alg

open GlobalTheory.Mem.Gelf (rowE GlRel gelfC)

variable {n : ℕ}

/- English proof (translation)
Unfold `dw`. Rewrite using `[dif_pos hlam]`.
-/
theorem dw_w (lam : Fin n → ℤ) (hlam : Antitone lam) : (dw lam).w = lam := by
  unfold dw; rw [dif_pos hlam]

/- English proof (translation)
Introduce `a b hab`. Unfold `Formalism.BasicNotions.DomWeight.natW`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right ((dw lam).anti hab) _)`.
-/
theorem natW_anti (lam : Fin n → ℤ) : Antitone (dw lam).natW := by
  intro a b hab
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right ((dw lam).anti hab) _)

/- English proof (translation)
Establish `hw` using `dw_w lam hlam`. Establish `hn : 0 < n` using `a.pos`. Establish `hd : (dw lam).detShift = (dw lam).w ⟨n - 1, by omega⟩`. Unfold `Formalism.BasicNotions.DomWeight.detShift`. Rewrite using `[dif_pos hn]`.

Establish `hle : (dw lam).detShift ≤ (dw lam).w a`. Rewrite using `[hd]`. Conclude with `(dw lam).anti (Fin.le_iff_val_le_val.mpr (by simp; omega))`. Establish `hz : (((dw lam).natW a : ℕ) : ℤ) = (dw lam).w a - (dw lam).detShift`. Unfold `Formalism.BasicNotions.DomWeight.natW`.

Conclude with `Int.toNat_of_nonneg (by omega)`. Establish `hc : (((dw lam).natW a : ℕ) : ℂ) = ((((dw lam).natW a : ℕ) : ℤ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[hc, hz, hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natW_add (lam : Fin n → ℤ) (hlam : Antitone lam) (a : Fin n) :
    (((dw lam).natW a : ℕ) : ℂ) + (((dw lam).detShift : ℤ) : ℂ) = (lam a : ℂ) := by
  have hw := dw_w lam hlam
  have hn : 0 < n := a.pos
  have hd : (dw lam).detShift = (dw lam).w ⟨n - 1, by omega⟩ := by
    unfold Formalism.BasicNotions.DomWeight.detShift
    rw [dif_pos hn]
  have hle : (dw lam).detShift ≤ (dw lam).w a := by
    rw [hd]
    exact (dw lam).anti (Fin.le_iff_val_le_val.mpr (by simp; omega))
  have hz : (((dw lam).natW a : ℕ) : ℤ) = (dw lam).w a - (dw lam).detShift := by
    unfold Formalism.BasicNotions.DomWeight.natW
    exact Int.toNat_of_nonneg (by omega)
  have hc : (((dw lam).natW a : ℕ) : ℂ) = ((((dw lam).natW a : ℕ) : ℤ) : ℂ) := by push_cast; rfl
  rw [hc, hz, hw]
  push_cast
  ring

/- English proof (translation)
Introduce `a b c d`. Establish `hD : ∀ (x y : Fin N) (F : A), (if x = y then C else 0) * F = F * (if x = y then C else 0)`. Introduce `x y F`. Apply the tactic sequence `split_ifs <;> simp [hC]`. Establish `key : ∀ (e f p q : A), (∀ F, p * F = F * p) → (∀ F, q * F = F * q) → (e + p) * (f + q) - (f + q) * (e + p) = (e * f - f * e) + (p * q - q * p)`.

Introduce `e f p q hp hq`. Simplify using `only [add_mul, mul_add]`. Rewrite using `[hp f, hq e]`. Normalize the expressions using the abelian group laws. Simplify using `only [Matrix.add_apply, Matrix.of_apply]`.

Rewrite using `[key _ _ _ _ (hD a b) (hD c d), h a b c d, hD a b (if c = d then C else 0), sub_self, add_zero]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a`. Substitute `hbc hda` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hbc, hda, Ne.symm hda]`.

Simplify using `[hbc, hda, Ne.symm hbc]`. Simplify using `[hbc, hda]`.
-/
theorem glRel_shift {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) (C : A)
    (hC : ∀ F : A, C * F = F * C) (h : GlRel E) :
    GlRel (E + Matrix.of fun a b => if a = b then C else 0) := by
  intro a b c d
  have hD : ∀ (x y : Fin N) (F : A), (if x = y then C else 0) * F = F * (if x = y then C else 0) := by
    intro x y F
    split_ifs <;> simp [hC]
  have key : ∀ (e f p q : A), (∀ F, p * F = F * p) → (∀ F, q * F = F * q) →
      (e + p) * (f + q) - (f + q) * (e + p) = (e * f - f * e) + (p * q - q * p) := by
    intro e f p q hp hq
    simp only [add_mul, mul_add]
    rw [hp f, hq e]
    abel
  simp only [Matrix.add_apply, Matrix.of_apply]
  rw [key _ _ _ _ (hD a b) (hD c d), h a b c d, hD a b (if c = d then C else 0), sub_self, add_zero]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp
  · simp [hbc, hda, Ne.symm hda]
  · simp [hbc, hda, Ne.symm hbc]
  · simp [hbc, hda]

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Simplify using `only [Et, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Et_eq (lam : Fin n → ℤ) : Et lam = GlobalTheory.Mem.Gelf.rowE ℂ n n +
    Matrix.of fun a b => if a = b then (((dw lam).detShift : ℤ) : ℂ) • (1 : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) else 0 := by
  refine Matrix.ext fun a b => ?_
  simp only [Et, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  congr 1
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Et_eq]`. Use `glRel_shift _ _ (fun F => ?_) (GlobalTheory.Mem.GelfCheck.glRel_rowE ℂ n n)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`.
-/
theorem glRel_Et (lam : Fin n → ℤ) : GlRel (Et lam) := by
  rw [Et_eq]
  refine glRel_shift _ _ (fun F => ?_) (GlobalTheory.Mem.GelfCheck.glRel_rowE ℂ n n)
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/- English proof (translation)
Rewrite using `[Et_eq]`. Simplify using `only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply]`. Use `Submodule.add_mem _ (GlobalTheory.BrCompare.rowE_mem a b hf) ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply]`.

Conclude with `Submodule.smul_mem _ _ hf`. Simplify using the standard rewrite rules.
-/
theorem Et_mem (lam : Fin n → ℤ) (a b : Fin n) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : Et lam a b f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) := by
  rw [Et_eq]
  simp only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ (GlobalTheory.BrCompare.rowE_mem a b hf) ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ _ hf
  · simp

/- English proof (translation)
Proceed by induction on `k generalizing a b f with`. Consider the case `zero`. Rewrite using `[pow_zero, Matrix.one_apply]`. Use `split_ifs`. Simplify using `using hf`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun c _ => by`. Rewrite using `[Module.End.mul_apply]`.

Conclude with `Et_mem lam a c (ih c b hf)`.
-/
theorem Etpow_mem (lam : Fin n → ℤ) (k : ℕ) (a b : Fin n) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : (Et lam ^ k) a b f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) := by
  induction k generalizing a b f with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · simpa using hf
    · simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun c _ => by
      rw [Module.End.mul_apply]
      exact Et_mem lam a c (ih c b hf)

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Simplify using `only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Simplify using `only [GlobalTheory.Mem.GelfCheck.pow_cov (glRel_Et lam) k]`. Rewrite using `[Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules.
-/
theorem trace_comm (lam : Fin n → ℤ) (k : ℕ) (c d : Fin n) :
    Et lam c d * (Et lam ^ k).trace = (Et lam ^ k).trace * Et lam c d := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.Mem.GelfCheck.pow_cov (glRel_Et lam) k]
  rw [Finset.sum_sub_distrib]
  simp

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Et_eq]`. Simplify using `only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply, if_true, eq_self_iff_true, LinearMap.smul_apply, Module.End.one_apply]`. Rewrite using `[GlobalTheory.BrCompare.hw_weight (natW_anti lam) a, ← add_smul, natW_add lam hlam a]`. Rewrite using `[Et_eq]`.

Simplify using `only [Matrix.add_apply, Matrix.of_apply, if_neg hab.ne, LinearMap.add_apply, LinearMap.zero_apply, add_zero]`. Conclude with `GlobalTheory.BrCompare.hw_raise _ a b hab`.
-/
theorem Et_hw (lam : Fin n → ℤ) (hlam : Antitone lam) :
    (∀ a, Et lam a a (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) = (lam a : ℂ) • Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) ∧
    ∀ a b, a < b → Et lam a b (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Et_eq]
    simp only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply, if_true, eq_self_iff_true,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [GlobalTheory.BrCompare.hw_weight (natW_anti lam) a, ← add_smul, natW_add lam hlam a]
  · rw [Et_eq]
    simp only [Matrix.add_apply, Matrix.of_apply, if_neg hab.ne, LinearMap.add_apply, LinearMap.zero_apply,
      add_zero]
    exact GlobalTheory.BrCompare.hw_raise _ a b hab

/- English proof (translation)
Establish `hE` using `glRel_Et lam`. Establish `hstab : ∀ a b, ∀ g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1), GlobalTheory.Mem.Gelf.rowE ℂ n n a b g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1)`. Introduce `a b g hg`. Rewrite `hg` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Establish `hr : GlobalTheory.Mem.Gelf.rowE ℂ n n a b = Et lam a b - (if a = b then (((dw lam).detShift : ℤ) : ℂ) • (1 : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) else 0)`.

Rewrite using `[Et_eq]`. Simplify using the standard rewrite rules. Establish `hcomm : (Et lam ^ k).trace * GlobalTheory.Mem.Gelf.rowE ℂ n n a b = GlobalTheory.Mem.Gelf.rowE ℂ n n a b * (Et lam ^ k).trace`. Rewrite using `[hr, mul_sub, sub_mul, ← trace_comm lam k a b]`. Apply the tactic sequence `split_ifs <;> simp [smul_mul_assoc, mul_smul_comm]`.

Establish `hg2` using `congrArg (fun L : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ) => L g) hcomm`. Simplify using `only [Module.End.mul_apply] at hg2`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hg2, hg]`. Simplify using the standard rewrite rules. Establish `hhw : Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1)`.

Take `⟨h1, h2⟩` from `Et_hw lam hlam`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GlobalTheory.Mem.GelfCheck.trace_pow_apply hE h1 h2 k]`. Simplify using the standard rewrite rules. Establish `hle` using `GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable ℂ n (dw lam).natW (natW_anti lam) _ hhw hstab`. Use `hle hf` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using this`.
-/
theorem trace_on_model (lam : Fin n → ℤ) (hlam : Antitone lam) (k : ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    (Et lam ^ k).trace f = gelfC (fun a => (lam a : ℂ)) k • f := by
  have hE := glRel_Et lam
  have hstab : ∀ a b, ∀ g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1),
      GlobalTheory.Mem.Gelf.rowE ℂ n n a b g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1) := by
    intro a b g hg
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg
    have hr : GlobalTheory.Mem.Gelf.rowE ℂ n n a b = Et lam a b
        - (if a = b then (((dw lam).detShift : ℤ) : ℂ) • (1 : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) else 0) := by
      rw [Et_eq]
      simp
    have hcomm : (Et lam ^ k).trace * GlobalTheory.Mem.Gelf.rowE ℂ n n a b = GlobalTheory.Mem.Gelf.rowE ℂ n n a b * (Et lam ^ k).trace := by
      rw [hr, mul_sub, sub_mul, ← trace_comm lam k a b]
      split_ifs <;> simp [smul_mul_assoc, mul_smul_comm]
    have hg2 := congrArg (fun L : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ) => L g) hcomm
    simp only [Module.End.mul_apply] at hg2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hg2, hg]
    simp
  have hhw : Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1) := by
    obtain ⟨h1, h2⟩ := Et_hw lam hlam
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GlobalTheory.Mem.GelfCheck.trace_pow_apply hE h1 h2 k]
    simp
  have hle := GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable ℂ n (dw lam).natW (natW_anti lam) _ hhw hstab
  have := hle hf
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

/- English proof (translation)
Unfold `GlobalTheory.Mem.Gelf.gelfC GlobalTheory.Dec.gelfVal`. Rewrite using `[GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat]`. Establish `h : Formalism.REAL.lsh (fun a => (lam a : ℂ)) = fun c => infOf lam true c + ((n : ℂ) - 1) / 2`. Use function extensionality and compare the values at `c`. Simplify using `[Formalism.REAL.lsh, infOf]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.
-/
theorem gelfC_eq (lam : Fin n → ℤ) (k : ℕ) :
    gelfC (fun a => (lam a : ℂ)) k = GlobalTheory.Dec.gelfVal (infOf lam true) k := by
  unfold GlobalTheory.Mem.Gelf.gelfC GlobalTheory.Dec.gelfVal
  rw [GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat]
  have h : Formalism.REAL.lsh (fun a => (lam a : ℂ)) = fun c => infOf lam true c + ((n : ℂ) - 1) / 2 := by
    funext c
    simp [Formalism.REAL.lsh, infOf]
    ring
  rw [h]

end PositivityTheory.RgBcC.Cxd2.Alg
