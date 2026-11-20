import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Take `⟨T, hT, Pc, j, hPc, hsub, hco'⟩` from `hT'`. Take `⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩` from `hIn.2.2 T hT`. Use `set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef`. Use `set c₀ : ℝ := min ε (ε ^ 2) with hc₀`. Establish `hc₀p : 0 < c₀` using `lt_min hε (by positivity)`.

Establish `hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l)`. Introduce `g hg l hl`. Break down `hl with hl | rfl` into its components or cases. Simplify using `at hl`. Use `Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2` as an intermediate fact.

Conclude with `(min_le_left _ _).trans this`. Establish `hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)`. Introduce `g hg`. Rewrite using `[Complex.normSq_ofReal]`. Establish `h1` using `hg.2`.

Establish `: ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g` using `by nlinarith`. Conclude with `(min_le_right _ _).trans this`. Establish `hcU` using `P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0`. Take `⟨⟨Cc, hCc0, hUB⟩, -⟩` from `hcU`. Use `set fo := (es.map fun e => e.2.length).sum with hfo`.

Take `⟨CP, hCP0, hCP⟩` from `hPc.2 [] (fun x hx => by simp at hx)`. Use `set D : ℕ := (2 * r + 2) * T.word.length with hD`. Use `set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw`. Establish `hcw0 : 0 ≤ cw` using `List.prod_nonneg fun x hx => by`. Take `⟨X, _, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `(P.BetaSesquilinearity.nz_pos X).le`. Establish `hεj : 0 ≤ (ε⁻¹) ^ j` using `by positivity`. Use `⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩` and prove the remaining obligations. Establish `hgS : g ∈ S` using `⟨hg, hgε⟩`. Establish `hgp` using `P.BetaSesquilinearity.gN_pos hg`.

Establish `hg1` using `P.BetaSesquilinearity.gN_ge_one hg`. Establish `hGpos : 0 < Gf k r Bs.z Bs.z' g` using `lt_of_lt_of_le hε hgε`. Establish `hgd : g ∈ C6.domL Bs ∅` using `⟨hg, hGpos, fun l hl => by simp at hl⟩`. Establish `hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k` using `k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩`. Establish `hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)`.

Establish `h` using `hUB [] hAdm0 g hgS`. Establish `e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g = (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g` using `rfl`. Rewrite `h` using `[e]`. Rewrite using `[hco g hgd]`. Simplify using `using h`.

Establish `hb0 : 0 ≤ b`. Establish `h` using `hF.2 [] [] (by simp) (by simp) (by simp) g hg`. Conclude with `le_trans (by positivity) h`. Establish `hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A))`. Rewrite using `[P.BetaSesquilinearity.Rw_scale]`.

Simplify using `only`. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]`. Apply `mul_le_mul_of_nonneg_left _ hcw0` to reduce the goal to its premises. Establish `hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X` using `fun X hX => by`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`.

Conclude with `P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)`. Establish `hl' : T'.word.length ≤ T.word.length` using `hsub.length_le`. Establish `h` using `hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg`. Establish `e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g` using `rfl`. Rewrite `h` using `[e]`.

Establish `hpw : 0 < B.gN g ^ A` using `Real.rpow_pos_of_pos hgp _`. Rewrite using `[Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]`. Conclude with `h`. Establish `hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D`. Use `hCP g hg` as an intermediate fact.

Simplify `this` using `[P.B4.W_nil]`. Establish `hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j`. Rewrite using `[norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]`. Conclude with `pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j`. Establish `hfo' : fo ≤ o` using `by omega`.

Establish `hwo : T.word.length ≤ o` using `by omega`. Rewrite using `[hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]`. Establish `hX : 0 ≤ B.gN g` using `hgp.le`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(T.coef g).le_opNorm _`.

Use `_ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by gcongr`. Use `_ = CP * ε⁻¹ ^ j * Cc * cw * b * (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by`. Rewrite using `[Real.rpow_natCast]`. Put the polynomial expressions in normal form. Use `_ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by`.

Rewrite using `[← Real.rpow_add hgp, sub_eq_add_neg]`. Use `_ ≤ CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `Real.rpow_le_rpow_of_exponent_le hg1` to reduce the goal to its premises. Establish `h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o` using `Nat.mul_le_mul_left _ hfo'`.

Establish `h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ)` using `by exact_mod_cast h3`. Establish `h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ)`. Rewrite using `[hD]`. Conclude with `Nat.mul_le_mul_left _ hwo` after adjusting the coercions. Move the coercions through the operations in `at h4 h5 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nfLeibBd_term (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    (T' : B.DTerm k r Wp Wq) (hT' : LeibTerm Bs Dop T') {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖T'.coef g (B.Rw T'.word F g)‖ ≤
          K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
  obtain ⟨T, hT, Pc, j, hPc, hsub, hco'⟩ := hT'
  obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hIn.2.2 T hT
  set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef
  set c₀ : ℝ := min ε (ε ^ 2) with hc₀
  have hc₀p : 0 < c₀ := lt_min hε (by positivity)
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
      c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · simp at hl
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2
      exact (min_le_left _ _).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2
    have : ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
    exact (min_le_right _ _).trans this
  have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  set fo := (es.map fun e => e.2.length).sum with hfo
  obtain ⟨CP, hCP0, hCP⟩ := hPc.2 [] (fun x hx => by simp at hx)
  set D : ℕ := (2 * r + 2) * T.word.length with hD
  set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw
  have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
    obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
  have hεj : 0 ≤ (ε⁻¹) ^ j := by positivity
  refine ⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩
  have hgS : g ∈ S := ⟨hg, hgε⟩
  have hgp := P.BetaSesquilinearity.gN_pos hg
  have hg1 := P.BetaSesquilinearity.gN_ge_one hg
  have hGpos : 0 < Gf k r Bs.z Bs.z' g := lt_of_lt_of_le hε hgε
  have hgd : g ∈ C6.domL Bs ∅ := ⟨hg, hGpos, fun l hl => by simp at hl⟩
  have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
  have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
    have h := hUB [] hAdm0 g hgS
    have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
        (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
    rw [e] at h
    rw [hco g hgd]
    simpa using h
  have hb0 : 0 ≤ b := by
    have h := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    exact le_trans (by positivity) h
  have hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
    rw [P.BetaSesquilinearity.Rw_scale]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)
    have hl' : T'.word.length ≤ T.word.length := hsub.length_le
    have h := hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
    have e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g := rfl
    rw [e] at h
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
    exact h
  have hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D := by
    have := hCP g hg
    simpa [P.B4.W_nil] using this
  have hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j
  have hfo' : fo ≤ o := by omega
  have hwo : T.word.length ≤ o := by omega
  rw [hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]
  have hX : 0 ≤ B.gN g := hgp.le
  calc ‖Pc g‖ * ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ * ‖T.coef g (B.Rw T'.word F g)‖
      ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * (‖T.coef g‖ * ‖B.Rw T'.word F g‖) := by
        gcongr
        exact (T.coef g).le_opNorm _
    _ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j *
          ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by
        gcongr
    _ = CP * ε⁻¹ ^ j * Cc * cw * b *
          (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
        rw [Real.rpow_natCast]; ring_nf
    _ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by
        rw [← Real.rpow_add hgp, sub_eq_add_neg]
    _ ≤ CP * ε⁻¹ ^ j * Cc * cw * b *
          B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hg1
        have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
        have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ) := by
          rw [hD]; exact_mod_cast Nat.mul_le_mul_left _ hwo
        push_cast at h4 h5 ⊢
        linarith

/- English proof (translation)
Unfold `NFLeibBd`. Introduce `k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε`. Proceed by induction on `L with`. Consider the case `nil`. Use `⟨0, le_refl _, ?_⟩` and prove the remaining obligations.

Introduce `F A b hF g hg hεg`. Simplify using `[B.opApply]`. Consider the case `cons T L ih`. Take `⟨K₁, hK₁, h₁⟩` from `nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε`. Take `⟨K₂, hK₂, h₂⟩` from `ih (fun T' hT' => hL T' (by simp [hT']))`.

Use `⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩` and prove the remaining obligations. Introduce `F A b hF g hg hεg`. Establish `e1` using `h₁ F A b hF g hg hεg`. Establish `e2` using `h₂ F A b hF g hg hεg`. Establish `hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g`.

Simplify using `[B.opApply]`. Rewrite using `[hs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem leibniz_bound_holds : NFLeibBd := by
  unfold NFLeibBd
  intro k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε
  induction L with
  | nil =>
    refine ⟨0, le_refl _, ?_⟩
    intro F A b hF g hg hεg
    simp [B.opApply]
  | cons T L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε
    obtain ⟨K₂, hK₂, h₂⟩ := ih (fun T' hT' => hL T' (by simp [hT']))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro F A b hF g hg hεg
    have e1 := h₁ F A b hF g hg hεg
    have e2 := h₂ F A b hF g hg hεg
    have hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      simp [B.opApply]
    rw [hs]
    calc _ ≤ ‖T.coef g (B.Rw T.word F g)‖ + ‖B.opApply L F g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end bd

end Formalism.FourierDecayAlt.P.CutBP
