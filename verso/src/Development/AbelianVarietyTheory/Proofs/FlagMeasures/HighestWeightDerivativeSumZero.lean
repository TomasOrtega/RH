import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Schmid

/- English proof (translation)
Establish `h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card = n - 1 - a`. Rewrite using `[← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Establish `h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card = a`. Rewrite using `[← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not, Finset.filter_gt_eq_Iio, Fin.card_Iio]`. Establish `ha` using `a.2`.

Establish `h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + a + 1 = n` using `by omega`. Establish `h3'` using `congrArg (Nat.cast : ℕ → ℝ) h3`. Establish `h2'` using `congrArg (Nat.cast : ℕ → ℝ) h2`. Move the coercions through the operations in `at h3' h2'`. Unfold `Formalism.REAL.rhoN Formalism.REAL.rhoC`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

/- English proof (translation)
Establish `: ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i = u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) + ((if i = a then 1 else 0) + (if i = b then 1 else 0))`. Introduce `i`. Simplify using `only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `by_cases h1 : i = a <;> by_cases h2 : i = b`. Conclude with `absurd (h1.symm.trans h2) hab`.

Apply the tactic sequence `all_goals simp [h1, h2, hab, hab.symm]`. Apply the tactic sequence `all_goals ring`. Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Simplify using the standard rewrite rules. Evaluate the numerical expressions.
-/
theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

/- English proof (translation)
Unfold `Formalism.MainNotions.S.vNormSq`. Rewrite using `[show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel, nsq_sub_root _ hab.ne]`. Establish `h1` using `hμ hab`. Establish `h2` using `rhoN_add_rhoC ε a`. Establish `h3` using `rhoN_add_rhoC ε b`.

Establish `h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Simplify using `only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vNormSq_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/- English proof (translation)
Rewrite using `[theta_map_word_sum_apply, ← Fintype.sum_prod_type']`. Use `Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_` and prove the remaining obligations. Establish `h : α = fun _ => (α 0)` using `fin_one_fun_eq_const_apply_zero α`. Establish `e : at1 G (α 0).1 (α 0).2 = G α` using `by conv_rhs => rw [h]`. Both sides reduce to the same expression.

Simplify using `only [Equiv.funUnique_apply]`. Express the relevant statement in the definitionally equal form `_ = E (α 0).1 (α 0).2 (at1 G (α 0).1 (α 0).2)`. Rewrite using `[e]`. Simplify using `[ew]`.
-/
theorem thetaA_one {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (G : Arr V n 1) :
    thetaA E 1 G = ∑ a, ∑ b, E a b (at1 G a b) := by
  rw [theta_map_word_sum_apply, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  have h : α = fun _ => (α 0) := fin_one_fun_eq_const_apply_zero α
  have e : at1 G (α 0).1 (α 0).2 = G α := by
    conv_rhs => rw [h]
    rfl
  simp only [Equiv.funUnique_apply]
  change _ = E (α 0).1 (α 0).2 (at1 G (α 0).1 (α 0).2)
  rw [e]
  simp [ew]

/- English proof (translation)
Introduce `n ε H _ _ _ σ V E lam u hl hσ hD hu hfd F hF`. Establish `hg` using `hD.1`. Take `⟨-, hθ⟩` from `(arr_module_facts V n ε E 1).1 hg`. Take `⟨-, -, hst, -, -, -, hpf⟩` from `pfil_facts_hold V n ε E u hg`. Establish `hker : Vminus ε E (LamOf ε lam) u ≤ LinearMap.ker (thetaA E 1)`.

Apply `isotypic_part_le_of_forall` to reduce the goal to its premises. Introduce `y hy μ hμ hyh`. Apply `compact_span_le_of_stable` to reduce the goal to its premises. Introduce `c d _ x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hθ, hx, map_zero]`. Rewrite using `[LinearMap.mem_ker]`. Take `⟨a, b, hba, hne, rfl⟩` from `hμ`. Assume the negation of the conclusion as `hw0`. Establish `hμeq : LamOf ε lam + Formalism.REAL.root a b = lowK ε lam - Formalism.REAL.root b a`.

Rewrite using `[root_swap' a b, sub_eq_add_neg]`. Both sides reduce to the same expression. Establish `hwh : KHighest ε E (lowK ε lam - Formalism.REAL.root b a) (thetaA E 1 y)`. Use `⟨fun c => ?_, fun c d hcd hcomp => ?_⟩` and prove the remaining obligations. Rewrite using `[← hθ, hyh.1 c, map_smul, hμeq]`.

Rewrite using `[← hθ, hyh.2 c d hcd hcomp, map_zero]`. Establish `hmem : thetaA E 1 y ∈ pfil ε E u 1` using `(theta_filtration_holds V n ε E u hg).1 1 y hy`. Use `hpf hfd 1` as an intermediate fact. Establish `hf : FiniteDimensional ℂ (kSpan ε E (thetaA E 1 y))` using `Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst 1) hmem)`. Establish `hK` using `(GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ.2.2.1 hD).1 _ _ hw0 hwh hf`.

Conclude with `absurd (hσ.2.2.2.2.2.2 _ _ hK) (not_le.mpr (vNormSq_sub_root_lt ε hl.1 hba))`. Rewrite using `[← thetaA_one]`. Conclude with `hker hF`.
-/
theorem mul_vminus_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  intro n ε H _ _ _ σ V E lam u hl hσ hD hu hfd F hF
  have hg := hD.1
  obtain ⟨-, hθ⟩ := (arr_module_facts V n ε E 1).1 hg
  obtain ⟨-, -, hst, -, -, -, hpf⟩ := pfil_facts_hold V n ε E u hg
  have hker : Vminus ε E (LamOf ε lam) u ≤ LinearMap.ker (thetaA E 1) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    apply compact_span_le_of_stable
    · intro c d _ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hθ, hx, map_zero]
    · rw [LinearMap.mem_ker]
      obtain ⟨a, b, hba, hne, rfl⟩ := hμ
      by_contra hw0
      have hμeq : LamOf ε lam + Formalism.REAL.root a b = lowK ε lam - Formalism.REAL.root b a := by
        rw [root_swap' a b, sub_eq_add_neg]; rfl
      have hwh : KHighest ε E (lowK ε lam - Formalism.REAL.root b a) (thetaA E 1 y) := by
        refine ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
        · rw [← hθ, hyh.1 c, map_smul, hμeq]
        · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]
      have hmem : thetaA E 1 y ∈ pfil ε E u 1 := (theta_filtration_holds V n ε E u hg).1 1 y hy
      have := hpf hfd 1
      have hf : FiniteDimensional ℂ (kSpan ε E (thetaA E 1 y)) :=
        Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst 1) hmem)
      have hK := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ.2.2.1 hD).1 _ _ hw0 hwh hf
      exact absurd (hσ.2.2.2.2.2.2 _ _ hK) (not_le.mpr (vNormSq_sub_root_lt ε hl.1 hba))
  rw [← thetaA_one]
  exact hker hF

end GlobalTheory.Jet.Schmid
