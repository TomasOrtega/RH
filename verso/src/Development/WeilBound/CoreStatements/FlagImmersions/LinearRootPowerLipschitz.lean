import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.Pc

/- English proof (translation)
The claim follows from `|∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ := by classical induction s using Finset.induction_on with | empty => simp | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi] have hB : |∏ i ∈ s, b i| ≤ 1 := by rw [Finset.abs_prod] e …`.
-/
theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) (δ : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (h : ∀ i, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hB : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hb i)
    have e : a i * ∏ i ∈ s, a i - b i * ∏ i ∈ s, b i =
        a i * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a i - b i) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ 1 * (s.card * δ) :=
      mul_le_mul (ha i) ih (abs_nonneg _) zero_le_one
    have h2 : |a i - b i| * |∏ i ∈ s, b i| ≤ δ * 1 :=
      mul_le_mul (h i) hB (abs_nonneg _) ((abs_nonneg _).trans (h i))
    push_cast
    linarith

def linCoef {Ψ : Type} {N : ℕ} (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | none => s
  | some x => -lam x.1 x.2

/- English proof (translation)
Rewrite using `[Fintype.sum_option]`. Simplify using `[linA, toA, linRoot, linCoef, add_comm]`.
-/
theorem linA_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (s : ℝ) :
    linA lam s = ∑ j, C (linCoef lam s j) * X j := by
  rw [Fintype.sum_option]
  simp [linA, toA, linRoot, linCoef, add_comm]

/- English proof (translation)
Use `RootFieldNumerics.map_prod_linear (Option (Ψ × Fin N)) d Φ (fun _ => linCoef lam s)` as an intermediate fact. Rewrite `this` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← linA_eq]`. Use `this` and compare the differences between its conclusion and the goal.
-/
theorem map_linA_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ)
    (lam : Wt Ψ N) (s : ℝ) [Fintype (Fin d → Option (Ψ × Fin N))] :
    Φ (linA lam s ^ d) = ∑ w : Fin d → Option (Ψ × Fin N), (∏ k, linCoef lam s (w k)) *
      Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  have := RootFieldNumerics.map_prod_linear (Option (Ψ × Fin N)) d Φ (fun _ => linCoef lam s)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← linA_eq] at this
  convert this

end RootFieldNumerics.Pc

/- English proof (translation)
Introduce `Ψ _ N d`. Use `⟨fun Φ => ?_, fun lam => by simp [linA], ?_⟩` and prove the remaining obligations. Simplify using `only [RootFieldNumerics.Pc.map_linA_pow]`. Use `continuous_finsetSum _ fun w _ => Continuous.mul (continuous_finsetProd _ fun k _ => ?_) continuous_const` and prove the remaining obligations. Consider the cases of `w k with`.

Consider the case `none => exact continuous_snd`. Consider the case `some x`. Simplify using `only [RootFieldNumerics.Pc.linCoef]`. Use `fun_prop`. Use `⟨(Fintype.card (Fin d → Option (Ψ × Fin N)) : ℝ) * d, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `Φ b hb lam mu s s' hl hm hs hs'`. Establish `hb0 : 0 ≤ b` using `(abs_nonneg _).trans (hb 0)`. Establish `hent : ∀ (l : Wt Ψ N) τ i, |l τ i| ≤ ‖l‖` using `fun l τ i => (norm_le_pi_norm (l τ) i).trans (norm_le_pi_norm l τ)`. Establish `hc : ∀ (l : Wt Ψ N) (t : ℝ), ‖l‖ ≤ 1 → |t| ≤ 1 → ∀ j, |RootFieldNumerics.Pc.linCoef l t j| ≤ 1`. Introduce `l t h1 h2 j`.

Consider the cases of `j with`. Consider the case `none => exact h2`. Consider the case `some x => simpa [RootFieldNumerics.Pc.linCoef] using (hent l x.1 x.2).trans h1`. Establish `hd : ∀ j, |RootFieldNumerics.Pc.linCoef lam s j - RootFieldNumerics.Pc.linCoef mu s' j| ≤ ‖lam - mu‖ + |s - s'|`. Introduce `j`.

Consider the cases of `j with`. Consider the case `none => exact le_add_of_nonneg_left (norm_nonneg _)`. Consider the case `some x`. Establish `h1` using `hent (lam - mu) x.1 x.2`. Establish `e : RootFieldNumerics.Pc.linCoef lam s (some x) - RootFieldNumerics.Pc.linCoef mu s' (some x) = -((lam - mu) x.1 x.2)`.

Simplify using `only [RootFieldNumerics.Pc.linCoef, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, abs_neg]`. Conclude with `h1.trans (le_add_of_nonneg_right (abs_nonneg _))`. Rewrite using `[RootFieldNumerics.Pc.map_linA_pow, RootFieldNumerics.Pc.map_linA_pow, ← Finset.sum_sub_distrib]`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_card_nsmul _ _ (d * (‖lam - mu‖ + |s - s'|) * b) fun w _ => ?_).trans ?_` and prove the remaining obligations. Rewrite using `[← sub_mul, abs_mul]`. Use `mul_le_mul ?_ (hb _) (abs_nonneg _) (by positivity)` and prove the remaining obligations. Simplify using `using RootFieldNumerics.Pc.abs_prod_sub_prod_le Finset.univ _ _ _ (fun k => hc lam s hl hs (w k)) (fun k => hc mu s' hm hs' (w k)) (fun k => hd (w k))`.

Rewrite using `[Finset.card_univ, nsmul_eq_mul]`. Conclude with `le_of_eq (by ring)`.
-/
theorem RootFieldNumerics.linear_root_power_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  intro Ψ _ N d
  classical
  refine ⟨fun Φ => ?_, fun lam => by simp [linA], ?_⟩
  · simp only [RootFieldNumerics.Pc.map_linA_pow]
    refine continuous_finsetSum _ fun w _ => Continuous.mul
      (continuous_finsetProd _ fun k _ => ?_) continuous_const
    cases w k with
    | none => exact continuous_snd
    | some x =>
      simp only [RootFieldNumerics.Pc.linCoef]
      fun_prop
  · refine ⟨(Fintype.card (Fin d → Option (Ψ × Fin N)) : ℝ) * d, by positivity, ?_⟩
    intro Φ b hb lam mu s s' hl hm hs hs'
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
    have hent : ∀ (l : Wt Ψ N) τ i, |l τ i| ≤ ‖l‖ := fun l τ i =>
      (norm_le_pi_norm (l τ) i).trans (norm_le_pi_norm l τ)
    have hc : ∀ (l : Wt Ψ N) (t : ℝ), ‖l‖ ≤ 1 → |t| ≤ 1 → ∀ j, |RootFieldNumerics.Pc.linCoef l t j| ≤ 1 := by
      intro l t h1 h2 j
      cases j with
      | none => exact h2
      | some x => simpa [RootFieldNumerics.Pc.linCoef] using (hent l x.1 x.2).trans h1
    have hd : ∀ j, |RootFieldNumerics.Pc.linCoef lam s j - RootFieldNumerics.Pc.linCoef mu s' j| ≤ ‖lam - mu‖ + |s - s'| := by
      intro j
      cases j with
      | none => exact le_add_of_nonneg_left (norm_nonneg _)
      | some x =>
        have h1 := hent (lam - mu) x.1 x.2
        have e : RootFieldNumerics.Pc.linCoef lam s (some x) - RootFieldNumerics.Pc.linCoef mu s' (some x) =
            -((lam - mu) x.1 x.2) := by
          simp only [RootFieldNumerics.Pc.linCoef, Pi.sub_apply]; ring
        rw [e, abs_neg]
        exact h1.trans (le_add_of_nonneg_right (abs_nonneg _))
    rw [RootFieldNumerics.Pc.map_linA_pow, RootFieldNumerics.Pc.map_linA_pow, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (d * (‖lam - mu‖ + |s - s'|) * b) fun w _ => ?_).trans ?_
    · rw [← sub_mul, abs_mul]
      refine mul_le_mul ?_ (hb _) (abs_nonneg _) (by positivity)
      simpa using RootFieldNumerics.Pc.abs_prod_sub_prod_le Finset.univ _ _ _
        (fun k => hc lam s hl hs (w k)) (fun k => hc mu s' hm hs' (w k)) (fun k => hd (w k))
    · rw [Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
