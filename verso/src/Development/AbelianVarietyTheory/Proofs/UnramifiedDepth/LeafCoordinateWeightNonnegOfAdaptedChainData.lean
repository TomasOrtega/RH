import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)

namespace GlobalTheory.LeafCoordWeight

/- English proof (translation)
Take `⟨ε⟩ : Nonempty (Fin (Fintype.card I) ≃ I)` from `⟨(Fintype.equivFin I).symm⟩`. Establish `hK` using `Kn_eq D.i_odd`. Establish `hl0 : (D.l : C) ≠ 0` using `by exact_mod_cast D.l_prime.ne_zero`. Establish `key` using `GlobalTheory.ChainCoord.chain C D.v D.l D.l_prime D.v_l D.l_ge (Fintype.card I) N (s0 D.i) {c | D.good (ε c)} (fun s => Finset.univ.filter fun c => D.lev (ε c) = s ∧ s < Kn D.i) (fun c s b => if s = 0 then (if ε c = ε b then 1 else 0) else D.al (ε c) s (ε b)) (fun s e j => chainM …`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hc).2`.

Conclude with `D.pure_good _ (h1 ▸ h2))`. Use the proof step `(fun s s' c _ _ hc hc' => (Finset.mem_filter.1 hc).2.1.symm.trans (Finset.mem_filter.1 hc').2.1)`. Use the proof step `(fun c e => by simp)`. Use the proof step `(fun c n e => by`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Apply the tactic sequence `by_cases h : ε c = ε e <;> simp [h]`. Simplify using `only [if_neg hn]`. Conclude with `D.al_all _ _ _)`. Use the proof step `(fun c hc => ⟨by`.

Use function extensionality and compare the values at `e`. Simplify using `using D.al_one _ hc (ε e), fun n e hn => by`. Simplify using `only [if_neg (show n ≠ 0 by omega)]`. Use `D.al_good _ hc n (ε e) hn` as an intermediate fact. Rewrite using `[neg_sub] at this⟩)` and apply the resulting hypothesis.

Use the proof step `(fun s hs c hc e he => by`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hc).2`. Establish `h3 : D.lev (ε e) ≠ D.lev (ε c) + 1` using `fun h => he (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, by omega⟩)`. Simplify using `only [if_neg (show (2 : ℕ) ≠ 0 by omega)]`. Rewrite using `[D.al_two _ (by omega), D.g_supp _ (by omega) _ h3, zero_add, inv_mul_cancel_left₀ hl0]`.

Conclude with `D.lam_int _ _)`. Use the proof step `(fun c j => by`. Simplify using `only [chainMat_zero]`. Apply the tactic sequence `split_ifs <;> simp)`. Use the proof step `(fun c hc => by`.

Use function extensionality and compare the values at `j`. Simplify using `only [chainMat_zero, Pi.zero_apply]`. Use `if_neg fun h => hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, by omega⟩)` and prove the remaining obligations. Rewrite using `[h, hem])`. Use the proof step `(fun s e j => by`.

Simplify using `only [chainMat_succ, if_neg (show (2 : ℕ) ≠ 0 by omega)]`. Rewrite using `[Finset.sum_filter, Finset.sum_filter, ← ε.sum_comp])`. Use the proof step `(fun c => ht _)`. Use the proof step `(fun e => by`. Use extensionality with `μ`.

Use `Eq.trans ?_ (hz (ε e) μ)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ n ∈ Finset.range (Finsupp.degree μ + 1), ∑ a, _ = _`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[← ε.sum_comp])`. Rewrite `key` using `[two_mul_chainStartIndex_add_one_of_odd D.i_odd]`.

Use `⟨fun c hc => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `ε.surjective c`. Conclude with `key.1 _ (by omega) c (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hc⟩)`. Take `⟨c, rfl⟩` from `ε.surjective c`. Use `key.2 c fun s _ h => hc ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 h).2`. Use linear arithmetic over natural numbers and integers.
-/
theorem chain_data {C : Type} [Field C] [CharZero C] {Z I : Type} [Fintype I] (D : Data C Z I)
    {N : ℕ} (em : Fin N → I) (hem : ∀ δ, D.lev (em δ) = 0) (t : I → MvPowerSeries (Fin N) C)
    (ht : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hz : ∀ (b : I) (μ : Fin N →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      (if s = 0 then (if c = b then 1 else 0) else D.al c s b) *
        MvPowerSeries.coeff μ (t c ^ (D.l ^ s)) =
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (if b = em j then 1 else 0) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C))) :
    (∀ c, D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i))
        (t c - ∑ j, MvPowerSeries.C (R := C)
          (GlobalTheory.ChainCoord.kap C D.l (D.lev c) * chainMat D (D.lev c) c (em j)) *
          (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ ((D.l ^ 2) ^ D.lev c))
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1))) ∧
    ∀ c, ¬ D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i)) (t c)
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1)) := by
  obtain ⟨ε⟩ : Nonempty (Fin (Fintype.card I) ≃ I) := ⟨(Fintype.equivFin I).symm⟩
  have hK := Kn_eq D.i_odd
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := GlobalTheory.ChainCoord.chain C D.v D.l D.l_prime D.v_l D.l_ge (Fintype.card I) N (s0 D.i)
    {c | D.good (ε c)}
    (fun s => Finset.univ.filter fun c => D.lev (ε c) = s ∧ s < Kn D.i)
    (fun c s b => if s = 0 then (if ε c = ε b then 1 else 0) else D.al (ε c) s (ε b))
    (fun s e j => chainMat D s (ε e) (em j)) (fun c => t (ε c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      exact D.pure_good _ (h1 ▸ h2))
    (fun s s' c _ _ hc hc' =>
      (Finset.mem_filter.1 hc).2.1.symm.trans (Finset.mem_filter.1 hc').2.1)
    (fun c e => by simp)
    (fun c n e => by
      by_cases hn : n = 0
      · subst hn
        by_cases h : ε c = ε e <;> simp [h]
      · simp only [if_neg hn]
        exact D.al_all _ _ _)
    (fun c hc => ⟨by
      funext e
      simpa using D.al_one _ hc (ε e), fun n e hn => by
      simp only [if_neg (show n ≠ 0 by omega)]
      have := D.al_good _ hc n (ε e) hn
      rwa [neg_sub] at this⟩)
    (fun s hs c hc e he => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      have h3 : D.lev (ε e) ≠ D.lev (ε c) + 1 := fun h =>
        he (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, by omega⟩)
      simp only [if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [D.al_two _ (by omega), D.g_supp _ (by omega) _ h3, zero_add, inv_mul_cancel_left₀ hl0]
      exact D.lam_int _ _)
    (fun c j => by
      simp only [chainMat_zero]
      split_ifs <;> simp)
    (fun c hc => by
      funext j
      simp only [chainMat_zero, Pi.zero_apply]
      refine if_neg fun h => hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, by omega⟩)
      rw [h, hem])
    (fun s e j => by
      simp only [chainMat_succ, if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [Finset.sum_filter, Finset.sum_filter, ← ε.sum_comp])
    (fun c => ht _)
    (fun e => by
      ext μ
      refine Eq.trans ?_ (hz (ε e) μ)
      change ∑ n ∈ Finset.range (Finsupp.degree μ + 1), ∑ a, _ = _
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← ε.sum_comp])
  rw [two_mul_chainStartIndex_add_one_of_odd D.i_odd] at key
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨c, rfl⟩ := ε.surjective c
    exact key.1 _ (by omega) c (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hc⟩)
  · obtain ⟨c, rfl⟩ := ε.surjective c
    refine key.2 c fun s _ h => hc ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 h).2
    omega

/- English proof (translation)
Introduce `μ`. Establish `h1 : r1 V.l i - del V.l i = 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)`. Establish `: (V.l : ℝ) ≠ 0` using `by exact_mod_cast V.l_prime.ne_zero`. Establish `h3 : 1 / (2 * (V.l : ℝ) ^ i) - 1 / (8 * (V.l : ℝ) ^ i) = 3 / (8 * (V.l : ℝ) ^ i)`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h3]`. Unfold `r1 del rho`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (μ.degree : ℝ) = ∑ m, (μ m : ℝ)`.

Rewrite using `[Finsupp.degree_eq_sum]`. Use `push_cast`. Both sides reduce to the same expression. Use `le_trans ?_ (add_le_add (h μ) le_rfl)` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, h1, h2, ← Finset.mul_sum]`.

Conclude with `WithTop.coe_le_coe.2 (le_of_eq (by ring))`.
-/
theorem wtGe1_of_ordGe {C : Type} [Field C] {V : VF C} {i N : ℕ} {w : ℝ}
    {f : MvPowerSeries (Fin N) C}
    (h : OrdGe V.v (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) f w) :
    WtGe1 V i w f := by
  intro μ
  have h1 : r1 V.l i - del V.l i = 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i) := by
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    have h3 : 1 / (2 * (V.l : ℝ) ^ i) - 1 / (8 * (V.l : ℝ) ^ i) = 3 / (8 * (V.l : ℝ) ^ i) := by
      field_simp
      ring
    rw [← h3]
    unfold r1 del rho
    ring
  have h2 : (μ.degree : ℝ) = ∑ m, (μ m : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  refine le_trans ?_ (add_le_add (h μ) le_rfl)
  rw [← WithTop.coe_add, h1, h2, ← Finset.mul_sum]
  exact WithTop.coe_le_coe.2 (le_of_eq (by ring))

/- English proof (translation)
Introduce `C _ _ V d _ I J _ _ G S Z D a i h t ht N em hem c`. Take `⟨h1, h2, -⟩` from `GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ)) (fun b j => if b = em j then 1 else 0) (fun c s b => if s = 0 then (if c = b then 1 else 0) else D.al c s b) (fun j x => by simp) (fun c b => by simp) (fun c k x hk => by`. Simplify using `only [if_neg (show k ≠ 0 by omega)]`. Conclude with `h.2.2.2.1 c k x hk)`. Rewrite `h2` using `[← h.2.1]`.

Take `⟨k1, k2⟩` from `chain_data D em hem _ h1 h2`. Establish `h3 : (3 : ℝ) ≤ D.l` using `by exact_mod_cast D.l_ge`. Establish `hq : 0 < (D.l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hρ : 0 < 1 / ((D.l : ℝ) ^ 2 - 1)` using `by positivity`. Apply `wtGe1_of_ordGe` to reduce the goal to its premises.

Rewrite using `[← h.1, ← h.2.1, ← h.2.2.1]`. Distinguish the cases in `hc : D.lev c < Kn D.i`. Establish `hint : ∀ j, ((0 : ℝ) : WithTop ℝ) ≤ D.v (chainMat D (D.lev c) c (em j))` using `fun j => by`. Rewrite using `[h.1]`. Conclude with `h.chainMat_int _ _ _`.

Establish `hP` using `GlobalTheory.ChainCoord.ord_pure (v := D.v) fun j => GlobalTheory.ChainCoord.ord_pure_level (σ := 3 / (8 * (D.l : ℝ) ^ D.i)) (s := D.lev c) (c := (0 : Fin 1)) (π := fun s _ j => chainMat D s c (em j)) D.l_ge D.v_l hint j`. Use `GlobalTheory.ChainCoord.ord_add (GlobalTheory.ChainCoord.ord_mono (k1 c hc) (w' := 0) (by linarith)) (GlobalTheory.ChainCoord.ord_mono hP (w' := 0) (by positivity))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.ChainCoord.ord_mono (k2 c hc) (by linarith)`.
-/
theorem weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h t ht N em hem c
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if b = em j then 1 else 0)
    (fun c s b => if s = 0 then (if c = b then 1 else 0) else D.al c s b)
    (fun j x => by simp) (fun c b => by simp)
    (fun c k x hk => by
      simp only [if_neg (show k ≠ 0 by omega)]
      exact h.2.2.2.1 c k x hk)
  rw [← h.2.1] at h2
  obtain ⟨k1, k2⟩ := chain_data D em hem _ h1 h2
  have h3 : (3 : ℝ) ≤ D.l := by exact_mod_cast D.l_ge
  have hq : 0 < (D.l : ℝ) ^ 2 - 1 := by nlinarith
  have hρ : 0 < 1 / ((D.l : ℝ) ^ 2 - 1) := by positivity
  apply wtGe1_of_ordGe
  rw [← h.1, ← h.2.1, ← h.2.2.1]
  by_cases hc : D.lev c < Kn D.i
  · have hint : ∀ j, ((0 : ℝ) : WithTop ℝ) ≤ D.v (chainMat D (D.lev c) c (em j)) := fun j => by
      rw [h.1]
      exact h.chainMat_int _ _ _
    have hP := GlobalTheory.ChainCoord.ord_pure (v := D.v) fun j =>
      GlobalTheory.ChainCoord.ord_pure_level (σ := 3 / (8 * (D.l : ℝ) ^ D.i)) (s := D.lev c) (c := (0 : Fin 1))
        (π := fun s _ j => chainMat D s c (em j)) D.l_ge D.v_l hint j
    have := GlobalTheory.ChainCoord.ord_add (GlobalTheory.ChainCoord.ord_mono (k1 c hc) (w' := 0) (by linarith))
      (GlobalTheory.ChainCoord.ord_mono hP (w' := 0) (by positivity))
    rwa [sub_add_cancel] at this
  · exact GlobalTheory.ChainCoord.ord_mono (k2 c hc) (by linarith)

end GlobalTheory.LeafCoordWeight
