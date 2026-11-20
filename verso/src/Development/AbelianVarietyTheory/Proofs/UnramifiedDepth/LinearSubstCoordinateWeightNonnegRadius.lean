import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OrdGeOfLgSumEqLinear

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

/- English proof (translation)
Introduce `C _ _ V d _ I J _ _ G S t hT N e he c μ`. Establish `hU : ∀ i j, V.Ge 0 (S.U⁻¹ i j)` using `inv_int S.U (fun i j => S.U_int i j) S.unimod`. Establish `hco : ∀ (h : I ⊕ J → C) (w : ℝ), (∀ k, V.Ge w (h (Sum.inl k))) → ∀ b, V.Ge w (S.co h b)`. Introduce `h w hh b`. Establish `hs` using `VF.Ge.sum (s := Finset.univ) (fun k _ => VF.Ge.mul (hh k) (hU k b))`.

Rewrite `hs` using `[add_zero]`. Conclude with `hs`. Choose the witnesses or unpack the hypotheses as in `⟨z, hze, hzi⟩ : ∃ z : I → Fin N → C, (∀ j x, e j x = ∑ b, z b j * S.tan b x) ∧ ∀ b j, V.Ge 0 (z b j) := by`. Use `⟨fun b j => S.co (Sum.elim (e j) 0) b, fun j x => ?_, fun b j => hco _ 0 (fun k => he j k) b⟩` and prove the remaining obligations. Establish `hs` using `S.co_spec (Sum.elim (e j) 0) x`.

Simplify using `only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs`. Conclude with `hs.symm`. Choose the witnesses or unpack the hypotheses as in `⟨al, hal0, halk, hali⟩ : ∃ al : I → ℕ → I → C, (∀ c b, al c 0 b = if c = b then 1 else 0) ∧ (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) ∧ ∀ c (n : ℕ) b, V.Ge (-(n : ℝ)) (al c n b) := by`. Use `⟨fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (Sum.elim (S.al c k) 0) b, fun c b => if_pos rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `c k x hk`.

Establish `hk0 : k ≠ 0` using `by omega`. Establish `hs` using `S.co_spec (Sum.elim (S.al c k) 0) x`. Simplify using `only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs`. Rewrite using `[← hs]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[if_neg hk0, Sys.al, S.cur_zero_inl]`. Introduce `c n b`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `beta_reduce`.

Rewrite using `[if_pos rfl, Nat.cast_zero, neg_zero]`. Use `split_ifs`. Conclude with `VF.Ge.one`. Conclude with `VF.Ge.zero _`. Use `beta_reduce`.

Rewrite using `[if_neg (show n ≠ 0 by omega)]`. Conclude with `hco _ _ (fun k => lattice_inclusion_forms_injective G S c n (Sum.inl k)) b`. Take `⟨h0, hlog, -⟩` from `GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t hT (Fin N) e z al hze hal0 halk`. Set `σ` to `Fintype.equivFin I`. Establish `key` using `GlobalTheory.ExpWeight.ordGe_of_lgSum_eq_linear C V.v V.l V.l_prime V.v_l (Fintype.card I) N (fun a n b => al (σ.symm a) n (σ.symm b)) (fun a j => z (σ.symm a) j) (fun a => linPull e (t (σ.symm a))) (fun a b => by simp only [hal0, Equiv.apply_eq_iff_eq]) (fun a n b => hali _ _ _) …`.

Establish `hz` using `hzi (σ.symm a) j`. Unfold `VF.Ge at hz`. Rewrite using `[WithTop.coe_zero] at hz)` and apply the resulting hypothesis. Use the proof step `(fun a => h0 _) ?_ (σ c)`. Establish `hα` using `key μ`.

Simplify using `only [Equiv.symm_apply_apply] at hα`. Unfold `VF.Ge`. Use `le_trans ?_ hα` and prove the remaining obligations. Use `WithTop.coe_le_coe.mpr ?_` and prove the remaining obligations. Establish `hl : (1 : ℝ) < V.l` using `by exact_mod_cast V.l_prime.one_lt`.

Establish `hpos : (0 : ℝ) < 1 / ((V.l : ℝ) - 1)`. Establish `: (0 : ℝ) < (V.l : ℝ) - 1` using `by linarith`. Check the signs of the components of the expression. Rewrite using `[← Finset.mul_sum, ← Nat.cast_sum, ← Finsupp.degree_eq_sum]`. Establish `hd : ((μ.degree : ℕ) : ℝ) / ((V.l : ℝ) - 1) = 1 / ((V.l : ℝ) - 1) * (μ.degree : ℝ)` using `by ring`.

Rewrite using `[hd]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `b`. Use extensionality with `α`. Use `show (∑ n ∈ Finset.range (α.degree + 1), ∑ a, al (σ.symm a) n (σ.symm b) * MvPowerSeries.coeff α (linPull e (t (σ.symm a)) ^ (V.l ^ n))) = _`.

Rewrite using `[← hlog (σ.symm b) α]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Conclude with `Equiv.sum_comp σ.symm (fun a => al a n (σ.symm b) * MvPowerSeries.coeff α (linPull e (t a) ^ (V.l ^ n)))`.
-/
theorem linPull_coord_weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ (c : I) (μ : Fin N →₀ ℕ), V.Ge (-((μ.degree : ℝ) / ((V.l : ℝ) - 1))) (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ _ V d _ I J _ _ G S t hT N e he c μ

  have hU : ∀ i j, V.Ge 0 (S.U⁻¹ i j) := inv_int S.U (fun i j => S.U_int i j) S.unimod

  have hco : ∀ (h : I ⊕ J → C) (w : ℝ), (∀ k, V.Ge w (h (Sum.inl k))) → ∀ b, V.Ge w (S.co h b) := by
    intro h w hh b
    have hs := VF.Ge.sum (s := Finset.univ) (fun k _ => VF.Ge.mul (hh k) (hU k b))
    rw [add_zero] at hs
    exact hs

  obtain ⟨z, hze, hzi⟩ : ∃ z : I → Fin N → C,
      (∀ j x, e j x = ∑ b, z b j * S.tan b x) ∧ ∀ b j, V.Ge 0 (z b j) := by
    refine ⟨fun b j => S.co (Sum.elim (e j) 0) b, fun j x => ?_, fun b j => hco _ 0 (fun k => he j k) b⟩
    have hs := S.co_spec (Sum.elim (e j) 0) x
    simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
    exact hs.symm

  obtain ⟨al, hal0, halk, hali⟩ : ∃ al : I → ℕ → I → C, (∀ c b, al c 0 b = if c = b then 1 else 0) ∧
      (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) ∧
      ∀ c (n : ℕ) b, V.Ge (-(n : ℝ)) (al c n b) := by
    refine ⟨fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (Sum.elim (S.al c k) 0) b,
      fun c b => if_pos rfl, ?_, ?_⟩
    · intro c k x hk
      have hk0 : k ≠ 0 := by omega
      have hs := S.co_spec (Sum.elim (S.al c k) 0) x
      simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
      rw [← hs]
      refine Finset.sum_congr rfl fun b _ => ?_
      beta_reduce
      rw [if_neg hk0, Sys.al, S.cur_zero_inl]
    · intro c n b
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · beta_reduce
        rw [if_pos rfl, Nat.cast_zero, neg_zero]
        split_ifs
        · exact VF.Ge.one
        · exact VF.Ge.zero _
      · beta_reduce
        rw [if_neg (show n ≠ 0 by omega)]
        exact hco _ _ (fun k => lattice_inclusion_forms_injective G S c n (Sum.inl k)) b
  obtain ⟨h0, hlog, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t hT (Fin N) e z al hze hal0 halk

  let σ := Fintype.equivFin I
  have key := GlobalTheory.ExpWeight.ordGe_of_lgSum_eq_linear C V.v V.l V.l_prime V.v_l (Fintype.card I) N
    (fun a n b => al (σ.symm a) n (σ.symm b)) (fun a j => z (σ.symm a) j)
    (fun a => linPull e (t (σ.symm a)))
    (fun a b => by simp only [hal0, Equiv.apply_eq_iff_eq])
    (fun a n b => hali _ _ _)
    (fun a j => by
      have hz := hzi (σ.symm a) j
      unfold VF.Ge at hz
      rwa [WithTop.coe_zero] at hz)
    (fun a => h0 _) ?_ (σ c)
  · have hα := key μ
    simp only [Equiv.symm_apply_apply] at hα
    unfold VF.Ge
    refine le_trans ?_ hα
    refine WithTop.coe_le_coe.mpr ?_
    have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hpos : (0 : ℝ) < 1 / ((V.l : ℝ) - 1) := by
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      positivity
    rw [← Finset.mul_sum, ← Nat.cast_sum, ← Finsupp.degree_eq_sum]
    have hd : ((μ.degree : ℕ) : ℝ) / ((V.l : ℝ) - 1) = 1 / ((V.l : ℝ) - 1) * (μ.degree : ℝ) := by ring
    rw [hd]
    linarith
  · intro b
    ext α
    show (∑ n ∈ Finset.range (α.degree + 1), ∑ a, al (σ.symm a) n (σ.symm b) *
      MvPowerSeries.coeff α (linPull e (t (σ.symm a)) ^ (V.l ^ n))) = _
    rw [← hlog (σ.symm b) α]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Equiv.sum_comp σ.symm (fun a => al a n (σ.symm b) * MvPowerSeries.coeff α (linPull e (t a) ^ (V.l ^ n)))

end GlobalTheory.MainTerm
