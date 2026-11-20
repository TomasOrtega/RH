import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryAOfPropositionA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumInvSqLeSub

namespace Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz

/- English proof (translation)
Use `first`. Consider the case `(rw [← Finset.map_add_right_Ioc, Finset.prod_map]; rfl)`. Consider the case `(rw [← Finset.map_add_right_Ioc, Finset.prod_map]; simp [addRightEmbedding])`. Consider the case `(apply Finset.prod_nbij' (fun j => j - p) (fun j => j + p) <;> intro j hj <;>`. Apply the tactic sequence `simp only [Finset.mem_Ioc] at hj ⊢ <;> first | omega | (congr 1; omega))`.
-/
lemma prod_Ioc_shift (f : ℕ → ℝ) (p a b : ℕ) :
    ∏ j ∈ Ioc (a + p) (b + p), f j = ∏ j ∈ Ioc a b, f (j + p) := by
  first
  | (rw [← Finset.map_add_right_Ioc, Finset.prod_map]; rfl)
  | (rw [← Finset.map_add_right_Ioc, Finset.prod_map]; simp [addRightEmbedding])
  | (apply Finset.prod_nbij' (fun j => j - p) (fun j => j + p) <;> intro j hj <;>
      simp only [Finset.mem_Ioc] at hj ⊢ <;> first | omega | (congr 1; omega))

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`. Apply the tactic sequence `constructor <;> intro h <;> exact ⟨by omega, by omega⟩`.
-/
lemma Icc_one_eq (p : ℕ) : Icc 1 p = Ioc 0 p := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  constructor <;> intro h <;> exact ⟨by omega, by omega⟩

/- English proof (translation)
Unfold `Vand`. Simplify using `only [Icc_one_eq]`. Establish `h1 : ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i (p + q), (x i - x j) = (∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i p, (x i - x j)) * ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc 0 q, (x i - x (j + p))`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_Ioc]`. Rewrite using `[← Finset.prod_Ioc_consecutive _ hi.2 (Nat.le_add_right p q)]`. Use `congr 1`. Establish `hs` using `prod_Ioc_shift (fun j => x i - x j) p 0 q`. Rewrite `hs` using `[zero_add, Nat.add_comm q p]`.

Conclude with `hs`. Establish `h2 : ∏ i ∈ Ioc p (p + q), ∏ j ∈ Ioc i (p + q), (x i - x j) = ∏ i ∈ Ioc 0 q, ∏ j ∈ Ioc i q, (x (i + p) - x (j + p))`. Establish `hs` using `prod_Ioc_shift (fun i => ∏ j ∈ Ioc i (p + q), (x i - x j)) p 0 q`. Rewrite `hs` using `[zero_add, Nat.add_comm q p]`. Rewrite using `[hs]`.

Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hs2` using `prod_Ioc_shift (fun j => x (i + p) - x j) p i q`. Rewrite `hs2` using `[Nat.add_comm q p]`. Conclude with `hs2`. Rewrite using `[← Finset.prod_Ioc_consecutive _ (Nat.zero_le p) (Nat.le_add_right p q), h1, h2]`.
-/
lemma vand_split (p q : ℕ) (x : ℕ → ℝ) :
    Vand (p + q) x = Vand p x * (∏ i ∈ Icc 1 p, ∏ j ∈ Icc 1 q, (x i - x (j + p))) *
      Vand q (fun j => x (j + p)) := by
  unfold Vand
  simp only [Icc_one_eq]
  have h1 : ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i (p + q), (x i - x j)
      = (∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i p, (x i - x j)) *
        ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc 0 q, (x i - x (j + p)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ioc] at hi
    rw [← Finset.prod_Ioc_consecutive _ hi.2 (Nat.le_add_right p q)]
    congr 1
    have hs := prod_Ioc_shift (fun j => x i - x j) p 0 q
    rw [zero_add, Nat.add_comm q p] at hs
    exact hs
  have h2 : ∏ i ∈ Ioc p (p + q), ∏ j ∈ Ioc i (p + q), (x i - x j)
      = ∏ i ∈ Ioc 0 q, ∏ j ∈ Ioc i q, (x (i + p) - x (j + p)) := by
    have hs := prod_Ioc_shift (fun i => ∏ j ∈ Ioc i (p + q), (x i - x j)) p 0 q
    rw [zero_add, Nat.add_comm q p] at hs
    rw [hs]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hs2 := prod_Ioc_shift (fun j => x (i + p) - x j) p i q
    rw [Nat.add_comm q p] at hs2
    exact hs2
  rw [← Finset.prod_Ioc_consecutive _ (Nat.zero_le p) (Nat.le_add_right p q), h1, h2]

/- English proof (translation)
Unfold `Cfg.v`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma v_sub (c : Cfg) (i j : ℕ) : c.v i - c.v j = 4 * c.Del * ((j : ℝ) - (i : ℝ)) := by
  unfold Cfg.v
  ring

/- English proof (translation)
Establish `hki : (i : ℝ) + 1 ≤ (c.k : ℝ)` using `by exact_mod_cast hi`. Establish `h3 : 0 ≤ (c.k : ℝ) - 1 - (i : ℝ)` using `by linarith`. Establish `h4 : 0 ≤ c.Del` using `by linarith [h.hDel]`. Establish `h5` using `mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) h4) h3`. Unfold `Cfg.v`.

Combine the linear relations using `[h.hv0]`.
-/
lemma v_nonneg (c : Cfg) (h : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : 0 ≤ c.v i := by
  have hki : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  have h3 : 0 ≤ (c.k : ℝ) - 1 - (i : ℝ) := by linarith
  have h4 : 0 ≤ c.Del := by linarith [h.hDel]
  have h5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) h4) h3
  unfold Cfg.v
  linarith [h.hv0]

/- English proof (translation)
Unfold `Vand`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hj` using `[Finset.mem_Ioc]`. Rewrite using `[v_sub]`. Establish `hij : (i : ℝ) < (j : ℝ)` using `by exact_mod_cast hj.1`. Establish `hD : 0 < 4 * c.Del` using `by linarith [h.hDel]`. Conclude with `mul_pos hD (by linarith)`.
-/
lemma vand_v_pos (c : Cfg) (h : c.Ok) (p : ℕ) : 0 < Vand p c.v := by
  unfold Vand
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Ioc] at hj
  rw [v_sub]
  have hij : (i : ℝ) < (j : ℝ) := by exact_mod_cast hj.1
  have hD : 0 < 4 * c.Del := by linarith [h.hDel]
  exact mul_pos hD (by linarith)

/- English proof (translation)
Introduce `j hij hjm`. Proceed by induction on `j with`. Consider the case `zero => omega`. Consider the case `succ n ih`. Distinguish the cases in `hc : i < n`.

Establish `h1` using `ih hc (by omega)`. Establish `h2` using `h.hgap n (by omega) (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hin : i = n` using `by omega`. Rewrite using `[← hin]`.

Conclude with `h.hgap i hi (by omega)`.
-/
lemma b_step (c : Cfg) (h : c.Ok) (i : ℕ) (hi : 1 ≤ i) :
    ∀ j, i < j → j ≤ c.m → c.b i + 1 ≤ c.b j := by
  intro j hij hjm
  induction j with
  | zero => omega
  | succ n ih =>
    by_cases hc : i < n
    · have h1 := ih hc (by omega)
      have h2 := h.hgap n (by omega) (by omega)
      linarith
    · have hin : i = n := by omega
      rw [← hin]
      exact h.hgap i hi (by omega)

/- English proof (translation)
Break down `Nat.eq_or_lt_of_le hj with h1 | h1` into its components or cases. Rewrite using `[← h1]`. Conclude with `h.hb1`. Establish `h2` using `b_step c h 1 le_rfl j h1 hm`. Combine the linear relations using `[h.hb1]`.
-/
lemma b_ge_one (c : Cfg) (h : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h1 | h1
  · rw [← h1]
    exact h.hb1
  · have h2 := b_step c h 1 le_rfl j h1 hm
    linarith [h.hb1]

/- English proof (translation)
Establish `h1 : ∏ i ∈ s, (1:ℝ) ≤ ∏ i ∈ s, f i` using `Finset.prod_le_prod (fun i _ => zero_le_one) h`. Simplify using `using h1`.
-/
lemma one_le_prod_real {α : Type} (s : Finset α) (f : α → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have h1 : ∏ i ∈ s, (1:ℝ) ≤ ∏ i ∈ s, f i :=
    Finset.prod_le_prod (fun i _ => zero_le_one) h
  simpa using h1

/- English proof (translation)
Unfold `Cfg.prodb`. Apply `one_le_prod_real` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`. Conclude with `b_ge_one c h j hj.1 hj.2`.
-/
lemma prodb_ge_one (c : Cfg) (h : c.Ok) : 1 ≤ c.prodb := by
  unfold Cfg.prodb
  apply one_le_prod_real
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact b_ge_one c h j hj.1 hj.2

/- English proof (translation)
Introduce `c h`. Establish `hk` using `h.hk`. Establish `hkm : c.k + c.m - 1 = (c.k - 1) + c.m` using `by omega`. Establish `vcongr : ∀ (p : ℕ) (x y : ℕ → ℝ), (∀ i, 1 ≤ i → i ≤ p → x i = y i) → Vand p x = Vand p y`. Introduce `p x y hxy`.

Unfold `Vand`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hi` using `[Finset.mem_Icc]`. Rewrite `hj` using `[Finset.mem_Ioc]`. Rewrite using `[hxy i hi.1 hi.2, hxy j (by omega) hj.2]`. Establish `hlam1 : ∀ i, i ≤ c.k - 1 → c.lam i = c.v i`. Introduce `i hi`.

Establish `hi' : i < c.k` using `by omega`. Simplify using `only [Cfg.lam, if_pos hi']`. Establish `hlam2 : ∀ j, 1 ≤ j → c.lam (j + (c.k - 1)) = -c.b j`. Introduce `j hj`. Establish `h1 : ¬ (j + (c.k - 1) < c.k)` using `by omega`.

Establish `h2 : j + (c.k - 1) + 1 - c.k = j` using `by omega`. Simplify using `only [Cfg.lam, if_neg h1, h2]`. Establish `eqn : Vand (c.k + c.m - 1) c.lam = Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Vand c.m (fun j => -c.b j)`. Rewrite using `[hkm, vand_split (c.k - 1) c.m c.lam]`. Establish `e1 : Vand (c.k - 1) c.lam = Vand (c.k - 1) c.v` using `vcongr _ _ _ (fun i _ hi2 => hlam1 i hi2)`.

Establish `e2 : Vand c.m (fun j => c.lam (j + (c.k - 1))) = Vand c.m (fun j => -c.b j)` using `vcongr _ _ _ (fun j hj1 _ => hlam2 j hj1)`. Establish `e3 : ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.lam i - c.lam (j + (c.k - 1))) = ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`. Rewrite using `[hlam1 i hi.2, hlam2 j hj.1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, e3]`. Use `⟨eqn, ?_⟩` and prove the remaining obligations. Establish `hC : c.prodb ^ (c.k - 1) ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)`. Combine the equalities or inequalities in the displayed calculation. Consider the case `(rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; done)`.

Consider the case `(rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; rfl)`. Consider the case `(unfold Cfg.prodb; rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel])`. Use `_ ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`.

Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`. Combine the linear relations using `[b_ge_one c h j hj.1 hj.2]`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_Icc]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`. Combine the linear relations using `[b_ge_one c h j hj.1 hj.2]`.

Introduce `j _`. Combine the linear relations using `[v_nonneg c h i (by omega)]`. Establish `hV : 1 ≤ Vand c.m (fun j => -c.b j)`. Unfold `Vand`. Apply `one_le_prod_real` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Apply `one_le_prod_real` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Ioc]`.

Establish `hb` using `b_step c h i hi.1 j hj.1 hj.2`. Use `show (1:ℝ) ≤ -c.b i - -c.b j`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv` using `vand_v_pos c h (c.k - 1)`. Establish `hpb` using `prodb_ge_one c h`.

Establish `hC0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)` using `le_trans (pow_nonneg (by linarith) _) hC`. Rewrite using `[eqn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem vandLamLower : VandLamLower := by
  intro c h
  have hk := h.hk
  have hkm : c.k + c.m - 1 = (c.k - 1) + c.m := by omega
  have vcongr : ∀ (p : ℕ) (x y : ℕ → ℝ), (∀ i, 1 ≤ i → i ≤ p → x i = y i) → Vand p x = Vand p y := by
    intro p x y hxy
    unfold Vand
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_Ioc] at hj
    rw [hxy i hi.1 hi.2, hxy j (by omega) hj.2]
  have hlam1 : ∀ i, i ≤ c.k - 1 → c.lam i = c.v i := by
    intro i hi
    have hi' : i < c.k := by omega
    simp only [Cfg.lam, if_pos hi']
  have hlam2 : ∀ j, 1 ≤ j → c.lam (j + (c.k - 1)) = -c.b j := by
    intro j hj
    have h1 : ¬ (j + (c.k - 1) < c.k) := by omega
    have h2 : j + (c.k - 1) + 1 - c.k = j := by omega
    simp only [Cfg.lam, if_neg h1, h2]
  have eqn : Vand (c.k + c.m - 1) c.lam = Vand (c.k - 1) c.v *
      (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Vand c.m (fun j => -c.b j) := by
    rw [hkm, vand_split (c.k - 1) c.m c.lam]
    have e1 : Vand (c.k - 1) c.lam = Vand (c.k - 1) c.v :=
      vcongr _ _ _ (fun i _ hi2 => hlam1 i hi2)
    have e2 : Vand c.m (fun j => c.lam (j + (c.k - 1))) = Vand c.m (fun j => -c.b j) :=
      vcongr _ _ _ (fun j hj1 _ => hlam2 j hj1)
    have e3 : ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.lam i - c.lam (j + (c.k - 1)))
        = ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [hlam1 i hi.2, hlam2 j hj.1]
      ring
    rw [e1, e2, e3]
  refine ⟨eqn, ?_⟩
  have hC : c.prodb ^ (c.k - 1) ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
    calc c.prodb ^ (c.k - 1) = ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, c.b j := by
          first
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; done)
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; rfl)
          | (unfold Cfg.prodb; rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel])
      _ ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
          apply Finset.prod_le_prod
          · intro i _
            apply Finset.prod_nonneg
            intro j hj
            rw [Finset.mem_Icc] at hj
            linarith [b_ge_one c h j hj.1 hj.2]
          · intro i hi
            rw [Finset.mem_Icc] at hi
            apply Finset.prod_le_prod
            · intro j hj
              rw [Finset.mem_Icc] at hj
              linarith [b_ge_one c h j hj.1 hj.2]
            · intro j _
              linarith [v_nonneg c h i (by omega)]
  have hV : 1 ≤ Vand c.m (fun j => -c.b j) := by
    unfold Vand
    apply one_le_prod_real
    intro i hi
    rw [Finset.mem_Icc] at hi
    apply one_le_prod_real
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hb := b_step c h i hi.1 j hj.1 hj.2
    show (1:ℝ) ≤ -c.b i - -c.b j
    linarith
  have hv := vand_v_pos c h (c.k - 1)
  have hpb := prodb_ge_one c h
  have hC0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
    le_trans (pow_nonneg (by linarith) _) hC
  rw [eqn]
  calc Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1)
      ≤ Vand (c.k - 1) c.v * ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
        mul_le_mul_of_nonneg_left hC hv.le
    _ = Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * 1 :=
        (mul_one _).symm
    _ ≤ Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) *
          Vand c.m (fun j => -c.b j) :=
        mul_le_mul_of_nonneg_left hV (mul_nonneg hv.le hC0)

/- English proof (translation)
Introduce `c de de' ka rd g VV h hvth hw hw' hka hrd hg hVV`. Take `⟨hV, hV', hL⟩` from `hVW c de de' h hvth hw hw'`. Establish `hk4 : (4:ℝ) ≤ (c.k:ℝ)` using `by exact_mod_cast h.hk`. Establish `hk0 : (0:ℝ) < (c.k:ℝ)` using `by linarith`. Establish `hkne : (c.k:ℝ) ≠ 0` using `hk0.ne'`.

Establish `hP1 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de))`. Unfold `TcritPow`. Check the signs of the components of the expression. Establish `hP2 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de'))`. Unfold `TcritPow`.

Check the signs of the components of the expression. Establish `hR : 0 < Vand c.k (c.u de') / Vand c.k (c.u de)` using `div_pos hV' hV`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Tcrit`. Rewrite using `[← Real.div_rpow hP1.le hP2.le]`.

Use `congr 1`. Establish `key : ∀ P : ℝ, 0 < P → (P / Vand c.k (c.u de)) / (P / Vand c.k (c.u de')) = Vand c.k (c.u de') / Vand c.k (c.u de)`. Introduce `P hP`. Establish `h1` using `hP.ne'`. Establish `h2` using `hV.ne'`.

Establish `h3` using `hV'.ne'`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Consider the case `(rw [div_div_div_cancel_left' _ _ h1])`.

Unfold `TcritPow`. Conclude with `key _ (by positivity)`. Establish `hrw : (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) = Real.exp (Real.log (Vand c.k (c.u de') / Vand c.k (c.u de)) * (1 / (c.k:ℝ)))` using `Real.rpow_def_of_pos hR _`. Rewrite using `[hrw]`. Take `⟨hL1, hL2⟩` from `abs_le.mp hL`.

Establish `ht0 : (0:ℝ) < 1 / (c.k:ℝ)` using `by positivity`. Establish `ht : (c.k:ℝ) * (1 / (c.k:ℝ)) = 1` using `by first`. Consider the case `exact mul_one_div_cancel hkne`. Consider the case `field_simp`. Establish `ht4 : (1:ℝ) / (c.k:ℝ) ≤ 1 / 4` using `one_div_le_one_div_of_le (by norm_num) hk4`.

Establish `e3 : ((c.k:ℝ) / 2 + 1) * (1 / (c.k:ℝ)) = 1 / 2 + 1 / (c.k:ℝ)`. Take the linear combination `(1/2:ℝ) * ht`. Establish `u1` using `mul_le_mul_of_nonneg_right hL2 ht0.le`. Establish `u2` using `mul_le_mul_of_nonneg_right hL1 ht0.le`. Prove the components needed by the constructor for the conclusion.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tcritWords_of (hVW : VandWords) : TcritWords := by
  intro c de de' ka rd g VV h hvth hw hw' hka hrd hg hVV
  obtain ⟨hV, hV', hL⟩ := hVW c de de' h hvth hw hw'
  have hk4 : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast h.hk
  have hk0 : (0:ℝ) < (c.k:ℝ) := by linarith
  have hkne : (c.k:ℝ) ≠ 0 := hk0.ne'
  have hP1 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de)) := by
    unfold TcritPow
    positivity
  have hP2 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de')) := by
    unfold TcritPow
    positivity
  have hR : 0 < Vand c.k (c.u de') / Vand c.k (c.u de) := div_pos hV' hV
  refine ⟨?_, ?_⟩
  · unfold Tcrit
    rw [← Real.div_rpow hP1.le hP2.le]
    congr 1
    have key : ∀ P : ℝ, 0 < P →
        (P / Vand c.k (c.u de)) / (P / Vand c.k (c.u de')) = Vand c.k (c.u de') / Vand c.k (c.u de) := by
      intro P hP
      have h1 := hP.ne'
      have h2 := hV.ne'
      have h3 := hV'.ne'
      first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_div_div_cancel_left' _ _ h1])
    unfold TcritPow
    exact key _ (by positivity)
  · have hrw : (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) =
        Real.exp (Real.log (Vand c.k (c.u de') / Vand c.k (c.u de)) * (1 / (c.k:ℝ))) :=
      Real.rpow_def_of_pos hR _
    rw [hrw]
    obtain ⟨hL1, hL2⟩ := abs_le.mp hL
    have ht0 : (0:ℝ) < 1 / (c.k:ℝ) := by positivity
    have ht : (c.k:ℝ) * (1 / (c.k:ℝ)) = 1 := by
      first
      | exact mul_one_div_cancel hkne
      | field_simp
    have ht4 : (1:ℝ) / (c.k:ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hk4
    have e3 : ((c.k:ℝ) / 2 + 1) * (1 / (c.k:ℝ)) = 1 / 2 + 1 / (c.k:ℝ) := by
      linear_combination (1/2:ℝ) * ht
    have u1 := mul_le_mul_of_nonneg_right hL2 ht0.le
    have u2 := mul_le_mul_of_nonneg_right hL1 ht0.le
    constructor
    · apply Real.exp_le_exp.mpr
      nlinarith
    · apply Real.exp_le_exp.mpr
      nlinarith

/- English proof (translation)
Establish `h1 : Real.exp (1/4) ^ 4 = Real.exp 1` using `by first`. Consider the case `(rw [← Real.exp_nat_mul]; norm_num)`. Consider the case `(rw [← Real.exp_nat_mul]; congr 1; norm_num)`. Consider the case `(rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)`. Establish `h2` using `Real.exp_one_lt_d9`.

Establish `h3 : 0 < Real.exp (1/4)` using `Real.exp_pos _`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `ht2 : (1.69:ℝ) < Real.exp (1/4) ^ 2` using `by nlinarith`. Establish `ht4 : (2.8561:ℝ) < Real.exp (1/4) ^ 4` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma E_le : Real.exp (1/4) ≤ 1.3 := by
  have h1 : Real.exp (1/4) ^ 4 = Real.exp 1 := by
    first
    | (rw [← Real.exp_nat_mul]; norm_num)
    | (rw [← Real.exp_nat_mul]; congr 1; norm_num)
    | (rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1/4) := Real.exp_pos _
  by_contra hc
  push_neg at hc
  have ht2 : (1.69:ℝ) < Real.exp (1/4) ^ 2 := by nlinarith
  have ht4 : (2.8561:ℝ) < Real.exp (1/4) ^ 4 := by nlinarith
  linarith

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
lemma E_pos : 0 < Real.exp (1/4) := Real.exp_pos _

/- English proof (translation)
Establish `hE` using `E_le`. Establish `hE0` using `E_pos`. Establish `hf : (0:ℝ) < (n.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos n`. Establish `hx : (0:ℝ) ≤ (n:ℝ) + 2` using `by positivity`. Establish `h1 : ((n:ℝ) + 2) ^ n / (n.factorial : ℝ) ≤ Real.exp ((n:ℝ) + 2)` using `by first`.

Consider the case `exact Real.pow_div_factorial_le_exp _ hx n`. Consider the case `exact Real.pow_div_factorial_le_exp hx n`. Establish `h2 : ((n:ℝ) + 2) ^ n ≤ Real.exp ((n:ℝ) + 2) * (n.factorial : ℝ)` using `by first`. Consider the case `(rwa [div_le_iff₀ hf] at h1)`. Consider the case `(rwa [div_le_iff hf] at h1)`.

Consider the case `(have h1' := mul_le_mul_of_nonneg_right h1 hf.le`. Rewrite using `[div_mul_cancel₀ _ hf.ne'] at h1')` and apply the resulting hypothesis. Establish `h3 : Real.exp ((n:ℝ) + 2) = Real.exp 1 ^ (n + 2)`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hX : ((n:ℝ) + 2) ^ n ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `he1 : Real.exp 1 ≤ 2.72` using `by linarith [Real.exp_one_lt_d9]`.

Establish `he2 : Real.exp 1 ^ (n + 2) ≤ (2.72:ℝ) ^ (n + 2)` using `by first`. Consider the case `exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 (n + 2)`. Consider the case `exact pow_le_pow_left (Real.exp_pos 1).le he1 (n + 2)`. Consider the case `gcongr`. Conclude with `mul_le_mul_of_nonneg_right he2 hf.le`.

Establish `hEp : Real.exp (1/4) ^ (n + 1) ≤ (1.3:ℝ) ^ (n + 1)` using `by first`. Consider the case `exact pow_le_pow_left₀ hE0.le hE (n + 1)`. Consider the case `exact pow_le_pow_left hE0.le hE (n + 1)`. Consider the case `gcongr`. Establish `key : ∀ m : ℕ, 2 ≤ m → 2 * (0.38:ℝ) ^ (m + 2) * (2.72:ℝ) ^ (m + 2) * (1.3:ℝ) ^ (m + 1) ≤ 4 ^ m`.

Introduce `m hm`. Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ k _ ih`. Establish `e1 : 2 * (0.38:ℝ) ^ (k + 1 + 2) * (2.72:ℝ) ^ (k + 1 + 2) * (1.3:ℝ) ^ (k + 1 + 1) = (0.38 * 2.72 * 1.3) * (2 * (0.38:ℝ) ^ (k + 2) * (2.72:ℝ) ^ (k + 2) * (1.3:ℝ) ^ (k + 1))`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (4:ℝ) ^ (k + 1) = 4 ^ k * 4` using `pow_succ 4 k`. Establish `h4 : (0:ℝ) < 4 ^ k` using `pow_pos (by norm_num) k`. Rewrite using `[e1, e2]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hQ` using `key n hn`. Establish `hA : 0 ≤ 2 * (0.38:ℝ) ^ (n + 2)` using `by positivity`. Establish `hY : 0 ≤ ((n:ℝ) + 2) ^ n` using `by positivity`. Establish `hZ : 0 ≤ Real.exp (1/4) ^ (n + 1)` using `by positivity`. Establish `hW : 0 ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ)` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_left hX hA) hEp hZ` to reduce the goal to its premises. Conclude with `mul_nonneg hA hW`. Use `_ = (2 * (0.38:ℝ) ^ (n + 2) * (2.72:ℝ) ^ (n + 2) * (1.3:ℝ) ^ (n + 1)) * (n.factorial : ℝ) := by`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ 4 ^ n * (n.factorial : ℝ) := mul_le_mul_of_nonneg_right hQ hf.le`.
-/
lemma fac_bound (n : ℕ) (hn : 2 ≤ n) :
    2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1) ≤ 4 ^ n * (n.factorial : ℝ) := by
  have hE := E_le
  have hE0 := E_pos
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hx : (0:ℝ) ≤ (n:ℝ) + 2 := by positivity
  have h1 : ((n:ℝ) + 2) ^ n / (n.factorial : ℝ) ≤ Real.exp ((n:ℝ) + 2) := by
    first
    | exact Real.pow_div_factorial_le_exp _ hx n
    | exact Real.pow_div_factorial_le_exp hx n
  have h2 : ((n:ℝ) + 2) ^ n ≤ Real.exp ((n:ℝ) + 2) * (n.factorial : ℝ) := by
    first
    | (rwa [div_le_iff₀ hf] at h1)
    | (rwa [div_le_iff hf] at h1)
    | (have h1' := mul_le_mul_of_nonneg_right h1 hf.le
       rwa [div_mul_cancel₀ _ hf.ne'] at h1')
  have h3 : Real.exp ((n:ℝ) + 2) = Real.exp 1 ^ (n + 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hX : ((n:ℝ) + 2) ^ n ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by
    calc ((n:ℝ) + 2) ^ n ≤ Real.exp ((n:ℝ) + 2) * (n.factorial : ℝ) := h2
      _ = Real.exp 1 ^ (n + 2) * (n.factorial : ℝ) := by rw [h3]
      _ ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by
        have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
        have he2 : Real.exp 1 ^ (n + 2) ≤ (2.72:ℝ) ^ (n + 2) := by
          first
          | exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 (n + 2)
          | exact pow_le_pow_left (Real.exp_pos 1).le he1 (n + 2)
          | gcongr
        exact mul_le_mul_of_nonneg_right he2 hf.le
  have hEp : Real.exp (1/4) ^ (n + 1) ≤ (1.3:ℝ) ^ (n + 1) := by
    first
    | exact pow_le_pow_left₀ hE0.le hE (n + 1)
    | exact pow_le_pow_left hE0.le hE (n + 1)
    | gcongr
  have key : ∀ m : ℕ, 2 ≤ m →
      2 * (0.38:ℝ) ^ (m + 2) * (2.72:ℝ) ^ (m + 2) * (1.3:ℝ) ^ (m + 1) ≤ 4 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k _ ih =>
      have e1 : 2 * (0.38:ℝ) ^ (k + 1 + 2) * (2.72:ℝ) ^ (k + 1 + 2) * (1.3:ℝ) ^ (k + 1 + 1)
          = (0.38 * 2.72 * 1.3) * (2 * (0.38:ℝ) ^ (k + 2) * (2.72:ℝ) ^ (k + 2) * (1.3:ℝ) ^ (k + 1)) := by
        ring
      have e2 : (4:ℝ) ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
      have h4 : (0:ℝ) < 4 ^ k := pow_pos (by norm_num) k
      rw [e1, e2]
      nlinarith
  have hQ := key n hn
  have hA : 0 ≤ 2 * (0.38:ℝ) ^ (n + 2) := by positivity
  have hY : 0 ≤ ((n:ℝ) + 2) ^ n := by positivity
  have hZ : 0 ≤ Real.exp (1/4) ^ (n + 1) := by positivity
  have hW : 0 ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by positivity
  calc 2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1)
      ≤ 2 * (0.38:ℝ) ^ (n + 2) * ((2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ)) * (1.3:ℝ) ^ (n + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hX hA) hEp hZ
        exact mul_nonneg hA hW
    _ = (2 * (0.38:ℝ) ^ (n + 2) * (2.72:ℝ) ^ (n + 2) * (1.3:ℝ) ^ (n + 1)) * (n.factorial : ℝ) := by
        ring
    _ ≤ 4 ^ n * (n.factorial : ℝ) := mul_le_mul_of_nonneg_right hQ hf.le

/- English proof (translation)
Establish `h : (α * α⁻¹) ^ n = 1` using `by rw [mul_inv_cancel₀ hα, one_pow]`. Take the linear combination `(2 ^ n * κ ^ (n + 1) * E ^ (n + 1) * e ^ (n + 1) * B ^ (n + 1) * Vv * α⁻¹) * h`.
-/
lemma nontop_alg (n : ℕ) (κ e B α E Vv : ℝ) (hα : α ≠ 0) :
    (κ * e / (1 + 0) * B / α) ^ (n + 1) * ((2 * α) ^ n * (E ^ (n + 1) * Vv)) =
      (2 * κ * E) ^ (n + 1) * (e ^ (n + 1) * B) * (1 / α) * (Vv * B ^ n / 2) := by
  have h : (α * α⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hα, one_pow]
  linear_combination (2 ^ n * κ ^ (n + 1) * E ^ (n + 1) * e ^ (n + 1) * B ^ (n + 1) * Vv * α⁻¹) * h

/- English proof (translation)
Establish `h1 : (a * a⁻¹) ^ n = 1` using `by rw [mul_inv_cancel₀ ha, one_pow]`. Establish `h2 : (b * b⁻¹) ^ n = 1` using `by rw [mul_inv_cancel₀ hb, one_pow]`. Establish `h3 : (θ * θ⁻¹) ^ n = 1` using `by rw [mul_inv_cancel₀ hθ, one_pow]`. Rewrite using `[div_div_eq_mul_div]`. Take the linear combination `((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) * (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) * (b * b⁻¹) ^ n * (θ * θ⁻¹) ^ n) * h1 + ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) * (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * …`.
-/
lemma top_alg (n : ℕ) (κ e B a b K θ E W : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) :
    (κ * e / θ * B / (a * b / K)) ^ (n + 2) * ((a ^ n * (a + b)) * ((E ^ (n + 1) * W) * (b * θ) ^ n)) =
      (e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
        (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) := by
  have h1 : (a * a⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ ha, one_pow]
  have h2 : (b * b⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hb, one_pow]
  have h3 : (θ * θ⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hθ, one_pow]
  rw [div_div_eq_mul_div]
  linear_combination
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) * (b * b⁻¹) ^ n * (θ * θ⁻¹) ^ n) * h1 +
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) * (θ * θ⁻¹) ^ n) * h2 +
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1))) * h3

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Rewrite `hVu`, the goal using `[show n + 1 - 1 = n by omega]`. Establish `hα0 : 0 < α` using `by linarith`. Establish `hB0 : 0 ≤ B` using `by linarith`. Establish `hbase : 0 ≤ 0.38 * e / (1 + 0) * B / α` using `by positivity`.

Establish `key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w → x * y * z * w ≤ w`. Introduce `x y z w hx hx1 hy hy1 hz hz1 hw`. Establish `h1 : x * y ≤ 1` using `by nlinarith`. Establish `h1' : 0 ≤ x * y` using `mul_nonneg hx hy`. Establish `h2 : x * y * z ≤ 1` using `by nlinarith`.

Establish `h2' : 0 ≤ x * y * z` using `mul_nonneg h1' hz`. Use the polynomial consequences of the given equalities and inequalities. Establish `hE1 : 2 * 0.38 * Real.exp (1/4) ≤ 1` using `by linarith [E_le]`. Establish `hE0 : 0 ≤ 2 * 0.38 * Real.exp (1/4)` using `by positivity`. Establish `hA1 : (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Consider the case `exact pow_le_pow_left₀ hE0 hE1 (n + 1)`. Consider the case `exact pow_le_pow_left hE0 hE1 (n + 1)`. Consider the case `gcongr`. Use `_ = 1 := one_pow _`.

Establish `hA0 : 0 ≤ (2 * 0.38 * Real.exp (1/4)) ^ (n + 1)` using `pow_nonneg hE0 _`. Establish `hC1 : 1 / α ≤ 1` using `by first`. Consider the case `(rw [div_le_one hα0]; linarith)`. Consider the case `(rw [div_le_one₀ hα0]; linarith)`. Consider the case `(rw [div_le_iff₀ hα0]; linarith)`.

Consider the case `(rw [div_le_iff hα0]; linarith)`. Establish `hC0 : 0 ≤ 1 / α` using `by positivity`. Establish `hS0 : 0 ≤ e ^ (n + 1) * B` using `by positivity`. Establish `hR : 0 ≤ Vv * B ^ n / 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma non_top_final_inequality (k : ℕ) (hk : 1 ≤ k) (e B α Vv Vu : ℝ) (hα : 1 ≤ α) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hVv : 0 < Vv) (hs : e ^ k * B ≤ 1)
    (hVu : Vu ≤ (2 * α) ^ (k - 1) * (Real.exp (1/4) ^ k * Vv)) :
    (0.38 * e / (1 + 0) * B / α) ^ k * Vu ≤ Vv * B ^ (k - 1) / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega] at hVu ⊢
  have hα0 : 0 < α := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hbase : 0 ≤ 0.38 * e / (1 + 0) * B / α := by positivity
  have key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w →
      x * y * z * w ≤ w := by
    intro x y z w hx hx1 hy hy1 hz hz1 hw
    have h1 : x * y ≤ 1 := by nlinarith
    have h1' : 0 ≤ x * y := mul_nonneg hx hy
    have h2 : x * y * z ≤ 1 := by nlinarith
    have h2' : 0 ≤ x * y * z := mul_nonneg h1' hz
    nlinarith
  have hE1 : 2 * 0.38 * Real.exp (1/4) ≤ 1 := by linarith [E_le]
  have hE0 : 0 ≤ 2 * 0.38 * Real.exp (1/4) := by positivity
  have hA1 : (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) ≤ 1 := by
    calc (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) ≤ 1 ^ (n + 1) := by
          first
          | exact pow_le_pow_left₀ hE0 hE1 (n + 1)
          | exact pow_le_pow_left hE0 hE1 (n + 1)
          | gcongr
      _ = 1 := one_pow _
  have hA0 : 0 ≤ (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) := pow_nonneg hE0 _
  have hC1 : 1 / α ≤ 1 := by
    first
    | (rw [div_le_one hα0]; linarith)
    | (rw [div_le_one₀ hα0]; linarith)
    | (rw [div_le_iff₀ hα0]; linarith)
    | (rw [div_le_iff hα0]; linarith)
  have hC0 : 0 ≤ 1 / α := by positivity
  have hS0 : 0 ≤ e ^ (n + 1) * B := by positivity
  have hR : 0 ≤ Vv * B ^ n / 2 := by positivity
  calc (0.38 * e / (1 + 0) * B / α) ^ (n + 1) * Vu
      ≤ (0.38 * e / (1 + 0) * B / α) ^ (n + 1) * ((2 * α) ^ n * (Real.exp (1/4) ^ (n + 1) * Vv)) :=
        mul_le_mul_of_nonneg_left hVu (pow_nonneg hbase _)
    _ = (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) * (e ^ (n + 1) * B) * (1 / α) * (Vv * B ^ n / 2) :=
        nontop_alg n 0.38 e B α (Real.exp (1/4)) Vv hα0.ne'
    _ ≤ Vv * B ^ n / 2 := key3 _ _ _ _ hA0 hA1 hS0 hs hC0 hC1 hR

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, k = n + 2` from `⟨k - 2, by omega⟩`. Establish `hn : 2 ≤ n` using `by omega`. Rewrite `hVu`, the goal using `[show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]`. Move the coercions through the operations in `at hq ⊢`. Establish `hθ0 : 0 < θ` using `by linarith`.

Establish `hB0 : 0 ≤ B` using `by linarith`. Establish `hK0 : 0 < ((n:ℝ) + 2) * Del` using `by positivity`. Establish `hbase : 0 ≤ 0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del))` using `by positivity`. Establish `key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w → x * y * z * w ≤ w`. Introduce `x y z w hx hx1 hy hy1 hz hz1 hw`.

Establish `h1 : x * y ≤ 1` using `by nlinarith`. Establish `h1' : 0 ≤ x * y` using `mul_nonneg hx hy`. Establish `h2 : x * y * z ≤ 1` using `by nlinarith`. Establish `h2' : 0 ≤ x * y * z` using `mul_nonneg h1' hz`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hX2 : (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2) ≤ 1`. Establish `hd : 0 < a ^ 2 * b ^ 2` using `by positivity`. Use `first`. Consider the case `(rw [div_le_one hd]; linarith)`. Consider the case `(rw [div_le_one₀ hd]; linarith)`.

Consider the case `(rw [div_le_iff₀ hd]; linarith)`. Consider the case `(rw [div_le_iff hd]; linarith)`. Establish `hX2' : 0 ≤ (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2)` using `by positivity`. Establish `hX3 : 1 / θ ^ 2 ≤ 1`. Establish `hd : 0 < θ ^ 2` using `by positivity`.

Use `first`. Consider the case `(rw [div_le_one hd]; nlinarith)`. Consider the case `(rw [div_le_one₀ hd]; nlinarith)`. Consider the case `(rw [div_le_iff₀ hd]; nlinarith)`. Consider the case `(rw [div_le_iff hd]; nlinarith)`.

Establish `hX3' : 0 ≤ 1 / θ ^ 2` using `by positivity`. Establish `hX1' : 0 ≤ e ^ (n + 2) * B` using `by positivity`. Establish `hfb` using `fac_bound n hn`. Establish `hD : 0 ≤ Del ^ n * W * B ^ (n + 1) / 2` using `by positivity`. Establish `hYZ : (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1)) ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hYZ0 : 0 ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1)) := key3 _ _ _ _ hX1' hs hX2' hX2 hX3' hX3 hYZ0`.

Use `_ ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := hYZ`.
-/
lemma top_final_inequality (k : ℕ) (hk : 4 ≤ k) (e B a b Del θ W Vu : ℝ) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hW : 0 < W) (hs : e ^ k * B ≤ 1) (hθ : 1 ≤ θ) (ha : 0 < a) (hb : 0 < b) (hDel : 0 < Del)
    (hq : ((k:ℝ) * Del) ^ 2 * (a + b) ≤ a ^ 2 * b ^ 2)
    (hVu : Vu ≤ (a ^ (k - 2) * (a + b)) * ((Real.exp (1/4) ^ (k - 1) * W) * (b * θ) ^ (k - 2))) :
    (0.38 * e / θ * B / (a * b / ((k:ℝ) * Del))) ^ k * Vu ≤
      (W * (4 * Del) ^ (k - 2) * ((k - 2).factorial : ℝ)) * B ^ (k - 1) / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega] at hVu ⊢
  push_cast at hq ⊢
  have hθ0 : 0 < θ := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hK0 : 0 < ((n:ℝ) + 2) * Del := by positivity
  have hbase : 0 ≤ 0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del)) := by positivity
  have key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w →
      x * y * z * w ≤ w := by
    intro x y z w hx hx1 hy hy1 hz hz1 hw
    have h1 : x * y ≤ 1 := by nlinarith
    have h1' : 0 ≤ x * y := mul_nonneg hx hy
    have h2 : x * y * z ≤ 1 := by nlinarith
    have h2' : 0 ≤ x * y * z := mul_nonneg h1' hz
    nlinarith
  have hX2 : (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2) ≤ 1 := by
    have hd : 0 < a ^ 2 * b ^ 2 := by positivity
    first
    | (rw [div_le_one hd]; linarith)
    | (rw [div_le_one₀ hd]; linarith)
    | (rw [div_le_iff₀ hd]; linarith)
    | (rw [div_le_iff hd]; linarith)
  have hX2' : 0 ≤ (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2) := by positivity
  have hX3 : 1 / θ ^ 2 ≤ 1 := by
    have hd : 0 < θ ^ 2 := by positivity
    first
    | (rw [div_le_one hd]; nlinarith)
    | (rw [div_le_one₀ hd]; nlinarith)
    | (rw [div_le_iff₀ hd]; nlinarith)
    | (rw [div_le_iff hd]; nlinarith)
  have hX3' : 0 ≤ 1 / θ ^ 2 := by positivity
  have hX1' : 0 ≤ e ^ (n + 2) * B := by positivity
  have hfb := fac_bound n hn
  have hD : 0 ≤ Del ^ n * W * B ^ (n + 1) / 2 := by positivity
  have hYZ : (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))
      ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := by
    calc (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))
        = (2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1)) *
            (Del ^ n * W * B ^ (n + 1) / 2) := by simp only [mul_pow]; ring
      _ ≤ (4 ^ n * (n.factorial : ℝ)) * (Del ^ n * W * B ^ (n + 1) / 2) :=
          mul_le_mul_of_nonneg_right hfb hD
      _ = (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := by simp only [mul_pow]; ring
  have hYZ0 : 0 ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) *
      (W * B ^ (n + 1)) := by positivity
  calc (0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del))) ^ (n + 2) * Vu
      ≤ (0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del))) ^ (n + 2) *
          ((a ^ n * (a + b)) * ((Real.exp (1/4) ^ (n + 1) * W) * (b * θ) ^ n)) :=
        mul_le_mul_of_nonneg_left hVu (pow_nonneg hbase _)
    _ = (e ^ (n + 2) * B) * ((((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
          ((0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1)) * (W * B ^ (n + 1)) :=
        top_alg n 0.38 e B a b (((n:ℝ) + 2) * Del) θ (Real.exp (1/4)) W ha.ne' hb.ne' hθ0.ne'
    _ = (e ^ (n + 2) * B) * ((((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
          ((0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))) := by
        ring
    _ ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1)) :=
        key3 _ _ _ _ hX1' hs hX2' hX2 hX3' hX3 hYZ0
    _ ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := hYZ

/- English proof (translation)
Unfold `Vand`. Simplify using the standard rewrite rules.
-/
lemma vand_one (x : ℕ → ℝ) : Vand 1 x = 1 := by
  unfold Vand
  simp

/- English proof (translation)
Rewrite using `[Nat.add_comm q 1, vand_split 1 q x, vand_one]`. Simplify using `only [Finset.Icc_self, Finset.prod_singleton, one_mul]`.
-/
lemma vand_head (q : ℕ) (x : ℕ → ℝ) :
    Vand (q + 1) x = (∏ j ∈ Icc 1 q, (x 1 - x (j + 1))) * Vand q (fun j => x (j + 1)) := by
  rw [Nat.add_comm q 1, vand_split 1 q x, vand_one]
  simp only [Finset.Icc_self, Finset.prod_singleton, one_mul]

/- English proof (translation)
Rewrite using `[vand_split p 1 x, vand_one]`. Simplify using `only [Finset.Icc_self, Finset.prod_singleton, mul_one, Nat.add_comm 1 p]`.
-/
lemma vand_last (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = Vand p x * ∏ i ∈ Icc 1 p, (x i - x (p + 1)) := by
  rw [vand_split p 1 x, vand_one]
  simp only [Finset.Icc_self, Finset.prod_singleton, mul_one, Nat.add_comm 1 p]

/- English proof (translation)
Simplify using `[Cfg.u]`.
-/
lemma u_one (c : Cfg) (de : ℕ → ℝ) : c.u de 1 = c.a := by
  simp [Cfg.u]

/- English proof (translation)
Establish `h0 : j ≠ 0` using `by omega`. Establish `h1' : j + 1 ≠ 1` using `by omega`. Establish `h2' : j + 1 ≠ c.k` using `by omega`. Simplify using `[Cfg.u, h0, h1', h2']`.
-/
lemma u_mid (c : Cfg) (de : ℕ → ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 2 ≤ c.k) :
    c.u de (j + 1) = c.v j - 1 / 2 - de j * c.Del := by
  have h0 : j ≠ 0 := by omega
  have h1' : j + 1 ≠ 1 := by omega
  have h2' : j + 1 ≠ c.k := by omega
  simp [Cfg.u, h0, h1', h2']

/- English proof (translation)
Establish `h1' : c.k ≠ 1` using `by omega`. Simplify using `[Cfg.u, h1']`.
-/
lemma u_last (c : Cfg) (de : ℕ → ℝ) (hk : 4 ≤ c.k) : c.u de c.k = c.ulast := by
  have h1' : c.k ≠ 1 := by omega
  simp [Cfg.u, h1']

/- English proof (translation)
Rewrite using `[u_mid c de j h1 h2]`. Establish `hj : (j:ℝ) + 2 ≤ (c.k:ℝ)` using `by exact_mod_cast h2`. Establish `hj1 : (1:ℝ) ≤ (j:ℝ)` using `by exact_mod_cast h1`. Establish `hD` using `h.hDel`. Establish `hv0` using `h.hv0`.

Apply the tactic sequence `rcases hw.1 j with hd | hd <;> rw [hd] <;> simp only [Cfg.v, Nat.cast_one] <;>`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
lemma u_mid_bounds (c : Cfg) (h : c.Ok) (de : ℕ → ℝ) (hw : IsWord c.k de) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j + 2 ≤ c.k) : 0 ≤ c.u de (j + 1) ∧ c.u de (j + 1) ≤ c.v 1 := by
  rw [u_mid c de j h1 h2]
  have hj : (j:ℝ) + 2 ≤ (c.k:ℝ) := by exact_mod_cast h2
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast h1
  have hD := h.hDel
  have hv0 := h.hv0
  rcases hw.1 j with hd | hd <;> rw [hd] <;> simp only [Cfg.v, Nat.cast_one] <;>
    constructor <;> nlinarith

/- English proof (translation)
Establish `hk : (0:ℝ) < (c.k:ℝ)`. Use `h.hk` as an intermediate fact. Conclude with `(by omega : 0 < c.k)` after adjusting the coercions. Establish `hbb0 : 0 < bb` using `by linarith [hs.hbb]`. Establish `e1 : Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k = Real.exp (-(2 * c.m * Real.log bb))`.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Establish `hk' : (c.k:ℝ) ≠ 0` using `hk.ne'`. Use `first`. Consider the case `(field_simp; done)`.

Consider the case `(field_simp; ring)`. Establish `e2 : Real.exp (2 * c.m * Real.log bb) = bb ^ (2 * c.m)`. Rewrite using `[show (2 * (c.m:ℝ) * Real.log bb) = ((2 * c.m : ℕ) : ℝ) * Real.log bb by push_cast; ring]`. Rewrite using `[← Real.log_pow, Real.exp_log (by positivity)]`. Establish `hp : c.prodb ≤ bb ^ (2 * c.m)`.

Unfold `Cfg.prodb`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`.

Combine the linear relations using `[b_ge_one c h j hj.1 hj.2]`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Icc]`. Conclude with `hs.hbj j hj.1 hj.2`. Use `_ = bb ^ (2 * c.m) := by first`.

Consider the case `(rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, pow_mul])`. Consider the case `(rw [Finset.prod_const, Nat.card_Icc, pow_mul])`. Consider the case `(rw [Finset.prod_const, Nat.card_Icc, pow_mul]; congr 1; omega)`. Consider the case `(simp [Finset.prod_const, pow_mul])`. Establish `hpos : 0 < bb ^ (2 * c.m)` using `by positivity`.

Rewrite using `[e1, Real.exp_neg, e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma mu_bound (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) :
    Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k * c.prodb ≤ 1 := by
  have hk : (0:ℝ) < (c.k:ℝ) := by
    have := h.hk
    exact_mod_cast (by omega : 0 < c.k)
  have hbb0 : 0 < bb := by linarith [hs.hbb]
  have e1 : Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k = Real.exp (-(2 * c.m * Real.log bb)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hk' : (c.k:ℝ) ≠ 0 := hk.ne'
    first
    | (field_simp; done)
    | (field_simp; ring)
  have e2 : Real.exp (2 * c.m * Real.log bb) = bb ^ (2 * c.m) := by
    rw [show (2 * (c.m:ℝ) * Real.log bb) = ((2 * c.m : ℕ) : ℝ) * Real.log bb by push_cast; ring]
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hp : c.prodb ≤ bb ^ (2 * c.m) := by
    unfold Cfg.prodb
    calc ∏ j ∈ Icc 1 c.m, c.b j ≤ ∏ j ∈ Icc 1 c.m, bb ^ 2 := by
          apply Finset.prod_le_prod
          · intro j hj
            rw [Finset.mem_Icc] at hj
            linarith [b_ge_one c h j hj.1 hj.2]
          · intro j hj
            rw [Finset.mem_Icc] at hj
            exact hs.hbj j hj.1 hj.2
      _ = bb ^ (2 * c.m) := by
          first
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, pow_mul])
          | (rw [Finset.prod_const, Nat.card_Icc, pow_mul])
          | (rw [Finset.prod_const, Nat.card_Icc, pow_mul]; congr 1; omega)
          | (simp [Finset.prod_const, pow_mul])
  have hpos : 0 < bb ^ (2 * c.m) := by positivity
  rw [e1, Real.exp_neg, e2]
  calc (bb ^ (2 * c.m))⁻¹ * c.prodb ≤ (bb ^ (2 * c.m))⁻¹ * bb ^ (2 * c.m) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/- English proof (translation)
Establish `hk4` using `h.hk`. Establish `hvthp : c.vthp = 0` using `by simp [Cfg.vthp, htop]`. Establish `haeff : c.aeff = c.a - c.v 1` using `by simp [Cfg.aeff, htop]`. Establish `hkR : (4:ℝ) ≤ (c.k:ℝ)` using `by exact_mod_cast hk4`. Establish `hα : 1 ≤ c.a - c.v 1`.

Establish `h1` using `h.ha`. Establish `h2` using `h.hDel`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcOne : cOne c bb * c.prodb / c.aeff = 0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 0) * c.prodb / (c.a - c.v 1)`. Rewrite using `[haeff]`.

Unfold `cOne`. Rewrite using `[hvthp]`. Rewrite using `[hcOne]`. Establish `hB` using `prodb_ge_one c h`. Take `⟨hVpos, hRde, hRlo, hRhi⟩` from `hNT c de h hw htop`.

Take `⟨_, hEF2⟩` from `hEF c de h hw`. Take `⟨hPlo, hPhi⟩` from `hEF2 htop`. Establish `hsplit : Vand c.k (c.u de) = (∏ i ∈ Icc 2 c.k, (c.a - c.u de i)) * Vand (c.k - 1) (fun i => c.u de (i + 1))`. Establish `hk1 : c.k = (c.k - 1) + 1` using `by omega`. Use `conv_lhs => rw [hk1]`.

Rewrite using `[vand_head, u_one]`. Use `congr 1`. Establish `hI : Icc 2 c.k = Ioc 1 c.k`. Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`.

Apply the tactic sequence `constructor <;> intro hh <;> exact ⟨by omega, by omega⟩`. Establish `hs2` using `prod_Ioc_shift (fun i => c.a - c.u de i) 1 0 (c.k - 1)`. Rewrite `hs2` using `[zero_add, show c.k - 1 + 1 = c.k by omega]`. Rewrite using `[Icc_one_eq, hI]`. Conclude with `hs2.symm`.

Establish `hexp : Real.exp ((c.k:ℝ) / 4) = Real.exp (1/4) ^ c.k`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hP2 : Vand (c.k - 1) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v`.

Rewrite using `[hRde, ← hexp]`. Conclude with `mul_le_mul_of_nonneg_right hRhi hVpos.le`. Establish `hP20 : 0 ≤ Vand (c.k - 1) (fun i => c.u de (i + 1))`. Rewrite using `[hRde]`. Conclude with `mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hVpos.le`.

Establish `hVu : Vand c.k (c.u de) ≤ (2 * (c.a - c.v 1)) ^ (c.k - 1) * (Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v)`. Rewrite using `[hsplit]`. Conclude with `mul_le_mul hPhi hP2 hP20 (pow_nonneg (by linarith) _)`. Prove the components needed by the constructor for the conclusion. Conclude with `div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)`.

Conclude with `non_top_final_inequality c.k (by omega) _ c.prodb (c.a - c.v 1) (Vand (c.k - 1) c.v) (Vand c.k (c.u de)) hα (Real.exp_pos _).le hB hVpos (mu_bound c h bb hs) hVu`.
-/
lemma key_nontop (hNT : VandNonTop) (hEF : EdgeFactors) (c : Cfg) (bb : ℝ) (de : ℕ → ℝ) (h : c.Ok)
    (hs : c.Small bb) (hw : IsWord c.k de) (htop : c.top = false) :
    0 ≤ cOne c bb * c.prodb / c.aeff ∧
    (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
  have hk4 := h.hk
  have hvthp : c.vthp = 0 := by simp [Cfg.vthp, htop]
  have haeff : c.aeff = c.a - c.v 1 := by simp [Cfg.aeff, htop]
  have hkR : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast hk4
  have hα : 1 ≤ c.a - c.v 1 := by
    have h1 := h.ha
    have h2 := h.hDel
    nlinarith
  have hcOne : cOne c bb * c.prodb / c.aeff =
      0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 0) * c.prodb / (c.a - c.v 1) := by
    rw [haeff]
    unfold cOne
    rw [hvthp]
  rw [hcOne]
  have hB := prodb_ge_one c h
  obtain ⟨hVpos, hRde, hRlo, hRhi⟩ := hNT c de h hw htop
  obtain ⟨_, hEF2⟩ := hEF c de h hw
  obtain ⟨hPlo, hPhi⟩ := hEF2 htop
  have hsplit : Vand c.k (c.u de) =
      (∏ i ∈ Icc 2 c.k, (c.a - c.u de i)) * Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    have hk1 : c.k = (c.k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [vand_head, u_one]
    congr 1
    have hI : Icc 2 c.k = Ioc 1 c.k := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor <;> intro hh <;> exact ⟨by omega, by omega⟩
    have hs2 := prod_Ioc_shift (fun i => c.a - c.u de i) 1 0 (c.k - 1)
    rw [zero_add, show c.k - 1 + 1 = c.k by omega] at hs2
    rw [Icc_one_eq, hI]
    exact hs2.symm
  have hexp : Real.exp ((c.k:ℝ) / 4) = Real.exp (1/4) ^ c.k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hP2 : Vand (c.k - 1) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v := by
    rw [hRde, ← hexp]
    exact mul_le_mul_of_nonneg_right hRhi hVpos.le
  have hP20 : 0 ≤ Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    rw [hRde]
    exact mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hVpos.le
  have hVu : Vand c.k (c.u de) ≤ (2 * (c.a - c.v 1)) ^ (c.k - 1) *
      (Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v) := by
    rw [hsplit]
    exact mul_le_mul hPhi hP2 hP20 (pow_nonneg (by linarith) _)
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  · exact non_top_final_inequality c.k (by omega) _ c.prodb (c.a - c.v 1) (Vand (c.k - 1) c.v)
      (Vand c.k (c.u de)) hα (Real.exp_pos _).le hB hVpos (mu_bound c h bb hs) hVu

/- English proof (translation)
Establish `hk4` using `h.hk`. Establish `hkR : (4:ℝ) ≤ (c.k:ℝ)` using `by exact_mod_cast hk4`. Establish `hD` using `h.hDel`. Establish `hD0 : 0 < c.Del` using `by linarith`. Take `⟨hbp1, hbp2⟩` from `h.htop htop`.

Establish `hb1` using `h.hb1`. Establish `hbp0 : 3 ≤ c.bp` using `by linarith`. Establish `hbpne : c.bp ≠ 0` using `(by linarith : (0:ℝ) < c.bp).ne'`. Establish `hvthp : c.vthp = 4 * c.k * c.Del / c.bp` using `by simp [Cfg.vthp, htop]`. Establish `haeff : c.aeff = c.a * c.bp / (c.k * c.Del)` using `by simp [Cfg.aeff, htop]`.

Establish `hv1` using `h.hv1`. Establish `hv1n : 0 ≤ c.v 1` using `v_nonneg c h 1 (by omega)`. Establish `ha` using `h.ha`. Establish `hK0 : 0 < (c.k:ℝ) * c.Del` using `by positivity`. Establish `ha0 : 0 < c.a` using `by linarith`.

Establish `hθ : 1 ≤ 1 + 4 * (c.k:ℝ) * c.Del / c.bp`. Establish `h4 : 0 ≤ 4 * (c.k:ℝ) * c.Del / c.bp` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcOne : cOne c bb * c.prodb / c.aeff = 0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp) * c.prodb / (c.a * c.bp / (c.k * c.Del))`. Rewrite using `[haeff]`.

Unfold `cOne`. Rewrite using `[hvthp]`. Rewrite using `[hcOne]`. Establish `hB` using `prodb_ge_one c h`. Take `⟨hW, hRde, hRlo, hRhi, hV1⟩` from `hTp c de h hw`.

Establish `hvth` using `hs.hvth`. Unfold `Cfg.vth at hvth`. Establish `hb1pos : 0 < c.b 1` using `by linarith`. Establish `hvth' : 4 * (c.m:ℝ) * c.k * c.Del ≤ c.b 1 / 10` using `by first`. Consider the case `(rw [div_le_iff₀ hb1pos] at hvth; linarith)`.

Consider the case `(rw [div_le_iff hb1pos] at hvth; linarith)`. Establish `hm2 : (2:ℝ) ≤ (c.m:ℝ)` using `by exact_mod_cast h.hm`. Establish `hK1 : (c.k:ℝ) * c.Del ≤ c.bp / 40`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hm2) hK0.le]`. Establish `hK2 : (c.k:ℝ) * c.Del ≤ c.a / 4` using `by linarith`.

Establish `hK4 : (4:ℝ) ≤ (c.k:ℝ) * c.Del`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hD)]`. Establish `hq : ((c.k:ℝ) * c.Del) ^ 2 * (c.a + c.bp) ≤ c.a ^ 2 * c.bp ^ 2`. Establish `s1` using `mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK1) ha0.le`. Establish `s3` using `mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK2) (by linarith : (0:ℝ) ≤ c.bp)`.

Establish `s2 : 0 ≤ c.bp ^ 2 * c.a * (c.a / 2 - 1 / 1600)`. Apply `mul_nonneg (mul_nonneg (sq_nonneg _) ha0.le)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s4 : 0 ≤ c.a ^ 2 * c.bp * (c.bp / 2 - 1 / 16)`. Apply `mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith))` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `hsplit : Vand c.k (c.u de) = (∏ i ∈ Icc 2 c.k, (c.a - c.u de i)) * Vand (c.k - 1) (fun i => c.u de (i + 1))`. Establish `hk1 : c.k = (c.k - 1) + 1` using `by omega`. Use `conv_lhs => rw [hk1]`.

Rewrite using `[vand_head, u_one]`. Use `congr 1`. Establish `hI : Icc 2 c.k = Ioc 1 c.k`. Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`.

Apply the tactic sequence `constructor <;> intro hh <;> exact ⟨by omega, by omega⟩`. Establish `hs2` using `prod_Ioc_shift (fun i => c.a - c.u de i) 1 0 (c.k - 1)`. Rewrite `hs2` using `[zero_add, show c.k - 1 + 1 = c.k by omega]`. Rewrite using `[Icc_one_eq, hI]`. Conclude with `hs2.symm`.

Establish `hulast : c.u de c.k = -c.bp`. Rewrite using `[u_last c de hk4]`. Simplify using `[Cfg.ulast, htop]`. Establish `hP1 : ∏ i ∈ Icc 2 c.k, (c.a - c.u de i) = (∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i)) * (c.a + c.bp)`. Establish `hI : Icc 2 c.k = Ioc 1 c.k`.

Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`. Apply the tactic sequence `constructor <;> intro hh <;> exact ⟨by omega, by omega⟩`. Rewrite using `[hI]`. Establish `hk1 : c.k = (c.k - 1) + 1` using `by omega`.

Use `conv_lhs => rw [hk1]`. Rewrite using `[Finset.prod_Ioc_succ_top (by omega : 1 ≤ c.k - 1), ← hk1, hulast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA1 : ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) ≤ c.a ^ (c.k - 2)`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ioc]`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Establish `hb` using `u_mid_bounds c h de hw j (by omega) (by omega)`.

Combine the linear relations using `[hb.2]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ioc]`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Establish `hb` using `u_mid_bounds c h de hw j (by omega) (by omega)`.

Combine the linear relations using `[hb.1]`. Use `_ = c.a ^ (c.k - 2) := by first`. Consider the case `(rw [Finset.prod_const, Nat.card_Ioc]; done)`. Consider the case `(rw [Finset.prod_const, Nat.card_Ioc, Nat.sub_sub])`. Consider the case `(rw [Finset.prod_const, Nat.card_Ioc]; congr 1; omega)`.

Establish `hA10 : 0 ≤ ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i)`. Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ioc]`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`.

Establish `hb` using `u_mid_bounds c h de hw j (by omega) (by omega)`. Combine the linear relations using `[hb.2]`. Establish `hP2split : Vand (c.k - 1) (fun i => c.u de (i + 1)) = Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp)`. Establish `hk2 : c.k - 1 = (c.k - 2) + 1` using `by omega`. Rewrite using `[hk2, vand_last]`.

Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `try beta_reduce`. Rewrite using `[show c.k - 2 + 1 + 1 = c.k by omega, hulast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hF : ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) ≤ (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2)`. Establish `hbt : c.bp * (1 + 4 * c.k * c.Del / c.bp) = c.bp + 4 * c.k * c.Del`. Establish `e : c.bp * c.bp⁻¹ = 1` using `mul_inv_cancel₀ hbpne`. Take the linear combination `(4 * (c.k:ℝ) * c.Del) * e`.

Rewrite using `[hbt]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`.

Establish `hb` using `u_mid_bounds c h de hw i hi.1 (by omega)`. Combine the linear relations using `[hb.1]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Establish `hb` using `u_mid_bounds c h de hw i hi.1 (by omega)`.

Combine the linear relations using `[hb.2]`. Use `_ = (c.bp + 4 * (c.k:ℝ) * c.Del) ^ (c.k - 2) := by`. Rewrite using `[Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]`. Establish `hF0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp)`. Apply `Finset.prod_nonneg` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Establish `hb` using `u_mid_bounds c h de hw i hi.1 (by omega)`. Combine the linear relations using `[hb.1]`. Establish `hexp : Real.exp (((c.k:ℝ) - 1) / 4) = Real.exp (1/4) ^ (c.k - 1)`.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Rewrite using `[Nat.cast_sub (show 1 ≤ c.k by omega), Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hV2 : Vand (c.k - 2) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v`.

Rewrite using `[hRde, ← hexp]`. Conclude with `mul_le_mul_of_nonneg_right hRhi hW.le`. Establish `hV20 : 0 ≤ Vand (c.k - 2) (fun i => c.u de (i + 1))`. Rewrite using `[hRde]`. Conclude with `mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hW.le`.

Establish `hab : 0 ≤ c.a + c.bp` using `by linarith`. Establish `hVu : Vand c.k (c.u de) ≤ (c.a ^ (c.k - 2) * (c.a + c.bp)) * ((Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v) * (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2))`. Rewrite using `[hsplit, hP1, hP2split]`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_right hA1 hab) (mul_le_mul hV2 hF hF0 (mul_nonneg (by positivity) hW.le)) (mul_nonneg hV20 hF0) (mul_nonneg (pow_nonneg ha0.le _) hab)`. Rewrite using `[hV1]`.

Prove the components needed by the constructor for the conclusion. Establish `hX : 0 ≤ 0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp)`. Check the signs of the components of the expression. Conclude with `div_nonneg (mul_nonneg hX (by linarith)) (by positivity)`. Conclude with `top_final_inequality c.k hk4 _ c.prodb c.a c.bp c.Del _ (Vand (c.k - 2) c.v) (Vand c.k (c.u de)) (Real.exp_pos _).le hB hW (mu_bound c h bb hs) hθ ha0 (by linarith) hD0 hq hVu`.
-/
lemma key_top (hTp : VandTop) (c : Cfg) (bb : ℝ) (de : ℕ → ℝ) (h : c.Ok)
    (hs : c.Small bb) (hw : IsWord c.k de) (htop : c.top = true) :
    0 ≤ cOne c bb * c.prodb / c.aeff ∧
    (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
  have hk4 := h.hk
  have hkR : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast hk4
  have hD := h.hDel
  have hD0 : 0 < c.Del := by linarith
  obtain ⟨hbp1, hbp2⟩ := h.htop htop
  have hb1 := h.hb1
  have hbp0 : 3 ≤ c.bp := by linarith
  have hbpne : c.bp ≠ 0 := (by linarith : (0:ℝ) < c.bp).ne'
  have hvthp : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, htop]
  have haeff : c.aeff = c.a * c.bp / (c.k * c.Del) := by simp [Cfg.aeff, htop]
  have hv1 := h.hv1
  have hv1n : 0 ≤ c.v 1 := v_nonneg c h 1 (by omega)
  have ha := h.ha
  have hK0 : 0 < (c.k:ℝ) * c.Del := by positivity
  have ha0 : 0 < c.a := by linarith
  have hθ : 1 ≤ 1 + 4 * (c.k:ℝ) * c.Del / c.bp := by
    have h4 : 0 ≤ 4 * (c.k:ℝ) * c.Del / c.bp := by positivity
    linarith
  have hcOne : cOne c bb * c.prodb / c.aeff =
      0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp) * c.prodb /
        (c.a * c.bp / (c.k * c.Del)) := by
    rw [haeff]
    unfold cOne
    rw [hvthp]
  rw [hcOne]
  have hB := prodb_ge_one c h
  obtain ⟨hW, hRde, hRlo, hRhi, hV1⟩ := hTp c de h hw
  have hvth := hs.hvth
  unfold Cfg.vth at hvth
  have hb1pos : 0 < c.b 1 := by linarith
  have hvth' : 4 * (c.m:ℝ) * c.k * c.Del ≤ c.b 1 / 10 := by
    first
    | (rw [div_le_iff₀ hb1pos] at hvth; linarith)
    | (rw [div_le_iff hb1pos] at hvth; linarith)
  have hm2 : (2:ℝ) ≤ (c.m:ℝ) := by exact_mod_cast h.hm
  have hK1 : (c.k:ℝ) * c.Del ≤ c.bp / 40 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hK0.le]
  have hK2 : (c.k:ℝ) * c.Del ≤ c.a / 4 := by linarith
  have hK4 : (4:ℝ) ≤ (c.k:ℝ) * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hD)]
  have hq : ((c.k:ℝ) * c.Del) ^ 2 * (c.a + c.bp) ≤ c.a ^ 2 * c.bp ^ 2 := by
    have s1 := mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK1) ha0.le
    have s3 := mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK2)
      (by linarith : (0:ℝ) ≤ c.bp)
    have s2 : 0 ≤ c.bp ^ 2 * c.a * (c.a / 2 - 1 / 1600) := by
      apply mul_nonneg (mul_nonneg (sq_nonneg _) ha0.le)
      linarith
    have s4 : 0 ≤ c.a ^ 2 * c.bp * (c.bp / 2 - 1 / 16) := by
      apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
      linarith
    nlinarith
  have hsplit : Vand c.k (c.u de) =
      (∏ i ∈ Icc 2 c.k, (c.a - c.u de i)) * Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    have hk1 : c.k = (c.k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [vand_head, u_one]
    congr 1
    have hI : Icc 2 c.k = Ioc 1 c.k := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor <;> intro hh <;> exact ⟨by omega, by omega⟩
    have hs2 := prod_Ioc_shift (fun i => c.a - c.u de i) 1 0 (c.k - 1)
    rw [zero_add, show c.k - 1 + 1 = c.k by omega] at hs2
    rw [Icc_one_eq, hI]
    exact hs2.symm
  have hulast : c.u de c.k = -c.bp := by
    rw [u_last c de hk4]
    simp [Cfg.ulast, htop]
  have hP1 : ∏ i ∈ Icc 2 c.k, (c.a - c.u de i) =
      (∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i)) * (c.a + c.bp) := by
    have hI : Icc 2 c.k = Ioc 1 c.k := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor <;> intro hh <;> exact ⟨by omega, by omega⟩
    rw [hI]
    have hk1 : c.k = (c.k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [Finset.prod_Ioc_succ_top (by omega : 1 ≤ c.k - 1), ← hk1, hulast]
    ring
  have hA1 : ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) ≤ c.a ^ (c.k - 2) := by
    calc ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) ≤ ∏ i ∈ Ioc 1 (c.k - 1), c.a := by
          apply Finset.prod_le_prod
          · intro i hi
            rw [Finset.mem_Ioc] at hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have hb := u_mid_bounds c h de hw j (by omega) (by omega)
            linarith [hb.2]
          · intro i hi
            rw [Finset.mem_Ioc] at hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have hb := u_mid_bounds c h de hw j (by omega) (by omega)
            linarith [hb.1]
      _ = c.a ^ (c.k - 2) := by
          first
          | (rw [Finset.prod_const, Nat.card_Ioc]; done)
          | (rw [Finset.prod_const, Nat.card_Ioc, Nat.sub_sub])
          | (rw [Finset.prod_const, Nat.card_Ioc]; congr 1; omega)
  have hA10 : 0 ≤ ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) := by
    apply Finset.prod_nonneg
    intro i hi
    rw [Finset.mem_Ioc] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hb := u_mid_bounds c h de hw j (by omega) (by omega)
    linarith [hb.2]
  have hP2split : Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) := by
    have hk2 : c.k - 1 = (c.k - 2) + 1 := by omega
    rw [hk2, vand_last]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    try beta_reduce
    rw [show c.k - 2 + 1 + 1 = c.k by omega, hulast]
    ring
  have hF : ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) ≤
      (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2) := by
    have hbt : c.bp * (1 + 4 * c.k * c.Del / c.bp) = c.bp + 4 * c.k * c.Del := by
      have e : c.bp * c.bp⁻¹ = 1 := mul_inv_cancel₀ hbpne
      linear_combination (4 * (c.k:ℝ) * c.Del) * e
    rw [hbt]
    calc ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp)
        ≤ ∏ i ∈ Icc 1 (c.k - 2), (c.bp + 4 * (c.k:ℝ) * c.Del) := by
          apply Finset.prod_le_prod
          · intro i hi
            rw [Finset.mem_Icc] at hi
            have hb := u_mid_bounds c h de hw i hi.1 (by omega)
            linarith [hb.1]
          · intro i hi
            rw [Finset.mem_Icc] at hi
            have hb := u_mid_bounds c h de hw i hi.1 (by omega)
            linarith [hb.2]
      _ = (c.bp + 4 * (c.k:ℝ) * c.Del) ^ (c.k - 2) := by
          rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hF0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) := by
    apply Finset.prod_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hb := u_mid_bounds c h de hw i hi.1 (by omega)
    linarith [hb.1]
  have hexp : Real.exp (((c.k:ℝ) - 1) / 4) = Real.exp (1/4) ^ (c.k - 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ c.k by omega), Nat.cast_one]
    ring
  have hV2 : Vand (c.k - 2) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v := by
    rw [hRde, ← hexp]
    exact mul_le_mul_of_nonneg_right hRhi hW.le
  have hV20 : 0 ≤ Vand (c.k - 2) (fun i => c.u de (i + 1)) := by
    rw [hRde]
    exact mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hW.le
  have hab : 0 ≤ c.a + c.bp := by linarith
  have hVu : Vand c.k (c.u de) ≤ (c.a ^ (c.k - 2) * (c.a + c.bp)) *
      ((Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v) *
        (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2)) := by
    rw [hsplit, hP1, hP2split]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hA1 hab)
      (mul_le_mul hV2 hF hF0 (mul_nonneg (by positivity) hW.le))
      (mul_nonneg hV20 hF0) (mul_nonneg (pow_nonneg ha0.le _) hab)
  rw [hV1]
  constructor
  · have hX : 0 ≤ 0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp) := by
      positivity
    exact div_nonneg (mul_nonneg hX (by linarith)) (by positivity)
  · exact top_final_inequality c.k hk4 _ c.prodb c.a c.bp c.Del _ (Vand (c.k - 2) c.v) (Vand c.k (c.u de))
      (Real.exp_pos _).le hB hW (mu_bound c h bb hs) hθ ha0 (by linarith) hD0 hq hVu

/- English proof (translation)
Introduce `c r bb de ka rd g VV h hm hs hw hrd hka hg hFD`. Establish `hk1 : 1 ≤ c.k` using `by have := h.hk; omega`. Take `⟨hVu0, -, -⟩` from `hVW c de de h hs.hvth hw hw`. Establish `hkey : 0 ≤ cOne c bb * c.prodb / c.aeff ∧ (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤ Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2`. Consider the cases of `htop : c.top`.

Conclude with `key_nontop hNT hEF c bb de h hs hw htop`. Conclude with `key_top hTp c bb de h hs hw htop`. Take `⟨hcP0, hcPk⟩` from `hkey`. Establish `hLam` using `(vandLamLower c h).2`. Unfold `FormalDegreeLower at hFD`.

Establish `hvp` using `vand_v_pos c h (c.k - 1)`. Establish `hpb` using `prodb_ge_one c h`. Establish `hpos : 0 < Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1)` using `mul_pos hvp (pow_pos (by linarith) _)`. Establish `hVV0 : 0 < VV` using `by linarith`. Establish `hkV : (cOne c bb * c.prodb / c.aeff) ^ c.k ≤ VV / Vand c.k (c.u de)` using `by first`.

Consider the case `(rw [le_div_iff₀ hVu0]; linarith)`. Consider the case `(rw [le_div_iff hVu0]; linarith)`. Establish `hcPY : cOne c bb * c.prodb / c.aeff ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ))`. Establish `hk0 : c.k ≠ 0` using `by omega`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[one_div]`. Use `first`. Consider the case `exact (Real.pow_rpow_inv_natCast hcP0 hk0).symm`. Consider the case `exact (Real.pow_nat_rpow_nat_inv hcP0 hk0).symm`. Use `_ ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) := Real.rpow_le_rpow (pow_nonneg hcP0 _) hkV (by positivity)`.

Establish `hrd0 : 0 < rd` using `by linarith`. Establish `hka0 : 0 < ka` using `by rw [hka]; positivity`. Establish `hg0 : 0 < g` using `by linarith [Real.pi_pos]`. Establish `hA : 0 < (ka ^ (c.m - 1))⁻¹ * g ^ c.m` using `by positivity`. Establish `hb` using `hBr c.k r c.m ka rd g VV (Vand c.k (c.u de)) hm hk1 hrd hka hg hVV0 hVu0`.

Take `⟨hom1, -, hT⟩` from `hb`. Rewrite using `[hT]`. Establish `fin : ∀ A om Y cP : ℝ, 0 < A → 1 ≤ om → 0 ≤ cP → cP ≤ Y → A * cP ≤ A * om * Y`. Introduce `A om Y cP hA' hom hc hY`. Establish `hY0 : 0 ≤ Y` using `le_trans hc hY`.

Establish `h1 : cP ≤ om * Y` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff = ((ka ^ (c.m - 1))⁻¹ * g ^ c.m) * (cOne c bb * c.prodb / c.aeff) by ring]`. Conclude with `fin _ _ _ _ hA hom1 hcP0 hcPY`.
-/
theorem tcritLower_of (hBr : BracketBound) (hNT : VandNonTop) (hTp : VandTop) (hEF : EdgeFactors)
    (hVW : VandWords) : TcritLower := by
  intro c r bb de ka rd g VV h hm hs hw hrd hka hg hFD
  have hk1 : 1 ≤ c.k := by have := h.hk; omega
  obtain ⟨hVu0, -, -⟩ := hVW c de de h hs.hvth hw hw
  have hkey : 0 ≤ cOne c bb * c.prodb / c.aeff ∧
      (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
        Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
    cases htop : c.top
    · exact key_nontop hNT hEF c bb de h hs hw htop
    · exact key_top hTp c bb de h hs hw htop
  obtain ⟨hcP0, hcPk⟩ := hkey
  have hLam := (vandLamLower c h).2
  unfold FormalDegreeLower at hFD
  have hvp := vand_v_pos c h (c.k - 1)
  have hpb := prodb_ge_one c h
  have hpos : 0 < Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) := mul_pos hvp (pow_pos (by linarith) _)
  have hVV0 : 0 < VV := by linarith
  have hkV : (cOne c bb * c.prodb / c.aeff) ^ c.k ≤ VV / Vand c.k (c.u de) := by
    first
    | (rw [le_div_iff₀ hVu0]; linarith)
    | (rw [le_div_iff hVu0]; linarith)
  have hcPY : cOne c bb * c.prodb / c.aeff ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) := by
    have hk0 : c.k ≠ 0 := by omega
    calc cOne c bb * c.prodb / c.aeff
        = ((cOne c bb * c.prodb / c.aeff) ^ c.k) ^ ((1:ℝ) / (c.k:ℝ)) := by
          rw [one_div]
          first
          | exact (Real.pow_rpow_inv_natCast hcP0 hk0).symm
          | exact (Real.pow_nat_rpow_nat_inv hcP0 hk0).symm
      _ ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg hcP0 _) hkV (by positivity)
  have hrd0 : 0 < rd := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hg0 : 0 < g := by linarith [Real.pi_pos]
  have hA : 0 < (ka ^ (c.m - 1))⁻¹ * g ^ c.m := by positivity
  have hb := hBr c.k r c.m ka rd g VV (Vand c.k (c.u de)) hm hk1 hrd hka hg hVV0 hVu0
  obtain ⟨hom1, -, hT⟩ := hb
  rw [hT]
  have fin : ∀ A om Y cP : ℝ, 0 < A → 1 ≤ om → 0 ≤ cP → cP ≤ Y → A * cP ≤ A * om * Y := by
    intro A om Y cP hA' hom hc hY
    have hY0 : 0 ≤ Y := le_trans hc hY
    have h1 : cP ≤ om * Y := by nlinarith
    calc A * cP ≤ A * (om * Y) := mul_le_mul_of_nonneg_left h1 hA'.le
      _ = A * om * Y := by ring
  rw [show cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff =
      ((ka ^ (c.m - 1))⁻¹ * g ^ c.m) * (cOne c bb * c.prodb / c.aeff) by ring]
  exact fin _ _ _ _ hA hom1 hcP0 hcPY

/- English proof (translation)
Unfold `TcritPow`. Use `first`. Consider the case `positivity`. Consider the case `(apply div_pos _ hVu`. Apply `mul_pos _ hVV` to reduce the goal to its premises.

Apply `mul_pos _ (pow_pos hg _)` to reduce the goal to its premises. Conclude with `mul_pos (inv_pos.mpr (pow_pos hka _)) (Real.rpow_pos_of_pos hrd _))`.
-/
lemma tcritPow_pos (k m : ℕ) (ka rd g VV Vu : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hVu : 0 < Vu) : 0 < TcritPow k m ka rd g VV Vu := by
  unfold TcritPow
  first
  | positivity
  | (apply div_pos _ hVu
     apply mul_pos _ hVV
     apply mul_pos _ (pow_pos hg _)
     exact mul_pos (inv_pos.mpr (pow_pos hka _)) (Real.rpow_pos_of_pos hrd _))

/- English proof (translation)
Establish `key : ∀ P : ℝ, 0 < P → Real.log (P / V) - Real.log (P / V') = Real.log (V' / V)`. Introduce `P hP`. Rewrite using `[Real.log_div hP.ne' hV.ne', Real.log_div hP.ne' hV'.ne', Real.log_div hV'.ne' hV.ne']`. Expand and normalize the polynomial expressions, which then agree. Unfold `TcritPow`.

Conclude with `key _ (by positivity)`.
-/
lemma log_tp_diff (k m : ℕ) (ka rd g VV V V' : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hV : 0 < V) (hV' : 0 < V') :
    Real.log (TcritPow k m ka rd g VV V) - Real.log (TcritPow k m ka rd g VV V') =
      Real.log (V' / V) := by
  have key : ∀ P : ℝ, 0 < P → Real.log (P / V) - Real.log (P / V') = Real.log (V' / V) := by
    intro P hP
    rw [Real.log_div hP.ne' hV.ne', Real.log_div hP.ne' hV'.ne', Real.log_div hV'.ne' hV.ne']
    ring
  unfold TcritPow
  exact key _ (by positivity)

/- English proof (translation)
Establish `h1 : 0 < sfac p`. Unfold `sfac`. Conclude with `Finset.prod_pos (fun i _ => Nat.factorial_pos i)`. Conclude with `h1` after adjusting the coercions.
-/
lemma sfac_pos (p : ℕ) : 0 < (sfac p : ℝ) := by
  have h1 : 0 < sfac p := by
    unfold sfac
    exact Finset.prod_pos (fun i _ => Nat.factorial_pos i)
  exact_mod_cast h1

/- English proof (translation)
Unfold `glCard`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_range]`. Establish `h1 : q ^ j < q ^ p` using `by first`.

Consider the case `exact pow_lt_pow_right₀ hq hj`. Consider the case `exact pow_lt_pow_right hq hj`. Consider the case `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma glCard_pos (p : ℕ) (q : ℝ) (hq : 1 < q) : 0 < glCard p q := by
  unfold glCard
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : q ^ j < q ^ p := by
    first
    | exact pow_lt_pow_right₀ hq hj
    | exact pow_lt_pow_right hq hj
    | gcongr
  linarith

/- English proof (translation)
Establish `hq0 : 0 < q` using `by linarith`. Unfold `colIdx`. Conclude with `div_pos (glCard_pos k q hq) (pow_pos hq0 _)`.
-/
lemma colIdx_pos (k : ℕ) (q : ℝ) (hq : 1 < q) : 0 < colIdx k q := by
  have hq0 : 0 < q := by linarith
  unfold colIdx
  exact div_pos (glCard_pos k q hq) (pow_pos hq0 _)

/- English proof (translation)
The claim follows from `|(S.f : ℝ) * ((S.k : ℝ) * Real.log S.T) - ∑ w, Real.log (S.TcritPow w) + 2 * Real.log Gam| ≤ Real.log 2 + Real.log C0 := by have hk1 := hOk.hk have hv0 := hOk.hv have hT2 := hOk.hT have hg1' : (1:ℝ) < (S.g1:ℝ) := by exact_mod_cast (by omega : 1 < S.g1) have hg2' : (1:ℝ) < (S.g2:ℝ …`.
-/
lemma one_word (hPA : PropA) (hEa : EaSize) {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hMR : S.MassRatios) (hLB : S.LBound) (hCC : S.ColumnCount) (hk : 2 ≤ S.k) (hg1 : 4 ≤ S.g1)
    (hg2 : 4 ≤ S.g2) (hds : ∀ w, 0 < S.dsig w) (C0 Gam : ℝ) (hC0 : 1 ≤ C0) (hGam : 0 < Gam)
    (hCh : S.ChoiceOfT C0 Gam) (hf2 : (S.f : ℝ) * (8 / 2 ^ S.k) ≤ Real.log 2) :
    |(S.f : ℝ) * ((S.k : ℝ) * Real.log S.T) - ∑ w, Real.log (S.TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := by
  have hk1 := hOk.hk
  have hv0 := hOk.hv
  have hT2 := hOk.hT
  have hg1' : (1:ℝ) < (S.g1:ℝ) := by exact_mod_cast (by omega : 1 < S.g1)
  have hg2' : (1:ℝ) < (S.g2:ℝ) := by exact_mod_cast (by omega : 1 < S.g2)
  have hTk2 : 2 ≤ S.T ^ S.k := le_trans hT2 (Nat.le_self_pow (by omega) _)
  have hTkR : (2:ℝ) ≤ (S.T:ℝ) ^ S.k := by exact_mod_cast hTk2
  have hTk : (0:ℝ) < (S.T:ℝ) ^ S.k := by linarith
  have hdu : 0 < S.du := by
    have hCC' := hCC
    unfold SizeData.ColumnCount at hCC'
    rw [hCC']
    have h1 : 0 < S.idxCol := by
      unfold SizeData.idxCol
      exact mul_pos (pow_pos (colIdx_pos S.k _ hg1') _) (pow_pos (colIdx_pos S.k _ hg2') _)
    have h2 : 0 < ∏ w, S.dimPi w := by
      apply Finset.prod_pos
      intro w _
      unfold SizeData.dimPi
      exact div_pos (hOk.hVu w) (sfac_pos _)
    have h4 : 0 < ((S.T:ℝ) ^ S.k - 1) ^ S.f := pow_pos (by linarith) _
    exact mul_pos (mul_pos (mul_pos hOk.hvol h1) h2) h4
  obtain ⟨hEa0, hEa2⟩ := hEa ι S hOk hLB hk hg1 hg2
  have hka : 0 < S.ka := by
    unfold SizeData.ka
    positivity
  have hrd : 0 < S.rd := by
    unfold SizeData.rd
    positivity
  have hg : 0 < S.g := by
    unfold SizeData.g
    exact mul_pos (by linarith) (by linarith)
  have hTc : ∀ w, 0 < S.TcritPow w := by
    intro w
    unfold SizeData.TcritPow
    have hVV : 0 < S.VV w := by
      unfold SizeData.VV
      exact mul_pos (hds w) (sfac_pos _)
    exact tcritPow_pos _ _ _ _ _ _ _ hka hrd hg hVV (hOk.hVu w)
  have hPA' := hPA ι S hOk hMR hCC
  have hprod : 0 < ∏ w, (S.TcritPow w / (S.T:ℝ) ^ S.k) :=
    Finset.prod_pos (fun w _ => div_pos (hTc w) hTk)
  have hR : 0 < S.Dstar / S.du := by
    rw [hPA']
    exact mul_pos hEa0 hprod
  have hDs : 0 < S.Dstar := by
    first
    | exact (div_pos_iff_of_pos_right hdu).mp hR
    | (have h5 := mul_pos hR hdu
       rwa [div_mul_cancel₀ _ hdu.ne'] at h5)
  have hlog : Real.log (S.Dstar / S.du) =
      Real.log S.Ea + ∑ w, (Real.log (S.TcritPow w) - S.k * Real.log S.T) := by
    have hlp : Real.log (∏ w, (S.TcritPow w / (S.T:ℝ) ^ S.k)) =
        ∑ w, Real.log (S.TcritPow w / (S.T:ℝ) ^ S.k) := by
      first
      | exact Real.log_prod (fun w _ => (div_pos (hTc w) hTk).ne')
      | exact Real.log_prod _ _ (fun w _ => (div_pos (hTc w) hTk).ne')
    rw [hPA', Real.log_mul hEa0.ne' hprod.ne', hlp]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.log_div (hTc w).ne' hTk.ne', Real.log_pow]
  have hsum : ∑ w, (Real.log (S.TcritPow w) - S.k * Real.log S.T) =
      ∑ w, Real.log (S.TcritPow w) - (S.f:ℝ) * (S.k * Real.log S.T) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    try rfl
  have eL : Real.log (S.Dstar / S.du) = Real.log S.Dstar - Real.log S.du :=
    Real.log_div hDs.ne' hdu.ne'
  obtain ⟨hc1, hc2⟩ := hCh
  have hC00 : 0 < C0 := by linarith
  have hl1 := Real.log_le_log (by positivity) hc1
  have hl2 := Real.log_le_log hdu hc2
  have eA : Real.log ((Gam ^ 2)⁻¹ * S.Dstar * C0⁻¹) =
      -(2 * Real.log Gam) + Real.log S.Dstar - Real.log C0 := by
    rw [Real.log_mul (by positivity : (Gam ^ 2)⁻¹ * S.Dstar ≠ 0) (by positivity : C0⁻¹ ≠ 0),
      Real.log_mul (by positivity : (Gam ^ 2)⁻¹ ≠ 0) hDs.ne', Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have eB : Real.log ((Gam ^ 2)⁻¹ * S.Dstar * C0) =
      -(2 * Real.log Gam) + Real.log S.Dstar + Real.log C0 := by
    rw [Real.log_mul (by positivity : (Gam ^ 2)⁻¹ * S.Dstar ≠ 0) hC00.ne',
      Real.log_mul (by positivity : (Gam ^ 2)⁻¹ ≠ 0) hDs.ne', Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [eA] at hl1
  rw [eB] at hl2
  have hE := abs_le.mp hEa2
  rw [abs_le]
  constructor <;> linarith [hE.1, hE.2]

/- English proof (translation)
Introduce `ι _ G bb CDel Cb C0 Gam de de' T T' du du' hH hw hw' hT hT' hMR hLB hCC hCC' hds hC0 hGam hCh hCh' hf2 hC`. Establish `hf : 2 ≤ Fintype.card ι`. Establish `h1 : G.m ≤ G.f` using `hH.hmf`. Establish `h2 : G.m = 2 * G.r + 2` using `rfl`. Establish `h3 : G.f = Fintype.card ι` using `rfl`.

Use linear arithmetic over natural numbers and integers. Take `⟨w0⟩ : Nonempty ι` from `Fintype.card_pos_iff.1 (by omega)`. Establish `hk : 4 ≤ G.k` using `(hH.hplace w0).hk`. Establish `hkR : (4:ℝ) ≤ G.k` using `by exact_mod_cast hk`. Establish `hfR : (2:ℝ) ≤ (Fintype.card ι : ℝ)` using `by exact_mod_cast hf`.

Establish `hV : ∀ w, 0 < Vand G.k ((G.place w).u de) ∧ 0 < Vand G.k ((G.place w).u de') ∧ |Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de))| ≤ (G.k : ℝ) / 2 + 1` using `fun w => hVW (G.place w) de de' (hH.hplace w) (hH.hsmall w).hvth hw hw'`. Establish `hkb : (4:ℝ) ≤ ((G.k : ℝ) * bb) ^ 8`. Establish `h1 : (4:ℝ) ≤ (G.k : ℝ) * bb`. Use `hH.hbb` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Establish `hg1 : 4 ≤ G.g1` using `by exact_mod_cast hkb.trans hH.hg1`. Establish `hg2 : 4 ≤ G.g2` using `by exact_mod_cast hkb.trans hH.hg2`. Establish `hv0 : 0 < G.v` using `by have := hH.hv; linarith`. Establish `hOk : (G.size de T du).Ok` using `⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT, hH.hvol, fun w => (hV w).1⟩`.

Establish `hOk' : (G.size de' T' du').Ok` using `⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT', hH.hvol, fun w => (hV w).2.1⟩`. Establish `hX` using `one_word hPA hEa (G.size de T du) hOk hMR hLB hCC (by omega : 2 ≤ G.k) hg1 hg2 hds C0 Gam hC0 hGam hCh hf2`. Establish `hX'` using `one_word hPA hEa (G.size de' T' du') hOk' hMR hLB hCC' (by omega : 2 ≤ G.k) hg1 hg2 hds C0 Gam hC0 hGam hCh' hf2`. Establish `hdiff : ∀ w, Real.log ((G.size de T du).TcritPow w) - Real.log ((G.size de' T' du').TcritPow w) = Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de))`. Introduce `w`.

Establish `hg1' : (0:ℝ) < G.g1` using `by exact_mod_cast (by omega : 0 < G.g1)`. Establish `hg2' : (0:ℝ) < G.g2` using `by exact_mod_cast (by omega : 0 < G.g2)`. Conclude with `log_tp_diff G.k (2 * G.r + 2) (Real.pi / G.v) (2 * G.v) ((G.g1 : ℝ) * (G.g2 : ℝ)) (G.dsig w * (sfac (G.k + (2 * G.r + 2) - 1) : ℝ)) _ _ (by have := Real.pi_pos; positivity) (by positivity) (by positivity) (by have := hds w; have := sfac_pos (G.k + (2 * G.r + 2) - 1); positivity) …`. Establish `hsum : |∑ w, Real.log ((G.size de T du).TcritPow w) - ∑ w, Real.log ((G.size de' T' du').TcritPow w)| ≤ (Fintype.card ι : ℝ) * ((G.k : ℝ) / 2 + 1)`. Rewrite using `[← Finset.sum_sub_distrib]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `w _`. Rewrite using `[hdiff w]`. Conclude with `(hV w).2.2`.

Use `_ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hC' : Real.log 2 + Real.log C0 ≤ (G.k : ℝ) * (Fintype.card ι : ℝ) / 16`. Establish `h2C : 0 < 2 * C0` using `by linarith`. Establish `h1 : (2 * C0) ^ (4 / ((G.k : ℝ) * (Fintype.card ι : ℝ))) ≤ Real.exp (1 / 4)` using `hC`. Rewrite `h1` using `[Real.rpow_def_of_pos h2C, Real.exp_le_exp, Real.log_mul (by norm_num) (by linarith), mul_div_assoc', div_le_iff₀ (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT0 : (0:ℝ) < T` using `by exact_mod_cast (by omega : 0 < T)`. Establish `hT0' : (0:ℝ) < T'` using `by exact_mod_cast (by omega : 0 < T')`. Establish `hX1 : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T) - ∑ w, Real.log ((G.size de T du).TcritPow w) + 2 * Real.log Gam| ≤ Real.log 2 + Real.log C0` using `hX`. Establish `hX1' : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T') - ∑ w, Real.log ((G.size de' T' du').TcritPow w) + 2 * Real.log Gam| ≤ Real.log 2 + Real.log C0` using `hX'`.

Rewrite `hX1`, `hX1'`, `hsum` using `[abs_le]`. Establish `hfk : 0 < (Fintype.card ι : ℝ) * (G.k : ℝ)` using `by positivity`. Establish `hf4 : (Fintype.card ι : ℝ) * 4 ≤ (Fintype.card ι : ℝ) * (G.k : ℝ)` using `by gcongr`. Establish `hmain1 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T') ≤ (Fintype.card ι : ℝ) * (G.k : ℝ) * 1` using `by nlinarith [hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]`. Establish `hmain2 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (-1) ≤ (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T')`.

Use polynomial arithmetic with `[hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]`. Establish `h1` using `le_of_mul_le_mul_left hmain1 hfk`. Establish `h2` using `le_of_mul_le_mul_left hmain2 hfk`. Establish `hTT : (T : ℝ) / T' = Real.exp (Real.log T - Real.log T')`. Rewrite using `[Real.exp_sub, Real.exp_log hT0, Real.exp_log hT0']`.

Rewrite using `[hTT]`. Conclude with `⟨Real.exp_le_exp.2 h2, Real.exp_le_exp.2 h1⟩`.
-/
theorem tWords_of (hPA : PropA) (hEa : EaSize) (hVW : VandWords) : TWords := by
  intro ι _ G bb CDel Cb C0 Gam de de' T T' du du' hH hw hw' hT hT' hMR hLB hCC hCC' hds hC0 hGam
    hCh hCh' hf2 hC
  have hf : 2 ≤ Fintype.card ι := by
    have h1 : G.m ≤ G.f := hH.hmf
    have h2 : G.m = 2 * G.r + 2 := rfl
    have h3 : G.f = Fintype.card ι := rfl
    omega
  obtain ⟨w0⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hk : 4 ≤ G.k := (hH.hplace w0).hk
  have hkR : (4:ℝ) ≤ G.k := by exact_mod_cast hk
  have hfR : (2:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hf
  have hV : ∀ w, 0 < Vand G.k ((G.place w).u de) ∧ 0 < Vand G.k ((G.place w).u de') ∧
      |Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de))| ≤ (G.k : ℝ) / 2 + 1 :=
    fun w => hVW (G.place w) de de' (hH.hplace w) (hH.hsmall w).hvth hw hw'
  have hkb : (4:ℝ) ≤ ((G.k : ℝ) * bb) ^ 8 := by
    have h1 : (4:ℝ) ≤ (G.k : ℝ) * bb := by
      have := hH.hbb
      nlinarith
    calc (4:ℝ) ≤ 4 ^ 8 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 8
  have hg1 : 4 ≤ G.g1 := by exact_mod_cast hkb.trans hH.hg1
  have hg2 : 4 ≤ G.g2 := by exact_mod_cast hkb.trans hH.hg2
  have hv0 : 0 < G.v := by have := hH.hv; linarith
  have hOk : (G.size de T du).Ok :=
    ⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT, hH.hvol,
      fun w => (hV w).1⟩
  have hOk' : (G.size de' T' du').Ok :=
    ⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT', hH.hvol,
      fun w => (hV w).2.1⟩
  have hX := one_word hPA hEa (G.size de T du) hOk hMR hLB hCC (by omega : 2 ≤ G.k) hg1 hg2 hds
    C0 Gam hC0 hGam hCh hf2
  have hX' := one_word hPA hEa (G.size de' T' du') hOk' hMR hLB hCC' (by omega : 2 ≤ G.k) hg1 hg2 hds
    C0 Gam hC0 hGam hCh' hf2
  have hdiff : ∀ w, Real.log ((G.size de T du).TcritPow w) - Real.log ((G.size de' T' du').TcritPow w)
      = Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de)) := by
    intro w
    have hg1' : (0:ℝ) < G.g1 := by exact_mod_cast (by omega : 0 < G.g1)
    have hg2' : (0:ℝ) < G.g2 := by exact_mod_cast (by omega : 0 < G.g2)
    exact log_tp_diff G.k (2 * G.r + 2) (Real.pi / G.v) (2 * G.v) ((G.g1 : ℝ) * (G.g2 : ℝ))
      (G.dsig w * (sfac (G.k + (2 * G.r + 2) - 1) : ℝ)) _ _
      (by have := Real.pi_pos; positivity) (by positivity) (by positivity)
      (by have := hds w; have := sfac_pos (G.k + (2 * G.r + 2) - 1); positivity) (hV w).1 (hV w).2.1
  have hsum : |∑ w, Real.log ((G.size de T du).TcritPow w) -
      ∑ w, Real.log ((G.size de' T' du').TcritPow w)| ≤ (Fintype.card ι : ℝ) * ((G.k : ℝ) / 2 + 1) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ w, |Real.log ((G.size de T du).TcritPow w) -
          Real.log ((G.size de' T' du').TcritPow w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : ι, ((G.k : ℝ) / 2 + 1) := by
          apply Finset.sum_le_sum; intro w _; rw [hdiff w]; exact (hV w).2.2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hC' : Real.log 2 + Real.log C0 ≤ (G.k : ℝ) * (Fintype.card ι : ℝ) / 16 := by
    have h2C : 0 < 2 * C0 := by linarith
    have h1 : (2 * C0) ^ (4 / ((G.k : ℝ) * (Fintype.card ι : ℝ))) ≤ Real.exp (1 / 4) := hC
    rw [Real.rpow_def_of_pos h2C, Real.exp_le_exp, Real.log_mul (by norm_num) (by linarith),
      mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    linarith
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hT0' : (0:ℝ) < T' := by exact_mod_cast (by omega : 0 < T')
  have hX1 : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T) -
      ∑ w, Real.log ((G.size de T du).TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := hX
  have hX1' : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T') -
      ∑ w, Real.log ((G.size de' T' du').TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := hX'
  rw [abs_le] at hX1 hX1' hsum
  have hfk : 0 < (Fintype.card ι : ℝ) * (G.k : ℝ) := by positivity
  have hf4 : (Fintype.card ι : ℝ) * 4 ≤ (Fintype.card ι : ℝ) * (G.k : ℝ) := by gcongr
  have hmain1 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T') ≤
      (Fintype.card ι : ℝ) * (G.k : ℝ) * 1 := by nlinarith [hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]
  have hmain2 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (-1) ≤
      (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T') := by
    nlinarith [hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]
  have h1 := le_of_mul_le_mul_left hmain1 hfk
  have h2 := le_of_mul_le_mul_left hmain2 hfk
  have hTT : (T : ℝ) / T' = Real.exp (Real.log T - Real.log T') := by
    rw [Real.exp_sub, Real.exp_log hT0, Real.exp_log hT0']
  rw [hTT]
  exact ⟨Real.exp_le_exp.2 h2, Real.exp_le_exp.2 h1⟩

end Formalism.FourierDecayAlt.P.Sz5

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Sz5.tcritWords_of vandermondeWords`.
-/
theorem critical_threshold_words : Formalism.FourierDecayAlt.Sz.TcritWords := Sz5.tcritWords_of vandermondeWords

/- English proof (translation)
The claim follows from `Sz5.tWords_of massRatioFormula exponent_sizes vandermondeWords`.
-/
theorem threshold_words : Formalism.FourierDecayAlt.Sz.TWords := Sz5.tWords_of massRatioFormula exponent_sizes vandermondeWords

/- English proof (translation)
The claim follows from `Sz5.vandLamLower`.
-/
theorem vandermonde_lambda_lower_bound : Formalism.FourierDecayAlt.Sz.VandLamLower := Sz5.vandLamLower

/- English proof (translation)
The claim follows from `Sz5.tcritLower_of bracket_bound_alt vandermondeNonTop vandermondeTop edgeFactors vandermondeWords`.
-/
theorem critical_threshold_lower_bound : Formalism.FourierDecayAlt.Sz.TcritLower := Sz5.tcritLower_of bracket_bound_alt vandermondeNonTop vandermondeTop edgeFactors vandermondeWords

end Formalism.FourierDecayAlt.P
