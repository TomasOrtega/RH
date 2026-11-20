import ReciprocityTheory.Chebotarev.SplitDef
import ReciprocityTheory.Chebotarev.SplitF
import ReciprocityTheory.Chebotarev.ChebyshevLambdaSubPsiBounded

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Establish `: Nrm q ≠ 0`. Unfold `Nrm`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `q.ne_bot`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions.
-/
theorem splitC_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 0 < ((Nrm q : ℕ) : ℝ) := by
  have : Nrm q ≠ 0 := by
    unfold Nrm
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

/- English proof (translation)
Establish `h` using `splitC_nrm_pos q`. Establish `: 0 < Nrm q` using `by exact_mod_cast h`. Conclude with `this` after adjusting the coercions.
-/
theorem splitC_nrm_ge_one {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ ((Nrm q : ℕ) : ℝ) := by
  have h := splitC_nrm_pos q
  have : 0 < Nrm q := by exact_mod_cast h
  exact_mod_cast this

/- English proof (translation)
Rewrite using `[tsum_eq_sum (s := hS.toFinset)]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `q hq`. Rewrite using `[Set.indicator_of_mem (hS.mem_toFinset.mp hq)]`.

Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)`. Use `_ = hS.toFinset.card := by simp`. Introduce `q hq`. Rewrite using `[Set.indicator_of_notMem]`. Introduce `h'`.

Conclude with `hq (hS.mem_toFinset.mpr h')`.
-/
theorem splitC_indicator_le {E : Type} [Field E] [NumberField E] (S : Set (Prm E)) (hS : S.Finite) (s : ℝ)
    (hs : 0 ≤ s) : ∑' q, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q ≤ hS.toFinset.card := by
  rw [tsum_eq_sum (s := hS.toFinset)]
  · calc ∑ q ∈ hS.toFinset, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q
        ≤ ∑ _q ∈ hS.toFinset, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Set.indicator_of_mem (hS.mem_toFinset.mp hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)
      _ = hS.toFinset.card := by simp
  · intro q hq
    rw [Set.indicator_of_notMem]
    intro h'
    exact hq (hS.mem_toFinset.mpr h')

/- English proof (translation)
Establish `key` using `fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s)) (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_ …`. Introduce `q hq`. Establish `hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} = {P : Prm E' | under P = q ∧ Nrm P = Nrm q}`. Use extensionality with `P`. Simplify using `only [Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `(Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, by rw [h2]⟩`. Rewrite using `[hset]`. Conclude with `h q hq)`. Establish `hind` using `splitC_indicator_le S hS s (by linarith)`.

Unfold `PE`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hind hk0]`.
-/
theorem splitC_bound (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by
  have key := fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s))
    (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E s hs) S hS
    (by
      intro q hq
      have hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} =
          {P : Prm E' | under P = q ∧ Nrm P = Nrm q} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2
          exact_mod_cast this
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
      rw [hset]
      exact h q hq)
  have hind := splitC_indicator_le S hS s (by linarith)
  unfold PE
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hind hk0]

/- English proof (translation)
Use `set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef`. Establish `hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard`. Introduce `q hq`. Assume the negation of the conclusion as `hc`. Conclude with `hq hc`.

Take `⟨C1, hC1⟩` from `chebyshev_log_bounded E`. Take `⟨C2, hC2⟩` from `chebyshev_log_bounded E'`. Use `set N : ℝ := (h.toFinset.card : ℝ)`. Use `set M : ℝ := max (C2 + k * (N + C1)) 0`. Use `set s : ℝ := 1 + Real.exp (-(M + 1))`.

Establish `he : 0 < Real.exp (-(M + 1))` using `Real.exp_pos _`. Establish `he1 : Real.exp (-(M + 1)) ≤ 1` using `Real.exp_le_one_iff.mpr (by`. Establish `: 0 ≤ M` using `le_max_right _ _`. Use the proof step `linarith)`. Establish `hs1 : 1 < s` using `by simp only [s]; linarith`.

Establish `hs2 : s ∈ Set.Ioc 1 2` using `⟨hs1, by simp only [s]; linarith⟩`. Establish `hlog : Real.log (1 / (s - 1)) = M + 1`. Simplify using `only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]`. Establish `hb` using `splitC_bound E E' k S h hfib s hs1`. Establish `h1` using `hC1 s hs2`.

Establish `h2` using `hC2 s hs2`. Rewrite `h1`, `h2` using `[hlog]`. Establish `hk' : (2 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hM : C2 + k * (N + C1) ≤ M` using `le_max_left _ _`. Establish `hM0 : 0 ≤ M` using `le_max_right _ _`.

Establish `a1` using `abs_le.mp h1`. Establish `a2` using `abs_le.mp h2`. Establish `: (k : ℝ) * (M + 1 - C1) ≤ k * PE E s` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem splitC_not_almost_split (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by
  set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef
  have hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
    intro q hq
    by_contra hc
    exact hq hc
  obtain ⟨C1, hC1⟩ := chebyshev_log_bounded E
  obtain ⟨C2, hC2⟩ := chebyshev_log_bounded E'
  set N : ℝ := (h.toFinset.card : ℝ)
  set M : ℝ := max (C2 + k * (N + C1)) 0
  set s : ℝ := 1 + Real.exp (-(M + 1))
  have he : 0 < Real.exp (-(M + 1)) := Real.exp_pos _
  have he1 : Real.exp (-(M + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ M := le_max_right _ _
    linarith)
  have hs1 : 1 < s := by simp only [s]; linarith
  have hs2 : s ∈ Set.Ioc 1 2 := ⟨hs1, by simp only [s]; linarith⟩
  have hlog : Real.log (1 / (s - 1)) = M + 1 := by
    simp only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := splitC_bound E E' k S h hfib s hs1
  have h1 := hC1 s hs2
  have h2 := hC2 s hs2
  rw [hlog] at h1 h2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : C2 + k * (N + C1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have : (k : ℝ) * (M + 1 - C1) ≤ k * PE E s := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

end ReciprocityTheory.Cheb
