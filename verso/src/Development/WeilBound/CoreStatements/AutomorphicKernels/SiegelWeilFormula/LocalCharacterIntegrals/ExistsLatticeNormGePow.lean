import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ContinuousLatticeNorm

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.SwLocFin
open scoped TensorProduct Matrix ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {v : HeightOneSpectrum (𝓞 F)}

def digits (ϖ : Fv F v) : (m : ℕ) → (Fin m → Bool) → Fv F v
  | 0, _ => 0
  | m + 1, δ => (if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)

/- English proof (translation)
Apply the tactic sequence `cases b <;> simp`.
-/
theorem norm_ite_le (b : Bool) : ‖(if b then (1 : Fv F v) else 0)‖ ≤ 1 := by
  cases b <;> simp

/- English proof (translation)
The claim follows from `| 0, _ => by simp [digits] | m + 1, δ => by show ‖(if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)‖ ≤ 1 refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_ite_le _) ?_) rw [norm_mul] exact mul_le_one₀ hϖ (norm_nonneg _) (norm_digits_le hϖ m _)`.
-/
theorem norm_digits_le {ϖ : Fv F v} (hϖ : ‖ϖ‖ ≤ 1) : ∀ (m : ℕ) (δ : Fin m → Bool), ‖digits ϖ m δ‖ ≤ 1
  | 0, _ => by simp [digits]
  | m + 1, δ => by
    show ‖(if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)‖ ≤ 1
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_ite_le _) ?_)
    rw [norm_mul]
    exact mul_le_one₀ hϖ (norm_nonneg _) (norm_digits_le hϖ m _)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rw [norm_neg]; exact hb))`.
-/
theorem norm_sub_le_one {a b : Fv F v} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rw [norm_neg]; exact hb))

/- English proof (translation)
The claim follows from `| 0, δ, δ', h => absurd (funext fun i => i.elim0) h | m + 1, δ, δ', h => by show ‖ϖ‖ ^ (m + 1) ≤ ‖((if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)) - ((if δ' 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ'))‖ by_cases h0 : δ 0 = δ' 0 · have ht : Fin.tail δ ≠ Fin.tail δ' := by …`.
-/
theorem digits_sep {ϖ : Fv F v} (hϖ1 : ‖ϖ‖ < 1) :
    ∀ (m : ℕ) (δ δ' : Fin m → Bool), δ ≠ δ' → ‖ϖ‖ ^ m ≤ ‖digits ϖ m δ - digits ϖ m δ'‖
  | 0, δ, δ', h => absurd (funext fun i => i.elim0) h
  | m + 1, δ, δ', h => by
    show ‖ϖ‖ ^ (m + 1) ≤ ‖((if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)) -
      ((if δ' 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ'))‖
    by_cases h0 : δ 0 = δ' 0
    · have ht : Fin.tail δ ≠ Fin.tail δ' := by
        intro ht; apply h; rw [← Fin.cons_self_tail δ, ← Fin.cons_self_tail δ', h0, ht]
      rw [h0, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (digits_sep hϖ1 m _ _ ht) (norm_nonneg _)
    · have hone : ‖((if δ 0 then 1 else 0 : Fv F v)) - (if δ' 0 then 1 else 0)‖ = 1 := by
        cases hδ : δ 0 <;> cases hδ' : δ' 0 <;> simp_all
      have hsmall : ‖ϖ * (digits ϖ m (Fin.tail δ) - digits ϖ m (Fin.tail δ'))‖ < 1 := by
        rw [norm_mul]
        have := norm_sub_le_one (norm_digits_le hϖ1.le m (Fin.tail δ)) (norm_digits_le hϖ1.le m (Fin.tail δ'))
        calc _ ≤ ‖ϖ‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact hϖ1
      have hre : ((if δ 0 then (1 : Fv F v) else 0) + ϖ * digits ϖ m (Fin.tail δ)) -
          ((if δ' 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ')) =
          ((if δ 0 then 1 else 0) - (if δ' 0 then 1 else 0)) +
            ϖ * (digits ϖ m (Fin.tail δ) - digits ϖ m (Fin.tail δ')) := by ring
      rw [hre, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hone]; exact hsmall.ne'), hone]
      exact (pow_le_one₀ (norm_nonneg _) hϖ1.le).trans (le_max_left _ _)

variable {n : ℕ}

/- English proof (translation)
Unfold `nu2 at hb ⊢`. Use `set G : Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y'} with hG`. Establish `hL1m : MeasurableSet (L₁ : Set (Fin n → Fv F v ⊗[F] E))` using `h1.1.measurableSet`. Use `set T : ι → Set (Fin n → Fv F v ⊗[F] E) := fun i => (fun x => -b.mulVec (y i) + x) ⁻¹' (L₁ : Set _) with hT`. Establish `hTm : ∀ i, MeasurableSet (T i)` using `fun i => (measurable_const_add _) hL1m`.

Establish `hTv : ∀ i, lam (T i) = lam L₁` using `fun i => measure_preimage_add lam _ _`. Establish `hdisj : Pairwise (Function.onFun Disjoint T)`. Introduce `i j hij`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hxi hxj`.

Apply `hsep j i (Ne.symm hij)` to reduce the goal to its premises. Establish `hxi' : -b.mulVec (y i) + x ∈ L₁` using `hxi`. Establish `hxj' : -b.mulVec (y j) + x ∈ L₁` using `hxj`. Establish `heq : b.mulVec (y j) - b.mulVec (y i) = (-b.mulVec (y i) + x) - (-b.mulVec (y j) + x)` using `by abel`. Rewrite using `[heq]`.

Conclude with `L₁.sub_mem hxi' hxj'`. Establish `hsubG : (⋃ i, T i) ⊆ G`. Introduce `x hx`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hx`. Conclude with `⟨-b.mulVec (y i) + x, hi, y i, hy i, by abel⟩`.

Establish `hmeas : (Fintype.card ι : ℝ≥0∞) * lam L₁ ≤ lam G`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl (fun i _ => hTv i), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `_ = lam (⋃ i, T i) := by rw [measure_iUnion hdisj hTm, tsum_fintype]`. Use `_ ≤ lam G := measure_mono hsubG`.

Establish `hpos : lam L₁ ≠ 0` using `(h1.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'`. Establish `hfin : lam L₁ ≠ ⊤` using `h1.2.measure_lt_top.ne`. Establish `hle : (Fintype.card ι : ℝ≥0∞) ≤ lam G / lam L₁` using `(ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 hmeas`. Establish `hne : lam G / lam L₁ ≠ ⊤`. Introduce `htop`.

Rewrite `hb` using `[htop, ENNReal.toReal_top]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `ENNReal.toReal_mono hne hle` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_natCast]`. Then use the resulting hypothesis.
-/
theorem card_le_lattice_norm {ι : Type} [Fintype ι] (lam : Measure (Fin n → Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h1 : IsCO L₁) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hb : 1 ≤ nu2 lam L₁ L₂ b) (y : ι → Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ L₂)
    (hsep : ∀ i j, i ≠ j → b.mulVec (y i) - b.mulVec (y j) ∉ L₁) :
    (Fintype.card ι : ℝ) ≤ nu2 lam L₁ L₂ b := by
  classical
  unfold nu2 at hb ⊢
  set G : Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y'} with hG
  have hL1m : MeasurableSet (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := h1.1.measurableSet
  set T : ι → Set (Fin n → Fv F v ⊗[F] E) := fun i => (fun x => -b.mulVec (y i) + x) ⁻¹' (L₁ : Set _) with hT
  have hTm : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_add _) hL1m
  have hTv : ∀ i, lam (T i) = lam L₁ := fun i => measure_preimage_add lam _ _
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    apply hsep j i (Ne.symm hij)
    have hxi' : -b.mulVec (y i) + x ∈ L₁ := hxi
    have hxj' : -b.mulVec (y j) + x ∈ L₁ := hxj
    have heq : b.mulVec (y j) - b.mulVec (y i) = (-b.mulVec (y i) + x) - (-b.mulVec (y j) + x) := by abel
    rw [heq]; exact L₁.sub_mem hxi' hxj'
  have hsubG : (⋃ i, T i) ⊆ G := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨-b.mulVec (y i) + x, hi, y i, hy i, by abel⟩
  have hmeas : (Fintype.card ι : ℝ≥0∞) * lam L₁ ≤ lam G := by
    calc (Fintype.card ι : ℝ≥0∞) * lam L₁ = ∑ i, lam (T i) := by
          rw [Finset.sum_congr rfl (fun i _ => hTv i), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = lam (⋃ i, T i) := by rw [measure_iUnion hdisj hTm, tsum_fintype]
      _ ≤ lam G := measure_mono hsubG
  have hpos : lam L₁ ≠ 0 := (h1.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin : lam L₁ ≠ ⊤ := h1.2.measure_lt_top.ne
  have hle : (Fintype.card ι : ℝ≥0∞) ≤ lam G / lam L₁ :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 hmeas
  have hne : lam G / lam L₁ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hb
    linarith
  have := ENNReal.toReal_mono hne hle
  rwa [ENNReal.toReal_natCast] at this

/- English proof (translation)
Rewrite using `[nV_le_iff (nA_nonneg _)]`. Introduce `i`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.single_eq_of_ne hik, nA_zero]`. Conclude with `nA_nonneg _`.
-/
theorem nV_single_le (k : Fin n) : nV v (Pi.single k (1 : Fv F v ⊗[F] E)) ≤ nA v (1 : Fv F v ⊗[F] E) := by
  classical
  rw [nV_le_iff (nA_nonneg _)]
  intro i
  by_cases hik : i = k
  · subst hik; simp
  · rw [Pi.single_eq_of_ne hik, nA_zero]; exact nA_nonneg _

/- English proof (translation)
Break down `(Finset.univ : Finset (Fin p × Fin q)).eq_empty_or_nonempty with he | hne` into its components or cases. It suffices to derive a contradiction. Establish `: nM v x ≤ 0` using `(nM_le_iff le_rfl).2 fun i j => absurd (Finset.mem_univ (i, j)) (by rw [he]; exact Finset.notMem_empty _)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨⟨i, j⟩, -, hmax⟩` from `Finset.exists_max_image _ (fun ij : Fin p × Fin q => nA v (x ij.1 ij.2)) hne`.

Conclude with `⟨i, j, (nM_le_iff (nA_nonneg _)).2 fun i' j' => hmax (i', j') (Finset.mem_univ _)⟩`.
-/
theorem exists_entry_ge {p q : ℕ} (x : Fin p → Fin q → Fv F v ⊗[F] E) (hx : 0 < nM v x) :
    ∃ i j, nM v x ≤ nA v (x i j) := by
  rcases (Finset.univ : Finset (Fin p × Fin q)).eq_empty_or_nonempty with he | hne
  · exfalso
    have : nM v x ≤ 0 := (nM_le_iff le_rfl).2 fun i j =>
      absurd (Finset.mem_univ (i, j)) (by rw [he]; exact Finset.notMem_empty _)
    linarith
  · obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image _ (fun ij : Fin p × Fin q => nA v (x ij.1 ij.2)) hne
    exact ⟨i, j, (nM_le_iff (nA_nonneg _)).2 fun i' j' => hmax (i', j') (Finset.mem_univ _)⟩

/- English proof (translation)
Take `⟨ε, hε, hsub⟩` from `exists_ballV_subset (v := v) (U := (L₂ : Set (Fin n → Fv F v ⊗[F] E))) (h2.1.mem_nhds L₂.zero_mem)`. Take `⟨ρ, hρ⟩` from `exists_bound_nV (v := v) h1.2`. Use `set C := nA v (1 : Fv F v ⊗[F] E) with hC`. Establish `hC0 : 0 ≤ C` using `nA_nonneg _`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < C + 1)) hϖ1`.

Use `set t0 : Fv F v := ϖ ^ N with ht0`. Establish `ht0n : ‖t0‖ = ‖ϖ‖ ^ N` using `norm_pow _ _`. Establish `ht0p : 0 < ‖t0‖` using `by rw [ht0n]; exact pow_pos hϖ0 _`. Establish `ht0C : ‖t0‖ * C ≤ ε`. Rewrite using `[ht0n]`.

Establish `h' : ‖ϖ‖ ^ N * (C + 1) < ε` using `(lt_div_iff₀ (by linarith)).1 hN`. Use polynomial arithmetic with `[pow_pos hϖ0 N]`. Use `⟨(|ρ| + 1) / ‖t0‖, div_pos (by positivity) ht0p, fun m b hb hR => ?_⟩` and prove the remaining obligations. Establish `hq : 0 < ‖ϖ‖⁻¹ ^ m` using `pow_pos (inv_pos.2 hϖ0) _`. Establish `hbpos : 0 < nM v b` using `lt_of_lt_of_le (mul_pos (div_pos (by positivity) ht0p) hq) hR`.

Take `⟨i, k, hik⟩` from `exists_entry_ge (v := v) b hbpos`. Use `set e : Fin n → Fv F v ⊗[F] E := Pi.single k 1 with he`. Use `set w : Fin n → Fv F v ⊗[F] E := b.mulVec e with hw`. Establish `hwi : nM v b ≤ nV v w`. Use `hik.trans ?_` and prove the remaining obligations.

Establish `: w i = b i k` using `by rw [hw, he, Matrix.mulVec_single_one]; rfl`. Rewrite using `[← this]`. Conclude with `nA_le_nV _ _`. Set `y : (Fin m → Bool) → Fin n → Fv F v ⊗[F] E` to `fun δ => (digits ϖ m δ * t0) • e`. Establish `hy : ∀ δ, y δ ∈ L₂`.

Introduce `δ`. Apply `hsub` to reduce the goal to its premises. Use `show nV v ((digits ϖ m δ * t0) • e) ≤ ε`. Rewrite using `[nV_smul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul (mul_le_mul_of_nonneg_right (norm_digits_le hϖ1.le m δ) (norm_nonneg _)) (nV_single_le k) (by unfold nV; exact norm_nonneg _) (by positivity)` to reduce the goal to its premises. Use `_ ≤ ε := by rw [one_mul]; exact ht0C`. Establish `hsep : ∀ δ δ', δ ≠ δ' → b.mulVec (y δ) - b.mulVec (y δ') ∉ L₁`. Introduce `δ δ' hne hmem`. Establish `hval : b.mulVec (y δ) - b.mulVec (y δ') = ((digits ϖ m δ - digits ϖ m δ') * t0) • w`.

Simplify using `only [y, Matrix.mulVec_smul, hw, ← sub_smul, ← sub_mul]`. Establish `h3` using `hρ _ hmem`. Rewrite `h3` using `[hval, nV_smul, norm_mul]`. Establish `h4 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) ≤ ‖digits ϖ m δ - digits ϖ m δ'‖ * ‖t0‖ * nV v w` using `by gcongr`. Conclude with `digits_sep hϖ1 m δ δ' hne`.

Conclude with `hR.trans hwi`. Establish `h5 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) = |ρ| + 1`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite `h4` using `[h5]`.

Use `le_abs_self ρ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `card_le_lattice_norm lam h1 b hb y hy hsep` as an intermediate fact. Simplify `this` using `[Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]`.
-/
theorem exists_lattice_norm_ge_pow {ϖ : Fv F v} (hϖ0 : 0 < ‖ϖ‖) (hϖ1 : ‖ϖ‖ < 1)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h1 : IsCO L₁) (h2 : IsCO L₂) :
    ∃ R₀ > 0, ∀ (m : ℕ) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), 1 ≤ nu2 lam L₁ L₂ b →
      R₀ * ‖ϖ‖⁻¹ ^ m ≤ nM v b → (2 : ℝ) ^ m ≤ nu2 lam L₁ L₂ b := by
  classical
  obtain ⟨ε, hε, hsub⟩ := exists_ballV_subset (v := v) (U := (L₂ : Set (Fin n → Fv F v ⊗[F] E)))
    (h2.1.mem_nhds L₂.zero_mem)
  obtain ⟨ρ, hρ⟩ := exists_bound_nV (v := v) h1.2
  set C := nA v (1 : Fv F v ⊗[F] E) with hC
  have hC0 : 0 ≤ C := nA_nonneg _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < C + 1)) hϖ1
  set t0 : Fv F v := ϖ ^ N with ht0
  have ht0n : ‖t0‖ = ‖ϖ‖ ^ N := norm_pow _ _
  have ht0p : 0 < ‖t0‖ := by rw [ht0n]; exact pow_pos hϖ0 _
  have ht0C : ‖t0‖ * C ≤ ε := by
    rw [ht0n]
    have h' : ‖ϖ‖ ^ N * (C + 1) < ε := (lt_div_iff₀ (by linarith)).1 hN
    nlinarith [pow_pos hϖ0 N]
  refine ⟨(|ρ| + 1) / ‖t0‖, div_pos (by positivity) ht0p, fun m b hb hR => ?_⟩
  have hq : 0 < ‖ϖ‖⁻¹ ^ m := pow_pos (inv_pos.2 hϖ0) _
  have hbpos : 0 < nM v b := lt_of_lt_of_le (mul_pos (div_pos (by positivity) ht0p) hq) hR
  obtain ⟨i, k, hik⟩ := exists_entry_ge (v := v) b hbpos
  set e : Fin n → Fv F v ⊗[F] E := Pi.single k 1 with he
  set w : Fin n → Fv F v ⊗[F] E := b.mulVec e with hw
  have hwi : nM v b ≤ nV v w := by
    refine hik.trans ?_
    have : w i = b i k := by rw [hw, he, Matrix.mulVec_single_one]; rfl
    rw [← this]; exact nA_le_nV _ _
  let y : (Fin m → Bool) → Fin n → Fv F v ⊗[F] E := fun δ => (digits ϖ m δ * t0) • e
  have hy : ∀ δ, y δ ∈ L₂ := by
    intro δ
    apply hsub
    show nV v ((digits ϖ m δ * t0) • e) ≤ ε
    rw [nV_smul, norm_mul]
    calc ‖digits ϖ m δ‖ * ‖t0‖ * nV v e ≤ 1 * ‖t0‖ * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (norm_digits_le hϖ1.le m δ) (norm_nonneg _))
            (nV_single_le k) (by unfold nV; exact norm_nonneg _) (by positivity)
      _ ≤ ε := by rw [one_mul]; exact ht0C
  have hsep : ∀ δ δ', δ ≠ δ' → b.mulVec (y δ) - b.mulVec (y δ') ∉ L₁ := by
    intro δ δ' hne hmem
    have hval : b.mulVec (y δ) - b.mulVec (y δ') = ((digits ϖ m δ - digits ϖ m δ') * t0) • w := by
      simp only [y, Matrix.mulVec_smul, hw, ← sub_smul, ← sub_mul]
    have h3 := hρ _ hmem
    rw [hval, nV_smul, norm_mul] at h3
    have h4 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) ≤
        ‖digits ϖ m δ - digits ϖ m δ'‖ * ‖t0‖ * nV v w := by
      gcongr
      · exact digits_sep hϖ1 m δ δ' hne
      · exact hR.trans hwi
    have h5 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) = |ρ| + 1 := by
      rw [inv_pow]
      field_simp
    rw [h5] at h4
    have := le_abs_self ρ
    linarith
  have := card_le_lattice_norm lam h1 b hb y hy hsep
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify using `[sigR, Algebra.TensorProduct.map_tmul]`.
-/
theorem cvSigR_smul (σ : E →ₐ[F] E) (t : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (t • x) = t • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [sigR, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Establish `hS' : ∀ a b, sigR (Fv F v) σ (S b a) = S a b` using `hS`. Use `show ∀ a b, sigR (Fv F v) σ ((t • S) b a) = (t • S) a b`. Introduce `a b`. Simplify using `only [Matrix.smul_apply]`. Rewrite using `[cvSigR_smul, hS' a b]`.
-/
theorem smul_mem_herm (σ : E →ₐ[F] E) (t : Fv F v) {S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hS : S ∈ HermR (Fv F v) σ n) : t • S ∈ HermR (Fv F v) σ n := by
  have hS' : ∀ a b, sigR (Fv F v) σ (S b a) = S a b := hS
  show ∀ a b, sigR (Fv F v) σ ((t • S) b a) = (t • S) a b
  intro a b
  simp only [Matrix.smul_apply]
  rw [cvSigR_smul, hS' a b]

def scH (σ : E →ₐ[F] E) (n : ℕ) {t : Fv F v} (ht : t ≠ 0) : HermR (Fv F v) σ n ≃+ HermR (Fv F v) σ n where
  toFun b := ⟨t • b.1, smul_mem_herm σ t b.2⟩
  invFun b := ⟨t⁻¹ • b.1, smul_mem_herm σ t⁻¹ b.2⟩
  left_inv b := Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ ht])
  right_inv b := Subtype.ext (by simp [smul_smul, mul_inv_cancel₀ ht])
  map_add' a b := Subtype.ext (by simp [smul_add])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scH_val (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) (b : HermR (Fv F v) σ n) :
    (scH σ n ht b).1 = t • b.1 := rfl

/- English proof (translation)
The claim follows from `Continuous.subtype_mk (continuous_subtype_val.const_smul t) _`.
-/
theorem continuous_scH (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) : Continuous (scH σ n ht) :=
  Continuous.subtype_mk (continuous_subtype_val.const_smul t) _

/- English proof (translation)
The claim follows from `Continuous.subtype_mk (continuous_subtype_val.const_smul t⁻¹) _`.
-/
theorem continuous_scH_symm (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) : Continuous (scH σ n ht).symm :=
  Continuous.subtype_mk (continuous_subtype_val.const_smul t⁻¹) _

instance secondCountable_HermCv (σ : E →ₐ[F] E) (n : ℕ) : SecondCountableTopology (HermR (Fv F v) σ n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  TopologicalSpace.Subtype.secondCountableTopology _

/- English proof (translation)
Use `haveI : (ν.map (scH σ n ht)).IsAddHaarMeasure := (scH σ n ht).isAddHaarMeasure_map ν (continuous_scH σ ht) (continuous_scH_symm σ ht)`. Use `⟨Measure.addHaarScalarFactor (ν.map (scH σ n ht)) ν, fun A hA => ?_⟩` and prove the remaining obligations. Establish `hk` using `Measure.isAddLeftInvariant_eq_smul (ν.map (scH σ n ht)) ν`. Use `congrArg (fun μ : Measure (HermR (Fv F v) σ n) => μ A) hk` as an intermediate fact. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this`.

Rewrite using `[← Measure.map_apply (continuous_scH σ ht).measurable hA]`. Conclude with `this`.
-/
theorem exists_scale (σ : E →ₐ[F] E) (n : ℕ) (ν : Measure (HermR (Fv F v) σ n)) [ν.IsAddHaarMeasure]
    {t : Fv F v} (ht : t ≠ 0) :
    ∃ k : ℝ≥0, ∀ A, MeasurableSet A → ν ((scH σ n ht) ⁻¹' A) = k * ν A := by
  haveI : (ν.map (scH σ n ht)).IsAddHaarMeasure :=
    (scH σ n ht).isAddHaarMeasure_map ν (continuous_scH σ ht) (continuous_scH_symm σ ht)
  refine ⟨Measure.addHaarScalarFactor (ν.map (scH σ n ht)) ν, fun A hA => ?_⟩
  have hk := Measure.isAddLeftInvariant_eq_smul (ν.map (scH σ n ht)) ν
  have := congrArg (fun μ : Measure (HermR (Fv F v) σ n) => μ A) hk
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  rw [← Measure.map_apply (continuous_scH σ ht).measurable hA]
  exact this

end PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth
open scoped TensorProduct Matrix ENNReal NNReal

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h`. Use `haveI : lam.IsAddHaarMeasure := h.haar`. Use `haveI : νv.IsAddHaarMeasure := h.sdH.1`. Take `⟨ϖ, hϖ0, hϖ1⟩` from `exists_norm_lt_one (F := F) v`. Establish `hϖne : ϖ ≠ 0` using `norm_pos_iff.1 hϖ0`.

Take `⟨R₀, hR₀, hKL⟩` from `exists_lattice_norm_ge_pow hϖ0 hϖ1 lam h.co₁ h.co₂`. Take `⟨k, hk⟩` from `exists_scale σ n νv hϖne`. Take `⟨C, hC⟩` from `uu_bound h`. Establish `hnu1` using `lattice_norm_ge_one h`. Use `set q : ℝ := ‖ϖ‖⁻¹ with hq`.

Establish `hq1 : 1 < q` using `(one_lt_inv₀ hϖ0).2 hϖ1`. Use `set V := νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀} with hVdef`. Establish `hV : V ≠ ⊤` using `(isCompact_ballH R₀).measure_lt_top.ne`. Establish `hstep : ∀ r : ℝ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r * q} = k * νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r}`. Introduce `r`.

Rewrite using `[← hk _ (measurableSet_ballH r)]`. Use `congrArg νv (Set.ext fun b => ?_)` and prove the remaining obligations. Use `show nM v b.1 ≤ r * q ↔ nM v (scH σ n hϖne b).1 ≤ r`. Establish `hs : nM v (scH σ n hϖne b).1 = ‖ϖ‖ * nM v b.1`. Rewrite using `[scH_val]`.

Conclude with `nM_smul ϖ b.1`. Rewrite using `[hs, hq, ← div_eq_mul_inv, le_div_iff₀ hϖ0, mul_comm]`. Establish `hball : ∀ j : ℕ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀ * q ^ j} = (k : ℝ≥0∞) ^ j * V`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp only [pow_zero, mul_one, one_mul]`. Conclude with `hVdef.symm`. Consider the case `succ j ih => rw [pow_succ, ← mul_assoc, hstep, ih, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `set σs : ℝ := Real.logb 2 (2 * k + 2) with hσs`.

Establish `hσs0 : 0 ≤ σs` using `Real.logb_nonneg one_lt_two (by linarith [NNReal.coe_nonneg k])`. Use `⟨((M : ℝ) - n) / 2 + σs, fun z hz => ?_⟩` and prove the remaining obligations. Use `set s : ℝ := z.re - ((M : ℝ) - n) / 2 with hs`. Establish `hsσ : σs < s` using `by rw [hs]; linarith`. Establish `hs0 : 0 ≤ s` using `by linarith`.

Establish `h2s : 2 * (k : ℝ) + 2 ≤ 2 ^ s`. Combine the equalities or inequalities in the displayed calculation. Use `set r : ℝ := (2 : ℝ) ^ (-s) with hrdef`. Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hrk : r * k < 1`.

Establish `h2pos : 0 < (2 : ℝ) ^ s` using `by positivity`. Rewrite using `[hrdef, Real.rpow_neg zero_le_two, inv_mul_eq_div, div_lt_one h2pos]`. Combine the linear relations using `[NNReal.coe_nonneg k]`. Use `set H : HermR (Fv F v) σ n → ℝ := fun b => nu2 lam L₁ L₂ b.1 ^ (-s) with hH`. Establish `hHc : Continuous H` using `(continuous_lattice_norm h).rpow_const fun b => Or.inl (by linarith [hnu1 b])`.

Establish `hH0 : ∀ b, 0 ≤ H b` using `fun b => Real.rpow_nonneg (by linarith [hnu1 b]) _`. Establish `hH1 : ∀ b, H b ≤ 1` using `fun b => Real.rpow_le_one_of_one_le_of_nonpos (hnu1 b) (by linarith)`. Use `set A : ℕ → Set (HermR (Fv F v) σ n) := fun j => {b | R₀ * q ^ j ≤ nM v b.1 ∧ nM v b.1 ≤ R₀ * q ^ (j + 1)} with hA`. Establish `hm : Measurable fun b : HermR (Fv F v) σ n => nM v b.1` using `(show Continuous fun b : HermR (Fv F v) σ n => nM v b.1 from continuous_nM.comp continuous_subtype_val).measurable`. Establish `hAm : ∀ j, MeasurableSet (A j)` using `fun j => (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)`.

Establish `hHA : ∀ j, ∀ b ∈ A j, H b ≤ r ^ j`. Introduce `j b hb`. Establish `h2 : (2 : ℝ) ^ j ≤ nu2 lam L₁ L₂ b.1` using `hKL j b.1 (hnu1 b) hb.1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hrdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_mul zero_le_two, mul_comm]`.

Establish `hcov : (Set.univ : Set (HermR (Fv F v) σ n)) ⊆ {b | nM v b.1 ≤ R₀} ∪ ⋃ j, A j`. Introduce `b _`. Distinguish the cases in `hb : nM v b.1 ≤ R₀`. Conclude with `Or.inl hb`. Use `push_neg at hb`.

Take `⟨j, hj1, hj2⟩` from `exists_nat_pow_near (x := nM v b.1 / R₀) (y := q) ((one_le_div hR₀).2 hb.le) hq1`. Use `Or.inr (Set.mem_iUnion.2 ⟨j, ?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(le_div_iff₀ hR₀).1 hj1`. Rewrite using `[mul_comm]`.

Conclude with `((div_lt_iff₀ hR₀).1 hj2).le`. Establish `hBint : ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv ≤ V`. Combine the equalities or inequalities in the displayed calculation. Establish `hAint : ∀ j, ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv ≤ (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j`. Introduce `j`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hball (j + 1)]`. Conclude with `measure_mono fun b hb => hb.2`. Use `_ = (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := by`. Rewrite using `[ENNReal.ofReal_pow hr0, ENNReal.ofReal_mul hr0, ENNReal.ofReal_coe_nnreal]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hx : ENNReal.ofReal (r * k) < 1` using `by rw [ENNReal.ofReal_lt_one]; exact hrk`. Establish `hHint : Integrable H νv`. Use `⟨hHc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Eventually.of_forall hH0)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_geometric]`. Use `_ < ⊤ := ENNReal.add_lt_top.2 ⟨hV.lt_top, ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hV.lt_top) (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hx))⟩`. Establish `hf : whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z = fun b => ((nu2 lam L₁ L₂ b.1 : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) * uu σ J ψ v μv Φv T b`. Use function extensionality and compare the values at `b`.

Simplify using `only [whI, uu, mul_assoc]`. Rewrite using `[hf]`. Use `(hHint.const_mul C).mono' ?_ (Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Conclude with `(((Complex.continuous_ofReal.comp (continuous_lattice_norm h)).cpow continuous_const fun b => Complex.ofReal_mem_slitPlane.2 (by linarith [hnu1 b])).mul (continuous_uu h)).aestronglyMeasurable`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hnu1 b])]`.

Establish `hre : (-(z - ((M : ℂ) - n) / 2)).re = -s`. Rewrite using `[hs]`. Simplify using `[Complex.sub_re, Complex.div_ofNat_re]`. Rewrite using `[hre, mul_comm C]`. Conclude with `mul_le_mul_of_nonneg_left (hC b) (hH0 b)`.
-/
theorem convP : ConvP := by
  intro F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
  haveI : lam.IsAddHaarMeasure := h.haar
  haveI : νv.IsAddHaarMeasure := h.sdH.1
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_norm_lt_one (F := F) v
  have hϖne : ϖ ≠ 0 := norm_pos_iff.1 hϖ0
  obtain ⟨R₀, hR₀, hKL⟩ := exists_lattice_norm_ge_pow hϖ0 hϖ1 lam h.co₁ h.co₂
  obtain ⟨k, hk⟩ := exists_scale σ n νv hϖne
  obtain ⟨C, hC⟩ := uu_bound h
  have hnu1 := lattice_norm_ge_one h
  set q : ℝ := ‖ϖ‖⁻¹ with hq
  have hq1 : 1 < q := (one_lt_inv₀ hϖ0).2 hϖ1
  set V := νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀} with hVdef
  have hV : V ≠ ⊤ := (isCompact_ballH R₀).measure_lt_top.ne
  have hstep : ∀ r : ℝ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r * q} =
      k * νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r} := by
    intro r
    rw [← hk _ (measurableSet_ballH r)]
    refine congrArg νv (Set.ext fun b => ?_)
    show nM v b.1 ≤ r * q ↔ nM v (scH σ n hϖne b).1 ≤ r
    have hs : nM v (scH σ n hϖne b).1 = ‖ϖ‖ * nM v b.1 := by
      rw [scH_val]; exact nM_smul ϖ b.1
    rw [hs, hq, ← div_eq_mul_inv, le_div_iff₀ hϖ0, mul_comm]
  have hball : ∀ j : ℕ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀ * q ^ j} = (k : ℝ≥0∞) ^ j * V := by
    intro j
    induction j with
    | zero => simp only [pow_zero, mul_one, one_mul]; exact hVdef.symm
    | succ j ih => rw [pow_succ, ← mul_assoc, hstep, ih, pow_succ]; ring
  set σs : ℝ := Real.logb 2 (2 * k + 2) with hσs
  have hσs0 : 0 ≤ σs := Real.logb_nonneg one_lt_two (by linarith [NNReal.coe_nonneg k])
  refine ⟨((M : ℝ) - n) / 2 + σs, fun z hz => ?_⟩
  set s : ℝ := z.re - ((M : ℝ) - n) / 2 with hs
  have hsσ : σs < s := by rw [hs]; linarith
  have hs0 : 0 ≤ s := by linarith
  have h2s : 2 * (k : ℝ) + 2 ≤ 2 ^ s := by
    calc 2 * (k : ℝ) + 2 = 2 ^ σs := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ 2 ^ s := Real.rpow_le_rpow_of_exponent_le one_le_two hsσ.le
  set r : ℝ := (2 : ℝ) ^ (-s) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrk : r * k < 1 := by
    have h2pos : 0 < (2 : ℝ) ^ s := by positivity
    rw [hrdef, Real.rpow_neg zero_le_two, inv_mul_eq_div, div_lt_one h2pos]
    linarith [NNReal.coe_nonneg k]
  set H : HermR (Fv F v) σ n → ℝ := fun b => nu2 lam L₁ L₂ b.1 ^ (-s) with hH
  have hHc : Continuous H := (continuous_lattice_norm h).rpow_const fun b => Or.inl (by linarith [hnu1 b])
  have hH0 : ∀ b, 0 ≤ H b := fun b => Real.rpow_nonneg (by linarith [hnu1 b]) _
  have hH1 : ∀ b, H b ≤ 1 := fun b => Real.rpow_le_one_of_one_le_of_nonpos (hnu1 b) (by linarith)
  set A : ℕ → Set (HermR (Fv F v) σ n) :=
    fun j => {b | R₀ * q ^ j ≤ nM v b.1 ∧ nM v b.1 ≤ R₀ * q ^ (j + 1)} with hA
  have hm : Measurable fun b : HermR (Fv F v) σ n => nM v b.1 :=
    (show Continuous fun b : HermR (Fv F v) σ n => nM v b.1 from continuous_nM.comp continuous_subtype_val).measurable
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hHA : ∀ j, ∀ b ∈ A j, H b ≤ r ^ j := by
    intro j b hb
    have h2 : (2 : ℝ) ^ j ≤ nu2 lam L₁ L₂ b.1 := hKL j b.1 (hnu1 b) hb.1
    calc H b ≤ ((2 : ℝ) ^ j) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
      _ = r ^ j := by
        rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
          ← Real.rpow_mul zero_le_two, mul_comm]
  have hcov : (Set.univ : Set (HermR (Fv F v) σ n)) ⊆ {b | nM v b.1 ≤ R₀} ∪ ⋃ j, A j := by
    intro b _
    by_cases hb : nM v b.1 ≤ R₀
    · exact Or.inl hb
    · push_neg at hb
      obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := nM v b.1 / R₀) (y := q) ((one_le_div hR₀).2 hb.le) hq1
      refine Or.inr (Set.mem_iUnion.2 ⟨j, ?_, ?_⟩)
      · rw [mul_comm]; exact (le_div_iff₀ hR₀).1 hj1
      · rw [mul_comm]; exact ((div_lt_iff₀ hR₀).1 hj2).le
  have hBint : ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv ≤ V := by
    calc _ ≤ ∫⁻ _ in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, 1 ∂νv :=
          lintegral_mono fun b => ENNReal.ofReal_le_one.2 (hH1 b)
      _ = V := by rw [setLIntegral_const, one_mul]
  have hAint : ∀ j, ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv ≤ (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := by
    intro j
    calc ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv ≤ ∫⁻ _ in A j, ENNReal.ofReal (r ^ j) ∂νv :=
          lintegral_mono_ae (ae_restrict_of_forall_mem (hAm j) fun b hb => ENNReal.ofReal_le_ofReal (hHA j b hb))
      _ = ENNReal.ofReal (r ^ j) * νv (A j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (r ^ j) * ((k : ℝ≥0∞) ^ (j + 1) * V) := by
          gcongr
          rw [← hball (j + 1)]
          exact measure_mono fun b hb => hb.2
      _ = (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := by
          rw [ENNReal.ofReal_pow hr0, ENNReal.ofReal_mul hr0, ENNReal.ofReal_coe_nnreal]; ring
  have hx : ENNReal.ofReal (r * k) < 1 := by rw [ENNReal.ofReal_lt_one]; exact hrk
  have hHint : Integrable H νv := by
    refine ⟨hHc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hH0)]
    calc ∫⁻ b, ENNReal.ofReal (H b) ∂νv = ∫⁻ b in Set.univ, ENNReal.ofReal (H b) ∂νv := by rw [Measure.restrict_univ]
      _ ≤ ∫⁻ b in {b | nM v b.1 ≤ R₀} ∪ ⋃ j, A j, ENNReal.ofReal (H b) ∂νv := lintegral_mono_set hcov
      _ ≤ ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv +
            ∫⁻ b in ⋃ j, A j, ENNReal.ofReal (H b) ∂νv := lintegral_union_le _ _ _
      _ ≤ ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv +
            ∑' j, ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv := add_le_add le_rfl (lintegral_iUnion_le _ _)
      _ ≤ V + ∑' j, (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := add_le_add hBint (ENNReal.tsum_le_tsum hAint)
      _ = V + (k : ℝ≥0∞) * V * (1 - ENNReal.ofReal (r * k))⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hV.lt_top, ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.coe_lt_top hV.lt_top) (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hx))⟩
  have hf : whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z =
      fun b => ((nu2 lam L₁ L₂ b.1 : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) * uu σ J ψ v μv Φv T b := by
    funext b; simp only [whI, uu, mul_assoc]
  rw [hf]
  refine (hHint.const_mul C).mono' ?_ (Eventually.of_forall fun b => ?_)
  · exact (((Complex.continuous_ofReal.comp (continuous_lattice_norm h)).cpow continuous_const fun b =>
      Complex.ofReal_mem_slitPlane.2 (by linarith [hnu1 b])).mul (continuous_uu h)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hnu1 b])]
    have hre : (-(z - ((M : ℂ) - n) / 2)).re = -s := by
      rw [hs]; simp [Complex.sub_re, Complex.div_ofNat_re]
    rw [hre, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC b) (hH0 b)

end PositivityTheory.SiegelWeilFormula.SwLocFin
