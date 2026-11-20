import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `haveI : CharZero Ω := RingHom.charZero ι`. Establish `hmap : (g.map (algebraMap ℚ Ω)).map ι = g.map (algebraMap ℚ (PadicAlgCl p))`. Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Conclude with `RingHom.ext_rat _ _`.

Establish `hroot : ((g.map (algebraMap ℚ Ω)).map ι).IsRoot b`. Rewrite using `[hmap, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]`. Conclude with `hb`. Conclude with `Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) (Polynomial.map_ne_zero hg) hroot`.
-/
theorem mem_range_of_aeval_rat_eq_zero (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] {g : Polynomial ℚ} (hg : g ≠ 0)
    {b : PadicAlgCl p} (hb : Polynomial.aeval b g = 0) : b ∈ ι.range := by
  classical
  haveI : CharZero Ω := RingHom.charZero ι
  have hmap : (g.map (algebraMap ℚ Ω)).map ι = g.map (algebraMap ℚ (PadicAlgCl p)) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hroot : ((g.map (algebraMap ℚ Ω)).map ι).IsRoot b := by
    rw [hmap, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hb
  exact Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) (Polynomial.map_ne_zero hg) hroot

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `G hG hd b`. Establish `hdeg : G.degree ≠ 0`. Rewrite using `[Polynomial.degree_eq_natDegree hG.ne_zero, hd]`.

Simplify using the standard rewrite rules. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root G hdeg`. Use `⟨α, hα, ?_⟩` and prove the remaining obligations. Establish `hQ` using `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα`. Establish `hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic` using `(Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)`.

Establish `hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = 0`. Establish `h` using `(Polynomial.monic_X_sub_C α).natDegree_mul hQm`. Rewrite `h` using `[hQ, hd, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `hQ1 : G /ₘ (Polynomial.X - Polynomial.C α) = 1` using `by first`.

Consider the case `exact Polynomial.eq_one_of_monic_natDegree_zero hQm hQd`. Consider the case `exact hQm.natDegree_eq_zero.mp hQd`. Consider the case `exact (Polynomial.Monic.natDegree_eq_zero_iff_eq_one hQm).mp hQd`. Establish `he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b` using `by conv_lhs => rw [← hQ]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`.

Rewrite using `[he, hQ1, Polynomial.eval_one, mul_one, pow_one]`. Consider the case `succ n ih`. Introduce `G hG hd b`. Establish `hdeg : G.degree ≠ 0`. Rewrite using `[Polynomial.degree_eq_natDegree hG.ne_zero, hd]`.

Conclude with `Nat.succ_ne_zero (n + 1)` after adjusting the coercions. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root G hdeg`. Establish `hQ` using `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα`. Establish `hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic` using `(Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)`. Establish `hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n + 1`.

Establish `h` using `(Polynomial.monic_X_sub_C α).natDegree_mul hQm`. Rewrite `h` using `[hQ, hd, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b` using `by conv_lhs => rw [← hQ]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`.

Take `⟨β, hβ, hb⟩` from `ih _ hQm hQd b`. Establish `hβG : G.IsRoot β`. Rewrite `hβ`, the goal using `[Polynomial.IsRoot.def]`. Rewrite using `[← hQ, Polynomial.eval_mul, hβ, mul_zero]`. Establish `hGb : ‖G.eval b‖ = ‖b - α‖ * ‖(G /ₘ (Polynomial.X - Polynomial.C α)).eval b‖`.

Rewrite using `[he, norm_mul]`. Break down `le_total ‖b - α‖ ‖b - β‖ with h | h` into its components or cases. Use `⟨α, hα, ?_⟩` and prove the remaining obligations. Rewrite using `[hGb, pow_succ']`. Conclude with `mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) h _).trans hb) (norm_nonneg _)`.

Use `⟨β, hβG, ?_⟩` and prove the remaining obligations. Rewrite using `[hGb, pow_succ']`. Conclude with `mul_le_mul h hb (by positivity) (norm_nonneg _)`.
-/
private theorem exists_root_norm_sub_pow_le_eval {K : Type*} [NormedField K] [IsAlgClosed K] (n : ℕ) :
    ∀ G : Polynomial K, G.Monic → G.natDegree = n + 1 → ∀ b : K,
      ∃ β, G.IsRoot β ∧ ‖b - β‖ ^ (n + 1) ≤ ‖G.eval b‖ := by
  induction n with
  | zero =>
    intro G hG hd b
    have hdeg : G.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hG.ne_zero, hd]
      simp
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hdeg
    refine ⟨α, hα, ?_⟩
    have hQ := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα
    have hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      (Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)
    have hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = 0 := by
      have h := (Polynomial.monic_X_sub_C α).natDegree_mul hQm
      rw [hQ, hd, Polynomial.natDegree_X_sub_C] at h
      omega
    have hQ1 : G /ₘ (Polynomial.X - Polynomial.C α) = 1 := by
      first
        | exact Polynomial.eq_one_of_monic_natDegree_zero hQm hQd
        | exact hQm.natDegree_eq_zero.mp hQd
        | exact (Polynomial.Monic.natDegree_eq_zero_iff_eq_one hQm).mp hQd
    have he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b := by
      conv_lhs => rw [← hQ]
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [he, hQ1, Polynomial.eval_one, mul_one, pow_one]
  | succ n ih =>
    intro G hG hd b
    have hdeg : G.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hG.ne_zero, hd]
      exact_mod_cast Nat.succ_ne_zero (n + 1)
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hdeg
    have hQ := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα
    have hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      (Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)
    have hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n + 1 := by
      have h := (Polynomial.monic_X_sub_C α).natDegree_mul hQm
      rw [hQ, hd, Polynomial.natDegree_X_sub_C] at h
      omega
    have he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b := by
      conv_lhs => rw [← hQ]
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    obtain ⟨β, hβ, hb⟩ := ih _ hQm hQd b
    have hβG : G.IsRoot β := by
      rw [Polynomial.IsRoot.def] at hβ ⊢
      rw [← hQ, Polynomial.eval_mul, hβ, mul_zero]
    have hGb : ‖G.eval b‖ = ‖b - α‖ * ‖(G /ₘ (Polynomial.X - Polynomial.C α)).eval b‖ := by
      rw [he, norm_mul]
    rcases le_total ‖b - α‖ ‖b - β‖ with h | h
    · refine ⟨α, hα, ?_⟩
      rw [hGb, pow_succ']
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) h _).trans hb) (norm_nonneg _)
    · refine ⟨β, hβG, ?_⟩
      rw [hGb, pow_succ']
      exact mul_le_mul h hb (by positivity) (norm_nonneg _)

/- English proof (translation)
Rewrite using `[Metric.denseRange_iff]`. Introduce `b ε hε`. Establish `hint : IsIntegral ℚ_[p] b` using `(Algebra.IsAlgebraic.isAlgebraic b).isIntegral`. Establish `hfm : (minpoly ℚ_[p] b).Monic` using `minpoly.monic hint`. Establish `hpos : 0 < (minpoly ℚ_[p] b).natDegree` using `minpoly.natDegree_pos hint`.

Take `⟨n, hn⟩ : ∃ n, (minpoly ℚ_[p] b).natDegree = n + 1` from `⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩`. Establish `hFb : ((minpoly ℚ_[p] b).map (algebraMap ℚ_[p] (PadicAlgCl p))).eval b = 0`. Rewrite using `[Polynomial.eval_map, ← Polynomial.aeval_def]`. Conclude with `minpoly.aeval ℚ_[p] b`. Use `set f := minpoly ℚ_[p] b with hf`.

Use `set M : ℝ := max 1 ‖b‖ with hMdef`. Establish `hM : 1 ≤ M` using `le_max_left _ _`. Establish `hbM : ‖b‖ ≤ M` using `le_max_right _ _`. Establish `hMp : 0 < M` using `by linarith`. Use `set δ : ℝ := ε ^ (n + 1) / (2 * ((n : ℝ) + 2) * M ^ (n + 1)) with hδdef`.

Establish `hδ : 0 < δ` using `by positivity`. Use `choose q hq using fun i : ℕ => Padic.rat_dense p (f.coeff i) hδ`. Use `set s : Polynomial ℚ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (q i) * Polynomial.X ^ i with hs`. Establish `hsdeg : s.degree < ((n + 1 : ℕ) : WithBot ℕ)`. Rewrite using `[hs, Finset.sum_range]`.

Conclude with `Polynomial.degree_sum_fin_lt _`. Use `set g : Polynomial ℚ := Polynomial.X ^ (n + 1) + s with hg`. Establish `hgm : g.Monic` using `Polynomial.monic_X_pow_add hsdeg`. Establish `hgn : g.natDegree = n + 1`. Rewrite using `[hg, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact hsdeg), Polynomial.natDegree_X_pow]`.

Use `set G := g.map (algebraMap ℚ (PadicAlgCl p)) with hG`. Use `set F := f.map (algebraMap ℚ_[p] (PadicAlgCl p)) with hF`. Establish `hGm : G.Monic` using `hgm.map _`. Establish `hGn : G.natDegree = n + 1` using `by rw [hG, Polynomial.natDegree_map]; exact hgn`. Establish `hDn : (G - F).natDegree < n + 2`.

Use `lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_` and prove the remaining obligations. Rewrite using `[hGn, hF, Polynomial.natDegree_map, hn, max_self]`. Use linear arithmetic over natural numbers and integers. Establish `hGb : G.eval b = ∑ i ∈ Finset.range (n + 2), (G - F).coeff i * b ^ i`. Rewrite using `[← Polynomial.eval_eq_sum_range' hDn, Polynomial.eval_sub, hFb, sub_zero]`.

Establish `hterm : ∀ i ∈ Finset.range (n + 2), ‖(G - F).coeff i * b ^ i‖ ≤ δ * M ^ (n + 1)`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[norm_mul, norm_pow]`. Establish `hbi : ‖b‖ ^ i ≤ M ^ (n + 1)` using `(pow_le_pow_left₀ (norm_nonneg _) hbM i).trans (pow_le_pow_right₀ hM (by omega))`.

Establish `hc : ‖(G - F).coeff i‖ ≤ δ`. Rewrite using `[Polynomial.coeff_sub, hG, hF, Polynomial.coeff_map, Polynomial.coeff_map]`. Break down `Nat.lt_or_ge i (n + 1) with hi' | hi'` into its components or cases. Establish `hgc : g.coeff i = q i`. Rewrite using `[hg, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add, hs, Polynomial.finset_sum_coeff]`.

Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hi')]`. Rewrite using `[hgc, eq_ratCast (algebraMap ℚ (PadicAlgCl p)), ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]`. Conclude with `(hq i).le`. Establish `hi2 : i = n + 1` using `by omega`.

Establish `hg1 : g.coeff i = 1`. Establish `h` using `hgm.coeff_natDegree`. Rewrite `h` using `[hgn]`. Rewrite using `[hi2, h]`. Establish `hf1 : f.coeff i = 1`.

Establish `h` using `hfm.coeff_natDegree`. Rewrite `h` using `[hn]`. Rewrite using `[hi2, h]`. Rewrite using `[hg1, hf1, map_one, map_one, sub_self, norm_zero]`. Conclude with `hδ.le`.

Conclude with `mul_le_mul hc hbi (by positivity) hδ.le`. Establish `hGlt : ‖G.eval b‖ < ε ^ (n + 1)`. Rewrite using `[hGb]`. Use `lt_of_le_of_lt (norm_sum_le _ _) ?_` and prove the remaining obligations. Use `lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `e : ((n + 2 : ℕ) : ℝ) * (δ * M ^ (n + 1)) = ε ^ (n + 1) / 2`. Rewrite using `[hδdef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Establish `: 0 < ε ^ (n + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨β, hβ, hβb⟩` from `exists_root_norm_sub_pow_le_eval n G hGm hGn b`. Establish `hβε : ‖b - β‖ < ε` using `lt_of_pow_lt_pow_left₀ (n + 1) hε.le (lt_of_le_of_lt hβb hGlt)`.

Establish `hβr : β ∈ ι.range` using `mem_range_of_aeval_rat_eq_zero ι hgm.ne_zero (by`. Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map]`. Conclude with `hβ)`. Take `⟨y, hy⟩` from `RingHom.mem_range.mp hβr`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[dist_eq_norm, hy]`. Conclude with `hβε`.
-/
theorem denseRange_of_isAlgClosed (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] : DenseRange ι := by
  classical
  rw [Metric.denseRange_iff]
  intro b ε hε
  have hint : IsIntegral ℚ_[p] b := (Algebra.IsAlgebraic.isAlgebraic b).isIntegral
  have hfm : (minpoly ℚ_[p] b).Monic := minpoly.monic hint
  have hpos : 0 < (minpoly ℚ_[p] b).natDegree := minpoly.natDegree_pos hint
  obtain ⟨n, hn⟩ : ∃ n, (minpoly ℚ_[p] b).natDegree = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hFb : ((minpoly ℚ_[p] b).map (algebraMap ℚ_[p] (PadicAlgCl p))).eval b = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[p] b
  set f := minpoly ℚ_[p] b with hf
  set M : ℝ := max 1 ‖b‖ with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hbM : ‖b‖ ≤ M := le_max_right _ _
  have hMp : 0 < M := by linarith
  set δ : ℝ := ε ^ (n + 1) / (2 * ((n : ℝ) + 2) * M ^ (n + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  choose q hq using fun i : ℕ => Padic.rat_dense p (f.coeff i) hδ
  set s : Polynomial ℚ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (q i) * Polynomial.X ^ i with hs
  have hsdeg : s.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [hs, Finset.sum_range]
    exact Polynomial.degree_sum_fin_lt _
  set g : Polynomial ℚ := Polynomial.X ^ (n + 1) + s with hg
  have hgm : g.Monic := Polynomial.monic_X_pow_add hsdeg
  have hgn : g.natDegree = n + 1 := by
    rw [hg, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact hsdeg),
      Polynomial.natDegree_X_pow]
  set G := g.map (algebraMap ℚ (PadicAlgCl p)) with hG
  set F := f.map (algebraMap ℚ_[p] (PadicAlgCl p)) with hF
  have hGm : G.Monic := hgm.map _
  have hGn : G.natDegree = n + 1 := by rw [hG, Polynomial.natDegree_map]; exact hgn
  have hDn : (G - F).natDegree < n + 2 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
    rw [hGn, hF, Polynomial.natDegree_map, hn, max_self]
    omega
  have hGb : G.eval b = ∑ i ∈ Finset.range (n + 2), (G - F).coeff i * b ^ i := by
    rw [← Polynomial.eval_eq_sum_range' hDn, Polynomial.eval_sub, hFb, sub_zero]
  have hterm : ∀ i ∈ Finset.range (n + 2), ‖(G - F).coeff i * b ^ i‖ ≤ δ * M ^ (n + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hbi : ‖b‖ ^ i ≤ M ^ (n + 1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hbM i).trans (pow_le_pow_right₀ hM (by omega))
    have hc : ‖(G - F).coeff i‖ ≤ δ := by
      rw [Polynomial.coeff_sub, hG, hF, Polynomial.coeff_map, Polynomial.coeff_map]
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hgc : g.coeff i = q i := by
          rw [hg, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add, hs,
            Polynomial.finset_sum_coeff]
          simp only [Polynomial.coeff_C_mul_X_pow]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hi')]
        rw [hgc, eq_ratCast (algebraMap ℚ (PadicAlgCl p)), ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)),
          ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
        exact (hq i).le
      · have hi2 : i = n + 1 := by omega
        have hg1 : g.coeff i = 1 := by
          have h := hgm.coeff_natDegree
          rw [hgn] at h
          rw [hi2, h]
        have hf1 : f.coeff i = 1 := by
          have h := hfm.coeff_natDegree
          rw [hn] at h
          rw [hi2, h]
        rw [hg1, hf1, map_one, map_one, sub_self, norm_zero]
        exact hδ.le
    exact mul_le_mul hc hbi (by positivity) hδ.le
  have hGlt : ‖G.eval b‖ < ε ^ (n + 1) := by
    rw [hGb]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ((n + 2 : ℕ) : ℝ) * (δ * M ^ (n + 1)) = ε ^ (n + 1) / 2 := by
      rw [hδdef]
      push_cast
      field_simp
    rw [e]
    have : 0 < ε ^ (n + 1) := by positivity
    linarith
  obtain ⟨β, hβ, hβb⟩ := exists_root_norm_sub_pow_le_eval n G hGm hGn b
  have hβε : ‖b - β‖ < ε := lt_of_pow_lt_pow_left₀ (n + 1) hε.le (lt_of_le_of_lt hβb hGlt)
  have hβr : β ∈ ι.range := mem_range_of_aeval_rat_eq_zero ι hgm.ne_zero (by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hβ)
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp hβr
  refine ⟨y, ?_⟩
  rw [dist_eq_norm, hy]
  exact hβε

/- English proof (translation)
Set `b` to `Module.finBasis ℚ F`. Set `f` to `ι.comp (algebraMap F Ω)`. Establish `hle : Kloc F ι ≤ IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i))`. Apply `IntermediateField.adjoin_le_iff.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[← b.sum_repr y, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul, Rat.smul_def, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p))]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`. Use `haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i))) := IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`.

Conclude with `FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)`.
-/
theorem finiteDimensional_Kloc (ι : Ω →+* PadicAlgCl p) : FiniteDimensional ℚ_[p] (Kloc F ι) := by
  classical
  let b := Module.finBasis ℚ F
  let f := ι.comp (algebraMap F Ω)
  have hle : Kloc F ι ≤ IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i)) := by
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

/- English proof (translation)
Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem isAlgClosure_Kloc (ι : Ω →+* PadicAlgCl p) : IsAlgClosure (Kloc F ι) (PadicAlgCl p) := by
  exact ⟨inferInstance, inferInstance⟩

variable (F) in
include F in

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Conclude with `denseRange_of_isAlgClosed ι`.
-/
theorem denseRange (ι : Ω →+* PadicAlgCl p) : DenseRange ι := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  exact denseRange_of_isAlgClosed ι

/- English proof (translation)
Set `f : F →+* PadicAlgCl p` to `ι.comp (algebraMap F Ω)`. Set `S : Subfield (PadicAlgCl p)` to `f.fieldRange.topologicalClosure`. Establish `hQ : ∀ c : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) c ∈ S`. Introduce `c`. Use `show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))`.

Use `Metric.mem_closure_iff.2 fun δ hδ => ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `Padic.rat_dense p c hδ`. Use `⟨f q, RingHom.mem_fieldRange.2 ⟨q, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, map_ratCast f, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← map_sub]`. Use `hq using 1` and compare the differences between its conclusion and the goal.

Conclude with `PadicAlgCl.norm_extends ..`. Set `L : IntermediateField ℚ_[p] (PadicAlgCl p)` to `S.toIntermediateField hQ`. Establish `hle : Kloc F ι ≤ L` using `IntermediateField.adjoin_le_iff.2 (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))`.

Conclude with `subset_closure (RingHom.mem_fieldRange.2 ⟨y, rfl⟩))`. Establish `hx : (x : PadicAlgCl p) ∈ closure (f.fieldRange : Set (PadicAlgCl p))` using `hle x.2`. Take `⟨b, hb1, hb⟩` from `Metric.mem_closure_iff.1 hx ε hε`. Take `⟨y, rfl⟩` from `RingHom.mem_fieldRange.1 hb1`. Conclude with `⟨y, by rw [← dist_eq_norm]; exact hb⟩`.
-/
theorem exists_norm_sub_lt (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : F, ‖(x : PadicAlgCl p) - ι (algebraMap F Ω y)‖ < ε := by
  classical
  let f : F →+* PadicAlgCl p := ι.comp (algebraMap F Ω)
  let S : Subfield (PadicAlgCl p) := f.fieldRange.topologicalClosure
  have hQ : ∀ c : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) c ∈ S := by
    intro c
    show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))
    refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    obtain ⟨q, hq⟩ := Padic.rat_dense p c hδ
    refine ⟨f q, RingHom.mem_fieldRange.2 ⟨q, rfl⟩, ?_⟩
    rw [dist_eq_norm, map_ratCast f, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← map_sub]
    convert hq using 1
    exact PadicAlgCl.norm_extends ..
  let L : IntermediateField ℚ_[p] (PadicAlgCl p) := S.toIntermediateField hQ
  have hle : Kloc F ι ≤ L := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨y, rfl⟩
    show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))
    exact subset_closure (RingHom.mem_fieldRange.2 ⟨y, rfl⟩))
  have hx : (x : PadicAlgCl p) ∈ closure (f.fieldRange : Set (PadicAlgCl p)) := hle x.2
  obtain ⟨b, hb1, hb⟩ := Metric.mem_closure_iff.1 hx ε hε
  obtain ⟨y, rfl⟩ := RingHom.mem_fieldRange.1 hb1
  exact ⟨y, by rw [← dist_eq_norm]; exact hb⟩

/- English proof (translation)
Conclude with `(spectralNorm_eq_of_equiv σ x).symm`.
-/
theorem norm_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  exact (spectralNorm_eq_of_equiv σ x).symm

/- English proof (translation)
Conclude with `norm_map (σ.restrictScalars ℚ_[p]) x`.
-/
theorem norm_map_GK (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  exact norm_map (σ.restrictScalars ℚ_[p]) x

end ReciprocityTheory.Neutral.Cmp
