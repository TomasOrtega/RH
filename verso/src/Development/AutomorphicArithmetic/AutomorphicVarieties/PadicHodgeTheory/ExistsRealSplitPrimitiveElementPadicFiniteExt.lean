import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumberFieldAdjoinEq

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField

namespace UpperTheory.V.RealGen

open Polynomial IntermediateField Filter Topology

private noncomputable def model (n : ℕ) : ℚ[X] :=
  ∏ i ∈ Finset.range n, (X - C ((i : ℚ) + 1 / 2))

end UpperTheory.V.RealGen

open Polynomial in
/- English proof (translation)
Unfold `UpperTheory.V.RealGen.model`. Rewrite using `[eval_prod, eval_prod, ← Finset.prod_mul_distrib]`. Establish `hmem : j ∈ Finset.range n` using `Finset.mem_range.mpr hj`. Rewrite using `[← Finset.mul_prod_erase _ _ hmem]`. Establish `hpos : 0 < ∏ i ∈ (Finset.range n).erase j, (eval (j : ℚ) (X - C ((i : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((i : ℚ) + 1 / 2)))`.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i hi`. Establish `hij : i ≠ j` using `Finset.ne_of_mem_erase hi`. Simplify using `only [eval_sub, eval_X, eval_C]`. Establish `h1 : (1 : ℚ) ≤ ((j : ℚ) - i) ^ 2`.

Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Establish `: (i : ℚ) + 1 ≤ j` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities. Establish `: (j : ℚ) + 1 ≤ i` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities. Establish `hneg : eval (j : ℚ) (X - C ((j : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((j : ℚ) + 1 / 2)) < 0`. Simplify using `only [eval_sub, eval_X, eval_C]`. Evaluate the numerical expressions. Conclude with `mul_neg_of_neg_of_pos hneg hpos`.
-/
private theorem model_eval_mul_eval_succ_neg (n j : ℕ) (hj : j < n) :
    (UpperTheory.V.RealGen.model n).eval (j : ℚ) * (UpperTheory.V.RealGen.model n).eval ((j : ℚ) + 1) < 0 := by
  unfold UpperTheory.V.RealGen.model
  rw [eval_prod, eval_prod, ← Finset.prod_mul_distrib]
  have hmem : j ∈ Finset.range n := Finset.mem_range.mpr hj
  rw [← Finset.mul_prod_erase _ _ hmem]
  have hpos : 0 < ∏ i ∈ (Finset.range n).erase j,
      (eval (j : ℚ) (X - C ((i : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((i : ℚ) + 1 / 2))) := by
    apply Finset.prod_pos
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [eval_sub, eval_X, eval_C]
    have h1 : (1 : ℚ) ≤ ((j : ℚ) - i) ^ 2 := by
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℚ) + 1 ≤ j := by exact_mod_cast h
        nlinarith
      · have : (j : ℚ) + 1 ≤ i := by exact_mod_cast h
        nlinarith
    nlinarith
  have hneg : eval (j : ℚ) (X - C ((j : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((j : ℚ) + 1 / 2)) < 0 := by
    simp only [eval_sub, eval_X, eval_C]
    norm_num
  exact mul_neg_of_neg_of_pos hneg hpos

open Polynomial in
/- English proof (translation)
Unfold `UpperTheory.V.RealGen.model`. Use `⟨monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _), ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]`. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]`.
-/
private theorem model_monic_natDegree (n : ℕ) :
    (UpperTheory.V.RealGen.model n).Monic ∧ (UpperTheory.V.RealGen.model n).natDegree = n := by
  unfold UpperTheory.V.RealGen.model
  refine ⟨monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _), ?_⟩
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

open Polynomial in
/- English proof (translation)
Use `set G := g.map (algebraMap ℚ ℝ) with hGdef`. Establish `hev : ∀ x : ℚ, G.eval (x : ℝ) = ((g.eval x : ℚ) : ℝ)`. Introduce `x`. Rewrite using `[hGdef, eval_map, show (x : ℝ) = algebraMap ℚ ℝ x from rfl, eval₂_at_apply]`. Both sides reduce to the same expression.

Establish `hroot : ∀ j : Fin n, ∃ x ∈ Set.Ioo (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1), G.eval x = 0`. Introduce `j`. Establish `hj` using `halt j j.2`. Establish `hcont : ContinuousOn (fun x => G.eval x) (Set.Icc (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1))` using `G.continuous.continuousOn`. Establish `h0 : (((j : ℕ) : ℝ)) ≤ ((j : ℕ) : ℝ) + 1` using `by linarith`.

Establish `e1 : G.eval (((j : ℕ) : ℝ)) = ((g.eval ((j : ℕ) : ℚ) : ℚ) : ℝ)`. Rewrite using `[← hev]`. Use `norm_cast`. Establish `e2 : G.eval (((j : ℕ) : ℝ) + 1) = ((g.eval (((j : ℕ) : ℚ) + 1) : ℚ) : ℝ)`. Rewrite using `[← hev]`.

Use `push_cast`. Both sides reduce to the same expression. Break down `mul_neg_iff.mp hj with ⟨ha, hb⟩ | ⟨ha, hb⟩` into its components or cases. Take `⟨x, hx, hx0⟩` from `intermediate_value_Ioo' h0 hcont (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ) + 1)) (G.eval (((j : ℕ) : ℝ))) from ⟨by rw [e2]; exact_mod_cast hb, by rw [e1]; exact_mod_cast ha⟩)`. Conclude with `⟨x, hx, hx0⟩`.

Take `⟨x, hx, hx0⟩` from `intermediate_value_Ioo h0 hcont (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ))) (G.eval (((j : ℕ) : ℝ) + 1)) from ⟨by rw [e1]; exact_mod_cast ha, by rw [e2]; exact_mod_cast hb⟩)`. Conclude with `⟨x, hx, hx0⟩`. Use `choose r hr hr0 using hroot`. Establish `hinj : Function.Injective r`. Introduce `a b hab`.

Establish `ha` using `hr a`. Establish `hb` using `hr b`. Rewrite `ha` using `[hab]`. Apply `Fin.ext` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`.

Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `: ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast h`. Combine the linear relations using `[ha.2, hb.1]`. Establish `: ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ)` using `by exact_mod_cast h`. Combine the linear relations using `[ha.1, hb.2]`.

Establish `hG0 : G ≠ 0` using `(hmon.map (algebraMap ℚ ℝ)).ne_zero`. Establish `hsub : Finset.univ.image r ⊆ G.roots.toFinset`. Introduce `x hx`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp hx`. Rewrite using `[Multiset.mem_toFinset, mem_roots hG0]`.

Conclude with `hr0 j`. Establish `hcard : n ≤ G.roots.card`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_image_of_injective _ hinj]`. Simplify using the standard rewrite rules.

Use `_ ≤ G.roots.toFinset.card := Finset.card_le_card hsub`. Use `_ ≤ G.roots.card := Multiset.toFinset_card_le _`. Establish `hdG : G.natDegree = n`. Rewrite using `[hGdef, natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, hdeg]`. Rewrite using `[splits_iff_card_roots]`.

Conclude with `le_antisymm (card_roots' G) (hdG ▸ hcard)`.
-/
private theorem splits_real_of_sign_changing_at_integers (g : ℚ[X]) (n : ℕ) (hmon : g.Monic) (hdeg : g.natDegree = n)
    (halt : ∀ j < n, g.eval (j : ℚ) * g.eval ((j : ℚ) + 1) < 0) :
    (g.map (algebraMap ℚ ℝ)).Splits := by
  set G := g.map (algebraMap ℚ ℝ) with hGdef
  have hev : ∀ x : ℚ, G.eval (x : ℝ) = ((g.eval x : ℚ) : ℝ) := by
    intro x
    rw [hGdef, eval_map, show (x : ℝ) = algebraMap ℚ ℝ x from rfl, eval₂_at_apply]; rfl
  have hroot : ∀ j : Fin n, ∃ x ∈ Set.Ioo (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1), G.eval x = 0 := by
    intro j
    have hj := halt j j.2
    have hcont : ContinuousOn (fun x => G.eval x) (Set.Icc (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1)) :=
      G.continuous.continuousOn
    have h0 : (((j : ℕ) : ℝ)) ≤ ((j : ℕ) : ℝ) + 1 := by linarith
    have e1 : G.eval (((j : ℕ) : ℝ)) = ((g.eval ((j : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← hev]; norm_cast
    have e2 : G.eval (((j : ℕ) : ℝ) + 1) = ((g.eval (((j : ℕ) : ℚ) + 1) : ℚ) : ℝ) := by
      rw [← hev]; push_cast; rfl
    rcases mul_neg_iff.mp hj with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' h0 hcont
        (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ) + 1)) (G.eval (((j : ℕ) : ℝ))) from
          ⟨by rw [e2]; exact_mod_cast hb, by rw [e1]; exact_mod_cast ha⟩)
      exact ⟨x, hx, hx0⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo h0 hcont
        (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ))) (G.eval (((j : ℕ) : ℝ) + 1)) from
          ⟨by rw [e1]; exact_mod_cast ha, by rw [e2]; exact_mod_cast hb⟩)
      exact ⟨x, hx, hx0⟩
  choose r hr hr0 using hroot
  have hinj : Function.Injective r := by
    intro a b hab
    have ha := hr a
    have hb := hr b
    rw [hab] at ha
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h
      linarith [ha.2, hb.1]
    · have : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast h
      linarith [ha.1, hb.2]
  have hG0 : G ≠ 0 := (hmon.map (algebraMap ℚ ℝ)).ne_zero
  have hsub : Finset.univ.image r ⊆ G.roots.toFinset := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hG0]
    exact hr0 j
  have hcard : n ≤ G.roots.card := by
    calc n = (Finset.univ.image r).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ G.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ G.roots.card := Multiset.toFinset_card_le _
  have hdG : G.natDegree = n := by
    rw [hGdef, natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, hdeg]
  rw [splits_iff_card_roots]
  exact le_antisymm (card_roots' G) (hdG ▸ hcard)

open Polynomial in
/- English proof (translation)
Use `set G := g.map (algebraMap ℚ (Om l)) with hGdef`. Establish `hGm : G.Monic` using `hmon.map _`. Establish `hsp : G.Splits` using `IsAlgClosed.splits G`. Establish `hprod` using `hsp.eq_prod_roots_of_monic hGm`. Establish `hcard : G.roots.card = n`.

Rewrite using `[splits_iff_card_roots.mp hsp, hGdef, natDegree_map_eq_of_injective (algebraMap ℚ (Om l)).injective, hdeg]`. Establish `hev : aeval α g = (G.roots.map (fun b => α - b)).prod`. Rewrite using `[aeval_def, ← eval_map, ← hGdef]`. Use `conv_lhs => rw [hprod]`. Rewrite using `[eval_multiset_prod, Multiset.map_map]`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `b _`. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Establish `hle : δ ^ n ≤ ‖aeval α g‖`. Rewrite using `[hev]`. Use `show δ ^ n ≤ (normHom : Om l →*₀ ℝ) _`. Rewrite using `[map_multiset_prod, Multiset.map_map]`.

Establish `h2 : (G.roots.map (fun _ => δ)).prod ≤ (G.roots.map ((normHom : Om l →*₀ ℝ) ∘ fun b => α - b)).prod`. Apply `Multiset.prod_map_le_prod_map₀` to reduce the goal to its premises. Introduce `_ _`. Conclude with `hδ.le`. Introduce `b hb`.

Establish `hroot : aeval b g = 0`. Rewrite using `[aeval_def, ← eval_map, ← hGdef]`. Conclude with `(mem_roots hGm.ne_zero).mp hb`. Simplify using `using hno b hroot`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Multiset.map_const', Multiset.prod_replicate, hcard]`. Use `_ ≤ _ := h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem exists_root_near_of_aeval_small (l : ℕ) [Fact l.Prime] (g : ℚ[X]) (n : ℕ) (hmon : g.Monic)
    (hdeg : g.natDegree = n) (α : Om l) (δ : ℝ) (hδ : 0 < δ) (hsmall : ‖aeval α g‖ < δ ^ n) :
    ∃ β : Om l, aeval β g = 0 ∧ ‖α - β‖ < δ := by
  set G := g.map (algebraMap ℚ (Om l)) with hGdef
  have hGm : G.Monic := hmon.map _
  have hsp : G.Splits := IsAlgClosed.splits G
  have hprod := hsp.eq_prod_roots_of_monic hGm
  have hcard : G.roots.card = n := by
    rw [splits_iff_card_roots.mp hsp, hGdef,
      natDegree_map_eq_of_injective (algebraMap ℚ (Om l)).injective, hdeg]
  have hev : aeval α g = (G.roots.map (fun b => α - b)).prod := by
    rw [aeval_def, ← eval_map, ← hGdef]
    conv_lhs => rw [hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp
  by_contra hno
  push_neg at hno
  have hle : δ ^ n ≤ ‖aeval α g‖ := by
    rw [hev]
    show δ ^ n ≤ (normHom : Om l →*₀ ℝ) _
    rw [map_multiset_prod, Multiset.map_map]
    have h2 : (G.roots.map (fun _ => δ)).prod ≤
        (G.roots.map ((normHom : Om l →*₀ ℝ) ∘ fun b => α - b)).prod := by
      apply Multiset.prod_map_le_prod_map₀
      · intro _ _; exact hδ.le
      intro b hb
      have hroot : aeval b g = 0 := by
        rw [aeval_def, ← eval_map, ← hGdef]
        exact (mem_roots hGm.ne_zero).mp hb
      simpa using hno b hroot
    calc δ ^ n = (G.roots.map (fun _ => δ)).prod := by
          rw [Multiset.map_const', Multiset.prod_replicate, hcard]
      _ ≤ _ := h2
  linarith

open Polynomial in
/- English proof (translation)
Use `set S : ℝ := ∑ i : Fin n, ‖α‖ ^ (i : ℕ) with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg (fun i _ => by positivity)`. Establish `hB : 0 < S + 1` using `by linarith`. Establish `hq : ∀ i : Fin n, ∃ r : ℚ, ‖f.coeff i - (r : ℚ_[l])‖ < ε / (S + 1)` using `fun i => Padic.rat_dense l _ (by positivity)`. Use `choose q hq using hq`.

Use `set p : ℚ[X] := ∑ i : Fin n, C (q i) * X ^ (i : ℕ) with hp`. Establish `hpd : p.degree < n` using `degree_sum_fin_lt q`. Establish `hdX : (X ^ n : ℚ[X]).degree = n` using `degree_X_pow n`. Use `⟨X ^ n + p, monic_X_pow_add hpd, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_add_eq_left_of_degree_lt (by rw [hdX]; exact hpd), natDegree_X_pow]`.

Establish `hf' : f = X ^ n + ∑ i : Fin n, C (f.coeff i) * X ^ (i : ℕ)` using `by conv_lhs => rw [hf.as_sum]`. Rewrite using `[hn, Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) n]`. Establish `e : aeval α (X ^ n + p) - aeval α f = ∑ i : Fin n, algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ)` using `by conv_lhs => rw [hf', hp]`. Simplify using `only [map_add, map_sum, map_mul, aeval_C, aeval_X_pow, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[map_sub, sub_mul, map_ratCast]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_mul, norm_pow, norm_algebraMap']`. Use `_ ≤ ∑ i : Fin n, ε / (S + 1) * ‖α‖ ^ (i : ℕ) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i _`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Rewrite using `[norm_sub_rev]`. Conclude with `(hq i).le`. Use `_ = ε / (S + 1) * S := by rw [hS, Finset.mul_sum]`.

Use `_ < ε := by`. Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ hB]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exists_rat_monic_aeval_close (l : ℕ) [Fact l.Prime] (f : ℚ_[l][X]) (hf : f.Monic) (n : ℕ)
    (hn : f.natDegree = n) (α : Om l) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℚ[X], g.Monic ∧ g.natDegree = n ∧ ‖aeval α g - aeval α f‖ < ε := by
  set S : ℝ := ∑ i : Fin n, ‖α‖ ^ (i : ℕ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 < S + 1 := by linarith
  have hq : ∀ i : Fin n, ∃ r : ℚ, ‖f.coeff i - (r : ℚ_[l])‖ < ε / (S + 1) :=
    fun i => Padic.rat_dense l _ (by positivity)
  choose q hq using hq
  set p : ℚ[X] := ∑ i : Fin n, C (q i) * X ^ (i : ℕ) with hp
  have hpd : p.degree < n := degree_sum_fin_lt q
  have hdX : (X ^ n : ℚ[X]).degree = n := degree_X_pow n
  refine ⟨X ^ n + p, monic_X_pow_add hpd, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rw [hdX]; exact hpd), natDegree_X_pow]
  · have hf' : f = X ^ n + ∑ i : Fin n, C (f.coeff i) * X ^ (i : ℕ) := by
      conv_lhs => rw [hf.as_sum]
      rw [hn, Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) n]
    have e : aeval α (X ^ n + p) - aeval α f =
        ∑ i : Fin n, algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ) := by
      conv_lhs => rw [hf', hp]
      simp only [map_add, map_sum, map_mul, aeval_C, aeval_X_pow, add_sub_add_left_eq_sub,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sub, sub_mul, map_ratCast]
      simp
    rw [e]
    calc ‖∑ i : Fin n, algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ)‖
        ≤ ∑ i : Fin n, ‖algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ)‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin n, ‖(q i : ℚ_[l]) - f.coeff i‖ * ‖α‖ ^ (i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_pow, norm_algebraMap']
      _ ≤ ∑ i : Fin n, ε / (S + 1) * ‖α‖ ^ (i : ℕ) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [norm_sub_rev]
          exact (hq i).le
      _ = ε / (S + 1) * S := by rw [hS, Finset.mul_sum]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hB]
          nlinarith

open Polynomial in
/- English proof (translation)
Use `set M := UpperTheory.V.RealGen.model n with hM`. Take `⟨hMm, hMd⟩` from `model_monic_natDegree n`. Rewrite `hMm`, `hMd` using `[← hM]`. Establish `hMs : ∀ j < n, M.eval (j : ℚ) * M.eval ((j : ℚ) + 1) < 0` using `fun j hj => model_eval_mul_eval_succ_neg n j hj`. Establish `hMnz : ∀ j ∈ Finset.range (n + 1), M.eval (j : ℚ) ≠ 0`.

Introduce `j hj`. Rewrite `hj` using `[Finset.mem_range]`. Break down `Nat.lt_or_ge j n with h | h` into its components or cases. Conclude with `left_ne_zero_of_mul (hMs j h).ne`. Establish `hjn : j = n` using `by omega`.

Establish `h2` using `hMs (n - 1) (by omega)`. Establish `e : ((n - 1 : ℕ) : ℚ) + 1 = (j : ℚ)`. Rewrite using `[hjn, Nat.cast_sub (by omega)]; push_cast; ring`. Rewrite `h2` using `[e]`. Conclude with `right_ne_zero_of_mul h2.ne`.

Use `set D : ℚ := ∑ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| with hD`. Establish `hDj : ∀ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| ≤ D`. Introduce `j hj`. Conclude with `Finset.single_le_sum (f := fun j : ℕ => (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)|) (fun i _ => by positivity) hj`. Establish `hD0 : 0 < D`.

Establish `h0 : (0 : ℕ) ∈ Finset.range (n + 1)` using `by simp`. Establish `hp : 0 < (|g₁.eval ((0 : ℕ) : ℚ)| + 1) / |M.eval ((0 : ℕ) : ℚ)|`. Use `hMnz 0 h0` as an intermediate fact. Check the signs of the components of the expression. Conclude with `lt_of_lt_of_le hp (hDj 0 h0)`.

Use `set A : ℝ := ‖aeval α (M - g₁)‖ with hA`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (max (A / ε) (2 * (D : ℝ))) hl1`. Use `set L : ℚ := (l : ℚ) ^ (k + 1) with hL`. Establish `hLpos : 0 < L` using `pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _`.

Establish `hLk : ((l : ℝ)) ^ k ≤ (L : ℝ)`. Rewrite using `[hL]`. Use `push_cast`. Conclude with `pow_le_pow_right₀ hl1.le (Nat.le_succ k)`. Use `set t : ℚ := L / (L + 1) with ht`.

Establish `ht0 : t ≠ 0` using `by positivity`. Establish `hdiff : (M - g₁).degree < g₁.degree`. Use `degree_sub_lt (p := M) (q := g₁) (by rw [degree_eq_natDegree hMm.ne_zero, degree_eq_natDegree hmon.ne_zero, hMd, hdeg]) hMm.ne_zero (by rw [hMm.leadingCoeff, hmon.leadingCoeff])` as an intermediate fact. Rewrite `this` using `[degree_eq_natDegree hMm.ne_zero, hMd, ← hdeg, ← degree_eq_natDegree hmon.ne_zero]`. Then use the resulting hypothesis. Establish `hCd : (C t * (M - g₁)).degree < g₁.degree`.

Rewrite using `[degree_C_mul ht0]`. Conclude with `hdiff`. Use `⟨g₁ + C t * (M - g₁), hmon.add_of_left hCd, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_add_eq_left_of_degree_lt hCd, hdeg]`. Establish `e : aeval α (g₁ + C t * (M - g₁)) - aeval α g₁ = algebraMap ℚ (Om l) t * aeval α (M - g₁)`.

Rewrite using `[map_add, add_sub_cancel_left, map_mul, aeval_C]`. Rewrite using `[e, norm_mul, IsScalarTower.algebraMap_apply ℚ ℚ_[l] (Om l), norm_algebraMap', ← hA]`. Establish `hnL : ‖((L : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ))`. Rewrite using `[hL]`. Use `push_cast`.

Conclude with `Padic.norm_p_pow (k + 1)`. Establish `hlt : ‖((L : ℚ) : ℚ_[l])‖ < 1`. Rewrite using `[hnL]`. Apply `zpow_lt_one_of_neg₀ hl1` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Establish `hn1 : ‖((L : ℚ) : ℚ_[l]) + 1‖ = 1`. Rewrite using `[Padic.add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne), norm_one]`. Conclude with `max_eq_right hlt.le`. Establish `hnt : ‖((t : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ))`. Rewrite using `[ht]`.

Use `push_cast`. Rewrite using `[norm_div, hn1, div_one, hnL]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[eq_ratCast (algebraMap ℚ ℚ_[l]) t, hnt]`.

Establish `hA0 : 0 ≤ A` using `norm_nonneg _`. Establish `hkA : A / ε < (l : ℝ) ^ k` using `lt_of_le_of_lt (le_max_left _ _) hk`. Establish `hA' : A < ε * (l : ℝ) ^ k` using `by rwa [div_lt_iff₀ hε, mul_comm] at hkA`. Establish `hz : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = 1 / ((l : ℝ) ^ k * l)`. Rewrite using `[zpow_neg, zpow_natCast, pow_succ, one_div]`.

Rewrite using `[hz, one_div_mul_eq_div, div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `j hj`. Establish `hkD : 2 * (D : ℝ) < (L : ℝ)` using `lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk) hLk`. Establish `hkD' : 2 * D < L` using `by exact_mod_cast hkD`.

Establish `sgn : ∀ i ∈ Finset.range (n + 1), 0 < (g₁ + C t * (M - g₁)).eval (i : ℚ) * M.eval (i : ℚ)`. Introduce `i hi`. Establish `hMi` using `hMnz i hi`. Establish `hbi` using `hDj i hi`. Use `set a := g₁.eval (i : ℚ)`.

Use `set m := M.eval (i : ℚ)`. Establish `hm : 0 < |m|` using `abs_pos.mpr hMi`. Establish `hb : |a| + 1 ≤ D * |m|` using `by rwa [div_le_iff₀ hm] at hbi`. Establish `ev : (g₁ + C t * (M - g₁)).eval (i : ℚ) = a + t * (m - a)`. Simplify using `[a, m]`.

Rewrite using `[ev]`. Establish `hL1 : 0 < L + 1` using `by linarith`. Establish `key : (a + t * (m - a)) * m * (L + 1) = a * m + L * m * m`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hmm : m * m = |m| * |m|` using `(abs_mul_abs_self m).symm`. Establish `ham : -(|a| * |m|) ≤ a * m`. Use `neg_abs_le (a * m)` as an intermediate fact. Rewrite `this` using `[abs_mul]`. Then use the resulting hypothesis.

Establish `h3 : (|a| + 1) * |m| ≤ D * |m| * |m|` using `by nlinarith`. Establish `h4 : 2 * D * (|m| * |m|) < L * (|m| * |m|)`. Apply `mul_lt_mul_of_pos_right hkD'` to reduce the goal to its premises. Check the signs of the components of the expression. Establish `hLm : L * m * m = L * (|m| * |m|)` using `by rw [mul_assoc, hmm]`.

Establish `h5 : 0 < (a + t * (m - a)) * m * (L + 1)`. Rewrite using `[key, hLm]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `lt_of_mul_lt_mul_right (by rw [zero_mul]; exact h5) hL1.le`. Establish `s1` using `sgn j (by rw [Finset.mem_range]; omega)`.

Establish `s2` using `sgn (j + 1) (by rw [Finset.mem_range]; omega)`. Move the coercions through the operations in `at s2`. Establish `hm` using `hMs j hj`. Use polynomial arithmetic with `[mul_pos s1 s2]`.
-/
private theorem exists_rat_monic_close_sign_changing_at_integers (l : ℕ) [Fact l.Prime] (g₁ : ℚ[X]) (n : ℕ) (hn : 0 < n)
    (hmon : g₁.Monic) (hdeg : g₁.natDegree = n) (α : Om l) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℚ[X], g.Monic ∧ g.natDegree = n ∧ ‖aeval α g - aeval α g₁‖ < ε ∧
      ∀ j < n, g.eval (j : ℚ) * g.eval ((j : ℚ) + 1) < 0 := by
  set M := UpperTheory.V.RealGen.model n with hM
  obtain ⟨hMm, hMd⟩ := model_monic_natDegree n
  rw [← hM] at hMm hMd
  have hMs : ∀ j < n, M.eval (j : ℚ) * M.eval ((j : ℚ) + 1) < 0 := fun j hj => model_eval_mul_eval_succ_neg n j hj
  have hMnz : ∀ j ∈ Finset.range (n + 1), M.eval (j : ℚ) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j n with h | h
    · exact left_ne_zero_of_mul (hMs j h).ne
    · have hjn : j = n := by omega
      have h2 := hMs (n - 1) (by omega)
      have e : ((n - 1 : ℕ) : ℚ) + 1 = (j : ℚ) := by
        rw [hjn, Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at h2
      exact right_ne_zero_of_mul h2.ne
  set D : ℚ := ∑ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| with hD
  have hDj : ∀ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| ≤ D := by
    intro j hj
    exact Finset.single_le_sum (f := fun j : ℕ => (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)|)
      (fun i _ => by positivity) hj
  have hD0 : 0 < D := by
    have h0 : (0 : ℕ) ∈ Finset.range (n + 1) := by simp
    have hp : 0 < (|g₁.eval ((0 : ℕ) : ℚ)| + 1) / |M.eval ((0 : ℕ) : ℚ)| := by
      have := hMnz 0 h0
      positivity
    exact lt_of_lt_of_le hp (hDj 0 h0)
  set A : ℝ := ‖aeval α (M - g₁)‖ with hA
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max (A / ε) (2 * (D : ℝ))) hl1
  set L : ℚ := (l : ℚ) ^ (k + 1) with hL
  have hLpos : 0 < L := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have hLk : ((l : ℝ)) ^ k ≤ (L : ℝ) := by
    rw [hL]; push_cast
    exact pow_le_pow_right₀ hl1.le (Nat.le_succ k)
  set t : ℚ := L / (L + 1) with ht
  have ht0 : t ≠ 0 := by positivity
  have hdiff : (M - g₁).degree < g₁.degree := by
    have := degree_sub_lt (p := M) (q := g₁)
      (by rw [degree_eq_natDegree hMm.ne_zero, degree_eq_natDegree hmon.ne_zero, hMd, hdeg])
      hMm.ne_zero (by rw [hMm.leadingCoeff, hmon.leadingCoeff])
    rwa [degree_eq_natDegree hMm.ne_zero, hMd, ← hdeg, ← degree_eq_natDegree hmon.ne_zero] at this
  have hCd : (C t * (M - g₁)).degree < g₁.degree := by
    rw [degree_C_mul ht0]; exact hdiff
  refine ⟨g₁ + C t * (M - g₁), hmon.add_of_left hCd, ?_, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt hCd, hdeg]
  · have e : aeval α (g₁ + C t * (M - g₁)) - aeval α g₁ = algebraMap ℚ (Om l) t * aeval α (M - g₁) := by
      rw [map_add, add_sub_cancel_left, map_mul, aeval_C]
    rw [e, norm_mul, IsScalarTower.algebraMap_apply ℚ ℚ_[l] (Om l), norm_algebraMap', ← hA]
    have hnL : ‖((L : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      rw [hL]; push_cast; exact Padic.norm_p_pow (k + 1)
    have hlt : ‖((L : ℚ) : ℚ_[l])‖ < 1 := by
      rw [hnL]
      apply zpow_lt_one_of_neg₀ hl1
      omega
    have hn1 : ‖((L : ℚ) : ℚ_[l]) + 1‖ = 1 := by
      rw [Padic.add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne), norm_one]
      exact max_eq_right hlt.le
    have hnt : ‖((t : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      rw [ht]; push_cast
      rw [norm_div, hn1, div_one, hnL]
      push_cast; rfl
    rw [eq_ratCast (algebraMap ℚ ℚ_[l]) t, hnt]
    have hA0 : 0 ≤ A := norm_nonneg _
    have hkA : A / ε < (l : ℝ) ^ k := lt_of_le_of_lt (le_max_left _ _) hk
    have hA' : A < ε * (l : ℝ) ^ k := by rwa [div_lt_iff₀ hε, mul_comm] at hkA
    have hz : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = 1 / ((l : ℝ) ^ k * l) := by
      rw [zpow_neg, zpow_natCast, pow_succ, one_div]
    rw [hz, one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith
  · intro j hj
    have hkD : 2 * (D : ℝ) < (L : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk) hLk
    have hkD' : 2 * D < L := by exact_mod_cast hkD
    have sgn : ∀ i ∈ Finset.range (n + 1),
        0 < (g₁ + C t * (M - g₁)).eval (i : ℚ) * M.eval (i : ℚ) := by
      intro i hi
      have hMi := hMnz i hi
      have hbi := hDj i hi
      set a := g₁.eval (i : ℚ)
      set m := M.eval (i : ℚ)
      have hm : 0 < |m| := abs_pos.mpr hMi
      have hb : |a| + 1 ≤ D * |m| := by rwa [div_le_iff₀ hm] at hbi
      have ev : (g₁ + C t * (M - g₁)).eval (i : ℚ) = a + t * (m - a) := by
        simp [a, m]
      rw [ev]
      have hL1 : 0 < L + 1 := by linarith
      have key : (a + t * (m - a)) * m * (L + 1) = a * m + L * m * m := by
        rw [ht]; field_simp; ring
      have hmm : m * m = |m| * |m| := (abs_mul_abs_self m).symm
      have ham : -(|a| * |m|) ≤ a * m := by
        have := neg_abs_le (a * m); rwa [abs_mul] at this
      have h3 : (|a| + 1) * |m| ≤ D * |m| * |m| := by nlinarith
      have h4 : 2 * D * (|m| * |m|) < L * (|m| * |m|) := by
        apply mul_lt_mul_of_pos_right hkD'; positivity
      have hLm : L * m * m = L * (|m| * |m|) := by rw [mul_assoc, hmm]
      have h5 : 0 < (a + t * (m - a)) * m * (L + 1) := by
        rw [key, hLm]; nlinarith
      exact lt_of_mul_lt_mul_right (by rw [zero_mul]; exact h5) hL1.le
    have s1 := sgn j (by rw [Finset.mem_range]; omega)
    have s2 := sgn (j + 1) (by rw [Finset.mem_range]; omega)
    push_cast at s2
    have hm := hMs j hj
    nlinarith [mul_pos s1 s2]

open Polynomial IntermediateField in
/- English proof (translation)
Introduce `l _ K`. Use `haveI : FiniteDimensional ℚ_[l] K.1 := K.2`. Take `⟨α₀, hα₀⟩` from `Field.exists_primitive_element ℚ_[l] K.1`. Use `set α : Om l := (α₀ : Om l) with hαdef`. Establish `hαK : α ∈ K.1` using `α₀.2`.

Establish `hint : IsIntegral ℚ_[l] α` using `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral`. Use `set f := minpoly ℚ_[l] α with hfdef`. Use `set n := f.natDegree with hndef`. Establish `hfm : f.Monic` using `minpoly.monic hint`. Establish `hn : 0 < n` using `minpoly.natDegree_pos hint`.

Establish `hKn : Module.finrank ℚ_[l] K.1 = n`. Establish `h1 : Module.finrank ℚ_[l] (ℚ_[l]⟮α₀⟯) = (minpoly ℚ_[l] α₀).natDegree` using `IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α₀)`. Rewrite `h1` using `[hα₀, IntermediateField.finrank_top', IntermediateField.minpoly_eq]`. Conclude with `h1`. Establish `hKeq : ℚ_[l]⟮α⟯ = K.1`.

Apply `IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin_simple_le_iff.mpr hαK)` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin.finrank hint, hKn]`. Use `set R := (f.map (algebraMap ℚ_[l] (Om l))).roots.toFinset.erase α with hR`. Establish `hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ R, δ ≤ ‖α - x‖`. Distinguish the cases in `hne : R.Nonempty`.

Take `⟨x0, hx0, hmin⟩` from `R.exists_min_image (fun x => ‖α - x‖) hne`. Use `⟨‖α - x0‖, ?_, hmin⟩` and prove the remaining obligations. Rewrite using `[norm_pos_iff, sub_ne_zero]`. Conclude with `(Finset.ne_of_mem_erase hx0).symm`. Use `⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩` and prove the remaining obligations.

Take `⟨δ, hδ0, hδR⟩` from `hδ`. Establish `hε : 0 < δ ^ n / 2` using `by positivity`. Take `⟨g₁, hg₁m, hg₁d, hg₁⟩` from `exists_rat_monic_aeval_close l f hfm n rfl α (δ ^ n / 2) hε`. Take `⟨g, hgm, hgd, hg, halt⟩` from `exists_rat_monic_close_sign_changing_at_integers l g₁ n hn hg₁m hg₁d α (δ ^ n / 2) hε`. Establish `hf0 : Polynomial.aeval α f = 0` using `minpoly.aeval ℚ_[l] α`.

Establish `hsmall : ‖Polynomial.aeval α g‖ < δ ^ n`. Establish `e : Polynomial.aeval α g = (Polynomial.aeval α g - Polynomial.aeval α g₁) + (Polynomial.aeval α g₁ - Polynomial.aeval α f)`. Rewrite using `[hf0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨β, hβ, hαβ⟩` from `exists_root_near_of_aeval_small l g n hgm hgd α δ hδ0 hsmall`. Establish `hβint : IsIntegral ℚ_[l] β` using `(Algebra.IsAlgebraic.isAlgebraic β).isIntegral`. Establish `hαβK : α ∈ ℚ_[l]⟮β⟯`. Apply `IsKrasner.krasner (minpoly.irreducible hint).separable (IsAlgClosed.splits _) hβint` to reduce the goal to its premises.

Introduce `x' hconj hne`. Establish `hx' : x' ∈ R`. Rewrite using `[hR, Finset.mem_erase, Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_monic_ne_zero hfm), Polynomial.IsRoot, Polynomial.eval_map_algebraMap]`. Conclude with `⟨fun h => hne h.symm, hconj.aeval_eq_zero⟩`. Conclude with `lt_of_lt_of_le hαβ (hδR x' hx')`.

Use `⟨β, g, hgm, splits_real_of_sign_changing_at_integers g n hgm hgd halt, hβ, ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional ℚ_[l] (ℚ_[l]⟮β⟯) := IntermediateField.adjoin.finiteDimensional hβint`. Use `symm`. Apply `IntermediateField.eq_of_le_of_finrank_le` to reduce the goal to its premises. Rewrite using `[← hKeq]`.

Conclude with `IntermediateField.adjoin_simple_le_iff.mpr hαβK`. Rewrite using `[IntermediateField.adjoin.finrank hβint, hKn]`. Establish `hgm' : (g.map (algebraMap ℚ ℚ_[l])).Monic` using `hgm.map _`. Establish `hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l])`. Apply `minpoly.dvd` to reduce the goal to its premises.

Rewrite using `[Polynomial.aeval_map_algebraMap]`. Conclude with `hβ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.exists_real_split_primitive_element_padic_finite_ext :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (β : Om l) (g : Polynomial ℚ), g.Monic ∧ (g.map (algebraMap ℚ ℝ)).Splits ∧ Polynomial.aeval β g = 0 ∧ IntermediateField.adjoin ℚ_[l] {β} = K.1 := by
  classical
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element ℚ_[l] K.1
  set α : Om l := (α₀ : Om l) with hαdef
  have hαK : α ∈ K.1 := α₀.2
  have hint : IsIntegral ℚ_[l] α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set f := minpoly ℚ_[l] α with hfdef
  set n := f.natDegree with hndef
  have hfm : f.Monic := minpoly.monic hint
  have hn : 0 < n := minpoly.natDegree_pos hint
  have hKn : Module.finrank ℚ_[l] K.1 = n := by
    have h1 : Module.finrank ℚ_[l] (ℚ_[l]⟮α₀⟯) = (minpoly ℚ_[l] α₀).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α₀)
    rw [hα₀, IntermediateField.finrank_top', IntermediateField.minpoly_eq] at h1
    exact h1
  have hKeq : ℚ_[l]⟮α⟯ = K.1 := by
    apply IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin_simple_le_iff.mpr hαK)
    rw [IntermediateField.adjoin.finrank hint, hKn]
  set R := (f.map (algebraMap ℚ_[l] (Om l))).roots.toFinset.erase α with hR
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ R, δ ≤ ‖α - x‖ := by
    by_cases hne : R.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := R.exists_min_image (fun x => ‖α - x‖) hne
      refine ⟨‖α - x0‖, ?_, hmin⟩
      rw [norm_pos_iff, sub_ne_zero]
      exact (Finset.ne_of_mem_erase hx0).symm
    · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨δ, hδ0, hδR⟩ := hδ
  have hε : 0 < δ ^ n / 2 := by positivity
  obtain ⟨g₁, hg₁m, hg₁d, hg₁⟩ := exists_rat_monic_aeval_close l f hfm n rfl α (δ ^ n / 2) hε
  obtain ⟨g, hgm, hgd, hg, halt⟩ := exists_rat_monic_close_sign_changing_at_integers l g₁ n hn hg₁m hg₁d α (δ ^ n / 2) hε
  have hf0 : Polynomial.aeval α f = 0 := minpoly.aeval ℚ_[l] α
  have hsmall : ‖Polynomial.aeval α g‖ < δ ^ n := by
    have e : Polynomial.aeval α g =
        (Polynomial.aeval α g - Polynomial.aeval α g₁) + (Polynomial.aeval α g₁ - Polynomial.aeval α f) := by
      rw [hf0]; ring
    rw [e]
    calc _ ≤ ‖Polynomial.aeval α g - Polynomial.aeval α g₁‖ + ‖Polynomial.aeval α g₁ - Polynomial.aeval α f‖ :=
          norm_add_le _ _
      _ < δ ^ n / 2 + δ ^ n / 2 := add_lt_add hg hg₁
      _ = δ ^ n := by ring
  obtain ⟨β, hβ, hαβ⟩ := exists_root_near_of_aeval_small l g n hgm hgd α δ hδ0 hsmall
  have hβint : IsIntegral ℚ_[l] β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hαβK : α ∈ ℚ_[l]⟮β⟯ := by
    apply IsKrasner.krasner (minpoly.irreducible hint).separable (IsAlgClosed.splits _) hβint
    intro x' hconj hne
    have hx' : x' ∈ R := by
      rw [hR, Finset.mem_erase, Multiset.mem_toFinset,
        Polynomial.mem_roots (Polynomial.map_monic_ne_zero hfm), Polynomial.IsRoot,
        Polynomial.eval_map_algebraMap]
      exact ⟨fun h => hne h.symm, hconj.aeval_eq_zero⟩
    exact lt_of_lt_of_le hαβ (hδR x' hx')
  refine ⟨β, g, hgm, splits_real_of_sign_changing_at_integers g n hgm hgd halt, hβ, ?_⟩
  haveI : FiniteDimensional ℚ_[l] (ℚ_[l]⟮β⟯) := IntermediateField.adjoin.finiteDimensional hβint
  symm
  apply IntermediateField.eq_of_le_of_finrank_le
  · rw [← hKeq]; exact IntermediateField.adjoin_simple_le_iff.mpr hαβK
  · rw [IntermediateField.adjoin.finrank hβint, hKn]
    have hgm' : (g.map (algebraMap ℚ ℚ_[l])).Monic := hgm.map _
    have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_map_algebraMap]
      exact hβ
    calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hgm'.ne_zero
      _ = n := by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℚ_[l]).injective, hgd]
