import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.GramWindow2

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset

section Point

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

/- English proof (translation)
Rewrite using `[← algebraMap_smul ℚ_[p] c x, PadicInt.algebraMap_apply]`.
-/
theorem zsmul_eq (c : ℤ_[p]) (x : MvPolynomial σ ℚ_[p]) : c • x = (c : ℚ_[p]) • x := by
  rw [← algebraMap_smul ℚ_[p] c x, PadicInt.algebraMap_apply]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[norm_zero]`. Conclude with `absurd h (not_lt.2 (Real.rpow_nonneg (by linarith) _))`.

Rewrite `h`, the goal using `[Padic.norm_eq_zpow_neg_valuation hd]`. Establish `e1 : (p : ℝ) ^ (-((k : ℝ) + 1)) = (p : ℝ) ^ (-(k + 1) : ℤ)`. Rewrite using `[← Real.rpow_intCast]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h` using `[e1]`. Establish `h2` using `(zpow_lt_zpow_iff_right₀ hp1).1 h`. Conclude with `(zpow_le_zpow_iff_right₀ hp1).2 (by omega)`.
-/
theorem norm_ge_of_gt (d : ℚ_[p]) (k : ℤ) (h : (p : ℝ) ^ (-((k : ℝ) + 1)) < ‖d‖) : (p : ℝ) ^ (-k) ≤ ‖d‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hd : d ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (not_lt.2 (Real.rpow_nonneg (by linarith) _))
  rw [Padic.norm_eq_zpow_neg_valuation hd] at h ⊢
  have e1 : (p : ℝ) ^ (-((k : ℝ) + 1)) = (p : ℝ) ^ (-(k + 1) : ℤ) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [e1] at h
  have h2 := (zpow_lt_zpow_iff_right₀ hp1).1 h
  exact (zpow_le_zpow_iff_right₀ hp1).2 (by omega)

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`. Use `set be : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] := LinearMap.mk₂ ℚ_[p] Ψ h2 (fun c u v => by rw [h1, smul_eq_mul]) h4 (fun c u v => by rw [h3, smul_eq_mul]) with hbe`. Establish `hbeΨ : ∀ u v, be u v = Ψ u v` using `fun u v => rfl`. Use `set L := Submodule.span ℤ_[p] (Set.range e) with hL`.

Establish `heL : ∀ a, e a ∈ L` using `fun a => Submodule.subset_span ⟨a, rfl⟩`. Use `set P := U⁻¹ with hP`. Use `set Q := V⁻¹ with hQ`. Establish `hPU : P * U = 1` using `Matrix.nonsing_inv_mul U hU`. Establish `hVQ : V * Q = 1` using `Matrix.mul_nonsing_inv V hV`.

Use `set x : Fin n → MvPolynomial σ ℚ_[p] := fun i => ∑ a, P i a • e a with hx`. Use `set y : Fin n → MvPolynomial σ ℚ_[p] := fun l => ∑ b, Q b l • e b with hy`. Establish `hxL : ∀ i, x i ∈ L` using `fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)`. Establish `hyL : ∀ i, y i ∈ L` using `fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)`. Establish `hxy : ∀ i l, s * Ψ (x i) (y l) = if i = l then (d i : ℚ_[p]) else 0`.

Introduce `i l`. Establish `e1 : s * Ψ (x i) (y l) = ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p])`. Rewrite using `[← hbeΨ, hx, hy]`. Simplify using `only [zsmul_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hbeΨ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (((P * (U * Matrix.diagonal d * V) * Q) i l : ℤ_[p]) : ℚ_[p]) = ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p])`. Simplify using `only [hG]`.

Generalize the expression as in `U * Matrix.diagonal d * V = M`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [PadicInt.coe_sum, PadicInt.coe_mul]`.

Establish `e3 : P * (U * Matrix.diagonal d * V) * Q = Matrix.diagonal d`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.diagonal d := by rw [hPU, hVQ, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[e1, ← e2, e3, Matrix.diagonal_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `set S := Finset.univ.filter (fun i => ¬ ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1))) with hS`. Use `set m := S.card with hm`. Use `set ι : Fin m → Fin n := fun t => (S.equivFin.symm t : Fin n) with hι`. Establish `hιinj : Function.Injective ι` using `fun t t' h => S.equivFin.symm.injective (Subtype.ext h)`.

Establish `hιS : ∀ t, (p : ℝ) ^ (-k) ≤ ‖(d (ι t) : ℚ_[p])‖`. Introduce `t`. Establish `: ι t ∈ S` using `(S.equivFin.symm t).2`. Rewrite `this` using `[hS, Finset.mem_filter]`. Conclude with `norm_ge_of_gt _ k (not_le.1 this.2)`.

Establish `hd0 : ∀ t, (d (ι t) : ℚ_[p]) ≠ 0`. Introduce `t h0`. Use `hιS t` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `absurd this (not_le.2 (zpow_pos (by linarith) _))`.

Establish `hsc : ∀ t, ‖(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p])‖ ≤ 1`. Introduce `t`. Rewrite using `[norm_div, norm_mul, norm_zpow, Padic.norm_p, inv_zpow', div_le_one (norm_pos_iff.2 (hd0 t))]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgood : m ≤ Formalism.GM.M.goodCount p Ψ L k`.

Establish `hW : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Set.range e))` using `FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range e)`. Establish `hb` using `Formalism.MainNotions.G.SymmetricFormBlocks.gc_bdd_gen p Ψ h1 (fun n' s' f v => by show be (∑ i ∈ s', f i) v = ∑ i ∈ s', be (f i) v`. Rewrite using `[map_sum, LinearMap.sum_apply])`. Use `L (Submodule.span ℚ_[p] (Set.range e)) (fun z hz => Submodule.span_subset_span ℤ_[p] ℚ_[p] _ hz) k`. Use `set cc : Fin m → ℤ_[p] := fun t => ⟨(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]), hsc t⟩ with hcc`.

Use `le_csSup hb ⟨fun t => x (ι t), fun t => cc t • y (ι t), fun t => hxL _, fun t => L.smul_mem _ (hyL _), ?_⟩` and prove the remaining obligations. Introduce `t t'`. Use `show Ψ (x (ι t)) (cc t' • y (ι t')) = _`. Rewrite using `[zsmul_eq, h3]`. Establish `hh` using `hxy (ι t) (ι t')`.

Establish `hΨ : Ψ (x (ι t)) (y (ι t')) = (if ι t = ι t' then (d (ι t) : ℚ_[p]) else 0) / s`. Rewrite using `[← hh]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hΨ]`. Distinguish the cases in `htt : t = t'`.

Substitute `htt` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Use `show (p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]) * ((d (ι t) : ℚ_[p]) / s) = _`. Use `hd0 t` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Rewrite using `[if_neg htt, if_neg (fun h => htt (hιinj h)), zero_div, mul_zero]`. Establish `hrank : Module.finrank ℤ_[p] L = n`. Rewrite using `[hL, finrank_span_eq_card hli, Fintype.card_fin]`. Establish `hcard : (Finset.univ.filter (fun i => ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card + m = n`. Rewrite using `[hm, hS, Finset.card_filter_add_card_filter_not]`.

Simplify using the standard rewrite rules. Unfold `Formalism.GM.M.bad`. Use linear arithmetic over natural numbers and integers.
-/
theorem bad_le_smith (n : ℕ) (k : ℤ) (Ψ : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (e : Fin n → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] e)
    (h1 : ∀ (a : ℚ_[p]) u v, Ψ (a • u) v = a * Ψ u v) (h2 : ∀ u u' v, Ψ (u + u') v = Ψ u v + Ψ u' v)
    (h3 : ∀ (a : ℚ_[p]) u v, Ψ u (a • v) = a * Ψ u v) (h4 : ∀ u v v', Ψ u (v + v') = Ψ u v + Ψ u v')
    (s : ℚ_[p]) (hs0 : s ≠ 0) (hs1 : ‖s‖ ≤ 1) (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hG : ∀ a b, s * Ψ (e a) (e b) = (((U * Matrix.diagonal d * V) a b : ℤ_[p]) : ℚ_[p])) :
    Formalism.GM.M.bad p Ψ (Submodule.span ℤ_[p] (Set.range e)) k ≤
      (Finset.univ.filter (fun i => ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  set be : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    LinearMap.mk₂ ℚ_[p] Ψ h2 (fun c u v => by rw [h1, smul_eq_mul]) h4 (fun c u v => by rw [h3, smul_eq_mul]) with hbe
  have hbeΨ : ∀ u v, be u v = Ψ u v := fun u v => rfl
  set L := Submodule.span ℤ_[p] (Set.range e) with hL
  have heL : ∀ a, e a ∈ L := fun a => Submodule.subset_span ⟨a, rfl⟩

  set P := U⁻¹ with hP
  set Q := V⁻¹ with hQ
  have hPU : P * U = 1 := Matrix.nonsing_inv_mul U hU
  have hVQ : V * Q = 1 := Matrix.mul_nonsing_inv V hV
  set x : Fin n → MvPolynomial σ ℚ_[p] := fun i => ∑ a, P i a • e a with hx
  set y : Fin n → MvPolynomial σ ℚ_[p] := fun l => ∑ b, Q b l • e b with hy
  have hxL : ∀ i, x i ∈ L := fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)
  have hyL : ∀ i, y i ∈ L := fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)
  have hxy : ∀ i l, s * Ψ (x i) (y l) = if i = l then (d i : ℚ_[p]) else 0 := by
    intro i l
    have e1 : s * Ψ (x i) (y l) = ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p]) := by
      rw [← hbeΨ, hx, hy]
      simp only [zsmul_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hbeΨ,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have e2 : (((P * (U * Matrix.diagonal d * V) * Q) i l : ℤ_[p]) : ℚ_[p]) =
        ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p]) := by
      simp only [hG]
      generalize U * Matrix.diagonal d * V = M
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [PadicInt.coe_sum, PadicInt.coe_mul]
    have e3 : P * (U * Matrix.diagonal d * V) * Q = Matrix.diagonal d := by
      calc P * (U * Matrix.diagonal d * V) * Q = (P * U) * Matrix.diagonal d * (V * Q) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal d := by rw [hPU, hVQ, Matrix.one_mul, Matrix.mul_one]
    rw [e1, ← e2, e3, Matrix.diagonal_apply]
    split_ifs <;> simp

  set S := Finset.univ.filter (fun i => ¬ ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1))) with hS
  set m := S.card with hm
  set ι : Fin m → Fin n := fun t => (S.equivFin.symm t : Fin n) with hι
  have hιinj : Function.Injective ι := fun t t' h => S.equivFin.symm.injective (Subtype.ext h)
  have hιS : ∀ t, (p : ℝ) ^ (-k) ≤ ‖(d (ι t) : ℚ_[p])‖ := by
    intro t
    have : ι t ∈ S := (S.equivFin.symm t).2
    rw [hS, Finset.mem_filter] at this
    exact norm_ge_of_gt _ k (not_le.1 this.2)
  have hd0 : ∀ t, (d (ι t) : ℚ_[p]) ≠ 0 := by
    intro t h0
    have := hιS t
    rw [h0, norm_zero] at this
    exact absurd this (not_le.2 (zpow_pos (by linarith) _))
  have hsc : ∀ t, ‖(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p])‖ ≤ 1 := by
    intro t
    rw [norm_div, norm_mul, norm_zpow, Padic.norm_p, inv_zpow', div_le_one (norm_pos_iff.2 (hd0 t))]
    calc (p : ℝ) ^ (-k) * ‖s‖ ≤ (p : ℝ) ^ (-k) * 1 :=
          mul_le_mul_of_nonneg_left hs1 (zpow_nonneg (by linarith) _)
      _ ≤ ‖(d (ι t) : ℚ_[p])‖ := by rw [mul_one]; exact hιS t
  have hgood : m ≤ Formalism.GM.M.goodCount p Ψ L k := by
    have hW : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Set.range e)) :=
      FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range e)
    have hb := Formalism.MainNotions.G.SymmetricFormBlocks.gc_bdd_gen p Ψ h1
      (fun n' s' f v => by
        show be (∑ i ∈ s', f i) v = ∑ i ∈ s', be (f i) v
        rw [map_sum, LinearMap.sum_apply])
      L (Submodule.span ℚ_[p] (Set.range e)) (fun z hz => Submodule.span_subset_span ℤ_[p] ℚ_[p] _ hz) k
    set cc : Fin m → ℤ_[p] := fun t => ⟨(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]), hsc t⟩ with hcc
    refine le_csSup hb ⟨fun t => x (ι t), fun t => cc t • y (ι t), fun t => hxL _,
      fun t => L.smul_mem _ (hyL _), ?_⟩
    intro t t'
    show Ψ (x (ι t)) (cc t' • y (ι t')) = _
    rw [zsmul_eq, h3]
    have hh := hxy (ι t) (ι t')
    have hΨ : Ψ (x (ι t)) (y (ι t')) = (if ι t = ι t' then (d (ι t) : ℚ_[p]) else 0) / s := by
      rw [← hh]; field_simp
    rw [hΨ]
    by_cases htt : t = t'
    · subst htt
      rw [if_pos rfl, if_pos rfl]
      show (p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]) * ((d (ι t) : ℚ_[p]) / s) = _
      have := hd0 t
      field_simp
    · rw [if_neg htt, if_neg (fun h => htt (hιinj h)), zero_div, mul_zero]
  have hrank : Module.finrank ℤ_[p] L = n := by
    rw [hL, finrank_span_eq_card hli, Fintype.card_fin]
  have hcard : (Finset.univ.filter (fun i => ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card + m = n := by
    rw [hm, hS, Finset.card_filter_add_card_filter_not]
    simp
  unfold Formalism.GM.M.bad
  omega

end Point

open Formalism.GM Formalism.GM.MeanGammaLemmas in
/- English proof (translation)
Introduce `p hp σ n del h Y0 k La0 t0 Ψ e s c hli h1 h2 h3 h4 hY0 hYh hdel hk hc hdet hlead hgram`. Use `set Aq := binMatK ℚ_[p] del c with hAq`. Use `set cz : Fin n → Fin n → ℕ → ℤ_[p] := fun a b i => ⟨c a b i, hc a b i⟩ with hcz`. Establish `hczc : ∀ a b i, ((cz a b i : ℤ_[p]) : ℚ_[p]) = c a b i` using `fun _ _ _ => rfl`. Use `set M : ℕ → Matrix (Fin n) (Fin n) ℤ_[p] := fun j a b => ∑ i ∈ Finset.range (del + 1), cz a b i * (((t0 + j).choose i : ℕ) : ℤ_[p]) with hMdef`.

Establish `hM : ∀ j a b, ((M j a b : ℤ_[p]) : ℚ_[p]) = (Aq a b).eval (((t0 + j : ℕ) : ℚ_[p]))`. Introduce `j a b`. Rewrite using `[hAq, binMatK_eval_nat]`. Simplify using `only [hMdef, PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_natCast, hczc]`. Use `choose U V d hU hV hfac using fun j => Formalism.GM.Top.smithZp p n (M j)`.

Establish `hpt : ∀ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ) ≤ ((Finset.univ.filter (fun i => ‖(d j i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ)`. Introduce `j hj`. Take `⟨hs0, hs1, hg⟩` from `hgram j hj`. Use `bad_le_smith n k (Ψ j) e hli (h1 j) (h2 j) (h3 j) (h4 j) (s j) hs0 hs1 (U j) (V j) (d j) (hU j) (hV j) (fun a b => by rw [hg a b, ← hfac j, hM, Matrix.map_apply])` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Use `set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg`. Use `set φ : ℤ_[p] →+* PadicAlgCl p := alg.comp PadicInt.Coe.ringHom with hφ`. Establish `hφn : ∀ z : ℤ_[p], ‖φ z‖ = ‖z‖`. Introduce `z`. Use `show ‖alg (z : ℚ_[p])‖ = _`.

Rewrite using `[halg, norm_algebraMap', PadicInt.norm_def]`. Use `set c' : Fin n → Fin n → ℕ → PadicAlgCl p := fun i j k => alg (c i j k) with hc'`. Establish `hAK : binMatK (PadicAlgCl p) del c' = Aq.map (Polynomial.map alg)` using `binMatK_map ℚ_[p] (PadicAlgCl p) alg del _`. Establish `hDk : (binMatK (PadicAlgCl p) del c').det = Aq.det.map alg`. Rewrite using `[hAK]`.

Conclude with `split_det p Aq`. Take `⟨hsplit, hcard⟩` from `splits_form (binMatK (PadicAlgCl p) del c').det`. Establish `hlc : (binMatK (PadicAlgCl p) del c').det.leadingCoeff = alg Aq.det.leadingCoeff`. Rewrite using `[hDk, Polynomial.leadingCoeff_map]`. Establish `hnd : (binMatK (PadicAlgCl p) del c').det.natDegree = Aq.det.natDegree`.

Rewrite using `[hDk, Polynomial.natDegree_map]`. Establish `hlcnorm : ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖`. Rewrite using `[hlc, halg, norm_algebraMap']`. Establish `hleadne : (binMatK (PadicAlgCl p) del c').det.leadingCoeff ≠ 0`. Rewrite using `[← norm_pos_iff, hlcnorm, norm_pos_iff]`.

Conclude with `Polynomial.leadingCoeff_ne_zero.2 hdet`. Establish `hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ + ((binMatK (PadicAlgCl p) del c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0`. Rewrite using `[hlcnorm, hcard, hnd]`. Conclude with `hlead`. Establish `hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1`.

Introduce `i j k`. Simplify using `only [hc', halg, norm_algebraMap']`. Conclude with `hc i j k`. Use `set idx : ℤ → ℕ := fun t => (t - (t0 : ℤ)).toNat with hidxdef`. Establish `hidx : ∀ j : ℕ, idx (progr (t0 : ℤ) 1 j) = j`.

Introduce `j`. Simplify using `only [hidxdef, progr]`. Use linear arithmetic over natural numbers and integers. Use `set U' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (U (idx t)) with hU'`. Use `set V' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (V (idx t)) with hV'`.

Use `set dg' : ℤ → Fin n → PadicAlgCl p := fun t b => φ (d (idx t) b) with hdg'`. Establish `hsm : ∀ j ∈ Finset.range Y0, (∀ x y, ‖U' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧ (∀ x y, ‖V' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧ ‖(U' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧ ‖(V' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧ (binMatK (PadicAlgCl p) del c').map (Polynomial.eval ((progr (t0 : ℤ) 1 j : ℤ) : Padi …`. Introduce `j _`. Simplify using `only [hU', hV', hdg', hidx]`. Use `⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hφn]`. Conclude with `PadicInt.norm_le_one _`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hφn]`. Conclude with `PadicInt.norm_le_one _`. Rewrite using `[← RingHom.map_det, hφn]`.

Conclude with `PadicInt.isUnit_iff.1 (hU j)`. Rewrite using `[← RingHom.map_det, hφn]`. Conclude with `PadicInt.isUnit_iff.1 (hV j)`. Establish `e1 : (Matrix.diagonal fun b => φ (d j b)) = φ.mapMatrix (Matrix.diagonal (d j))`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero φ)]`.

Rewrite using `[e1, ← map_mul, ← map_mul, ← hfac j, hAK]`. Use extensionality with `x y`. Establish `hpt' : ((progr (t0 : ℤ) 1 j : ℤ) : PadicAlgCl p) = ((t0 + j : ℕ) : PadicAlgCl p)`. Simplify using `[progr]`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, hpt', Polynomial.eval_natCast_map, ← hM, RingHom.mapMatrix_apply, Matrix.map_apply]`.

Both sides reduce to the same expression. Establish `hE0 : (0 : ℝ) < (k : ℝ) + 1`. Establish `: (0 : ℝ) ≤ (k : ℝ)` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `Formalism.GM.Top.windowFullAP p (PadicAlgCl p) n del h ((k : ℝ) + 1) c' (binMatK (PadicAlgCl p) del c').det.leadingCoeff (binMatK (PadicAlgCl p) del c').det.roots (t0 : ℤ) 1 Y0 La0 U' V' dg' isCoprime_one_left hY0 hYh (by omega) hE0 hleadne hc'norm hsplit hsm hLB'`.

Establish `hYpos : (0 : ℝ) < Y0` using `by exact_mod_cast hY0`. Rewrite `key` using `[div_le_iff₀ hYpos]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hdg', hidx, hφn, PadicInt.norm_def]`.

Use `_ ≤ (n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1)) * Y0 := key`. Use `_ = (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1))) := by ring`.
-/
theorem gramWindow2_proved : GramWindow2 := by
  intro p hp σ n del h Y0 k La0 t0 Ψ e s c hli h1 h2 h3 h4 hY0 hYh hdel hk hc hdet hlead hgram
  classical
  set Aq := binMatK ℚ_[p] del c with hAq

  set cz : Fin n → Fin n → ℕ → ℤ_[p] := fun a b i => ⟨c a b i, hc a b i⟩ with hcz
  have hczc : ∀ a b i, ((cz a b i : ℤ_[p]) : ℚ_[p]) = c a b i := fun _ _ _ => rfl
  set M : ℕ → Matrix (Fin n) (Fin n) ℤ_[p] := fun j a b =>
    ∑ i ∈ Finset.range (del + 1), cz a b i * (((t0 + j).choose i : ℕ) : ℤ_[p]) with hMdef
  have hM : ∀ j a b, ((M j a b : ℤ_[p]) : ℚ_[p]) = (Aq a b).eval (((t0 + j : ℕ) : ℚ_[p])) := by
    intro j a b
    rw [hAq, binMatK_eval_nat]
    simp only [hMdef, PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_natCast, hczc]
  choose U V d hU hV hfac using fun j => Formalism.GM.Top.smithZp p n (M j)

  have hpt : ∀ j ∈ Finset.range Y0,
      (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ) ≤
        ((Finset.univ.filter (fun i => ‖(d j i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) := by
    intro j hj
    obtain ⟨hs0, hs1, hg⟩ := hgram j hj
    have := bad_le_smith n k (Ψ j) e hli (h1 j) (h2 j) (h3 j) (h4 j) (s j) hs0 hs1 (U j) (V j) (d j) (hU j) (hV j)
      (fun a b => by rw [hg a b, ← hfac j, hM, Matrix.map_apply])
    exact_mod_cast this

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set φ : ℤ_[p] →+* PadicAlgCl p := alg.comp PadicInt.Coe.ringHom with hφ
  have hφn : ∀ z : ℤ_[p], ‖φ z‖ = ‖z‖ := by
    intro z
    show ‖alg (z : ℚ_[p])‖ = _
    rw [halg, norm_algebraMap', PadicInt.norm_def]
  set c' : Fin n → Fin n → ℕ → PadicAlgCl p := fun i j k => alg (c i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) del c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg del _
  have hDk : (binMatK (PadicAlgCl p) del c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) del c').det
  have hlc : (binMatK (PadicAlgCl p) del c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, Polynomial.leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) del c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, Polynomial.natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hleadne : (binMatK (PadicAlgCl p) del c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm, norm_pos_iff]
    exact Polynomial.leadingCoeff_ne_zero.2 hdet
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) del c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0 := by
    rw [hlcnorm, hcard, hnd]; exact hlead
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap']
    exact hc i j k
  set idx : ℤ → ℕ := fun t => (t - (t0 : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (t0 : ℤ) 1 j) = j := by
    intro j
    simp only [hidxdef, progr]
    omega
  set U' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (U (idx t)) with hU'
  set V' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (V (idx t)) with hV'
  set dg' : ℤ → Fin n → PadicAlgCl p := fun t b => φ (d (idx t) b) with hdg'
  have hsm : ∀ j ∈ Finset.range Y0, (∀ x y, ‖U' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧
      ‖(U' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧ ‖(V' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) del c').map (Polynomial.eval ((progr (t0 : ℤ) 1 j : ℤ) : PadicAlgCl p)) =
        U' (progr (t0 : ℤ) 1 j) * Matrix.diagonal (dg' (progr (t0 : ℤ) 1 j)) * V' (progr (t0 : ℤ) 1 j) := by
    intro j _
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, hφn]; exact PadicInt.norm_le_one _
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, hφn]; exact PadicInt.norm_le_one _
    · rw [← RingHom.map_det, hφn]; exact PadicInt.isUnit_iff.1 (hU j)
    · rw [← RingHom.map_det, hφn]; exact PadicInt.isUnit_iff.1 (hV j)
    · have e1 : (Matrix.diagonal fun b => φ (d j b)) = φ.mapMatrix (Matrix.diagonal (d j)) := by
        rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero φ)]
      rw [e1, ← map_mul, ← map_mul, ← hfac j, hAK]
      ext x y
      have hpt' : ((progr (t0 : ℤ) 1 j : ℤ) : PadicAlgCl p) = ((t0 + j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      rw [Matrix.map_apply, Matrix.map_apply, hpt', Polynomial.eval_natCast_map, ← hM, RingHom.mapMatrix_apply,
        Matrix.map_apply]
      rfl
  have hE0 : (0 : ℝ) < (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have key := Formalism.GM.Top.windowFullAP p (PadicAlgCl p) n del h ((k : ℝ) + 1) c'
    (binMatK (PadicAlgCl p) del c').det.leadingCoeff (binMatK (PadicAlgCl p) del c').det.roots (t0 : ℤ) 1 Y0 La0
    U' V' dg' isCoprime_one_left hY0 hYh (by omega) hE0 hleadne hc'norm hsplit hsm hLB'
  have hYpos : (0 : ℝ) < Y0 := by exact_mod_cast hY0
  rw [div_le_iff₀ hYpos] at key
  calc (∑ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ))
      ≤ ∑ j ∈ Finset.range Y0,
          ((Finset.univ.filter (fun i => ‖(d j i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) :=
        Finset.sum_le_sum hpt
    _ = ∑ j ∈ Finset.range Y0,
          ((Finset.univ.filter (fun i => ‖dg' (progr (t0 : ℤ) 1 j) i‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hdg', hidx, hφn, PadicInt.norm_def]
    _ ≤ (n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1)) * Y0 := key
    _ = (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1))) := by ring

end Formalism.MainNotions.G.GramWindowAlt

end
