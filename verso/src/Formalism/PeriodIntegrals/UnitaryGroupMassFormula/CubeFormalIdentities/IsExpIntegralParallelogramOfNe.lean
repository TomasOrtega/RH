import Mathlib
import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}

/- English proof (translation)
The claim follows from `coeff_embDomain_rename e F α`.
-/
private theorem coeff_embDomain_rename' (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff (α.embDomain e) (rename e F) = coeff α F :=
  coeff_embDomain_rename e F α

/- English proof (translation)
Apply `coeff_rename_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨α, rfl⟩`. Conclude with `hβ ⟨α, Finsupp.embDomain_eq_mapDomain _ _⟩`.
-/
private theorem coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) {β : τ →₀ ℕ}
    (hβ : ¬ ∃ α : σ →₀ ℕ, α.embDomain e = β) : coeff β (rename e F) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨α, rfl⟩
  exact hβ ⟨α, Finsupp.embDomain_eq_mapDomain _ _⟩

/- English proof (translation)
The claim follows from `constantCoeff_rename e F`.
-/
private theorem constantCoeff_rename_embedding (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) :
    constantCoeff (rename e F) = constantCoeff F :=
  constantCoeff_rename e F

/- English proof (translation)
Take `⟨h0, hI⟩` from `hD`. Establish `h0' : constantCoeff (rename e D) = 0` using `by rw [constantCoeff_rename_embedding]; exact h0`. Use `show constantCoeff (rename e D) = 0 ∧ PI.FglGram.IntegralMv (PI.FglGram.expMv (rename e D))`. Use `⟨h0', ?_⟩` and prove the remaining obligations. Introduce `β`.

Distinguish the cases in `hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β`. Take `⟨α, rfl⟩` from `hβ`. Establish `hα` using `hI α`. Rewrite `hα` using `[coeff_expMv_of_le h0 (α.degree + (α.embDomain e).degree) (Nat.le_add_right _ _)]`. Rewrite using `[coeff_expMv_of_le h0' (α.degree + (α.embDomain e).degree) (Nat.le_add_left _ _)]`.

Establish `hc : ∀ n, coeff (α.embDomain e) (rename e D ^ n) = coeff α (D ^ n)` using `fun n => by`. Rewrite using `[← map_pow, coeff_embDomain_rename']`. Simplify using `only [hc]`. Conclude with `hα`. Rewrite using `[coeff_expMv (rename e D) β]`.

Establish `hz : ∀ n, coeff β (rename e D ^ n) = 0` using `fun n => by`. Rewrite using `[← map_pow]`. Conclude with `coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ`. Simplify using `only [hz, zero_div, Finset.sum_const_zero]`. Simplify using `[PI.FglGram.IsIntP]`.
-/
theorem good_rename (e : σ ↪ τ) {D : MvPowerSeries σ ℂ_[p]} (hD : Good D) : Good (rename e D) := by
  obtain ⟨h0, hI⟩ := hD
  have h0' : constantCoeff (rename e D) = 0 := by rw [constantCoeff_rename_embedding]; exact h0
  show constantCoeff (rename e D) = 0 ∧ PI.FglGram.IntegralMv (PI.FglGram.expMv (rename e D))
  refine ⟨h0', ?_⟩
  intro β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    have hα := hI α
    rw [coeff_expMv_of_le h0 (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _)] at hα
    rw [coeff_expMv_of_le h0' (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e D ^ n) = coeff α (D ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
    exact hα
  · rw [coeff_expMv (rename e D) β]
    have hz : ∀ n, coeff β (rename e D ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, zero_div, Finset.sum_const_zero]
    simp [PI.FglGram.IsIntP]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst a` using `PowerSeries.HasSubst.of_constantCoeff_zero ha`. Rewrite using `[PowerSeries.coeff_subst hs]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]`. Simplify using `only [smul_eq_mul]`. Introduce `n hn`.

Rewrite `hn` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Apply `hn` to reduce the goal to its premises. Establish `h0 : coeff β (a ^ n) = 0`.

Use `coeff_mul_pow_eq_zero ha (1 : MvPowerSeries τ ℂ_[p]) (n := n) (α := β) (by omega)` as an intermediate fact. Simplify using `using this`. Rewrite using `[h0, smul_zero]`.
-/
private theorem coeff_subst_eq_sum_range_of_degree_le {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) (β : τ →₀ ℕ) (N : ℕ) (hN : β.degree ≤ N) :
    coeff β (PowerSeries.subst a g) =
      ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n g * coeff β (a ^ n) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]
  · simp only [smul_eq_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    have h0 : coeff β (a ^ n) = 0 := by
      have := coeff_mul_pow_eq_zero ha (1 : MvPowerSeries τ ℂ_[p]) (n := n) (α := β)
        (by omega)
      simpa using this
    rw [h0, smul_zero]

/- English proof (translation)
Establish `ha' : constantCoeff (rename e a) = 0` using `by rw [constantCoeff_rename_embedding]; exact ha`. Use extensionality with `β`. Distinguish the cases in `hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β`. Take `⟨α, rfl⟩` from `hβ`. Rewrite using `[coeff_embDomain_rename', coeff_subst_eq_sum_range_of_degree_le ha g α (α.degree + (α.embDomain e).degree) (Nat.le_add_right _ _), coeff_subst_eq_sum_range_of_degree_le ha' g _ (α.degree + (α.embDomain e).degree) (Nat.le_add_left _ _)]`.

Establish `hc : ∀ n, coeff (α.embDomain e) (rename e a ^ n) = coeff α (a ^ n)` using `fun n => by`. Rewrite using `[← map_pow, coeff_embDomain_rename']`. Simplify using `only [hc]`. Rewrite using `[coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ, coeff_subst_eq_sum_range_of_degree_le ha' g β β.degree le_rfl]`. Establish `hz : ∀ n, coeff β (rename e a ^ n) = 0` using `fun n => by`.

Rewrite using `[← map_pow]`. Conclude with `coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ`. Simplify using `only [hz, mul_zero, Finset.sum_const_zero]`.
-/
theorem rename_psubst (e : σ ↪ τ) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst a g) = PowerSeries.subst (rename e a) g := by
  have ha' : constantCoeff (rename e a) = 0 := by rw [constantCoeff_rename_embedding]; exact ha
  ext β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    rw [coeff_embDomain_rename', coeff_subst_eq_sum_range_of_degree_le ha g α (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _), coeff_subst_eq_sum_range_of_degree_le ha' g _ (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e a ^ n) = coeff α (a ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
  · rw [coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ, coeff_subst_eq_sum_range_of_degree_le ha' g β β.degree le_rfl]
    have hz : ∀ n, coeff β (rename e a ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Establish `h` using `coeff_subst_eq_sum_range_of_degree_le ha g 0 0 (by simp)`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, h]`. Simplify using the standard rewrite rules.
-/
private theorem constantCoeff_subst_of_zero_lemma_2 {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  have h := coeff_subst_eq_sum_range_of_degree_le ha g 0 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h]
  simp

/- English proof (translation)
Establish `h1` using `constantCoeff_subst_of_zero_lemma_2 (τ := Unit) (a := ex) hex l`. Rewrite `h1` using `[h]`. Rewrite using `[← h1]`. Conclude with `PowerSeries.constantCoeff_X`.
-/
theorem constantCoeff_log_eq_zero {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have h1 := constantCoeff_subst_of_zero_lemma_2 (τ := Unit) (a := ex) hex l
  rw [h] at h1
  rw [← h1]
  exact PowerSeries.constantCoeff_X

section

variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)

include hl in
/- English proof (translation)
Simplify using `only [PI.FglGram.lg]`. Rewrite using `[map_add, constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, add_zero]`.
-/
theorem cc_lg_add (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (lg l a + lg l b) = 0 := by
  simp only [PI.FglGram.lg]
  rw [map_add, constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, add_zero]

include hl in
/- English proof (translation)
Simplify using `only [PI.FglGram.lg]`. Rewrite using `[map_sub, constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, sub_zero]`.
-/
theorem cc_lg_sub (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (lg l a - lg l b) = 0 := by
  simp only [PI.FglGram.lg]
  rw [map_sub, constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, sub_zero]

include hex hl in
/- English proof (translation)
Establish `hsum` using `cc_lg_add hl a b ha hb`. Establish `hF : constantCoeff (PI.FglGram.add l ex a b) = 0`. Simplify using `only [PI.FglGram.add, PI.FglGram.pt]`. Rewrite using `[constantCoeff_subst_of_zero_lemma_2 hsum]`. Conclude with `hex`.

Simplify using `only [PI.FglGram.phAt]`. Rewrite using `[rename_psubst e hF]`. Use `congr 1`. Simplify using `only [PI.FglGram.add, PI.FglGram.pt]`. Rewrite using `[rename_psubst e hsum, map_add]`.

Simplify using `only [PI.FglGram.lg]`. Rewrite using `[rename_psubst e ha, rename_psubst e hb]`.
-/
theorem rename_phAt_add (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (add l ex a b)) = phAt ph (add l ex (rename e a) (rename e b)) := by
  have hsum := cc_lg_add hl a b ha hb
  have hF : constantCoeff (PI.FglGram.add l ex a b) = 0 := by
    simp only [PI.FglGram.add, PI.FglGram.pt]
    rw [constantCoeff_subst_of_zero_lemma_2 hsum]
    exact hex
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e hF]
  congr 1
  simp only [PI.FglGram.add, PI.FglGram.pt]
  rw [rename_psubst e hsum, map_add]
  simp only [PI.FglGram.lg]
  rw [rename_psubst e ha, rename_psubst e hb]

include hex hl in
/- English proof (translation)
Establish `hdif` using `cc_lg_sub hl a b ha hb`. Establish `hF : constantCoeff (PI.FglGram.sub l ex a b) = 0`. Simplify using `only [PI.FglGram.sub, PI.FglGram.pt]`. Rewrite using `[constantCoeff_subst_of_zero_lemma_2 hdif]`. Conclude with `hex`.

Simplify using `only [PI.FglGram.phAt]`. Rewrite using `[rename_psubst e hF]`. Use `congr 1`. Simplify using `only [PI.FglGram.sub, PI.FglGram.pt]`. Rewrite using `[rename_psubst e hdif, map_sub]`.

Simplify using `only [PI.FglGram.lg]`. Rewrite using `[rename_psubst e ha, rename_psubst e hb]`.
-/
theorem rename_phAt_sub (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (sub l ex a b)) = phAt ph (sub l ex (rename e a) (rename e b)) := by
  have hdif := cc_lg_sub hl a b ha hb
  have hF : constantCoeff (PI.FglGram.sub l ex a b) = 0 := by
    simp only [PI.FglGram.sub, PI.FglGram.pt]
    rw [constantCoeff_subst_of_zero_lemma_2 hdif]
    exact hex
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e hF]
  congr 1
  simp only [PI.FglGram.sub, PI.FglGram.pt]
  rw [rename_psubst e hdif, map_sub]
  simp only [PI.FglGram.lg]
  rw [rename_psubst e ha, rename_psubst e hb]

/- English proof (translation)
The claim follows from `rename_X e i`.
-/
private theorem rename_embedding_X (e : σ ↪ τ) (i : σ) :
    rename e (X i : MvPowerSeries σ ℂ_[p]) = X (e i) :=
  rename_X e i

/- English proof (translation)
Establish `h0 : constantCoeff (PI.FglGram.Xv (p` using `p) i) = 0 := constantCoeff_X i`. Establish `h1 : rename e (PI.FglGram.Xv (p` using `p) i) = PI.FglGram.Xv (e i) := rename_embedding_X e i`. Simplify using `only [PI.FglGram.phAt]`. Rewrite using `[rename_psubst e h0, h1]`.
-/
theorem rename_phAt_X (e : σ ↪ τ) (i : σ) :
    rename e (phAt ph (Xv (p := p) i)) = phAt ph (Xv (e i)) := by
  have h0 : constantCoeff (PI.FglGram.Xv (p := p) i) = 0 := constantCoeff_X i
  have h1 : rename e (PI.FglGram.Xv (p := p) i) = PI.FglGram.Xv (e i) := rename_embedding_X e i
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e h0, h1]

include hex hl in

/- English proof (translation)
Establish `hinj : Function.Injective ![i, j]`. Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first`. Consider the case `rfl`. Consider the case `simp_all`.

Set `e : Fin 2 ↪ Fin 3` to `⟨![i, j], hinj⟩`. Establish `c0 : constantCoeff (PI.FglGram.Xv (p` using `p) (0 : Fin 2)) = 0 := constantCoeff_X _`. Establish `c1 : constantCoeff (PI.FglGram.Xv (p` using `p) (1 : Fin 2)) = 0 := constantCoeff_X _`. Establish `r0 : rename e (PI.FglGram.Xv (p` using `p) (0 : Fin 2)) = PI.FglGram.Xv i := rename_embedding_X e 0`. Establish `r1 : rename e (PI.FglGram.Xv (p` using `p) (1 : Fin 2)) = PI.FglGram.Xv j := rename_embedding_X e 1`.

Establish `qa : rename e (PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv (p` using `p) (0 : Fin 2)) (PI.FglGram.Xv 1))) = PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by`. Rewrite using `[rename_phAt_add ph hex hl e _ _ c0 c1, r0, r1]`. Establish `qs : rename e (PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv (p` using `p) (0 : Fin 2)) (PI.FglGram.Xv 1))) = PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by`. Rewrite using `[rename_phAt_sub ph hex hl e _ _ c0 c1, r0, r1]`. Establish `q0 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p` using `p) (0 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv i) := rename_phAt_X ph e 0`.

Establish `q1 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p` using `p) (1 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv j) := rename_phAt_X ph e 1`. Establish `h2` using `good_rename e ((simeq_iff_good _ _).1 hE1)`. Simplify using `only [map_sub, map_add, map_mul, map_ofNat, qa, qs, q0, q1] at h2`. Conclude with `h2`.
-/
theorem isExpIntegral_parallelogram_of_ne (i j : Fin 3) (hij : i ≠ j)
    (hE1 : Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) :
        MvPowerSeries (Fin 2) ℂ_[p]) (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1))) :
    Good (phAt ph (add l ex (Xv i) (Xv j)) + phAt ph (sub l ex (Xv i) (Xv j)) -
      (2 * phAt ph (Xv i) + 2 * phAt ph (Xv j)) : MvPowerSeries (Fin 3) ℂ_[p]) := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | simp_all
  let e : Fin 2 ↪ Fin 3 := ⟨![i, j], hinj⟩
  have c0 : constantCoeff (PI.FglGram.Xv (p := p) (0 : Fin 2)) = 0 := constantCoeff_X _
  have c1 : constantCoeff (PI.FglGram.Xv (p := p) (1 : Fin 2)) = 0 := constantCoeff_X _
  have r0 : rename e (PI.FglGram.Xv (p := p) (0 : Fin 2)) = PI.FglGram.Xv i := rename_embedding_X e 0
  have r1 : rename e (PI.FglGram.Xv (p := p) (1 : Fin 2)) = PI.FglGram.Xv j := rename_embedding_X e 1
  have qa : rename e (PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_add ph hex hl e _ _ c0 c1, r0, r1]
  have qs : rename e (PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_sub ph hex hl e _ _ c0 c1, r0, r1]
  have q0 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (0 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv i) :=
    rename_phAt_X ph e 0
  have q1 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (1 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv j) :=
    rename_phAt_X ph e 1
  have h2 := good_rename e ((simeq_iff_good _ _).1 hE1)
  simp only [map_sub, map_add, map_mul, map_ofNat, qa, qs, q0, q1] at h2
  exact h2

end

/- English proof (translation)
Unfold `PI.FglGram.CubeRelationOfParallelogram`. Introduce `p _ l ex ph hlep hE1 hE3`. Take `⟨hex, hX, -⟩` from `hlep`. Establish `hl` using `constantCoeff_log_eq_zero hex hX`. Establish `product_zeroth_first_parts` using `isExpIntegral_parallelogram_of_ne ph hex hl 0 1 (by decide) hE1`.

Establish `sizeConstantAtParamsWeight` using `isExpIntegral_parallelogram_of_ne ph hex hl 1 2 (by decide) hE1`. Establish `InnerProductFormulaField` using `isExpIntegral_parallelogram_of_ne ph hex hl 2 0 (by decide) hE1`. Establish `H3` using `(simeq_iff_good _ _).1 hE3`. Rewrite using `[simeq_iff_good]`. Establish `key` using `(good_sub ((good_sub ((good_sub H3) product_zeroth_first_parts)) sizeConstantAtParamsWeight)) InnerProductFormulaField`.

Use `key using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cubeRelationOfParallelogram : CubeRelationOfParallelogram := by
  unfold PI.FglGram.CubeRelationOfParallelogram
  intro p _ l ex ph hlep hE1 hE3
  obtain ⟨hex, hX, -⟩ := hlep
  have hl := constantCoeff_log_eq_zero hex hX
  have product_zeroth_first_parts := isExpIntegral_parallelogram_of_ne ph hex hl 0 1 (by decide) hE1
  have sizeConstantAtParamsWeight := isExpIntegral_parallelogram_of_ne ph hex hl 1 2 (by decide) hE1
  have InnerProductFormulaField := isExpIntegral_parallelogram_of_ne ph hex hl 2 0 (by decide) hE1
  have H3 := (simeq_iff_good _ _).1 hE3
  rw [simeq_iff_good]
  have key := (good_sub ((good_sub ((good_sub H3) product_zeroth_first_parts)) sizeConstantAtParamsWeight)) InnerProductFormulaField
  convert key using 1
  ring

end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
