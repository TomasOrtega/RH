import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSStrict

/- English proof (translation)
Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg q)]`. Simplify using the standard rewrite rules.
-/
theorem qpow (q : ℕ) (x : ℝ) : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
  simp

/- English proof (translation)
Rewrite using `[qpow]`. Simplify using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem pair_val (q : ℕ) (γ : ℂˣ) (x : ℝ) :
    (γ : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(x : ℂ)) =
      ((‖(γ : ℂ)‖ ^ 2 * (q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [qpow]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem norm_conjU (γ : ℂˣ) : ‖((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ)‖ = ‖(γ : ℂ)‖ := by
  simp

/- English proof (translation)
Establish `h1' : HasProd ({v | v ∉ T}.mulIndicator f) A` using `(hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1`. Establish `h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B` using `(hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2`. Establish `h3 : HasProd (({w} : Set ι).mulIndicator f) (f w)`. Use `hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])` as an intermediate fact. Simplify using `using this`.

Establish `h4` using `h3.mul h2'`. Establish `heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) = {v | v ∉ T}.mulIndicator f`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Simplify using `[Set.mulIndicator_apply, hw]`. Apply the tactic sequence `by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]`. Rewrite `h4` using `[heq]`. Conclude with `h1'.unique h4`.
-/
theorem hasProd_split {ι : Type*} [DecidableEq ι] (f : ι → ℂ) (T : Finset ι) (w : ι) (hw : w ∉ T) {A B : ℂ}
    (h1 : HasProd (fun v : {v : ι // v ∉ T} => f v.1) A)
    (h2 : HasProd (fun v : {v : ι // v ∉ insert w T} => f v.1) B) : A = f w * B := by
  have h1' : HasProd ({v | v ∉ T}.mulIndicator f) A :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1
  have h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2
  have h3 : HasProd (({w} : Set ι).mulIndicator f) (f w) := by
    have := hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])
    simpa using this
  have h4 := h3.mul h2'
  have heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) =
      {v | v ∉ T}.mulIndicator f := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [Set.mulIndicator_apply, hw]
    · by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]
  rw [heq] at h4
  exact h1'.unique h4

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]`. Establish `ha` using `h a (Multiset.mem_cons_self a s)`.

Establish `hs` using `ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem half_pow_le_norm_prod {α : Type*} (g : α → ℂ) (m : Multiset α) (h : ∀ p ∈ m, (1/2 : ℝ) ≤ ‖g p‖) :
    (1/2 : ℝ) ^ Multiset.card m ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))
    calc (1/2 : ℝ) ^ Multiset.card s * (1/2) = (1/2) * (1/2) ^ Multiset.card s := mul_comm _ _
      _ ≤ _ := mul_le_mul ha hs (by positivity) (norm_nonneg _)

/- English proof (translation)
Establish `hpos : 0 < ‖1 - z‖`. Use `norm_sub_norm_le (1 : ℂ) z` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ‖1 - z‖ ≤ 2`.

Use `norm_sub_le (1 : ℂ) z` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_inv, one_div]`. Conclude with `inv_anti₀ hpos hle`.
-/
theorem half_le_norm_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : (1/2 : ℝ) ≤ ‖(1 - z)⁻¹‖ := by
  have hpos : 0 < ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simp at this; linarith
  have hle : ‖1 - z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) z
    simp at this; linarith
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

def gfac (q : ℕ) (x : ℝ) (p : ℂˣ × ℂˣ) : ℂ := (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locL_eq (q : ℕ) (B B' : Multiset ℂˣ) (x : ℝ) : locL q B B' (x : ℂ) = ((B ×ˢ B').map (gfac q x)).prod := rfl

/- English proof (translation)
Introduce `E _ _ _ a σ ha hσ T hT w hw α hα`. Take `⟨L1, hL1, -, c1, hc1, hlim1⟩` from `GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT`. Establish `hT' : UnrOutside (insert w T) σ` using `fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))`. Take `⟨L2, hL2, -, c2, hc2, hlim2⟩` from `GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'`. Establish `hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ)`.

Introduce `x hx`. Rewrite using `[← locL_eq]`. Establish `e` using `hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal) (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1`. Conclude with `e`. Generalize the expression as in `hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit`.

Establish `hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B'` using `fun γ hγ => Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩`. Generalize the expression as in `hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢`. Establish `hq1 : (1 : ℝ) < q` using `by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Establish `hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ)`.

Introduce `γ hγ`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2`. Establish `: (γ : ℂ) ≠ 0` using `γ.ne_zero`.

Check the signs of the components of the expression. Establish `hlogq : 0 < Real.log q` using `Real.log_pos hq1`. Use `set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def`. Establish `hx0 : 1 < x0`. Rewrite using `[hx0def, lt_div_iff₀ hlogq, one_mul]`.

Conclude with `Real.log_lt_log hq0 hlt`. Establish `hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹`. Rewrite using `[Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]`. Use `congr 1`. Establish `: Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2)`.

Rewrite using `[hx0def]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Real.exp_log hγ0]`. Establish `hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0`. Apply `Multiset.prod_eq_zero` to reduce the goal to its premises.

Use `Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩` and prove the remaining obligations. Simplify using `only [gfac]`. Rewrite using `[pair_val, hpow, mul_inv_cancel₀ hγ0.ne']`. Simplify using the standard rewrite rules. Establish `h` using `hsplit x0 hx0`.

Rewrite `h` using `[hF0, zero_mul]`. Establish `h1` using `(hL1 x0 hx0).2`. Establish `: L1 x0 = 0` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hnot`.

Use `push_neg at hnot`. Establish `heq : ‖(α : ℂ)‖ ^ 2 = q` using `le_antisymm (hle α hα) hnot`. Use `set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht`. Establish `ht1 : ∀ x, 1 < x → t x < 1`. Introduce `x hx`.

Establish `: (q : ℝ) ^ (1 + -x) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)`. Rewrite `this` using `[Real.rpow_add hq0, Real.rpow_one]`. Then use the resulting hypothesis. Take `⟨rest, hrest⟩` from `Multiset.exists_cons_of_mem (hmem α hα)`. Establish `hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤ (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖`. Introduce `x hx`.

Establish `hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹`. Simplify using `only [gfac]`. Rewrite using `[pair_val, heq]`. Simplify using `only [ht]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖`. Introduce `p hp`. Establish `hp' : p ∈ (sat σ w) ×ˢ B'`. Rewrite using `[hrest]`.

Conclude with `Multiset.mem_cons_of_mem hp`. Take `⟨hp1, hp2⟩` from `Multiset.mem_product.mp hp'`. Rewrite `hp2` using `[← hB']`. Take `⟨β, hβ, hβe⟩` from `Multiset.mem_map.mp hp2`. Establish `hb1` using `hle p.1 hp1`.

Establish `hb2` using `hle β hβ`. Establish `hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖` using `by rw [← hβe]; exact norm_conjU β`. Establish `hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q`. Rewrite using `[hn2]`. Use polynomial arithmetic with `[sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]`.

Apply `half_le_norm_inv_one_sub` to reduce the goal to its premises. Rewrite using `[qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 < 1 - t x` using `by linarith [ht1 x hx]`. Rewrite using `[hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]`.

Conclude with `half_pow_le_norm_prod (gfac q x) rest hrestb`. Establish `hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x)`. Introduce `x hx`. Establish `h` using `hsplit x hx`. Establish `hL2pos : 0 < L2 x` using `by linarith [(hL2 x hx).2]`.

Establish `hL1pos : 0 < L1 x` using `by linarith [(hL1 x hx).2]`. Establish `hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ)`. Use `push_cast`. Rewrite using `[h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]`. Rewrite using `[hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos), mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]`.

Establish `htlim : Tendsto t (𝓝[>] 1) (𝓝 1)`. Establish `hc : Continuous t` using `continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))`. Use `hc.tendsto 1` as an intermediate fact. Simplify using `only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this`. Conclude with `tendsto_nhdsWithin_of_tendsto_nhds this`.

Establish `hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0)`. Use `((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')` as an intermediate fact. Simplify using `using this`. Establish `hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) < (1/2 : ℝ) ^ Multiset.card rest` using `hlim (gt_mem_nhds (by positivity))`. Establish `hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x` using `self_mem_nhdsWithin`.

Take `⟨x, hx1, hx2⟩` from `(hev1.and hev2).exists`. Use `hlow x hx2` as an intermediate fact. Rewrite `this` using `[hnorm x hx2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sq_lt_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a →
    σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w,
      ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ _ a σ ha hσ T hT w hw α hα
  classical
  obtain ⟨L1, hL1, -, c1, hc1, hlim1⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  have hT' : UnrOutside (insert w T) σ := fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))
  obtain ⟨L2, hL2, -, c2, hc2, hlim2⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'
  have hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map
      (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ) := by
    intro x hx
    rw [← locL_eq]
    have e := hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal)
      (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1
    exact e
  generalize hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit
  have hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B' := fun γ hγ =>
    Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩
  generalize hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢
  have hq1 : (1 : ℝ) < q := by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith

  have hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ) := by
    intro γ hγ
    by_contra hlt
    push_neg at hlt
    have hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2 := by
      have : (γ : ℂ) ≠ 0 := γ.ne_zero
      positivity
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def
    have hx0 : 1 < x0 := by
      rw [hx0def, lt_div_iff₀ hlogq, one_mul]
      exact Real.log_lt_log hq0 hlt
    have hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]
      congr 1
      have : Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2) := by
        rw [hx0def]; field_simp
      rw [this, Real.exp_log hγ0]
    have hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0 := by
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩
      simp only [gfac]
      rw [pair_val, hpow, mul_inv_cancel₀ hγ0.ne']
      simp
    have h := hsplit x0 hx0
    rw [hF0, zero_mul] at h
    have h1 := (hL1 x0 hx0).2
    have : L1 x0 = 0 := by exact_mod_cast h
    linarith
  by_contra hnot
  push_neg at hnot
  have heq : ‖(α : ℂ)‖ ^ 2 = q := le_antisymm (hle α hα) hnot
  set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht
  have ht1 : ∀ x, 1 < x → t x < 1 := by
    intro x hx
    have : (q : ℝ) ^ (1 + -x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rwa [Real.rpow_add hq0, Real.rpow_one] at this
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem (hmem α hα)

  have hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤
      (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ := by
    intro x hx
    have hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹ := by
      simp only [gfac]
      rw [pair_val, heq]
      simp only [ht]
      push_cast
      ring
    have hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖ := by
      intro p hp
      have hp' : p ∈ (sat σ w) ×ˢ B' := by
        rw [hrest]; exact Multiset.mem_cons_of_mem hp
      obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hp'
      rw [← hB'] at hp2
      obtain ⟨β, hβ, hβe⟩ := Multiset.mem_map.mp hp2
      have hb1 := hle p.1 hp1
      have hb2 := hle β hβ
      have hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖ := by rw [← hβe]; exact norm_conjU β
      have hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q := by
        rw [hn2]
        nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]
      apply half_le_norm_inv_one_sub
      rw [qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
      calc ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ * (q : ℝ) ^ (-x) ≤ q * (q : ℝ) ^ (-x) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hq0.le _)
        _ < 1 := ht1 x hx
    have hpos : 0 < 1 - t x := by linarith [ht1 x hx]
    rw [hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    exact half_pow_le_norm_prod (gfac q x) rest hrestb

  have hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x) := by
    intro x hx
    have h := hsplit x hx
    have hL2pos : 0 < L2 x := by linarith [(hL2 x hx).2]
    have hL1pos : 0 < L1 x := by linarith [(hL1 x hx).2]
    have hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ) := by
      push_cast
      rw [h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]
    rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos),
      mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]
  have htlim : Tendsto t (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous t := continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))
    have := hc.tendsto 1
    simp only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')
    simpa using this
  have hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) <
      (1/2 : ℝ) ^ Multiset.card rest := hlim (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
  have := hlow x hx2
  rw [hnorm x hx2] at this
  linarith

end GlobalTheory.RSStrict
