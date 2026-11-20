import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

section Comb

variable {d : ℕ}

/- English proof (translation)
Establish `hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m)` using `by simp`. Use `set u : Fin 2 × Fin d →₀ ℕ := single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 with hu`. Establish `hle : u ≤ n`. Rewrite using `[Finsupp.le_def]`. Introduce `x`.

Simplify using `only [hu, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]`. Apply the tactic sequence `by_cases h0x : ((0 : Fin 2), l) = x <;> by_cases h1x : ((1 : Fin 2), m) = x`. Conclude with `absurd (h0x.trans h1x.symm) hne`. Substitute `h0x` using the available equality. Simplify using `only [if_true, h1x, if_false]`.

Use linear arithmetic over natural numbers and integers. Substitute `h1x` using the available equality. Simplify using `only [if_true, h0x, if_false]`. Use linear arithmetic over natural numbers and integers. Simplify using `[h0x, h1x]`.

Take `⟨w, rfl⟩ : ∃ w, n = u + w` from `⟨n - u, (add_tsub_cancel_of_le hle).symm⟩`. Establish `hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree`. Introduce `a b`. Use `first`. Consider the case `exact map_add _ a b`.

Consider the case `simp [Finsupp.degree_eq_weight_one, map_add]`. Consider the case `simp [Finsupp.degree, Finsupp.sum_add_index']`. Establish `hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1`. Introduce `x`. Use `first`.

Consider the case `exact Finsupp.degree_single x 1`. Consider the case `simp [Finsupp.degree_eq_weight_one]`. Consider the case `simp [Finsupp.degree]`. Establish `hdu : u.degree = 2`. Rewrite using `[hu, hadd, hsg, hsg]`.

Rewrite `hd` using `[hadd, hdu]`. Establish `hw : w.degree = 0` using `by omega`. Rewrite `hw` using `[Finsupp.degree_eq_zero_iff]`. Rewrite using `[hw, add_zero]`.
-/
theorem eq_xz {n : Fin 2 × Fin d →₀ ℕ} {l m : Fin d} (h0 : n (0, l) ≠ 0) (h1 : n (1, m) ≠ 0) (hd : n.degree ≤ 2) :
    n = single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 := by
  have hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m) := by simp
  set u : Fin 2 × Fin d →₀ ℕ := single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 with hu
  have hle : u ≤ n := by
    rw [Finsupp.le_def]
    intro x
    simp only [hu, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases h0x : ((0 : Fin 2), l) = x <;> by_cases h1x : ((1 : Fin 2), m) = x
    · exact absurd (h0x.trans h1x.symm) hne
    · subst h0x
      simp only [if_true, h1x, if_false]
      omega
    · subst h1x
      simp only [if_true, h0x, if_false]
      omega
    · simp [h0x, h1x]
  obtain ⟨w, rfl⟩ : ∃ w, n = u + w := ⟨n - u, (add_tsub_cancel_of_le hle).symm⟩
  have hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree := by
    intro a b
    first
      | exact map_add _ a b
      | simp [Finsupp.degree_eq_weight_one, map_add]
      | simp [Finsupp.degree, Finsupp.sum_add_index']
  have hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1 := by
    intro x
    first
      | exact Finsupp.degree_single x 1
      | simp [Finsupp.degree_eq_weight_one]
      | simp [Finsupp.degree]
  have hdu : u.degree = 2 := by
    rw [hu, hadd, hsg, hsg]
  rw [hadd, hdu] at hd
  have hw : w.degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at hw
  rw [hw, add_zero]

/- English proof (translation)
Rewrite using `[MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial, if_neg]`. Introduce `hle`. Establish `h1` using `Finsupp.le_def.1 hle s`. Simplify using `[hn] at h1`.
-/
theorem coeff_mul_X_eq_zero {σ R : Type*} [CommRing R] (p : MvPowerSeries σ R) (s : σ) (n : σ →₀ ℕ) (hn : n s = 0) :
    coeff n (p * X s) = 0 := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial, if_neg]
  intro hle
  have h1 := Finsupp.le_def.1 hle s
  simp [hn] at h1

end Comb

section Subst

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Use `le_iInf fun s => MvPowerSeries.le_order fun e he => ?_` and prove the remaining obligations. Establish `he0 : e.degree = 0`. Establish `: e.degree < 1` using `by exact_mod_cast he`. Use linear arithmetic over natural numbers and integers. Rewrite `he0` using `[Finsupp.degree_eq_zero_iff]`.

Rewrite using `[he0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `ha s`.
-/
theorem one_le_iInf_order {τ : Type*} (a : Fin 2 × Fin d → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0) :
    (1 : ℕ∞) ≤ ⨅ s, (a s).order := by
  refine le_iInf fun s => MvPowerSeries.le_order fun e he => ?_
  have he0 : e.degree = 0 := by
    have : e.degree < 1 := by exact_mod_cast he
    omega
  rw [Finsupp.degree_eq_zero_iff] at he0
  rw [he0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s

/- English proof (translation)
Use `nontriviality k`. Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Set `g : Fin d × Fin d → (Fin 2 × Fin d →₀ ℕ)` to `fun p => single ((0 : Fin 2), p.1) 1 + single ((1 : Fin 2), p.2) 1`. Establish `hg : Function.Injective g`. Introduce and unpack `⟨l, m⟩ ⟨l', m'⟩ e`.

Establish `e0` using `congrArg (· ((0 : Fin 2), l)) e`. Establish `e1` using `congrArg (· ((1 : Fin 2), m)) e`. Simplify using `only [g, Finsupp.add_apply, single_apply, Prod.mk.injEq] at e0 e1`. Simplify using `only [true_and] at e0 e1`. Establish `n01 : ((1 : Fin 2) = 0) = False` using `by simp`.

Establish `n10 : ((0 : Fin 2) = 1) = False` using `by simp`. Simplify using `only [n01, n10, false_and, and_false, if_false, add_zero, zero_add] at e0 e1`. Apply the tactic sequence `split_ifs at e0 e1 <;> simp_all`. Establish `hprod : ∀ D : Fin 2 × Fin d →₀ ℕ, D.prod (fun s e => a s ^ e) = subst a (monomial D (1 : k))` using `fun D => by`. Rewrite using `[subst_monomial hs, map_one, one_mul]`.

Rewrite using `[coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.image g Finset.univ) ?_, Finset.sum_image (fun p _ q _ e => hg e), ← Finset.univ_product_univ, Finset.sum_product]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m)` using `fun e => absurd (congrArg Prod.fst e) (by simp)`. Rewrite using `[smul_eq_mul]`. Use `congr 2`.

Use `show (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1).prod (fun s e => a s ^ e) = _`. Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Simplify using `[Finsupp.prod_single_index]`. Introduce `D hD`. Rewrite `hD` using `[Function.mem_support]`.

Establish `hc : coeff D h ≠ 0` using `fun e => hD (by rw [e, zero_smul])`. Establish `hp : coeff n (D.prod fun s e => a s ^ e) ≠ 0` using `fun e => hD (by rw [e, smul_zero])`. Establish `hx : ∃ l, D (0, l) ≠ 0`. Assume the negation of the conclusion as `hx`. Use `push Not at hx`.

Conclude with `hc (coeff_eq_zero_of_vanish_first_axis h h0 D hx)`. Establish `hz : ∃ m, D (1, m) ≠ 0`. Assume the negation of the conclusion as `hz`. Use `push Not at hz`. Conclude with `hc (coeff_eq_zero_of_vanish_second_axis h h1 D hz)`.

Take `⟨l, hl⟩` from `hx`. Take `⟨m, hm⟩` from `hz`. Establish `hdeg : D.degree ≤ 2`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Apply `hp` to reduce the goal to its premises. Rewrite using `[hprod]`. Apply `coeff_of_lt_order` to reduce the goal to its premises. Use `lt_of_lt_of_le ?_ (le_order_subst hs _)` and prove the remaining obligations. Rewrite using `[order_monomial_of_ne_zero one_ne_zero, hn]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[eq_xz hl hm hdeg]`. Conclude with `Finset.mem_image.2 ⟨(l, m), Finset.mem_univ _, rfl⟩`.
-/
theorem coeff_subst_xz {τ : Type*} (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (a : Fin 2 × Fin d → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (n : τ →₀ ℕ) (hn : n.degree = 2) :
    coeff n (subst a h) = ∑ l, ∑ m, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1) h *
      coeff n (a (0, l) * a (1, m)) := by
  classical
  nontriviality k
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let g : Fin d × Fin d → (Fin 2 × Fin d →₀ ℕ) := fun p => single ((0 : Fin 2), p.1) 1 + single ((1 : Fin 2), p.2) 1
  have hg : Function.Injective g := by
    rintro ⟨l, m⟩ ⟨l', m'⟩ e
    have e0 := congrArg (· ((0 : Fin 2), l)) e
    have e1 := congrArg (· ((1 : Fin 2), m)) e
    simp only [g, Finsupp.add_apply, single_apply, Prod.mk.injEq] at e0 e1
    simp only [true_and] at e0 e1
    have n01 : ((1 : Fin 2) = 0) = False := by simp
    have n10 : ((0 : Fin 2) = 1) = False := by simp
    simp only [n01, n10, false_and, and_false, if_false, add_zero, zero_add] at e0 e1
    split_ifs at e0 e1 <;> simp_all
  have hprod : ∀ D : Fin 2 × Fin d →₀ ℕ, D.prod (fun s e => a s ^ e) = subst a (monomial D (1 : k)) := fun D => by
    rw [subst_monomial hs, map_one, one_mul]
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.image g Finset.univ) ?_,
    Finset.sum_image (fun p _ q _ e => hg e), ← Finset.univ_product_univ, Finset.sum_product]
  · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    have hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m) := fun e => absurd (congrArg Prod.fst e) (by simp)
    rw [smul_eq_mul]
    congr 2
    show (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1).prod (fun s e => a s ^ e) = _
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp [Finsupp.prod_single_index]
  · intro D hD
    rw [Function.mem_support] at hD
    have hc : coeff D h ≠ 0 := fun e => hD (by rw [e, zero_smul])
    have hp : coeff n (D.prod fun s e => a s ^ e) ≠ 0 := fun e => hD (by rw [e, smul_zero])
    have hx : ∃ l, D (0, l) ≠ 0 := by
      by_contra hx; push Not at hx; exact hc (coeff_eq_zero_of_vanish_first_axis h h0 D hx)
    have hz : ∃ m, D (1, m) ≠ 0 := by
      by_contra hz; push Not at hz; exact hc (coeff_eq_zero_of_vanish_second_axis h h1 D hz)
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hz
    have hdeg : D.degree ≤ 2 := by
      by_contra hlt
      push Not at hlt
      apply hp
      rw [hprod]
      apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (le_order_subst hs _)
      rw [order_monomial_of_ne_zero one_ne_zero, hn]
      calc ((2 : ℕ) : ℕ∞) < (D.degree : ℕ∞) := by exact_mod_cast hlt
        _ = 1 * (D.degree : ℕ∞) := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (one_le_iInf_order a ha) le_rfl
    rw [eq_xz hl hm hdeg]
    exact Finset.mem_image.2 ⟨(l, m), Finset.mem_univ _, rfl⟩

end Subst

section Main

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

/- English proof (translation)
Rewrite using `[rename_eq_subst]`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, i⟩` from `p`.

Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem eval_first_point_rename (φ : PS k 1 d) : ev (n := 2) ![pt k d 0] φ = rename (eXv d) φ := by
  rw [rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

/- English proof (translation)
Rewrite using `[rename_eq_subst]`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, i⟩` from `p`.

Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem eval_second_point_rename (φ : PS k 1 d) : ev (n := 2) ![pt k d 1] φ = rename (eZ d) φ := by
  rw [rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

/- English proof (translation)
Establish `hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree`. Introduce `a b`. Use `first`. Consider the case `exact map_add _ a b`. Consider the case `simp [Finsupp.degree_eq_weight_one, map_add]`.

Consider the case `simp [Finsupp.degree, Finsupp.sum_add_index']`. Establish `hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1`. Introduce `x`. Use `first`. Consider the case `exact Finsupp.degree_single x 1`.

Consider the case `simp [Finsupp.degree_eq_weight_one]`. Consider the case `simp [Finsupp.degree]`. Rewrite using `[hadd, hsg, hsg]`.
-/
theorem degree_xz (j i : Fin d) : (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1).degree = 2 := by
  have hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree := by
    intro a b
    first
      | exact map_add _ a b
      | simp [Finsupp.degree_eq_weight_one, map_add]
      | simp [Finsupp.degree, Finsupp.sum_add_index']
  have hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1 := by
    intro x
    first
      | exact Finsupp.degree_single x 1
      | simp [Finsupp.degree_eq_weight_one]
      | simp [Finsupp.degree]
  rw [hadd, hsg, hsg]

/- English proof (translation)
Distinguish the cases in `hm : m = i`. Substitute `hm` using the available equality. Rewrite using `[if_pos rfl]`. Establish `e : single ((0 : Fin 2), j) 1 = embDomain (eXv d) (single ((0 : Fin 1), j) 1)`. Rewrite using `[embDomain_single]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Use `show coeff _ (_ * monomial (single ((1 : Fin 2), m) 1) 1) = _`. Rewrite using `[coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]`. Apply the tactic sequence `try rw [mul_one]`.

Rewrite using `[coeff_embDomain_rename]`. Rewrite using `[if_neg hm]`. Apply `coeff_mul_X_eq_zero` to reduce the goal to its premises. Simplify using `[single_apply, Ne.symm hm]`.
-/
theorem coeff_xz_mul_X (φ : PS k 1 d) (j i m : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (rename (eXv d) φ * X ((1 : Fin 2), m)) =
      if m = i then coeff (single ((0 : Fin 1), j) 1) φ else 0 := by
  classical
  by_cases hm : m = i
  · subst hm
    rw [if_pos rfl]
    have e : single ((0 : Fin 2), j) 1 = embDomain (eXv d) (single ((0 : Fin 1), j) 1) := by
      rw [embDomain_single]; rfl
    rw [e]
    show coeff _ (_ * monomial (single ((1 : Fin 2), m) 1) 1) = _
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]
    try rw [mul_one]
    rw [coeff_embDomain_rename]
  · rw [if_neg hm]
    apply coeff_mul_X_eq_zero
    simp [single_apply, Ne.symm hm]

/- English proof (translation)
Rewrite using `[mul_comm, add_comm]`. Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Rewrite using `[if_pos rfl]`. Establish `e : single ((1 : Fin 2), i) 1 = embDomain (eZ d) (single ((0 : Fin 1), i) 1)`.

Rewrite using `[embDomain_single]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `show coeff _ (_ * monomial (single ((0 : Fin 2), l) 1) 1) = _`. Rewrite using `[coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]`.

Apply the tactic sequence `try rw [mul_one]`. Rewrite using `[coeff_embDomain_rename]`. Rewrite using `[if_neg hl]`. Apply `coeff_mul_X_eq_zero` to reduce the goal to its premises. Simplify using `[single_apply, Ne.symm hl]`.
-/
theorem coeff_xz_X_mul (ψ : PS k 1 d) (j i l : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (X ((0 : Fin 2), l) * rename (eZ d) ψ) =
      if l = j then coeff (single ((0 : Fin 1), i) 1) ψ else 0 := by
  classical
  rw [mul_comm, add_comm]
  by_cases hl : l = j
  · subst hl
    rw [if_pos rfl]
    have e : single ((1 : Fin 2), i) 1 = embDomain (eZ d) (single ((0 : Fin 1), i) 1) := by
      rw [embDomain_single]; rfl
    rw [e]
    show coeff _ (_ * monomial (single ((0 : Fin 2), l) 1) 1) = _
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]
    try rw [mul_one]
    rw [coeff_embDomain_rename]
  · rw [if_neg hl]
    apply coeff_mul_X_eq_zero
    simp [single_apply, Ne.symm hl]

/- English proof (translation)
Simplify using `only [FB.actK]`. Rewrite using `[constantCoeff_map, B.A.const, map_zero]`.
-/
theorem const_actK (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by
  simp only [FB.actK]
  rw [constantCoeff_map, B.A.const, map_zero]

/- English proof (translation)
Unfold `ev`. Rewrite using `[coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `e0 : ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((0, l) : Fin 2 × Fin d).1 ((0, l) : Fin 2 × Fin d).2 = rename (eXv d) (B.actK k a l)` using `eval_first_point_rename _`. Establish `e1 : ∀ m : Fin d, ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((1, m) : Fin 2 × Fin d).1 ((1, m) : Fin 2 × Fin d).2 = X ((1 : Fin 2), m)` using `fun m => rfl`.

Simplify using `only [e0, e1, coeff_xz_mul_X, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Introduce and unpack `⟨j', i'⟩ fin_cases j'`. Use `show constantCoeff (ev (n := 2) ![pt k d 0] (B.actK k a i')) = 0`. Rewrite using `[eval_first_point_rename, constantCoeff_rename, const_actK]`.

Conclude with `constantCoeff_X _`.
-/
theorem coeff_ad_side1 (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)
        (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h) =
      ∑ l, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), i) 1) h * dAct k B a l j := by
  classical
  unfold ev
  rw [coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have e0 : ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((0, l) : Fin 2 × Fin d).1 ((0, l) : Fin 2 × Fin d).2 =
        rename (eXv d) (B.actK k a l) := eval_first_point_rename _
    have e1 : ∀ m : Fin d, ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((1, m) : Fin 2 × Fin d).1
        ((1, m) : Fin 2 × Fin d).2 = X ((1 : Fin 2), m) := fun m => rfl
    simp only [e0, e1, coeff_xz_mul_X, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rintro ⟨j', i'⟩
    fin_cases j'
    · show constantCoeff (ev (n := 2) ![pt k d 0] (B.actK k a i')) = 0
      rw [eval_first_point_rename, constantCoeff_rename, const_actK]
    · exact constantCoeff_X _

/- English proof (translation)
Unfold `ev`. Rewrite using `[coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]`. Establish `e0 : ∀ l : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((0, l) : Fin 2 × Fin d).1 ((0, l) : Fin 2 × Fin d).2 = X ((0 : Fin 2), l)` using `fun l => rfl`. Establish `e1 : ∀ m : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((1, m) : Fin 2 × Fin d).1 ((1, m) : Fin 2 × Fin d).2 = rename (eZ d) (B.actK k (star a) m)` using `fun m => eval_second_point_rename _`. Simplify using `only [e0, e1, coeff_xz_X_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Introduce and unpack `⟨j', i'⟩ fin_cases j'`. Conclude with `constantCoeff_X _`.

Use `show constantCoeff (ev (n := 2) ![pt k d 1] (B.actK k (star a) i')) = 0`. Rewrite using `[eval_second_point_rename, constantCoeff_rename, const_actK]`.
-/
theorem coeff_ad_side2 (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)
        (ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) =
      ∑ m, coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), m) 1) h * dAct k B (star a) m i := by
  classical
  unfold ev
  rw [coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]
  · have e0 : ∀ l : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((0, l) : Fin 2 × Fin d).1
        ((0, l) : Fin 2 × Fin d).2 = X ((0 : Fin 2), l) := fun l => rfl
    have e1 : ∀ m : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((1, m) : Fin 2 × Fin d).1
        ((1, m) : Fin 2 × Fin d).2 = rename (eZ d) (B.actK k (star a) m) := fun m => eval_second_point_rename _
    simp only [e0, e1, coeff_xz_X_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rintro ⟨j', i'⟩
    fin_cases j'
    · exact constantCoeff_X _
    · show constantCoeff (ev (n := 2) ![pt k d 1] (B.actK k (star a) i')) = 0
      rw [eval_second_point_rename, constantCoeff_rename, const_actK]

end Main

section Final

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

/- English proof (translation)
Apply `coeff_of_lt_order` to reduce the goal to its premises. Unfold `ev`. Use `lt_of_lt_of_le ?_ (le_order_subst (hasSubst_of_constantCoeff_zero (a := fun p : Fin 2 × Fin d => a' p.1 p.2) (fun p => ha' p.1 p.2)) h)` and prove the remaining obligations. Establish `h2 : (2 : ℕ∞) ≤ h.order` using `nat_le_order (coeff_eq_zero_of_axes h hc.ax0 hc.ax1)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coeff_ev_low (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a' : Fin 2 → Pt k 2 d)
    (ha' : ∀ j i, constantCoeff (a' j i) = 0) (e : Fin 2 × Fin d →₀ ℕ) (he : e.degree < 2) :
    coeff e (ev (n := 2) a' h) = 0 := by
  apply coeff_of_lt_order
  unfold ev
  refine lt_of_lt_of_le ?_ (le_order_subst (hasSubst_of_constantCoeff_zero (a := fun p : Fin 2 × Fin d => a' p.1 p.2)
    (fun p => ha' p.1 p.2)) h)
  have h2 : (2 : ℕ∞) ≤ h.order := nat_le_order (coeff_eq_zero_of_axes h hc.ax0 hc.ax1)
  calc (e.degree : ℕ∞) < 2 := by exact_mod_cast he
    _ = 1 * 2 := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (one_le_iInf_order _ (fun p => ha' p.1 p.2)) h2

/- English proof (translation)
Establish `k0 : ∀ i', constantCoeff (comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i') = 0` using `fun i' => by`. Establish `: comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i' = rename (eXv d) (B.actK k a i')` using `eval_first_point_rename _`. Rewrite using `[this, constantCoeff_rename, const_actK]`. Establish `k1 : ∀ i', constantCoeff (comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i') = 0` using `fun i' => by`. Establish `: comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i' = rename (eZ d) (B.actK k (star a) i')` using `eval_second_point_rename _`.

Rewrite using `[this, constantCoeff_rename, const_actK]`. Establish `kX : ∀ (j' : Fin 2) (i' : Fin d), constantCoeff (pt k d j' i' : PS k 2 d) = 0` using `fun j' i' => constantCoeff_X _`. Establish `c1 : ∀ j' i', constantCoeff ((![comp1 (B.actK k a) (pt k d 0), pt k d 1] : Fin 2 → Pt k 2 d) j' i') = 0`. Introduce `j' i'`. Use `fin_cases j'`.

Use `exacts [k0 i', kX 1 i']`. Establish `c2 : ∀ j' i', constantCoeff ((![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] : Fin 2 → Pt k 2 d) j' i') = 0`. Introduce `j' i'`. Use `fin_cases j'`. Use `exacts [kX 0 i', k1 i']`.

Establish `hord : ∀ e : Fin 2 × Fin d →₀ ℕ, e.degree < 2 → coeff e (ev (n` using `2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := fun e he => by`. Rewrite using `[map_sub, coeff_ev_low B h hc _ c1 e he, coeff_ev_low B h hc _ c2 e he, sub_zero]`. Establish `e` using `congrArg (coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)) (hc.ad a)`. Rewrite `e` using `[coeff_expS_two _ hord _ (degree_xz j i), map_sub, coeff_ad_side1 B h hc a i j, coeff_ad_side2 B h hc a i j, coeff_map]`. Use `⟨-coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (B.ad a), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_neg, e]`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, gaugeBilinearTerm_eq_neg_double_sum, neg_mul, mul_neg, Finset.sum_neg_distrib]`. Establish `hc2 : ∑ x, dAct k B (star a) x i * coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), x) 1) h = ∑ m, coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), m) 1) h * dAct k B (star a) m i` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[hc2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem M_int (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    (sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h) i j ∈ (algebraMap R k).range := by
  have k0 : ∀ i', constantCoeff (comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i' = rename (eXv d) (B.actK k a i') := eval_first_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have k1 : ∀ i', constantCoeff (comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i' = rename (eZ d) (B.actK k (star a) i') :=
      eval_second_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have kX : ∀ (j' : Fin 2) (i' : Fin d), constantCoeff (pt k d j' i' : PS k 2 d) = 0 := fun j' i' => constantCoeff_X _
  have c1 : ∀ j' i', constantCoeff ((![comp1 (B.actK k a) (pt k d 0), pt k d 1] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [k0 i', kX 1 i']
  have c2 : ∀ j' i', constantCoeff ((![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [kX 0 i', k1 i']
  have hord : ∀ e : Fin 2 × Fin d →₀ ℕ, e.degree < 2 → coeff e (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := fun e he => by
    rw [map_sub, coeff_ev_low B h hc _ c1 e he, coeff_ev_low B h hc _ c2 e he, sub_zero]
  have e := congrArg (coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)) (hc.ad a)
  rw [coeff_expS_two _ hord _ (degree_xz j i), map_sub, coeff_ad_side1 B h hc a i j, coeff_ad_side2 B h hc a i j,
    coeff_map] at e
  refine ⟨-coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (B.ad a), ?_⟩
  rw [map_neg, e]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, gaugeBilinearTerm_eq_neg_double_sum, neg_mul, mul_neg,
    Finset.sum_neg_distrib]
  have hc2 : ∑ x, dAct k B (star a) x i * coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), x) 1) h =
      ∑ m, coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), m) 1) h * dAct k B (star a) m i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc2]
  ring

/- English proof (translation)
Introduce `R _ d O _ _ k _ _ _ _ B h hc a ξ hξ`. Take `⟨u, φ, rfl⟩` from `hξ`. Establish `hA : ∀ (b : O) (i j : Fin d), dAct k B b i j = algebraMap R k (coeff (single ((0 : Fin 1), j) 1) (B.A.act b i))` using `fun b i j => by`. Unfold `dAct FB.actK`. Rewrite using `[coeff_map]`.

Use `choose M hM using fun i j => M_int B h hc a i j`. Use `set S := sg1 k h`. Use `set vu : Fin d → k := fun j => algebraMap R k (u j)`. Use `set vφ : Fin d → k := fun j => algebraMap R k (φ j)`. Set `u₂ : Fin d → R` to `fun i => ∑ j, coeff (single ((0 : Fin 1), j) 1) (B.A.act a i) * u j`.

Set `φ₂ : Fin d → R` to `fun i => ∑ j, coeff (single ((0 : Fin 1), i) 1) (B.A.act (star a) j) * φ j + ∑ j, M i j * u j`. Establish `hu₂ : (fun i => algebraMap R k (u₂ i)) = (dAct k B a).mulVec vu` using `funext fun i => by`. Simplify using `only [u₂, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, vu]`. Establish `hφ₂ : (fun i => algebraMap R k (φ₂ i)) = (dAct k B (star a)).transpose.mulVec vφ + (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu` using `funext fun i => by`. Simplify using `only [φ₂, map_add, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, hM, Matrix.transpose_apply, Pi.add_apply, vu, vφ]`.

Use `⟨u₂, φ₂, Prod.ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `hu₂.symm`. Use `show (dAct k B (star a)).transpose.mulVec (fun i => vφ i - S.mulVec vu i) = fun i => algebraMap R k (φ₂ i) - S.mulVec (fun j => algebraMap R k (u₂ j)) i`. Rewrite using `[hu₂]`. Establish `hφi : ∀ i, algebraMap R k (φ₂ i) = ((dAct k B (star a)).transpose.mulVec vφ + (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu) i` using `fun i => congrFun hφ₂ i`.

Simplify using `only [hφi]`. Establish `e1 : (fun i => vφ i - S.mulVec vu i) = vφ - S.mulVec vu` using `rfl`. Rewrite using `[e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauge_stable : ReciprocityTheory.ChartRestriction.G.TB.HStableSt := by
  intro R _ d O _ _ k _ _ _ _ B h hc a ξ hξ
  obtain ⟨u, φ, rfl⟩ := hξ
  have hA : ∀ (b : O) (i j : Fin d),
      dAct k B b i j = algebraMap R k (coeff (single ((0 : Fin 1), j) 1) (B.A.act b i)) := fun b i j => by
    unfold dAct FB.actK; rw [coeff_map]
  choose M hM using fun i j => M_int B h hc a i j
  set S := sg1 k h
  set vu : Fin d → k := fun j => algebraMap R k (u j)
  set vφ : Fin d → k := fun j => algebraMap R k (φ j)
  let u₂ : Fin d → R := fun i => ∑ j, coeff (single ((0 : Fin 1), j) 1) (B.A.act a i) * u j
  let φ₂ : Fin d → R := fun i => ∑ j, coeff (single ((0 : Fin 1), i) 1) (B.A.act (star a) j) * φ j + ∑ j, M i j * u j
  have hu₂ : (fun i => algebraMap R k (u₂ i)) = (dAct k B a).mulVec vu := funext fun i => by
    simp only [u₂, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, vu]
  have hφ₂ : (fun i => algebraMap R k (φ₂ i)) = (dAct k B (star a)).transpose.mulVec vφ +
      (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu := funext fun i => by
    simp only [φ₂, map_add, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, hM, Matrix.transpose_apply,
      Pi.add_apply, vu, vφ]
  refine ⟨u₂, φ₂, Prod.ext ?_ ?_⟩
  · exact hu₂.symm
  · show (dAct k B (star a)).transpose.mulVec (fun i => vφ i - S.mulVec vu i) =
      fun i => algebraMap R k (φ₂ i) - S.mulVec (fun j => algebraMap R k (u₂ j)) i
    rw [hu₂]
    have hφi : ∀ i, algebraMap R k (φ₂ i) = ((dAct k B (star a)).transpose.mulVec vφ +
        (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu) i := fun i => congrFun hφ₂ i
    simp only [hφi]
    have e1 : (fun i => vφ i - S.mulVec vu i) = vφ - S.mulVec vu := rfl
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

end Final

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
