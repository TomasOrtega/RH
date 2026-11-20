import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

/- English proof (translation)
Establish `h2` using `congrArg (coeff n) h`. Rewrite `h2` using `[← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (fun s => by simp), map_smul, smul_eq_mul]`. Simplify using `only [← pow_mul, Finset.prod_pow_eq_pow_sum] at h2`. Establish `hr : ((2 : ℚ) ^ (∑ s, w s * n s) - 2) ≠ 0`. Introduce `h0`.

Apply `hn` to reduce the goal to its premises. Establish `h3 : (2 : ℕ) ^ (∑ s, w s * n s) = 2` using `by exact_mod_cast sub_eq_zero.1 h0`. Conclude with `Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)`. Establish `hk : algebraMap ℚ k ((2 : ℚ) ^ (∑ s, w s * n s) - 2) * coeff n f = 0`. Rewrite using `[map_sub, map_pow, map_ofNat]`.

Take the linear combination `h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coeff_zero_of_scale {σ : Type} [Fintype σ] (w : σ → ℕ) (f : MvPowerSeries σ k)
    (h : subst ((fun s => (2 : k) ^ w s) • (X : σ → MvPowerSeries σ k)) f = (2 : k) • f) (n : σ →₀ ℕ)
    (hn : (∑ s, w s * n s) ≠ 1) : coeff n f = 0 := by
  have h2 := congrArg (coeff n) h
  rw [← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun s => by simp), map_smul, smul_eq_mul] at h2
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum] at h2
  have hr : ((2 : ℚ) ^ (∑ s, w s * n s) - 2) ≠ 0 := by
    intro h0
    apply hn
    have h3 : (2 : ℕ) ^ (∑ s, w s * n s) = 2 := by exact_mod_cast sub_eq_zero.1 h0
    exact Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)
  have hk : algebraMap ℚ k ((2 : ℚ) ^ (∑ s, w s * n s) - 2) * coeff n f = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h2
  calc coeff n f
      = algebraMap ℚ k (((2 : ℚ) ^ (∑ s, w s * n s) - 2)⁻¹ * ((2 : ℚ) ^ (∑ s, w s * n s) - 2))
          * coeff n f := by rw [inv_mul_cancel₀ hr, map_one, one_mul]
    _ = 0 := by rw [map_mul, mul_assoc, hk, mul_zero]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2`.
-/
theorem hasSubst_pts {n m d : ℕ} (a : Fin m → Pt k n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

/- English proof (translation)
Unfold `ev`. Conclude with `MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f`.
-/
theorem ev_ev {n m l d : ℕ} (a : Fin m → Pt k n d) (b : Fin n → Pt k l d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

/- English proof (translation)
Unfold `ev`. Conclude with `MvPowerSeries.subst_X (hasSubst_pts a ha) (j, i)`.
-/
theorem ev_X {n m d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) (i : Fin d) :
    ev a (X (j, i) : PS k m d) = a j i := by
  unfold ev
  exact MvPowerSeries.subst_X (hasSubst_pts a ha) (j, i)

/- English proof (translation)
Simplify using `[pt]`.
-/
theorem const_pt {n d : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by
  simp [pt]

def AddLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 1 d),
    ev (n := 2) ![pt k d 0 + pt k d 1] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f →
      ∀ n : Fin 1 × Fin d →₀ ℕ, n.degree ≠ 1 → coeff n f = 0

/- English proof (translation)
Establish `e : (fun p : Fin n × Fin d => pt k d p.1 p.2) = MvPowerSeries.X`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Unfold `ev`. Rewrite using `[e, MvPowerSeries.subst_self]`.

Both sides reduce to the same expression.
-/
theorem ev_pt {n d : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have e : (fun p : Fin n × Fin d => pt k d p.1 p.2) = MvPowerSeries.X := by
    funext p
    rfl
  unfold ev
  rw [e, MvPowerSeries.subst_self]
  rfl

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum]`. Simplify using the standard rewrite rules.
-/
theorem sum_degree {σ : Type} [Fintype σ] (n : σ →₀ ℕ) : n.degree = ∑ s, 1 * n s := by
  rw [Finsupp.degree_eq_sum]
  simp

/- English proof (translation)
Unfold `ev`. Conclude with `MvPowerSeries.subst_add (hasSubst_pts b hb) f g`.
-/
theorem ev_add' {n m d : ℕ} (b : Fin m → Pt k n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_pts b hb) f g

/- English proof (translation)
Introduce `k _ _ d f hf n hn`. Set `b : Fin 2 → Pt k 1 d` to `![pt k d 0, pt k d 0]`. Apply the tactic sequence `have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by fin_cases j <;> simp [b, pt]`. Establish `hA : ev b (ev (n` using `2) ![pt k d 0 + pt k d 1] f) = ev (fun (j : Fin 1) i => (2 : k) ^ 1 • (X (j, i) : PS k 1 d)) f := by`. Rewrite using `[ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]`.

Use `congr 1`. Use function extensionality and compare the values at `j i`. Use `fin_cases j`. Simplify using `[b, pt, ev_add' b hb0, ev_X b hb0, two_smul]`. Establish `hB : ∀ c : Fin 2, ev b (ev (n` using `2) ![pt k d c] f) = f := by`.

Introduce `c`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]`. Use `congr 1`. Use function extensionality and compare the values at `j i`.

Use `fin_cases j`. Apply the tactic sequence `fin_cases c <;> simp [b, pt, ev_X b hb0]`. Use `_ = f := ev_pt f`. Establish `h1` using `congrArg (ev b) hf`. Rewrite `h1` using `[ev_add' b hb0, hA, hB 0, hB 1]`.

Use `coeff_zero_of_scale (fun _ => 1) f ?_ n ?_` and prove the remaining obligations. Rewrite using `[two_smul]`. Conclude with `h1`. Rewrite using `[← sum_degree]`. Conclude with `hn`.
-/
theorem addition_linear : AddLinSt := by
  intro k _ _ d f hf n hn
  let b : Fin 2 → Pt k 1 d := ![pt k d 0, pt k d 0]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 2) ![pt k d 0 + pt k d 1] f)
      = ev (fun (j : Fin 1) i => (2 : k) ^ 1 • (X (j, i) : PS k 1 d)) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j
    simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 2, ev b (ev (n := 2) ![pt k d c] f) = f := by
    intro c
    calc ev b (ev (n := 2) ![pt k d c] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases j
          fin_cases c <;> simp [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0, hB 1] at h1
  refine coeff_zero_of_scale (fun _ => 1) f ?_ n ?_
  · rw [two_smul]
    exact h1
  · rw [← sum_degree]
    exact hn

/- English proof (translation)
Set `w : Fin 2 × Fin d → ℕ` to `fun p => if p.1 = 0 then c0 else c1`. Establish `hfam : ((fun s => (2 : k) ^ w s) • (X : Fin 2 × Fin d → PS k 2 d)) = fun p => (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d), fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) p.1 p.2`. Use function extensionality and compare the values at `p`. Break down `p with ⟨j, i⟩` into its components or cases. Apply the tactic sequence `fin_cases j <;> simp [w]`.

Use `coeff_zero_of_scale w f ?_ n ?_` and prove the remaining obligations. Rewrite using `[hfam]`. Conclude with `h`. Rewrite using `[Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify `hn` using `[w, Finset.mul_sum]`.
-/
theorem scale_two {d : ℕ} (f : PS k 2 d) (c0 c1 : ℕ)
    (h : ev (n := 2) (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
      fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f = (2 : k) • f)
    (n : Fin 2 × Fin d →₀ ℕ) (hn : c0 * (∑ i, n (0, i)) + c1 * (∑ i, n (1, i)) ≠ 1) : coeff n f = 0 := by
  let w : Fin 2 × Fin d → ℕ := fun p => if p.1 = 0 then c0 else c1
  have hfam : ((fun s => (2 : k) ^ w s) • (X : Fin 2 × Fin d → PS k 2 d)) = fun p =>
      (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) p.1 p.2 := by
    funext p
    rcases p with ⟨j, i⟩
    fin_cases j <;> simp [w]
  refine coeff_zero_of_scale w f ?_ n ?_
  · rw [hfam]
    exact h
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simpa [w, Finset.mul_sum] using hn

def AddLinFstSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (0, i)) ≠ 1 → coeff n f = 0

def AddLinSndSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (1, i)) ≠ 1 → coeff n f = 0

def BiaddBilinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, ¬ ((∑ i, n (0, i)) = 1 ∧ (∑ i, n (1, i)) = 1) → coeff n f = 0

/- English proof (translation)
Introduce `k _ _ d f hf n hn`. Set `b : Fin 3 → Pt k 2 d` to `![pt k d 0, pt k d 0, pt k d 1]`. Apply the tactic sequence `have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by fin_cases j <;> simp [b, pt]`. Establish `hA : ev b (ev (n` using `3) ![pt k d 0 + pt k d 1, pt k d 2] f) = ev (![fun i => (2 : k) ^ 1 • (X ((0 : Fin 2), i) : PS k 2 d), fun i => (2 : k) ^ 0 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by`. Apply the tactic sequence `rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]`.

Use `congr 1`. Use function extensionality and compare the values at `j i`. Apply the tactic sequence `fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]`. Establish `hB : ∀ c : Fin 3, c ≠ 2 → ev b (ev (n` using `3) ![pt k d c, pt k d 2] f) = f := by`. Introduce `c hc`.

Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]`. Use `congr 1`. Use function extensionality and compare the values at `j i`. Apply the tactic sequence `fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]`.

Use `_ = f := ev_pt f`. Establish `h1` using `congrArg (ev b) hf`. Rewrite `h1` using `[ev_add' b hb0, hA, hB 0 (by decide), hB 1 (by decide)]`. Use `scale_two f 1 0 ?_ n ?_` and prove the remaining obligations. Rewrite using `[two_smul]`.

Conclude with `h1`. Simplify using `using hn`.
-/
theorem addition_linear_fst : AddLinFstSt := by
  intro k _ _ d f hf n hn
  let b : Fin 3 → Pt k 2 d := ![pt k d 0, pt k d 0, pt k d 1]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f)
      = ev (![fun i => (2 : k) ^ 1 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ 0 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 3, c ≠ 2 → ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = f := by
    intro c hc
    calc ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0 (by decide), hB 1 (by decide)] at h1
  refine scale_two f 1 0 ?_ n ?_
  · rw [two_smul]
    exact h1
  · simpa using hn

/- English proof (translation)
Introduce `k _ _ d f hf n hn`. Set `b : Fin 3 → Pt k 2 d` to `![pt k d 0, pt k d 1, pt k d 1]`. Apply the tactic sequence `have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by fin_cases j <;> simp [b, pt]`. Establish `hA : ev b (ev (n` using `3) ![pt k d 0, pt k d 1 + pt k d 2] f) = ev (![fun i => (2 : k) ^ 0 • (X ((0 : Fin 2), i) : PS k 2 d), fun i => (2 : k) ^ 1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by`. Apply the tactic sequence `rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]`.

Use `congr 1`. Use function extensionality and compare the values at `j i`. Apply the tactic sequence `fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]`. Establish `hB : ∀ c : Fin 3, c ≠ 0 → ev b (ev (n` using `3) ![pt k d 0, pt k d c] f) = f := by`. Introduce `c hc`.

Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]`. Use `congr 1`. Use function extensionality and compare the values at `j i`. Apply the tactic sequence `fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]`.

Use `_ = f := ev_pt f`. Establish `h1` using `congrArg (ev b) hf`. Rewrite `h1` using `[ev_add' b hb0, hA, hB 1 (by decide), hB 2 (by decide)]`. Use `scale_two f 0 1 ?_ n ?_` and prove the remaining obligations. Rewrite using `[two_smul]`.

Conclude with `h1`. Simplify using `using hn`.
-/
theorem addition_linear_snd : AddLinSndSt := by
  intro k _ _ d f hf n hn
  let b : Fin 3 → Pt k 2 d := ![pt k d 0, pt k d 1, pt k d 1]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f)
      = ev (![fun i => (2 : k) ^ 0 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ 1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 3, c ≠ 0 → ev b (ev (n := 3) ![pt k d 0, pt k d c] f) = f := by
    intro c hc
    calc ev b (ev (n := 3) ![pt k d 0, pt k d c] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 1 (by decide), hB 2 (by decide)] at h1
  refine scale_two f 0 1 ?_ n ?_
  · rw [two_smul]
    exact h1
  · simpa using hn

/- English proof (translation)
Introduce `k _ _ d f h1 h2 n hn`. Distinguish the cases in `h : (∑ i, n (0, i)) = 1`. Conclude with `addition_linear_snd k d f h2 n fun h' => hn ⟨h, h'⟩`. Conclude with `addition_linear_fst k d f h1 n h`.
-/
theorem biadditive_bilinear : BiaddBilinSt := by
  intro k _ _ d f h1 h2 n hn
  by_cases h : (∑ i, n (0, i)) = 1
  · exact addition_linear_snd k d f h2 n fun h' => hn ⟨h, h'⟩
  · exact addition_linear_fst k d f h1 n h

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
