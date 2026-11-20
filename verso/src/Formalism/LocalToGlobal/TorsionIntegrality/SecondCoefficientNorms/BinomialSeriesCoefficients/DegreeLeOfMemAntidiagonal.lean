import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IntBinomScalar

noncomputable section

open PowerSeries

namespace Formalism.L2.Th1.C

namespace IntegralMvPolynomialLemmas

section Chain

variable {A : Type*} [CommRing A] {σ : Type*}

/- English proof (translation)
Establish `hs : HasSubst a` using `HasSubst.of_constantCoeff_zero ha`. Rewrite using `[coeff_subst hs, coeff_subst hs]`. Use `finsum_congr fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ≤ e.degree`. Rewrite using `[hgh k hk]`.

Establish `: MvPowerSeries.coeff e (a ^ k) = 0`. Apply `MvPowerSeries.coeff_of_lt_order` to reduce the goal to its premises. Use `lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha)` and prove the remaining obligations. Conclude with `(not_le.mp hk)` after adjusting the coercions. Rewrite using `[this, smul_zero, smul_zero]`.
-/
theorem coeff_subst_congr {g h : PowerSeries A} {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  rw [coeff_subst hs, coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  · rw [hgh k hk]
  · have : MvPowerSeries.coeff e (a ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha)
      exact_mod_cast (not_le.mp hk)
    rw [this, smul_zero, smul_zero]

/- English proof (translation)
Establish `hs : HasSubst a` using `HasSubst.of_constantCoeff_zero ha`. Rewrite using `[subst_coe hs, derivative_coe, subst_coe hs, Derivation.comp_aeval_eq, smul_eq_mul]`.
-/
theorem pderiv_subst_coe (p : Polynomial A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv A i ((p : PowerSeries A).subst a) =
      (derivative A (p : PowerSeries A)).subst a * MvPowerSeries.pderiv A i a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  rw [subst_coe hs, derivative_coe, subst_coe hs, Derivation.comp_aeval_eq, smul_eq_mul]

/- English proof (translation)
Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hx, map_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add]
  omega

/- English proof (translation)
Use extensionality with `d`. Establish `hdeg : (d + Finsupp.single i 1).degree = d.degree + 1`. Rewrite using `[map_add, Finsupp.degree_single]`. Establish `h1 : MvPowerSeries.coeff (d + Finsupp.single i 1) (g.subst a) = MvPowerSeries.coeff (d + Finsupp.single i 1) (((trunc (d.degree + 2) g : Polynomial A) : PowerSeries A).subst a)`. Apply `coeff_subst_congr ha` to reduce the goal to its premises.

Introduce `k hk`. Rewrite using `[coeff_coe_trunc_of_lt (by omega)]`. Rewrite using `[MvPowerSeries.coeff_pderiv, h1, ← MvPowerSeries.coeff_pderiv, pderiv_subst_coe _ ha, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Use `congr 1`.

Apply `coeff_subst_congr ha` to reduce the goal to its premises. Introduce `k hk`. Use `degree_le_of_mem_antidiagonal hx` as an intermediate fact. Rewrite using `[coeff_derivative, coeff_derivative, coeff_coe_trunc_of_lt (by omega)]`.
-/
theorem pderiv_subst (g : PowerSeries A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv A i (g.subst a) =
      (derivative A g).subst a * MvPowerSeries.pderiv A i a := by
  classical
  ext d
  have hdeg : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff (d + Finsupp.single i 1) (g.subst a) =
      MvPowerSeries.coeff (d + Finsupp.single i 1)
        (((trunc (d.degree + 2) g : Polynomial A) : PowerSeries A).subst a) := by
    apply coeff_subst_congr ha
    intro k hk
    rw [coeff_coe_trunc_of_lt (by omega)]
  rw [MvPowerSeries.coeff_pderiv, h1, ← MvPowerSeries.coeff_pderiv, pderiv_subst_coe _ ha,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  apply coeff_subst_congr ha
  intro k hk
  have := degree_le_of_mem_antidiagonal hx
  rw [coeff_derivative, coeff_derivative, coeff_coe_trunc_of_lt (by omega)]

/- English proof (translation)
Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `: x.1.degree ≠ 0` using `fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)`. Rewrite using `[← hx, map_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_snd_lt [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h1 : x.1 ≠ 0) : x.2.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.1.degree ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
  rw [← hx, map_add]
  omega

/- English proof (translation)
Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `: x.2.degree ≠ 0` using `fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)`. Rewrite using `[← hx, map_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_fst_lt [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h2 : x.2 ≠ 0) : x.1.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)
  rw [← hx, map_add]
  omega

end Chain

section Integral

variable {K : Type} [Field K] {σ : Type} {R : Subring K}

/- English proof (translation)
Introduce `d`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.
-/
theorem intMv_one : IntMv R (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Introduce `d`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hF p.1) (hG p.2)`.
-/
theorem intMv_mul {F G : MvPowerSeries σ K} (hF : IntMv R F) (hG : IntMv R G) :
    IntMv R (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hF p.1) (hG p.2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `intMv_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `intMv_mul ih hF`.
-/
theorem intMv_pow {F : MvPowerSeries σ K} (hF : IntMv R F) (n : ℕ) : IntMv R (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intMv_one
  | succ n ih => rw [pow_succ]; exact intMv_mul ih hF

/- English proof (translation)
The claim follows from `Finset.prod_induction F (IntMv R) (fun _ _ => intMv_mul) intMv_one hF`.
-/
theorem intMv_prod {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries σ K}
    (hF : ∀ i ∈ s, IntMv R (F i)) : IntMv R (∏ i ∈ s, F i) :=
  Finset.prod_induction F (IntMv R) (fun _ _ => intMv_mul) intMv_one hF

/- English proof (translation)
Introduce `d`. Rewrite using `[MvPowerSeries.coeff_pderiv]`. Conclude with `Subring.mul_mem _ (hF _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))`.
-/
theorem intMv_pderiv {F : MvPowerSeries σ K} (hF : IntMv R F) (i : σ) :
    IntMv R (MvPowerSeries.pderiv K i F) := by
  intro d
  rw [MvPowerSeries.coeff_pderiv]
  exact Subring.mul_mem _ (hF _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))

/- English proof (translation)
Introduce `e`. Rewrite using `[coeff_subst (HasSubst.of_constantCoeff_zero ha.1)]`. Use `finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Conclude with `R.mul_mem (hc k) (intMv_pow ha.2 k e)`.
-/
theorem intMv_subst {c : PowerSeries K} (hc : IntPS R c) {a : MvPowerSeries σ K}
    (ha : IsPt R a) : IntMv R (c.subst a) := by
  intro e
  rw [coeff_subst (HasSubst.of_constantCoeff_zero ha.1)]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hc k) (intMv_pow ha.2 k e)

/- English proof (translation)
Introduce `e`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1)]`. Use `finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Conclude with `R.mul_mem (hF d) (intMv_prod _ (fun s _ => intMv_pow (ha s).2 _) e)`.
-/
theorem intMv_substMv {τ : Type} [Finite σ] {F : MvPowerSeries σ K} (hF : IntMv R F)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, IsPt R (a s)) : IntMv R (MvPowerSeries.subst a F) := by
  intro e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1)]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hF d) (intMv_prod _ (fun s _ => intMv_pow (ha s).2 _) e)

/- English proof (translation)
Establish `hV : V = 1 - (U - 1) * V` using `by rw [sub_mul, hUV]; ring`. Establish `hh : IntMv R (U - 1)` using `fun n => by`. Rewrite using `[map_sub]`. Conclude with `R.sub_mem (hU n) (intMv_one n)`. Establish `hh0 : MvPowerSeries.coeff 0 (U - 1) = 0`.

Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hU0, map_one, sub_self]`. Establish `key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n V ∈ R`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Introduce `n hn`. Rewrite using `[hV, map_sub, MvPowerSeries.coeff_mul]`. Use `R.sub_mem (intMv_one n) (Subring.sum_mem _ fun p hp => ?_)` and prove the remaining obligations. Distinguish the cases in `h1 : p.1 = 0`. Rewrite using `[h1, hh0, zero_mul]`.

Conclude with `R.zero_mem`. Conclude with `R.mul_mem (hh _) (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)`. Conclude with `fun n => key _ n rfl`.
-/
theorem intMv_of_mul_eq_one {U V : MvPowerSeries σ K} (hU : IntMv R U)
    (hU0 : MvPowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntMv R V := by
  classical
  have hV : V = 1 - (U - 1) * V := by rw [sub_mul, hUV]; ring
  have hh : IntMv R (U - 1) := fun n => by
    rw [map_sub]; exact R.sub_mem (hU n) (intMv_one n)
  have hh0 : MvPowerSeries.coeff 0 (U - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hU0, map_one, sub_self]
  have key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n V ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hV, map_sub, MvPowerSeries.coeff_mul]
      refine R.sub_mem (intMv_one n) (Subring.sum_mem _ fun p hp => ?_)
      by_cases h1 : p.1 = 0
      · rw [h1, hh0, zero_mul]; exact R.zero_mem
      · exact R.mul_mem (hh _) (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)
  exact fun n => key _ n rfl

/- English proof (translation)
Establish `hh0 : MvPowerSeries.coeff 0 (g - 1) = 0`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]`. Establish `hid : ∀ n, MvPowerSeries.coeff n (g - 1) = (2 : K)⁻¹ * (MvPowerSeries.coeff n (g * g) - MvPowerSeries.coeff n (1 : MvPowerSeries σ K) - MvPowerSeries.coeff n ((g - 1) * (g - 1)))`. Introduce `n`. Establish `: g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1)` using `by ring`.

Rewrite using `[← map_sub, ← map_sub, this, map_add]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n (g - 1) ∈ R`. Introduce `m`.

Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `n hn`. Rewrite using `[hid n, MvPowerSeries.coeff_mul n (g - 1)]`. Use `R.mul_mem h2 (R.sub_mem (R.sub_mem (hgg n) (intMv_one n)) (Subring.sum_mem _ fun p hp => ?_))` and prove the remaining obligations.

Distinguish the cases in `h1 : p.1 = 0`. Rewrite using `[h1, hh0, zero_mul]`. Conclude with `R.zero_mem`. Distinguish the cases in `h2' : p.2 = 0`. Rewrite using `[h2', hh0, mul_zero]`.

Conclude with `R.zero_mem`. Conclude with `R.mul_mem (ih _ (hn ▸ degree_fst_lt hp h2') _ rfl) (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)`. Introduce `n`. Establish `: g = (g - 1) + 1` using `by ring`. Rewrite using `[this, map_add]`.

Conclude with `R.add_mem (key _ n rfl) (intMv_one n)`.
-/
theorem intMv_of_sq {g : MvPowerSeries σ K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : MvPowerSeries.constantCoeff g = 1) (hgg : IntMv R (g * g)) : IntMv R g := by
  classical
  have hh0 : MvPowerSeries.coeff 0 (g - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hid : ∀ n, MvPowerSeries.coeff n (g - 1) = (2 : K)⁻¹ * (MvPowerSeries.coeff n (g * g)
      - MvPowerSeries.coeff n (1 : MvPowerSeries σ K)
      - MvPowerSeries.coeff n ((g - 1) * (g - 1))) := by
    intro n
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n (g - 1) ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hid n, MvPowerSeries.coeff_mul n (g - 1)]
      refine R.mul_mem h2 (R.sub_mem (R.sub_mem (hgg n) (intMv_one n))
        (Subring.sum_mem _ fun p hp => ?_))
      by_cases h1 : p.1 = 0
      · rw [h1, hh0, zero_mul]; exact R.zero_mem
      by_cases h2' : p.2 = 0
      · rw [h2', hh0, mul_zero]; exact R.zero_mem
      exact R.mul_mem (ih _ (hn ▸ degree_fst_lt hp h2') _ rfl)
        (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)
  intro n
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem (key _ n rfl) (intMv_one n)

end Integral

section Exp

variable {K : Type} [Field K] [CharZero K] {σ : Type}

/- English proof (translation)
Establish `h` using `coeff_subst_congr (g := exp K) (h := C (1 : K)) hf 0 (fun k hk => by`. Establish `: k = 0` using `by simpa using hk`. Substitute `this` using the available equality. Use the proof step `simp)`. Rewrite `h` using `[subst_C]`.

Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Unfold `mvExp`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  have h := coeff_subst_congr (g := exp K) (h := C (1 : K)) hf 0 (fun k hk => by
    have : k = 0 := by simpa using hk
    subst this
    simp)
  rw [subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold mvExp
  rw [h]
  simp

/- English proof (translation)
Unfold `mvExp`. Rewrite using `[pderiv_subst _ hf, derivative_exp]`.
-/
theorem pderiv_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    MvPowerSeries.pderiv K i (mvExp f) = mvExp f * MvPowerSeries.pderiv K i f := by
  unfold mvExp
  rw [pderiv_subst _ hf, derivative_exp]

/- English proof (translation)
Unfold `mvExp`. Rewrite using `[subst_def, subst_def]`. Conclude with `MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hf).const (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (exp K)`.
-/
theorem substMv_mvExp {τ : Type} [Finite σ] {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  rw [subst_def, subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hf).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (exp K)

end Exp

end IntegralMvPolynomialLemmas

open IntegralMvPolynomialLemmas

/- English proof (translation)
Introduce `K _ _ R σ`. Take `⟨h0, -, hadd, -⟩` from `hE K σ`. Use `⟨⟨map_zero _, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `intMv_one`.

Introduce `f g hf hg`. Use `⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[hadd f g hf.1 hg.1]`. Conclude with `intMv_mul hf.2 hg.2`. Introduce `f hf`.

Establish `hn : MvPowerSeries.constantCoeff (-f) = 0` using `by rw [map_neg, hf.1, neg_zero]`. Use `⟨hn, intMv_of_mul_eq_one hf.2 (constantCoeff_mvExp hf.1) ?_⟩` and prove the remaining obligations. Rewrite using `[← hadd f (-f) hf.1 hn, add_neg_cancel, h0]`.
-/
theorem lGSubgroup_of (hE : MvExpLaws) : LGSubgroup := by
  intro K _ _ R σ
  obtain ⟨h0, -, hadd, -⟩ := hE K σ
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  · rw [h0]; exact intMv_one
  · intro f g hf hg
    refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
    rw [hadd f g hf.1 hg.1]
    exact intMv_mul hf.2 hg.2
  · intro f hf
    have hn : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf.1, neg_zero]
    refine ⟨hn, intMv_of_mul_eq_one hf.2 (constantCoeff_mvExp hf.1) ?_⟩
    rw [← hadd f (-f) hf.1 hn, add_neg_cancel, h0]

/- English proof (translation)
Introduce `K _ _ R σ h2 f hf`. Take `⟨-, -, hadd, -⟩` from `hE K σ`. Establish `hf0 : MvPowerSeries.constantCoeff f = 0`. Establish `h` using `hf.1`. Rewrite `h` using `[map_add, ← two_mul]`.

Conclude with `(mul_eq_zero.mp h).resolve_left two_ne_zero`. Use `⟨hf0, intMv_of_sq h2 two_ne_zero (constantCoeff_mvExp hf0) ?_⟩` and prove the remaining obligations. Rewrite using `[← hadd f f hf0 hf0]`. Conclude with `hf.2`.
-/
theorem lGHalf_of (hE : MvExpLaws) : LGHalf := by
  intro K _ _ R σ h2 f hf
  obtain ⟨-, -, hadd, -⟩ := hE K σ
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_add, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨hf0, intMv_of_sq h2 two_ne_zero (constantCoeff_mvExp hf0) ?_⟩
  rw [← hadd f f hf0 hf0]
  exact hf.2

/- English proof (translation)
Introduce `K _ R f hf σ a ha`. Conclude with `intMv_subst hf ha`.
-/
theorem coeffsInSubst' : IntSubst := by
  intro K _ R f hf σ a ha
  exact intMv_subst hf ha

/- English proof (translation)
Introduce `K _ _ R f hf σ a ha`. Use `⟨constantCoeff_subst_eq_zero ha.1 f hf.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hS K σ f a hf.1 ha.1]`. Conclude with `intMv_subst (fun n => hf.2 _) ha`.
-/
theorem lGSubst_of (hS : MvExpSubst) : LGSubst := by
  intro K _ _ R f hf σ a ha
  refine ⟨constantCoeff_subst_eq_zero ha.1 f hf.1, ?_⟩
  rw [← hS K σ f a hf.1 ha.1]
  exact intMv_subst (fun n => hf.2 _) ha

/- English proof (translation)
Introduce `K _ _ R σ _ f hf τ a ha`. Establish `ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0` using `fun s => (ha s).1`. Use `⟨MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0) ha0 hf.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← substMv_mvExp hf.1 ha0]`. Conclude with `intMv_substMv hf.2 ha`.
-/
theorem expIntegralMvSubst' : LGSubstMv := by
  intro K _ _ R σ _ f hf τ a ha
  have ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0 := fun s => (ha s).1
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0) ha0 hf.1, ?_⟩
  rw [← substMv_mvExp hf.1 ha0]
  exact intMv_substMv hf.2 ha

/- English proof (translation)
Introduce `K _ _ R σ f hf i`. Establish `h0` using `constantCoeff_mvExp hf.1`. Establish `hne : MvPowerSeries.constantCoeff (mvExp f) ≠ 0` using `by rw [h0]; exact one_ne_zero`. Establish `hinv : mvExp f * (mvExp f)⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel _ hne`. Establish `hV : IntMv R (mvExp f)⁻¹` using `intMv_of_mul_eq_one hf.2 h0 hinv`.

Establish `: MvPowerSeries.pderiv K i f = (mvExp f)⁻¹ * MvPowerSeries.pderiv K i (mvExp f)`. Rewrite using `[pderiv_mvExp hf.1, ← mul_assoc, mul_comm _ (mvExp f), hinv, one_mul]`. Rewrite using `[this]`. Conclude with `intMv_mul hV (intMv_pderiv hf.2 i)`.
-/
theorem expIntegralDeriv' : LGDeriv := by
  intro K _ _ R σ f hf i
  have h0 := constantCoeff_mvExp hf.1
  have hne : MvPowerSeries.constantCoeff (mvExp f) ≠ 0 := by rw [h0]; exact one_ne_zero
  have hinv : mvExp f * (mvExp f)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hne
  have hV : IntMv R (mvExp f)⁻¹ := intMv_of_mul_eq_one hf.2 h0 hinv
  have : MvPowerSeries.pderiv K i f = (mvExp f)⁻¹ * MvPowerSeries.pderiv K i (mvExp f) := by
    rw [pderiv_mvExp hf.1, ← mul_assoc, mul_comm _ (mvExp f), hinv, one_mul]
  rw [this]
  exact intMv_mul hV (intMv_pderiv hf.2 i)

end Formalism.L2.Th1.C
