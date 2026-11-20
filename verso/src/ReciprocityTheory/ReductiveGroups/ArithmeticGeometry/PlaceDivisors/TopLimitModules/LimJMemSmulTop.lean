import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.FmodConst

set_option autoImplicit false

noncomputable section

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.TL

section Jets

variable {T : Type} [CommRing T]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq]`. Establish `hI : (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) = MvPolynomial.idealOfVars σ T` using `rfl`. Rewrite using `[hI, MvPolynomial.mem_pow_idealOfVars_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Assume the negation of the conclusion as `hne`. Establish `hmem : x ∈ (P - Q).support`. Rewrite using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub]`. Conclude with `sub_ne_zero.mpr hne`. Use `h x hmem` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `h x hx`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Rewrite `hx` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h x hlt, sub_self]`.

Conclude with `hx rfl`.
-/
theorem limJ_mk_eq_iff {σ : Type} (k : ℕ) (P Q : MvPolynomial σ T) :
    (Ideal.Quotient.mk _ P : JetR T σ k) = Ideal.Quotient.mk _ Q ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → P.coeff x = Q.coeff x := by
  rw [Ideal.Quotient.eq]
  have hI : (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) =
      MvPolynomial.idealOfVars σ T := rfl
  rw [hI, MvPolynomial.mem_pow_idealOfVars_iff]
  constructor
  · intro h x hx
    by_contra hne
    have hmem : x ∈ (P - Q).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub]
      exact sub_ne_zero.mpr hne
    have := h x hmem
    omega
  · intro h x hx
    by_contra hlt
    push_neg at hlt
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h x hlt, sub_self] at hx
    exact hx rfl

/- English proof (translation)
Rewrite using `[MvPowerSeries.truncTotalAlgHom_apply, MvPowerSeries.truncTotalAlgHom_apply]`. Use `(limJ_mk_eq_iff k (truncTotal (k + 1) f) (truncTotal (k + 1) g)).trans ?_` and prove the remaining obligations. Use `forall_congr' fun x => imp_congr_right fun hx => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_truncTotal _ hx]`.
-/
theorem limJ_tt_eq_iff {σ : Type} [Finite σ] (k : ℕ) (f g : MvPowerSeries σ T) :
    truncTotalAlgHom σ T (k + 1) f = truncTotalAlgHom σ T (k + 1) g ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → coeff x f = coeff x g := by
  rw [MvPowerSeries.truncTotalAlgHom_apply, MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k (truncTotal (k + 1) f) (truncTotal (k + 1) g)).trans ?_
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_truncTotal _ hx]

/- English proof (translation)
Establish `hle : ∀ i, x i ≤ x.degree` using `fun i => by`. Distinguish the cases in `hi : i ∈ x.support`. Conclude with `Finset.single_le_sum (f := fun j => x j) (fun _ _ => Nat.zero_le _) hi`. Establish `h0 : x i = 0`. Assume the negation of the conclusion as `h'`.

Conclude with `hi (Finsupp.mem_support_iff.mpr h')`. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`. Use `lt_of_le_of_ne (fun i => ?_) (fun h => ?_)` and prove the remaining obligations. Use `show x i ≤ k + 1`.

Use `hle i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h2 : x i0 = k + 1`. Rewrite using `[h]`. Both sides reduce to the same expression.

Use `hle i0` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem limJ_lt_box {σ : Type} [Finite σ] (i0 : σ) (k : ℕ) (x : σ →₀ ℕ) (hx : x.degree < k + 1) :
    x < Finsupp.equivFunOnFinite.symm (fun _ : σ => k + 1) := by
  classical
  have hle : ∀ i, x i ≤ x.degree := fun i => by
    by_cases hi : i ∈ x.support
    · exact Finset.single_le_sum (f := fun j => x j) (fun _ _ => Nat.zero_le _) hi
    · have h0 : x i = 0 := by
        by_contra h'
        exact hi (Finsupp.mem_support_iff.mpr h')
      rw [h0]
      exact Nat.zero_le _
  refine lt_of_le_of_ne (fun i => ?_) (fun h => ?_)
  · show x i ≤ k + 1
    have := hle i
    omega
  · have h2 : x i0 = k + 1 := by
      rw [h]
      rfl
    have := hle i0
    omega

/- English proof (translation)
Rewrite using `[MvPowerSeries.truncTotalAlgHom_apply]`. Use `(limJ_mk_eq_iff k _ _).mpr fun x hx => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_trunc, if_pos (limJ_lt_box (⟨0, hn⟩, ⟨0, hd⟩) k x hx)]`.
-/
theorem limJ_psJet_eq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (f : PS T n d) :
    psJet k f = truncTotalAlgHom (Fin n × Fin d) T (k + 1) f := by
  rw [MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k _ _).mpr fun x hx => ?_
  classical
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_trunc,
    if_pos (limJ_lt_box (⟨0, hn⟩, ⟨0, hd⟩) k x hx)]

/- English proof (translation)
Use `first`. Consider the case `exact (Finsupp.degree_eq_zero_iff _).mp h`. Consider the case `exact Finsupp.degree_eq_zero_iff.mp h`.
-/
private theorem vzero_lemma {ρ : Type*} {e : ρ →₀ ℕ} (h : e.degree = 0) : e = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff _).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x.1 + x.2 = e` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree` using `by first`.

Consider the case `exact Finsupp.degree_add _ _`. Consider the case `exact map_add _ _ _`. Rewrite `hdeg` using `[hx']`. Distinguish the cases in `h1 : x.1.degree < m`. Rewrite using `[hP _ h1, zero_mul]`.

Rewrite using `[hQ _ (by omega), mul_zero]`.
-/
private theorem vmul_lemma_2 {ρ K : Type*} [CommRing K] {P Q : MvPowerSeries ρ K} {m n : ℕ}
    (hP : ∀ e : ρ →₀ ℕ, e.degree < m → coeff e P = 0)
    (hQ : ∀ e : ρ →₀ ℕ, e.degree < n → coeff e Q = 0) :
    ∀ e : ρ →₀ ℕ, e.degree < m + n → coeff e (P * Q) = 0 := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := by
    first
    | exact Finsupp.degree_add _ _
    | exact map_add _ _ _
  rw [hx'] at hdeg
  by_cases h1 : x.1.degree < m
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro e he`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Use `vmul_lemma_2 ih ?_` and prove the remaining obligations. Introduce `e he`. Establish `h0 : e = 0` using `vzero_lemma (by omega)`. Rewrite using `[h0, coeff_zero_eq_constantCoeff_apply, hA]`.
-/
private theorem vpow_lemma_3 {ρ K : Type*} [CommRing K] {A : MvPowerSeries ρ K}
    (hA : constantCoeff A = 0) (k : ℕ) :
    ∀ e : ρ →₀ ℕ, e.degree < k → coeff e (A ^ k) = 0 := by
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    rw [pow_succ]
    refine vmul_lemma_2 ih ?_
    intro e he
    have h0 : e = 0 := vzero_lemma (by omega)
    rw [h0, coeff_zero_eq_constantCoeff_apply, hA]

/- English proof (translation)
Use `Finset.induction_on S (fun e he => by simp at he) (fun a S ha ih => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `vmul_lemma_2 (vpow_lemma_3 (hA a) (d a)) ih`.
-/
private theorem vprod_lemma_4 {ι ρ K : Type*} [CommRing K] {A : ι → MvPowerSeries ρ K}
    (hA : ∀ s, constantCoeff (A s) = 0) (d : ι →₀ ℕ) (S : Finset ι) :
    ∀ e : ρ →₀ ℕ, e.degree < ∑ s ∈ S, d s → coeff e (∏ s ∈ S, A s ^ d s) = 0 := by
  classical
  refine Finset.induction_on S (fun e he => by simp at he) (fun a S ha ih => ?_)
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact vmul_lemma_2 (vpow_lemma_3 (hA a) (d a)) ih

/- English proof (translation)
Use `first`. Consider the case `exact HasSubst.of_constantCoeff_zero ha`. Consider the case `exact hasSubst_of_constantCoeff_zero ha`.
-/
private theorem hs_lemma_5 {ρ τ K : Type*} [CommRing K] [Finite ρ] {a : ρ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero ha
  | exact hasSubst_of_constantCoeff_zero ha

/- English proof (translation)
Introduce `e he`. Rewrite using `[MvPowerSeries.coeff_subst (hs_lemma_5 ha0) N e]`. Use `(finsum_congr fun d => ?_).trans finsum_zero` and prove the remaining obligations. Distinguish the cases in `hd : d.degree < m`. Rewrite using `[hN d hd, zero_smul]`.

Establish `hz : coeff e (d.prod fun s n => a s ^ n) = 0` using `vprod_lemma_4 ha0 d d.support e (by show e.degree < d.degree; omega)`. Rewrite using `[hz, smul_zero]`.
-/
private theorem osub_lemma_6 {ρ τ K : Type*} [CommRing K] [Finite ρ] {a : ρ → MvPowerSeries τ K}
    (ha0 : ∀ s, constantCoeff (a s) = 0) {N : MvPowerSeries ρ K} {m : ℕ}
    (hN : ∀ d : ρ →₀ ℕ, d.degree < m → coeff d N = 0) :
    ∀ e : τ →₀ ℕ, e.degree < m → coeff e (MvPowerSeries.subst a N) = 0 := by
  intro e he
  rw [MvPowerSeries.coeff_subst (hs_lemma_5 ha0) N e]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  by_cases hd : d.degree < m
  · rw [hN d hd, zero_smul]
  · have hz : coeff e (d.prod fun s n => a s ^ n) = 0 :=
      vprod_lemma_4 ha0 d d.support e (by show e.degree < d.degree; omega)
    rw [hz, smul_zero]

/- English proof (translation)
Establish `has : HasSubst a` using `hs_lemma_5 ha`. Establish `hpoly : ∀ P : MvPolynomial σ T, truncTotalAlgHom τ T (k + 1) (MvPowerSeries.subst (R` using `T) (S := T) a (P : MvPowerSeries σ T)) = MvPolynomial.aeval (fun i => truncTotalAlgHom τ T (k + 1) (a i)) P := by`. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on`. Use `next c =>`.

Rewrite using `[MvPolynomial.coe_C, ← MvPowerSeries.coe_substAlgHom has, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, MvPolynomial.aeval_C, MvPowerSeries.truncTotalAlgHom_apply, ← MvPowerSeries.c_eq_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]`. Use `(limJ_mk_eq_iff k _ _).mpr fun x hx => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_truncTotal _ hx, MvPolynomial.coeff_C, MvPowerSeries.coeff_C]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1.symm) | (exfalso; exact h1 h2.symm)`. Use `next p q hp hq =>`.

Rewrite using `[MvPolynomial.coe_add, ← MvPowerSeries.coe_substAlgHom has]`. Simplify using `only [map_add]`. Rewrite using `[MvPowerSeries.coe_substAlgHom has, hp, hq]`. Use `next p n hp =>`. Rewrite using `[MvPolynomial.coe_mul, MvPolynomial.coe_X, ← MvPowerSeries.coe_substAlgHom has]`.

Simplify using `only [map_mul, MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X]`. Rewrite using `[MvPowerSeries.coe_substAlgHom has, hp]`. Rewrite using `[← hpoly, limJ_tt_eq_iff]`. Introduce `x hx`. Rewrite using `[← sub_eq_zero, ← map_sub, ← MvPowerSeries.coe_substAlgHom has, ← map_sub, MvPowerSeries.coe_substAlgHom has]`.

Use `osub_lemma_6 ha (fun d hd => ?_) x hx` and prove the remaining obligations. Rewrite using `[map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd, sub_self]`.
-/
theorem limJ_tt_subst {σ τ : Type} [Finite σ] [Finite τ] (k : ℕ) (a : σ → MvPowerSeries τ T)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ T) :
    truncTotalAlgHom τ T (k + 1) (MvPowerSeries.subst (R := T) (S := T) a f) =
      MvPolynomial.aeval (fun i => truncTotalAlgHom τ T (k + 1) (a i)) (truncTotal (k + 1) f) := by
  have has : HasSubst a := hs_lemma_5 ha
  have hpoly : ∀ P : MvPolynomial σ T,
      truncTotalAlgHom τ T (k + 1) (MvPowerSeries.subst (R := T) (S := T) a (P : MvPowerSeries σ T)) =
        MvPolynomial.aeval (fun i => truncTotalAlgHom τ T (k + 1) (a i)) P := by
    intro P
    induction P using MvPolynomial.induction_on
    next c =>
      rw [MvPolynomial.coe_C, ← MvPowerSeries.coe_substAlgHom has, MvPowerSeries.c_eq_algebraMap,
        AlgHom.commutes, MvPolynomial.aeval_C, MvPowerSeries.truncTotalAlgHom_apply,
        ← MvPowerSeries.c_eq_algebraMap, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
      refine (limJ_mk_eq_iff k _ _).mpr fun x hx => ?_
      classical
      rw [MvPowerSeries.coeff_truncTotal _ hx, MvPolynomial.coeff_C, MvPowerSeries.coeff_C]
      split_ifs with h1 h2 h2 <;>
        first | rfl | (exfalso; exact h2 h1.symm) | (exfalso; exact h1 h2.symm)
    next p q hp hq =>
      rw [MvPolynomial.coe_add, ← MvPowerSeries.coe_substAlgHom has]
      simp only [map_add]
      rw [MvPowerSeries.coe_substAlgHom has, hp, hq]
    next p n hp =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, ← MvPowerSeries.coe_substAlgHom has]
      simp only [map_mul, MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X]
      rw [MvPowerSeries.coe_substAlgHom has, hp]
  rw [← hpoly, limJ_tt_eq_iff]
  intro x hx
  rw [← sub_eq_zero, ← map_sub, ← MvPowerSeries.coe_substAlgHom has, ← map_sub,
    MvPowerSeries.coe_substAlgHom has]
  refine osub_lemma_6 ha (fun d hd => ?_) x hx
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd, sub_self]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem limJ_substJ_mk {n d : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (P : MvPolynomial (Fin 1 × Fin d) T) :
    substJ m φ hφ (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun q => psJet m (φ q.2)) P :=
  rfl

/- English proof (translation)
Rewrite using `[limJ_psJet_eq hn hd, limJ_tt_subst k b hb f]`. Establish `e1 : psJet k f = Ideal.Quotient.mk _ (truncTotal (k + 1) f)`. Rewrite using `[limJ_psJet_eq (n := 1) Nat.one_pos hd, MvPowerSeries.truncTotalAlgHom_apply]`. Rewrite using `[e1, limJ_substJ_mk]`. Establish `hfun : (fun i => truncTotalAlgHom (Fin n × Fin d) T (k + 1) (b i)) = fun q => psJet k (φ q.2)`.

Use function extensionality and compare the values at `q`. Rewrite using `[hbφ q, limJ_psJet_eq hn hd]`. Rewrite using `[hfun]`.
-/
theorem limJ_psJet_subst {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (b : Fin 1 × Fin d → PS T n d)
    (hb : ∀ q, constantCoeff (b q) = 0) (φ : Fin d → PS T n d) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hbφ : ∀ q, b q = φ q.2) (f : PS T 1 d) :
    psJet k (MvPowerSeries.subst b f) = substJ k φ hφ (psJet k f) := by
  rw [limJ_psJet_eq hn hd, limJ_tt_subst k b hb f]
  have e1 : psJet k f = Ideal.Quotient.mk _ (truncTotal (k + 1) f) := by
    rw [limJ_psJet_eq (n := 1) Nat.one_pos hd, MvPowerSeries.truncTotalAlgHom_apply]
  rw [e1, limJ_substJ_mk]
  have hfun : (fun i => truncTotalAlgHom (Fin n × Fin d) T (k + 1) (b i)) =
      fun q => psJet k (φ q.2) := by
    funext q
    rw [hbφ q, limJ_psJet_eq hn hd]
  rw [hfun]

/- English proof (translation)
Rewrite using `[limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, map_mul]`.
-/
theorem limJ_psJet_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (f g : PS T n d) :
    psJet k (f * g) = psJet k f * psJet k g := by
  rw [limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, map_mul]

/- English proof (translation)
Establish `h2 : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (X p : PS T 2 d)) g = g` using `by first`. Consider the case `exact congrFun MvPowerSeries.subst_self g`. Consider the case `simp [MvPowerSeries.subst_self]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Unfold `ev`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨i, j⟩` from `p`. Apply the tactic sequence `fin_cases i <;> first | rfl | simp [pt]`.
-/
theorem limJ_ev_pts {d : ℕ} (g : PS T 2 d) : ev (n := 2) ![pt T d 0, pt T d 1] g = g := by
  have h2 : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (X p : PS T 2 d)) g = g := by
    first
    | exact congrFun MvPowerSeries.subst_self g
    | simp [MvPowerSeries.subst_self]
  refine Eq.trans ?_ h2
  unfold ev
  congr 1
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> first | rfl | simp [pt]

end Jets

section Limits

variable {O : Type} [CommRing O] (p : ℕ) [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Rewrite using `[SModEq.sub_mem]`. Establish `h1 : a - b ∈ Ideal.span {(p : O) ^ (m + 1)}` using `Ideal.Quotient.eq.mp h`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Conclude with `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)) h1`.
-/
theorem limJ_mem_smul_top (m : ℕ) (a b : O)
    (h : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) a = Ideal.Quotient.mk _ b) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O O)] := by
  rw [SModEq.sub_mem]
  have h1 : a - b ∈ Ideal.span {(p : O) ^ (m + 1)} := Ideal.Quotient.eq.mp h
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)) h1

/- English proof (translation)
Rewrite using `[IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]`. Introduce `n`. Conclude with `limJ_mem_smul_top p n a b (h n)`.
-/
theorem limJ_unique (a b : O)
    (h : ∀ n, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) a = Ideal.Quotient.mk _ b) : a = b := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]
  intro n
  exact limJ_mem_smul_top p n a b (h n)

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `a ha`. Simplify using `using ha`.

Consider the case `succ j ih`. Introduce `a ha`. Apply `ih` to reduce the goal to its premises. Establish `ha' : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + j + 1 + 1)}) a = x (m + j + 1)` using `ha`. Rewrite using `[← hx (m + j), ← ha']`.

Use `first`. Consider the case `rfl`. Consider the case `simp [redQ]`.
-/
theorem limJ_back (x : ∀ n, O ⧸ Ideal.span {(p : O) ^ (n + 1)})
    (hx : ∀ n, redQ p n (x (n + 1)) = x n) (m : ℕ) :
    ∀ j (a : O), Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + j + 1)}) a = x (m + j) →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) a = x m := by
  intro j
  induction j with
  | zero =>
    intro a ha
    simpa using ha
  | succ j ih =>
    intro a ha
    apply ih
    have ha' : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + j + 1 + 1)}) a = x (m + j + 1) := ha
    rw [← hx (m + j), ← ha']
    first
    | rfl
    | simp [redQ]

/- English proof (translation)
Use `choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)`. Establish `hdown : ∀ m j, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) (f (m + j)) = x m` using `fun m j => limJ_back p x hx m j (f (m + j)) (hf (m + j))`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {(p : O)}) f (fun {m n} hmn => by`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Apply `limJ_mem_smul_top p m` to reduce the goal to its premises.

Rewrite using `[hf m, hdown m j])`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h1` using `hL (n + 1)`. Rewrite `h1` using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Rewrite using `[← hdown n 1]`.

Conclude with `(Ideal.Quotient.eq.mpr h1).symm`.
-/
theorem limJ_exists (x : ∀ n, O ⧸ Ideal.span {(p : O) ^ (n + 1)})
    (hx : ∀ n, redQ p n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hdown : ∀ m j, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) (f (m + j)) = x m :=
    fun m j => limJ_back p x hx m j (f (m + j)) (hf (m + j))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) f (fun {m n} hmn => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
    apply limJ_mem_smul_top p m
    rw [hf m, hdown m j])
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
  rw [← hdown n 1]
  exact (Ideal.Quotient.eq.mpr h1).symm

end Limits

/- English proof (translation)
Introduce `O _ p _ d F U hd hN hK hZ hM`. Use `set π : ∀ n : ℕ, O →+* O ⧸ Ideal.span {(p : O) ^ (n + 1)} := fun n => Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) with hπ`. Use `choose P hP using fun n k => Ideal.Quotient.mk_surjective (U n k)`. Set `c : ∀ n : ℕ, (Fin 1 × Fin d →₀ ℕ) → O ⧸ Ideal.span {(p : O) ^ (n + 1)}` to `fun n μ => (P n μ.degree).coeff μ`. Establish `hck : ∀ n μ k, μ.degree ≤ k → (P n k).coeff μ = c n μ`.

Introduce `n μ k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ k hk ih`. Rewrite using `[← ih]`.

Establish `h1 : (Ideal.Quotient.mk _ (P n k) : JetR _ (Fin 1 × Fin d) k) = Ideal.Quotient.mk _ (P n (k + 1))`. Rewrite using `[hP, ← hK n k, ← hP]`. Both sides reduce to the same expression. Conclude with `((limJ_mk_eq_iff k _ _).1 h1 μ (by omega)).symm`. Establish `hcn : ∀ n μ, redQ p n (c (n + 1) μ) = c n μ`.

Introduce `n μ`. Establish `h1 : (Ideal.Quotient.mk _ (MvPolynomial.map (redQ p n) (P (n + 1) μ.degree)) : JetR _ (Fin 1 × Fin d) μ.degree) = Ideal.Quotient.mk _ (P n μ.degree)`. Rewrite using `[hP n, ← hN n, ← hP]`. Both sides reduce to the same expression. Establish `h2` using `(limJ_mk_eq_iff _ _ _).1 h1 μ (by omega)`.

Rewrite `h2` using `[MvPolynomial.coeff_map]`. Conclude with `h2`. Use `choose a ha using fun μ => limJ_exists p (fun n => c n μ) (fun n => hcn n μ)`. Set `u : PS O 1 d` to `fun μ => a μ`. Establish `hu : ∀ μ, coeff μ u = a μ` using `fun μ => rfl`.

Establish `hJ : ∀ n k, psJet k (MvPowerSeries.map (π n) u) = U n k`. Introduce `n k`. Rewrite using `[limJ_psJet_eq Nat.one_pos hd, ← hP n k, truncTotalAlgHom_apply, limJ_mk_eq_iff]`. Introduce `μ hμ`. Rewrite using `[coeff_truncTotal _ hμ, coeff_map, hu, ha μ n, hck n μ k (by omega)]`.

Use `⟨u, ⟨?_, ?_⟩, hJ⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hu]`. Apply `limJ_unique p` to reduce the goal to its premises. Introduce `n`. Rewrite using `[ha 0 n, map_one]`.

Establish `h1 : (Ideal.Quotient.mk _ (P n 0) : JetR _ (Fin 1 × Fin d) 0) = Ideal.Quotient.mk _ 1`. Rewrite using `[map_one, ← hZ n 0, ← hP n 0]`. Both sides reduce to the same expression. Establish `h2` using `(limJ_mk_eq_iff 0 _ _).1 h1 0 (by simp)`. Rewrite `h2` using `[MvPolynomial.coeff_zero_one]`.

Conclude with `h2`. Establish `hadd : addOf F.F (pt O (n` using `2) d 0) (pt O d 1) = F.F :=`. Use function extensionality and compare the values at `fun i => limJ_ev_pts (F.F i)`. Establish `hbL : ∀ q : Fin 1 × Fin d, (![addOf F.F (pt O (n` using `2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2 = F.F q.2 := by`. Introduce `q`.

Rewrite using `[Fin.fin_one_eq_zero q.1, hadd]`. Both sides reduce to the same expression. Establish `hbLc : ∀ q : Fin 1 × Fin d, constantCoeff ((![addOf F.F (pt O (n` using `2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by`. Introduce `q`. Rewrite using `[hbL]`.

Conclude with `F.const _`. Establish `hbP : ∀ (i : Fin 2) (q : Fin 1 × Fin d), (![pt O (n` using `2) d i] : Fin 1 → Pt O 2 d) q.1 q.2 = X (i, q.2) := by`. Introduce `i q`. Rewrite using `[Fin.fin_one_eq_zero q.1]`. Both sides reduce to the same expression.

Establish `hbPc : ∀ (i : Fin 2) (q : Fin 1 × Fin d), constantCoeff ((![pt O (n` using `2) d i] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by`. Introduce `i q`. Rewrite using `[hbP]`. Simplify using the standard rewrite rules. Use extensionality with `ν`.

Apply `limJ_unique p` to reduce the goal to its premises. Introduce `n`. Rewrite using `[← coeff_map, ← coeff_map]`. Use `(limJ_tt_eq_iff ν.degree _ _).1 ?_ ν (by omega)` and prove the remaining obligations. Rewrite using `[← limJ_psJet_eq (by omega) hd, ← limJ_psJet_eq (by omega) hd]`.

Unfold `ev`. Rewrite using `[map_mul, map_subst (hasSubst_of_constantCoeff_zero hbLc), map_subst (hasSubst_of_constantCoeff_zero (hbPc 0)), map_subst (hasSubst_of_constantCoeff_zero (hbPc 1)), limJ_psJet_mul (by omega) hd]`. Rewrite using `[limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbL]; exact Fmod_const p F n q.2) (Fmod p F n) (Fmod_const p F n) (fun q => by rw [hbL]; rfl), limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbP, map_X]; simp) (fun j => (MvPowerSeries.X ((0 : Fin 2), j) : PS _ 2 d)) (fun …`. Conclude with `hM n ν.degree`.
-/
theorem lim_holds : LimSt := by
  intro O _ p _ d F U hd hN hK hZ hM

  set π : ∀ n : ℕ, O →+* O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
    fun n => Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) with hπ

  choose P hP using fun n k => Ideal.Quotient.mk_surjective (U n k)
  let c : ∀ n : ℕ, (Fin 1 × Fin d →₀ ℕ) → O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
    fun n μ => (P n μ.degree).coeff μ
  have hck : ∀ n μ k, μ.degree ≤ k → (P n k).coeff μ = c n μ := by
    intro n μ k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P n k) : JetR _ (Fin 1 × Fin d) k) =
          Ideal.Quotient.mk _ (P n (k + 1)) := by
        rw [hP, ← hK n k, ← hP]
        rfl
      exact ((limJ_mk_eq_iff k _ _).1 h1 μ (by omega)).symm
  have hcn : ∀ n μ, redQ p n (c (n + 1) μ) = c n μ := by
    intro n μ
    have h1 : (Ideal.Quotient.mk _ (MvPolynomial.map (redQ p n) (P (n + 1) μ.degree)) :
        JetR _ (Fin 1 × Fin d) μ.degree) = Ideal.Quotient.mk _ (P n μ.degree) := by
      rw [hP n, ← hN n, ← hP]
      rfl
    have h2 := (limJ_mk_eq_iff _ _ _).1 h1 μ (by omega)
    rw [MvPolynomial.coeff_map] at h2
    exact h2
  choose a ha using fun μ => limJ_exists p (fun n => c n μ) (fun n => hcn n μ)
  let u : PS O 1 d := fun μ => a μ
  have hu : ∀ μ, coeff μ u = a μ := fun μ => rfl
  have hJ : ∀ n k, psJet k (MvPowerSeries.map (π n) u) = U n k := by
    intro n k
    rw [limJ_psJet_eq Nat.one_pos hd, ← hP n k, truncTotalAlgHom_apply, limJ_mk_eq_iff]
    intro μ hμ
    rw [coeff_truncTotal _ hμ, coeff_map, hu, ha μ n, hck n μ k (by omega)]
  refine ⟨u, ⟨?_, ?_⟩, hJ⟩
  ·
    rw [← coeff_zero_eq_constantCoeff_apply, hu]
    apply limJ_unique p
    intro n
    rw [ha 0 n, map_one]
    have h1 : (Ideal.Quotient.mk _ (P n 0) : JetR _ (Fin 1 × Fin d) 0) = Ideal.Quotient.mk _ 1 := by
      rw [map_one, ← hZ n 0, ← hP n 0]
      rfl
    have h2 := (limJ_mk_eq_iff 0 _ _).1 h1 0 (by simp)
    rw [MvPolynomial.coeff_zero_one] at h2
    exact h2
  ·
    have hadd : addOf F.F (pt O (n := 2) d 0) (pt O d 1) = F.F :=
      funext fun i => limJ_ev_pts (F.F i)
    have hbL : ∀ q : Fin 1 × Fin d,
        (![addOf F.F (pt O (n := 2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2 = F.F q.2 := by
      intro q
      rw [Fin.fin_one_eq_zero q.1, hadd]
      rfl
    have hbLc : ∀ q : Fin 1 × Fin d,
        constantCoeff ((![addOf F.F (pt O (n := 2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by
      intro q; rw [hbL]; exact F.const _
    have hbP : ∀ (i : Fin 2) (q : Fin 1 × Fin d),
        (![pt O (n := 2) d i] : Fin 1 → Pt O 2 d) q.1 q.2 = X (i, q.2) := by
      intro i q
      rw [Fin.fin_one_eq_zero q.1]
      rfl
    have hbPc : ∀ (i : Fin 2) (q : Fin 1 × Fin d),
        constantCoeff ((![pt O (n := 2) d i] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by
      intro i q; rw [hbP]; simp
    ext ν
    apply limJ_unique p
    intro n
    rw [← coeff_map, ← coeff_map]
    refine (limJ_tt_eq_iff ν.degree _ _).1 ?_ ν (by omega)
    rw [← limJ_psJet_eq (by omega) hd, ← limJ_psJet_eq (by omega) hd]
    unfold ev
    rw [map_mul, map_subst (hasSubst_of_constantCoeff_zero hbLc), map_subst (hasSubst_of_constantCoeff_zero (hbPc 0)),
      map_subst (hasSubst_of_constantCoeff_zero (hbPc 1)), limJ_psJet_mul (by omega) hd]
    rw [limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbL]; exact Fmod_const p F n q.2) (Fmod p F n) (Fmod_const p F n)
        (fun q => by rw [hbL]; rfl),
      limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbP, map_X]; simp) (fun j => (MvPowerSeries.X ((0 : Fin 2), j) : PS _ 2 d))
        (fun j => by simp) (fun q => by rw [hbP, map_X]),
      limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbP, map_X]; simp) (fun j => (MvPowerSeries.X ((1 : Fin 2), j) : PS _ 2 d))
        (fun j => by simp) (fun q => by rw [hbP, map_X]), hJ]
    exact hM n ν.degree

end ReciprocityTheory.ChartRestriction.G.Pdiv.TL
