import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffTripleSubstitution

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

/- English proof (translation)
Introduce `a ha`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Use `replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `hdeg : x.1.degree + x.2.degree = a.degree` using `by rw [← hx, map_add]`.

Distinguish the cases in `h1 : x.1.degree < k`. Rewrite using `[hp _ h1, zero_mul]`. Rewrite using `[hq _ (by omega), mul_zero]`.
-/
private theorem coeff_mul_eq_zero_of_degree_lt_add_character_germs {σ : Type} {p q : MvPowerSeries σ C} {k l : ℕ}
    (hp : ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a p = 0)
    (hq : ∀ a : σ →₀ ℕ, a.degree < l → MvPowerSeries.coeff a q = 0) :
    ∀ a : σ →₀ ℕ, a.degree < k + l → MvPowerSeries.coeff a (p * q) = 0 := by
  intro a ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = a.degree := by rw [← hx, map_add]
  by_cases h1 : x.1.degree < k
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a ha`. Conclude with `absurd ha (Nat.not_lt_zero _)`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Use `coeff_mul_eq_zero_of_degree_lt_add_character_germs ih fun a ha => ?_` and prove the remaining obligations. Establish `h0 : a = 0` using `(Finsupp.degree_eq_zero_iff a).mp (by omega)`. Rewrite using `[h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]`.
-/
private theorem coeff_pow_eq_zero_of_degree_lt_character_germs' {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ k : ℕ, ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a (f ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ k ih =>
    rw [pow_succ]
    refine coeff_mul_eq_zero_of_degree_lt_add_character_germs ih fun a ha => ?_
    have h0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

/- English proof (translation)
Use `show ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) = _`. Rewrite using `[← Finset.sum_range_add_sum_Ico _ (show m.degree + 1 ≤ N + 1 by omega)]`. Rewrite using `[Finset.sum_eq_zero (s := Finset.Ico (m.degree + 1) (N + 1)) (fun k hk => by`. Rewrite `hk` using `[Finset.mem_Ico]`. Rewrite using `[coeff_pow_eq_zero_of_degree_lt_character_germs' hf k m (by omega), zero_div]), add_zero]`.
-/
private theorem coeff_mvExp_eq_sum_range_of_degree_le {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (m : σ →₀ ℕ) (N : ℕ) (hN : m.degree ≤ N) :
    MvPowerSeries.coeff m (mvExp f) =
      ∑ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) := by
  show ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) = _
  rw [← Finset.sum_range_add_sum_Ico _ (show m.degree + 1 ≤ N + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (m.degree + 1) (N + 1)) (fun k hk => by
    rw [Finset.mem_Ico] at hk
    rw [coeff_pow_eq_zero_of_degree_lt_character_germs' hf k m (by omega), zero_div]), add_zero]

/- English proof (translation)
Use extensionality with `m`. Establish `hfg : MvPowerSeries.constantCoeff (f + g) = 0` using `by rw [map_add, hf, hg, add_zero]`. Use `set N := m.degree with hN`. Establish `hT : ∀ i j : ℕ, N < i + j → MvPowerSeries.coeff m (f ^ i * g ^ j) = 0` using `fun i j h => coeff_mul_eq_zero_of_degree_lt_add_character_germs (coeff_pow_eq_zero_of_degree_lt_character_germs' hf i) (coeff_pow_eq_zero_of_degree_lt_character_germs' hg j) m (by omega)`. Establish `hL : MvPowerSeries.coeff m (mvExp (f + g)) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))`.

Rewrite using `[coeff_mvExp_eq_sum_range_of_degree_le hfg m N le_rfl]`. Establish `hk : ∀ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m ((f + g) ^ k) / (k.factorial : C) = ∑ i ∈ Finset.range (k + 1), MvPowerSeries.coeff m (f ^ i * g ^ (k - i)) / ((i.factorial : C) * ((k - i).factorial : C))`. Introduce `k _`. Rewrite using `[add_pow, map_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hik : i ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Rewrite using `[← nsmul_eq_mul', map_nsmul, nsmul_eq_mul, Nat.cast_choose C hik]`. Establish `h1 : (k.factorial : C) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)`. Establish `h2 : (i.factorial : C) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)`. Establish `h3 : ((k - i).factorial : C) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[Finset.sum_congr rfl hk]`. Rewrite using `[Finset.sum_range_diag_flip (N + 1) fun i j => MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Use `Finset.sum_subset (fun j hj => by` and prove the remaining obligations.

Rewrite `hj`, the goal using `[Finset.mem_range]`. Use the proof step `omega) fun j hj hj' => ?_`. Rewrite `hj`, `hj'` using `[Finset.mem_range]`. Rewrite using `[hT i j (by omega), zero_div]`. Establish `hR : MvPowerSeries.coeff m (mvExp f * mvExp g) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))`.

Rewrite using `[MvPowerSeries.coeff_mul]`. Establish `hx : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, MvPowerSeries.coeff x.1 (mvExp f) * MvPowerSeries.coeff x.2 (mvExp g) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j) / ((i.factorial : C) * (j.factorial …`. Introduce `x hx`. Use `replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `hd : x.1.degree + x.2.degree = N` using `by rw [hN, ← hx, map_add]`.

Rewrite using `[coeff_mvExp_eq_sum_range_of_degree_le hf x.1 N (by omega), coeff_mvExp_eq_sum_range_of_degree_le hg x.2 N (by omega), Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[div_mul_div_comm]`. Rewrite using `[Finset.sum_congr rfl hx, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_mul, Finset.sum_div]`. Rewrite using `[hL, hR]`.
-/
theorem exp_add {σ : Type} {f g : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  ext m
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  set N := m.degree with hN
  have hT : ∀ i j : ℕ, N < i + j → MvPowerSeries.coeff m (f ^ i * g ^ j) = 0 :=
    fun i j h => coeff_mul_eq_zero_of_degree_lt_add_character_germs (coeff_pow_eq_zero_of_degree_lt_character_germs' hf i) (coeff_pow_eq_zero_of_degree_lt_character_germs' hg j) m (by omega)

  have hL : MvPowerSeries.coeff m (mvExp (f + g)) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [coeff_mvExp_eq_sum_range_of_degree_le hfg m N le_rfl]
    have hk : ∀ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m ((f + g) ^ k) / (k.factorial : C) =
        ∑ i ∈ Finset.range (k + 1), MvPowerSeries.coeff m (f ^ i * g ^ (k - i)) /
          ((i.factorial : C) * ((k - i).factorial : C)) := by
      intro k _
      rw [add_pow, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← nsmul_eq_mul', map_nsmul, nsmul_eq_mul, Nat.cast_choose C hik]
      have h1 : (k.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have h2 : (i.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have h3 : ((k - i).factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    rw [Finset.sum_congr rfl hk]
    rw [Finset.sum_range_diag_flip (N + 1) fun i j =>
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_subset (fun j hj => by
      rw [Finset.mem_range] at hj ⊢
      omega) fun j hj hj' => ?_
    rw [Finset.mem_range] at hj hj'
    rw [hT i j (by omega), zero_div]

  have hR : MvPowerSeries.coeff m (mvExp f * mvExp g) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [MvPowerSeries.coeff_mul]
    have hx : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, MvPowerSeries.coeff x.1 (mvExp f) * MvPowerSeries.coeff x.2 (mvExp g) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j) /
            ((i.factorial : C) * (j.factorial : C)) := by
      intro x hx
      replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hd : x.1.degree + x.2.degree = N := by rw [hN, ← hx, map_add]
      rw [coeff_mvExp_eq_sum_range_of_degree_le hf x.1 N (by omega), coeff_mvExp_eq_sum_range_of_degree_le hg x.2 N (by omega), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_div_comm]
    rw [Finset.sum_congr rfl hx, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_div]
  rw [hL, hR]

/- English proof (translation)
Use `first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Consider the case `exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩`.
-/
private theorem hasSubst_of_Z0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

/- English proof (translation)
Introduce `q`. Simplify using `only [P2]`. Use `split_ifs`. Use `exacts [ha _, hb _]`.
-/
private theorem constantCoeff_P2_eq_zero {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : ∀ q, MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
  intro q
  simp only [P2]
  split_ifs
  exacts [ha _, hb _]

/- English proof (translation)
Introduce `q`. Simplify using `only [P3]`. Use `split_ifs`. Use `exacts [ha _, hb _, hc _]`.
-/
private theorem constantCoeff_P3_eq_zero {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    ∀ q, MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  intro q
  simp only [P3]
  split_ifs
  exacts [ha _, hb _, hc _]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_mvExp_eq_sum_range_of_degree_le (map_zero _) m m.degree le_rfl, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[zero_pow hk, map_zero, zero_div]`.

Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h`.
-/
private theorem mvExp_zero_character_germs {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp_eq_sum_range_of_degree_le (map_zero _) m m.degree le_rfl, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[Nat.cast_zero, zero_smul, pow_zero]`. Conclude with `mvExp_zero_character_germs`. Consider the case `succ k ih`.

Establish `hk : MvPowerSeries.constantCoeff ((k : C) • f) = 0` using `by simp [hf]`. Rewrite using `[Nat.cast_succ, add_smul, one_smul, exp_add hk hf, ih, pow_succ]`.
-/
theorem exp_nsmul {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) (k : ℕ) :
    mvExp ((k : C) • f) = mvExp f ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact mvExp_zero_character_germs
  | succ k ih =>
    have hk : MvPowerSeries.constantCoeff ((k : C) • f) = 0 := by simp [hf]
    rw [Nat.cast_succ, add_smul, one_smul, exp_add hk hf, ih, pow_succ]

variable (Y : FBChart C V O dd)

section Subst

variable [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
  {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
  (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)

include hA hu hv in
/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (constantCoeff_P2_eq_zero hu hv)) (hasSubst_of_Z0 hA)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [P2]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem subst_pair_substitution_comm (f : PS C 2 dd) :
    MvPowerSeries.subst A (MvPowerSeries.subst (P2 u v) f) =
      MvPowerSeries.subst (P2 (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i))) f := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (constantCoeff_P2_eq_zero hu hv)) (hasSubst_of_Z0 hA)]
  congr 1
  funext q
  simp only [P2]
  split_ifs <;> rfl

include hA hu hv in
/- English proof (translation)
The claim follows from `subst_pair_substitution_comm hA hu hv Y.h`.
-/
theorem hAt_subst : MvPowerSeries.subst A (hAt Y u v) =
    hAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) :=  subst_pair_substitution_comm hA hu hv Y.h

include hA hu hv in
/- English proof (translation)
The claim follows from `subst_pair_substitution_comm hA hu hv (Y.B.G.F i)`.
-/
theorem addAt_subst (i : Fin dd) : MvPowerSeries.subst A (addAt Y u v i) =
    addAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) i :=  subst_pair_substitution_comm hA hu hv (Y.B.G.F i)

include hA hu in
/- English proof (translation)
Use `show MvPowerSeries.subst A (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => u q.2) (Y.B.A.act x i)) = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst A (u q.2)) (Y.B.A.act x i)`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => u q.2) fun q => hu q.2) (hasSubst_of_Z0 hA)]`.
-/
theorem actAt_subst (x : O) (i : Fin dd) : MvPowerSeries.subst A (actAt Y x u i) =
    actAt Y x (fun i => MvPowerSeries.subst A (u i)) i := by
  show MvPowerSeries.subst A (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => u q.2) (Y.B.A.act x i)) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst A (u q.2)) (Y.B.A.act x i)
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => u q.2) fun q => hu q.2) (hasSubst_of_Z0 hA)]

end Subst

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (constantCoeff_P2_eq_zero ha hb)) (constantCoeff_P2_eq_zero ha hb) (Y.B.G.const i)`.
-/
theorem cc_addAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (addAt Y a b i) = 0 :=  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (constantCoeff_P2_eq_zero ha hb))
    (constantCoeff_P2_eq_zero ha hb) (Y.B.G.const i)

/- English proof (translation)
Use `show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst (P2 x y) Y.h`. Use `congr 1`. Use function extensionality and compare the values at `q`. Break down `q with ⟨j, l⟩` into its components or cases. Apply the tactic sequence `fin_cases j <;> first | rfl | simp [P2]`.
-/
private theorem ev_pt_pair {n : ℕ} (x y : Pt C n dd) : ev (n := n) ![x, y] Y.h = hAt Y x y := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst (P2 x y) Y.h
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl | simp [P2]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![a, b] : Fin 2 → Pt C n dd) p.1 p.2) (MvPowerSeries.map (algebraMap C C) (Y.B.G.F i)) = MvPowerSeries.subst (P2 a b) (Y.B.G.F i)`. Establish `hm : MvPowerSeries.map (algebraMap C C) (Y.B.G.F i) = Y.B.G.F i`. Use extensionality with `n`. Simplify using `[MvPowerSeries.coeff_map]`.

Rewrite using `[hm]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Break down `q with ⟨j, l⟩` into its components or cases. Apply the tactic sequence `fin_cases j <;> first | rfl | simp [P2]`.
-/
theorem addOf_eq {n : ℕ} (a b : Pt C n dd) : addOf (Y.B.FK C) a b = addAt Y a b := by
  funext i
  show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![a, b] : Fin 2 → Pt C n dd) p.1 p.2)
      (MvPowerSeries.map (algebraMap C C) (Y.B.G.F i)) = MvPowerSeries.subst (P2 a b) (Y.B.G.F i)
  have hm : MvPowerSeries.map (algebraMap C C) (Y.B.G.F i) = Y.B.G.F i := by
    ext n
    simp [MvPowerSeries.coeff_map]
  rw [hm]
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl | simp [P2]

section Three

variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)

include ha hb hc

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((0 : Fin 3), i)) = a i`. Rewrite using `[MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]`. Simplify using `[P3]`.
-/
theorem triple_subst_first_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (0 : Fin 3) i)) = a := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((0 : Fin 3), i)) = a i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((1 : Fin 3), i)) = b i`. Rewrite using `[MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]`. Simplify using `[P3]`.
-/
theorem triple_subst_second_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (1 : Fin 3) i)) = b := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((1 : Fin 3), i)) = b i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((2 : Fin 3), i)) = c i`. Rewrite using `[MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]`. Simplify using `[P3]`.
-/
theorem triple_subst_third_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (2 : Fin 3) i)) = c := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((2 : Fin 3), i)) = c i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

/- English proof (translation)
Establish `hp : ∀ (j : Fin 3) (i : Fin dd), MvPowerSeries.constantCoeff (pt C dd j i : PS C 3 dd) = 0` using `fun j i => MvPowerSeries.constantCoeff_X _`. Establish `hP3` using `constantCoeff_P3_eq_zero ha hb hc`. Establish `hg` using `Y.gauge.ph2`. Rewrite `hg` using `[toK_eq, ev_pt_pair Y, ev_pt_pair Y, ev_pt_pair Y, addOf_eq]`. Establish `hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd 0) (pt C dd 1) + hAt Y (pt C dd 0) (pt C dd 2) - hAt Y (pt C dd (0 : Fin 3)) (addAt Y (pt C dd 1) (pt C dd 2))) = 0`.

Rewrite using `[map_sub, map_add, cc_hAt Y (hp 0) (hp 1), cc_hAt Y (hp 0) (hp 2), cc_hAt Y (hp 0) (cc_addAt Y (hp 1) (hp 2))]`. Simplify using the standard rewrite rules. Rewrite using `[hg, expS_eq _ hcc, subst_exp hP3 hcc]`. Use `congr 1`. Rewrite using `[← MvPowerSeries.coe_substAlgHom (hasSubst_of_Z0 hP3), map_sub, map_add, MvPowerSeries.coe_substAlgHom]`.

Rewrite using `[hAt_subst Y hP3 (hp 0) (hp 1), hAt_subst Y hP3 (hp 0) (hp 2), hAt_subst Y hP3 (hp 0) (cc_addAt Y (hp 1) (hp 2))]`. Establish `haddS : (fun i => MvPowerSeries.subst (P3 a b c) (addAt Y (pt C dd (1 : Fin 3)) (pt C dd 2) i)) = addAt Y b c`. Use function extensionality and compare the values at `i`. Rewrite using `[addAt_subst Y hP3 (hp 1) (hp 2) i, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]`. Rewrite using `[haddS, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]`.
-/
theorem second_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph2 =
    mvExp (hAt Y a b + hAt Y a c - hAt Y a (addAt Y b c)) := by
  have hp : ∀ (j : Fin 3) (i : Fin dd), MvPowerSeries.constantCoeff (pt C dd j i : PS C 3 dd) = 0 :=
    fun j i => MvPowerSeries.constantCoeff_X _
  have hP3 := constantCoeff_P3_eq_zero ha hb hc
  have hg := Y.gauge.ph2
  rw [toK_eq, ev_pt_pair Y, ev_pt_pair Y, ev_pt_pair Y, addOf_eq] at hg
  have hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd 0) (pt C dd 1) + hAt Y (pt C dd 0) (pt C dd 2) -
      hAt Y (pt C dd (0 : Fin 3)) (addAt Y (pt C dd 1) (pt C dd 2))) = 0 := by
    rw [map_sub, map_add, cc_hAt Y (hp 0) (hp 1), cc_hAt Y (hp 0) (hp 2),
      cc_hAt Y (hp 0) (cc_addAt Y (hp 1) (hp 2))]
    simp
  rw [hg, expS_eq _ hcc, subst_exp hP3 hcc]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_Z0 hP3), map_sub, map_add, MvPowerSeries.coe_substAlgHom]
  rw [hAt_subst Y hP3 (hp 0) (hp 1), hAt_subst Y hP3 (hp 0) (hp 2),
    hAt_subst Y hP3 (hp 0) (cc_addAt Y (hp 1) (hp 2))]
  have haddS : (fun i => MvPowerSeries.subst (P3 a b c) (addAt Y (pt C dd (1 : Fin 3)) (pt C dd 2) i)) =
      addAt Y b c := by
    funext i
    rw [addAt_subst Y hP3 (hp 1) (hp 2) i, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]
  rw [haddS, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]

end Three

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act (x + y) i) = MvPowerSeries.subst (P2 (actAt Y x a) (actAt Y y a)) (Y.B.G.F i)`. Rewrite using `[Y.B.A.add_act]`. Use `show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![Y.B.A.act x, Y.B.A.act y] : Fin 2 → Pt C 1 dd) p.1 p.2) (Y.B.G.F i)) = _`. Establish `hcc : ∀ p : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((![Y.B.A.act x, Y.B.A.act y] : Fin 2 → Pt C 1 dd) p.1 p.2) = 0`.

Introduce `p`. Break down `p with ⟨j, l⟩` into its components or cases. Use `fin_cases j`. Conclude with `Y.B.A.const _ _`. Conclude with `Y.B.A.const _ _`.

Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 hcc) (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Break down `q with ⟨j, l⟩` into its components or cases. Use `fin_cases j`.

Apply the tactic sequence `first | rfl | simp [P2, actAt]`. Apply the tactic sequence `first | rfl | simp [P2, actAt]`.
-/
theorem actAt_add (x y : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    actAt Y (x + y) a = addAt Y (actAt Y x a) (actAt Y y a) := by
  funext i
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act (x + y) i) =
    MvPowerSeries.subst (P2 (actAt Y x a) (actAt Y y a)) (Y.B.G.F i)
  rw [Y.B.A.add_act]
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2)
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![Y.B.A.act x, Y.B.A.act y] : Fin 2 → Pt C 1 dd) p.1 p.2)
        (Y.B.G.F i)) = _
  have hcc : ∀ p : Fin 2 × Fin dd,
      MvPowerSeries.constantCoeff ((![Y.B.A.act x, Y.B.A.act y] : Fin 2 → Pt C 1 dd) p.1 p.2) = 0 := by
    intro p
    rcases p with ⟨j, l⟩
    fin_cases j
    · exact Y.B.A.const _ _
    · exact Y.B.A.const _ _
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 hcc) (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2)]
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j
  · first | rfl | simp [P2, actAt]
  · first | rfl | simp [P2, actAt]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act 1 i) = a i`. Rewrite using `[Y.B.A.one_act]`. Use `show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (MvPowerSeries.X ((0 : Fin 1), i)) = a i`. Rewrite using `[MvPowerSeries.subst_X (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2)]`.
-/
theorem actAt_one {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    actAt Y 1 a = a := by
  funext i
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act 1 i) = a i
  rw [Y.B.A.one_act]
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (MvPowerSeries.X ((0 : Fin 1), i)) = a i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2)]

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2) (fun q => ha q.2) (Y.B.A.const x i)`.
-/
private theorem constantCoeff_actAt_eq_zero (x : O) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (actAt Y x a i) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => a q.2) fun q => ha q.2)
    (fun q => ha q.2) (Y.B.A.const x i)

/- English proof (translation)
Establish `hwX` using `constantCoeff_actAt_eq_zero Y Y.w0 hX`. Establish `hwZ` using `constantCoeff_actAt_eq_zero Y Y.w0 hZ`. Establish `hbZ` using `constantCoeff_actAt_eq_zero Y (star Y.w0) hZ`. Establish `hsum : addAt Y (actAt Y Y.w0 Z) (actAt Y (star Y.w0) Z) = Z`. Rewrite using `[← actAt_add Y _ _ hZ, Y.halfIntegralGenerator_add_conj_eq_one, actAt_one Y hZ]`.

Establish `h1 : MvPowerSeries.constantCoeff (hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z) = 0`. Rewrite using `[map_sub, cc_hAt Y hZ hwX, cc_hAt Y hwX hZ, sub_zero]`. Establish `h2 : MvPowerSeries.constantCoeff (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z)) = 0`. Rewrite using `[map_sub, cc_hAt Y hwX hZ, cc_hAt Y hX hbZ, sub_zero]`. Establish `h3 : MvPowerSeries.constantCoeff (hAt Y X (actAt Y Y.w0 Z) + hAt Y X (actAt Y (star Y.w0) Z) - hAt Y X Z) = 0`.

Rewrite using `[map_sub, map_add, cc_hAt Y hX hwZ, cc_hAt Y hX hbZ, cc_hAt Y hX hZ]`. Simplify using the standard rewrite rules. Establish `h12 : MvPowerSeries.constantCoeff ((hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z) + (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z))) = 0`. Rewrite using `[map_add, h1, h2, add_zero]`. Establish `hsy : MvPowerSeries.subst (P2 (actAt Y Y.w0 X) Z) Y.B.sy = mvExp (hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z)` using `by first`.

Consider the case `exact sy_at Y hwX hZ`. Consider the case `exact sy_at Y`. Consider the case `exact sy_at`. Establish `had : MvPowerSeries.subst (P2 X Z) (Y.B.ad Y.w0) = mvExp (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z))` using `by first`. Consider the case `exact ad_at Y hX hZ Y.w0`.

Consider the case `exact ad_at Y Y.w0`. Consider the case `exact ad_at Y (x := Y.w0)`. Rewrite using `[hsy, had, second_partial_law_at_points Y hX hwZ hbZ, hsum, ← exp_add h1 h2, ← exp_add h12 h3]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_id {X Z : Fin dd → MvPowerSeries τ C} (hX : ∀ i, MvPowerSeries.constantCoeff (X i) = 0)
    (hZ : ∀ i, MvPowerSeries.constantCoeff (Z i) = 0) :
    mvExp (hAt Y X (actAt Y Y.w0 Z) + hAt Y Z (actAt Y Y.w0 X) - hAt Y X Z) =
      MvPowerSeries.subst (P2 (actAt Y Y.w0 X) Z) Y.B.sy * MvPowerSeries.subst (P2 X Z) (Y.B.ad Y.w0) *
        MvPowerSeries.subst (P3 X (actAt Y Y.w0 Z) (actAt Y (star Y.w0) Z)) Y.B.ph2 := by
  have hwX := constantCoeff_actAt_eq_zero Y Y.w0 hX
  have hwZ := constantCoeff_actAt_eq_zero Y Y.w0 hZ
  have hbZ := constantCoeff_actAt_eq_zero Y (star Y.w0) hZ
  have hsum : addAt Y (actAt Y Y.w0 Z) (actAt Y (star Y.w0) Z) = Z := by
    rw [← actAt_add Y _ _ hZ, Y.halfIntegralGenerator_add_conj_eq_one, actAt_one Y hZ]
  have h1 : MvPowerSeries.constantCoeff (hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z) = 0 := by
    rw [map_sub, cc_hAt Y hZ hwX, cc_hAt Y hwX hZ, sub_zero]
  have h2 : MvPowerSeries.constantCoeff (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z)) = 0 := by
    rw [map_sub, cc_hAt Y hwX hZ, cc_hAt Y hX hbZ, sub_zero]
  have h3 : MvPowerSeries.constantCoeff (hAt Y X (actAt Y Y.w0 Z) + hAt Y X (actAt Y (star Y.w0) Z) -
      hAt Y X Z) = 0 := by
    rw [map_sub, map_add, cc_hAt Y hX hwZ, cc_hAt Y hX hbZ, cc_hAt Y hX hZ]
    simp
  have h12 : MvPowerSeries.constantCoeff ((hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z) +
      (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z))) = 0 := by
    rw [map_add, h1, h2, add_zero]
  have hsy : MvPowerSeries.subst (P2 (actAt Y Y.w0 X) Z) Y.B.sy =
      mvExp (hAt Y Z (actAt Y Y.w0 X) - hAt Y (actAt Y Y.w0 X) Z) := by
    first
    | exact sy_at Y hwX hZ
    | exact sy_at Y
    | exact sy_at
  have had : MvPowerSeries.subst (P2 X Z) (Y.B.ad Y.w0) =
      mvExp (hAt Y (actAt Y Y.w0 X) Z - hAt Y X (actAt Y (star Y.w0) Z)) := by
    first
    | exact ad_at Y hX hZ Y.w0
    | exact ad_at Y Y.w0
    | exact ad_at Y (x := Y.w0)
  rw [hsy, had, second_partial_law_at_points Y hX hwZ hbZ, hsum, ← exp_add h1 h2, ← exp_add h12 h3]
  congr 1
  ring

end VP

end Formalism.L2.FormalSeriesBounds
