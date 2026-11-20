import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

/- English proof (translation)
Introduce `m hm`. Establish `hA : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `hA' : MvPowerSeries.HasSubst a'` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha'`. Establish `hdiff : ∀ i, a i - a' i ∈ Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}`. Introduce `i`.

Rewrite using `[Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Introduce `n hn`. Rewrite using `[map_sub, h i n hn, sub_self]`. Establish `hprod : ∀ e : σ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) = PowerSeries.coeff m (e.prod fun s n => a' s ^ n)`. Introduce `e`.

Establish `hq : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a s ^ n) = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a' s ^ n)`. Simplify using `only [Finsupp.prod, map_prod, map_pow]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq.2 (hdiff s)]`. Rewrite `hq` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`.

Establish `hm'` using `hq m hm`. Rewrite `hm'` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Simplify using `only [alongCv]`. Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) = MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a' f)`. Rewrite using `[MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hA']`.

Use `finsum_congr fun e => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `hprod e`.
-/
theorem coeff_alongCv_congr {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by
  intro m hm
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  have hdiff : ∀ i, a i - a' i ∈ Ideal.span {(PowerSeries.X : PowerSeries C) ^ k} := by
    intro i
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, h i n hn, sub_self]
  have hprod : ∀ e : σ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => a' s ^ n) := by
    intro e
    have hq : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a' s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Ideal.Quotient.eq.2 (hdiff s)]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hq
    have hm' := hq m hm
    rwa [map_sub, sub_eq_zero] at hm'
  simp only [alongCv]
  change MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a' f)
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hA']
  refine finsum_congr fun e => ?_
  congr 1
  exact hprod e

/- English proof (translation)
Simplify using `only [tyS, PowerSeries.coeff_mk]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hs : l ^ s = m`. Rewrite using `[if_pos hs, if_pos hs]`. Apply `hab` to reduce the goal to its premises.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : l ^ N ≤ l ^ s` using `Nat.pow_le_pow_right (by omega) hc`. Rewrite `h1` using `[hs]`. Conclude with `absurd hm (not_lt.2 h1)`.

Rewrite using `[if_neg hs, if_neg hs]`.
-/
theorem coeff_tyS_congr {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) (N : ℕ) (hab : ∀ i < N, a i = b i) (m : ℕ)
    (hm : m < l ^ N) : PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  simp only [tyS, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : l ^ s = m
  · rw [if_pos hs, if_pos hs]
    apply hab
    by_contra hc
    push_neg at hc
    have h1 : l ^ N ≤ l ^ s := Nat.pow_le_pow_right (by omega) hc
    rw [hs] at h1
    exact absurd hm (not_lt.2 h1)
  · rw [if_neg hs, if_neg hs]

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `only [tyS, PowerSeries.coeff_mk]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.constantCoeff (tyS l a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [tyS, PowerSeries.coeff_mk]
  simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst X.lg` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0`. Establish `hB : MvPowerSeries.HasSubst δ` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hδ`. Simplify using `only [alongCv]`. Rewrite using `[← MvPowerSeries.subst_comp_subst_apply hA hB, hexlg i, MvPowerSeries.subst_X hB]`.
-/
theorem curve_eq_ex_lg (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (δ : κ → PowerSeries C) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) (i : κ) :
    δ i = alongCv (fun j => alongCv δ (X.lg j)) (X.ex i) := by
  have hA : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hB : MvPowerSeries.HasSubst δ := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
  simp only [alongCv]
  rw [← MvPowerSeries.subst_comp_subst_apply hA hB, hexlg i, MvPowerSeries.subst_X hB]

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => rwa [Vpow_zero]`. Consider the case `succ s ih => rw [Vpow_succ]`. Conclude with `X.V_mem V g _ ih`.
-/
theorem Vpow_mem' (V : VF C) (g : Fin 2) (s : ℕ) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero => rwa [Vpow_zero]
  | succ s ih => rw [Vpow_succ]; exact X.V_mem V g _ ih

/- English proof (translation)
Establish `hl2` using `V.l_prime.two_le`. Establish `hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g` using `fun N => X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)`. Establish `hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n`. Introduce `N i hi n`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`.

Use `show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n`. Establish `hsub : Finset.range (i + 1) ⊆ Finset.range N` using `Finset.range_subset_range.2 (by omega)`. Rewrite using `[← Finset.sum_subset hsub]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Use `Finset.mem_range.1 hs` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `s _ hs`. Rewrite using `[if_pos]`. Establish `: ¬ s < i + 1` using `fun h => hs (Finset.mem_range.2 h)`.

Use linear arithmetic over natural numbers and integers. Use `choose γN lamN hγN hlamN h1N h2N using hP`. Use `set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA`. Establish `hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0`. Introduce `i`.

Rewrite using `[hA]`. Use `show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0`. Rewrite using `[map_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]`. Use `set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef`. Establish `hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0` using `fun i => constantCoeff_subst_zero hA0 (hex0 i)`. Establish `hlgγ : ∀ i, alongCv γ (X.lg i) = A i`. Introduce `i`.

Establish `hS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hA0`. Establish `e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i`. Rewrite using `[hlgex i, MvPowerSeries.subst_X hS]`. Rewrite using `[← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]`. Both sides reduce to the same expression.

Establish `htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) = PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n)`. Introduce `N n m hm`. Conclude with `coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm`. Establish `hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i)`. Introduce `N i m hm`.

Rewrite using `[X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]`. Use `coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm` and prove the remaining obligations. Introduce `j m' hm'`. Use `show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) = PowerSeries.coeff m' (alongCv (γN N) (X.lg j))`. Rewrite using `[h1N N j]`.

Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']`. Establish `hγI : IsCv V γ`. Introduce `i`.

Use `⟨hγ0 i, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[hγN' n i n (Nat.lt_pow_self (by omega))]`. Conclude with `(hγN n i).2 n`. Use `set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) + alongCv γ (X.sg (X.u (1 - g) q)) - ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef`. Establish `hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q)`.

Introduce `N q m hm`. Establish `e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) + alongCv (γN N) (X.sg (X.u (1 - g) q)) - ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) els …`. Rewrite using `[h2N N q]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hlamdef]`.

Use `show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) + alongCv γ (X.sg (X.u (1 - g) q)) - ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _`. Rewrite using `[map_sub, map_sub, map_add, map_add, map_sum, map_sum, htyN N _ m hm, coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]`. Both sides reduce to the same expression. Establish `hlamI : IsCv V lam`. Introduce `q`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp), PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(hlamN 0 q).1`. Rewrite using `[hlamN' n q n (Nat.lt_pow_self (by omega))]`. Conclude with `(hlamN n q).2 n`. Use `⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩` and prove the remaining obligations.

Introduce `q`. Establish `hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c`. Introduce `a b c`. Normalize the expressions using the abelian group laws. Conclude with `hab _ _ _`.
-/
theorem sumV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (y : ℕ → ℕ → I g ⊕ JJ I g → C) (hy : ∀ s, y s ∈ X.TySet V g) : sumV y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g := fun N =>
    X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)
  have hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n := by
    intro N i hi n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n
    have hsub : Finset.range (i + 1) ⊆ Finset.range N := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_neg]
      have := Finset.mem_range.1 hs
      omega
    · intro s _ hs
      rw [if_pos]
      have : ¬ s < i + 1 := fun h => hs (Finset.mem_range.2 h)
      omega
  choose γN lamN hγN hlamN h1N h2N using hP
  set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA
  have hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0 := by
    intro i
    rw [hA]
    show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]
  set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hA0 (hex0 i)
  have hlgγ : ∀ i, alongCv γ (X.lg i) = A i := by
    intro i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
    have e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i := by
      rw [hlgex i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]
    rfl
  have htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) =
      PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n) := by
    intro N n m hm
    exact coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm
  have hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i) := by
    intro N i m hm
    rw [X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]
    refine coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm
    intro j m' hm'
    show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) =
      PowerSeries.coeff m' (alongCv (γN N) (X.lg j))
    rw [h1N N j]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']
  have hγI : IsCv V γ := by
    intro i
    refine ⟨hγ0 i, fun n => ?_⟩
    rw [hγN' n i n (Nat.lt_pow_self (by omega))]
    exact (hγN n i).2 n
  set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef
  have hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q) := by
    intro N q m hm
    have e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) +
        alongCv (γN N) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) •
          tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) else 0) := by
      rw [h2N N q]
      abel
    rw [e, hlamdef]
    show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _
    rw [map_sub, map_sub, map_add, map_add, map_sum, map_sum, htyN N _ m hm,
      coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]
    · rfl
  have hlamI : IsCv V lam := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlamN 0 q).1
    · rw [hlamN' n q n (Nat.lt_pow_self (by omega))]
      exact (hlamN n q).2 n
  refine ⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩
  intro q
  have hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c := by
    intro a b c
    abel
  exact hab _ _ _

end RawChart

end Formalism.L2.FormalSeriesBounds
