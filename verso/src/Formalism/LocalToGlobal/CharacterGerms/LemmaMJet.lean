import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
import Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)

variable {C : Type} [Field C] {σ τ : Type}

/- English proof (translation)
Simplify using `only [jetAt0, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem jet_add_right (P : MvPolynomial σ C) (G H : MvPowerSeries σ C) :
    jetAt0 P (G + H) = jetAt0 P G + jetAt0 P H := by
  simp only [jetAt0, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem jet_smul_right (P : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 P (a • G) = a * jetAt0 P G := by
  simp only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Simplify using `[jetAt0]`.
-/
theorem jet_zero_right (P : MvPolynomial σ C) : jetAt0 P (0 : MvPowerSeries σ C) = 0 := by
  simp [jetAt0]

/- English proof (translation)
Simplify using `only [jetAt0, map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem jet_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by
  simp only [jetAt0, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using `[jetAt0]`. Simplify using `[jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]`.
-/
theorem jet_C (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by
  by_cases ha : a = 0
  · subst ha
    simp [jetAt0]
  · simp [jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]

/- English proof (translation)
Unfold `mfact`. Use `set s := insert x m.support with hs`. Establish `hsub : (m + Finsupp.single x 1).support ⊆ s`. Introduce `y hy`. Break down `Finset.mem_union.1 (Finsupp.support_add hy) with h | h` into its components or cases.

Conclude with `Finset.mem_insert_of_mem h`. Rewrite `h` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`. Rewrite using `[h]`. Conclude with `Finset.mem_insert_self _ _`. Rewrite using `[Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero), Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]`.

Establish `hx : x ∈ s` using `Finset.mem_insert_self _ _`. Rewrite using `[← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]`. Establish `hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial` using `Finset.prod_congr rfl fun y hy => by`. Rewrite `hy` using `[Finset.mem_erase]`. Simplify using `[Finsupp.single_apply, Ne.symm hy.1]`.

Rewrite using `[hrest]`. Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfact_add_single (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by
  unfold mfact
  set s := insert x m.support with hs
  have hsub : (m + Finsupp.single x 1).support ⊆ s := by
    intro y hy
    rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  rw [Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]
  have hx : x ∈ s := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]
  have hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial :=
    Finset.prod_congr rfl fun y hy => by
      rw [Finset.mem_erase] at hy
      simp [Finsupp.single_apply, Ne.symm hy.1]
  rw [hrest]
  simp [Nat.factorial_succ]
  ring

/- English proof (translation)
Unfold `jetAt0`. Rewrite using `[MvPolynomial.support_mul_X, Finset.sum_map]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Establish `hd : MvPowerSeries.coeff n (dVar x G) = ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G` using `rfl`. Simplify using `only [addRightEmbedding_apply]`.

Rewrite using `[MvPolynomial.coeff_mul_X, mfact_add_single, hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jet_mul_X (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by
  unfold jetAt0
  rw [MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hd : MvPowerSeries.coeff n (dVar x G) =
      ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G := rfl
  simp only [addRightEmbedding_apply]
  rw [MvPolynomial.coeff_mul_X, mfact_add_single, hd]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[mul_comm p]`. Unfold `jetAt0`. Rewrite using `[Finset.mul_sum]`. Use `(Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)` and prove the remaining obligations. Introduce `m hm`.

Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]`. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[h, mul_zero]`.

Introduce `m _ hm`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]`. Rewrite using `[MvPolynomial.coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jet_mul_C (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by
  rw [mul_comm p]
  unfold jetAt0
  rw [Finset.mul_sum]
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h, mul_zero]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  · rw [MvPolynomial.coeff_C_mul]
    ring

def linT [Fintype σ] (M : τ → σ → C) : MvPolynomial τ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun c => ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on generalizing F with`. Consider the case `C a`. Establish `h : linT M (MvPolynomial.C a) = MvPolynomial.C a`. Unfold `linT`. Rewrite using `[MvPolynomial.aeval_C]`.

Both sides reduce to the same expression. Rewrite using `[h, jet_C, jet_C]`. Use `congr 1`. Establish `h0` using `coeff_subst_linS_congr M (F := F) (G := MvPowerSeries.C (constantCoeff F)) (N := 0) (fun μ hμ => by`. Establish `: μ = 0`.

Rewrite using `[← Finsupp.degree_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Use the proof step `simp) 0 (by simp)`. Rewrite `h0` using `[subst_linS_C]`.

Simplify using `using h0`. Consider the case `add p q hp hq => rw [map_add, tpjet_jetAt0_add, tpjet_jetAt0_add, hp, hq]`. Consider the case `mul_X p c hp`. Rewrite using `[jet_mul_X, dVar_subst_linS, jet_sum_right, map_mul]`. Establish `h : linT M (MvPolynomial.X c) = ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w`.

Unfold `linT`. Rewrite using `[MvPolynomial.aeval_X]`. Rewrite using `[h, Finset.mul_sum, tpjet_jetAt0_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[jet_smul_right, hp, ← mul_assoc, jet_mul_X, jet_mul_C]`.
-/
theorem jet_subst_linS [Fintype σ] [Fintype τ] (M : τ → σ → C) (Q : MvPolynomial τ C)
    (F : MvPowerSeries σ C) :
    jetAt0 Q (subst (linS M) F) = jetAt0 (linT M Q) F := by
  induction Q using MvPolynomial.induction_on generalizing F with
  | C a =>
    have h : linT M (MvPolynomial.C a) = MvPolynomial.C a := by
      unfold linT; rw [MvPolynomial.aeval_C]; rfl
    rw [h, jet_C, jet_C]
    congr 1
    have h0 := coeff_subst_linS_congr M (F := F) (G := MvPowerSeries.C (constantCoeff F)) (N := 0)
      (fun μ hμ => by
        have : μ = 0 := by
          rw [← Finsupp.degree_eq_zero_iff]; omega
        subst this
        simp) 0 (by simp)
    rw [subst_linS_C] at h0
    simpa using h0
  | add p q hp hq => rw [map_add, tpjet_jetAt0_add, tpjet_jetAt0_add, hp, hq]
  | mul_X p c hp =>
    rw [jet_mul_X, dVar_subst_linS, jet_sum_right, map_mul]
    have h : linT M (MvPolynomial.X c) = ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w := by
      unfold linT; rw [MvPolynomial.aeval_X]
    rw [h, Finset.mul_sum, tpjet_jetAt0_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [jet_smul_right, hp, ← mul_assoc, jet_mul_X, jet_mul_C]

/- English proof (translation)
Establish `hpow : ∀ k, OrdGE k (h ^ k)`. Introduce `k`. Use `ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)` as an intermediate fact. Simplify `this` using `[Finset.prod_const, Finset.card_range]`. Use `show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]`. Introduce `k hk hk'`.

Rewrite `hk`, `hk'` using `[Finset.mem_range]`. Rewrite using `[hpow k m (by omega), zero_div]`.
-/
theorem coeff_mvExp_partial {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]

/- English proof (translation)
Use extensionality with `e`. Establish `hsh : OrdGE 1 (subst a h)` using `ordGE_subst ha hh`. Rewrite using `[coeff_subst_congr ha (F := mvExp h) (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree) (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl, coeff_mvExp_partial hsh e.degree e le_rfl]`. Use `congr 1`. Rewrite using `[← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]`.

Simplify using `only [map_smul, map_pow]`.
-/
theorem subst_mvExp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]

end Formalism.L2.FormalSeriesBounds
