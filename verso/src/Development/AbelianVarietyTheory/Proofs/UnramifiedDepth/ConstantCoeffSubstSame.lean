import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves

noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {k : Type} [CommRing k]

def OrdGE {σ : Type} (r : ℕ) (g : MvPowerSeries σ k) : Prop := ∀ e : σ →₀ ℕ, e.degree < r → coeff e g = 0

/- English proof (translation)
Introduce `_ h` and use `absurd h (Nat.not_lt_zero _)`.
-/
theorem ordGE_zero_left {σ : Type} (g : MvPowerSeries σ k) : OrdGE 0 g := fun _ h => absurd h (Nat.not_lt_zero _)

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `hdeg : p.1.degree + p.2.degree = e.degree` using `by rw [← map_add, hp]`. Distinguish the cases in `h1 : p.1.degree < a`. Rewrite using `[hf _ h1, zero_mul]`. Establish `h2 : p.2.degree < b` using `by omega`. Rewrite using `[hg _ h2, mul_zero]`.
-/
theorem ordGE_mul {σ : Type} {a b : ℕ} {f g : MvPowerSeries σ k} (hf : OrdGE a f) (hg : OrdGE b g) :
    OrdGE (a + b) (f * g) := by
  classical
  intro e he
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = e.degree := by rw [← map_add, hp]
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · have h2 : p.2.degree < b := by omega
    rw [hg _ h2, mul_zero]

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]`.
-/
theorem ordGE_pderiv {σ : Type} {r : ℕ} (i : σ) {g : MvPowerSeries σ k} (h : OrdGE (r + 1) g) :
    OrdGE r (pderiv k i g) := by
  intro e he
  rw [coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

/- English proof (translation)
Introduce `e he`. Establish `he0 : e = 0` using `(Finsupp.degree_eq_zero_iff e).1 (by omega)`. Substitute `he0` using the available equality. Rewrite using `[coeff_zero_eq_constantCoeff_apply, h]`.
-/
theorem ordGE_one_of_const {σ : Type} {A : MvPowerSeries σ k} (h : constantCoeff A = 0) : OrdGE 1 A := by
  intro e he
  have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
  subst he0
  rw [coeff_zero_eq_constantCoeff_apply, h]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ordGE_zero_left _`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `ordGE_mul ih hA`.
-/
theorem ordGE_pow {σ : Type} {A : MvPowerSeries σ k} (hA : OrdGE 1 A) (n : ℕ) : OrdGE n (A ^ n) := by
  induction n with
  | zero => exact ordGE_zero_left _
  | succ n ih =>
    rw [pow_succ]
    exact ordGE_mul ih hA

/- English proof (translation)
Rewrite using `[Finsupp.degree_apply]`. Unfold `Finsupp.prod`. Proceed by induction on `dd.support using Finset.induction_on with`. Consider the case `empty => simpa using ordGE_zero_left (1 : MvPowerSeries σ k)`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `ordGE_mul (ordGE_pow (hA a) _) ih`.
-/
theorem ordGE_finsuppProd {σ τ : Type} (A : τ → MvPowerSeries σ k) (hA : ∀ s, OrdGE 1 (A s)) (dd : τ →₀ ℕ) :
    OrdGE dd.degree (dd.prod fun s n => A s ^ n) := by
  classical
  rw [Finsupp.degree_apply]
  unfold Finsupp.prod
  induction dd.support using Finset.induction_on with
  | empty => simpa using ordGE_zero_left (1 : MvPowerSeries σ k)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ordGE_mul (ordGE_pow (hA a) _) ih

/- English proof (translation)
Introduce `e he`. Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Rewrite using `[coeff_subst hs]`. Establish `hz : ∀ d : σ →₀ ℕ, coeff d g • coeff e (d.prod fun s n => a s ^ n) = 0`. Introduce `d`.

Distinguish the cases in `hd : d.degree < r`. Rewrite using `[hg d hd, zero_smul]`. Rewrite using `[ordGE_finsuppProd a (fun s => ordGE_one_of_const (ha s)) d e (by omega), smul_zero]`. Simplify using `only [hz, finsum_zero]`.
-/
theorem ordGE_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0)
    {r : ℕ} {g : MvPowerSeries σ k} (hg : OrdGE r g) : OrdGE r (subst a g) := by
  intro e he
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs]
  have hz : ∀ d : σ →₀ ℕ, coeff d g • coeff e (d.prod fun s n => a s ^ n) = 0 := by
    intro d
    by_cases hd : d.degree < r
    · rw [hg d hd, zero_smul]
    · rw [ordGE_finsuppProd a (fun s => ordGE_one_of_const (ha s)) d e (by omega), smul_zero]
  simp only [hz, finsum_zero]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]`. Consider the case `mul_X p s hp`. Rewrite using `[map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp]`.

Simplify using `only [Derivation.leibniz, MvPolynomial.pderiv_X, map_add, smul_eq_mul, add_mul, Finset.sum_add_distrib, map_mul, MvPolynomial.aeval_X, Pi.single_apply]`. Simplify using `only [Finset.mul_sum]`. Simplify using `only [apply_ite (MvPolynomial.aeval a), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Put the polynomial expressions in normal form.
-/
theorem pderiv_aeval {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ k) (p : MvPolynomial σ k) (t : τ) :
    pderiv k t (MvPolynomial.aeval a p) =
      ∑ s, MvPolynomial.aeval a (MvPolynomial.pderiv s p) * pderiv k t (a s) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p s hp =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp]
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, map_add, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      map_mul, MvPolynomial.aeval_X, Pi.single_apply]
    simp only [Finset.mul_sum]
    simp only [apply_ite (MvPolynomial.aeval a), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring_nf

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Use extensionality with `e`. Establish `key : ∀ g : MvPowerSeries σ k, OrdGE (e.degree + 1 + 1) g → coeff e (pderiv k t (subst a g)) = 0 ∧ coeff e (∑ s, subst a (pderiv k s g) * pderiv k t (a s)) = 0`. Introduce `g hg`. Use `⟨ordGE_pderiv t (ordGE_subst a ha hg) e (by omega), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Conclude with `ordGE_mul (ordGE_subst a ha (ordGE_pderiv s hg)) (ordGE_zero_left (pderiv k t (a s))) e (by omega)`. Use `set p := truncTotal (e.degree + 1 + 1) f`. Establish `hr : OrdGE (e.degree + 1 + 1) (f - (p : MvPowerSeries σ k))`.

Introduce `d hd`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]`. Take `⟨h1, h2⟩` from `key _ hr`. Establish `hf : f = (p : MvPowerSeries σ k) + (f - p)` using `by ring`. Rewrite using `[hf, subst_add hs, map_add, map_add, h1, add_zero]`.

Simplify using `only [map_add, subst_add hs, add_mul, Finset.sum_add_distrib]`. Rewrite using `[h2, add_zero, subst_coe, pderiv_aeval]`. Simplify using `only [pderiv_coe, subst_coe]`.
-/
theorem pderiv_subst {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  ext e
  have key : ∀ g : MvPowerSeries σ k, OrdGE (e.degree + 1 + 1) g →
      coeff e (pderiv k t (subst a g)) = 0 ∧ coeff e (∑ s, subst a (pderiv k s g) * pderiv k t (a s)) = 0 := by
    intro g hg
    refine ⟨ordGE_pderiv t (ordGE_subst a ha hg) e (by omega), ?_⟩
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    exact ordGE_mul (ordGE_subst a ha (ordGE_pderiv s hg)) (ordGE_zero_left (pderiv k t (a s))) e (by omega)
  set p := truncTotal (e.degree + 1 + 1) f
  have hr : OrdGE (e.degree + 1 + 1) (f - (p : MvPowerSeries σ k)) := by
    intro d hd
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
  obtain ⟨h1, h2⟩ := key _ hr
  have hf : f = (p : MvPowerSeries σ k) + (f - p) := by ring
  rw [hf, subst_add hs, map_add, map_add, h1, add_zero]
  simp only [map_add, subst_add hs, add_mul, Finset.sum_add_distrib]
  rw [h2, add_zero, subst_coe, pderiv_aeval]
  simp only [pderiv_coe, subst_coe]

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Establish `hf : f = C (constantCoeff f) + (f - C (constantCoeff f))` using `by ring`. Rewrite using `[hf, subst_add hs, map_add, subst_C, constantCoeff_subst_eq_zero hs ha (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_subst_same {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ k) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hf : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  rw [hf, subst_add hs, map_add, subst_C, constantCoeff_subst_eq_zero hs ha (by simp)]
  simp

/- English proof (translation)
Use extensionality with `x`. Establish `hc : ∀ t, constantCoeff (killCompl e (X t) : MvPowerSeries σ k) = 0` using `fun t => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]`. Establish `hs` using `hasSubst_of_constantCoeff_zero hc`. Rewrite using `[coeff_subst hs, finsum_eq_single _ (Finsupp.embDomain e x), coeff_killCompl]`.

Establish `: (Finsupp.embDomain e x).prod (fun s n => (killCompl e (X s) : MvPowerSeries σ k) ^ n) = killCompl e (monomial (Finsupp.embDomain e x) 1)`. Rewrite using `[monomial_one_eq, map_finsuppProd]`. Simplify using `only [map_pow]`. Rewrite using `[this, coeff_killCompl, coeff_monomial_same, smul_eq_mul, mul_one]`. Introduce `d hd`.

Establish `: d.prod (fun s n => (killCompl e (X s) : MvPowerSeries σ k) ^ n) = killCompl e (monomial d 1)`. Rewrite using `[monomial_one_eq, map_finsuppProd]`. Simplify using `only [map_pow]`. Rewrite using `[this, coeff_killCompl, coeff_monomial, if_neg (Ne.symm hd), smul_zero]`.
-/
theorem killCompl_eq_subst {σ τ : Type} [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ k) :
    killCompl e f = subst (fun t => (killCompl e (X t) : MvPowerSeries σ k)) f := by
  classical
  ext x
  have hc : ∀ t, constantCoeff (killCompl e (X t) : MvPowerSeries σ k) = 0 := fun t => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hs := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst hs, finsum_eq_single _ (Finsupp.embDomain e x), coeff_killCompl]
  · have : (Finsupp.embDomain e x).prod (fun s n => (killCompl e (X s) : MvPowerSeries σ k) ^ n) =
        killCompl e (monomial (Finsupp.embDomain e x) 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow]
    rw [this, coeff_killCompl, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    have : d.prod (fun s n => (killCompl e (X s) : MvPowerSeries σ k) ^ n) = killCompl e (monomial d 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow]
    rw [this, coeff_killCompl, coeff_monomial, if_neg (Ne.symm hd), smul_zero]

/- English proof (translation)
Establish `hc : ∀ t, constantCoeff (killCompl e (X t) : MvPowerSeries σ k) = 0` using `fun t => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]`. Rewrite using `[killCompl_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero hc)]`. Simplify using `only [← killCompl_eq_subst]`.
-/
theorem killCompl_subst {σ τ υ : Type} [Finite τ] [Finite υ] (e : σ ↪ τ) {a : υ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries υ k) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  have hc : ∀ t, constantCoeff (killCompl e (X t) : MvPowerSeries σ k) = 0 := fun t => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  rw [killCompl_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha)
    (hasSubst_of_constantCoeff_zero hc)]
  simp only [← killCompl_eq_subst]

variable {K : Type} [Field K]

/- English proof (translation)
Unfold `jetAt0`. Use `Finset.sum_subset hs fun m _ hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]`.
-/
theorem jetAt0_eq_sum {σ : Type} (P : MvPolynomial σ K) (G : MvPowerSeries σ K) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (mfact m : K) * coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[jetAt0_eq_sum (P + Q) G (P.support ∪ Q.support) MvPolynomial.support_add, jetAt0_eq_sum P G (P.support ∪ Q.support) Finset.subset_union_left, jetAt0_eq_sum Q G (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jetAt0_add_left {σ : Type} (P Q : MvPolynomial σ K) (G : MvPowerSeries σ K) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  rw [jetAt0_eq_sum (P + Q) G (P.support ∪ Q.support) MvPolynomial.support_add,
    jetAt0_eq_sum P G (P.support ∪ Q.support) Finset.subset_union_left,
    jetAt0_eq_sum Q G (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

/- English proof (translation)
Rewrite using `[jetAt0_eq_sum _ G P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul), jetAt0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jetAt0_C_mul {σ : Type} (c : K) (P : MvPolynomial σ K) (G : MvPowerSeries σ K) :
    jetAt0 (MvPolynomial.C c * P) G = c * jetAt0 P G := by
  classical
  rw [jetAt0_eq_sum _ G P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul),
    jetAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul]; ring

/- English proof (translation)
Rewrite using `[jetAt0_eq_sum _ G {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]`.
-/
theorem jetAt0_monomial {σ : Type} (m : σ →₀ ℕ) (c : K) (G : MvPowerSeries σ K) :
    jetAt0 (MvPolynomial.monomial m c) G = c * (mfact m : K) * coeff m G := by
  classical
  rw [jetAt0_eq_sum _ G {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

/- English proof (translation)
Simplify using `[jetAt0]`.
-/
theorem jetAt0_zero_left {σ : Type} (G : MvPowerSeries σ K) : jetAt0 0 G = 0 := by
  simp [jetAt0]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [jetAt0_zero_left]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jetAt0_add_left, ih]`.
-/
theorem jetAt0_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ K) (G : MvPowerSeries σ K) :
    jetAt0 (∑ i ∈ s, P i) G = ∑ i ∈ s, jetAt0 (P i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jetAt0_add_left, ih]

/- English proof (translation)
Unfold `jetAt0`. Simplify using `only [map_sum, Finset.mul_sum, coeff_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring` and prove the remaining obligations.
-/
theorem jetAt0_sum_smul_right {σ ι : Type} (s : Finset ι) (P : MvPolynomial σ K) (c : ι → K)
    (G : ι → MvPowerSeries σ K) :
    jetAt0 P (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * jetAt0 P (G i) := by
  unfold jetAt0
  simp only [map_sum, Finset.mul_sum, coeff_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Establish `h1 : ∀ u : σ →₀ ℕ, mfact u = (u s).factorial * mfact (u.erase s)`. Introduce `u`. Unfold `mfact`. Conclude with `(Finsupp.mul_prod_erase' u s _ (fun _ => rfl)).symm`. Rewrite using `[h1 (m + _), h1 m, Finsupp.erase_add, Finsupp.erase_single, add_zero]`.

Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfact_add_single {σ : Type} (m : σ →₀ ℕ) (s : σ) :
    mfact (m + Finsupp.single s 1) = mfact m * (m s + 1) := by
  classical
  have h1 : ∀ u : σ →₀ ℕ, mfact u = (u s).factorial * mfact (u.erase s) := by
    intro u
    unfold mfact
    exact (Finsupp.mul_prod_erase' u s _ (fun _ => rfl)).symm
  rw [h1 (m + _), h1 m, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp [Nat.factorial_succ]; ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[MvPolynomial.X, MvPolynomial.monomial_mul, jetAt0_monomial, jetAt0_monomial, coeff_pderiv, mfact_add_single]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add p q hp hq => rw [add_mul, jetAt0_add_left, jetAt0_add_left, hp, hq]`.
-/
theorem jetAt0_mul_X {σ : Type} (P : MvPolynomial σ K) (s : σ) (G : MvPowerSeries σ K) :
    jetAt0 (P * MvPolynomial.X s) G = jetAt0 P (pderiv K s G) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, jetAt0_monomial, jetAt0_monomial, coeff_pderiv,
      mfact_add_single]
    push_cast; ring
  | add p q hp hq => rw [add_mul, jetAt0_add_left, jetAt0_add_left, hp, hq]

/- English proof (translation)
Establish `ha : ∀ s, constantCoeff (∑ t, M s t • (X t : MvPowerSeries τ K)) = 0`. Introduce `s`. Simplify using `[map_sum]`. Proceed by induction on `Q using MvPolynomial.induction_on generalizing G with`. Consider the case `C c`.

Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← MvPolynomial.monomial_zero', ← MvPolynomial.monomial_zero', jetAt0_monomial, jetAt0_monomial, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_same ha]`. Simplify using `[mfact]`. Consider the case `add p q hp hq => rw [map_add, jetAt0_add_left, jetAt0_add_left, hp, hq]`. Consider the case `mul_X p t hp`. Rewrite using `[jetAt0_mul_X, pderiv_subst ha, map_mul, MvPolynomial.aeval_X, Finset.mul_sum, jetAt0_sum_left]`.

Establish `: ∀ s, pderiv K t (∑ t, M s t • (X t : MvPowerSeries τ K)) = C (M s t)`. Introduce `s`. Rewrite using `[map_sum, Finset.sum_eq_single t]`. Rewrite using `[Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]`. Introduce `b _ hb`.

Rewrite using `[Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [this]`. Simplify using `only [mul_comm _ (C _ : MvPowerSeries τ K), ← smul_eq_C_mul]`.

Rewrite using `[jetAt0_sum_smul_right]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hp, mul_left_comm, jetAt0_C_mul, jetAt0_mul_X]`.
-/
theorem jetAt0_subst_linear {σ τ : Type} [Fintype σ] [Fintype τ] (M : σ → τ → K) (Q : MvPolynomial τ K)
    (G : MvPowerSeries σ K) :
    jetAt0 Q (subst (fun s => ∑ t, M s t • (X t : MvPowerSeries τ K)) G) =
      jetAt0 (MvPolynomial.aeval (fun t => ∑ s, MvPolynomial.C (M s t) * MvPolynomial.X s) Q) G := by
  classical
  have ha : ∀ s, constantCoeff (∑ t, M s t • (X t : MvPowerSeries τ K)) = 0 := by
    intro s; simp [map_sum]
  induction Q using MvPolynomial.induction_on generalizing G with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← MvPolynomial.monomial_zero',
      ← MvPolynomial.monomial_zero', jetAt0_monomial, jetAt0_monomial,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_same ha]
    simp [mfact]
  | add p q hp hq => rw [map_add, jetAt0_add_left, jetAt0_add_left, hp, hq]
  | mul_X p t hp =>
    rw [jetAt0_mul_X, pderiv_subst ha, map_mul, MvPolynomial.aeval_X, Finset.mul_sum, jetAt0_sum_left]
    have : ∀ s, pderiv K t (∑ t, M s t • (X t : MvPowerSeries τ K)) = C (M s t) := by
      intro s
      rw [map_sum, Finset.sum_eq_single t]
      · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
      · intro b _ hb
        rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [this]
    simp only [mul_comm _ (C _ : MvPowerSeries τ K), ← smul_eq_C_mul]
    rw [jetAt0_sum_smul_right]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hp, mul_left_comm, jetAt0_C_mul, jetAt0_mul_X]

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Establish `key : ∀ {υ : Type} (u : MvPowerSeries υ K), constantCoeff u = 0 → ∀ N : ℕ, OrdGE (N + 1) (mvExp u - ∑ j ∈ Finset.range (N + 1), ((j.factorial : K)⁻¹) • u ^ j)`. Introduce `υ u hu N e he`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `∑ j ∈ Finset.range (e.degree + 1), coeff e (u ^ j) / (j.factorial : K) = _`.

Rewrite using `[Finset.sum_subset (s₂ := Finset.range (N + 1)) (Finset.range_mono (by omega))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`.

Rewrite using `[ordGE_pow (ordGE_one_of_const hu) j e (by simp at hj; omega), zero_div]`. Use extensionality with `e`. Establish `h1` using `ordGE_subst a ha (key h h0 e.degree) e (by omega)`. Establish `h2` using `key (subst a h) (by rw [constantCoeff_subst_same ha, h0]) e.degree e (by omega)`. Rewrite `h2` using `[map_sub, sub_eq_zero]`.

Rewrite `h1` using `[subst_sub hs, map_sub, sub_eq_zero]`. Rewrite using `[h1, h2, ← coe_substAlgHom hs, map_sum]`. Simplify using `only [map_smul, map_pow]`.
-/
theorem subst_mvExp {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) (h : MvPowerSeries σ K) (h0 : constantCoeff h = 0) :
    subst a (mvExp h) = mvExp (subst a h) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have key : ∀ {υ : Type} (u : MvPowerSeries υ K), constantCoeff u = 0 → ∀ N : ℕ,
      OrdGE (N + 1) (mvExp u - ∑ j ∈ Finset.range (N + 1), ((j.factorial : K)⁻¹) • u ^ j) := by
    intro υ u hu N e he
    rw [map_sub, map_sum, sub_eq_zero]
    change ∑ j ∈ Finset.range (e.degree + 1), coeff e (u ^ j) / (j.factorial : K) = _
    rw [Finset.sum_subset (s₂ := Finset.range (N + 1)) (Finset.range_mono (by omega))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [coeff_smul]; ring
    · intro j _ hj
      rw [ordGE_pow (ordGE_one_of_const hu) j e (by simp at hj; omega), zero_div]
  ext e
  have h1 := ordGE_subst a ha (key h h0 e.degree) e (by omega)
  have h2 := key (subst a h) (by rw [constantCoeff_subst_same ha, h0]) e.degree e (by omega)
  rw [map_sub, sub_eq_zero] at h2
  rw [subst_sub hs, map_sub, sub_eq_zero] at h1
  rw [h1, h2, ← coe_substAlgHom hs, map_sum]
  simp only [map_smul, map_pow]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hu0⟩ : ∃ u : Fin n → K, (Matrix.of A).mulVec u = 0 ∧ u ≠ 0 := by`. Use `LinearMap.ker_ne_bot_of_finrank_lt (f := (Matrix.of A).mulVecLin) (by simpa using hj)` as an intermediate fact. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot this`. Conclude with `⟨u, hu, hu0⟩`. Use `haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩`.

Take `⟨p, hp⟩` from `Finite.exists_min (fun x => V.v (u x))`. Establish `hup : u p ≠ 0`. Introduce `h`. Apply `hu0` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `hp x` as an intermediate fact. Rewrite `this` using `[h, V.v.map_zero, top_le_iff]`. Conclude with `(AddValuation.top_iff _).1 this`. Establish `hsint : ∀ x, V.Ge 0 (u x / u p)`. Introduce `x`.

Establish `h1 : V.v (u x) = V.v (u x / u p) + V.v (u p)`. Rewrite using `[← V.v.map_mul, div_mul_cancel₀ _ hup]`. Establish `h2` using `hp x`. Establish `h3 : V.v (u p) ≠ ⊤` using `fun h => hup ((AddValuation.top_iff _).1 h)`. Rewrite `h2` using `[h1]`.

Unfold `VF.Ge`. Rewrite using `[WithTop.coe_zero]`. Establish `: (0 : WithTop ℝ) + V.v (u p) ≤ V.v (u x / u p) + V.v (u p)` using `by rwa [zero_add]`. Conclude with `(WithTop.add_le_add_iff_right h3).1 this`. Establish `hAs : ∀ c, ∑ x, A c x * (u x / u p) = 0`.

Introduce `c`. Use `congrFun hu c` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this`. Simplify using `only [← mul_div_assoc, ← Finset.sum_div, this, zero_div]`. Use `⟨fun x => (if x = p then 1 else 0) - ∑ c, B p c * A c x, fun x => u x / u p, ?_, hsint, ?_, hAs, ?_⟩` and prove the remaining obligations.

Introduce `x`. Use `VF.Ge.sub ?_ (VF.Ge.sum fun c _ => (hB _ _).mul_int (hA _ _))` and prove the remaining obligations. Use `split_ifs`. Use `exacts [VF.Ge.one, VF.Ge.zero _]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hAs]`. Simplify using `[hup]`. Introduce `c'`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hAB]`. Simplify using the standard rewrite rules.
-/
theorem complete_step (V : VF K) {n j : ℕ} (hj : j < n) (A : Fin j → Fin n → K) (B : Fin n → Fin j → K)
    (hA : ∀ c x, V.Ge 0 (A c x)) (hB : ∀ x c, V.Ge 0 (B x c))
    (hAB : ∀ c c', ∑ x, A c x * B x c' = if c = c' then 1 else 0) :
    ∃ (r s : Fin n → K), (∀ x, V.Ge 0 (r x)) ∧ (∀ x, V.Ge 0 (s x)) ∧ (∑ x, r x * s x = 1) ∧
      (∀ c, ∑ x, A c x * s x = 0) ∧ ∀ c, ∑ x, r x * B x c = 0 := by
  classical
  obtain ⟨u, hu, hu0⟩ : ∃ u : Fin n → K, (Matrix.of A).mulVec u = 0 ∧ u ≠ 0 := by
    have := LinearMap.ker_ne_bot_of_finrank_lt (f := (Matrix.of A).mulVecLin) (by simpa using hj)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨u, hu, hu0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun x => V.v (u x))
  have hup : u p ≠ 0 := by
    intro h
    apply hu0
    funext x
    have := hp x
    rw [h, V.v.map_zero, top_le_iff] at this
    exact (AddValuation.top_iff _).1 this
  have hsint : ∀ x, V.Ge 0 (u x / u p) := by
    intro x
    have h1 : V.v (u x) = V.v (u x / u p) + V.v (u p) := by
      rw [← V.v.map_mul, div_mul_cancel₀ _ hup]
    have h2 := hp x
    have h3 : V.v (u p) ≠ ⊤ := fun h => hup ((AddValuation.top_iff _).1 h)
    rw [h1] at h2
    unfold VF.Ge
    rw [WithTop.coe_zero]
    have : (0 : WithTop ℝ) + V.v (u p) ≤ V.v (u x / u p) + V.v (u p) := by rwa [zero_add]
    exact (WithTop.add_le_add_iff_right h3).1 this
  have hAs : ∀ c, ∑ x, A c x * (u x / u p) = 0 := by
    intro c
    have := congrFun hu c
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simp only [← mul_div_assoc, ← Finset.sum_div, this, zero_div]
  refine ⟨fun x => (if x = p then 1 else 0) - ∑ c, B p c * A c x, fun x => u x / u p, ?_, hsint, ?_, hAs, ?_⟩
  · intro x
    refine VF.Ge.sub ?_ (VF.Ge.sum fun c _ => (hB _ _).mul_int (hA _ _))
    split_ifs
    exacts [VF.Ge.one, VF.Ge.zero _]
  · simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hAs]
    simp [hup]
  · intro c'
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hAB]
    simp

/- English proof (translation)
Proceed by induction on `j, h0 using Nat.le_induction with`. Consider the case `base => exact ⟨A, B, hA, hB, hAB, fun c => rfl⟩`. Consider the case `succ j h0 ih`. Take `⟨A', B', h1, h2, h3, h4⟩` from `ih (by omega)`. Take `⟨r, s, hr, hs, hrs, hAs, hrB⟩` from `complete_step V (by omega : j < n) A' B' h1 h2 h3`.

Use `⟨Fin.snoc (α := fun _ => Fin n → K) A' r, fun x => Fin.snoc (α := fun _ => K) (B' x) (s x), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c x`. Use `Fin.lastCases ?_ (fun c => ?_) c` and prove the remaining obligations. Simplify using `using hr x`. Simplify using `using h1 c x`.

Introduce `x c`. Use `Fin.lastCases ?_ (fun c => ?_) c` and prove the remaining obligations. Simplify using `using hs x`. Simplify using `using h2 x c`. Introduce `c c'`.

Apply the tactic sequence `refine Fin.lastCases ?_ (fun c => ?_) c <;> refine Fin.lastCases ?_ (fun c' => ?_) c'`. Simplify using `using hrs`. Simplify `hrB c'` using `[(Fin.castSucc_lt_last c').ne']`. Simplify `hAs c` using `[(Fin.castSucc_lt_last c).ne]`. Simplify using `using h3 c c'`.

Introduce `c`. Establish `: Fin.castLE (Nat.le_succ_of_le h0) c = Fin.castSucc (Fin.castLE h0 c)` using `rfl`. Rewrite using `[this, Fin.snoc_castSucc, h4]`.
-/
theorem complete_rows (V : VF K) {n n0 : ℕ} (A : Fin n0 → Fin n → K) (B : Fin n → Fin n0 → K)
    (hA : ∀ c x, V.Ge 0 (A c x)) (hB : ∀ x c, V.Ge 0 (B x c))
    (hAB : ∀ c c', ∑ x, A c x * B x c' = if c = c' then 1 else 0) (j : ℕ) (h0 : n0 ≤ j) (hj : j ≤ n) :
    ∃ (A' : Fin j → Fin n → K) (B' : Fin n → Fin j → K), (∀ c x, V.Ge 0 (A' c x)) ∧
      (∀ x c, V.Ge 0 (B' x c)) ∧ (∀ c c', ∑ x, A' c x * B' x c' = if c = c' then 1 else 0) ∧
      ∀ c, A' (Fin.castLE h0 c) = A c := by
  induction j, h0 using Nat.le_induction with
  | base => exact ⟨A, B, hA, hB, hAB, fun c => rfl⟩
  | succ j h0 ih =>
    obtain ⟨A', B', h1, h2, h3, h4⟩ := ih (by omega)
    obtain ⟨r, s, hr, hs, hrs, hAs, hrB⟩ := complete_step V (by omega : j < n) A' B' h1 h2 h3
    refine ⟨Fin.snoc (α := fun _ => Fin n → K) A' r, fun x => Fin.snoc (α := fun _ => K) (B' x) (s x),
      ?_, ?_, ?_, ?_⟩
    · intro c x
      refine Fin.lastCases ?_ (fun c => ?_) c
      · simpa using hr x
      · simpa using h1 c x
    · intro x c
      refine Fin.lastCases ?_ (fun c => ?_) c
      · simpa using hs x
      · simpa using h2 x c
    · intro c c'
      refine Fin.lastCases ?_ (fun c => ?_) c <;> refine Fin.lastCases ?_ (fun c' => ?_) c'
      · simpa using hrs
      · simpa [(Fin.castSucc_lt_last c').ne'] using hrB c'
      · simpa [(Fin.castSucc_lt_last c).ne] using hAs c
      · simpa using h3 c c'
    · intro c
      have : Fin.castLE (Nat.le_succ_of_le h0) c = Fin.castSucc (Fin.castLE h0 c) := rfl
      rw [this, Fin.snoc_castSucc, h4]

end GlobalTheory.MinorShiftJet
