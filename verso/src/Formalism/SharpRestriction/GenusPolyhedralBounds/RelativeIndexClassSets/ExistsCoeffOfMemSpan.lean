import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section Abstract

open MvPolynomial

variable {k K L : Type*} [CommRing k] [Field K] [CommRing L] [Algebra k L] [Algebra K L]
  {n δ : ℕ} (y : Fin n → L) (θ : Fin δ → L) (J : ℕ → Submodule K L) (Δ : Fin n → Derivation k L L)

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[show monomial (f + g) (1 : K) = monomial f 1 * monomial g 1 by rw [monomial_mul, one_mul], map_mul, Derivation.leibniz, Derivation.leibniz, hf, hg, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]`. Consider the case `single i a`.

Rewrite using `[← X_pow_eq_monomial, map_pow, aeval_X, Derivation.leibniz_pow, Derivation.leibniz_pow, hy, pderiv_X, map_nsmul, smul_eq_mul, smul_eq_mul, map_mul, map_pow, aeval_X]`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, Pi.single_eq_of_ne (Ne.symm h), map_zero]`.
-/
theorem ind_mono (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (l : Fin n) (m : Fin n →₀ ℕ) :
    Δ l (aeval y (monomial m (1 : K))) = aeval y (pderiv l (monomial m (1 : K))) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [show monomial (f + g) (1 : K) = monomial f 1 * monomial g 1 by rw [monomial_mul, one_mul], map_mul,
      Derivation.leibniz, Derivation.leibniz, hf, hg, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
  | single i a =>
    rw [← X_pow_eq_monomial, map_pow, aeval_X, Derivation.leibniz_pow, Derivation.leibniz_pow, hy, pderiv_X,
      map_nsmul, smul_eq_mul, smul_eq_mul, map_mul, map_pow, aeval_X]
    by_cases h : l = i
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h), map_zero]

/- English proof (translation)
Rewrite using `[← map_smul, smul_monomial, smul_eq_mul, mul_one]`.
-/
theorem aeval_monomial_eq_smul (m : Fin n →₀ ℕ) (c : K) :
    aeval y (monomial m c) = c • aeval y (monomial m (1 : K)) := by
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[← support_sum_monomial_coeff p, map_sum, Finset.sum_mul]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hd : m.degree = a`. Assume the negation of the conclusion as `h`. Conclude with `(MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)`.

Rewrite using `[aeval_monomial_eq_smul, smul_mul_assoc, ← hd]`. Conclude with `Submodule.smul_mem _ _ (hY m i)`.
-/
theorem ind_hom_mem (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (i : Fin δ) : aeval y p * θ i ∈ J a := by
  rw [← support_sum_monomial_coeff p, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  rw [aeval_monomial_eq_smul, smul_mul_assoc, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

/- English proof (translation)
Rewrite using `[← support_sum_monomial_coeff p]`. Simplify using `only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hd : m.degree = a`. Assume the negation of the conclusion as `h`.

Conclude with `(MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)`. Take `⟨c', hc'⟩` from `hK l (coeff m p)`. Establish `e1 : Δ l (aeval y (monomial m (coeff m p)) * θ i) = c' • (aeval y (monomial m (1 : K)) * θ i) + aeval y (pderiv l (monomial m (coeff m p))) * θ i`. Establish `e2 : pderiv l (monomial m (coeff m p)) = coeff m p • pderiv l (monomial m (1 : K))`. Rewrite using `[← Derivation.map_smul, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[e2, map_smul, aeval_monomial_eq_smul, Algebra.smul_def, Derivation.leibniz, hθ, smul_zero, zero_add, Derivation.leibniz, hc', ind_mono y Δ hy]`. Simplify using `only [smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, add_sub_cancel_right, ← hd]`. Conclude with `Submodule.smul_mem _ _ (hY m i)`.
-/
theorem ind_der_mem (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (l : Fin n) (i : Fin δ) :
    Δ l (aeval y p * θ i) - aeval y (pderiv l p) * θ i ∈ J a := by
  rw [← support_sum_monomial_coeff p]
  simp only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  obtain ⟨c', hc'⟩ := hK l (coeff m p)
  have e1 : Δ l (aeval y (monomial m (coeff m p)) * θ i) =
      c' • (aeval y (monomial m (1 : K)) * θ i) + aeval y (pderiv l (monomial m (coeff m p))) * θ i := by
    have e2 : pderiv l (monomial m (coeff m p)) = coeff m p • pderiv l (monomial m (1 : K)) := by
      rw [← Derivation.map_smul, smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, aeval_monomial_eq_smul, Algebra.smul_def, Derivation.leibniz, hθ, smul_zero, zero_add,
      Derivation.leibniz, hc', ind_mono y Δ hy]
    simp only [smul_eq_mul, Algebra.smul_def]
    ring
  rw [e1, add_sub_cancel_right, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

variable [CharZero K]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `c hc _`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]`.

Introduce `m hm`. Conclude with `absurd (hc i m hm) (Nat.not_lt_zero _)`. Consider the case `succ a ih`. Introduce `c hc hmem`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases.

Establish `hC : ∀ i, c i = C (coeff 0 (c i))`. Introduce `i`. Use extensionality with `m`. Rewrite using `[coeff_C]`. Use `split_ifs with h`.

Rewrite using `[← h]`. Assume the negation of the conclusion as `h'`. Use `hc i m (MvPolynomial.mem_support_iff.mpr h')` as an intermediate fact. Conclude with `h ((Finsupp.degree_eq_zero_iff m).mp (by omega)).symm`. Establish `h0` using `hbase (fun i => coeff 0 (c i)) (by`.

Establish `e : ∑ i, aeval y (c i) * θ i = ∑ i, coeff 0 (c i) • θ i` using `Finset.sum_congr rfl fun i _ => by conv_lhs => rw [hC i]`. Rewrite using `[aeval_C, Algebra.smul_def]`. Rewrite using `[← e]`. Conclude with `hmem)`. Use function extensionality and compare the values at `i`.

Establish `h0i : coeff 0 (c i) = 0` using `congrFun h0 i`. Rewrite using `[hC i, h0i, map_zero]`. Both sides reduce to the same expression. Establish `hlow : (fun i => c i - homogeneousComponent a (c i)) = 0`. Apply `ih` to reduce the goal to its premises.

Introduce `i m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent]`. Distinguish the cases in `hd : m.degree = a`. Rewrite `hm` using `[if_pos hd, sub_self]`. Conclude with `absurd rfl hm`.

Rewrite `hm` using `[if_neg hd, sub_zero]`. Use `hc i m (MvPolynomial.mem_support_iff.mpr hm)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e : ∑ i, aeval y (c i - homogeneousComponent a (c i)) * θ i = ∑ i, aeval y (c i) * θ i - ∑ i, aeval y (homogeneousComponent a (c i)) * θ i`. Rewrite using `[← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_sub, sub_mul]`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ (hanti a hmem) (Submodule.sum_mem _ fun i _ => ind_hom_mem y θ J hY (homogeneousComponent_isHomogeneous a (c i)) i)`. Establish `hhom : ∀ i, (c i).IsHomogeneous a`. Introduce `i`.

Use `congrFun hlow i` as an intermediate fact. Rewrite `this` using `[Pi.zero_apply, sub_eq_zero]`. Rewrite using `[this]`. Conclude with `homogeneousComponent_isHomogeneous a (c i)`. Establish `hpd : ∀ l, (fun i => pderiv l (c i)) = 0`.

Introduce `l`. Apply `ih` to reduce the goal to its premises. Introduce `i m hm`. Establish `hd : m.degree = a - 1`. Assume the negation of the conclusion as `h`.

Conclude with `(MvPolynomial.mem_support_iff.mp hm) ((hhom i).pderiv.coeff_eq_zero h)`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hJ l a _ hmem`. Rewrite `h1` using `[map_sum]`. Establish `h2 : ∑ i, (Δ l (aeval y (c i) * θ i) - aeval y (pderiv l (c i)) * θ i) ∈ J a` using `Submodule.sum_mem _ fun i _ => ind_der_mem y θ J Δ hy hθ hK hY (hhom i) l i`.

Rewrite `h2` using `[Finset.sum_sub_distrib]`. Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `i`. Establish `hE` using `(hhom i).sum_X_mul_pderiv`.

Establish `h0 : ∑ l, X l * pderiv l (c i) = 0` using `Finset.sum_eq_zero fun l _ => by rw [congrFun (hpd l) i, Pi.zero_apply, mul_zero]`. Rewrite `hE` using `[h0]`. Rewrite using `[Pi.zero_apply]`. Conclude with `(smul_eq_zero.mp hE.symm).resolve_left (by omega)`.
-/
theorem ind_claim (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hJ : ∀ l a x, x ∈ J (a + 1) → Δ l x ∈ J a) (hanti : ∀ a, J (a + 1) ≤ J a)
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree)
    (hbase : ∀ c : Fin δ → K, ∑ i, c i • θ i ∈ J 1 → c = 0) (a : ℕ) :
    ∀ c : Fin δ → MvPolynomial (Fin n) K, (∀ i, ∀ m ∈ (c i).support, m.degree < a) →
      ∑ i, aeval y (c i) * θ i ∈ J a → c = 0 := by
  induction a with
  | zero =>
    intro c hc _
    funext i
    rw [Pi.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro m hm
    exact absurd (hc i m hm) (Nat.not_lt_zero _)
  | succ a ih =>
    intro c hc hmem
    rcases Nat.eq_zero_or_pos a with rfl | ha
    ·
      have hC : ∀ i, c i = C (coeff 0 (c i)) := by
        intro i
        ext m
        rw [coeff_C]
        split_ifs with h
        · rw [← h]
        · by_contra h'
          have := hc i m (MvPolynomial.mem_support_iff.mpr h')
          exact h ((Finsupp.degree_eq_zero_iff m).mp (by omega)).symm
      have h0 := hbase (fun i => coeff 0 (c i)) (by
        have e : ∑ i, aeval y (c i) * θ i = ∑ i, coeff 0 (c i) • θ i :=
          Finset.sum_congr rfl fun i _ => by
            conv_lhs => rw [hC i]
            rw [aeval_C, Algebra.smul_def]
        rw [← e]; exact hmem)
      funext i
      have h0i : coeff 0 (c i) = 0 := congrFun h0 i
      rw [hC i, h0i, map_zero]
      rfl
    ·
      have hlow : (fun i => c i - homogeneousComponent a (c i)) = 0 := by
        apply ih
        · intro i m hm
          rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
          by_cases hd : m.degree = a
          · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
          · rw [if_neg hd, sub_zero] at hm
            have := hc i m (MvPolynomial.mem_support_iff.mpr hm)
            omega
        · have e : ∑ i, aeval y (c i - homogeneousComponent a (c i)) * θ i =
              ∑ i, aeval y (c i) * θ i - ∑ i, aeval y (homogeneousComponent a (c i)) * θ i := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [map_sub, sub_mul]
          rw [e]
          exact Submodule.sub_mem _ (hanti a hmem)
            (Submodule.sum_mem _ fun i _ => ind_hom_mem y θ J hY (homogeneousComponent_isHomogeneous a (c i)) i)
      have hhom : ∀ i, (c i).IsHomogeneous a := by
        intro i
        have := congrFun hlow i
        rw [Pi.zero_apply, sub_eq_zero] at this
        rw [this]; exact homogeneousComponent_isHomogeneous a (c i)

      have hpd : ∀ l, (fun i => pderiv l (c i)) = 0 := by
        intro l
        apply ih
        · intro i m hm
          have hd : m.degree = a - 1 := by
            by_contra h
            exact (MvPolynomial.mem_support_iff.mp hm) ((hhom i).pderiv.coeff_eq_zero h)
          omega
        · have h1 := hJ l a _ hmem
          rw [map_sum] at h1
          have h2 : ∑ i, (Δ l (aeval y (c i) * θ i) - aeval y (pderiv l (c i)) * θ i) ∈ J a :=
            Submodule.sum_mem _ fun i _ => ind_der_mem y θ J Δ hy hθ hK hY (hhom i) l i
          rw [Finset.sum_sub_distrib] at h2
          have := Submodule.sub_mem _ h1 h2
          rwa [sub_sub_cancel] at this
      funext i
      have hE := (hhom i).sum_X_mul_pderiv
      have h0 : ∑ l, X l * pderiv l (c i) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [congrFun (hpd l) i, Pi.zero_apply, mul_zero]
      rw [h0] at hE
      rw [Pi.zero_apply]
      exact (smul_eq_zero.mp hE.symm).resolve_left (by omega)

end Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`.
-/
theorem der_sum_apply {k L ι : Type*} [CommRing k] [CommRing L] [Algebra k L] (s : Finset ι)
    (f : ι → Derivation k L L) (x : L) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

section Concrete

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

@[instance_reducible] def LwAlgKl : Algebra (X.Kl la) (Lw X la w) := inferInstanceAs (Algebra (X.Kl la) (Localization.Away (sec X la w 0)))

attribute [local instance] LwAlgKl

def pdLw (p : Idx D j N) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) := pdLc X la w p

/- English proof (translation)
The claim follows from `pdLc_algebraMap X la w p x`.
-/
theorem pdLw_algebraMap (p : Idx D j N) (x : Rp X la N) :
    pdLw X la w p (algebraMap (Rp X la N) (Lw X la w) x) = algebraMap (Rp X la N) (Lw X la w) (pdRp X la N p x) :=
  pdLc_algebraMap X la w p x

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), pdLw_algebraMap, pdRp_algebraMap, ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]`.
-/
theorem pdLw_algebraMap_Kp (p : Idx D j N) (c : Kp X la N) :
    pdLw X la w p (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (pdKp X la N p c) := by
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), pdLw_algebraMap, pdRp_algebraMap,
    ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]

/- English proof (translation)
Establish `h` using `hasse_jid_power X la w u (Finsupp.single p 1) (a + 1) x hx`. Rewrite `h` using `[Finsupp.sum_single_index rfl, Nat.add_sub_cancel]`. Conclude with `h`.
-/
theorem pdLw_mem (p : Idx D j N) (u : WeightFamilies.Wt D j) (a : ℕ) {x : Lw X la w} (hx : x ∈ JHfr X la w u (a + 1)) :
    pdLw X la w p x ∈ JHfr X la w u a := by
  have h := hasse_jid_power X la w u (Finsupp.single p 1) (a + 1) x hx
  rw [Finsupp.sum_single_index rfl, Nat.add_sub_cancel] at h
  exact h

/- English proof (translation)
Establish `h` using `congrArg (pdLw X la w p) (section_mul_inverse_eq_one X la w)`. Rewrite `h` using `[Derivation.leibniz, Derivation.map_one_eq_zero, pdLw_algebraMap, pdRp_sec, if_neg hp, map_zero, smul_zero, add_zero, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[section_mul_inverse_eq_one, one_mul]`. Use `_ = w0inv X la w * (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * pdLw X la w p (w0inv X la w)) := by ring`.

Use `_ = 0 := by rw [h, mul_zero]`.
-/
theorem pdLw_w0inv (p : Idx D j N) (hp : p.1 ≠ 0) : pdLw X la w p (w0inv X la w) = 0 := by
  have h := congrArg (pdLw X la w p) (section_mul_inverse_eq_one X la w)
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, pdLw_algebraMap, pdRp_sec, if_neg hp, map_zero, smul_zero,
    add_zero, smul_eq_mul] at h
  calc pdLw X la w p (w0inv X la w)
      = (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * w0inv X la w) * pdLw X la w p (w0inv X la w) := by
        rw [section_mul_inverse_eq_one, one_mul]
    _ = w0inv X la w * (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * pdLw X la w p (w0inv X la w)) := by ring
    _ = 0 := by rw [h, mul_zero]

def t0 (κ : Fin N) : Kp X la N := algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, κ))

def dSec (l : Fin (WeightFamilies.dimY D j)) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) :=
  ∑ κ, algebraMap (Kp X la N) (Lw X la w) (t0 X la κ) • pdLw X la w (l.succ, κ)

/- English proof (translation)
Unfold `dSec`. Rewrite using `[der_sum_apply]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.smul_apply, smul_eq_mul, Algebra.smul_def]`.
-/
theorem dSec_apply (l : Fin (WeightFamilies.dimY D j)) (x : Lw X la w) :
    dSec X la w l x = ∑ κ, t0 X la κ • pdLw X la w (l.succ, κ) x := by
  unfold dSec
  rw [der_sum_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Derivation.smul_apply, smul_eq_mul, Algebra.smul_def]

def ySec (l : Fin (WeightFamilies.dimY D j)) : Lw X la w := (sfr X la w l.succ : Lw X la w)

/- English proof (translation)
Establish `h1 : ∀ κ, pdLw X la w (l.succ, κ) (ySec X la w l') = if l = l' then algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w κ))) * w0inv X la w else 0`. Introduce `κ`. Unfold `ySec`. Rewrite using `[coe_sfr, frac_apply, pow_one, Derivation.leibniz, pdLw_w0inv X la w _ (Fin.succ_ne_zero l), smul_zero, zero_add, pdLw_algebraMap, pdRp_sec, smul_eq_mul]`. Distinguish the cases in `h : l = l'`.

Rewrite using `[if_pos h, if_pos (by rw [h]), mul_comm]`. Rewrite using `[if_neg h, if_neg (fun e => h (Fin.succ_injective _ e)), map_zero, mul_zero]`. Rewrite using `[dSec_apply]`. Simplify using `only [h1]`. Distinguish the cases in `h : l = l'`.

Simplify using `only [if_pos h]`. Rewrite using `[← section_mul_inverse_eq_one X la w]`. Unfold `sec`. Rewrite using `[map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_mul_assoc]`. Use `congr 1`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]`. Both sides reduce to the same expression. Simplify using `only [if_neg h, smul_zero, Finset.sum_const_zero]`.
-/
theorem dSec_ySec (l l' : Fin (WeightFamilies.dimY D j)) : dSec X la w l (ySec X la w l') = if l = l' then 1 else 0 := by
  have h1 : ∀ κ, pdLw X la w (l.succ, κ) (ySec X la w l') =
      if l = l' then algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w κ))) * w0inv X la w else 0 := by
    intro κ
    unfold ySec
    rw [coe_sfr, frac_apply, pow_one, Derivation.leibniz, pdLw_w0inv X la w _ (Fin.succ_ne_zero l), smul_zero, zero_add,
      pdLw_algebraMap, pdRp_sec, smul_eq_mul]
    by_cases h : l = l'
    · rw [if_pos h, if_pos (by rw [h]), mul_comm]
    · rw [if_neg h, if_neg (fun e => h (Fin.succ_injective _ e)), map_zero, mul_zero]
  rw [dSec_apply]
  simp only [h1]
  by_cases h : l = l'
  · simp only [if_pos h]
    rw [← section_mul_inverse_eq_one X la w]
    unfold sec
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [← smul_mul_assoc]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]
    rfl
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]

/- English proof (translation)
Rewrite using `[dSec_apply]`. Use `Finset.sum_eq_zero fun κ _ => ?_` and prove the remaining obligations. Rewrite using `[pdLw_algebraMap, pdRp_emb, map_zero, smul_zero]`.
-/
theorem dSec_emb (l : Fin (WeightFamilies.dimY D j)) (F : X.Forms) :
    dSec X la w l (algebraMap (Rp X la N) (Lw X la w) (emb X la N F)) = 0 := by
  rw [dSec_apply]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [pdLw_algebraMap, pdRp_emb, map_zero, smul_zero]

/- English proof (translation)
Use `⟨∑ κ, t0 X la κ * pdKp X la N (l.succ, κ) c, ?_⟩` and prove the remaining obligations. Rewrite using `[dSec_apply, map_sum]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations. Rewrite using `[pdLw_algebraMap_Kp, Algebra.smul_def, map_mul]`.
-/
theorem dSec_algebraMap_Kp (l : Fin (WeightFamilies.dimY D j)) (c : Kp X la N) :
    ∃ c' : Kp X la N, dSec X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) c' := by
  refine ⟨∑ κ, t0 X la κ * pdKp X la N (l.succ, κ) c, ?_⟩
  rw [dSec_apply, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [pdLw_algebraMap_Kp, Algebra.smul_def, map_mul]

/- English proof (translation)
Rewrite using `[dSec_apply]`. Conclude with `Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (pdLw_mem X la w _ u a hx)`.
-/
theorem dSec_mem (l : Fin (WeightFamilies.dimY D j)) (u : WeightFamilies.Wt D j) (a : ℕ) (x : Lw X la w) (hx : x ∈ JHfr X la w u (a + 1)) :
    dSec X la w l x ∈ JHfr X la w u a := by
  rw [dSec_apply]
  exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (pdLw_mem X la w _ u a hx)

/- English proof (translation)
Introduce `x hx`. Establish `h1 : x ∈ JHs X la w u (a + 1)` using `hx`. Rewrite `h1` using `[← Jid_pow_smul_HK]`. Establish `h2 : x ∈ Jid X la w ^ a • HK X la w u` using `Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ a)) le_rfl h1`. Rewrite `h2` using `[Jid_pow_smul_HK]`.

Conclude with `h2`.
-/
theorem JHfr_succ_le (u : WeightFamilies.Wt D j) (a : ℕ) : JHfr X la w u (a + 1) ≤ JHfr X la w u a := by
  intro x hx
  have h1 : x ∈ JHs X la w u (a + 1) := hx
  rw [← Jid_pow_smul_HK] at h1
  have h2 : x ∈ Jid X la w ^ a • HK X la w u := Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ a)) le_rfl h1
  rw [Jid_pow_smul_HK] at h2
  exact h2

open MvPolynomial in
/- English proof (translation)
Rewrite using `[aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum, ← coe_prod_sfr]`. Use `show _ = (Frac0 X la w).val (∏ i, sfr X la w i.succ ^ m i)`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Both sides reduce to the same expression.
-/
theorem aeval_ySec_monomial (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) = frac X la w m.degree (secPow X la w m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum,
    ← coe_prod_sfr]
  show _ = (Frac0 X la w).val (∏ i, sfr X la w i.succ ^ m i)
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  rfl

open MvPolynomial in
/- English proof (translation)
Rewrite using `[aeval_ySec_monomial, ← frac_zero, frac_mul, mem_JHfr]`. Use `⟨0, _, secPow_mul_mem_Mon X la w (Finsupp.degree_eq_sum m).symm ?_, by rw [add_comm]⟩` and prove the remaining obligations. Rewrite using `[addL_zero]`. Conclude with `emb_mem_Vw X la N u F`.
-/
theorem ySec_monomial_mul_mem (u : WeightFamilies.Wt D j) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (F : B.Cusp j u) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc u F)) ∈
      JHfr X la w u m.degree := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, mem_JHfr]
  refine ⟨0, _, secPow_mul_mem_Mon X la w (Finsupp.degree_eq_sum m).symm ?_, by rw [add_comm]⟩
  rw [addL_zero]
  exact emb_mem_Vw X la N u F

end Concrete

section Final

open MvPolynomial

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  (wF : WeightFamilies.Wt D j) (T : ℕ)

/- English proof (translation)
The claim follows from `have := Kl_charZero X la charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective`.
-/
theorem Kp_charZero' : CharZero (Kp X la N) :=
  have := Kl_charZero X la
  charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

def gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) : Rp X la N :=
  secPow X la w m * sec X la w 0 ^ (T - m.degree) * emb X la N (X.inc wF θ)

def phiN (θ : B.Cusp j wF) : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N) →ₗ[Kp X la N] Rp X la N :=
  (basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N)).constr (Kp X la N) (gN X la w wF T θ)

/- English proof (translation)
Establish `e : monomial m c = c • basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N) m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Unfold `phiN`. Rewrite using `[e, map_smul, Module.Basis.constr_basis]`.
-/
theorem phiN_monomial (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (c : Kp X la N) :
    phiN X la w wF T θ (monomial m c) = c • gN X la w wF T θ m := by
  have e : monomial m c = c • basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N) m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  unfold phiN
  rw [e, map_smul, Module.Basis.constr_basis]

/- English proof (translation)
Rewrite using `[aeval_ySec_monomial, ← frac_zero, frac_mul, ← frac_pow_mul X la w (m.degree + 0) (T - m.degree)]`. Unfold `gN`. Rewrite using `[show m.degree + 0 + (T - m.degree) = T by omega]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frac_gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (hm : m.degree ≤ T) :
    frac X la w T (gN X la w wF T θ m) = aeval (ySec X la w) (monomial m (1 : Kp X la N)) *
      algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, ← frac_pow_mul X la w (m.degree + 0) (T - m.degree)]
  unfold gN
  rw [show m.degree + 0 + (T - m.degree) = T by omega]
  congr 1
  ring

/- English proof (translation)
Establish `key : ∀ (s : Finset (Fin (WeightFamilies.dimY D j) →₀ ℕ)) (f : (Fin (WeightFamilies.dimY D j) →₀ ℕ) → Kp X la N), (∀ m ∈ s, m.degree ≤ T) → frac X la w T (phiN X la w wF T θ (∑ m ∈ s, monomial m (f m))) = aeval (ySec X la w) (∑ m ∈ s, monomial m (f m)) * algebraMap (Rp X la N) (L …`. Introduce `s f hs`. Simplify using `only [map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[phiN_monomial, map_smul, frac_gN X la w wF T θ m (hs m hm), aeval_monomial_eq_smul (ySec X la w) m (f m), smul_mul_assoc]`.

Use `key p.support (fun m => coeff m p) hp` as an intermediate fact. Rewrite `this` using `[support_sum_monomial_coeff]`. Then use the resulting hypothesis.
-/
theorem frac_phiN (θ : B.Cusp j wF) (p : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N))
    (hp : ∀ m ∈ p.support, m.degree ≤ T) :
    frac X la w T (phiN X la w wF T θ p) =
      aeval (ySec X la w) p * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  have key : ∀ (s : Finset (Fin (WeightFamilies.dimY D j) →₀ ℕ)) (f : (Fin (WeightFamilies.dimY D j) →₀ ℕ) → Kp X la N),
      (∀ m ∈ s, m.degree ≤ T) → frac X la w T (phiN X la w wF T θ (∑ m ∈ s, monomial m (f m))) =
        aeval (ySec X la w) (∑ m ∈ s, monomial m (f m)) *
          algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
    intro s f hs
    simp only [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [phiN_monomial, map_smul, frac_gN X la w wF T θ m (hs m hm), aeval_monomial_eq_smul (ySec X la w) m (f m),
      smul_mul_assoc]
  have := key p.support (fun m => coeff m p) hp
  rwa [support_sum_monomial_coeff] at this

end Final

section Main

open MvPolynomial

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨al, i, hal, hx⟩` from `hx`. Use `⟨fun i' => if i' = i then monomial (Finsupp.equivFunOnFinite.symm al) 1 else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `i' m hm dsimp only at hm`.

Distinguish the cases in `h : i' = i`. Rewrite `hm` using `[if_pos h]`. Use `Finset.mem_singleton.mp (support_monomial_subset hm)` as an intermediate fact. Rewrite using `[this, Finsupp.degree_eq_sum]`. Conclude with `hal`.

Rewrite `hm` using `[if_neg h, support_zero]`. Conclude with `absurd hm (Finset.notMem_empty _)`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `only`. Rewrite using `[if_pos rfl, phiN_monomial, one_smul, hx]`.

Unfold `gN`. Rewrite using `[Finsupp.degree_eq_sum]`. Both sides reduce to the same expression. Introduce `i' _ h dsimp only`. Rewrite using `[if_neg h, map_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Consider the case `zero => exact ⟨0, fun i m hm => by simp at hm, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, hxc⟩` from `hx`.

Take `⟨c', hc', hyc⟩` from `hy`. Use `⟨c + c', fun i m hm => ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hc i m h`. Conclude with `hc' i m h`.

Rewrite using `[Submodule.coe_add, hxc, hyc, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add]`. Consider the case `smul a x _ hx`. Take `⟨c, hc, hxc⟩` from `hx`. Use `⟨a • c, fun i m hm => hc i m (support_smul hm), ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.coe_smul, hxc, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, map_smul]`.
-/
theorem exists_coeff_of_mem_span {x : ↥(Vw X la G.N (addL wF wL T))}
    (hx : x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la)) :
    ∃ c : Fin G.del → MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la G.N),
      (∀ i, ∀ m ∈ (c i).support, m.degree < a0 D j T) ∧
        (x : Rp X la G.N) = ∑ i, phiN X la G.w wF T (G.th' i) (c i) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨al, i, hal, hx⟩ := hx
    refine ⟨fun i' => if i' = i then monomial (Finsupp.equivFunOnFinite.symm al) 1 else 0, ?_, ?_⟩
    · intro i' m hm
      dsimp only at hm
      by_cases h : i' = i
      · rw [if_pos h] at hm
        have := Finset.mem_singleton.mp (support_monomial_subset hm)
        rw [this, Finsupp.degree_eq_sum]
        exact hal
      · rw [if_neg h, support_zero] at hm
        exact absurd hm (Finset.notMem_empty _)
    · rw [Finset.sum_eq_single i]
      · dsimp only
        rw [if_pos rfl, phiN_monomial, one_smul, hx]
        unfold gN
        rw [Finsupp.degree_eq_sum]
        rfl
      · intro i' _ h
        dsimp only
        rw [if_neg h, map_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨0, fun i m hm => by simp at hm, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', hyc⟩ := hy
    refine ⟨c + c', fun i m hm => ?_, ?_⟩
    · rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hc i m h
      · exact hc' i m h
    · rw [Submodule.coe_add, hxc, hyc, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add]
  | smul a x _ hx =>
    obtain ⟨c, hc, hxc⟩ := hx
    refine ⟨a • c, fun i m hm => hc i m (support_smul hm), ?_⟩
    rw [Submodule.coe_smul, hxc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, map_smul]

attribute [local instance] LwAlgKl

/- English proof (translation)
Introduce `x hx h0`. Use `Kp_charZero' X la (N := G.N)` as an intermediate fact. Take `⟨c, hc, hxc⟩` from `exists_coeff_of_mem_span G la hx`. Establish `hbase : ∀ b : Fin G.del → Kp X la G.N, ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF 1 → b = 0`. Introduce `b hb`.

Establish `hlin : ∑ i, b i • tL G la i = 0`. Establish `e : ∑ i, b i • tL G la i = rho0 X la G.w wF (∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF)))`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl`. Rewrite using `[e, restriction_apply_eq_reduction, reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la G.w), mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK0]`.

Establish `e2 : algebraMap (Rp X la G.N) (Lw X la G.w) ((∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF)) : ↥(Vw X la G.N wF)) : Rp X la G.N) = ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))`. Rewrite using `[AddSubmonoidClass.coe_finsetSum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w), ← Algebra.smul_def]`. Rewrite using `[e2]`.

Conclude with `hb`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp hB.1 b hlin i`. Establish `hmem : ∑ i, aeval (ySec X la G.w) (c i) * algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF (a0 D j T)`. Rewrite `h0` using `[rhoK_apply, toWK_eq_zero_iff, mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK, hxc, map_sum]`.

Establish `e : ∀ i, frac X la G.w T (phiN X la G.w wF T (G.th' i) (c i)) = aeval (ySec X la G.w) (c i) * algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))` using `fun i => frac_phiN X la G.w wF T (G.th' i) (c i) fun m hm => ((hc i m hm).le.trans (Nat.sub_le _ _))`. Simplify using `only [e] at h0`. Conclude with `h0`. Establish `hc0` using `ind_claim (ySec X la G.w) (fun i => algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))) (JHfr X la G.w wF) (dSec X la G.w) (dSec_ySec X la G.w) (fun l i => dSec_emb X la G.w l _) (dSec_algebraMap_Kp X la G.w) (fun l a x hx => dSec_mem X la G.w l wF a x hx) …`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hxc, hc0]`. Simplify using the standard rewrite rules.
-/
theorem in64 (hB : InBasis G la) : ∀ x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la),
    rhoK X la G.w wF (a0 D j T) T x = 0 → x = 0 := by
  intro x hx h0
  have := Kp_charZero' X la (N := G.N)
  obtain ⟨c, hc, hxc⟩ := exists_coeff_of_mem_span G la hx

  have hbase : ∀ b : Fin G.del → Kp X la G.N,
      ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF 1 →
        b = 0 := by
    intro b hb
    have hlin : ∑ i, b i • tL G la i = 0 := by
      have e : ∑ i, b i • tL G la i = rho0 X la G.w wF
          (∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF))) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
      rw [e, restriction_apply_eq_reduction, reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la G.w), mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK0]
      have e2 : algebraMap (Rp X la G.N) (Lw X la G.w) ((∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)),
          emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF)) : ↥(Vw X la G.N wF)) : Rp X la G.N) =
          ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := by
        rw [AddSubmonoidClass.coe_finsetSum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w), ← Algebra.smul_def]
      rw [e2]
      exact hb
    funext i
    exact Fintype.linearIndependent_iff.mp hB.1 b hlin i
  have hmem : ∑ i, aeval (ySec X la G.w) (c i) *
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF (a0 D j T) := by
    rw [rhoK_apply, toWK_eq_zero_iff, mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK, hxc, map_sum] at h0
    have e : ∀ i, frac X la G.w T (phiN X la G.w wF T (G.th' i) (c i)) = aeval (ySec X la G.w) (c i) *
        algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := fun i =>
      frac_phiN X la G.w wF T (G.th' i) (c i) fun m hm => ((hc i m hm).le.trans (Nat.sub_le _ _))
    simp only [e] at h0
    exact h0
  have hc0 := ind_claim (ySec X la G.w)
    (fun i => algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))) (JHfr X la G.w wF)
    (dSec X la G.w) (dSec_ySec X la G.w) (fun l i => dSec_emb X la G.w l _) (dSec_algebraMap_Kp X la G.w)
    (fun l a x hx => dSec_mem X la G.w l wF a x hx) (JHfr_succ_le X la G.w wF)
    (fun m i => ySec_monomial_mul_mem X la G.w wF m (G.th' i)) hbase (a0 D j T) c hc hmem
  apply Subtype.ext
  rw [hxc, hc0]
  simp

end Main

end Formalism.MainNotions.Gaps.EtaleWeightGaps
