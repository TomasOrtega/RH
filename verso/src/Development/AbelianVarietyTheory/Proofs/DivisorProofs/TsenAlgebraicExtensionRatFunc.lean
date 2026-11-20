import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.COnePropertyFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroZeroFormPolynomialIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open Polynomial

namespace GlobalTheory

open Polynomial in
/- English proof (translation)
Introduce `ν hν`. Apply `hp` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_map]`. Introduce `h`. Conclude with `hν (hφ (h.trans (map_zero φ).symm))`.
-/
private theorem isHomogeneous_of_map_of_injective {R S : Type} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {n d : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : (MvPolynomial.map φ p).IsHomogeneous d) : p.IsHomogeneous d := by
  intro ν hν
  apply hp
  rw [MvPolynomial.coeff_map]
  intro h
  exact hν (hφ (h.trans (map_zero φ).symm))

open Polynomial in
/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp]`.
-/
private theorem mvPolynomial_eval_map_comp {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (x : Fin n → R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.eval (φ ∘ x) (MvPolynomial.map φ p) = φ (MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

open Polynomial in
/- English proof (translation)
Use `set E := IntermediateField.adjoin F (f.coeffs : Set K) with hE`. Use `haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Choose the witnesses or unpack the hypotheses as in `⟨fE, hfE⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap E K)) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `a ha`.

Conclude with `⟨⟨a, IntermediateField.subset_adjoin F _ ha⟩, rfl⟩`. Establish `hfEh : fE.IsHomogeneous d` using `isHomogeneous_of_map_of_injective (algebraMap E K).injective (hfE ▸ hf)`. Take `⟨x, hx0, hx⟩` from `_root_.GlobalTheory.c_one_of_finite_extension F E hF n d fE hfEh hd hdn`. Use `⟨algebraMap E K ∘ x, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `(algebraMap E K).injective (by simpa using congrFun h i)`. Rewrite using `[← hfE, mvPolynomial_eval_map_comp, hx, map_zero]`.
-/
private theorem exists_ne_zero_homogeneous_zero_of_forall_subfield {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    (hF : ∀ (n d : ℕ) (f : MvPolynomial (Fin n) F), f.IsHomogeneous d → 0 < d → d < n →
      ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x f = 0)
    (n d : ℕ) (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  set E := IntermediateField.adjoin F (f.coeffs : Set K) with hE
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨fE, hfE⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap E K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, IntermediateField.subset_adjoin F _ ha⟩, rfl⟩
  have hfEh : fE.IsHomogeneous d :=
    isHomogeneous_of_map_of_injective (algebraMap E K).injective (hfE ▸ hf)
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.c_one_of_finite_extension F E hF n d fE hfEh hd hdn
  refine ⟨algebraMap E K ∘ x, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact (algebraMap E K).injective (by simpa using congrFun h i)
  · rw [← hfE, mvPolynomial_eval_map_comp, hx, map_zero]

open Polynomial in
variable {σ k : Type} [CommRing k] in
/- English proof (translation)
Introduce `j` and use `by rw [Polynomial.finset_sum_coeff] exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => hp i hi j`.
-/
private theorem coeffHom_sum {ι : Type} (s : Finset ι) {e : ℕ} (p : ι → (MvPolynomial σ k)[X])
    (hp : ∀ i ∈ s, _root_.GlobalTheory.TsenCount.CoeffHom e (p i)) :
    _root_.GlobalTheory.TsenCount.CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [Polynomial.finset_sum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => hp i hi j

open Polynomial in
variable {σ k : Type} [CommRing k] in
/- English proof (translation)
Introduce `j` and use `by rw [Polynomial.coeff_mul] exact MvPolynomial.IsHomogeneous.sum _ _ _ fun x _ => (hp x.1).mul (hq x.2)`.
-/
private theorem coeffHom_mul {e e' : ℕ} {p q : (MvPolynomial σ k)[X]}
    (hp : _root_.GlobalTheory.TsenCount.CoeffHom e p) (hq : _root_.GlobalTheory.TsenCount.CoeffHom e' q) :
    _root_.GlobalTheory.TsenCount.CoeffHom (e + e') (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun x _ => (hp x.1).mul (hq x.2)

open Polynomial in
variable {σ k : Type} [CommRing k] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `j`. Rewrite using `[Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]`. Use `split_ifs`.

Conclude with `MvPolynomial.isHomogeneous_one _ _`. Conclude with `MvPolynomial.isHomogeneous_zero _ _ _`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `coeffHom_mul (hp a (Finset.mem_insert_self a s)) (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))`.
-/
private theorem coeffHom_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (p : ι → (MvPolynomial σ k)[X]) (hp : ∀ i ∈ s, _root_.GlobalTheory.TsenCount.CoeffHom (e i) (p i)) :
    _root_.GlobalTheory.TsenCount.CoeffHom (∑ i ∈ s, e i) (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro j
    rw [Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]
    split_ifs
    · exact MvPolynomial.isHomogeneous_one _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact coeffHom_mul (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

open Polynomial in
variable {σ k : Type} [CommRing k] in
/- English proof (translation)
Use `coeffHom_prod (Finset.range m) (fun _ => e) (fun _ => p) (fun _ _ => hp)` as an intermediate fact. Simplify using `using this`.
-/
private theorem coeffHom_pow {e : ℕ} {p : (MvPolynomial σ k)[X]}
    (hp : _root_.GlobalTheory.TsenCount.CoeffHom e p) (m : ℕ) :
    _root_.GlobalTheory.TsenCount.CoeffHom (m * e) (p ^ m) := by
  have := coeffHom_prod (Finset.range m) (fun _ => e) (fun _ => p) (fun _ _ => hp)
  simpa using this

/- English proof (translation)
Establish `hM0 : (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}).IsMaximal` using `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨0, rfl⟩`. Establish `hIM : Ideal.span (Set.range g) ≤ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval]`.

Conclude with `hg i`. Take `⟨Q, hQmin, hQM⟩` from `Ideal.exists_minimalPrimes_le hIM`. Establish `hQprime : Q.IsPrime` using `hQmin.1.1`. Establish `hht : Q.height ≤ r`. Use `(Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ Q hQmin).trans ?_` and prove the remaining obligations.

Establish `h1` using `Submodule.spanRank_span_le_card (R := MvPolynomial (Fin m) k) (Set.range g)`. Establish `h2 : Cardinal.mk (Set.range g) ≤ r`. Simplify using `using Cardinal.mk_range_le (f := g)`. Combine the equalities or inequalities in the displayed calculation. Establish `hQne : Q ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}`.

Introduce `hQ`. Establish `hm` using `(_root_.ReciprocityTheory.CA.height_maximal_mvPolynomial_field k m (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)})).2`. Establish `hm' : Q.height = m` using `hQ ▸ hm`. Rewrite `hht` using `[hm']`. Establish `: m ≤ r` using `by exact_mod_cast hht`.

Use linear arithmetic over natural numbers and integers. Establish `hex : ∃ J : Ideal (MvPolynomial (Fin m) k), J.IsMaximal ∧ Q ≤ J ∧ J ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hjac : Q.jacobson = Q` using `isJacobsonRing_iff_prime_eq.1 inferInstance Q hQprime`.

Establish `hle : MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} ≤ Q.jacobson`. Rewrite using `[Ideal.jacobson]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `J ⟨hQJ, hJ⟩`. Rewrite using `[hcon J hJ hQJ]`.

Conclude with `hQne (le_antisymm hQM (hjac ▸ hle))`. Take `⟨J, hJ, hQJ, hJne⟩` from `hex`. Take `⟨x, rfl⟩` from `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hJ`. Use `⟨x, ?_, fun i => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hJne rfl`. Establish `hx : g i ∈ MvPolynomial.vanishingIdeal k {x}` using `hQJ (hQmin.1.2 (Ideal.subset_span ⟨i, rfl⟩))`. Rewrite `hx` using `[MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval]`. Then use the resulting hypothesis.
-/
private theorem exists_ne_zero_common_zero_of_lt {k : Type} [Field k] [IsAlgClosed k] {m r : ℕ}
    (g : Fin r → MvPolynomial (Fin m) k) (hg : ∀ i, MvPolynomial.eval 0 (g i) = 0) (hr : r < m) :
    ∃ x : Fin m → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (g i) = 0 := by
  classical
  have hM0 : (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}).IsMaximal :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨0, rfl⟩
  have hIM : Ideal.span (Set.range g) ≤ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval]
    exact hg i
  obtain ⟨Q, hQmin, hQM⟩ := Ideal.exists_minimalPrimes_le hIM
  have hQprime : Q.IsPrime := hQmin.1.1
  have hht : Q.height ≤ r := by
    refine (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ Q hQmin).trans ?_
    have h1 := Submodule.spanRank_span_le_card (R := MvPolynomial (Fin m) k) (Set.range g)
    have h2 : Cardinal.mk (Set.range g) ≤ r := by
      simpa using Cardinal.mk_range_le (f := g)
    calc Cardinal.toENat (Submodule.spanRank (Ideal.span (Set.range g)))
        ≤ Cardinal.toENat (r : Cardinal) := Cardinal.toENat.monotone' (h1.trans h2)
      _ = r := by simp
  have hQne : Q ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    intro hQ
    have hm := (_root_.ReciprocityTheory.CA.height_maximal_mvPolynomial_field k m (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)})).2
    have hm' : Q.height = m := hQ ▸ hm
    rw [hm'] at hht
    have : m ≤ r := by exact_mod_cast hht
    omega
  have hex : ∃ J : Ideal (MvPolynomial (Fin m) k), J.IsMaximal ∧ Q ≤ J ∧
      J ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    by_contra hcon
    push_neg at hcon
    have hjac : Q.jacobson = Q := isJacobsonRing_iff_prime_eq.1 inferInstance Q hQprime
    have hle : MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} ≤ Q.jacobson := by
      rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro J ⟨hQJ, hJ⟩
      rw [hcon J hJ hQJ]
    exact hQne (le_antisymm hQM (hjac ▸ hle))
  obtain ⟨J, hJ, hQJ, hJne⟩ := hex
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hJ
  refine ⟨x, ?_, fun i => ?_⟩
  · rintro rfl
    exact hJne rfl
  · have hx : g i ∈ MvPolynomial.vanishingIdeal k {x} :=
      hQJ (hQmin.1.2 (Ideal.subset_span ⟨i, rfl⟩))
    rwa [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] at hx

open Polynomial in
/- English proof (translation)
Use `set D := F.support.sup fun ν => (F.coeff ν).natDegree with hD`. Establish `hDle : ∀ ν, (F.coeff ν).natDegree ≤ D`. Introduce `ν`. Distinguish the cases in `hν : ν ∈ F.support`. Conclude with `Finset.le_sup (f := fun ν => (F.coeff ν).natDegree) hν`.

Rewrite using `[MvPolynomial.notMem_support_iff.1 hν]`. Simplify using the standard rewrite rules. Use `set s := D`. Use `set m := n * (s + 1)`. Use `set e : Fin n × Fin (s + 1) ≃ Fin m := finProdFinEquiv`.

Set `y : Fin n → (MvPolynomial (Fin m) k)[X]` to `fun i => ∑ j : Fin (s + 1), Polynomial.C (MvPolynomial.X (e (i, j))) * Polynomial.X ^ (j : ℕ)`. Set `Φ : (MvPolynomial (Fin m) k)[X]` to `MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C)) y F`. Establish `hy : ∀ i, _root_.GlobalTheory.TsenCount.CoeffHom 1 (y i)`. Introduce `i`. Use `coeffHom_sum _ _ fun j _ => ?_` and prove the remaining obligations.

Introduce `l`. Rewrite using `[Polynomial.coeff_C_mul_X_pow]`. Use `split_ifs`. Conclude with `MvPolynomial.isHomogeneous_X _ _`. Conclude with `MvPolynomial.isHomogeneous_zero _ _ _`.

Establish `hyd : ∀ i, (y i).natDegree ≤ s`. Introduce `i`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.2)`. Establish `hΦ : _root_.GlobalTheory.TsenCount.CoeffHom d Φ`.

Simplify using `only [Φ, MvPolynomial.eval₂_eq']`. Use `coeffHom_sum _ _ fun ν hν => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i, ν i = d`. Use `hF (MvPolynomial.mem_support_iff.1 hν)` as an intermediate fact. Rewrite using `[← this]`.

Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Establish `h1 : _root_.GlobalTheory.TsenCount.CoeffHom 0 ((Polynomial.mapRingHom (MvPolynomial.C (σ` using `Fin m))) (F.coeff ν)) := by`. Introduce `l`. Rewrite using `[Polynomial.coe_mapRingHom, Polynomial.coeff_map]`. Conclude with `MvPolynomial.isHomogeneous_C _ _`.

Establish `h2` using `coeffHom_prod Finset.univ (fun i => ν i * 1) (fun i => y i ^ ν i) (fun i _ => coeffHom_pow (hy i) (ν i))`. Establish `h3` using `coeffHom_mul h1 h2`. Simplify `h3` using `[hdeg]`. Establish `hΦdeg : Φ.natDegree ≤ D + d * s`. Simplify using `only [Φ, MvPolynomial.eval₂_eq']`.

Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun ν hν => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i, ν i = d`. Use `hF (MvPolynomial.mem_support_iff.1 hν)` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype]`.

Use `(Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Conclude with `(Polynomial.natDegree_map_le).trans (hDle ν)`. Use `(Polynomial.natDegree_prod_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `set r := D + d * s + 1`.

Establish `hrm : r < m`. Simplify using `only [r, m, s]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨a, ha0, ha⟩` from `exists_ne_zero_common_zero_of_lt (k := k) (m := m) (r := r) (fun j => Φ.coeff j) (fun j => by`. Rewrite using `[MvPolynomial.eval_zero]`.

Conclude with `(hΦ j).coeff_eq_zero (by simp; omega)) hrm`. Set `x : Fin n → k[X]` to `fun i => ∑ j : Fin (s + 1), Polynomial.C (a (e (i, j))) * Polynomial.X ^ (j : ℕ)`. Establish `hmapΦ : Polynomial.map (MvPolynomial.eval a) Φ = 0`. Use extensionality with `j`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero]`.

Distinguish the cases in `hj : j < r`. Conclude with `ha ⟨j, hj⟩`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]`. Establish `hΦx : Polynomial.map (MvPolynomial.eval a) Φ = MvPolynomial.eval x F`. Establish `h1` using `MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (MvPolynomial.eval a)) (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) y F`.

Rewrite `h1` using `[Polynomial.coe_mapRingHom]`. Simplify using `only [Φ]`. Rewrite using `[h1]`. Establish `h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp (Polynomial.mapRingHom (MvPolynomial.C (σ` using `Fin m))) = RingHom.id k[X] := by`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations.

Establish `hc : (MvPolynomial.eval a).comp (MvPolynomial.C (σ` using `Fin m)) = RingHom.id k := by`. Use extensionality with `c`. Simplify using the standard rewrite rules. Rewrite using `[RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom, Polynomial.map_map, hc, Polynomial.map_id, RingHom.id_apply]`. Establish `h3 : Polynomial.map (MvPolynomial.eval a) ∘ y = x`.

Use function extensionality and compare the values at `i`. Simplify using `[y, x, Polynomial.map_sum]`. Rewrite using `[h2, h3]`. Both sides reduce to the same expression. Use `⟨x, ?_, hΦx ▸ hmapΦ⟩` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, a t ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `ha0 (funext hcon)`. Take `⟨⟨i, j⟩, rfl⟩` from `e.surjective t`.

Introduce `hx`. Establish `hxi : (x i).coeff j = 0`. Rewrite using `[congrFun hx i]`. Simplify using the standard rewrite rules. Establish `hc : (x i).coeff j = a (e (i, j))`.

Simplify using `only [x, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `h`. Conclude with `hb (Fin.ext h.symm)`. Simplify using the standard rewrite rules. Conclude with `ht (hc.symm.trans hxi)`.
-/
private theorem exists_ne_zero_polynomial_zero_of_homogeneous {k : Type} [Field k] [IsAlgClosed k] {n d : ℕ}
    (F : MvPolynomial (Fin n) k[X]) (hF : F.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  classical
  set D := F.support.sup fun ν => (F.coeff ν).natDegree with hD
  have hDle : ∀ ν, (F.coeff ν).natDegree ≤ D := by
    intro ν
    by_cases hν : ν ∈ F.support
    · exact Finset.le_sup (f := fun ν => (F.coeff ν).natDegree) hν
    · rw [MvPolynomial.notMem_support_iff.1 hν]
      simp
  set s := D
  set m := n * (s + 1)
  set e : Fin n × Fin (s + 1) ≃ Fin m := finProdFinEquiv
  let y : Fin n → (MvPolynomial (Fin m) k)[X] := fun i =>
    ∑ j : Fin (s + 1), Polynomial.C (MvPolynomial.X (e (i, j))) * Polynomial.X ^ (j : ℕ)
  let Φ : (MvPolynomial (Fin m) k)[X] :=
    MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C)) y F
  have hy : ∀ i, _root_.GlobalTheory.TsenCount.CoeffHom 1 (y i) := by
    intro i
    refine coeffHom_sum _ _ fun j _ => ?_
    intro l
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hyd : ∀ i, (y i).natDegree ≤ s := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.2)
  have hΦ : _root_.GlobalTheory.TsenCount.CoeffHom d Φ := by
    simp only [Φ, MvPolynomial.eval₂_eq']
    refine coeffHom_sum _ _ fun ν hν => ?_
    have hdeg : ∑ i, ν i = d := by
      have := hF (MvPolynomial.mem_support_iff.1 hν)
      rw [← this]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    have h1 : _root_.GlobalTheory.TsenCount.CoeffHom 0
        ((Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) (F.coeff ν)) := by
      intro l
      rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      exact MvPolynomial.isHomogeneous_C _ _
    have h2 := coeffHom_prod Finset.univ (fun i => ν i * 1) (fun i => y i ^ ν i)
      (fun i _ => coeffHom_pow (hy i) (ν i))
    have h3 := coeffHom_mul h1 h2
    simpa [hdeg] using h3
  have hΦdeg : Φ.natDegree ≤ D + d * s := by
    simp only [Φ, MvPolynomial.eval₂_eq']
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun ν hν => ?_
    have hdeg : ∑ i, ν i = d := by
      have := hF (MvPolynomial.mem_support_iff.1 hν)
      rw [← this]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)
    · exact (Polynomial.natDegree_map_le).trans (hDle ν)
    · refine (Polynomial.natDegree_prod_le _ _).trans ?_
      calc ∑ i, (y i ^ ν i).natDegree ≤ ∑ i, ν i * s :=
            Finset.sum_le_sum fun i _ => (Polynomial.natDegree_pow_le).trans
              (Nat.mul_le_mul_left _ (hyd i))
        _ = d * s := by rw [← Finset.sum_mul, hdeg]
  set r := D + d * s + 1
  have hrm : r < m := by
    simp only [r, m, s]
    nlinarith
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_common_zero_of_lt (k := k) (m := m) (r := r)
    (fun j => Φ.coeff j) (fun j => by
      rw [MvPolynomial.eval_zero]
      exact (hΦ j).coeff_eq_zero (by simp; omega)) hrm
  let x : Fin n → k[X] := fun i =>
    ∑ j : Fin (s + 1), Polynomial.C (a (e (i, j))) * Polynomial.X ^ (j : ℕ)
  have hmapΦ : Polynomial.map (MvPolynomial.eval a) Φ = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < r
    · exact ha ⟨j, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have hΦx : Polynomial.map (MvPolynomial.eval a) Φ = MvPolynomial.eval x F := by
    have h1 := MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (MvPolynomial.eval a))
      (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) y F
    rw [Polynomial.coe_mapRingHom] at h1
    simp only [Φ]
    rw [h1]
    have h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp
        (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) = RingHom.id k[X] := by
      refine RingHom.ext fun p => ?_
      have hc : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := Fin m)) = RingHom.id k := by
        ext c
        simp
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom, Polynomial.map_map, hc,
        Polynomial.map_id, RingHom.id_apply]
    have h3 : Polynomial.map (MvPolynomial.eval a) ∘ y = x := by
      funext i
      simp [y, x, Polynomial.map_sum]
    rw [h2, h3]
    rfl
  refine ⟨x, ?_, hΦx ▸ hmapΦ⟩
  obtain ⟨t, ht⟩ : ∃ t, a t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact ha0 (funext hcon)
  obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective t
  intro hx
  have hxi : (x i).coeff j = 0 := by
    rw [congrFun hx i]
    simp
  have hc : (x i).coeff j = a (e (i, j)) := by
    simp only [x, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  exact ht (hc.symm.trans hxi)

open Polynomial in
/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) f.coeffs`. Establish `hc0 : algebraMap k[X] (RatFunc k) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f ∈ Set.range (MvPolynomial.map (algebraMap k[X] (RatFunc k))) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `a ha`.

Take `⟨ν, hν, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 ha`. Rewrite using `[MvPolynomial.coeff_C_mul]`. Establish `hν' : f.coeff ν ∈ f.coeffs`. Use `MvPolynomial.coeff_mem_coeffs ν ?_` and prove the remaining obligations. Introduce `h`.

Rewrite `hν` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, h, mul_zero]`. Conclude with `hν rfl`. Take `⟨p, hp⟩` from `hb _ hν'`. Conclude with `⟨p, hp.trans (Algebra.smul_def _ _)⟩`. Establish `hFh : F.IsHomogeneous d`.

Use `isHomogeneous_of_map_of_injective (IsFractionRing.injective k[X] (RatFunc k)) ?_` and prove the remaining obligations. Rewrite using `[hF]`. Simplify using `using (MvPolynomial.isHomogeneous_C (Fin n) (algebraMap k[X] (RatFunc k) b)).mul hf`. Take `⟨x, hx0, hx⟩` from `exists_ne_zero_polynomial_zero_of_homogeneous F hFh hd hdn`. Use `⟨algebraMap k[X] (RatFunc k) ∘ x, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `IsFractionRing.injective k[X] (RatFunc k) (by simpa using congrFun h i)`. Establish `key` using `mvPolynomial_eval_map_comp (algebraMap k[X] (RatFunc k)) x F`.

Rewrite `key` using `[hF, hx, map_zero]`. Simplify using `only [map_mul, MvPolynomial.eval_C] at key`. Conclude with `(mul_eq_zero.1 key).resolve_left hc0`.
-/
private theorem exists_ne_zero_ratFunc_homogeneous_zero {k : Type} [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (RatFunc k)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) f.coeffs
  have hc0 : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨F, hF⟩ : MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f ∈
      Set.range (MvPolynomial.map (algebraMap k[X] (RatFunc k))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, hν, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    rw [MvPolynomial.coeff_C_mul]
    have hν' : f.coeff ν ∈ f.coeffs := by
      refine MvPolynomial.coeff_mem_coeffs ν ?_
      intro h
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, h, mul_zero] at hν
      exact hν rfl
    obtain ⟨p, hp⟩ := hb _ hν'
    exact ⟨p, hp.trans (Algebra.smul_def _ _)⟩
  have hFh : F.IsHomogeneous d := by
    refine isHomogeneous_of_map_of_injective (IsFractionRing.injective k[X] (RatFunc k)) ?_
    rw [hF]
    simpa using (MvPolynomial.isHomogeneous_C (Fin n) (algebraMap k[X] (RatFunc k) b)).mul hf
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_polynomial_zero_of_homogeneous F hFh hd hdn
  refine ⟨algebraMap k[X] (RatFunc k) ∘ x, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact IsFractionRing.injective k[X] (RatFunc k) (by simpa using congrFun h i)
  · have key := mvPolynomial_eval_map_comp (algebraMap k[X] (RatFunc k)) x F
    rw [hF, hx, map_zero] at key
    simp only [map_mul, MvPolynomial.eval_C] at key
    exact (mul_eq_zero.1 key).resolve_left hc0

open Polynomial in

/- English proof (translation)
Introduce `k K _ _ _ _ _ n d f hf hd hdn`. Conclude with `exists_ne_zero_homogeneous_zero_of_forall_subfield (F := RatFunc k) (fun n d f hf hd hdn => exists_ne_zero_ratFunc_homogeneous_zero (k := k) n d f hf hd hdn) n d f hf hd hdn`.
-/
theorem _root_.GlobalTheory.tsen_algebraic_extension_ratFunc :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
      [Algebra.IsAlgebraic (RatFunc k) K] (n d : ℕ) (f : MvPolynomial (Fin n) K),
      f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  intro k K _ _ _ _ _ n d f hf hd hdn
  exact exists_ne_zero_homogeneous_zero_of_forall_subfield (F := RatFunc k)
    (fun n d f hf hd hdn => exists_ne_zero_ratFunc_homogeneous_zero (k := k) n d f hf hd hdn) n d f hf hd hdn

end GlobalTheory
