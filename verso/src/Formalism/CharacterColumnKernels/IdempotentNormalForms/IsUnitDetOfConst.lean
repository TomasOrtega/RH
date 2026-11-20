import Formalism.CharacterColumnKernels.StatementN

open Finset

noncomputable section

namespace Formalism.NG
namespace BlockDetAlt

variable {O : Type*} [CommRing O] {X' : Type*}

def liftHom : (X' → O) →+* (X' → FractionRing O) :=
  RingHom.pi fun x' => (algebraMap O (FractionRing O)).comp (Pi.evalRingHom (fun _ : X' => O) x')

def Fr (T' : Subalgebra O (X' → O)) : Subring (X' → FractionRing O) :=
  T'.toSubring.map liftHom

/- English proof (translation)
Simplify using `only [Fr, Subring.mem_map, Subalgebra.mem_toSubring]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, hf, fun x' => rfl⟩`. Introduce and unpack `⟨f, hf, h⟩`.

Conclude with `⟨f, hf, funext h⟩`.
-/
lemma mem_Fr {T' : Subalgebra O (X' → O)} {φ : X' → FractionRing O} :
    φ ∈ Fr T' ↔ ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') = φ x' := by
  simp only [Fr, Subring.mem_map, Subalgebra.mem_toSubring]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, fun x' => rfl⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, funext h⟩

def goodS (T' : Subalgebra O (X' → O)) : Subring (PowerSeries (X' → FractionRing O)) where
  carrier := {φ | ∀ n, PowerSeries.coeff n φ ∈ Fr T'}
  mul_mem' {a b} ha hb n := by
    rw [PowerSeries.coeff_mul]
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (ha _) (hb _)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {a b} ha hb n := by
    rw [map_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' n := by
    rw [map_zero]
    exact Subring.zero_mem _
  neg_mem' {a} ha n := by
    rw [map_neg]
    exact Subring.neg_mem _ (ha n)

variable {d : Type} [Fintype d] [DecidableEq d]

def coefMat (n : ℕ) (a : Matrix d d (PowerSeries (X' → FractionRing O))) :
    X' → Matrix d d (FractionRing O) :=
  fun x' i j => PowerSeries.coeff n (a i j) x'

/- English proof (translation)
Use extensionality with `x' i j`. Simplify using `only [coefMat, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, Finset.sum_apply, Matrix.sum_apply, Pi.mul_apply]`. Conclude with `Finset.sum_comm`.
-/
lemma coefMat_mul (n : ℕ) (a b : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (a * b) = ∑ p ∈ antidiagonal n, coefMat p.1 a * coefMat p.2 b := by
  ext x' i j
  simp only [coefMat, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, Finset.sum_apply, Matrix.sum_apply,
    Pi.mul_apply]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `x' i j`. Simplify using `[coefMat]`.
-/
lemma coefMat_add (n : ℕ) (a b : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (a + b) = coefMat n a + coefMat n b := by
  ext x' i j
  simp [coefMat]

/- English proof (translation)
Use extensionality with `x' i j`. Simplify using `[coefMat]`.
-/
lemma coefMat_neg (n : ℕ) (a : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (-a) = -coefMat n a := by
  ext x' i j
  simp [coefMat]

/- English proof (translation)
Use extensionality with `x' i j`. Simplify using `[coefMat]`.
-/
lemma coefMat_zero (n : ℕ) :
    coefMat n (0 : Matrix d d (PowerSeries (X' → FractionRing O))) = 0 := by
  ext x' i j
  simp [coefMat]

/- English proof (translation)
Use extensionality with `x' i j`. Apply the tactic sequence `by_cases hn : n = 0 <;> by_cases hij : i = j <;>`. Simplify using `[coefMat, Matrix.one_apply, hn, hij, PowerSeries.coeff_one]`.
-/
lemma coefMat_one (n : ℕ) :
    coefMat n (1 : Matrix d d (PowerSeries (X' → FractionRing O))) = if n = 0 then 1 else 0 := by
  ext x' i j
  by_cases hn : n = 0 <;> by_cases hij : i = j <;>
    simp [coefMat, Matrix.one_apply, hn, hij, PowerSeries.coeff_one]

def goodM (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    Subring (Matrix d d (PowerSeries (X' → FractionRing O))) where
  carrier := {a | ∀ n, coefMat n a ∈ R'}
  mul_mem' {a b} ha hb n := by
    rw [coefMat_mul]
    exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (ha _) (hb _)
  one_mem' n := by
    rw [coefMat_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  add_mem' {a b} ha hb n := by
    rw [coefMat_add]
    exact Subalgebra.add_mem _ (ha n) (hb n)
  zero_mem' n := by
    rw [coefMat_zero]
    exact Subalgebra.zero_mem _
  neg_mem' {a} ha n := by
    rw [coefMat_neg]
    exact Subalgebra.neg_mem _ (ha n)

section Trunc
variable {K : Type*} [CommRing K]

/- English proof (translation)
Establish `hdiv : ∀ i j, (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣ U i j - V i j` using `fun i j => PowerSeries.X_pow_dvd_iff.2 (fun k hk => by rw [map_sub, h i j k (by omega), sub_self])`. Establish `hUV : (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix U = (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix V`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hdiv i j))`. Establish `hdet : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) U.det = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) V.det`.

Rewrite using `[RingHom.map_det, RingHom.map_det, hUV]`. Establish `hd` using `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hdet)`. Establish `h0` using `PowerSeries.X_pow_dvd_iff.1 hd m (by omega)`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
lemma coeff_det_congr {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (U V : Matrix ι ι (PowerSeries K))
    (h : ∀ i j, ∀ k ≤ m, PowerSeries.coeff k (U i j) = PowerSeries.coeff k (V i j)) :
    PowerSeries.coeff m U.det = PowerSeries.coeff m V.det := by
  have hdiv : ∀ i j, (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣ U i j - V i j := fun i j =>
    PowerSeries.X_pow_dvd_iff.2 (fun k hk => by rw [map_sub, h i j k (by omega), sub_self])
  have hUV : (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix U =
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix V := by
    ext i j
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hdiv i j))
  have hdet : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) U.det =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) V.det := by
    rw [RingHom.map_det, RingHom.map_det, hUV]
  have hd := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hdet)
  have h0 := PowerSeries.X_pow_dvd_iff.1 hd m (by omega)
  rwa [map_sub, sub_eq_zero] at h0

def wt {m : ℕ} (e : Fin m →₀ ℕ) : ℕ := ∑ j, (j.1 + 1) * e j

def bnd (m : ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => m)

def psi (m : ℕ) : MvPolynomial (Fin m) K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.C) (fun j : Fin m => PowerSeries.X ^ (j.1 + 1))

/- English proof (translation)
Establish `hbnd : ∀ e : Fin m →₀ ℕ, wt e = m → e ∈ Finset.Iic (bnd m)`. Introduce `e he`. Rewrite using `[Finset.mem_Iic, Finsupp.le_def]`. Introduce `j`. Establish `hb : bnd m j = m` using `rfl`.

Rewrite using `[hb]`. Establish `h1 : (j.1 + 1) * e j ≤ wt e` using `Finset.single_le_sum (f := fun j : Fin m => (j.1 + 1) * e j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Combine the equalities or inequalities in the displayed calculation. Establish `hpsi : ∀ (e : Fin m →₀ ℕ) (c : K), psi m (MvPolynomial.monomial e c) = PowerSeries.C c * PowerSeries.X ^ wt e`. Introduce `e c`.

Rewrite using `[psi, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Repeatedly rewrite using `[← pow_mul]`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression. Use `conv_lhs => rw [P.as_sum]`.

Rewrite using `[map_sum, map_sum]`. Simplify using `only [hpsi, PowerSeries.coeff_C_mul_X_pow]`. Establish `h1 : ∑ e ∈ P.support, (if m = wt e then MvPolynomial.coeff e P else 0) = ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if m = wt e then MvPolynomial.coeff e P else 0)` using `Finset.sum_subset Finset.subset_union_left (fun e _ he => by`. Rewrite using `[MvPolynomial.notMem_support_iff.1 he]`. Use the proof step `simp)`.

Establish `h2 : ∑ e ∈ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0) = ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0)` using `Finset.sum_subset Finset.subset_union_right (fun e _ he => if_neg (fun h => he (hbnd e h)))`. Rewrite using `[h1, h2]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : wt e = m`. Rewrite using `[if_pos h, if_pos h.symm]`.

Rewrite using `[if_neg h, if_neg (Ne.symm h)]`.
-/
lemma coeff_psi (m : ℕ) (P : MvPolynomial (Fin m) K) :
    PowerSeries.coeff m (psi m P) =
      ∑ e ∈ Finset.Iic (bnd m), if wt e = m then MvPolynomial.coeff e P else 0 := by
  classical
  have hbnd : ∀ e : Fin m →₀ ℕ, wt e = m → e ∈ Finset.Iic (bnd m) := by
    intro e he
    rw [Finset.mem_Iic, Finsupp.le_def]
    intro j
    have hb : bnd m j = m := rfl
    rw [hb]
    have h1 : (j.1 + 1) * e j ≤ wt e :=
      Finset.single_le_sum (f := fun j : Fin m => (j.1 + 1) * e j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    calc e j ≤ (j.1 + 1) * e j := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ wt e := h1
      _ = m := he
  have hpsi : ∀ (e : Fin m →₀ ℕ) (c : K), psi m (MvPolynomial.monomial e c) =
      PowerSeries.C c * PowerSeries.X ^ wt e := by
    intro e c
    rw [psi, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  conv_lhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  simp only [hpsi, PowerSeries.coeff_C_mul_X_pow]
  have h1 : ∑ e ∈ P.support, (if m = wt e then MvPolynomial.coeff e P else 0) =
      ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if m = wt e then MvPolynomial.coeff e P else 0) :=
    Finset.sum_subset Finset.subset_union_left (fun e _ he => by
      rw [MvPolynomial.notMem_support_iff.1 he]
      simp)
  have h2 : ∑ e ∈ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0) =
      ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0) :=
    Finset.sum_subset Finset.subset_union_right (fun e _ he => if_neg (fun h => he (hbnd e h)))
  rw [h1, h2]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : wt e = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
end Trunc

section Good
variable {d : Type} [Fintype d] [DecidableEq d]

def HypDet (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    Prop :=
  ∀ (m : ℕ) (r : Fin m → R') (s : Fin m →₀ ℕ), ∃ f ∈ T', ∀ x',
    algebraMap O (FractionRing O) (f x') =
      MvPolynomial.coeff s (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) (FractionRing O)) •
        ((r i : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C))

/- English proof (translation)
Establish `hL : PowerSeries.coeff n a.det x' = PowerSeries.coeff n ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix a).det`. Rewrite using `[← RingHom.map_det, PowerSeries.coeff_map]`. Both sides reduce to the same expression. Establish `hmat : (psi (n + Fintype.card d)).mapMatrix (∑ j : Fin (n + Fintype.card d), (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) • (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C) = (PowerSeries.X : PowerSeries (FractionRing O)) • ∑ j …`. Use extensionality with `i k`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, psi, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL, RingHom.map_det, hmat, Matrix.det_smul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]`.

Use `symm`. Apply `coeff_det_congr` to reduce the goal to its premises. Introduce `i j k hk`. Establish `hd0 : 0 < Fintype.card d` using `Fintype.card_pos_iff.2 ⟨i⟩`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, RingHom.mapMatrix_apply, PowerSeries.coeff_map]`.

Rewrite using `[Finset.sum_eq_single ⟨k, by omega⟩]`. Rewrite using `[mul_comm, PowerSeries.coeff_C_mul_X_pow, if_pos rfl]`. Both sides reduce to the same expression. Introduce `b _ hb`. Rewrite using `[mul_comm, PowerSeries.coeff_C_mul_X_pow, if_neg]`.

Introduce `h`. Conclude with `hb (Fin.ext h.symm)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma coeff_det_eq (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (a : Matrix d d (PowerSeries (X' → FractionRing O))) (ha : a ∈ goodM R') (n : ℕ) (x' : X') :
    PowerSeries.coeff n a.det x' = PowerSeries.coeff (n + Fintype.card d) (psi (n + Fintype.card d)
      (Matrix.det (∑ j : Fin (n + Fintype.card d),
        (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) •
          (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map
            MvPolynomial.C))) := by
  classical
  have hL : PowerSeries.coeff n a.det x' =
      PowerSeries.coeff n ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix a).det := by
    rw [← RingHom.map_det, PowerSeries.coeff_map]
    rfl
  have hmat : (psi (n + Fintype.card d)).mapMatrix (∑ j : Fin (n + Fintype.card d),
      (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) •
        (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C) =
      (PowerSeries.X : PowerSeries (FractionRing O)) • ∑ j : Fin (n + Fintype.card d),
        (PowerSeries.X : PowerSeries (FractionRing O)) ^ j.1 • (coefMat j.1 a x').map PowerSeries.C := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, psi, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hL, RingHom.map_det, hmat, Matrix.det_smul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    Nat.add_sub_cancel]
  symm
  apply coeff_det_congr
  intro i j k hk
  have hd0 : 0 < Fintype.card d := Fintype.card_pos_iff.2 ⟨i⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    RingHom.mapMatrix_apply, PowerSeries.coeff_map]
  rw [Finset.sum_eq_single ⟨k, by omega⟩]
  · rw [mul_comm, PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
    rfl
  · intro b _ hb
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow, if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `show ∀ n, PowerSeries.coeff n a.det ∈ Fr T'`. Introduce `n`. Set `r : Fin (n + Fintype.card d) → R'` to `fun j => ⟨coefMat j.1 a, ha j.1⟩`. Use `choose F hF hFx using fun e : Fin (n + Fintype.card d) →₀ ℕ => hyp (n + Fintype.card d) r e`. Use `mem_Fr.2 ⟨∑ e ∈ Finset.Iic (bnd (n + Fintype.card d)), if wt e = n + Fintype.card d then F e else 0, ?_, fun x' => ?_⟩` and prove the remaining obligations.

Use `Subalgebra.sum_mem _ fun e _ => ?_ split_ifs` and prove the remaining obligations. Conclude with `hF e`. Conclude with `Subalgebra.zero_mem _`. Rewrite using `[coeff_det_eq R' a ha n x', coeff_psi, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : wt e = n + Fintype.card d`. Rewrite using `[if_pos h, if_pos h]`. Conclude with `hFx e x'`. Rewrite using `[if_neg h, if_neg h]`. Simplify using the standard rewrite rules.
-/
lemma detGood (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') {a : Matrix d d (PowerSeries (X' → FractionRing O))}
    (ha : a ∈ goodM R') : a.det ∈ goodS T' := by
  classical
  show ∀ n, PowerSeries.coeff n a.det ∈ Fr T'
  intro n
  let r : Fin (n + Fintype.card d) → R' := fun j => ⟨coefMat j.1 a, ha j.1⟩
  choose F hF hFx using fun e : Fin (n + Fintype.card d) →₀ ℕ => hyp (n + Fintype.card d) r e
  refine mem_Fr.2 ⟨∑ e ∈ Finset.Iic (bnd (n + Fintype.card d)),
    if wt e = n + Fintype.card d then F e else 0, ?_, fun x' => ?_⟩
  · refine Subalgebra.sum_mem _ fun e _ => ?_
    split_ifs
    · exact hF e
    · exact Subalgebra.zero_mem _
  · rw [coeff_det_eq R' a ha n x', coeff_psi, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : wt e = n + Fintype.card d
    · rw [if_pos h, if_pos h]
      exact hFx e x'
    · rw [if_neg h, if_neg h]
      simp
end Good

section Inv
variable {d : Type} [Fintype d] [DecidableEq d]

/- English proof (translation)
Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]`. Conclude with `isUnit_one`.
-/
lemma isUnit_det_of_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (PowerSeries (X' → FractionRing O)))
    (hA : (PowerSeries.constantCoeff).mapMatrix A = 1) : IsUnit A.det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
Establish `hAB : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A (isUnit_det_of_const A hc)`. Establish `h0 : coefMat 0 A = 1`. Use extensionality with `x' i j`. Establish `h1` using `congrArg (fun M => M i j x') hc`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1`.

Simplify using `only [coefMat, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[h1]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Use `show ∀ n, coefMat n A⁻¹ ∈ R'`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Establish `e` using `congrArg (coefMat n) hAB`. Rewrite `e` using `[coefMat_mul, coefMat_one]`. Establish `hmem : ((0 : ℕ), n) ∈ antidiagonal n` using `by simp`.

Establish `hB : coefMat n A⁻¹ = (if n = 0 then 1 else 0) - ∑ p ∈ (antidiagonal n).erase (0, n), coefMat p.1 A * coefMat p.2 A⁻¹`. Rewrite using `[← e, ← Finset.add_sum_erase _ _ hmem, h0, one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hB]`. Apply `Subalgebra.sub_mem` to reduce the goal to its premises.

Use `split_ifs`. Conclude with `Subalgebra.one_mem _`. Conclude with `Subalgebra.zero_mem _`. Apply `Subalgebra.sum_mem` to reduce the goal to its premises. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_erase]`. Establish `hp2 : p.1 + p.2 = n` using `by simpa using hp.2`. Apply `Subalgebra.mul_mem _ (hA p.1) (ih p.2 ?_)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Conclude with `hp.1 (Prod.ext (by simp; omega) (by simp; omega))`.
-/
lemma invGood (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    {A : Matrix d d (PowerSeries (X' → FractionRing O))} (hA : A ∈ goodM R')
    (hc : (PowerSeries.constantCoeff).mapMatrix A = 1) : A⁻¹ ∈ goodM R' := by
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_det_of_const A hc)
  have h0 : coefMat 0 A = 1 := by
    ext x' i j
    have h1 := congrArg (fun M => M i j x') hc
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    simp only [coefMat, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  show ∀ n, coefMat n A⁻¹ ∈ R'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := congrArg (coefMat n) hAB
    rw [coefMat_mul, coefMat_one] at e
    have hmem : ((0 : ℕ), n) ∈ antidiagonal n := by simp
    have hB : coefMat n A⁻¹ = (if n = 0 then 1 else 0) -
        ∑ p ∈ (antidiagonal n).erase (0, n), coefMat p.1 A * coefMat p.2 A⁻¹ := by
      rw [← e, ← Finset.add_sum_erase _ _ hmem, h0, one_mul]
      abel
    rw [hB]
    apply Subalgebra.sub_mem
    · split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · apply Subalgebra.sum_mem
      intro p hp
      rw [Finset.mem_erase] at hp
      have hp2 : p.1 + p.2 = n := by simpa using hp.2
      apply Subalgebra.mul_mem _ (hA p.1) (ih p.2 ?_)
      by_contra hlt
      exact hp.1 (Prod.ext (by simp; omega) (by simp; omega))
end Inv

section Schur
variable {d : Type} [Fintype d] [DecidableEq d]

def optEquiv (g d : Type) : Option g × d ≃ d ⊕ (g × d) where
  toFun x := match x with
    | (none, i) => Sum.inl i
    | (some p, i) => Sum.inr (p, i)
  invFun y := match y with
    | Sum.inl i => (none, i)
    | Sum.inr (p, i) => (some p, i)
  left_inv := by rintro ⟨_ | p, i⟩ <;> rfl
  right_inv := by rintro (i | ⟨p, i⟩) <;> rfl

def SchurP (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (g : Type) [Fintype g] : Prop :=
  ∀ [DecidableEq g] (Φ : Matrix (g × d) (g × d) (PowerSeries (X' → FractionRing O))),
    (∀ p q, (Matrix.of fun i j => Φ (p, i) (q, j)) ∈ goodM R') →
    (PowerSeries.constantCoeff).mapMatrix Φ = 1 → Φ.det ∈ goodS T'

/- English proof (translation)
Establish `hFin : ∀ n : ℕ, SchurP T' R' (Fin n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_ Φ _ _`.

Rewrite using `[Matrix.det_isEmpty]`. Conclude with `(goodS T').one_mem`. Consider the case `succ n ih`. Introduce `_ Φ hΦ hc`. Set `E : Fin (n + 1) × d ≃ d ⊕ (Fin n × d)` to `((finSuccEquiv n).prodCongr (Equiv.refl d)).trans (optEquiv (Fin n) d)`.

Establish `hE : ∀ i, E.symm (Sum.inl i) = (0, i)` using `fun i => by simp [E, optEquiv]`. Establish `hE' : ∀ (p : Fin n) i, E.symm (Sum.inr (p, i)) = (p.succ, i)` using `fun p i => by simp [E, optEquiv]`. Set `A : Matrix d d (PowerSeries (X' → FractionRing O))` to `Matrix.of fun i j => Φ (0, i) (0, j)`. Set `B : Matrix d (Fin n × d) (PowerSeries (X' → FractionRing O))` to `Matrix.of fun i Q => Φ (0, i) (Q.1.succ, Q.2)`. Set `C : Matrix (Fin n × d) d (PowerSeries (X' → FractionRing O))` to `Matrix.of fun P j => Φ (P.1.succ, P.2) (0, j)`.

Set `D : Matrix (Fin n × d) (Fin n × d) (PowerSeries (X' → FractionRing O))` to `Matrix.of fun P Q => Φ (P.1.succ, P.2) (Q.1.succ, Q.2)`. Establish `hblk : Matrix.reindex E E Φ = Matrix.fromBlocks A B C D`. Apply the tactic sequence `ext (i | ⟨p, i⟩) (j | ⟨q, j⟩) <;> simp [A, B, C, D, Matrix.reindex_apply, hE, hE']`. Establish `hc' : ∀ P Q, PowerSeries.constantCoeff (Φ P Q) = if P = Q then 1 else 0` using `fun P Q => by`. Establish `h1` using `congrFun (congrFun hc P) Q`.

Simplify `h1` using `[Matrix.one_apply]`. Establish `hAc : (PowerSeries.constantCoeff).mapMatrix A = 1`. Use extensionality with `i j`. Simplify using `[A, hc', Matrix.one_apply]`. Establish `hAg : A ∈ goodM R'` using `hΦ 0 0`.

Use `haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_det_of_const A hAc)`. Rewrite using `[← Matrix.det_reindex_self E Φ, hblk, Matrix.det_fromBlocks₁₁]`. Apply `(goodS T').mul_mem (detGood T' R' hyp hAg)` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Introduce `p q`.

Establish `hb : (Matrix.of fun i j => (D - C * ⅟A * B) (p, i) (q, j)) = (Matrix.of fun i j => Φ (p.succ, i) (q.succ, j)) - (Matrix.of fun i j => Φ (p.succ, i) (0, j)) * A⁻¹ * (Matrix.of fun i j => Φ (0, i) (q.succ, j))`. Use extensionality with `i j`. Simplify using `[A, B, C, D, Matrix.mul_apply, Matrix.invOf_eq_nonsing_inv]`. Rewrite using `[hb]`. Conclude with `(goodM R').sub_mem (hΦ p.succ q.succ) ((goodM R').mul_mem ((goodM R').mul_mem (hΦ p.succ 0) (invGood R' hAg hAc)) (hΦ 0 q.succ))`.

Use extensionality with `P Q`. Simplify using `[A, B, C, D, Matrix.mul_apply, hc', Matrix.one_apply, Matrix.invOf_eq_nonsing_inv, Fin.succ_ne_zero]`. Apply the tactic sequence `all_goals simp only [← Prod.ext_iff]`. Introduce `_ Φ hΦ hc`. Set `e` to `Fintype.equivFin g`.

Set `E : g × d ≃ Fin (Fintype.card g) × d` to `e.prodCongr (Equiv.refl d)`. Establish `h` using `hFin (Fintype.card g) (Matrix.reindex E E Φ) ?_ ?_`. Rewrite `h` using `[Matrix.det_reindex_self]`. Then use the resulting hypothesis. Introduce `p q`. Establish `hb : (Matrix.of fun i j => Matrix.reindex E E Φ (p, i) (q, j)) = Matrix.of fun i j => Φ (e.symm p, i) (e.symm q, j)`.

Use extensionality with `i j`. Simplify using `[E]`. Rewrite using `[hb]`. Conclude with `hΦ _ _`. Rewrite using `[show (PowerSeries.constantCoeff).mapMatrix (Matrix.reindex E E Φ) = Matrix.reindex E E ((PowerSeries.constantCoeff).mapMatrix Φ) from rfl, hc, Matrix.reindex_apply, Matrix.submatrix_one_equiv]`.
-/
lemma schur (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') (g : Type) [Fintype g] : SchurP T' R' g := by
  classical
  have hFin : ∀ n : ℕ, SchurP T' R' (Fin n) := by
    intro n
    induction n with
    | zero =>
      intro _ Φ _ _
      rw [Matrix.det_isEmpty]
      exact (goodS T').one_mem
    | succ n ih =>
      intro _ Φ hΦ hc
      let E : Fin (n + 1) × d ≃ d ⊕ (Fin n × d) :=
        ((finSuccEquiv n).prodCongr (Equiv.refl d)).trans (optEquiv (Fin n) d)
      have hE : ∀ i, E.symm (Sum.inl i) = (0, i) := fun i => by simp [E, optEquiv]
      have hE' : ∀ (p : Fin n) i, E.symm (Sum.inr (p, i)) = (p.succ, i) := fun p i => by simp [E, optEquiv]
      let A : Matrix d d (PowerSeries (X' → FractionRing O)) := Matrix.of fun i j => Φ (0, i) (0, j)
      let B : Matrix d (Fin n × d) (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun i Q => Φ (0, i) (Q.1.succ, Q.2)
      let C : Matrix (Fin n × d) d (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun P j => Φ (P.1.succ, P.2) (0, j)
      let D : Matrix (Fin n × d) (Fin n × d) (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun P Q => Φ (P.1.succ, P.2) (Q.1.succ, Q.2)
      have hblk : Matrix.reindex E E Φ = Matrix.fromBlocks A B C D := by
        ext (i | ⟨p, i⟩) (j | ⟨q, j⟩) <;> simp [A, B, C, D, Matrix.reindex_apply, hE, hE']
      have hc' : ∀ P Q, PowerSeries.constantCoeff (Φ P Q) = if P = Q then 1 else 0 := fun P Q => by
        have h1 := congrFun (congrFun hc P) Q
        simpa [Matrix.one_apply] using h1
      have hAc : (PowerSeries.constantCoeff).mapMatrix A = 1 := by
        ext i j
        simp [A, hc', Matrix.one_apply]
      have hAg : A ∈ goodM R' := hΦ 0 0
      haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_det_of_const A hAc)
      rw [← Matrix.det_reindex_self E Φ, hblk, Matrix.det_fromBlocks₁₁]
      apply (goodS T').mul_mem (detGood T' R' hyp hAg)
      apply ih
      · intro p q
        have hb : (Matrix.of fun i j => (D - C * ⅟A * B) (p, i) (q, j)) =
            (Matrix.of fun i j => Φ (p.succ, i) (q.succ, j)) -
              (Matrix.of fun i j => Φ (p.succ, i) (0, j)) * A⁻¹ * (Matrix.of fun i j => Φ (0, i) (q.succ, j)) := by
          ext i j
          simp [A, B, C, D, Matrix.mul_apply, Matrix.invOf_eq_nonsing_inv]
        rw [hb]
        exact (goodM R').sub_mem (hΦ p.succ q.succ)
          ((goodM R').mul_mem ((goodM R').mul_mem (hΦ p.succ 0) (invGood R' hAg hAc)) (hΦ 0 q.succ))
      · ext P Q
        simp [A, B, C, D, Matrix.mul_apply, hc', Matrix.one_apply, Matrix.invOf_eq_nonsing_inv, Fin.succ_ne_zero]
        all_goals simp only [← Prod.ext_iff]
  intro _ Φ hΦ hc
  let e := Fintype.equivFin g
  let E : g × d ≃ Fin (Fintype.card g) × d := e.prodCongr (Equiv.refl d)
  have h := hFin (Fintype.card g) (Matrix.reindex E E Φ) ?_ ?_
  · rwa [Matrix.det_reindex_self] at h
  · intro p q
    have hb : (Matrix.of fun i j => Matrix.reindex E E Φ (p, i) (q, j)) =
        Matrix.of fun i j => Φ (e.symm p, i) (e.symm q, j) := by
      ext i j
      simp [E]
    rw [hb]
    exact hΦ _ _
  · rw [show (PowerSeries.constantCoeff).mapMatrix (Matrix.reindex E E Φ) =
        Matrix.reindex E E ((PowerSeries.constantCoeff).mapMatrix Φ) from rfl, hc, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
end Schur

section Final
variable {d : Type} [Fintype d] [DecidableEq d]

def phiMat (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') : Matrix (g × d) (g × d) (PowerSeries (X' → FractionRing O)) :=
  1 - (PowerSeries.X : PowerSeries (X' → FractionRing O)) •
    Matrix.of fun P Q => PowerSeries.C (fun x' => (Θ P.1 Q.1 : X' → Matrix d d (FractionRing O)) x' P.2 Q.2)

/- English proof (translation)
Establish `hX : ∀ (c : X' → FractionRing O) (k : ℕ), PowerSeries.coeff k (PowerSeries.X * PowerSeries.C c) = if k = 1 then c else 0`. Introduce `c k`. Rewrite using `[mul_comm, ← pow_one (PowerSeries.X : PowerSeries (X' → FractionRing O)), PowerSeries.coeff_C_mul_X_pow]`. Use extensionality with `x' i j`. Simplify using `only [coefMat, phiMat, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, hX, Matrix.one_apply, Prod.mk.injEq]`.

Apply the tactic sequence `by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;> by_cases hpq : p = q <;> by_cases hij : i = j <;>`. Apply the tactic sequence `simp [hn0, hn1, hpq, hij, PowerSeries.coeff_one, Matrix.one_apply] <;> omega`.
-/
lemma phiMat_block (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) (n : ℕ) :
    coefMat n (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) =
      (if n = 0 ∧ p = q then 1 else 0) -
        (if n = 1 then (Θ p q : X' → Matrix d d (FractionRing O)) else 0) := by
  have hX : ∀ (c : X' → FractionRing O) (k : ℕ),
      PowerSeries.coeff k (PowerSeries.X * PowerSeries.C c) = if k = 1 then c else 0 := by
    intro c k
    rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries (X' → FractionRing O)), PowerSeries.coeff_C_mul_X_pow]
  ext x' i j
  simp only [coefMat, phiMat, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, hX,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;> by_cases hpq : p = q <;> by_cases hij : i = j <;>
    simp [hn0, hn1, hpq, hij, PowerSeries.coeff_one, Matrix.one_apply] <;> omega

/- English proof (translation)
Use `show ∀ n, coefMat n _ ∈ R'`. Introduce `n`. Rewrite using `[phiMat_block]`. Apply `Subalgebra.sub_mem` to reduce the goal to its premises. Use `split_ifs`.

Conclude with `Subalgebra.one_mem _`. Conclude with `Subalgebra.zero_mem _`. Use `split_ifs`. Conclude with `(Θ p q).2`. Conclude with `Subalgebra.zero_mem _`.
-/
lemma phiMat_good (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) :
    (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) ∈ goodM R' := by
  show ∀ n, coefMat n _ ∈ R'
  intro n
  rw [phiMat_block]
  apply Subalgebra.sub_mem
  · split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  · split_ifs
    · exact (Θ p q).2
    · exact Subalgebra.zero_mem _

/- English proof (translation)
Use extensionality with `P Q`. Simplify using `[phiMat, Matrix.one_apply]`.
-/
lemma phiMat_const (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') :
    (PowerSeries.constantCoeff).mapMatrix (phiMat R' Θ) = 1 := by
  ext P Q
  simp [phiMat, Matrix.one_apply]

/- English proof (translation)
Establish `hL : PowerSeries.coeff (Fintype.card (g × d)) (phiMat R' Θ).det x' = PowerSeries.coeff (Fintype.card (g × d)) ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ)).det`. Rewrite using `[← RingHom.map_det, PowerSeries.coeff_map]`. Both sides reduce to the same expression. Establish `hM : (PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ) = (Polynomial.coeToPowerSeries.ringHom).mapMatrix (1 - (Polynomial.X : Polynomial (FractionRing O)) • (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynom …`. Use extensionality with `P Q`.

Apply the tactic sequence `by_cases hPQ : P = Q <;>`. Apply the tactic sequence `simp [phiMat, bigMat, Matrix.one_apply, hPQ, Polynomial.coe_X, Polynomial.coe_C] <;> ring`. Rewrite using `[hL, hM, ← RingHom.map_det]`. Rewrite using `[show (Polynomial.coeToPowerSeries.ringHom : Polynomial (FractionRing O) →+* PowerSeries (FractionRing O)) (Matrix.det (1 - (Polynomial.X : Polynomial (FractionRing O)) • (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynomial.C)) = (((bigMat (fun r : …`. Rewrite using `[Polynomial.coeff_coe, ← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Polynomial.revAt_le (le_refl _), Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff]`.
-/
lemma phiMat_eval [IsDomain O] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type}
    [Fintype g] [DecidableEq g] (Θ : Matrix g g R') (x' : X') :
    (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det =
      (-1) ^ Fintype.card (g × d) *
        PowerSeries.coeff (Fintype.card (g × d)) (phiMat R' Θ).det x' := by
  classical
  have hL : PowerSeries.coeff (Fintype.card (g × d)) (phiMat R' Θ).det x' =
      PowerSeries.coeff (Fintype.card (g × d))
        ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ)).det := by
    rw [← RingHom.map_det, PowerSeries.coeff_map]
    rfl
  have hM : (PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ) =
      (Polynomial.coeToPowerSeries.ringHom).mapMatrix
        (1 - (Polynomial.X : Polynomial (FractionRing O)) •
          (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynomial.C) := by
    ext P Q
    by_cases hPQ : P = Q <;>
      simp [phiMat, bigMat, Matrix.one_apply, hPQ, Polynomial.coe_X, Polynomial.coe_C] <;> ring
  rw [hL, hM, ← RingHom.map_det]
  rw [show (Polynomial.coeToPowerSeries.ringHom : Polynomial (FractionRing O) →+* PowerSeries (FractionRing O))
      (Matrix.det (1 - (Polynomial.X : Polynomial (FractionRing O)) •
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynomial.C)) =
      (((bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).charpolyRev :
        Polynomial (FractionRing O)) : PowerSeries (FractionRing O)) from rfl]
  rw [Polynomial.coeff_coe, ← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le (le_refl _), Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff]

end Final

end BlockDetAlt

open BlockDetAlt in
/- English proof (translation)
Introduce `O _ _ X' T' d _ _ R' hyp g _ _ Θ`. Establish `hS` using `schur T' R' hyp g (phiMat R' Θ) (fun p q => phiMat_good R' Θ p q) (phiMat_const R' Θ)`. Take `⟨f, hf, hfx⟩` from `mem_Fr.1 (hS (Fintype.card (g × d)))`. Use `⟨(-1) ^ Fintype.card (g × d) * f, T'.mul_mem (T'.pow_mem (T'.neg_mem T'.one_mem) _) hf, fun x' => ?_⟩` and prove the remaining obligations. Rewrite using `[phiMat_eval R' Θ x', ← hfx x']`.

Simplify using the standard rewrite rules.
-/
theorem blockDet : StatBlockDet := by
  intro O _ _ X' T' d _ _ R' hyp g _ _ Θ
  have hS := schur T' R' hyp g (phiMat R' Θ) (fun p q => phiMat_good R' Θ p q) (phiMat_const R' Θ)
  obtain ⟨f, hf, hfx⟩ := mem_Fr.1 (hS (Fintype.card (g × d)))
  refine ⟨(-1) ^ Fintype.card (g × d) * f, T'.mul_mem (T'.pow_mem (T'.neg_mem T'.one_mem) _) hf, fun x' => ?_⟩
  rw [phiMat_eval R' Θ x', ← hfx x']
  simp

end Formalism.NG
