import Mathlib
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSimpArgs false

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Proj

variable {K : Type} [Field K] {σ : Type}

/- English proof (translation)
Rewrite using `[fockB_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, fockB_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem fockB_comm (f g : MvPolynomial σ K) : fockB f g = fockB g f := by
  classical
  rw [fockB_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    fockB_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Rewrite using `[fockB_eq_sum _ g {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]`.
-/
theorem fockB_monomial_left (m : σ →₀ ℕ) (a : K) (g : MvPolynomial σ K) :
    fockB (monomial m a) g = a * g.coeff m * (mfact m : K) := by
  classical
  rw [fockB_eq_sum _ g {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

variable {ι : Type} [Fintype ι] {n : ℕ} (sg : ι → DomWeight n)

/- English proof (translation)
Introduce `h0`. Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Use `set x : VV K sg := ∑ i, c i • bVV K sg i with hxdef`. Establish `hxc : (x : Pol K ι n) = ∑ i, c i • bVVfun K sg i`. Simplify using `[hxdef, Submodule.coe_sum, Submodule.coe_smul, bVV_coe]`.

Use `clear_value x`. Establish `hj : ∀ j, fockB (bVVfun K sg j) (x : Pol K ι n) = 0`. Introduce `j`. Establish `e` using `congrFun hc0 j`. Rewrite using `[hxc, ← fockBL_apply, map_sum]`.

Simplify using `only [map_smul, fockBL_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hx : ∀ y : VV K sg, pairBK sg y x = 0`. Introduce `y`. Rewrite using `[← (bVV K sg).sum_repr y, map_sum, LinearMap.sum_apply]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, pairBK_apply, pairB_apply, bVV_coe, hj j]`. Simplify using the standard rewrite rules. Establish `hx0 : x = 0` using `(pairingBNondegenerate_holds K ι n sg).2 x hx`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent c (by rw [← hxdef]; exact hx0) i`.
-/
theorem gramB_det_ne [CharZero K] : (gramB (K := K) sg).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  set x : VV K sg := ∑ i, c i • bVV K sg i with hxdef
  have hxc : (x : Pol K ι n) = ∑ i, c i • bVVfun K sg i := by
    simp [hxdef, Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  clear_value x
  have hj : ∀ j, fockB (bVVfun K sg j) (x : Pol K ι n) = 0 := by
    intro j
    have e := congrFun hc0 j
    rw [hxc, ← fockBL_apply, map_sum]
    simp only [map_smul, fockBL_apply, smul_eq_mul]
    calc _ = (gramB (K := K) sg).mulVec c j := by simp [Matrix.mulVec, dotProduct, gramB, mul_comm]
      _ = 0 := by rw [e]; rfl
  have hx : ∀ y : VV K sg, pairBK sg y x = 0 := by
    intro y
    rw [← (bVV K sg).sum_repr y, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, pairBK_apply, pairB_apply, bVV_coe, hj j]
    simp
  have hx0 : x = 0 := (pairingBNondegenerate_holds K ι n sg).2 x hx
  apply hc
  funext i
  exact Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent c (by rw [← hxdef]; exact hx0) i

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramB, fockB_comm]`.
-/
theorem gramB_transpose : (gramB (K := K) sg).transpose = gramB sg := by
  ext i j
  simp [gramB, fockB_comm]

/- English proof (translation)
Simplify using `only [projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, fockBL_apply, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, smul_smul]`.
-/
theorem projVV_coe (p : Pol K ι n) :
    (projVV sg p : Pol K ι n) = ∑ i, ∑ j, ((gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) p) • bVVfun K sg i := by
  classical
  simp only [projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    fockBL_apply, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, smul_smul]

/- English proof (translation)
Establish `hG : IsUnit (gramB (K` using `K) sg).det := isUnit_iff_ne_zero.mpr (gramB_det_ne sg)`. Establish `hinv : gramB (K` using `K) sg * (gramB sg)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG`. Rewrite using `[projVV_coe, ← fockBL_apply, map_sum]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockBL_apply, smul_eq_mul]`. Establish `e : ∀ j, ∑ i, (gramB (K` using `K) sg)⁻¹ i j * fockB (bVVfun K sg j) p * fockB (bVVfun K sg i) (bVVfun K sg k) = fockB (bVVfun K sg j) p * ((gramB (K := K) sg * (gramB (K := K) sg)⁻¹ : Matrix (VVIdx sg) (VVIdx sg) K) k j) := by`.

Introduce `j`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [gramB, Matrix.of_apply]`. Rewrite using `[fockB_comm (bVVfun K sg i)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_comm]`. Simplify using `only [e, hinv, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `fockB_comm _ _`.
-/
theorem fockB_projVV_basis [CharZero K] (p : Pol K ι n) (k : VVIdx sg) :
    fockB (projVV sg p : Pol K ι n) (bVVfun K sg k) = fockB p (bVVfun K sg k) := by
  classical
  have hG : IsUnit (gramB (K := K) sg).det := isUnit_iff_ne_zero.mpr (gramB_det_ne sg)
  have hinv : gramB (K := K) sg * (gramB sg)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  rw [projVV_coe, ← fockBL_apply, map_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockBL_apply, smul_eq_mul]
  have e : ∀ j, ∑ i, (gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) p * fockB (bVVfun K sg i) (bVVfun K sg k) =
      fockB (bVVfun K sg j) p * ((gramB (K := K) sg * (gramB (K := K) sg)⁻¹ : Matrix (VVIdx sg) (VVIdx sg) K) k j) := by
    intro j
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [gramB, Matrix.of_apply]
    rw [fockB_comm (bVVfun K sg i)]
    ring
  rw [Finset.sum_comm]
  simp only [e, hinv, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact fockB_comm _ _

/- English proof (translation)
Establish `hv' : v = ∑ k, ((bVV K sg).repr ⟨v, hv⟩ k) • bVVfun K sg k`. Establish `h1` using `congrArg Subtype.val ((bVV K sg).sum_repr ⟨v, hv⟩)`. Rewrite `h1` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, bVV_coe] at h1`. Conclude with `h1.symm`.

Rewrite using `[hv']`. Simplify using `only [← fockBL_apply, map_sum, map_smul]`. Simplify using `only [fockBL_apply, fockB_projVV_basis]`.
-/
theorem fockB_projVV [CharZero K] (p : Pol K ι n) (v : Pol K ι n) (hv : v ∈ VV K sg) :
    fockB (projVV sg p : Pol K ι n) v = fockB p v := by
  classical
  have hv' : v = ∑ k, ((bVV K sg).repr ⟨v, hv⟩ k) • bVVfun K sg k := by
    have h1 := congrArg Subtype.val ((bVV K sg).sum_repr ⟨v, hv⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul, bVV_coe] at h1
    exact h1.symm
  rw [hv']
  simp only [← fockBL_apply, map_sum, map_smul]
  simp only [fockBL_apply, fockB_projVV_basis]

/- English proof (translation)
Use `set d : VV K sg := projVV sg v - ⟨v, hv⟩ with hd`. Establish `hd0 : ∀ y : VV K sg, pairBK sg y d = 0`. Introduce `y`. Rewrite using `[pairBK_apply, pairB_apply, hd, Submodule.coe_sub, ← fockBL_apply, map_sub, fockBL_apply, fockBL_apply, fockB_comm (y : Pol K ι n), fockB_comm (y : Pol K ι n), fockB_projVV sg v y y.2]`. Simplify using the standard rewrite rules.

Use `(pairingBNondegenerate_holds K ι n sg).2 d hd0` as an intermediate fact. Rewrite `this` using `[hd, sub_eq_zero]`. Conclude with `congrArg Subtype.val this`.
-/
theorem projVV_of_mem [CharZero K] (v : Pol K ι n) (hv : v ∈ VV K sg) : (projVV sg v : Pol K ι n) = v := by
  set d : VV K sg := projVV sg v - ⟨v, hv⟩ with hd
  have hd0 : ∀ y : VV K sg, pairBK sg y d = 0 := by
    intro y
    rw [pairBK_apply, pairB_apply, hd, Submodule.coe_sub, ← fockBL_apply, map_sub, fockBL_apply, fockBL_apply,
      fockB_comm (y : Pol K ι n), fockB_comm (y : Pol K ι n), fockB_projVV sg v y y.2]
    simp
  have := (pairingBNondegenerate_holds K ι n sg).2 d hd0
  rw [hd, sub_eq_zero] at this
  exact congrArg Subtype.val this

end Proj

section Adj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ}

/- English proof (translation)
Unfold `mfact`. Conclude with `Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by simp at hx; simp [hx]`.
-/
theorem mfact_eq_prod {σ : Type} [Fintype σ] (m : σ →₀ ℕ) : mfact m = ∏ x, (m x).factorial := by
  unfold mfact
  exact Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by simp at hx; simp [hx]

/- English proof (translation)
Conclude with `Fin.ext rfl`.
-/
theorem iC_eq (i : Fin n) : iC (rfl : n + 1 = n + 1) i = i.castSucc := by
  exact Fin.ext rfl

/- English proof (translation)
Conclude with `Fin.ext rfl`.
-/
theorem iL_eq : iL (rfl : n + 1 = n + 1) = Fin.last n := by
  exact Fin.ext rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem upVar_eq (v : ι × Fin n × Fin n) : upVar (rfl : n + 1 = n + 1) v = (v.1, v.2.1.castSucc, v.2.2.castSucc) := by
  rfl

/- English proof (translation)
Simplify using `only [zExp, Finsupp.finset_sum_apply, Finsupp.single_apply, iL_eq, iC_eq]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single τ]`. Rewrite using `[Finset.sum_eq_single ⟨s.val, h.2⟩]`. Simplify using `[h.1, Fin.ext_iff]`.

Introduce `s' _ hs'`. Rewrite using `[if_neg]`. Introduce `e`. Apply `hs'` to reduce the goal to its premises. Use `congrArg (fun x => x.2.2.val) e` as an intermediate fact.

Conclude with `Fin.ext (by simpa using this)`. Simplify using the standard rewrite rules. Introduce `τ' _ hτ'`. Use `Finset.sum_eq_zero fun s' _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce `e`. Conclude with `hτ' (congrArg Prod.fst e)`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun s' _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce `e`. Apply `h` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq] at e`. Use `⟨e.2.1.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.2.2]`.

Conclude with `s'.2`.
-/
theorem zExp_apply (b : ι → Fin n → ℕ) (τ : ι) (a s : Fin (n + 1)) :
    zExp (rfl : n + 1 = n + 1) b (τ, a, s) =
      if h : a = Fin.last n ∧ s.val < n then b τ ⟨s.val, h.2⟩ else 0 := by
  classical
  simp only [zExp, Finsupp.finset_sum_apply, Finsupp.single_apply, iL_eq, iC_eq]
  split_ifs with h
  · rw [Finset.sum_eq_single τ]
    · rw [Finset.sum_eq_single ⟨s.val, h.2⟩]
      · simp [h.1, Fin.ext_iff]
      · intro s' _ hs'
        rw [if_neg]
        intro e
        apply hs'
        have := congrArg (fun x => x.2.2.val) e
        exact Fin.ext (by simpa using this)
      · simp
    · intro τ' _ hτ'
      refine Finset.sum_eq_zero fun s' _ => ?_
      rw [if_neg]
      intro e
      exact hτ' (congrArg Prod.fst e)
    · simp
  · refine Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun s' _ => ?_
    rw [if_neg]
    intro e
    apply h
    simp only [Prod.mk.injEq] at e
    refine ⟨e.2.1.symm, ?_⟩
    rw [← e.2.2]
    exact s'.2

/- English proof (translation)
Conclude with `Finsupp.mapDomain_apply (upVar_inj rfl) m' (τ, a, s)`.
-/
theorem mapDomain_up_castSucc (m' : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (a s : Fin n) :
    Finsupp.mapDomain (upVar (rfl : n + 1 = n + 1)) m' (τ, a.castSucc, s.castSucc) = m' (τ, a, s) := by
  exact Finsupp.mapDomain_apply (upVar_inj rfl) m' (τ, a, s)

/- English proof (translation)
Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨v, hv⟩`. Establish `h` using `congrArg (fun p : ι × Fin (n + 1) × Fin (n + 1) => (p.2.1 : ℕ)) hv`. Simplify using `only [upVar, iC, Fin.val_last] at h`. Use `v.2.1.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem mapDomain_up_last_left (m' : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (s : Fin (n + 1)) :
    Finsupp.mapDomain (upVar (rfl : n + 1 = n + 1)) m' (τ, Fin.last n, s) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨v, hv⟩
  have h := congrArg (fun p : ι × Fin (n + 1) × Fin (n + 1) => (p.2.1 : ℕ)) hv
  simp only [upVar, iC, Fin.val_last] at h
  have := v.2.1.isLt
  omega

/- English proof (translation)
Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨v, hv⟩`. Establish `h` using `congrArg (fun p : ι × Fin (n + 1) × Fin (n + 1) => (p.2.2 : ℕ)) hv`. Simplify using `only [upVar, iC, Fin.val_last] at h`. Use `v.2.2.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem mapDomain_up_last_right (m' : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (a : Fin (n + 1)) :
    Finsupp.mapDomain (upVar (rfl : n + 1 = n + 1)) m' (τ, a, Fin.last n) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨v, hv⟩
  have h := congrArg (fun p : ι × Fin (n + 1) × Fin (n + 1) => (p.2.2 : ℕ)) hv
  simp only [upVar, iC, Fin.val_last] at h
  have := v.2.2.isLt
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use extensionality with `⟨τ, a, s⟩`. Rewrite using `[Finsupp.add_apply, zExp_apply]`. Proceed by induction on `s using Fin.lastCases with`.

Consider the case `last`. Establish `e2` using `h2 τ a`. Rewrite `e2` using `[iL_eq]`. Rewrite using `[e2, mapDomain_up_last_right]`. Simplify using the standard rewrite rules.

Consider the case `cast s`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Establish `e1` using `h1 τ s`. Rewrite `e1` using `[iL_eq, iC_eq]`.

Rewrite using `[mapDomain_up_last_left, e1]`. Simplify using the standard rewrite rules. Consider the case `cast a`. Rewrite using `[mapDomain_up_castSucc, ← h3, Finsupp.comapDomain_apply, upVar_eq]`. Establish `: ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n)` using `fun h => (Fin.castSucc_ne_last a) h.1`.

Simplify using `[this]`. Introduce `hm`. Substitute `hm` using the available equality. Use `⟨⟨fun τ s => ?_, fun τ a => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, iL_eq, iC_eq, mapDomain_up_last_left, zExp_apply]`.

Simplify using the standard rewrite rules. Rewrite using `[Finsupp.add_apply, iL_eq, mapDomain_up_last_right, zExp_apply]`. Simplify using the standard rewrite rules. Use extensionality with `⟨τ, a, s⟩`. Rewrite using `[Finsupp.comapDomain_apply, upVar_eq, Finsupp.add_apply, mapDomain_up_castSucc, zExp_apply]`.

Establish `: ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n)` using `fun h => (Fin.castSucc_ne_last a) h.1`. Simplify using `[this]`.
-/
theorem isTop_iff (b : ι → Fin n → ℕ) (m : ι × Fin (n + 1) × Fin (n + 1) →₀ ℕ) (m' : ι × Fin n × Fin n →₀ ℕ) :
    (IsTop (rfl : n + 1 = n + 1) b m ∧ m.comapDomain (upVar rfl) (upVar_inj rfl).injOn = m') ↔
      m = Finsupp.mapDomain (upVar (rfl : n + 1 = n + 1)) m' + zExp rfl b := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    ext ⟨τ, a, s⟩
    rw [Finsupp.add_apply, zExp_apply]
    induction s using Fin.lastCases with
    | last =>
      have e2 := h2 τ a
      rw [iL_eq] at e2
      rw [e2, mapDomain_up_last_right]
      simp
    | cast s =>
      induction a using Fin.lastCases with
      | last =>
        have e1 := h1 τ s
        rw [iL_eq, iC_eq] at e1
        rw [mapDomain_up_last_left, e1]
        simp
      | cast a =>
        rw [mapDomain_up_castSucc, ← h3, Finsupp.comapDomain_apply, upVar_eq]
        have : ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n) := fun h =>
          (Fin.castSucc_ne_last a) h.1
        simp [this]
  · intro hm
    subst hm
    refine ⟨⟨fun τ s => ?_, fun τ a => ?_⟩, ?_⟩
    · rw [Finsupp.add_apply, iL_eq, iC_eq, mapDomain_up_last_left, zExp_apply]
      simp
    · rw [Finsupp.add_apply, iL_eq, mapDomain_up_last_right, zExp_apply]
      simp
    · ext ⟨τ, a, s⟩
      rw [Finsupp.comapDomain_apply, upVar_eq, Finsupp.add_apply, mapDomain_up_castSucc, zExp_apply]
      have : ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n) := fun h =>
        (Fin.castSucc_ne_last a) h.1
      simp [this]

/- English proof (translation)
Rewrite using `[mfact_eq_prod, mfact_eq_prod, bFac, Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type, Fin.prod_univ_castSucc]`. Simplify using `only [Finsupp.add_apply, Fin.prod_univ_castSucc, mapDomain_up_castSucc, mapDomain_up_last_left, mapDomain_up_last_right, zExp_apply]`. Establish `h1 : ∀ a s : Fin n, ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n)` using `fun a s h => (Fin.castSucc_ne_last a) h.1`.

Simplify using `[h1, Fintype.prod_prod_type]`.
-/
theorem mfact_raise (b : ι → Fin n → ℕ) (m' : ι × Fin n × Fin n →₀ ℕ) :
    mfact (Finsupp.mapDomain (upVar (rfl : n + 1 = n + 1)) m' + zExp rfl b) = mfact m' * bFac b := by
  rw [mfact_eq_prod, mfact_eq_prod, bFac, Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [Finsupp.add_apply, Fin.prod_univ_castSucc, mapDomain_up_castSucc, mapDomain_up_last_left,
    mapDomain_up_last_right, zExp_apply]
  have h1 : ∀ a s : Fin n, ¬ (a.castSucc = Fin.last n ∧ (s.castSucc : Fin (n + 1)).val < n) := fun a s h =>
    (Fin.castSucc_ne_last a) h.1
  simp [h1, Fintype.prod_prod_type]

/- English proof (translation)
Substitute `hN` using the available equality. Establish `key : ((bFac b : K) • (fockBL (K` using `K) (σ := ι × Fin n × Fin n)).compl₁₂ (coefLast rfl b) LinearMap.id) = (fockBL (K := K) (σ := ι × Fin (n + 1) × Fin (n + 1))).compl₁₂ LinearMap.id (raise rfl b) := by`. Use `(basisMonomials _ K).ext fun m => (basisMonomials _ K).ext fun m' => ?_` and prove the remaining obligations. Establish `hb : coefLast (K` using `K) rfl b (basisMonomials (ι × Fin (n + 1) × Fin (n + 1)) K m) = if IsTop rfl b m then monomial (m.comapDomain (upVar rfl) (upVar_inj rfl).injOn) (1 : K) else 0 := by`. Rewrite using `[coefLast, Module.Basis.constr_basis]`.

Simplify using `only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, fockBL_apply, hb]`. Simplify using `only [coe_basisMonomials, raise, LinearMap.comp_apply, AlgHom.toLinearMap_apply, upperParabolic, rename_monomial, LinearMap.mulLeft_apply, monomial_mul, one_mul, smul_eq_mul]`. Rewrite using `[fockB_monomial_left, coeff_monomial]`. Distinguish the cases in `ht : IsTop rfl b m`. Rewrite using `[if_pos ht, fockB_monomial_left, coeff_monomial]`.

Distinguish the cases in `hc : m' = m.comapDomain (upVar rfl) (upVar_inj rfl).injOn`. Establish `hm` using `(isTop_iff b m m').1 ⟨ht, hc.symm⟩`. Rewrite using `[if_pos hc, if_pos (by rw [hm]; exact add_comm _ _)]`. Rewrite using `[← hc, hm, mfact_raise]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, if_neg]`. Simplify using the standard rewrite rules. Introduce `e`. Conclude with `hc ((isTop_iff b m m').2 (by rw [← e]; exact add_comm _ _) |>.2).symm`.

Rewrite using `[if_neg ht]`. Rewrite using `[if_neg]`. Simplify using `[fockB]`. Introduce `e`. Conclude with `ht ((isTop_iff b m m').2 (by rw [← e]; exact add_comm _ _)).1`.

Use `congrArg (fun B => B f g) key` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, fockBL_apply, smul_eq_mul] at this`. Rewrite using `[mul_comm]`. Conclude with `this`.
-/
theorem fockB_coefLast (hN : N = n + 1) (b : ι → Fin n → ℕ) (f : Pol K ι N) (g : Pol K ι n) :
    fockB (coefLast hN b f) g * (bFac b : K) = fockB f (raise hN b g) := by
  classical
  subst hN
  have key : ((bFac b : K) • (fockBL (K := K) (σ := ι × Fin n × Fin n)).compl₁₂ (coefLast rfl b) LinearMap.id) =
      (fockBL (K := K) (σ := ι × Fin (n + 1) × Fin (n + 1))).compl₁₂ LinearMap.id (raise rfl b) := by
    refine (basisMonomials _ K).ext fun m => (basisMonomials _ K).ext fun m' => ?_
    have hb : coefLast (K := K) rfl b (basisMonomials (ι × Fin (n + 1) × Fin (n + 1)) K m) =
        if IsTop rfl b m then monomial (m.comapDomain (upVar rfl) (upVar_inj rfl).injOn) (1 : K) else 0 := by
      rw [coefLast, Module.Basis.constr_basis]
    simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, fockBL_apply, hb]
    simp only [coe_basisMonomials, raise, LinearMap.comp_apply, AlgHom.toLinearMap_apply, upperParabolic, rename_monomial,
      LinearMap.mulLeft_apply, monomial_mul, one_mul, smul_eq_mul]
    rw [fockB_monomial_left, coeff_monomial]
    by_cases ht : IsTop rfl b m
    · rw [if_pos ht, fockB_monomial_left, coeff_monomial]
      by_cases hc : m' = m.comapDomain (upVar rfl) (upVar_inj rfl).injOn
      · have hm := (isTop_iff b m m').1 ⟨ht, hc.symm⟩
        rw [if_pos hc, if_pos (by rw [hm]; exact add_comm _ _)]
        rw [← hc, hm, mfact_raise]
        push_cast
        ring
      · rw [if_neg hc, if_neg]
        · simp
        · intro e
          exact hc ((isTop_iff b m m').2 (by rw [← e]; exact add_comm _ _) |>.2).symm
    · rw [if_neg ht]
      rw [if_neg]
      · simp [fockB]
      · intro e
        exact ht ((isTop_iff b m m').2 (by rw [← e]; exact add_comm _ _)).1
  have := congrArg (fun B => B f g) key
  simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, fockBL_apply, smul_eq_mul] at this
  rw [mul_comm]
  exact this

end Adj

section Transpose

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Rewrite using `[fockB_eq_sum (c • f) g f.support support_smul, fockB, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockB_smul_left' {σ : Type} (c : K) (f g : MvPolynomial σ K) : fockB (c • f) g = c * fockB f g := by
  rw [fockB_eq_sum (c • f) g f.support support_smul, fockB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `only [fockB, coeff_smul, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem fockB_smul_right' {σ : Type} (c : K) (f g : MvPolynomial σ K) : fockB f (c • g) = c * fockB f g := by
  simp only [fockB, coeff_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Rewrite using `[ioConst, bFac, Nat.cast_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hB : ((∏ s, (bExp hN lam sg τ s).factorial : ℕ) : K) ≠ 0`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)` after adjusting the coercions. Rewrite using `[div_mul_eq_div_div, div_mul_cancel₀ _ hB]`.
-/
theorem ioConst_mul_bFac : ioConst hN K lam sg * (bFac (bExp hN lam sg) : K) =
    ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : K) * fockB (xiBr K hN (lam τ) (sg τ)) (xiBr K hN (lam τ) (sg τ)) /
      fockB (extremal K n (sg τ)) (extremal K n (sg τ)) := by
  rw [ioConst, bFac, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hB : ((∏ s, (bExp hN lam sg τ s).factorial : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)
  rw [div_mul_eq_div_div, div_mul_cancel₀ _ hB]

/- English proof (translation)
Introduce `f g`. Rewrite using `[pairBK_apply, pairBK_apply, pairB_apply, pairB_apply]`. Establish `h1 : ((brStd hN lam sg f : VV K sg) : Pol K ι n) = brConst hN K lam sg • (projVV sg (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) : Pol K ι n)`. Simplify using `[brStd, brStdP]`. Establish `h2 : ((ioStd hN lam sg g : VV K lam) : Pol K ι N) = ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (g : Pol K ι n)) : Pol K ι N)`.

Simplify using `[ioStd]`. Rewrite using `[h1, h2, fockB_smul_left', fockB_smul_right', fockB_projVV sg _ _ g.2, fockB_comm (f : Pol K ι N), fockB_projVV lam _ _ f.2, fockB_comm _ (f : Pol K ι N), ← fockB_coefLast hN (bExp hN lam sg)]`. Establish `hc : (extNormB K sg)⁻¹ * brConst hN K lam sg = (extNormB K lam)⁻¹ * (ioConst hN K lam sg * (bFac (bExp hN lam sg) : K))`. Rewrite using `[ioConst_mul_bFac]`. Simplify using `only [extNormB, brConst, kapBr, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(fockB (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) (g : Pol K ι n)) * hc`.
-/
theorem brTranspose : BrTranspose hN lam sg K := by
  intro f g
  rw [pairBK_apply, pairBK_apply, pairB_apply, pairB_apply]
  have h1 : ((brStd hN lam sg f : VV K sg) : Pol K ι n) =
      brConst hN K lam sg • (projVV sg (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) : Pol K ι n) := by
    simp [brStd, brStdP]
  have h2 : ((ioStd hN lam sg g : VV K lam) : Pol K ι N) =
      ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (g : Pol K ι n)) : Pol K ι N) := by
    simp [ioStd]
  rw [h1, h2, fockB_smul_left', fockB_smul_right', fockB_projVV sg _ _ g.2, fockB_comm (f : Pol K ι N),
    fockB_projVV lam _ _ f.2, fockB_comm _ (f : Pol K ι N), ← fockB_coefLast hN (bExp hN lam sg)]
  have hc : (extNormB K sg)⁻¹ * brConst hN K lam sg =
      (extNormB K lam)⁻¹ * (ioConst hN K lam sg * (bFac (bExp hN lam sg) : K)) := by
    rw [ioConst_mul_bFac]
    simp only [extNormB, brConst, kapBr, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    ring
  linear_combination (fockB (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) (g : Pol K ι n)) * hc

/- English proof (translation)
Simplify using `only [brAt, ioAt, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[brTranspose hN lam sg f g]`.
-/
theorem brAtTranspose (t : ι → K) (f : VV K lam) (g : VV K sg) :
    pairBK sg (brAt hN lam sg t f) g = pairBK lam f (ioAt hN lam sg t g) := by
  simp only [brAt, ioAt, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [brTranspose hN lam sg f g]

end Transpose

section Period

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

/- English proof (translation)
Simplify using `only [PtilFF, periodK, GSD.csOf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.proj_apply, lowerK, LinearMap.compLeft_apply, Function.comp_apply]`.
-/
theorem PtilFF_eq (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (u : Pr.Word)
    (ψ : RowPt Pr R sel mu → VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → VV X.K W.sgTrue) :
    PtilFF W Ch sel mu P h u ψ F = periodK W Ch sel mu P h (lowerK W sel mu u ψ) F := by
  simp only [PtilFF, periodK, GSD.csOf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, lowerK, LinearMap.compLeft_apply, Function.comp_apply]

/- English proof (translation)
Conclude with `PtilFF_eq W Ch sel mu P h u (evzC W Ch sel mu u ψ) ((MtildeV W Ch sel mu P).subtype F)`.
-/
theorem PtilC_eq (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (u : Pr.Word)
    (ψ : ColV W Ch u R.m) (F : MtildeV W Ch sel mu P) :
    PtilC W Ch sel mu P h u ψ F =
      periodK W Ch sel mu P h (lowerK W sel mu u (evzC W Ch sel mu u ψ))
        (show RowPt Pr R sel mu → VV X.K W.sgTrue from (MtildeV W Ch sel mu P).subtype F) := by
  exact PtilFF_eq W Ch sel mu P h u (evzC W Ch sel mu u ψ) ((MtildeV W Ch sel mu P).subtype F)

end Period

section Chi

variable {G : Type} [CommGroup G]

/- English proof (translation)
Establish `hz : ∀ (k : ℤ) (y : G), (chi ^ k) y = chi y ^ k` using `fun k y => rfl`. Unfold `chiScalar`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hz, zpow_neg, zpow_neg]`. Generalize the expression as in `chi x ^ (((N' / 2 : ℕ) : ℤ)) = c`. Generalize the expression as in `chi x' ^ (((N / 2 : ℕ) : ℤ)) = d`.

Generalize the expression as in `mt x = a`. Generalize the expression as in `mt x' = b`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem chiScalar_eq (mt chi : G →* ℂˣ) (N N' : ℕ) (x x' : G) : chiScalar mt chi N N' x x' = (mt x)⁻¹ * mt x' := by
  have hz : ∀ (k : ℤ) (y : G), (chi ^ k) y = chi y ^ k := fun k y => rfl
  unfold chiScalar
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hz, zpow_neg, zpow_neg]
  generalize chi x ^ (((N' / 2 : ℕ) : ℤ)) = c
  generalize chi x' ^ (((N / 2 : ℕ) : ℤ)) = d
  generalize mt x = a
  generalize mt x' = b
  calc a⁻¹ * c⁻¹ * (b * d) * (c * d⁻¹) = (a⁻¹ * b) * (c⁻¹ * c) * (d * d⁻¹) := by ac_rfl
    _ = a⁻¹ * b := by rw [inv_mul_cancel, mul_inv_cancel, mul_one, mul_one]

/- English proof (translation)
The claim follows from `chiScalar_eq m1 D.chiD N N' x x'`.
-/
theorem rhoA_chi (D : Formalism.BasicNotions.D7) (m1 : D.Dt →* ℂˣ) (N N' : ℕ) (x x' : D.Dt) :
    Formalism.MainNotions.GL3Columns.rhoA D m1 N' x * Formalism.MainNotions.GL3Columns.rhoA' D m1 N x' *
              (D.chiD x ^ (((N' / 2 : ℕ) : ℤ)) * D.chiD x' ^ (-((N / 2 : ℕ) : ℤ))) = (m1 x)⁻¹ * m1 x' :=
  chiScalar_eq m1 D.chiD N N' x x'

end Chi

end Formalism.L2.Ker

open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Fock

variable {K : Type} [Field K] {σ : Type}

/- English proof (translation)
Rewrite using `[fockB_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, fockB_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem lb_fockB_symm (f g : MvPolynomial σ K) : fockB f g = fockB g f := by
  classical
  rw [fockB_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    fockB_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Rewrite using `[fockB_eq_sum (map j f) (map j g) f.support (support_map_subset j f), fockB, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `[coeff_map, map_mul, map_natCast]`.
-/
theorem lb_fockB_map {K' : Type} [Field K'] (j : K →+* K') (f g : MvPolynomial σ K) :
    fockB (map j f) (map j g) = j (fockB f g) := by
  classical
  rw [fockB_eq_sum (map j f) (map j g) f.support (support_map_subset j f), fockB, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map, map_mul, map_natCast]

/- English proof (translation)
Rewrite using `[← fockBL_apply, map_zero]`.
-/
theorem lb_fockB_zero_right (f : MvPolynomial σ K) : fockB f 0 = 0 := by
  rw [← fockBL_apply, map_zero]

/- English proof (translation)
Simplify using `only [← fockBL_apply, map_add]`.
-/
theorem lb_fockB_add_right (f g g' : MvPolynomial σ K) : fockB f (g + g') = fockB f g + fockB f g' := by
  simp only [← fockBL_apply, map_add]

/- English proof (translation)
Simplify using `only [← fockBL_apply, map_smul, smul_eq_mul]`.
-/
theorem lb_fockB_smul_right (f g : MvPolynomial σ K) (c : K) : fockB f (c • g) = c * fockB f g := by
  simp only [← fockBL_apply, map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [← fockBL_apply, map_sub, LinearMap.sub_apply]`.
-/
theorem lb_fockB_sub_left (f f' g : MvPolynomial σ K) : fockB (f - f') g = fockB f g - fockB f' g := by
  simp only [← fockBL_apply, map_sub, LinearMap.sub_apply]

end Fock

section Proj

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

/- English proof (translation)
Establish `hnd` using `Formalism.L2.DIV.pairingBNondegenerate_holds K ι n lam`. Establish `h1 : (⟨x, hx⟩ : VV K lam) = 0`. Apply `hnd.1` to reduce the goal to its premises. Introduce `y`. Rewrite using `[pairBK_apply, pairB_apply, h y.1 y.2, mul_zero]`.

Conclude with `congrArg Subtype.val h1`.
-/
theorem lb_sep (x : Pol K ι n) (hx : x ∈ VV K lam) (h : ∀ y ∈ VV K lam, fockB x y = 0) : x = 0 := by
  have hnd := Formalism.L2.DIV.pairingBNondegenerate_holds K ι n lam
  have h1 : (⟨x, hx⟩ : VV K lam) = 0 := by
    apply hnd.1
    intro y
    rw [pairBK_apply, pairB_apply, h y.1 y.2, mul_zero]
  exact congrArg Subtype.val h1

/- English proof (translation)
Introduce `v hv`. Rewrite `hv` using `[← (bVVfun_spec K lam).2]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`.

Conclude with `h k`. Consider the case `zero => exact lb_fockB_zero_right x`. Consider the case `add y y' _ _ h1 h2 => rw [lb_fockB_add_right, h1, h2, add_zero]`. Consider the case `smul c y _ h1 => rw [lb_fockB_smul_right, h1, mul_zero]`.
-/
theorem lb_orth_of_basis (x : Pol K ι n) (h : ∀ k, fockB x (bVVfun K lam k) = 0) : ∀ v ∈ VV K lam, fockB x v = 0 := by
  intro v hv
  rw [← (bVVfun_spec K lam).2] at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact h k
  | zero => exact lb_fockB_zero_right x
  | add y y' _ _ h1 h2 => rw [lb_fockB_add_right, h1, h2, add_zero]
  | smul c y _ h1 => rw [lb_fockB_smul_right, h1, mul_zero]

open Classical in
/- English proof (translation)
Introduce `h0`. Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Use `set x : Pol K ι n := ∑ i, c i • bVVfun K lam i with hxdef`. Establish `hx : x ∈ VV K lam`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Rewrite using `[← bVV_coe]`. Conclude with `(bVV K lam i).2`. Establish `horth : ∀ k, fockB x (bVVfun K lam k) = 0`. Introduce `k`. Rewrite using `[lb_fockB_symm, hxdef]`.

Establish `e : fockB (bVVfun K lam k) (∑ i, c i • bVVfun K lam i) = (gramB (K` using `K) lam *ᵥ c) k := by`. Rewrite using `[← fockBL_apply, map_sum]`. Simplify using `only [map_smul, fockBL_apply, smul_eq_mul, Matrix.mulVec, dotProduct, gramB, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e, hc0]`.

Both sides reduce to the same expression. Establish `hx0` using `lb_sep lam x hx (lb_orth_of_basis lam x horth)`. Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 c (by rw [← hxdef]; exact hx0) i`.
-/
theorem lb_gram_det_ne : (gramB (K := K) lam).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  set x : Pol K ι n := ∑ i, c i • bVVfun K lam i with hxdef
  have hx : x ∈ VV K lam := by
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← bVV_coe]; exact (bVV K lam i).2
  have horth : ∀ k, fockB x (bVVfun K lam k) = 0 := by
    intro k
    rw [lb_fockB_symm, hxdef]
    have e : fockB (bVVfun K lam k) (∑ i, c i • bVVfun K lam i) = (gramB (K := K) lam *ᵥ c) k := by
      rw [← fockBL_apply, map_sum]
      simp only [map_smul, fockBL_apply, smul_eq_mul, Matrix.mulVec, dotProduct, gramB, Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hc0]; rfl
  have hx0 := lb_sep lam x hx (lb_orth_of_basis lam x horth)
  apply hc
  funext i
  exact Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 c (by rw [← hxdef]; exact hx0) i

open Classical in

/- English proof (translation)
Establish `hG : IsUnit (gramB (K` using `K) lam).det := isUnit_iff_ne_zero.mpr (lb_gram_det_ne lam)`. Establish `hsym : (gramB (K` using `K) lam)ᵀ = gramB (K := K) lam := by`. Use extensionality with `i j`. Simplify using `[gramB, lb_fockB_symm]`. Establish `hinv : ∀ j k, ∑ i, (gramB (K` using `K) lam)⁻¹ i j * fockB (bVVfun K lam i) (bVVfun K lam k) = if j = k then 1 else 0 := by`.

Introduce `j k`. Establish `e` using `congrFun (congrFun (Matrix.nonsing_inv_mul _ hG) j) k`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `h1 : (gramB (K` using `K) lam)⁻¹ i j = (gramB (K := K) lam)⁻¹ j i := by`. Use `congrFun (congrFun (Matrix.transpose_nonsing_inv (gramB (K := K) lam)) j) i` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_apply, hsym]`. Conclude with `this`. Rewrite using `[h1]`.

Both sides reduce to the same expression. Establish `hp : ((projVV lam p : VV K lam) : Pol K ι n) = ∑ i, ∑ j, ((gramB (K` using `K) lam)⁻¹ i j * fockB (bVVfun K lam j) p) • bVVfun K lam i := by`. Rewrite using `[projVV]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, fockBL_apply, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, smul_smul]`. Apply `lb_orth_of_basis lam` to reduce the goal to its premises.

Consider the case `> fun H => by`. Introduce `v hv`. Use `H (((projVV lam p : VV K lam) : Pol K ι n) - p) ?_ v hv` as an intermediate fact. Rewrite `this` using `[lb_fockB_sub_left, sub_eq_zero]`. Then use the resulting hypothesis. Introduce `k`.

Rewrite using `[lb_fockB_sub_left, hp, sub_eq_zero]`. Rewrite using `[lb_fockB_symm, ← fockBL_apply, map_sum]`. Simplify using `only [map_sum, map_smul, fockBL_apply, smul_eq_mul]`. Establish `e : ∀ i j, (gramB (K` using `K) lam)⁻¹ i j * fockB (bVVfun K lam j) p * fockB (bVVfun K lam k) (bVVfun K lam i) = fockB (bVVfun K lam j) p * ((gramB (K := K) lam)⁻¹ i j * fockB (bVVfun K lam i) (bVVfun K lam k)) := by`. Introduce `i j`.

Rewrite using `[lb_fockB_symm (bVVfun K lam k)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Conclude with `lb_fockB_symm _ _`.
-/
theorem lb_proj_spec (p : Pol K ι n) : ∀ v ∈ VV K lam, fockB ((projVV lam p : VV K lam) : Pol K ι n) v = fockB p v := by
  have hG : IsUnit (gramB (K := K) lam).det := isUnit_iff_ne_zero.mpr (lb_gram_det_ne lam)
  have hsym : (gramB (K := K) lam)ᵀ = gramB (K := K) lam := by
    ext i j; simp [gramB, lb_fockB_symm]
  have hinv : ∀ j k, ∑ i, (gramB (K := K) lam)⁻¹ i j * fockB (bVVfun K lam i) (bVVfun K lam k) = if j = k then 1 else 0 := by
    intro j k
    have e := congrFun (congrFun (Matrix.nonsing_inv_mul _ hG) j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (gramB (K := K) lam)⁻¹ i j = (gramB (K := K) lam)⁻¹ j i := by
      have := congrFun (congrFun (Matrix.transpose_nonsing_inv (gramB (K := K) lam)) j) i
      rw [Matrix.transpose_apply, hsym] at this
      exact this
    rw [h1]; rfl
  have hp : ((projVV lam p : VV K lam) : Pol K ι n) =
      ∑ i, ∑ j, ((gramB (K := K) lam)⁻¹ i j * fockB (bVVfun K lam j) p) • bVVfun K lam i := by
    rw [projVV]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      fockBL_apply, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, smul_smul]
  apply lb_orth_of_basis lam
  |> fun H => by
    intro v hv
    have := H (((projVV lam p : VV K lam) : Pol K ι n) - p) ?_ v hv
    · rwa [lb_fockB_sub_left, sub_eq_zero] at this
    · intro k
      rw [lb_fockB_sub_left, hp, sub_eq_zero]
      rw [lb_fockB_symm, ← fockBL_apply, map_sum]
      simp only [map_sum, map_smul, fockBL_apply, smul_eq_mul]
      have e : ∀ i j, (gramB (K := K) lam)⁻¹ i j * fockB (bVVfun K lam j) p * fockB (bVVfun K lam k) (bVVfun K lam i) =
          fockB (bVVfun K lam j) p * ((gramB (K := K) lam)⁻¹ i j * fockB (bVVfun K lam i) (bVVfun K lam k)) := by
        intro i j; rw [lb_fockB_symm (bVVfun K lam k)]; ring
      simp only [e]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact lb_fockB_symm _ _

/- English proof (translation)
Establish `hx : ((projVV lam p : VV K lam) : Pol K ι n) - y ∈ VV K lam` using `Submodule.sub_mem _ (projVV lam p).2 hy`. Use `lb_sep lam _ hx fun v hv => by rw [lb_fockB_sub_left, lb_proj_spec lam p v hv, h v hv, sub_self]` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem lb_proj_unique (p y : Pol K ι n) (hy : y ∈ VV K lam) (h : ∀ v ∈ VV K lam, fockB y v = fockB p v) :
    ((projVV lam p : VV K lam) : Pol K ι n) = y := by
  have hx : ((projVV lam p : VV K lam) : Pol K ι n) - y ∈ VV K lam := Submodule.sub_mem _ (projVV lam p).2 hy
  have := lb_sep lam _ hx fun v hv => by rw [lb_fockB_sub_left, lb_proj_spec lam p v hv, h v hv, sub_self]
  exact sub_eq_zero.mp this

end Proj

section BCMaps

variable {K K' : Type} [Field K] [Field K'] (j : K →+* K')

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem lb_map_lpMinor {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map j (Formalism.GradedWeylDivisibility.lpMinor K s hr hn) = Formalism.GradedWeylDivisibility.lpMinor K' s hr hn := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

/- English proof (translation)
Unfold `extremal Formalism.GradedWeylDivisibility.hw`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, lb_map_lpMinor]`.
-/
theorem lb_map_extremal {N : ℕ} (lam : DomWeight N) : map j (extremal K N lam) = extremal K' N lam := by
  unfold extremal Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, lb_map_lpMinor]

/- English proof (translation)
Unfold `xiBr zMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, lb_map_lpMinor, fk_map_initMinor]`.
-/
theorem lb_map_xiBr {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n) :
    map j (xiBr K hN l s) = xiBr K' hN l s := by
  unfold xiBr zMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, lb_map_lpMinor, fk_map_initMinor]

/- English proof (translation)
Unfold `kapBr`. Rewrite using `[map_div₀, ← lb_fockB_map, ← lb_fockB_map, lb_map_xiBr, lb_map_extremal]`.
-/
theorem lb_map_kapBr {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n) :
    j (kapBr K hN l s) = kapBr K' hN l s := by
  unfold kapBr
  rw [map_div₀, ← lb_fockB_map, ← lb_fockB_map, lb_map_xiBr, lb_map_extremal]

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Unfold `brConst`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, lb_map_kapBr]`.
-/
theorem lb_map_brConst {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) :
    j (brConst hN K lam sg) = brConst hN K' lam sg := by
  unfold brConst
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_intCast, lb_map_kapBr]

open Classical in
/- English proof (translation)
Establish `e : (monomial m a : Pol K ι N) = a • (basisMonomials (ι × Fin N × Fin N) K) m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, coefLast, Module.Basis.constr_basis]`.
-/
theorem lb_coefLast_monomial {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ) (m : ι × Fin N × Fin N →₀ ℕ) (a : K) :
    coefLast hN b (monomial m a) =
      a • (if IsTop hN b m then monomial (m.comapDomain (upVar hN) (upVar_inj hN).injOn) (1 : K) else 0) := by
  have e : (monomial m a : Pol K ι N) = a • (basisMonomials (ι × Fin N × Fin N) K) m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, coefLast, Module.Basis.constr_basis]

open Classical in
/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m a`. Rewrite using `[map_monomial, lb_coefLast_monomial, lb_coefLast_monomial, bc_map_smul]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]`.
-/
theorem lb_map_coefLast {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ) (f : Pol K ι N) :
    map j (coefLast hN b f) = coefLast hN b (map j f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [map_monomial, lb_coefLast_monomial, lb_coefLast_monomial, bc_map_smul]
    split_ifs <;> simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]

/- English proof (translation)
Use `symm`. Apply `lb_proj_unique (K := K') lam (map j p) _ (((baseChangeSpace_holds K K' j ι n lam).1 _).1 (projVV lam p).2)` to reduce the goal to its premises. Introduce `v hv`. Rewrite `hv` using `[← (baseChangeSpace_holds K K' j ι n lam).2]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `hy`. Rewrite using `[lb_fockB_map, lb_fockB_map, lb_proj_spec lam p w hw]`. Consider the case `zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]`. Consider the case `add y y' _ _ h1 h2 => rw [lb_fockB_add_right, lb_fockB_add_right, h1, h2]`.

Consider the case `smul c y _ h1 => rw [lb_fockB_smul_right, lb_fockB_smul_right, h1]`.
-/
theorem lb_map_projVV [CharZero K] [CharZero K'] {n : ℕ} (lam : ι → DomWeight n) (p : Pol K ι n) :
    map j ((projVV lam p : VV K lam) : Pol K ι n) = ((projVV lam (map j p) : VV K' lam) : Pol K' ι n) := by
  symm
  apply lb_proj_unique (K := K') lam (map j p) _ (((baseChangeSpace_holds K K' j ι n lam).1 _).1 (projVV lam p).2)
  intro v hv
  rw [← (baseChangeSpace_holds K K' j ι n lam).2] at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [lb_fockB_map, lb_fockB_map, lb_proj_spec lam p w hw]
  | zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]
  | add y y' _ _ h1 h2 => rw [lb_fockB_add_right, lb_fockB_add_right, h1, h2]
  | smul c y _ h1 => rw [lb_fockB_smul_right, lb_fockB_smul_right, h1]

/- English proof (translation)
Introduce `t x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [bcVV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, brAt, brStd, brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul, bc_map_smul]`. Rewrite using `[lb_map_projVV, lb_map_coefLast, lb_map_brConst, map_prod]`. Simplify using `only [map_zpow₀]`.
-/
theorem branching_map_rational [CharZero K] [CharZero K'] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N)
    (sg : ι → DomWeight n) : BrAtMap j hN lam sg := by
  intro t x
  apply Subtype.ext
  simp only [bcVV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, brAt, brStd, brStdP, LinearMap.smul_apply,
    LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul, bc_map_smul]
  rw [lb_map_projVV, lb_map_coefLast, lb_map_brConst, map_prod]
  simp only [map_zpow₀]

end BCMaps

section Member

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

/- English proof (translation)
The claim follows from `branching_map_rational s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue _ x`.
-/
theorem brC_map (s : X.K →+* ℂ) (u : Pr.Word) (x : VV X.K (W.lamTrue u R.m)) :
    brAt (N_m_succ R) (W.lamTrue u R.m) W.sgTrue (fun τ => s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))))
        (bcVV s (W.lamTrue u R.m) x) = bcVV s W.sgTrue (brC W u x) :=
  branching_map_rational s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue _ x

/- English proof (translation)
Use function extensionality and compare the values at `d`. Conclude with `branching_map_rational j hN lam sg t (ψ d)`.
-/
theorem lowerFn_map {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] (j : K →+* K') {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (Pt : Type) (t : ι → K) (ψ : Pt → VV K lam) :
    lowerFn hN lam sg Pt (fun τ => j (t τ)) (fun d => bcVV j lam (ψ d)) = fun d => bcVV j sg (lowerFn hN lam sg Pt t ψ d) := by
  funext d
  exact branching_map_rational j hN lam sg t (ψ d)

end Member

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Shift

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `ht` using `R.rank_add_five_le`. Establish `hN : R.N R.m = R.k + R.m * (R.t + 1)` using `rfl`. Establish `hmt : 2 * 2 ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul hm (by omega)`.

Establish `h1 : ¬ R.N R.m - 1 < R.k` using `by rw [hN]; omega`. Establish `h2 : ¬ R.N R.m - 2 < R.k` using `by rw [hN]; omega`. Establish `e1 : Examples₂.blkN R (R.N R.m - 1) = R.m - 1`. Unfold `Examples₂.blkN`. Rewrite using `[hN]`.

Establish `: R.k + R.m * (R.t + 1) - 1 - R.k = (R.m - 1) * (R.t + 1) + R.t`. Take `⟨m', hm'⟩ : ∃ m', R.m = m' + 1` from `⟨R.m - 1, by omega⟩`. Rewrite using `[hm']`. Simplify using `only [Nat.add_sub_cancel]`. Put the polynomial expressions in normal form.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]`. Establish `e2 : Examples₂.blkN R (R.N R.m - 2) = R.m - 1`. Unfold `Examples₂.blkN`. Rewrite using `[hN]`.

Establish `: R.k + R.m * (R.t + 1) - 2 - R.k = (R.m - 1) * (R.t + 1) + (R.t - 1)`. Take `⟨m', hm'⟩ : ∃ m', R.m = m' + 1` from `⟨R.m - 1, by omega⟩`. Rewrite using `[hm']`. Simplify using `only [Nat.add_sub_cancel]`. Put the polynomial expressions in normal form.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]`. Establish `hb1 : Examples₂.blkN R (R.N R.m - 1) < R.m` using `by rw [e1]; omega`. Establish `hb2 : Examples₂.blkN R (R.N R.m - 2) < R.m` using `by rw [e2]; omega`. Unfold `Examples₂.wtN`.

Rewrite using `[dif_neg h1, dif_neg h2, dif_pos hb1, dif_pos hb2]`. Establish `key : ∀ (a b : ℕ) (ha : a < R.m) (hb : b < R.m), a = b → -wG R (P.e ⟨a, ha⟩) (a + 1) = -wG R (P.e ⟨b, hb⟩) (b + 1)`. Introduce and unpack `a b ha hb rfl`. Both sides reduce to the same expression. Conclude with `key _ _ hb1 hb2 (by rw [e1, e2])`.
-/
theorem wtN_last_two (R : Ranks) (P : HCParam R) :
    Examples₂.wtN P (R.N R.m - 1) = Examples₂.wtN P (R.N R.m - 2) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have ht := R.rank_add_five_le
  have hN : R.N R.m = R.k + R.m * (R.t + 1) := rfl
  have hmt : 2 * 2 ≤ R.m * (R.t + 1) := Nat.mul_le_mul hm (by omega)
  have h1 : ¬ R.N R.m - 1 < R.k := by rw [hN]; omega
  have h2 : ¬ R.N R.m - 2 < R.k := by rw [hN]; omega
  have e1 : Examples₂.blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold Examples₂.blkN
    rw [hN]
    have : R.k + R.m * (R.t + 1) - 1 - R.k = (R.m - 1) * (R.t + 1) + R.t := by
      obtain ⟨m', hm'⟩ : ∃ m', R.m = m' + 1 := ⟨R.m - 1, by omega⟩
      rw [hm']
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have e2 : Examples₂.blkN R (R.N R.m - 2) = R.m - 1 := by
    unfold Examples₂.blkN
    rw [hN]
    have : R.k + R.m * (R.t + 1) - 2 - R.k = (R.m - 1) * (R.t + 1) + (R.t - 1) := by
      obtain ⟨m', hm'⟩ : ∃ m', R.m = m' + 1 := ⟨R.m - 1, by omega⟩
      rw [hm']
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hb1 : Examples₂.blkN R (R.N R.m - 1) < R.m := by rw [e1]; omega
  have hb2 : Examples₂.blkN R (R.N R.m - 2) < R.m := by rw [e2]; omega
  unfold Examples₂.wtN
  rw [dif_neg h1, dif_neg h2, dif_pos hb1, dif_pos hb2]
  have key : ∀ (a b : ℕ) (ha : a < R.m) (hb : b < R.m), a = b →
      -wG R (P.e ⟨a, ha⟩) (a + 1) = -wG R (P.e ⟨b, hb⟩) (b + 1) := by
    rintro a b ha hb rfl; rfl
  exact key _ _ hb1 hb2 (by rw [e1, e2])

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

/- English proof (translation)
Unfold `Wts.lamTrue shiftW Wts.lamN Examples₂.lamOf`. Simplify using `only [dif_pos (le_refl R.m)]`. Rewrite using `[Examples₂.wtQ_eq_wtN, Examples₂.wtQ_eq_wtN, hi, hj, wtN_last_two]`.
-/
theorem lamTrue_last_two (u : Pr.Word) (τ : X.Tau) (i j : Fin (R.N R.m)) (hi : i.1 = R.N R.m - 1) (hj : j.1 = R.N R.m - 2) :
    (W.lamTrue u R.m τ).w i = (W.lamTrue u R.m τ).w j := by
  unfold Wts.lamTrue shiftW Wts.lamN Examples₂.lamOf
  simp only [dif_pos (le_refl R.m)]
  rw [Examples₂.wtQ_eq_wtN, Examples₂.wtQ_eq_wtN, hi, hj, wtN_last_two]

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `hN : R.N R.m = R.k + R.m * (R.t + 1)` using `rfl`. Establish `hmt : 2 * 2 ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul hm (by have := R.rank_add_five_le; omega)`. Establish `hpos : 0 < R.N R.m - 1` using `by rw [hN]; omega`.

Establish `hpos' : 0 < R.N R.m` using `by omega`. Take `⟨ha, hb⟩` from `hI ⟨R.N R.m - 1 - 1, by omega⟩`. Unfold `aBr at ha`. Unfold `bBr at hb`. Establish `e` using `lamTrue_last_two W u τ (iS (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩) (iC (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩) (by simp [iS]; omega) (by simp [iC]; omega)`.

Unfold `SameShift DomWeight.detShift`. Rewrite using `[dif_pos hpos, dif_pos hpos']`. Establish `e2 : (W.lamTrue u R.m τ).w ⟨R.N R.m - 1, by omega⟩ = (W.lamTrue u R.m τ).w (iS (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩)`. Use `congr 1`. Use `ext`.

Simplify using `[iS]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e2]`. Establish `e3 : (W.sgTrue τ).w ⟨R.N R.m - 1 - 1, by omega⟩ = (W.sgTrue τ).w ⟨R.N R.m - 1 - 1, by omega⟩` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem sameShift_of_interlace (u : Pr.Word) (τ : X.Tau)
    (hI : Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ)) :
    SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hN : R.N R.m = R.k + R.m * (R.t + 1) := rfl
  have hmt : 2 * 2 ≤ R.m * (R.t + 1) := Nat.mul_le_mul hm (by have := R.rank_add_five_le; omega)
  have hpos : 0 < R.N R.m - 1 := by rw [hN]; omega
  have hpos' : 0 < R.N R.m := by omega
  obtain ⟨ha, hb⟩ := hI ⟨R.N R.m - 1 - 1, by omega⟩
  unfold aBr at ha
  unfold bBr at hb
  have e := lamTrue_last_two W u τ (iS (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩) (iC (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩)
    (by simp [iS]; omega) (by simp [iC]; omega)
  unfold SameShift DomWeight.detShift
  rw [dif_pos hpos, dif_pos hpos']
  have e2 : (W.lamTrue u R.m τ).w ⟨R.N R.m - 1, by omega⟩ = (W.lamTrue u R.m τ).w (iS (N_m_succ R) ⟨R.N R.m - 1 - 1, by omega⟩) := by
    congr 1; ext; simp [iS]; omega
  rw [e2]
  have e3 : (W.sgTrue τ).w ⟨R.N R.m - 1 - 1, by omega⟩ = (W.sgTrue τ).w ⟨R.N R.m - 1 - 1, by omega⟩ := rfl
  omega

end Shift

section Degen

open Classical

variable {K : Type} [Field K] {ι : Type} [Fintype ι]

def weylTwoBlockMatrix (τ0 : ι) (k : ℕ) : ι × Fin k × Fin k → ℕ := fun v => if v.1 = τ0 then 1 else 0

/- English proof (translation)
Rewrite using `[φ.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[rename_monomial, mem_weightedHomogeneousSubmodule]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]`.

Use `h (mem_support_iff.mp hd)` as an intermediate fact. Rewrite `this` using `[Finsupp.weight_apply]`. Simplify using `using this`.
-/
theorem iwh_rename {σ τ' : Type} (f : σ → τ') (w : τ' → ℕ) {φ : MvPolynomial σ K} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) φ D) : IsWeightedHomogeneous w (rename f φ) D := by
  rw [φ.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [rename_monomial, mem_weightedHomogeneousSubmodule]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  have := h (mem_support_iff.mp hd)
  rw [Finsupp.weight_apply] at this
  simpa using this

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul, mul_one]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW, Pi.single_apply]`.
-/
theorem weight_one_eq_sum_colW {k : ℕ} (m : Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (fun _ : Fin k × Fin k => (1 : ℕ)) m = ∑ s, Finsupp.weight (Formalism.GradedWeylDivisibility.colW k k) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

/- English proof (translation)
Introduce `m hm`. Establish `h` using `(Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.mp hF).1 hm`. Rewrite using `[weight_one_eq_sum_colW, h]`.
-/
theorem dualWeyl_total {k : ℕ} {ν : Fin k → ℕ} {F : MvPolynomial (Fin k × Fin k) K}
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl K k k ν) : IsWeightedHomogeneous (fun _ => (1 : ℕ)) F (∑ s, ν s) := by
  intro m hm
  have h := (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.mp hF).1 hm
  rw [weight_one_eq_sum_colW, h]

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `P ⟨F, hF, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_weightedHomogeneousSubmodule]`. Establish `e : (∑ s, (lam τ0).natW s) = ∑ τ ∈ Finset.univ, (if τ = τ0 then ∑ s, (lam τ0).natW s else 0)`.

Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `IsWeightedHomogeneous.prod _ _ _ fun τ _ => ?_` and prove the remaining obligations. Unfold `Formalism.GradedWeylDivisibility.blockEmb`.

Apply `iwh_rename` to reduce the goal to its premises. Distinguish the cases in `hτ : τ = τ0`. Substitute `hτ` using the available equality. Establish `h1` using `dualWeyl_total (hF τ)`. Rewrite using `[if_pos rfl]`.

Establish `e2 : (weylTwoBlockMatrix τ k ∘ fun v : Fin k × Fin k => (τ, v)) = fun _ => (1 : ℕ)`. Use function extensionality and compare the values at `v`. Simplify using `[weylTwoBlockMatrix]`. Rewrite using `[e2]`. Conclude with `h1`.

Rewrite using `[if_neg hτ]`. Establish `e2 : (weylTwoBlockMatrix τ0 k ∘ fun v : Fin k × Fin k => (τ, v)) = fun _ => (0 : ℕ)`. Use function extensionality and compare the values at `v`. Simplify using `[weylTwoBlockMatrix, hτ]`. Rewrite using `[e2]`.

Introduce `m _`. Simplify using `[Finsupp.weight_apply]`.
-/
theorem VV_le_blk {k : ℕ} (lam : ι → DomWeight k) (τ0 : ι) :
    VV K lam ≤ weightedHomogeneousSubmodule K (weylTwoBlockMatrix τ0 k) (∑ s, (lam τ0).natW s) := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
  have e : (∑ s, (lam τ0).natW s) = ∑ τ ∈ Finset.univ, (if τ = τ0 then ∑ s, (lam τ0).natW s else 0) := by
    rw [Finset.sum_ite_eq']; simp
  rw [e]
  refine IsWeightedHomogeneous.prod _ _ _ fun τ _ => ?_
  unfold Formalism.GradedWeylDivisibility.blockEmb
  apply iwh_rename
  by_cases hτ : τ = τ0
  · subst hτ
    have h1 := dualWeyl_total (hF τ)
    rw [if_pos rfl]
    have e2 : (weylTwoBlockMatrix τ k ∘ fun v : Fin k × Fin k => (τ, v)) = fun _ => (1 : ℕ) := by
      funext v; simp [weylTwoBlockMatrix]
    rw [e2]
    exact h1
  · rw [if_neg hτ]
    have e2 : (weylTwoBlockMatrix τ0 k ∘ fun v : Fin k × Fin k => (τ, v)) = fun _ => (0 : ℕ) := by
      funext v; simp [weylTwoBlockMatrix, hτ]
    rw [e2]
    intro m _
    simp [Finsupp.weight_apply]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_eq_single τ0 (by intro x _ hx; simp [weylTwoBlockMatrix, hx]) (by simp)]`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `[weylTwoBlockMatrix]`.
-/
theorem weight_blk_eq {k : ℕ} (τ0 : ι) (m : ι × Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (weylTwoBlockMatrix τ0 k) m = ∑ a, ∑ s, m (τ0, a, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single τ0 (by intro x _ hx; simp [weylTwoBlockMatrix, hx]) (by simp)]
  rw [Fintype.sum_prod_type]
  simp [weylTwoBlockMatrix]

/- English proof (translation)
Unfold `coefLast`. Establish `e : (monomial m (1 : K)) = basisMonomials (ι × Fin N × Fin N) K m` using `by simp [coe_basisMonomials]`. Rewrite using `[e, Module.Basis.constr_basis]`.
-/
theorem coefLast_monomial {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ) (m : ι × Fin N × Fin N →₀ ℕ) :
    coefLast (K := K) hN b (monomial m 1) =
      if IsTop hN b m then monomial (m.comapDomain (upVar hN) (upVar_inj hN).injOn) (1 : K) else 0 := by
  unfold coefLast
  have e : (monomial m (1 : K)) = basisMonomials (ι × Fin N × Fin N) K m := by simp [coe_basisMonomials]
  rw [e, Module.Basis.constr_basis]

/- English proof (translation)
Rewrite using `[weight_blk_eq, weight_blk_eq]`. Take `⟨h1, h2⟩` from `hm`. Substitute `hN` using the available equality. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.sum_univ_castSucc]`.

Establish `e1 : ∀ a : Fin n, m (τ0, a.castSucc, Fin.last n) = 0` using `fun a => h2 τ0 _`. Establish `e2 : m (τ0, Fin.last n, Fin.last n) = 0` using `h2 τ0 _`. Establish `e3 : ∀ s : Fin n, m (τ0, Fin.last n, s.castSucc) = b τ0 s` using `fun s => h1 τ0 s`. Simplify using `only [e1, e2, e3, add_zero]`. Use `congr 1`.
-/
theorem weight_top {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ) (τ0 : ι) (m : ι × Fin N × Fin N →₀ ℕ)
    (hm : IsTop hN b m) :
    Finsupp.weight (weylTwoBlockMatrix τ0 N) m =
      Finsupp.weight (weylTwoBlockMatrix τ0 n) (m.comapDomain (upVar hN) (upVar_inj hN).injOn) + ∑ s, b τ0 s := by
  rw [weight_blk_eq, weight_blk_eq]
  obtain ⟨h1, h2⟩ := hm
  subst hN
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc]
  have e1 : ∀ a : Fin n, m (τ0, a.castSucc, Fin.last n) = 0 := fun a => h2 τ0 _
  have e2 : m (τ0, Fin.last n, Fin.last n) = 0 := h2 τ0 _
  have e3 : ∀ s : Fin n, m (τ0, Fin.last n, s.castSucc) = b τ0 s := fun s => h1 τ0 s
  simp only [e1, e2, e3, add_zero]
  congr 1

/- English proof (translation)
Rewrite using `[← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[show monomial m (coeff m f) = coeff m f • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, coefLast_monomial]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `split_ifs with ht`.

Rewrite using `[mem_weightedHomogeneousSubmodule]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Establish `h1` using `hf (mem_support_iff.mp hm)`. Rewrite `h1` using `[weight_top hN b τ0 m ht, hD]`. Use linear arithmetic over natural numbers and integers.

Conclude with `Submodule.zero_mem _`.
-/
theorem coefLast_blk {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ) (τ0 : ι) {f : Pol K ι N} {D d : ℕ}
    (hf : IsWeightedHomogeneous (weylTwoBlockMatrix τ0 N) f D) (hD : D = d + ∑ s, b τ0 s) :
    IsWeightedHomogeneous (weylTwoBlockMatrix τ0 n) (coefLast hN b f) d := by
  rw [← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [show monomial m (coeff m f) = coeff m f • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coefLast_monomial]
  refine Submodule.smul_mem _ _ ?_
  split_ifs with ht
  · rw [mem_weightedHomogeneousSubmodule]
    apply isWeightedHomogeneous_monomial
    have h1 := hf (mem_support_iff.mp hm)
    rw [weight_top hN b τ0 m ht, hD] at h1
    omega
  · exact Submodule.zero_mem _

/- English proof (translation)
Unfold `fockB`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `h1` using `hp (mem_support_iff.mp hm)`. Distinguish the cases in `h : coeff m q = 0`. Simplify using `[h]`.

Conclude with `absurd (h1.symm.trans (hq h)) hne`.
-/
theorem fockB_eq_zero_of_blk {σ : Type} {w : σ → ℕ} {p q : MvPolynomial σ K} {d1 d2 : ℕ}
    (hp : IsWeightedHomogeneous w p d1) (hq : IsWeightedHomogeneous w q d2) (hne : d1 ≠ d2) : fockB p q = 0 := by
  unfold fockB
  refine Finset.sum_eq_zero fun m hm => ?_
  have h1 := hp (mem_support_iff.mp hm)
  by_cases h : coeff m q = 0
  · simp [h]
  · exact absurd (h1.symm.trans (hq h)) hne

end Degen

section Degen2

open Classical

variable {K : Type} [Field K] {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hl : lam.detShift = lam.w (Fin.last n)`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Use `congr 1`. Establish `hs : sg.detShift = sg.w ⟨n - 1, by omega⟩`.

Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hn]`. Establish `hA : ∀ i, ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.w (Fin.last n)`. Introduce `i; unfold DomWeight.natW; rw [hl, Int.toNat_of_nonneg (by have := lam.anti (Fin.le_last i); omega)]`. Establish `hC : ∀ s, ((sg.natW s : ℕ) : ℤ) = sg.w s - sg.w ⟨n - 1, by omega⟩`.

Introduce `s`. Unfold `DomWeight.natW`. Rewrite using `[hs, Int.toNat_of_nonneg (by have := sg.anti (show s ≤ (⟨n - 1, by omega⟩ : Fin n) from Fin.mk_le_mk.mpr (by omega)); omega)]`. Establish `hB : ∀ s, (((bBr rfl lam sg s).toNat : ℕ) : ℤ) = lam.w s.castSucc - sg.w s`. Introduce `s`.

Rewrite using `[Int.toNat_of_nonneg (hI s).2]`. Unfold `bBr iC`. Both sides reduce to the same expression. Establish `hlast` using `hI ⟨n - 1, by omega⟩`. Unfold `aBr iS at hlast`.

Establish `e : (⟨(n - 1 : ℕ) + 1, by omega⟩ : Fin (n + 1)) = Fin.last n` using `Fin.ext (by simp; omega)`. Simplify using `only [e] at hlast`. Use `⟨?_, by rw [hs, hl]; exact hlast.1⟩` and prove the remaining obligations. Use `push_cast`. Simplify using `only [hA, hB, hC]`.

Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [sub_self, add_zero, hs, hl]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shift_arith {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) (hI : Interlace rfl lam sg) (hn : 0 < n) :
    ((∑ i, lam.natW i : ℕ) : ℤ) =
      ((∑ s, (bBr rfl lam sg s).toNat : ℕ) : ℤ) + ((∑ s, sg.natW s : ℕ) : ℤ) + n * (sg.detShift - lam.detShift) ∧
    0 ≤ sg.detShift - lam.detShift := by
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift; rw [dif_pos (Nat.succ_pos n)]; congr 1
  have hs : sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
    unfold DomWeight.detShift; rw [dif_pos hn]
  have hA : ∀ i, ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.w (Fin.last n) := by
    intro i; unfold DomWeight.natW; rw [hl, Int.toNat_of_nonneg (by have := lam.anti (Fin.le_last i); omega)]
  have hC : ∀ s, ((sg.natW s : ℕ) : ℤ) = sg.w s - sg.w ⟨n - 1, by omega⟩ := by
    intro s; unfold DomWeight.natW
    rw [hs, Int.toNat_of_nonneg (by have := sg.anti (show s ≤ (⟨n - 1, by omega⟩ : Fin n) from Fin.mk_le_mk.mpr (by omega)); omega)]
  have hB : ∀ s, (((bBr rfl lam sg s).toNat : ℕ) : ℤ) = lam.w s.castSucc - sg.w s := by
    intro s; rw [Int.toNat_of_nonneg (hI s).2]; unfold bBr iC; rfl
  have hlast := hI ⟨n - 1, by omega⟩
  unfold aBr iS at hlast
  have e : (⟨(n - 1 : ℕ) + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
  simp only [e] at hlast
  refine ⟨?_, by rw [hs, hl]; exact hlast.1⟩
  push_cast
  simp only [hA, hB, hC]
  rw [Fin.sum_univ_castSucc]
  simp only [sub_self, add_zero, hs, hl]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/- English proof (translation)
Establish `key : ∀ (f : VV K lam) j, fockB (bVVfun K sg j) (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) = 0`. Introduce `f j`. Establish `hp : IsWeightedHomogeneous (weylTwoBlockMatrix τ0 n) (bVVfun K sg j) (∑ s, (sg τ0).natW s)`. Use `VV_le_blk (K := K) sg τ0 (show bVVfun K sg j ∈ VV K sg by rw [← bVV_coe]; exact (bVV K sg j).2)` as an intermediate fact. Rewrite `this` using `[mem_weightedHomogeneousSubmodule]`. Then use the resulting hypothesis.

Establish `hf : IsWeightedHomogeneous (weylTwoBlockMatrix τ0 N) (f : Pol K ι N) (∑ i, (lam τ0).natW i)`. Use `VV_le_blk (K := K) lam τ0 f.2` as an intermediate fact. Rewrite `this` using `[mem_weightedHomogeneousSubmodule]`. Then use the resulting hypothesis. Establish `harith : ∑ s, (sg τ0).natW s + ∑ s, bExp hN lam sg τ0 s < ∑ i, (lam τ0).natW i`. Establish `h` using `hI τ0`.

Substitute `hN` using the available equality. Take `⟨h1, h2⟩` from `shift_arith (lam τ0) (sg τ0) h hn`. Establish `h3 : (sg τ0).detShift - (lam τ0).detShift ≠ 0`. Introduce `h0`. Apply `hS` to reduce the goal to its premises.

Unfold `SameShift`. Use linear arithmetic over natural numbers and integers. Establish `h4 : (0 : ℤ) < (n : ℤ) * ((sg τ0).detShift - (lam τ0).detShift)` using `mul_pos (by exact_mod_cast hn) (lt_of_le_of_ne h2 (Ne.symm h3))`. Unfold `bExp`. Establish `: ((∑ s, (sg τ0).natW s + ∑ s, (bBr rfl (lam τ0) (sg τ0) s).toNat : ℕ) : ℤ) < ((∑ i, (lam τ0).natW i : ℕ) : ℤ)`.

Move the coercions through the operations in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Conclude with `fockB_eq_zero_of_blk hp (coefLast_blk hN _ τ0 hf (d := ∑ i, (lam τ0).natW i - ∑ s, bExp hN lam sg τ0 s) (by omega)) (by omega)`. Use `ext1 f`.

Simplify using `only [brStd, brStdP, LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, projVV, LinearMap.zero_apply]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, fockBL_apply, key, zero_smul, smul_zero, Finset.sum_const_zero]`.
-/
theorem brStd_eq_zero_of_shift {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : InterlaceAll hN lam sg) (hn : 0 < n) (τ0 : ι) (hS : ¬ SameShift (lam τ0) (sg τ0)) :
    brStd (K := K) hN lam sg = 0 := by
  have key : ∀ (f : VV K lam) j, fockB (bVVfun K sg j) (coefLast hN (bExp hN lam sg) (f : Pol K ι N)) = 0 := by
    intro f j
    have hp : IsWeightedHomogeneous (weylTwoBlockMatrix τ0 n) (bVVfun K sg j) (∑ s, (sg τ0).natW s) := by
      have := VV_le_blk (K := K) sg τ0 (show bVVfun K sg j ∈ VV K sg by rw [← bVV_coe]; exact (bVV K sg j).2)
      rwa [mem_weightedHomogeneousSubmodule] at this
    have hf : IsWeightedHomogeneous (weylTwoBlockMatrix τ0 N) (f : Pol K ι N) (∑ i, (lam τ0).natW i) := by
      have := VV_le_blk (K := K) lam τ0 f.2
      rwa [mem_weightedHomogeneousSubmodule] at this
    have harith : ∑ s, (sg τ0).natW s + ∑ s, bExp hN lam sg τ0 s < ∑ i, (lam τ0).natW i := by
      have h := hI τ0
      subst hN
      obtain ⟨h1, h2⟩ := shift_arith (lam τ0) (sg τ0) h hn
      have h3 : (sg τ0).detShift - (lam τ0).detShift ≠ 0 := by
        intro h0; apply hS; unfold SameShift; omega
      have h4 : (0 : ℤ) < (n : ℤ) * ((sg τ0).detShift - (lam τ0).detShift) :=
        mul_pos (by exact_mod_cast hn) (lt_of_le_of_ne h2 (Ne.symm h3))
      unfold bExp
      have : ((∑ s, (sg τ0).natW s + ∑ s, (bBr rfl (lam τ0) (sg τ0) s).toNat : ℕ) : ℤ) < ((∑ i, (lam τ0).natW i : ℕ) : ℤ) := by
        push_cast at h1 ⊢; linarith
      exact_mod_cast this
    exact fockB_eq_zero_of_blk hp
      (coefLast_blk hN _ τ0 hf (d := ∑ i, (lam τ0).natW i - ∑ s, bExp hN lam sg τ0 s) (by omega)) (by omega)
  ext1 f
  simp only [brStd, brStdP, LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, projVV,
    LinearMap.zero_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, fockBL_apply, key, zero_smul,
    smul_zero, Finset.sum_const_zero]

end Degen2

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Coef

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[iC, iL] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem lx_iC_ne_iL (i : Fin n) : iC hN i ≠ iL hN := by
  intro h
  have := congrArg Fin.val h
  simp [iC, iL] at this
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨a.1, by have := a.2; have : a.1 ≠ n := fun h => ha (Fin.ext h); omega⟩, Fin.ext rfl⟩`.
-/
theorem lx_eq_iC_of_ne (a : Fin N) (ha : a ≠ iL hN) : ∃ i : Fin n, iC hN i = a :=
  ⟨⟨a.1, by have := a.2; have : a.1 ≠ n := fun h => ha (Fin.ext h); omega⟩, Fin.ext rfl⟩

open Classical in
/- English proof (translation)
Simplify using `only [zExp, Finsupp.finsetSum_apply, Finsupp.single_apply]`.
-/
theorem lx_zExp_apply (b : ι → Fin n → ℕ) (v : ι × Fin N × Fin N) :
    zExp hN b v = ∑ τ, ∑ s, if (τ, iL hN, iC hN s) = v then b τ s else 0 := by
  classical
  simp only [zExp, Finsupp.finsetSum_apply, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[lx_zExp_apply, Finset.sum_eq_single_of_mem τ (Finset.mem_univ _), Finset.sum_eq_single_of_mem s (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Introduce `s' _ hs`. Conclude with `if_neg fun h => hs (iC_inj hN (congrArg (fun x => x.2.2) h))`. Introduce `τ' _ hτ`.

Conclude with `Finset.sum_eq_zero fun s' _ => if_neg fun h => hτ (congrArg Prod.fst h)`.
-/
theorem lx_zExp_top (b : ι → Fin n → ℕ) (τ : ι) (s : Fin n) : zExp hN b (τ, iL hN, iC hN s) = b τ s := by
  classical
  rw [lx_zExp_apply, Finset.sum_eq_single_of_mem τ (Finset.mem_univ _),
    Finset.sum_eq_single_of_mem s (Finset.mem_univ _)]
  · simp
  · intro s' _ hs
    exact if_neg fun h => hs (iC_inj hN (congrArg (fun x => x.2.2) h))
  · intro τ' _ hτ
    exact Finset.sum_eq_zero fun s' _ => if_neg fun h => hτ (congrArg Prod.fst h)

/- English proof (translation)
Rewrite using `[lx_zExp_apply]`. Use `Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun s _ => if_neg ?_` and prove the remaining obligations. Introduce `h`. Substitute `h` using the available equality. Break down `hv with h | h` into its components or cases.

Conclude with `h rfl`. Conclude with `lx_iC_ne_iL hN s h`.
-/
theorem lx_zExp_off (b : ι → Fin n → ℕ) (v : ι × Fin N × Fin N) (hv : v.2.1 ≠ iL hN ∨ v.2.2 = iL hN) :
    zExp hN b v = 0 := by
  classical
  rw [lx_zExp_apply]
  refine Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun s _ => if_neg ?_
  intro h
  subst h
  rcases hv with h | h
  · exact h rfl
  · exact lx_iC_ne_iL hN s h

/- English proof (translation)
The claim follows from `upVar_inj hN`.
-/
theorem lx_upVar_inj : Function.Injective (upVar (ι := ι) hN) := upVar_inj hN

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, rfl⟩`. Use extensionality with `⟨τ, a, s⟩`. Rewrite using `[Finsupp.add_apply]`. Distinguish the cases in `hs : s = iL hN`.

Substitute `hs` using the available equality. Rewrite using `[h2, lx_zExp_off hN b _ (Or.inr rfl), Finsupp.mapDomain_of_notMem_range]`. Introduce and unpack `⟨w, hw⟩`. Use `congrArg (fun x => x.2.2) hw` as an intermediate fact. Conclude with `lx_iC_ne_iL hN _ this`.

Take `⟨s', rfl⟩` from `lx_eq_iC_of_ne hN s hs`. Distinguish the cases in `ha : a = iL hN`. Substitute `ha` using the available equality. Rewrite using `[h1, lx_zExp_top, Finsupp.mapDomain_of_notMem_range, zero_add]`. Introduce and unpack `⟨w, hw⟩`.

Use `congrArg (fun x => x.2.1) hw` as an intermediate fact. Conclude with `lx_iC_ne_iL hN _ this`. Take `⟨a', rfl⟩` from `lx_eq_iC_of_ne hN a ha`. Establish `e : ((τ, iC hN a', iC hN s') : ι × Fin N × Fin N) = upVar hN (τ, a', s')` using `rfl`. Rewrite using `[e, Finsupp.mapDomain_apply (upVar_inj hN), Finsupp.comapDomain_apply, lx_zExp_off hN b _ (Or.inl (lx_iC_ne_iL hN a')), add_zero]`.

Introduce and unpack `rfl`. Use `⟨⟨fun τ s => ?_, fun τ a => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, lx_zExp_top, Finsupp.mapDomain_of_notMem_range, zero_add]`. Introduce and unpack `⟨w, hw⟩`. Use `congrArg (fun x => x.2.1) hw` as an intermediate fact.

Conclude with `lx_iC_ne_iL hN _ this`. Rewrite using `[Finsupp.add_apply, lx_zExp_off hN b _ (Or.inr rfl), Finsupp.mapDomain_of_notMem_range, zero_add]`. Introduce and unpack `⟨w, hw⟩`. Use `congrArg (fun x => x.2.2) hw` as an intermediate fact. Conclude with `lx_iC_ne_iL hN _ this`.

Use extensionality with `v`. Rewrite using `[Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply (upVar_inj hN), lx_zExp_off hN b _ (Or.inl (lx_iC_ne_iL hN _)), add_zero]`.
-/
theorem lx_isTop_iff (b : ι → Fin n → ℕ) (m : ι × Fin N × Fin N →₀ ℕ) (m' : ι × Fin n × Fin n →₀ ℕ) :
    (IsTop hN b m ∧ m.comapDomain (upVar hN) (upVar_inj hN).injOn = m') ↔
      m = Finsupp.mapDomain (upVar hN) m' + zExp hN b := by
  constructor
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    ext ⟨τ, a, s⟩
    rw [Finsupp.add_apply]
    by_cases hs : s = iL hN
    · subst hs
      rw [h2, lx_zExp_off hN b _ (Or.inr rfl), Finsupp.mapDomain_of_notMem_range]
      rintro ⟨w, hw⟩
      have := congrArg (fun x => x.2.2) hw
      exact lx_iC_ne_iL hN _ this
    · obtain ⟨s', rfl⟩ := lx_eq_iC_of_ne hN s hs
      by_cases ha : a = iL hN
      · subst ha
        rw [h1, lx_zExp_top, Finsupp.mapDomain_of_notMem_range, zero_add]
        rintro ⟨w, hw⟩
        have := congrArg (fun x => x.2.1) hw
        exact lx_iC_ne_iL hN _ this
      · obtain ⟨a', rfl⟩ := lx_eq_iC_of_ne hN a ha
        have e : ((τ, iC hN a', iC hN s') : ι × Fin N × Fin N) = upVar hN (τ, a', s') := rfl
        rw [e, Finsupp.mapDomain_apply (upVar_inj hN), Finsupp.comapDomain_apply,
          lx_zExp_off hN b _ (Or.inl (lx_iC_ne_iL hN a')), add_zero]
  · rintro rfl
    refine ⟨⟨fun τ s => ?_, fun τ a => ?_⟩, ?_⟩
    · rw [Finsupp.add_apply, lx_zExp_top, Finsupp.mapDomain_of_notMem_range, zero_add]
      rintro ⟨w, hw⟩
      have := congrArg (fun x => x.2.1) hw
      exact lx_iC_ne_iL hN _ this
    · rw [Finsupp.add_apply, lx_zExp_off hN b _ (Or.inr rfl), Finsupp.mapDomain_of_notMem_range, zero_add]
      rintro ⟨w, hw⟩
      have := congrArg (fun x => x.2.2) hw
      exact lx_iC_ne_iL hN _ this
    · ext v
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply (upVar_inj hN),
        lx_zExp_off hN b _ (Or.inl (lx_iC_ne_iL hN _)), add_zero]

/- English proof (translation)
Establish `key : (lcoeff K m').comp (coefLast (K` using `K) hN b) = lcoeff K (Finsupp.mapDomain (upVar hN) m' + zExp hN b) := by`. Use `(basisMonomials (ι × Fin N × Fin N) K).ext fun m => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, coefLast, Module.Basis.constr_basis]`. Simplify using `only [coe_basisMonomials, lcoeff_apply]`. Rewrite using `[coeff_monomial]`.

Distinguish the cases in `hT : IsTop hN b m`. Rewrite using `[if_pos hT, coeff_monomial]`. Distinguish the cases in `hm : m.comapDomain (upVar hN) (upVar_inj hN).injOn = m'`. Rewrite using `[if_pos hm, if_pos ((lx_isTop_iff hN b m m').1 ⟨hT, hm⟩)]`. Rewrite using `[if_neg hm, if_neg]`.

Introduce `h`. Conclude with `hm ((lx_isTop_iff hN b m m').2 h).2`. Rewrite using `[if_neg hT, coeff_zero, if_neg]`. Introduce `h`. Conclude with `hT ((lx_isTop_iff hN b m m').2 h).1`.

Conclude with `LinearMap.congr_fun key f`.
-/
theorem lx_coeff_coefLast (b : ι → Fin n → ℕ) (f : Pol K ι N) (m' : ι × Fin n × Fin n →₀ ℕ) :
    coeff m' (coefLast hN b f) = coeff (Finsupp.mapDomain (upVar hN) m' + zExp hN b) f := by
  classical
  have key : (lcoeff K m').comp (coefLast (K := K) hN b) = lcoeff K (Finsupp.mapDomain (upVar hN) m' + zExp hN b) := by
    refine (basisMonomials (ι × Fin N × Fin N) K).ext fun m => ?_
    rw [LinearMap.comp_apply, coefLast, Module.Basis.constr_basis]
    simp only [coe_basisMonomials, lcoeff_apply]
    rw [coeff_monomial]
    by_cases hT : IsTop hN b m
    · rw [if_pos hT, coeff_monomial]
      by_cases hm : m.comapDomain (upVar hN) (upVar_inj hN).injOn = m'
      · rw [if_pos hm, if_pos ((lx_isTop_iff hN b m m').1 ⟨hT, hm⟩)]
      · rw [if_neg hm, if_neg]
        intro h
        exact hm ((lx_isTop_iff hN b m m').2 h).2
    · rw [if_neg hT, coeff_zero, if_neg]
      intro h
      exact hT ((lx_isTop_iff hN b m m').2 h).1
  exact LinearMap.congr_fun key f

/- English proof (translation)
Use extensionality with `m'`. Rewrite using `[lx_coeff_coefLast, add_comm, coeff_monomial_mul, one_mul, upperParabolic, coeff_rename_mapDomain _ (upVar_inj hN)]`.
-/
theorem lx_coefLast_raise (b : ι → Fin n → ℕ) (g : Pol K ι n) :
    coefLast hN b (monomial (zExp hN b) (1 : K) * upperParabolic hN g) = g := by
  ext m'
  rw [lx_coeff_coefLast, add_comm, coeff_monomial_mul, one_mul, upperParabolic, coeff_rename_mapDomain _ (upVar_inj hN)]

end Coef

section One

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1)

def lxRho (v : Fin (n + 1) × Fin n) : Fin N × Fin N := (Fin.cast hN.symm v.1, iC hN v.2)

/- English proof (translation)
Introduce `v w h`. Simplify using `only [lxRho, Prod.mk.injEq] at h`. Conclude with `Prod.ext (by simpa using h.1) (iC_inj hN h.2)`.
-/
theorem lxRho_inj : Function.Injective (lxRho hN) := by
  intro v w h
  simp only [lxRho, Prod.mk.injEq] at h
  exact Prod.ext (by simpa using h.1) (iC_inj hN h.2)

def lamN (lam : DomWeight N) : Fin n → ℕ := fun i => (lam.w (iC hN i) - lam.detShift).toNat

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.initMinor Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]`.

Both sides reduce to the same expression.
-/
theorem lx_rename_minorA (i : Fin n) :
    rename (lxRho hN) (Formalism.GradedWeylDivisibility.initMinor K (Formalism.BranchingDeterminantCap.rowsA i) (by omega : i.val + 1 ≤ n)) =
      Formalism.GradedWeylDivisibility.lpMinor K (r := N) (n := N) (i.val + 1) (by have := i.2; omega) (by have := i.2; omega) := by
  unfold Formalism.GradedWeylDivisibility.initMinor Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.initMinor zMinor Formalism.GradedWeylDivisibility.initMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun p q => ?_` and prove the remaining obligations. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]`.

Use `congrArg (fun v => (X v : MvPolynomial (Fin N × Fin N) K)) (Prod.ext ?_ (Fin.ext rfl))` and prove the remaining obligations. Simplify using `only [lxRho, Formalism.BranchingDeterminantCap.rowsB]`. Apply the tactic sequence `split_ifs <;> first | exact Fin.ext rfl | exact Fin.ext (by simp [iL])`.
-/
theorem lx_rename_minorB (i : Fin n) :
    rename (lxRho hN) (Formalism.GradedWeylDivisibility.initMinor K (Formalism.BranchingDeterminantCap.rowsB i) (by omega : i.val + 1 ≤ n)) = zMinor K hN i := by
  unfold Formalism.GradedWeylDivisibility.initMinor zMinor Formalism.GradedWeylDivisibility.initMinor
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  refine congrArg (fun v => (X v : MvPolynomial (Fin N × Fin N) K)) (Prod.ext ?_ (Fin.ext rfl))
  simp only [lxRho, Formalism.BranchingDeterminantCap.rowsB]
  split_ifs <;> first | exact Fin.ext rfl | exact Fin.ext (by simp [iL])

variable {K}

/- English proof (translation)
Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`. Conclude with `Fin.ext (by simp [iL]; omega)`.
-/
theorem lx_detShift_N (lam : DomWeight N) : lam.detShift = lam.w (iL hN) := by
  unfold DomWeight.detShift
  rw [dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp [iL]; omega)

/- English proof (translation)
Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hn]`.
-/
theorem lx_detShift_n (sg : DomWeight n) (hn : 0 < n) : sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
  unfold DomWeight.detShift
  rw [dif_pos hn]

variable (lam : DomWeight N) (sg : DomWeight n)

/- English proof (translation)
Introduce `i`. Establish `hi` using `hI i`. Unfold `aBr bBr at hi`. Establish `hn : 0 < n` using `by have := i.2; omega`. Establish `hd : sg.detShift = lam.detShift` using `hS`.

Establish `e1` using `lx_detShift_N hN lam`. Establish `e2` using `lx_detShift_n (N := N) sg hn`. Establish `hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i` using `sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))`. Establish `hlamL : lam.w (iL hN) ≤ lam.w (iS hN i)` using `lam.anti (Fin.le_def.2 (by show i.val + 1 ≤ n; omega))`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [lamN, DomWeight.natW]`. Use linear arithmetic over natural numbers and integers. Unfold `Formalism.GradedWeylDivisibility.nuNext split_ifs with h`. Simplify using `only [lamN]`. Establish `e3 : iC hN ⟨i.val + 1, h⟩ = iS hN i` using `Fin.ext rfl`.

Rewrite using `[e3]`. Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.zero_le _`.
-/
theorem lx_il (hI : Interlace hN lam sg) (hS : SameShift lam sg) : Formalism.BranchingDeterminantCap.bmIL (lamN hN lam) sg.natW := by
  intro i
  have hi := hI i
  unfold aBr bBr at hi
  have hn : 0 < n := by have := i.2; omega
  have hd : sg.detShift = lam.detShift := hS
  have e1 := lx_detShift_N hN lam
  have e2 := lx_detShift_n (N := N) sg hn
  have hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))
  have hlamL : lam.w (iL hN) ≤ lam.w (iS hN i) := lam.anti (Fin.le_def.2 (by show i.val + 1 ≤ n; omega))
  refine ⟨?_, ?_⟩
  · simp only [lamN, DomWeight.natW]
    omega
  · unfold Formalism.GradedWeylDivisibility.nuNext
    split_ifs with h
    · simp only [lamN]
      have e3 : iC hN ⟨i.val + 1, h⟩ = iS hN i := Fin.ext rfl
      rw [e3]
      simp only [DomWeight.natW]
      omega
    · exact Nat.zero_le _

/- English proof (translation)
Establish `hi` using `hI i`. Unfold `aBr bBr at hi`. Establish `hn : 0 < n` using `by have := i.2; omega`. Establish `hd : sg.detShift = lam.detShift` using `hS`. Establish `e1` using `lx_detShift_N hN lam`.

Establish `e2` using `lx_detShift_n (N := N) sg hn`. Establish `hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i` using `sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))`. Establish `hlamL : lam.w (iL hN) ≤ lam.w (iS hN i)` using `lam.anti (Fin.le_def.2 (by show i.val + 1 ≤ n; omega))`. Unfold `aBr Formalism.GradedWeylDivisibility.nuNext`. Use `split_ifs with h`.

Simplify using `only [lamN, DomWeight.natW]`. Establish `e3 : iC hN ⟨i.val + 1, h⟩ = iS hN i` using `Fin.ext rfl`. Rewrite using `[e3]`. Use linear arithmetic over natural numbers and integers. Establish `e4 : iS hN i = iL hN` using `Fin.ext (by simp [iS, iL]; omega)`.

Establish `e5 : i = ⟨n - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e4]`. Simplify using `only [DomWeight.natW]`. Establish `e6 : sg.w i = sg.w ⟨n - 1, by omega⟩` using `congrArg sg.w e5`. Use linear arithmetic over natural numbers and integers.
-/
theorem lx_expA (hI : Interlace hN lam sg) (hS : SameShift lam sg) (i : Fin n) :
    (aBr hN lam sg i).toNat = sg.natW i - Formalism.GradedWeylDivisibility.nuNext (lamN hN lam) i := by
  have hi := hI i
  unfold aBr bBr at hi
  have hn : 0 < n := by have := i.2; omega
  have hd : sg.detShift = lam.detShift := hS
  have e1 := lx_detShift_N hN lam
  have e2 := lx_detShift_n (N := N) sg hn
  have hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))
  have hlamL : lam.w (iL hN) ≤ lam.w (iS hN i) := lam.anti (Fin.le_def.2 (by show i.val + 1 ≤ n; omega))
  unfold aBr Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · simp only [lamN, DomWeight.natW]
    have e3 : iC hN ⟨i.val + 1, h⟩ = iS hN i := Fin.ext rfl
    rw [e3]
    omega
  · have e4 : iS hN i = iL hN := Fin.ext (by simp [iS, iL]; omega)
    have e5 : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e4]
    simp only [DomWeight.natW]
    have e6 : sg.w i = sg.w ⟨n - 1, by omega⟩ := congrArg sg.w e5
    omega

/- English proof (translation)
Establish `hi` using `hI i`. Unfold `aBr bBr at hi`. Establish `hn : 0 < n` using `by have := i.2; omega`. Establish `hd : sg.detShift = lam.detShift` using `hS`. Establish `e1` using `lx_detShift_N hN lam`.

Establish `e2` using `lx_detShift_n (N := N) sg hn`. Establish `hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i` using `sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))`. Unfold `bBr`. Simplify using `only [lamN, DomWeight.natW]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lx_expB (hI : Interlace hN lam sg) (hS : SameShift lam sg) (i : Fin n) :
    (bBr hN lam sg i).toNat = lamN hN lam i - sg.natW i := by
  have hi := hI i
  unfold aBr bBr at hi
  have hn : 0 < n := by have := i.2; omega
  have hd : sg.detShift = lam.detShift := hS
  have e1 := lx_detShift_N hN lam
  have e2 := lx_detShift_n (N := N) sg hn
  have hlast : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))
  unfold bBr
  simp only [lamN, DomWeight.natW]
  omega

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.xiB xiBr`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, lx_rename_minorA, lx_rename_minorB, lx_expA hN lam sg hI hS, lx_expB hN lam sg hI hS]`.
-/
theorem lx_xi_rename (hI : Interlace hN lam sg) (hS : SameShift lam sg) :
    rename (lxRho hN) (Formalism.BranchingDeterminantCap.xiB K (lamN hN lam) sg.natW) = xiBr K hN lam sg := by
  unfold Formalism.BranchingDeterminantCap.xiB xiBr
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, lx_rename_minorA, lx_rename_minorB, lx_expA hN lam sg hI hS, lx_expB hN lam sg hI hS]

end One

section Ten

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

open Classical in

def lxW (τ : ι) : ι × Fin N × Fin N → ℕ := fun v => if v.1 = τ ∧ v.2.1 = iL hN then v.2.2.val + 1 else 0

def LxLow (τ : ι) (D : ℤ) (P : Pol K ι N) : Prop := ∀ M ∈ P.support, ((Finsupp.weight (lxW hN τ) M : ℕ) : ℤ) < D

/- English proof (translation)
Introduce `M hM`. Take `⟨x, hx, y, hy, rfl⟩` from `Finset.mem_add.1 (support_mul P Q hM)`. Rewrite using `[map_add, hQ (mem_support_iff.1 hy), add_zero]`. Conclude with `hP x hx`.
-/
theorem lx_low_mul {τ : ι} {D : ℤ} {P Q : Pol K ι N} (hP : LxLow hN τ D P)
    (hQ : IsWeightedHomogeneous (lxW hN τ) Q 0) : LxLow hN τ D (P * Q) := by
  classical
  intro M hM
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul P Q hM)
  rw [map_add, hQ (mem_support_iff.1 hy), add_zero]
  exact hP x hx

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `hP M (mem_support_iff.2 h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem lx_coeff_low {τ : ι} {D : ℤ} {P : Pol K ι N} (hP : LxLow hN τ D P) (M : ι × Fin N × Fin N →₀ ℕ)
    (hM : ((Finsupp.weight (lxW hN τ) M : ℕ) : ℤ) = D) : coeff M P = 0 := by
  by_contra h
  have := hP M (mem_support_iff.2 h)
  omega

/- English proof (translation)
Use `MvPolynomial.induction_on (motive := fun p => IsWeightedHomogeneous (lxW hN τ) (rename f p) 0) p (fun a => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)` and prove the remaining obligations. Rewrite using `[rename_C]`. Conclude with `isWeightedHomogeneous_C _ _`. Rewrite using `[map_add]`. Conclude with `hp.add hq`.

Rewrite using `[map_mul, rename_X]`. Establish `hx` using `isWeightedHomogeneous_X K (lxW hN τ) (f v)`. Rewrite `hx` using `[hf v]`. Simplify using `using hp.mul hx`.
-/
theorem rename_weightedHomogeneous_zero {α : Type} (f : α → ι × Fin N × Fin N) (τ : ι) (hf : ∀ v, lxW hN τ (f v) = 0)
    (p : MvPolynomial α K) : IsWeightedHomogeneous (lxW hN τ) (rename f p) 0 := by
  refine MvPolynomial.induction_on (motive := fun p => IsWeightedHomogeneous (lxW hN τ) (rename f p) 0) p
    (fun a => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)
  · rw [rename_C]
    exact isWeightedHomogeneous_C _ _
  · rw [map_add]
    exact hp.add hq
  · rw [map_mul, rename_X]
    have hx := isWeightedHomogeneous_X K (lxW hN τ) (f v)
    rw [hf v] at hx
    simpa using hp.mul hx

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply]`. Rewrite using `[Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Both sides reduce to the same expression.
-/
theorem lx_weight_mapDomain {α β M : Type} [AddCommMonoid M] (f : α → β) (w : β → M) (m : α →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f m) = Finsupp.weight (w ∘ f) m := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl

def lxR (τ : ι) (v : Fin (n + 1) × Fin n) : ι × Fin N × Fin N := (τ, lxRho hN v)

/- English proof (translation)
Introduce `v w h`. Simplify using `only [lxR, Prod.mk.injEq, true_and] at h`. Conclude with `lxRho_inj hN h`.
-/
theorem lxR_inj (τ : ι) : Function.Injective (lxR hN τ) := by
  intro v w h
  simp only [lxR, Prod.mk.injEq, true_and] at h
  exact lxRho_inj hN h

/- English proof (translation)
Unfold `lxW lxR lxRho`. Establish `e : (Fin.cast hN.symm v.1 = iL hN) ↔ v.1 = Fin.last n`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact Fin.ext (by have := congrArg Fin.val h; simpa [iL] using this)`. Introduce `h; exact Fin.ext (by simp [h, iL])`.

Distinguish the cases in `h : v.1 = Fin.last n`. Rewrite using `[if_pos ⟨rfl, e.2 h⟩, if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun h' => h (e.1 h'.2)), if_neg h]`.
-/
theorem lx_lxW_R (τ : ι) (v : Fin (n + 1) × Fin n) :
    lxW hN τ (lxR hN τ v) = if v.1 = Fin.last n then v.2.val + 1 else 0 := by
  unfold lxW lxR lxRho
  have e : (Fin.cast hN.symm v.1 = iL hN) ↔ v.1 = Fin.last n := by
    constructor
    · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa [iL] using this)
    · intro h; exact Fin.ext (by simp [h, iL])
  by_cases h : v.1 = Fin.last n
  · rw [if_pos ⟨rfl, e.2 h⟩, if_pos h]
    rfl
  · rw [if_neg (fun h' => h (e.1 h'.2)), if_neg h]

/- English proof (translation)
Unfold `lxW lxR`. Rewrite using `[if_neg (fun h' => h h'.1)]`.
-/
theorem lx_lxW_R_ne {τ τ' : ι} (h : τ' ≠ τ) (v : Fin (n + 1) × Fin n) : lxW hN τ (lxR hN τ' v) = 0 := by
  unfold lxW lxR
  rw [if_neg (fun h' => h h'.1)]

/- English proof (translation)
Rewrite using `[lx_weight_mapDomain]`. Unfold `Formalism.BranchingDeterminantCap.omg`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[lx_lxW_R]`. Unfold `Formalism.BranchingDeterminantCap.zW`. Distinguish the cases in `h : v.1 = Fin.last n`. Simplify using `only [if_pos h, Pi.single_apply]`. Rewrite using `[Finset.sum_eq_single v.2]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Introduce `s _ hs`. Simplify using `[hs]`. Simplify using the standard rewrite rules.

Simplify using `[if_neg h]`.
-/
theorem lx_omg (τ : ι) (m : Fin (n + 1) × Fin n →₀ ℕ) :
    (((Finsupp.weight (lxW hN τ) (Finsupp.mapDomain (lxR hN τ) m) : ℕ) : ℤ)) =
      Formalism.BranchingDeterminantCap.omg (Finsupp.weight (Formalism.BranchingDeterminantCap.zW n) m) := by
  classical
  rw [lx_weight_mapDomain]
  unfold Formalism.BranchingDeterminantCap.omg
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [lx_lxW_R]
  unfold Formalism.BranchingDeterminantCap.zW
  by_cases h : v.1 = Fin.last n
  · simp only [if_pos h, Pi.single_apply]
    rw [Finset.sum_eq_single v.2]
    · simp; ring
    · intro s _ hs; simp [hs]
    · simp
  · simp [if_neg h]

/- English proof (translation)
Introduce `M hM`. Rewrite `hM` using `[support_rename_of_injective (lxR_inj hN τ)]`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.1 hM`. Rewrite using `[lx_omg]`. Conclude with `hL m hm`.
-/
theorem lx_low_of (τ : ι) (D : ℤ) (L : MvPolynomial (Fin (n + 1) × Fin n) K) (hL : Formalism.BranchingDeterminantCap.IsLow D L) :
    LxLow hN τ D (rename (lxR hN τ) L) := by
  classical
  intro M hM
  rw [support_rename_of_injective (lxR_inj hN τ)] at hM
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hM
  rw [lx_omg]
  exact hL m hm

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_single_index (h := fun i c => c • w i) (zero_smul _ _)]`.
-/
theorem lx_w_single {β M : Type} [AddCommMonoid M] (w : β → M) (v : β) (c : ℕ) :
    Finsupp.weight w (Finsupp.single v c) = c • w v := by
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (h := fun i c => c • w i) (zero_smul _ _)]

/- English proof (translation)
Unfold `lxW`. Rewrite using `[if_pos ⟨rfl, rfl⟩]`. Both sides reduce to the same expression.
-/
theorem lx_lxW_top (τ : ι) (s : Fin n) : lxW hN τ (τ, iL hN, iC hN s) = s.val + 1 := by
  unfold lxW
  rw [if_pos ⟨rfl, rfl⟩]
  rfl

/- English proof (translation)
Unfold `lxW`. Rewrite using `[if_neg (fun h' => h h'.1)]`.
-/
theorem lx_lxW_other {τ τ' : ι} (h : τ' ≠ τ) (a s : Fin N) : lxW hN τ (τ', a, s) = 0 := by
  unfold lxW
  rw [if_neg (fun h' => h h'.1)]

/- English proof (translation)
Rewrite using `[map_add, lx_weight_mapDomain]`. Establish `h0 : Finsupp.weight (lxW hN τ ∘ upVar hN) m' = 0`. Establish `: (lxW hN τ ∘ upVar hN) = 0`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp_apply, Pi.zero_apply]`.

Unfold `lxW`. Use `split_ifs with h`. Conclude with `absurd h.2 (lx_iC_ne_iL hN v.2.1)`. Both sides reduce to the same expression. Rewrite using `[this]`.

Rewrite using `[Finsupp.weight_apply]`. Unfold `Finsupp.sum`. Conclude with `Finset.sum_eq_zero fun _ _ => smul_zero _`. Rewrite using `[h0, zero_add]`. Unfold `zExp Formalism.BranchingDeterminantCap.omg`.

Simplify using `only [map_sum, lx_w_single, Nat.cast_sum]`. Rewrite using `[Finset.sum_eq_single τ]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[lx_lxW_top, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `τ' _ hτ`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[lx_lxW_other hN hτ, smul_zero, Nat.cast_zero]`. Simplify using the standard rewrite rules.
-/
theorem weight_monomial_shift_eq_omega (b : ι → Fin n → ℕ) (τ : ι) (m' : ι × Fin n × Fin n →₀ ℕ) :
    ((Finsupp.weight (lxW hN τ) (Finsupp.mapDomain (upVar hN) m' + zExp hN b) : ℕ) : ℤ) =
      Formalism.BranchingDeterminantCap.omg (fun s => (b τ s : ℤ)) := by
  classical
  rw [map_add, lx_weight_mapDomain]
  have h0 : Finsupp.weight (lxW hN τ ∘ upVar hN) m' = 0 := by
    have : (lxW hN τ ∘ upVar hN) = 0 := by
      funext v
      simp only [Function.comp_apply, Pi.zero_apply]
      unfold lxW
      split_ifs with h
      · exact absurd h.2 (lx_iC_ne_iL hN v.2.1)
      · rfl
    rw [this]
    rw [Finsupp.weight_apply]
    unfold Finsupp.sum
    exact Finset.sum_eq_zero fun _ _ => smul_zero _
  rw [h0, zero_add]
  unfold zExp Formalism.BranchingDeterminantCap.omg
  simp only [map_sum, lx_w_single, Nat.cast_sum]
  rw [Finset.sum_eq_single τ]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [lx_lxW_top, smul_eq_mul]
    push_cast
    ring
  · intro τ' _ hτ
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [lx_lxW_other hN hτ, smul_zero, Nat.cast_zero]
  · simp

end Ten

section Assembly

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[rename_rename]`. Both sides reduce to the same expression.
-/
theorem lx_blockEmb_rename (τ : ι) (p : MvPolynomial (Fin (n + 1) × Fin n) K) :
    Formalism.GradedWeylDivisibility.blockEmb K τ (rename (lxRho hN) p) = rename (lxR hN τ) p := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  rw [rename_rename]
  rfl

/- English proof (translation)
The claim follows from `Fin.ext (by simp [iL])`.
-/
theorem lx_cast_last : Fin.cast hN.symm (Fin.last n) = iL hN := Fin.ext (by simp [iL])

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.zmon`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, rename_X]`. Simplify using `only [lxR, lxRho, lx_cast_last hN]`.
-/
theorem lx_rename_zmon (τ : ι) (c : Fin n → ℕ) :
    rename (lxR hN τ) (Formalism.BranchingDeterminantCap.zmon K n c) = ∏ s : Fin n, (X (τ, iL hN, iC hN s) : Pol K ι N) ^ c s := by
  unfold Formalism.BranchingDeterminantCap.zmon
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rename_X]
  simp only [lxR, lxRho, lx_cast_last hN]

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.emb upperParabolic Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[rename_rename, rename_rename]`. Conclude with `congrArg (fun F => rename F f) (funext fun v => Prod.ext rfl (Prod.ext (Fin.ext rfl) rfl))`.
-/
theorem lx_rename_emb (τ : ι) (f : MvPolynomial (Fin n × Fin n) K) :
    rename (lxR hN τ) (Formalism.BranchingDeterminantCap.emb K n f) = upperParabolic hN (Formalism.GradedWeylDivisibility.blockEmb K τ f) := by
  unfold Formalism.BranchingDeterminantCap.emb upperParabolic Formalism.GradedWeylDivisibility.blockEmb
  rw [rename_rename, rename_rename]
  exact congrArg (fun F => rename F f) (funext fun v => Prod.ext rfl (Prod.ext (Fin.ext rfl) rfl))

/- English proof (translation)
Unfold `zExp`. Rewrite using `[monomial_sum_one]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[monomial_sum_one]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[X_pow_eq_monomial]`.
-/
theorem lx_zExp_prod (b : ι → Fin n → ℕ) :
    (monomial (zExp hN b) (1 : K)) = ∏ τ, ∏ s : Fin n, (X (τ, iL hN, iC hN s) : Pol K ι N) ^ b τ s := by
  unfold zExp
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [X_pow_eq_monomial]

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod t (fun τ => rename (lxR hN τ) (p τ)) (fun _ => (0 : ℕ)) (fun τ hτ => rename_weightedHomogeneous_zero hN (lxR hN τ) τ0 (fun v => lx_lxW_R_ne hN (fun (h : τ = τ0) => ht (h ▸ hτ)) v) (p τ))`. Simplify using `using h`.
-/
theorem prod_rename_weightedHomogeneous_zero (τ0 : ι) (t : Finset ι) (ht : τ0 ∉ t) (p : ι → MvPolynomial (Fin (n + 1) × Fin n) K) :
    IsWeightedHomogeneous (lxW hN τ0) (∏ τ ∈ t, rename (lxR hN τ) (p τ)) 0 := by
  have h := IsWeightedHomogeneous.prod t (fun τ => rename (lxR hN τ) (p τ)) (fun _ => (0 : ℕ))
    (fun τ hτ => rename_weightedHomogeneous_zero hN (lxR hN τ) τ0 (fun v => lx_lxW_R_ne hN (fun (h : τ = τ0) => ht (h ▸ hτ)) v) (p τ))
  simpa using h

variable (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Unfold `CoefXi`. Establish `hIL : ∀ τ, Formalism.BranchingDeterminantCap.bmIL (lamN hN (lam τ)) (sg τ).natW` using `fun τ => lx_il hN (lam τ) (sg τ) (hI τ) (hS τ)`. Establish `hb : ∀ τ s, bExp hN lam sg τ s = lamN hN (lam τ) s - (sg τ).natW s` using `fun τ s => lx_expB hN (lam τ) (sg τ) (hI τ) (hS τ) s`. Set `Z : ι → MvPolynomial (Fin (n + 1) × Fin n) K` to `fun τ => Formalism.BranchingDeterminantCap.zmon K n (fun s => lamN hN (lam τ) s - (sg τ).natW s)`. Set `E : ι → MvPolynomial (Fin (n + 1) × Fin n) K` to `fun τ => Formalism.BranchingDeterminantCap.emb K n (extremal K n (sg τ))`.

Set `G : ι → MvPolynomial (Fin (n + 1) × Fin n) K` to `fun τ => Formalism.BranchingDeterminantCap.xiB K (lamN hN (lam τ)) (sg τ).natW`. Set `A : ι → Pol K ι N` to `fun τ => rename (lxR hN τ) (Z τ * E τ)`. Set `L : ι → Pol K ι N` to `fun τ => rename (lxR hN τ) (G τ - Z τ * E τ)`. Establish `hlow : ∀ τ, LxLow hN τ (Formalism.BranchingDeterminantCap.omg fun s => ((bExp hN lam sg τ s : ℕ) : ℤ)) (L τ)`. Introduce `τ`.

Establish `h` using `(Formalism.BranchingDeterminantCap.bmLift_xi (R := K) (lamN hN (lam τ)) (sg τ).natW (hIL τ)).2.2`. Establish `e : Formalism.BranchingDeterminantCap.omg (fun s => ((bExp hN lam sg τ s : ℕ) : ℤ)) = Formalism.BranchingDeterminantCap.omg (fun s => (((lamN hN (lam τ) s - (sg τ).natW s : ℕ)) : ℤ))`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[hb]`.

Rewrite using `[e]`. Conclude with `lx_low_of hN τ _ _ h`. Establish `hsplit : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (xiBr K hN (lam τ) (sg τ)) = A τ + L τ`. Introduce `τ`. Rewrite using `[← lx_xi_rename hN (lam τ) (sg τ) (hI τ) (hS τ), lx_blockEmb_rename]`.

Simplify using `only [A, L, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxi : xiTen hN K lam sg = ∏ τ, (A τ + L τ)`. Unfold `xiTen ten`. Conclude with `Finset.prod_congr rfl fun τ _ => hsplit τ`.

Establish `hA : ∏ τ, A τ = monomial (zExp hN (bExp hN lam sg)) (1 : K) * upperParabolic hN (hTen K sg)`. Simplify using `only [A, Z, E, map_mul, Finset.prod_mul_distrib, lx_rename_zmon, lx_rename_emb]`. Rewrite using `[lx_zExp_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hb]`. Unfold `hTen ten`. Rewrite using `[map_prod]`. Rewrite using `[hxi, Finset.prod_add, map_sum, Finset.sum_eq_single Finset.univ]`. Rewrite using `[Finset.sdiff_self, Finset.prod_empty, mul_one, hA, lx_coefLast_raise]`.

Introduce `t _ ht`. Choose the witnesses or unpack the hypotheses as in `⟨τ0, hτ0⟩ : ∃ τ0, τ0 ∉ t := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `ht (Finset.eq_univ_of_forall h)`.

Use extensionality with `m'`. Rewrite using `[lx_coeff_coefLast, coeff_zero]`. Use `lx_coeff_low hN (τ := τ0) ?_ _ (weight_monomial_shift_eq_omega hN (bExp hN lam sg) τ0 m')` and prove the remaining obligations. Establish `hmem : τ0 ∈ Finset.univ \ t` using `by simp [hτ0]`. Rewrite using `[← Finset.mul_prod_erase _ _ hmem, mul_left_comm]`.

Use `lx_low_mul hN (hlow τ0) ?_` and prove the remaining obligations. Establish `h1` using `prod_rename_weightedHomogeneous_zero hN τ0 t hτ0 (fun τ => Z τ * E τ)`. Establish `h2` using `prod_rename_weightedHomogeneous_zero hN τ0 ((Finset.univ \ t).erase τ0) (by simp) (fun τ => G τ - Z τ * E τ)`. Establish `h3` using `h1.mul h2`. Rewrite `h3` using `[zero_add]`.

Conclude with `h3`. Introduce `h`. Conclude with `absurd (Finset.mem_powerset.2 (Finset.Subset.refl _)) h`.
-/
theorem coefXi_of (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg) : CoefXi hN lam sg K := by
  classical
  unfold CoefXi
  have hIL : ∀ τ, Formalism.BranchingDeterminantCap.bmIL (lamN hN (lam τ)) (sg τ).natW := fun τ => lx_il hN (lam τ) (sg τ) (hI τ) (hS τ)
  have hb : ∀ τ s, bExp hN lam sg τ s = lamN hN (lam τ) s - (sg τ).natW s :=
    fun τ s => lx_expB hN (lam τ) (sg τ) (hI τ) (hS τ) s
  let Z : ι → MvPolynomial (Fin (n + 1) × Fin n) K :=
    fun τ => Formalism.BranchingDeterminantCap.zmon K n (fun s => lamN hN (lam τ) s - (sg τ).natW s)
  let E : ι → MvPolynomial (Fin (n + 1) × Fin n) K := fun τ => Formalism.BranchingDeterminantCap.emb K n (extremal K n (sg τ))
  let G : ι → MvPolynomial (Fin (n + 1) × Fin n) K := fun τ => Formalism.BranchingDeterminantCap.xiB K (lamN hN (lam τ)) (sg τ).natW
  let A : ι → Pol K ι N := fun τ => rename (lxR hN τ) (Z τ * E τ)
  let L : ι → Pol K ι N := fun τ => rename (lxR hN τ) (G τ - Z τ * E τ)
  have hlow : ∀ τ, LxLow hN τ (Formalism.BranchingDeterminantCap.omg fun s => ((bExp hN lam sg τ s : ℕ) : ℤ)) (L τ) := by
    intro τ
    have h := (Formalism.BranchingDeterminantCap.bmLift_xi (R := K) (lamN hN (lam τ)) (sg τ).natW (hIL τ)).2.2
    have e : Formalism.BranchingDeterminantCap.omg (fun s => ((bExp hN lam sg τ s : ℕ) : ℤ)) =
        Formalism.BranchingDeterminantCap.omg (fun s => (((lamN hN (lam τ) s - (sg τ).natW s : ℕ)) : ℤ)) := by
      congr 1
      funext s
      rw [hb]
    rw [e]
    exact lx_low_of hN τ _ _ h
  have hsplit : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (xiBr K hN (lam τ) (sg τ)) = A τ + L τ := by
    intro τ
    rw [← lx_xi_rename hN (lam τ) (sg τ) (hI τ) (hS τ), lx_blockEmb_rename]
    simp only [A, L, map_sub]
    ring
  have hxi : xiTen hN K lam sg = ∏ τ, (A τ + L τ) := by
    unfold xiTen ten
    exact Finset.prod_congr rfl fun τ _ => hsplit τ
  have hA : ∏ τ, A τ = monomial (zExp hN (bExp hN lam sg)) (1 : K) * upperParabolic hN (hTen K sg) := by
    simp only [A, Z, E, map_mul, Finset.prod_mul_distrib, lx_rename_zmon, lx_rename_emb]
    rw [lx_zExp_prod]
    congr 1
    · refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
      rw [hb]
    · unfold hTen ten
      rw [map_prod]
  rw [hxi, Finset.prod_add, map_sum, Finset.sum_eq_single Finset.univ]
  · rw [Finset.sdiff_self, Finset.prod_empty, mul_one, hA, lx_coefLast_raise]
  · intro t _ ht
    obtain ⟨τ0, hτ0⟩ : ∃ τ0, τ0 ∉ t := by
      by_contra h
      push Not at h
      exact ht (Finset.eq_univ_of_forall h)
    ext m'
    rw [lx_coeff_coefLast, coeff_zero]
    refine lx_coeff_low hN (τ := τ0) ?_ _ (weight_monomial_shift_eq_omega hN (bExp hN lam sg) τ0 m')
    have hmem : τ0 ∈ Finset.univ \ t := by simp [hτ0]
    rw [← Finset.mul_prod_erase _ _ hmem, mul_left_comm]
    refine lx_low_mul hN (hlow τ0) ?_
    have h1 := prod_rename_weightedHomogeneous_zero hN τ0 t hτ0 (fun τ => Z τ * E τ)
    have h2 := prod_rename_weightedHomogeneous_zero hN τ0 ((Finset.univ \ t).erase τ0) (by simp) (fun τ => G τ - Z τ * E τ)
    have h3 := h1.mul h2
    rw [zero_add] at h3
    exact h3
  · intro h
    exact absurd (Finset.mem_powerset.2 (Finset.Subset.refl _)) h

end Assembly

section Const

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

def lxLamF (lam : DomWeight N) : Fin (n + 1) → ℤ := fun a => lam.w (Fin.cast hN.symm a)

/- English proof (translation)
The claim follows from `congrArg lam.w (Fin.ext rfl)`.
-/
theorem lx_lamF_castSucc (lam : DomWeight N) (i : Fin n) : lxLamF hN lam i.castSucc = lam.w (iC hN i) :=
  congrArg lam.w (Fin.ext rfl)

/- English proof (translation)
The claim follows from `congrArg lam.w (Fin.ext rfl)`.
-/
theorem lx_lamF_succ (lam : DomWeight N) (i : Fin n) : lxLamF hN lam i.succ = lam.w (iS hN i) :=
  congrArg lam.w (Fin.ext rfl)

/- English proof (translation)
Establish `hd : Formalism.BranchingDeterminantCap.d0 (lxLamF hN lam) sg.w = d0 hN lam sg`. Unfold `Formalism.BranchingDeterminantCap.d0 d0 aBr`. Simplify using `only [lx_lamF_succ]`. Unfold `cBr Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig rSet Formalism.BranchingDeterminantCap.rset`. Simplify using `only [lx_lamF_castSucc, lx_lamF_succ, hd]`.

Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cBr_eq_cCap (lam : DomWeight N) (sg : DomWeight n) : cBr hN lam sg = Formalism.BranchingDeterminantCap.cCap (lxLamF hN lam) sg.w := by
  have hd : Formalism.BranchingDeterminantCap.d0 (lxLamF hN lam) sg.w = d0 hN lam sg := by
    unfold Formalism.BranchingDeterminantCap.d0 d0 aBr
    simp only [lx_lamF_succ]
  unfold cBr Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig rSet Formalism.BranchingDeterminantCap.rset
  simp only [lx_lamF_castSucc, lx_lamF_succ, hd]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[cBr_eq_cCap]`. Use `(Formalism.BranchingDeterminantCap.capacity_constant_bound n _ _ fun i => ?_).1` and prove the remaining obligations. Establish `h` using `hI i`. Unfold `aBr bBr at h`. Rewrite using `[lx_lamF_castSucc, lx_lamF_succ]`.

Apply the tactic sequence `constructor <;> omega`.
-/
theorem cBr_ne_zero (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace hN lam sg) : cBr hN lam sg ≠ 0 := by
  rw [cBr_eq_cCap]
  refine (Formalism.BranchingDeterminantCap.capacity_constant_bound n _ _ fun i => ?_).1
  have h := hI i
  unfold aBr bBr at h
  rw [lx_lamF_castSucc, lx_lamF_succ]
  constructor <;> omega

variable (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Establish `h` using `coefXi_of (K := K) hN lam sg hI hS`. Unfold `CoefXi at h`. Simplify using `only [brStdP, LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[h]`.
-/
theorem branchingProjection_xiTensor (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg) :
    brStdP hN lam sg (xiTen hN K lam sg) = brConst hN K lam sg • projVV sg (hTen K sg) := by
  have h := coefXi_of (K := K) hN lam sg hI hS
  unfold CoefXi at h
  simp only [brStdP, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [h]

end Const

section Open

variable (K : Type) [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

def XiTenMem : Prop := xiTen hN K lam sg ∈ VV K lam

def ProjFixesH : Prop := (projVV sg (hTen K sg) : Pol K ι n) = hTen K sg

end Open

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Mem

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat ten`. Conclude with `Submodule.subset_span ⟨f, hf, rfl⟩`.
-/
theorem lm_ten_mem {k : ℕ} (lam : ι → DomWeight k) (f : ι → MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ τ, f τ ∈ nablaSq K k (lam τ)) : ten f ∈ VV K lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat ten
  exact Submodule.subset_span ⟨f, hf, rfl⟩

/- English proof (translation)
Unfold `extremal nablaSq`. Conclude with `Formalism.GradedWeylDivisibility.hwMem K k k le_rfl l.natW (natW_antitone l)`.
-/
theorem lm_extremal_mem {k : ℕ} (l : DomWeight k) : extremal K k l ∈ nablaSq K k l := by
  unfold extremal nablaSq
  exact Formalism.GradedWeylDivisibility.hwMem K k k le_rfl l.natW (natW_antitone l)

/- English proof (translation)
The claim follows from `lm_ten_mem sg _ fun τ => lm_extremal_mem (sg τ)`.
-/
theorem hTen_mem (sg : ι → DomWeight n) : hTen K sg ∈ VV K sg :=
  lm_ten_mem sg _ fun τ => lm_extremal_mem (sg τ)

def lmExt : (Fin n → ℕ) →+ (Fin N → ℕ) where
  toFun w a := if h : a.val < n then w ⟨a.val, h⟩ else 0
  map_zero' := by funext a; simp
  map_add' w w' := by funext a; simp only [Pi.add_apply]; split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [Formalism.GradedWeylDivisibility.colW, lxRho, lmExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Use `split_ifs with h`. Simplify using `only [Pi.single_apply]`. Use `congr 1`.

Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `e; subst e; exact Fin.ext (by simp [iC])`. Introduce `e; exact Fin.ext (by rw [← e]; simp [iC])`. Rewrite using `[Pi.single_apply, if_neg]`.

Introduce `e`. Apply `h` to reduce the goal to its premises. Rewrite using `[e]`. Simplify using `[iC]`.
-/
theorem lm_colW (v : Fin (n + 1) × Fin n) :
    Formalism.GradedWeylDivisibility.colW N N (lxRho hN v) = lmExt (N := N) (Formalism.GradedWeylDivisibility.colW (n + 1) n v) := by
  funext a
  simp only [Formalism.GradedWeylDivisibility.colW, lxRho, lmExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · simp only [Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro e; subst e; exact Fin.ext (by simp [iC])
    · intro e; exact Fin.ext (by rw [← e]; simp [iC])
  · rw [Pi.single_apply, if_neg]
    intro e
    apply h
    rw [e]
    simp [iC]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]`. Both sides reduce to the same expression.
-/
theorem lm_weight_map (w : Fin N × Fin N → (Fin N → ℕ)) (m : Fin (n + 1) × Fin n →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain (lxRho hN) m) = Finsupp.weight (w ∘ lxRho hN) m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
  rfl

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, Function.comp_apply, lm_colW]`.
-/
theorem lm_weight_ext (m : Fin (n + 1) × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N ∘ lxRho hN) m = lmExt (N := N) (Finsupp.weight (Formalism.GradedWeylDivisibility.colW (n + 1) n) m) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_nsmul, Function.comp_apply, lm_colW]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [lmExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lamN, DomWeight.natW]`. Use `split_ifs with h`. Use `congr 2`. Establish `ha : a = iL hN` using `Fin.ext (by simp [iL]; have := a.2; omega)`.

Rewrite using `[ha, lx_detShift_N hN lam]`. Simplify using the standard rewrite rules.
-/
theorem lm_natW (lam : DomWeight N) : lmExt (N := N) (lamN hN lam) = lam.natW := by
  funext a
  simp only [lmExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lamN, DomWeight.natW]
  split_ifs with h
  · congr 2
  · have ha : a = iL hN := Fin.ext (by simp [iL]; have := a.2; omega)
    rw [ha, lx_detShift_N hN lam]
    simp

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]`. Establish `hj : (lxRho hN v).2 = iC hN j' ↔ v.2 = j'` using `⟨fun h => iC_inj hN h, fun h => by rw [← h]; rfl⟩`. Distinguish the cases in `h : v.2 = j'`.

Rewrite using `[if_pos (hj.2 h), if_pos h]`. Simplify using `[rename_X, lxRho]`. Rewrite using `[if_neg (fun h' => h (hj.1 h')), if_neg h]`. Simplify using `[rename_X]`.
-/
theorem lm_colAdd (l' j' : Fin n) :
    (Formalism.GradedWeylDivisibility.colAddGen K (r := N) (iC hN l') (iC hN j')).comp (rename (lxRho hN)) =
      (rename (Option.map (lxRho hN))).comp (Formalism.GradedWeylDivisibility.colAddGen K (r := n + 1) l' j') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
  have hj : (lxRho hN v).2 = iC hN j' ↔ v.2 = j' := ⟨fun h => iC_inj hN h, fun h => by rw [← h]; rfl⟩
  by_cases h : v.2 = j'
  · rw [if_pos (hj.2 h), if_pos h]
    simp [rename_X, lxRho]
  · rw [if_neg (fun h' => h (hj.1 h')), if_neg h]
    simp [rename_X]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]`. Rewrite using `[if_neg]`. Conclude with `lx_iC_ne_iL hN v.2`.
-/
theorem lm_colAdd_last (l : Fin N) :
    (Formalism.GradedWeylDivisibility.colAddGen K (r := N) l (iL hN)).comp (rename (lxRho hN)) =
      (rename (some : Fin N × Fin N → Option (Fin N × Fin N))).comp (rename (lxRho hN)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
  rw [if_neg]
  exact lx_iC_ne_iL hN v.2

/- English proof (translation)
Unfold `nablaSq`. Rewrite `hG`, the goal using `[Formalism.GradedWeylDivisibility.mem_dualWeyl_iff]`. Use `⟨?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Introduce `m hm`. Rewrite using `[← lm_natW hN lam]`.

Choose the witnesses or unpack the hypotheses as in `⟨m', hm', rfl⟩ : ∃ m' ∈ G.support, Finsupp.mapDomain (lxRho hN) m' = m := by`. Use `support_rename_of_injective (lxRho_inj hN) (p := G)` as an intermediate fact. Establish `hm2 : m ∈ (rename (lxRho hN) G).support` using `mem_support_iff.mpr hm`. Rewrite `hm2` using `[this, Finset.mem_image]`. Conclude with `hm2`.

Rewrite using `[lm_weight_map, lm_weight_ext, hG.1 (mem_support_iff.mp hm')]`. Distinguish the cases in `hj : j = iL hN`. Substitute `hj` using the available equality. Use `congrArg (fun φ => φ G) (lm_colAdd_last hN (K := K) l)` as an intermediate fact. Simplify `this` using `[AlgHom.comp_apply, rename_rename]`.

Take `⟨j', rfl⟩` from `lx_eq_iC_of_ne hN j hj`. Establish `hl : l ≠ iL hN`. Introduce `e`. Substitute `e` using the available equality. Establish `h1` using `Fin.lt_def.mp hlj`.

Establish `h2 : (iC hN j').val = j'.val` using `rfl`. Establish `h3 : (iL hN).val = n` using `rfl`. Establish `h4` using `j'.2`. Use linear arithmetic over natural numbers and integers. Take `⟨l', rfl⟩` from `lx_eq_iC_of_ne hN l hl`.

Establish `hlj' : l' < j'` using `Fin.lt_def.mpr (Fin.lt_def.mp hlj)`. Establish `h1` using `congrArg (fun φ => φ G) (lm_colAdd hN (K := K) l' j')`. Simplify using `only [AlgHom.comp_apply] at h1`. Rewrite using `[h1, hG.2 l' j' hlj', rename_rename, rename_rename]`. Both sides reduce to the same expression.
-/
theorem lm_rename_mem (lam : DomWeight N) (G : MvPolynomial (Fin (n + 1) × Fin n) K)
    (hG : G ∈ Formalism.GradedWeylDivisibility.dualWeyl K (n + 1) n (lamN hN lam)) : rename (lxRho hN) G ∈ nablaSq K N lam := by
  unfold nablaSq
  rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hG ⊢
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro m hm
    rw [← lm_natW hN lam]
    obtain ⟨m', hm', rfl⟩ : ∃ m' ∈ G.support, Finsupp.mapDomain (lxRho hN) m' = m := by
      have := support_rename_of_injective (lxRho_inj hN) (p := G)
      have hm2 : m ∈ (rename (lxRho hN) G).support := mem_support_iff.mpr hm
      rw [this, Finset.mem_image] at hm2
      exact hm2
    rw [lm_weight_map, lm_weight_ext, hG.1 (mem_support_iff.mp hm')]
  · by_cases hj : j = iL hN
    · subst hj
      have := congrArg (fun φ => φ G) (lm_colAdd_last hN (K := K) l)
      simpa [AlgHom.comp_apply, rename_rename] using this
    · obtain ⟨j', rfl⟩ := lx_eq_iC_of_ne hN j hj
      have hl : l ≠ iL hN := by
        intro e; subst e
        have h1 := Fin.lt_def.mp hlj
        have h2 : (iC hN j').val = j'.val := rfl
        have h3 : (iL hN).val = n := rfl
        have h4 := j'.2
        omega
      obtain ⟨l', rfl⟩ := lx_eq_iC_of_ne hN l hl
      have hlj' : l' < j' := Fin.lt_def.mpr (Fin.lt_def.mp hlj)
      have h1 := congrArg (fun φ => φ G) (lm_colAdd hN (K := K) l' j')
      simp only [AlgHom.comp_apply] at h1
      rw [h1, hG.2 l' j' hlj', rename_rename, rename_rename]
      rfl

/- English proof (translation)
Rewrite using `[← lx_xi_rename hN lam sg hI hS]`. Conclude with `lm_rename_mem hN lam _ (Formalism.BranchingDeterminantCap.bmLift_xi (R := K) _ _ (lx_il hN lam sg hI hS)).1`.
-/
theorem xiBr_mem (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace hN lam sg) (hS : SameShift lam sg) :
    xiBr K hN lam sg ∈ nablaSq K N lam := by
  rw [← lx_xi_rename hN lam sg hI hS]
  exact lm_rename_mem hN lam _ (Formalism.BranchingDeterminantCap.bmLift_xi (R := K) _ _ (lx_il hN lam sg hI hS)).1

/- English proof (translation)
The claim follows from `lm_ten_mem lam _ fun τ => xiBr_mem hN (lam τ) (sg τ) (hI τ) (hS τ)`.
-/
theorem xiTen_mem (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : InterlaceAll hN lam sg)
    (hS : SameShiftAll lam sg) : XiTenMem K hN lam sg :=
  lm_ten_mem lam _ fun τ => xiBr_mem hN (lam τ) (sg τ) (hI τ) (hS τ)

end Mem

section NonVanish

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Unfold `fockB`. Take `⟨m, hm⟩ : f.support.Nonempty` from `Finset.nonempty_iff_ne_empty.mpr (fun h => hf (support_eq_empty.mp h))`. Use `Finset.sum_pos (fun x hx => ?_) ⟨m, hm⟩` and prove the remaining obligations. Establish `hc : f.coeff x ≠ 0` using `mem_support_iff.mp hx`. Establish `h1 : 0 < f.coeff x * f.coeff x` using `mul_self_pos.mpr hc`.

Establish `h2 : (0 : ℚ) < (mfact x : ℚ)`. Establish `: 0 < mfact x` using `by unfold mfact; exact Finset.prod_pos fun _ _ => Nat.factorial_pos _`. Conclude with `this` after adjusting the coercions. Conclude with `mul_pos h1 h2`.
-/
theorem lm_fockB_pos {σ : Type} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockB f f := by
  unfold fockB
  obtain ⟨m, hm⟩ : f.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hf (support_eq_empty.mp h))
  refine Finset.sum_pos (fun x hx => ?_) ⟨m, hm⟩
  have hc : f.coeff x ≠ 0 := mem_support_iff.mp hx
  have h1 : 0 < f.coeff x * f.coeff x := mul_self_pos.mpr hc
  have h2 : (0 : ℚ) < (mfact x : ℚ) := by
    have : 0 < mfact x := by unfold mfact; exact Finset.prod_pos fun _ _ => Nat.factorial_pos _
    exact_mod_cast this
  exact mul_pos h1 h2

/- English proof (translation)
Rewrite using `[lb_fockB_map]`. Conclude with `(map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr (lm_fockB_pos f hf).ne'`.
-/
theorem lm_fockB_ne [CharZero K] {σ : Type} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    fockB (map (algebraMap ℚ K) f) (map (algebraMap ℚ K) f) ≠ 0 := by
  rw [lb_fockB_map]
  exact (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr (lm_fockB_pos f hf).ne'

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.blockEmb`. Introduce `h`. Apply `hf` to reduce the goal to its premises. Establish `hinj : Function.Injective (fun v : Fin k × Fin k => (τ, v))` using `fun a b e => by simpa using e`. Conclude with `rename_injective _ hinj (by rw [h, map_zero])`.
-/
theorem lm_blockEmb_ne {k : ℕ} (τ : ι) (f : MvPolynomial (Fin k × Fin k) K) (hf : f ≠ 0) :
    Formalism.GradedWeylDivisibility.blockEmb K τ f ≠ 0 := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  intro h
  apply hf
  have hinj : Function.Injective (fun v : Fin k × Fin k => (τ, v)) := fun a b e => by simpa using e
  exact rename_injective _ hinj (by rw [h, map_zero])

/- English proof (translation)
Unfold `ten`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => lm_blockEmb_ne τ (f τ) (hf τ)`.
-/
theorem lm_ten_ne {k : ℕ} (f : ι → MvPolynomial (Fin k × Fin k) K) (hf : ∀ τ, f τ ≠ 0) : ten f ≠ 0 := by
  unfold ten
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => lm_blockEmb_ne τ (f τ) (hf τ)

/- English proof (translation)
Unfold `extremal`. Conclude with `Formalism.GradedWeylDivisibility.hwNe K k k le_rfl l.natW`.
-/
theorem lm_extremal_ne {k : ℕ} (l : DomWeight k) : extremal K k l ≠ 0 := by
  unfold extremal
  exact Formalism.GradedWeylDivisibility.hwNe K k k le_rfl l.natW

/- English proof (translation)
The claim follows from `lm_ten_ne _ fun τ => lm_extremal_ne (sg τ)`.
-/
theorem hTen_ne (sg : ι → DomWeight n) : hTen K sg ≠ 0 := lm_ten_ne _ fun τ => lm_extremal_ne (sg τ)

/- English proof (translation)
Introduce `h0`. Establish `hc` using `coefXi_of (K := K) (ι := Unit) hN (fun _ => lam) (fun _ => sg) (fun _ => hI) (fun _ => hS)`. Unfold `CoefXi xiTen at hc`. Establish `hx : ten (fun _ : Unit => xiBr K hN lam sg) = 0`. Unfold `ten`.

Simplify using `[h0]`. Rewrite `hc` using `[hx, map_zero]`. Conclude with `hTen_ne (K := K) (fun _ : Unit => sg) hc.symm`.
-/
theorem xiBr_ne (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace hN lam sg) (hS : SameShift lam sg) :
    xiBr K hN lam sg ≠ 0 := by
  intro h0
  have hc := coefXi_of (K := K) (ι := Unit) hN (fun _ => lam) (fun _ => sg) (fun _ => hI) (fun _ => hS)
  unfold CoefXi xiTen at hc
  have hx : ten (fun _ : Unit => xiBr K hN lam sg) = 0 := by
    unfold ten
    simp [h0]
  rw [hx, map_zero] at hc
  exact hTen_ne (K := K) (fun _ : Unit => sg) hc.symm

/- English proof (translation)
Unfold `kapBr`. Use `div_ne_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[← lb_map_xiBr (algebraMap ℚ K)]`. Conclude with `lm_fockB_ne _ (xiBr_ne hN lam sg hI hS)`. Rewrite using `[← lb_map_extremal (algebraMap ℚ K)]`.

Conclude with `lm_fockB_ne _ (lm_extremal_ne lam)`.
-/
theorem kapBr_ne [CharZero K] (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace hN lam sg) (hS : SameShift lam sg) :
    kapBr K hN lam sg ≠ 0 := by
  unfold kapBr
  refine div_ne_zero ?_ ?_
  · rw [← lb_map_xiBr (algebraMap ℚ K)]
    exact lm_fockB_ne _ (xiBr_ne hN lam sg hI hS)
  · rw [← lb_map_extremal (algebraMap ℚ K)]
    exact lm_fockB_ne _ (lm_extremal_ne lam)

/- English proof (translation)
Unfold `brConst`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (kapBr_ne hN (lam τ) (sg τ) (hI τ) (hS τ))` and prove the remaining obligations. Conclude with `cBr_ne_zero hN (lam τ) (sg τ) (hI τ)` after adjusting the coercions.
-/
theorem brConst_ne [CharZero K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : InterlaceAll hN lam sg)
    (hS : SameShiftAll lam sg) : brConst hN K lam sg ≠ 0 := by
  unfold brConst
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (kapBr_ne hN (lam τ) (sg τ) (hI τ) (hS τ))
  exact_mod_cast cBr_ne_zero hN (lam τ) (sg τ) (hI τ)

/- English proof (translation)
Establish `h1 : brStd hN lam sg ⟨xiTen hN K lam sg, xiTen_mem hN lam sg hI hS⟩ = brStdP hN lam sg (xiTen hN K lam sg)` using `rfl`. Rewrite using `[h1, branchingProjection_xiTensor hN lam sg hI hS, Submodule.coe_smul, lb_proj_unique sg (hTen K sg) (hTen K sg) (hTen_mem sg) fun v _ => rfl]`.
-/
theorem brStd_xiTen [CharZero K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : InterlaceAll hN lam sg)
    (hS : SameShiftAll lam sg) :
    ((brStd hN lam sg ⟨xiTen hN K lam sg, xiTen_mem hN lam sg hI hS⟩ : VV K sg) : Pol K ι n) =
      brConst hN K lam sg • hTen K sg := by
  have h1 : brStd hN lam sg ⟨xiTen hN K lam sg, xiTen_mem hN lam sg hI hS⟩ = brStdP hN lam sg (xiTen hN K lam sg) := rfl
  rw [h1, branchingProjection_xiTensor hN lam sg hI hS, Submodule.coe_smul,
    lb_proj_unique sg (hTen K sg) (hTen K sg) (hTen_mem sg) fun v _ => rfl]

/- English proof (translation)
Introduce `h0`. Use `brStd_xiTen (K := K) hN lam sg hI hS` as an intermediate fact. Rewrite `this` using `[h0, LinearMap.zero_apply, Submodule.coe_zero]`. Conclude with `smul_ne_zero (brConst_ne (K := K) hN lam sg hI hS) (hTen_ne (K := K) sg) this.symm`.
-/
theorem brStd_ne_zero [CharZero K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : InterlaceAll hN lam sg)
    (hS : SameShiftAll lam sg) : brStd (K := K) hN lam sg ≠ 0 := by
  intro h0
  have := brStd_xiTen (K := K) hN lam sg hI hS
  rw [h0, LinearMap.zero_apply, Submodule.coe_zero] at this
  exact smul_ne_zero (brConst_ne (K := K) hN lam sg hI hS) (hTen_ne (K := K) sg) this.symm

end NonVanish

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Inhabit

def periodOf {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (Pt : Type) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → ℂˣ) : PeriodMap R C where
  Mt := ℂ
  Wz := Pt → VV ℂ lam
  evz := 0
  Wrow := Pt → VV ℂ sg
  lowerMap := lowerFn hN lam sg Pt fun τ => (t τ : ℂ)
  period := 0

def lowerShapeOf {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (Pt : Type) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → ℂˣ) :
    LowerShape (periodOf C Pt hN lam sg t) Pt hN lam sg t where
  iz := LinearEquiv.refl ℂ _
  ir := LinearEquiv.refl ℂ _
  comm _ := rfl

def periodTwice {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (Pt : Type) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → ℂˣ) : PeriodMap R C where
  Mt := ℂ
  Wz := Pt → VV ℂ lam
  evz := 0
  Wrow := Pt → VV ℂ sg
  lowerMap := (2 : ℂ) • lowerFn hN lam sg Pt fun τ => (t τ : ℂ)
  period := 0

def lowerShapeTwice {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (Pt : Type) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → ℂˣ) :
    LowerShape (periodTwice C Pt hN lam sg t) Pt hN lam sg t where
  iz := LinearEquiv.refl ℂ _
  ir := LinearEquiv.smulOfNeZero ℂ _ (2⁻¹ : ℂ) (by norm_num)
  comm x := by
    show (2⁻¹ : ℂ) • ((2 : ℂ) • lowerFn hN lam sg Pt (fun τ => (t τ : ℂ)) x) = lowerFn hN lam sg Pt (fun τ => (t τ : ℂ)) x
    rw [smul_smul]; norm_num

end Inhabit

section Small

def wt10 : DomWeight 2 := ⟨![1, 0], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def wt0 : DomWeight 1 := ⟨![0], by intro a b _; fin_cases a; fin_cases b; simp⟩

/- English proof (translation)
Introduce `τ i`. Use `fin_cases i`. Simplify using `[aBr, bBr, wt10, wt0, iC, iS]`.
-/
theorem small_interlace : InterlaceAll (rfl : 2 = 1 + 1) (fun _ : Unit => wt10) (fun _ : Unit => wt0) := by
  intro τ i
  fin_cases i
  simp [aBr, bBr, wt10, wt0, iC, iS]

/- English proof (translation)
Introduce `τ`. Simplify using `[SameShift, DomWeight.detShift, wt10, wt0]`.
-/
theorem small_sameShift : SameShiftAll (fun _ : Unit => wt10) (fun _ : Unit => wt0) := by
  intro τ
  simp [SameShift, DomWeight.detShift, wt10, wt0]

def weightTwoOneZero : DomWeight 3 := ⟨![2, 1, 0], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/- English proof (translation)
Introduce `τ i`. Apply the tactic sequence `fin_cases i <;> simp [aBr, bBr, weightTwoOneZero, wt10, iC, iS]`.
-/
theorem small2_interlace : InterlaceAll (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoOneZero) (fun _ : Unit => wt10) := by
  intro τ i
  fin_cases i <;> simp [aBr, bBr, weightTwoOneZero, wt10, iC, iS]

/- English proof (translation)
Introduce `τ`. Simplify using `[SameShift, DomWeight.detShift, weightTwoOneZero, wt10]`.
-/
theorem small2_sameShift : SameShiftAll (fun _ : Unit => weightTwoOneZero) (fun _ : Unit => wt10) := by
  intro τ
  simp [SameShift, DomWeight.detShift, weightTwoOneZero, wt10]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem small2_cBr : cBr (rfl : 3 = 2 + 1) weightTwoOneZero wt10 = 1 := by
  decide

def weightTwoZeroZero : DomWeight 3 := ⟨![2, 0, 0], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/- English proof (translation)
Introduce `τ i`. Apply the tactic sequence `fin_cases i <;> simp [aBr, bBr, weightTwoZeroZero, wt10, iC, iS]`.
-/
theorem small3_interlace : InterlaceAll (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) := by
  intro τ i
  fin_cases i <;> simp [aBr, bBr, weightTwoZeroZero, wt10, iC, iS]

/- English proof (translation)
Introduce `τ`. Simplify using `[SameShift, DomWeight.detShift, weightTwoZeroZero, wt10]`.
-/
theorem small3_sameShift : SameShiftAll (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) := by
  intro τ
  simp [SameShift, DomWeight.detShift, weightTwoZeroZero, wt10]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem small3_cBr : cBr (rfl : 3 = 2 + 1) weightTwoZeroZero wt10 = -1 := by
  decide

/- English proof (translation)
The claim follows from `coefXi_of rfl _ _ small3_interlace small3_sameShift`.
-/
theorem small3_coefXi : CoefXi (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) ℚ :=
  coefXi_of rfl _ _ small3_interlace small3_sameShift

/- English proof (translation)
The claim follows from `branchingProjection_xiTensor rfl _ _ small3_interlace small3_sameShift`.
-/
theorem small3_brStdP : brStdP (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10)
    (xiTen rfl ℚ (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10)) =
      brConst rfl ℚ (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) • projVV (fun _ : Unit => wt10) (hTen ℚ (fun _ : Unit => wt10)) :=
  branchingProjection_xiTensor rfl _ _ small3_interlace small3_sameShift

/- English proof (translation)
The claim follows from `brStd_ne_zero rfl _ _ small3_interlace small3_sameShift`.
-/
theorem small3_brStd_ne : brStd (K := ℚ) (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) ≠ 0 :=
  brStd_ne_zero rfl _ _ small3_interlace small3_sameShift

end Small

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

/- English proof (translation)
The claim follows from `coefXi_of (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ))`.
-/
theorem chain_coefXi (u : Pr.Word) (hI : ∀ τ, Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ)) :
    CoefXi (N_m_succ R) (W.lamTrue u R.m) W.sgTrue X.K :=
  coefXi_of (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ))

/- English proof (translation)
The claim follows from `brAtTranspose (N_m_succ R) _ _ _ f g`.
-/
theorem chain_brTranspose (u : Pr.Word) (f : VV X.K (W.lamTrue u R.m)) (g : VV X.K W.sgTrue) :
    pairBK W.sgTrue (brC W u f) g =
      pairBK (W.lamTrue u R.m) f
        (ioAt (N_m_succ R) (W.lamTrue u R.m) W.sgTrue (fun τ => X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) g) :=
  brAtTranspose (N_m_succ R) _ _ _ f g

/- English proof (translation)
The claim follows from `brStd_ne_zero (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ))`.
-/
theorem chain_brStd_ne (u : Pr.Word) (hI : ∀ τ, Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ)) :
    brStd (K := X.K) (N_m_succ R) (W.lamTrue u R.m) W.sgTrue ≠ 0 :=
  brStd_ne_zero (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ))

end Chain

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Norm

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Rewrite using `[← brTranspose hN lam sg]`. Rewrite using `[pairBK_apply, pairBK_apply, pairB_apply, pairB_apply]`. Establish `h1 : ((brStd hN lam sg ⟨xiTen hN K lam sg, hξ⟩ : VV K sg) : Pol K ι n) = brConst hN K lam sg • (projVV sg (coefLast hN (bExp hN lam sg) (xiTen hN K lam sg)) : Pol K ι n)`. Simplify using `[brStd, brStdP]`. Establish `hc` using `coefXi_of (K := K) hN lam sg hI hS`.

Unfold `CoefXi at hc`. Rewrite using `[h1, fockB_smul_left', fockB_projVV sg _ _ hh, hc]`. Establish `hA` using `pb_extNormB_ne K sg`. Establish `hL` using `pb_extNormB_ne K lam`. Simplify using `only [hTen, xiTen, sd_fockB_ten]`.

Simplify using `only [extNormB] at hA hL ⊢`. Rewrite using `[brConst]`. Simplify using `only [kapBr, Int.cast_prod, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ioHw_on_xi (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg)
    (hξ : xiTen hN K lam sg ∈ VV K lam) (hh : hTen K sg ∈ VV K sg) :
    pairBK lam ⟨xiTen hN K lam sg, hξ⟩ (ioStd hN lam sg ⟨hTen K sg, hh⟩) =
      ((∏ τ, (cBr hN (lam τ) (sg τ) : ℤ) : ℤ) : K) * pairBK lam ⟨xiTen hN K lam sg, hξ⟩ ⟨xiTen hN K lam sg, hξ⟩ := by
  rw [← brTranspose hN lam sg]
  rw [pairBK_apply, pairBK_apply, pairB_apply, pairB_apply]
  have h1 : ((brStd hN lam sg ⟨xiTen hN K lam sg, hξ⟩ : VV K sg) : Pol K ι n) =
      brConst hN K lam sg • (projVV sg (coefLast hN (bExp hN lam sg) (xiTen hN K lam sg)) : Pol K ι n) := by
    simp [brStd, brStdP]
  have hc := coefXi_of (K := K) hN lam sg hI hS
  unfold CoefXi at hc
  rw [h1, fockB_smul_left', fockB_projVV sg _ _ hh, hc]
  have hA := pb_extNormB_ne K sg
  have hL := pb_extNormB_ne K lam
  simp only [hTen, xiTen, sd_fockB_ten]
  simp only [extNormB] at hA hL ⊢
  rw [brConst]
  simp only [kapBr, Int.cast_prod, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  field_simp

/- English proof (translation)
The claim follows from `projVV_of_mem sg _ hh`.
-/
theorem projFixesH_of (hh : hTen K sg ∈ VV K sg) : ProjFixesH (K := K) sg :=
  projVV_of_mem sg _ hh

end Norm

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section ShiftTr

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Establish `hm` using `R.two_le_m`. Establish `ht` using `R.rank_add_five_le`. Establish `hN : R.N R.m = R.k + R.m * (R.t + 1)` using `rfl`. Take `⟨m', hm'⟩ : ∃ m', R.m = m' + 1` from `⟨R.m - 1, by omega⟩`. Establish `e1 : R.N R.m - 1 - R.k = R.t + m' * (R.t + 1)`.

Rewrite using `[hN, hm']`. Put the polynomial expressions in normal form. Use linear arithmetic over natural numbers and integers. Establish `e2 : R.N R.m - 2 - R.k = (R.t - 1) + m' * (R.t + 1)`. Rewrite using `[hN, hm']`.

Put the polynomial expressions in normal form. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2, Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]`.
-/
theorem blk_last_two (R : Ranks) : (R.N R.m - 1 - R.k) / (R.t + 1) = (R.N R.m - 2 - R.k) / (R.t + 1) := by
  have hm := R.two_le_m
  have ht := R.rank_add_five_le
  have hN : R.N R.m = R.k + R.m * (R.t + 1) := rfl
  obtain ⟨m', hm'⟩ : ∃ m', R.m = m' + 1 := ⟨R.m - 1, by omega⟩
  have e1 : R.N R.m - 1 - R.k = R.t + m' * (R.t + 1) := by
    rw [hN, hm']; ring_nf; omega
  have e2 : R.N R.m - 2 - R.k = (R.t - 1) + m' * (R.t + 1) := by
    rw [hN, hm']; ring_nf; omega
  rw [e1, e2, Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `ht` using `D.R.rank_add_five_le`. Establish `hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1)` using `rfl`. Establish `hmt : 2 * 2 ≤ D.R.m * (D.R.t + 1)` using `Nat.mul_le_mul hm (by omega)`.

Establish `h1` using `(D.fm u).lam_eq D.R.m le_rfl τ i`. Establish `h2` using `(D.fm u).lam_eq D.R.m le_rfl τ j`. Rewrite `h1` using `[dif_neg (by rw [hi, hN]; omega)]`. Rewrite `h2` using `[dif_neg (by rw [hj, hN]; omega)]`. Establish `hb : (i.1 - D.R.k) / (D.R.t + 1) = (j.1 - D.R.k) / (D.R.t + 1)`.

Rewrite using `[hi, hj]`. Conclude with `blk_last_two D.R`. Simplify using `only [hb] at h1`. Conclude with `h1.trans h2.symm` after adjusting the coercions.
-/
theorem lam_last_two (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i j : Fin (D.R.N D.R.m))
    (hi : i.1 = D.R.N D.R.m - 1) (hj : j.1 = D.R.N D.R.m - 2) :
    ((D.fm u).lam D.R.m τ).w i = ((D.fm u).lam D.R.m τ).w j := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have hmt : 2 * 2 ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul hm (by omega)
  have h1 := (D.fm u).lam_eq D.R.m le_rfl τ i
  have h2 := (D.fm u).lam_eq D.R.m le_rfl τ j
  rw [dif_neg (by rw [hi, hN]; omega)] at h1
  rw [dif_neg (by rw [hj, hN]; omega)] at h2
  have hb : (i.1 - D.R.k) / (D.R.t + 1) = (j.1 - D.R.k) / (D.R.t + 1) := by
    rw [hi, hj]; exact blk_last_two D.R
  simp only [hb] at h1
  exact_mod_cast h1.trans h2.symm

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1)` using `rfl`. Establish `hmt : 2 * 2 ≤ D.R.m * (D.R.t + 1)` using `Nat.mul_le_mul hm (by have := D.R.rank_add_five_le; omega)`. Establish `hpos : 0 < D.R.N D.R.m - 1` using `by rw [hN]; omega`.

Establish `hpos' : 0 < D.R.N D.R.m` using `by omega`. Take `⟨ha, hb⟩` from `hI ⟨D.R.N D.R.m - 1 - 1, by omega⟩`. Establish `e` using `lam_last_two D u τ ⟨D.R.N D.R.m - 1 - 1 + 1, by omega⟩ ⟨D.R.N D.R.m - 1 - 1, by omega⟩ (by simp; omega) (by simp; omega)`. Unfold `SameShift DomWeight.detShift`. Rewrite using `[dif_pos hpos, dif_pos hpos']`.

Establish `e2 : (lamTr D u τ).w ⟨D.R.N D.R.m - 1, by omega⟩ = (lamTr D u τ).w ⟨D.R.N D.R.m - 1 - 1 + 1, by omega⟩`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e2]`. Simplify using `only [lamTr, sgTr, wSh] at ha hb ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem sameShiftTr (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ)) :
    SameShift (lamTr D u τ) (sgTr D u τ) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have hmt : 2 * 2 ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul hm (by have := D.R.rank_add_five_le; omega)
  have hpos : 0 < D.R.N D.R.m - 1 := by rw [hN]; omega
  have hpos' : 0 < D.R.N D.R.m := by omega
  obtain ⟨ha, hb⟩ := hI ⟨D.R.N D.R.m - 1 - 1, by omega⟩
  have e := lam_last_two D u τ ⟨D.R.N D.R.m - 1 - 1 + 1, by omega⟩ ⟨D.R.N D.R.m - 1 - 1, by omega⟩
    (by simp; omega) (by simp; omega)
  unfold SameShift DomWeight.detShift
  rw [dif_pos hpos, dif_pos hpos']
  have e2 : (lamTr D u τ).w ⟨D.R.N D.R.m - 1, by omega⟩ = (lamTr D u τ).w ⟨D.R.N D.R.m - 1 - 1 + 1, by omega⟩ := by
    congr 1; ext; simp; omega
  rw [e2]
  simp only [lamTr, sgTr, wSh] at ha hb ⊢
  omega

end ShiftTr

section NZ

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Unfold `brAt`. Conclude with `smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (t τ).ne_zero) (brStd_ne_zero hN lam sg hI hS)`.
-/
theorem brAt_ne_zero (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg) (t : ι → Kˣ) :
    brAt hN lam sg (fun τ => (t τ : K)) ≠ 0 := by
  unfold brAt
  exact smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (t τ).ne_zero) (brStd_ne_zero hN lam sg hI hS)

/- English proof (translation)
Introduce `h0`. Apply `brAt_ne_zero hN lam sg hI hS t` to reduce the goal to its premises. Use `ext1 x`. Use `congrFun (LinearMap.congr_fun h0 (fun _ => x)) (Classical.arbitrary Pt)` as an intermediate fact. Simplify `this` using `[lowerFn]`.
-/
theorem lowerFn_ne_zero (Pt : Type) [Nonempty Pt] (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg) (t : ι → Kˣ) :
    lowerFn hN lam sg Pt (fun τ => (t τ : K)) ≠ 0 := by
  intro h0
  apply brAt_ne_zero hN lam sg hI hS t
  ext1 x
  have := congrFun (LinearMap.congr_fun h0 (fun _ => x)) (Classical.arbitrary Pt)
  simpa [lowerFn] using this

end NZ

section ShapeNe

/- English proof (translation)
Introduce `h0`. Apply `lowerFn_ne_zero hN lam sg Pt hI hS t` to reduce the goal to its premises. Use `ext1 y`. Use `S.comm (S.iz.symm y)` as an intermediate fact. Rewrite `this` using `[h0, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply]`.

Rewrite using `[← this, LinearMap.zero_apply]`.
-/
theorem lowerShape_ne {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {P : PeriodMap R C}
    {Pt : Type} [Nonempty Pt] {N n : ℕ} {hN : N = n + 1} {lam : ι → DomWeight N} {sg : ι → DomWeight n} {t : ι → ℂˣ}
    (S : LowerShape P Pt hN lam sg t) (hI : InterlaceAll hN lam sg) (hS : SameShiftAll lam sg) : P.lowerMap ≠ 0 := by
  intro h0
  apply lowerFn_ne_zero hN lam sg Pt hI hS t
  ext1 y
  have := S.comm (S.iz.symm y)
  rw [h0, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at this
  rw [← this, LinearMap.zero_apply]

/- English proof (translation)
The claim follows from `lowerShape_ne (lowerShapeOf C Unit rfl _ _ _) small3_interlace small3_sameShift`.
-/
theorem small3_lowerMap_ne {R : Ranks} {hc : Unit → HCParam R} (C : ColumnChain R Unit hc) :
    (periodOf C Unit (rfl : 3 = 2 + 1) (fun _ : Unit => weightTwoZeroZero) (fun _ : Unit => wt10) (fun _ => 1)).lowerMap ≠ 0 :=
  lowerShape_ne (lowerShapeOf C Unit rfl _ _ _) small3_interlace small3_sameShift

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

/- English proof (translation)
Establish `hne : ∀ τ, X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)) ≠ 0`. Introduce `τ`. Rewrite using `[Ne, map_eq_zero, star_eq_zero]`. Conclude with `hpi` after adjusting the coercions. Conclude with `brAt_ne_zero (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ)) fun τ => Units.mk0 _ (hne τ)`.
-/
theorem chain_brC_ne (u : Pr.Word) (hpi : Pr.piT u ≠ 0)
    (hI : ∀ τ, Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ)) : brC W u ≠ 0 := by
  have hne : ∀ τ, X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)) ≠ 0 := by
    intro τ
    rw [Ne, map_eq_zero, star_eq_zero]
    exact_mod_cast hpi
  exact brAt_ne_zero (N_m_succ R) _ _ hI (fun τ => sameShift_of_interlace W u τ (hI τ)) fun τ => Units.mk0 _ (hne τ)

end ShapeNe

section Comparison₂

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Take `⟨P, hP⟩` from `h`. Introduce `τ`. Rewrite using `[← hP τ]`. Conclude with `P.beOn_eq τ`.
-/
theorem lowerTie_beOn {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (h : LowerTie D u) : BeOnTie D u := by
  obtain ⟨P, hP⟩ := h
  intro τ
  rw [← hP τ]
  exact P.beOn_eq τ

/- English proof (translation)
Use `P.Pt_eq w φ hφ c` as an intermediate fact. Simplify using `only [hP] at this`. Conclude with `this`.
-/
theorem lowerTie_eval {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (P : Pend D u)
    (hP : ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (w : D.what₂.places.Pl)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    P.coP w ((D.mem u).P.lowerMap ((D.mem u).P.evz φ)) c =
      blk (fun τ => brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (P.coM w c (φ ((D.fm u).til c))) := by
  have := P.Pt_eq w φ hφ c
  simp only [hP] at this
  exact this

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.ten`. Simplify using `only [map_smul]`. Conclude with `Finset.prod_smul _ _ _`.
-/
theorem tensor_smul_univ {n : ℕ} (a : ι → ℂ) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => a τ • g τ) = (∏ τ, a τ) • Formalism.MainNotions.product_first_zeroth_parts.ten g := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  simp only [map_smul]
  exact Finset.prod_smul _ _ _

/- English proof (translation)
Apply `(MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext` to reduce the goal to its premises. Introduce `mon`. Simplify using `only [blk, Module.Basis.constr_basis, LinearMap.smul_apply]`. Conclude with `tensor_smul_univ a _`.
-/
theorem blk_smul {n n' : ℕ} (a : ι → ℂ) (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ) :
    blk (fun τ => ⇑(a τ • F τ)) = (∏ τ, a τ) • blk (fun τ => ⇑(F τ)) := by
  apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
  intro mon
  simp only [blk, Module.Basis.constr_basis, LinearMap.smul_apply]
  exact tensor_smul_univ a _

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using `[Formalism.REAL.fockF]`. Unfold `Formalism.REAL.fockF`. Rewrite using `[MvPolynomial.support_smul_eq hc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [coeff_smul, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_smul_smul {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • p) (c • q) = (c * star c) * Formalism.REAL.fockF p q := by
  by_cases hc : c = 0
  · subst hc; simp [Formalism.REAL.fockF]
  · unfold Formalism.REAL.fockF
    rw [MvPolynomial.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [coeff_smul, smul_eq_mul, star_mul']
    ring

/- English proof (translation)
Establish `h1` using `P.re_petersson_self_eq_sum_coord w _ hz`. Establish `h2` using `P'.re_petersson_self_eq_sum_coord w _ hz`. Establish `e : ∀ c, P'.coP w (Pt D u φ) c = (∏ τ, a τ) • P.coP w (Pt D u φ) c`. Introduce `c`. Rewrite using `[P'.Pt_eq w φ hφ c, P.Pt_eq w φ hφ c, hM]`.

Establish `: (fun τ => ⇑(P'.br τ)) = fun τ => ⇑(a τ • P.br τ)` using `by funext τ; rw [hb τ]`. Rewrite using `[this, blk_smul, LinearMap.smul_apply]`. Simplify using `only [e, hg, map_smul, nfAll, fockF_smul_smul, mul_div_assoc] at h2`. Establish `hn : ((∏ τ, a τ) * star (∏ τ, a τ)) = ((‖∏ τ, a τ‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Simplify using `only [hn, Complex.re_ofReal_mul] at h2`. Simplify using `only [nfAll] at h1`. Establish `h3 : ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = ‖∏ τ, a τ‖ ^ 2 * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re` using `by conv_rhs => rw [h1]`. Rewrite using `[h2, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ‖∏ τ, a τ‖ ^ 2 = 1`. Establish `: (‖∏ τ, a τ‖ ^ 2 - 1) * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = 0` using `by linarith`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `absurd h hne`. Establish `h5 : 0 ≤ ‖∏ τ, a τ‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pend_rigid {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (P P' : Pend D u) (a : D.what₂.Tau → ℂ)
    (hM : P'.coM = P.coM) (hg : P'.gP = P.gP) (hb : ∀ τ, P'.br τ = a τ • P.br τ) (w : D.what₂.places.Pl)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (hz : Pt D u φ ∈ (D.fm u).ptC)
    (hne : ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≠ 0) : ‖∏ τ, a τ‖ = 1 := by
  have h1 := P.re_petersson_self_eq_sum_coord w _ hz
  have h2 := P'.re_petersson_self_eq_sum_coord w _ hz
  have e : ∀ c, P'.coP w (Pt D u φ) c = (∏ τ, a τ) • P.coP w (Pt D u φ) c := by
    intro c
    rw [P'.Pt_eq w φ hφ c, P.Pt_eq w φ hφ c, hM]
    have : (fun τ => ⇑(P'.br τ)) = fun τ => ⇑(a τ • P.br τ) := by funext τ; rw [hb τ]
    rw [this, blk_smul, LinearMap.smul_apply]
  simp only [e, hg, map_smul, nfAll, fockF_smul_smul, mul_div_assoc] at h2
  have hn : ((∏ τ, a τ) * star (∏ τ, a τ)) = ((‖∏ τ, a τ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hn, Complex.re_ofReal_mul] at h2
  simp only [nfAll] at h1
  have h3 : ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = ‖∏ τ, a τ‖ ^ 2 * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re := by
    conv_rhs => rw [h1]
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have h4 : ‖∏ τ, a τ‖ ^ 2 = 1 := by
    have : (‖∏ τ, a τ‖ ^ 2 - 1) * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hne
  have h5 : 0 ≤ ‖∏ τ, a τ‖ := norm_nonneg _
  nlinarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.MainNotions.GlobalTheoryTheory.Inhab.pendJunk D u hE hC hI _ hb, fun _ => rfl⟩`.
-/
theorem lowerTie_of_isEmpty (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace) (hb : BeOnTie D u) : LowerTie D u :=
  ⟨Formalism.MainNotions.GlobalTheoryTheory.Inhab.pendJunk D u hE hC hI _ hb, fun _ => rfl⟩

end Comparison₂

section GlobalTheory

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Simplify using `only [toUnit, ten, Formalism.GradedWeylDivisibility.blockEmb, Finset.univ_unique, Finset.prod_singleton, renameEquiv_apply]`. Both sides reduce to the same expression.
-/
theorem toUnit_eq_ten (k : ℕ) (f : MvPolynomial (Fin k × Fin k) K) : toUnit K k f = ten (fun _ : Unit => f) := by
  simp only [toUnit, ten, Formalism.GradedWeylDivisibility.blockEmb, Finset.univ_unique, Finset.prod_singleton, renameEquiv_apply]
  rfl

def raiseOne (c : Fin n → ℕ) (g : MvPolynomial (Fin n × Fin n) K) : MvPolynomial (Fin N × Fin N) K :=
  (∏ s : Fin n, (X (iL hN, iC hN s) : MvPolynomial (Fin N × Fin N) K) ^ c s) * rename (fun v => (iC hN v.1, iC hN v.2)) g

/- English proof (translation)
Unfold `raise`. Rewrite using `[LinearMap.comp_apply, LinearMap.mulLeft_apply, lx_zExp_prod]`. Unfold `ten`. Rewrite using `[AlgHom.toLinearMap_apply, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Unfold `raiseOne`. Rewrite using `[map_mul, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Simplify using `[Formalism.GradedWeylDivisibility.blockEmb]`. Unfold `upperParabolic Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[rename_rename, rename_rename]`. Both sides reduce to the same expression.
-/
theorem raise_ten (b : ι → Fin n → ℕ) (g : ι → MvPolynomial (Fin n × Fin n) K) :
    raise hN b (ten g) = ten fun τ => raiseOne hN (b τ) (g τ) := by
  unfold raise
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, lx_zExp_prod]
  unfold ten
  rw [AlgHom.toLinearMap_apply, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold raiseOne
  rw [map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow]
    simp [Formalism.GradedWeylDivisibility.blockEmb]
  · unfold upperParabolic Formalism.GradedWeylDivisibility.blockEmb
    rw [rename_rename, rename_rename]
    rfl

/- English proof (translation)
Rewrite using `[fockB_coefLast, raise_ten, sd_fockB_ten]`.
-/
theorem fock_coef_ten (b : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) K) (g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockB (coefLast hN b (ten f)) (ten g) * (bFac b : K) = ∏ τ, fockB (f τ) (raiseOne hN (b τ) (g τ)) := by
  rw [fockB_coefLast, raise_ten, sd_fockB_ten]

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Establish `: (∏ s : Unit, Formalism.GradedWeylDivisibility.blockEmb K s (F s)) = toUnit K n (F ())`.

Rewrite using `[toUnit_eq_ten]`. Unfold `ten`. Simplify using the standard rewrite rules. Rewrite using `[this, AlgEquiv.symm_apply_apply]`. Conclude with `hF ()`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem unit_mem (s : DomWeight n) (y : Pol K Unit n) (hy : y ∈ VV K (fun _ : Unit => s)) :
    (toUnit K n).symm y ∈ nablaSq K n s := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have : (∏ s : Unit, Formalism.GradedWeylDivisibility.blockEmb K s (F s)) = toUnit K n (F ()) := by
      rw [toUnit_eq_ten]; unfold ten; simp
    rw [this, AlgEquiv.symm_apply_apply]
    exact hF ()
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Unfold `ten`. Simplify using `only [map_smul]`. Conclude with `Finset.prod_smul _ _ _`.
-/
theorem tenD_smul {k : ℕ} (a : ι → K) (g : ι → MvPolynomial (Fin k × Fin k) K) :
    ten (fun τ => a τ • g τ) = (∏ τ, a τ) • ten g := by
  unfold ten
  simp only [map_smul]
  exact Finset.prod_smul _ _ _

variable [CharZero K] (sg : ι → DomWeight n)

def prCoefOne (s : DomWeight n) (c : Fin n → ℕ) (F : MvPolynomial (Fin N × Fin N) K) : MvPolynomial (Fin n × Fin n) K :=
  (toUnit K n).symm (projVV (fun _ : Unit => s) (coefLast hN (fun _ : Unit => c) (toUnit K N F)) : Pol K Unit n)

/- English proof (translation)
Apply `lb_proj_unique sg _ _ (lm_ten_mem sg _ fun τ => unit_mem (sg τ) _ (Subtype.coe_prop _))` to reduce the goal to its premises. Introduce `v hv`. Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨F, hF, rfl⟩` from `hx`. Express the relevant statement in the definitionally equal form `fockB _ (ten F) = fockB _ (ten F)`. Establish `hB : (bFac b : K) ≠ 0`. Unfold `bFac`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _` after adjusting the coercions.

Apply `mul_right_cancel₀ hB` to reduce the goal to its premises. Rewrite using `[fock_coef_ten, sd_fockB_ten]`. Establish `hBp : (bFac b : K) = ∏ τ, (bFac (fun _ : Unit => b τ) : K)`. Unfold `bFac`. Use `push_cast`.

Simplify using the standard rewrite rules. Rewrite using `[hBp, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h1` using `fock_coef_ten (K := K) (ι := Unit) hN (fun _ => b τ) (fun _ => f τ) (fun _ => F τ)`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton] at h1`.

Rewrite using `[← h1]`. Use `congr 1`. Establish `h2 : fockB (prCoefOne hN (sg τ) (b τ) (f τ)) (F τ) = fockB (ten fun _ : Unit => prCoefOne hN (sg τ) (b τ) (f τ)) (ten fun _ : Unit => F τ)`. Rewrite using `[sd_fockB_ten]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `fockB (prCoefOne hN (sg τ) (b τ) (f τ)) (F τ) = _`. Rewrite using `[h2, ← toUnit_eq_ten, prCoefOne, AlgEquiv.apply_symm_apply, lb_proj_spec (fun _ : Unit => sg τ) _ _ (lm_ten_mem (fun _ : Unit => sg τ) _ fun _ => hF τ), toUnit_eq_ten]`. Consider the case `zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]`. Consider the case `add x y _ _ hx hy => rw [lb_fockB_add_right, lb_fockB_add_right, hx, hy]`. Consider the case `smul a x _ hx => rw [lb_fockB_smul_right, lb_fockB_smul_right, hx]`.
-/
theorem projVV_coef_ten (b : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) K) :
    (projVV sg (coefLast hN b (ten f)) : Pol K ι n) = ten fun τ => prCoefOne hN (sg τ) (b τ) (f τ) := by
  apply lb_proj_unique sg _ _ (lm_ten_mem sg _ fun τ => unit_mem (sg τ) _ (Subtype.coe_prop _))
  intro v hv
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    change fockB _ (ten F) = fockB _ (ten F)
    have hB : (bFac b : K) ≠ 0 := by
      unfold bFac
      exact_mod_cast Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _
    apply mul_right_cancel₀ hB
    rw [fock_coef_ten, sd_fockB_ten]
    have hBp : (bFac b : K) = ∏ τ, (bFac (fun _ : Unit => b τ) : K) := by
      unfold bFac; push_cast; simp
    rw [hBp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 := fock_coef_ten (K := K) (ι := Unit) hN (fun _ => b τ) (fun _ => f τ) (fun _ => F τ)
    simp only [Finset.univ_unique, Finset.prod_singleton] at h1
    rw [← h1]
    congr 1
    have h2 : fockB (prCoefOne hN (sg τ) (b τ) (f τ)) (F τ) =
        fockB (ten fun _ : Unit => prCoefOne hN (sg τ) (b τ) (f τ)) (ten fun _ : Unit => F τ) := by
      rw [sd_fockB_ten]; simp
    change fockB (prCoefOne hN (sg τ) (b τ) (f τ)) (F τ) = _
    rw [h2, ← toUnit_eq_ten, prCoefOne, AlgEquiv.apply_symm_apply,
      lb_proj_spec (fun _ : Unit => sg τ) _ _ (lm_ten_mem (fun _ : Unit => sg τ) _ fun _ => hF τ), toUnit_eq_ten]
  | zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]
  | add x y _ _ hx hy => rw [lb_fockB_add_right, lb_fockB_add_right, hx, hy]
  | smul a x _ hx => rw [lb_fockB_smul_right, lb_fockB_smul_right, hx]

variable (lam : ι → DomWeight N)

/- English proof (translation)
Unfold `brOne prCoefOne brStdP`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, AlgEquiv.toLinearMap_apply, map_smul, brConst, Finset.univ_unique, Finset.prod_singleton]`. Both sides reduce to the same expression.
-/
theorem brOne_eq (l : DomWeight N) (s : DomWeight n) (F : MvPolynomial (Fin N × Fin N) K) :
    brOne K hN l s F = (((cBr hN l s : ℤ) : K) * kapBr K hN l s) • prCoefOne hN s (fun i => (bBr hN l s i).toNat) F := by
  unfold brOne prCoefOne brStdP
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    AlgEquiv.toLinearMap_apply, map_smul, brConst, Finset.univ_unique, Finset.prod_singleton]
  rfl

/- English proof (translation)
Simplify using `only [brOne_eq, tenD_smul]`. Unfold `brStdP`. Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul, LinearMap.comp_apply, projVV_coef_ten]`. Both sides reduce to the same expression.
-/
theorem branchingProjection_tensor (f : ι → MvPolynomial (Fin N × Fin N) K) :
    (brStdP hN lam sg (ten f) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ) := by
  simp only [brOne_eq, tenD_smul]
  unfold brStdP
  rw [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.comp_apply, projVV_coef_ten]
  rfl

end GlobalTheory

section FinTwoTypeFamily

open Formalism.MainNotions.product_first_zeroth_parts

variable {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Use extensionality with `⟨τ, x⟩`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single τ]`. Rewrite using `[Finsupp.mapDomain_apply (Prod.mk_right_injective τ), Finsupp.comapDomain_apply]`. Introduce `σ _ hσ`. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises.

Introduce and unpack `⟨y, hy⟩`. Conclude with `hσ (congrArg Prod.fst hy)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ τ) h`.
-/
theorem mon_eq_sum {α : Type} (mon : ι × α →₀ ℕ) :
    mon = ∑ σ, (mon.comapDomain (Prod.mk σ) (Prod.mk_right_injective σ).injOn).mapDomain (Prod.mk σ) := by
  ext ⟨τ, x⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · rw [Finsupp.mapDomain_apply (Prod.mk_right_injective τ), Finsupp.comapDomain_apply]
  · intro σ _ hσ
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h; exact absurd (Finset.mem_univ τ) h

/- English proof (translation)
Establish `key : blk (fun τ => brOne ℂ hN (lam τ) (sg τ)) = (VV ℂ sg).subtype ∘ₗ brStdP hN lam sg`. Apply `(MvPolynomial.basisMonomials (ι × Fin N × Fin N) ℂ).ext` to reduce the goal to its premises. Introduce `mon`. Rewrite using `[MvPolynomial.coe_basisMonomials]`. Establish `hm : (monomial mon (1 : ℂ)) = Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => monomial (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) (1 : ℂ))`.

Rewrite using `[ten_monomial, ← mon_eq_sum]`. Express the relevant statement in the definitionally equal form `blk _ (monomial mon (1 : ℂ)) = ((VV ℂ sg).subtype ∘ₗ brStdP hN lam sg) (monomial mon (1 : ℂ))`. Rewrite using `[hm, blk_ten]`. Conclude with `(branchingProjection_tensor hN sg lam _).symm`. Conclude with `LinearMap.congr_fun key p`.
-/
theorem blk_brOne (p : Pol ℂ ι N) :
    blk (fun τ => brOne ℂ hN (lam τ) (sg τ)) p = (brStdP hN lam sg p : Pol ℂ ι n) := by
  have key : blk (fun τ => brOne ℂ hN (lam τ) (sg τ)) = (VV ℂ sg).subtype ∘ₗ brStdP hN lam sg := by
    apply (MvPolynomial.basisMonomials (ι × Fin N × Fin N) ℂ).ext
    intro mon
    rw [MvPolynomial.coe_basisMonomials]
    have hm : (monomial mon (1 : ℂ)) = Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => monomial (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) (1 : ℂ)) := by
      rw [ten_monomial, ← mon_eq_sum]
    change blk _ (monomial mon (1 : ℂ)) = ((VV ℂ sg).subtype ∘ₗ brStdP hN lam sg) (monomial mon (1 : ℂ))
    rw [hm, blk_ten]
    exact (branchingProjection_tensor hN sg lam _).symm
  exact LinearMap.congr_fun key p

end FinTwoTypeFamily

section OneP

variable {K : Type} [Field K] [CharZero K] {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Rewrite using `[brOne_eq]`. Conclude with `Submodule.smul_mem _ _ (unit_mem s _ (Subtype.coe_prop _))`.
-/
theorem brOne_mem (F : MvPolynomial (Fin N × Fin N) K) : brOne K hN l s F ∈ nablaSq K n s := by
  rw [brOne_eq]
  exact Submodule.smul_mem _ _ (unit_mem s _ (Subtype.coe_prop _))

/- English proof (translation)
Establish `h` using `brStd_xiTen (K := K) (ι := Unit) hN (fun _ => l) (fun _ => s) (fun _ => hI) (fun _ => hS)`. Establish `h1 : ((brStd hN (fun _ : Unit => l) (fun _ => s) ⟨xiTen hN K (fun _ : Unit => l) (fun _ => s), xiTen_mem hN _ _ (fun _ => hI) (fun _ => hS)⟩ : VV K (fun _ : Unit => s)) : Pol K Unit n) = (brStdP hN (fun _ : Unit => l) (fun _ => s) (ten fun _ : Unit => xiBr K hN l s) : Pol K Unit …` using `rfl`. Rewrite `h` using `[h1, branchingProjection_tensor]`. Apply `(toUnit K n).injective` to reduce the goal to its premises. Rewrite using `[map_smul, toUnit_eq_ten, toUnit_eq_ten]`.

Simplify `h` using `[brConst, hTen]`.
-/
theorem brOne_xi (hI : Interlace hN l s) (hS : SameShift l s) :
    brOne K hN l s (xiBr K hN l s) = (((cBr hN l s : ℤ) : K) * kapBr K hN l s) • extremal K n s := by
  have h := brStd_xiTen (K := K) (ι := Unit) hN (fun _ => l) (fun _ => s) (fun _ => hI) (fun _ => hS)
  have h1 : ((brStd hN (fun _ : Unit => l) (fun _ => s)
      ⟨xiTen hN K (fun _ : Unit => l) (fun _ => s), xiTen_mem hN _ _ (fun _ => hI) (fun _ => hS)⟩ : VV K (fun _ : Unit => s)) : Pol K Unit n) =
      (brStdP hN (fun _ : Unit => l) (fun _ => s) (ten fun _ : Unit => xiBr K hN l s) : Pol K Unit n) := rfl
  rw [h1, branchingProjection_tensor] at h
  apply (toUnit K n).injective
  rw [map_smul, toUnit_eq_ten, toUnit_eq_ten]
  simpa [brConst, hTen] using h

/- English proof (translation)
Rewrite using `[brOne_xi hN l s hI hS]`. Use `smul_ne_zero (mul_ne_zero ?_ (kapBr_ne hN l s hI hS)) (lm_extremal_ne s)` and prove the remaining obligations. Conclude with `cBr_ne_zero hN l s hI` after adjusting the coercions.
-/
theorem brOne_xi_ne (hI : Interlace hN l s) (hS : SameShift l s) : brOne K hN l s (xiBr K hN l s) ≠ 0 := by
  rw [brOne_xi hN l s hI hS]
  refine smul_ne_zero (mul_ne_zero ?_ (kapBr_ne hN l s hI hS)) (lm_extremal_ne s)
  exact_mod_cast cBr_ne_zero hN l s hI

/- English proof (translation)
Unfold `Formalism.MainNotions.PrimeDegreeVariant.Interlace Interlace aBr bBr iS iC`. Prove the components needed by the constructor for the conclusion. Introduce `H i; obtain ⟨h1, h2⟩ := H i; exact ⟨by linarith, by linarith⟩`. Introduce `H i; obtain ⟨h1, h2⟩ := H i; exact ⟨by linarith, by linarith⟩`.
-/
theorem interlace_iff (h : n + 1 = N) : Formalism.MainNotions.PrimeDegreeVariant.Interlace h l s ↔ Interlace h.symm l s := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.Interlace Interlace aBr bBr iS iC
  constructor
  · intro H i; obtain ⟨h1, h2⟩ := H i; exact ⟨by linarith, by linarith⟩
  · intro H i; obtain ⟨h1, h2⟩ := H i; exact ⟨by linarith, by linarith⟩

end OneP

section RecP

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Establish `hI'` using `(interlace_iff _ _ (Nm_succ D.R)).1 hI`. Establish `hS` using `sameShiftTr D u τ hI`. Use `⟨fun f => ?_, xiBr ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ), ?_, brOne_xi_ne _ _ _ hI' hS⟩` and prove the remaining obligations. Rewrite using `[← nablaSq_eq_delSq]`. Conclude with `brOne_mem _ _ _ f`.

Rewrite using `[← nablaSq_eq_delSq]`. Conclude with `xiBr_mem _ _ _ hI' hS`.
-/
theorem brOne_member (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ)) :
    (∀ f, brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f ∈ delSq ℂ _ (sgTr D u τ)) ∧
      ∃ f ∈ delSq ℂ _ (lamTr D u τ), brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f ≠ 0 := by
  have hI' := (interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := sameShiftTr D u τ hI
  refine ⟨fun f => ?_, xiBr ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ), ?_, brOne_xi_ne _ _ _ hI' hS⟩
  · rw [← nablaSq_eq_delSq]; exact brOne_mem _ _ _ f
  · rw [← nablaSq_eq_delSq]; exact xiBr_mem _ _ _ hI' hS

end RecP

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Emb

variable {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[iC]`.
-/
theorem emb_symm_iC (i : Fin n) : (finSumFinEquiv.trans (finCongr hN.symm)).symm (iC hN i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [iC]

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[iL]`.
-/
theorem emb_symm_iL : (finSumFinEquiv.trans (finCongr hN.symm)).symm (iL hN) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [iL]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embGL_coe' (g : GL (Fin n) K) :
    ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix
        (finSumFinEquiv.trans (finCongr hN.symm)).symm (finSumFinEquiv.trans (finCongr hN.symm)).symm := rfl

/- English proof (translation)
Use `show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _`. Rewrite using `[embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iC]`. Both sides reduce to the same expression.
-/
theorem embGL_CC (g : GL (Fin n) K) (a b : Fin n) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K).1 (iC hN a) (iC hN b) = g.1 a b := by
  show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _
  rw [embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iC]; rfl

/- English proof (translation)
Use `show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _`. Rewrite using `[embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]`. Both sides reduce to the same expression.
-/
theorem embGL_CL (g : GL (Fin n) K) (a : Fin n) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K).1 (iC hN a) (iL hN) = 0 := by
  show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _
  rw [embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]; rfl

/- English proof (translation)
Use `show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _`. Rewrite using `[embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]`. Both sides reduce to the same expression.
-/
theorem embGL_LC (g : GL (Fin n) K) (a : Fin n) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K).1 (iL hN) (iC hN a) = 0 := by
  show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _
  rw [embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]; rfl

/- English proof (translation)
Use `show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _`. Rewrite using `[embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iL]`. Simplify using the standard rewrite rules.
-/
theorem embGL_LL (g : GL (Fin n) K) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K).1 (iL hN) (iL hN) = 1 := by
  show ((Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) _ _ = _
  rw [embGL_coe' hN, Matrix.submatrix_apply, emb_symm_iL]; simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, embGL_coe' hN, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using the standard rewrite rules.
-/
theorem det_embGL' (g : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.det (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, embGL_coe' hN, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

/- English proof (translation)
Substitute `hN` using the available equality. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [iC_eq, iL_eq]`.
-/
theorem sum_split_CL {M : Type} [AddCommMonoid M] (F : Fin N → M) : ∑ b, F b = (∑ b : Fin n, F (iC hN b)) + F (iL hN) := by
  subst hN
  rw [Fin.sum_univ_castSucc]
  simp only [iC_eq, iL_eq]

end Emb

section Equiv

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

def embAll (g : ι → GL (Fin n) K) : ι → GL (Fin N) K := fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm (g τ)

/- English proof (translation)
Unfold `trAct Formalism.GradedWeylDivisibility.blockAct`. Rewrite using `[aeval_X]`. Both sides reduce to the same expression.
-/
theorem trAct_X {k : ℕ} (g : ι → GL (Fin k) K) (v : ι × Fin k × Fin k) :
    trAct g (X v) = ∑ b : Fin k, C ((g v.1).1 b v.2.1) * X (v.1, (b, v.2.2)) := by
  unfold trAct Formalism.GradedWeylDivisibility.blockAct
  rw [aeval_X]
  rfl

/- English proof (translation)
Rewrite using `[trAct_X, sum_split_CL hN]`. Simplify using `only [embAll, embGL_CL, embGL_LL, map_zero, zero_mul, Finset.sum_const_zero, zero_add, map_one, one_mul]`.
-/
theorem trAct_zvar (g : ι → GL (Fin n) K) (τ : ι) (s : Fin n) :
    trAct (embAll hN g) (X (τ, iL hN, iC hN s) : Pol K ι N) = X (τ, iL hN, iC hN s) := by
  rw [trAct_X, sum_split_CL hN]
  simp only [embAll, embGL_CL, embGL_LL, map_zero, zero_mul, Finset.sum_const_zero, zero_add, map_one, one_mul]

/- English proof (translation)
Establish `: (upperParabolic hN).comp (trAct g) = (trAct (embAll hN g)).comp (upperParabolic (K` using `K) (ι := ι) hN) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply]`. Rewrite using `[trAct_X]`.

Unfold `upperParabolic`. Rewrite using `[rename_X, trAct_X, sum_split_CL hN, map_sum]`. Simplify using `only [upVar, embAll, embGL_CC, embGL_LC, map_zero, zero_mul, add_zero, map_mul, rename_C, rename_X]`. Conclude with `AlgHom.congr_fun this p`.
-/
theorem variableInclusion_equivariant (g : ι → GL (Fin n) K) (p : Pol K ι n) : upperParabolic hN (trAct g p) = trAct (embAll hN g) (upperParabolic hN p) := by
  have : (upperParabolic hN).comp (trAct g) = (trAct (embAll hN g)).comp (upperParabolic (K := K) (ι := ι) hN) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply]
    rw [trAct_X]
    unfold upperParabolic
    rw [rename_X, trAct_X, sum_split_CL hN, map_sum]
    simp only [upVar, embAll, embGL_CC, embGL_LC, map_zero, zero_mul, add_zero, map_mul, rename_C, rename_X]
  exact AlgHom.congr_fun this p

/- English proof (translation)
Unfold `raise`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[map_mul, variableInclusion_equivariant, lx_zExp_prod]`. Use `congr 1`. Rewrite using `[map_prod]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, trAct_zvar]`.
-/
theorem raise_trAct (b : ι → Fin n → ℕ) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    raise hN b (trAct g p) = trAct (embAll hN g) (raise hN b p) := by
  unfold raise
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [map_mul, variableInclusion_equivariant, lx_zExp_prod]
  congr 1
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, trAct_zvar]

variable (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Unfold `detTwK`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `detPow embAll`. Rewrite using `[det_embGL' hN, hS τ]`.
-/
theorem detTwK_emb (hS : SameShiftAll lam sg) (g : ι → GL (Fin n) K) : detTwK lam (embAll hN g) = detTwK sg g := by
  unfold detTwK
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold detPow embAll
  rw [det_embGL' hN, hS τ]

/- English proof (translation)
Unfold `actP`. Simplify using `only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul]`. Rewrite using `[raise_trAct, detTwK_emb hN lam sg hS]`.
-/
theorem raise_actP (hS : SameShiftAll lam sg) (b : ι → Fin n → ℕ) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    raise hN b (actP sg g p) = actP lam (embAll hN g) (raise hN b p) := by
  unfold actP
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul]
  rw [raise_trAct, detTwK_emb hN lam sg hS]

variable [CharZero K]

/- English proof (translation)
Establish `h` using `pairB_adj l g F F'`. Rewrite `h` using `[pairB_apply, pairB_apply]`. Conclude with `mul_left_cancel₀ (inv_ne_zero (pb_extNormB_ne K l)) h`.
-/
theorem fockB_adj {k : ℕ} (l : ι → DomWeight k) (g : ι → GL (Fin k) K) (F F' : Pol K ι k) :
    fockB (actP l g F) F' = fockB F (actP l (invTrK g)⁻¹ F') := by
  have h := pairB_adj l g F F'
  rw [pairB_apply, pairB_apply] at h
  exact mul_left_cancel₀ (inv_ne_zero (pb_extNormB_ne K l)) h

/- English proof (translation)
Apply `lb_proj_unique l _ _ (polyAction_mem_VV l g (Subtype.coe_prop _))` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[fockB_adj, fockB_adj, lb_proj_spec l p _ (polyAction_mem_VV l _ hv)]`.
-/
theorem projVV_actP {k : ℕ} (l : ι → DomWeight k) (g : ι → GL (Fin k) K) (p : Pol K ι k) :
    (projVV l (actP l g p) : Pol K ι k) = actP l g (projVV l p : Pol K ι k) := by
  apply lb_proj_unique l _ _ (polyAction_mem_VV l g (Subtype.coe_prop _))
  intro v hv
  rw [fockB_adj, fockB_adj, lb_proj_spec l p _ (polyAction_mem_VV l _ hv)]

/- English proof (translation)
Introduce `hS g x hx`. Establish `h2 : ∀ y : VV K sg, ((ioStd hN lam sg y : VV K lam) : Pol K ι N) = ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (y : Pol K ι n)) : Pol K ι N)`. Introduce `y`. Simplify using `[ioStd]`. Rewrite using `[h2, h2, map_smul]`.

Use `congr 1`. Use `show (projVV lam (raise hN (bExp hN lam sg) (actP sg g x.1)) : Pol K ι N) = _`. Rewrite using `[raise_actP hN lam sg hS, projVV_actP]`. Both sides reduce to the same expression.
-/
theorem ioEquiv : IoEquiv hN lam sg K := by
  intro hS g x hx
  have h2 : ∀ y : VV K sg, ((ioStd hN lam sg y : VV K lam) : Pol K ι N) =
      ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (y : Pol K ι n)) : Pol K ι N) := by
    intro y; simp [ioStd]
  rw [h2, h2, map_smul]
  congr 1
  show (projVV lam (raise hN (bExp hN lam sg) (actP sg g x.1)) : Pol K ι N) = _
  rw [raise_actP hN lam sg hS, projVV_actP]
  rfl

end Equiv

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

def rE (K : Type) [Field K] (r n : ℕ) (a a' : Fin r) :
    Derivation K (MvPolynomial (Fin r × Fin n) K) (MvPolynomial (Fin r × Fin n) K) :=
  mkDerivation K fun v => if v.1 = a' then X (a, v.2) else 0

def pOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K :=
  rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2)) (extremal K n sg) *
    ∏ s : Fin n, X (iL hN, iC hN s) ^ (bBr hN lam sg s).toNat

def IsHwRow {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) : Prop :=
  (∀ a a' : Fin n, a < a' → rE K N N (iC hN a) (iC hN a') f = 0) ∧
    ∀ a : Fin n, rE K N N (iC hN a) (iC hN a) f = (sg.natW a : K) • f

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨m0, rfl⟩ : ∃ m0, m = m0 + Finsupp.single (t s0) 1` from `⟨m - Finsupp.single (t s0) 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hne))).symm⟩`. Establish `hw0 : Finsupp.weight w m0 + w (t s0) = d`. Rewrite using `[← hmd, map_add, lx_w_single, one_smul]`. Establish `hc` using `congrArg (coeff (Finsupp.single (u s0) 1 + m0)) hD`.

Rewrite `hc` using `[coeff_sum, coeff_zero, Finset.sum_eq_single s0]`. Rewrite `hc` using `[coeff_X_mul, coeff_pderiv]`. Break down `mul_eq_zero.1 hc with h | h` into its components or cases. Conclude with `(mem_support_iff.1 hm) h`. Establish `: ((m0 (t s0) + 1 : ℕ) : K) = 0` using `by push_cast; exact h`.

Conclude with `absurd (Nat.cast_eq_zero.1 this) (Nat.succ_ne_zero _)`. Introduce `s hsS hss`. Rewrite using `[coeff_X_mul']`. Use `split_ifs with hmem`. Rewrite using `[coeff_pderiv]`.

Establish `hle : Finsupp.single (u s) 1 ≤ Finsupp.single (u s0) 1 + m0` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hmem))`. Establish `e1 : Finsupp.weight w (Finsupp.single (u s0) 1 + m0 - Finsupp.single (u s) 1) + w (u s) = w (u s0) + Finsupp.weight w m0`. Use `congrArg (Finsupp.weight w) (tsub_add_cancel_of_le hle)` as an intermediate fact. Rewrite `this` using `[map_add, map_add, lx_w_single, lx_w_single, one_smul, one_smul]`. Conclude with `this`.

Establish `hnot : (Finsupp.single (u s0) 1 + m0 - Finsupp.single (u s) 1 + Finsupp.single (t s) 1) ∉ f.support`. Introduce `hin`. Use `hd _ hin` as an intermediate fact. Rewrite `this` using `[map_add, lx_w_single, one_smul]`. Use `hs s hsS hss` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[notMem_support_iff.1 hnot, zero_mul]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd hs0 h`.
-/
theorem hwA_key {K : Type} [Field K] [CharZero K] {σ ι' : Type} (S : Finset ι') (u t : ι' → σ) (w : σ → ℕ)
    (f : MvPolynomial σ K) (hD : ∑ s ∈ S, X (u s) * pderiv (t s) f = 0) (d : ℕ)
    (hd : ∀ m' ∈ f.support, Finsupp.weight w m' ≤ d) (s0 : ι') (hs0 : s0 ∈ S) (h0 : w (u s0) = w (t s0) + 1)
    (hs : ∀ s ∈ S, s ≠ s0 → w (u s) ≤ w (t s)) (m : σ →₀ ℕ) (hm : m ∈ f.support) (hmd : Finsupp.weight w m = d) :
    m (t s0) = 0 := by
  classical
  by_contra hne
  obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + Finsupp.single (t s0) 1 :=
    ⟨m - Finsupp.single (t s0) 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hne))).symm⟩
  have hw0 : Finsupp.weight w m0 + w (t s0) = d := by
    rw [← hmd, map_add, lx_w_single, one_smul]
  have hc := congrArg (coeff (Finsupp.single (u s0) 1 + m0)) hD
  rw [coeff_sum, coeff_zero, Finset.sum_eq_single s0] at hc
  · rw [coeff_X_mul, coeff_pderiv] at hc
    rcases mul_eq_zero.1 hc with h | h
    · exact (mem_support_iff.1 hm) h
    · have : ((m0 (t s0) + 1 : ℕ) : K) = 0 := by push_cast; exact h
      exact absurd (Nat.cast_eq_zero.1 this) (Nat.succ_ne_zero _)
  · intro s hsS hss
    rw [coeff_X_mul']
    split_ifs with hmem
    · rw [coeff_pderiv]
      have hle : Finsupp.single (u s) 1 ≤ Finsupp.single (u s0) 1 + m0 :=
        Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hmem))
      have e1 : Finsupp.weight w (Finsupp.single (u s0) 1 + m0 - Finsupp.single (u s) 1) + w (u s) =
          w (u s0) + Finsupp.weight w m0 := by
        have := congrArg (Finsupp.weight w) (tsub_add_cancel_of_le hle)
        rw [map_add, map_add, lx_w_single, lx_w_single, one_smul, one_smul] at this
        exact this
      have hnot : (Finsupp.single (u s0) 1 + m0 - Finsupp.single (u s) 1 + Finsupp.single (t s) 1) ∉ f.support := by
        intro hin
        have := hd _ hin
        rw [map_add, lx_w_single, one_smul] at this
        have := hs s hsS hss
        omega
      rw [notMem_support_iff.1 hnot, zero_mul]
    · rfl
  · intro h; exact absurd hs0 h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`. Both sides reduce to the same expression.
-/
theorem hwA_sum_app {K : Type} [Field K] {σ ι' : Type} (S : Finset ι') (c : ι' → MvPolynomial σ K)
    (D : ι' → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    (∑ a ∈ S, c a • D a) g = ∑ a ∈ S, c a * D a g := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; rfl

/- English proof (translation)
Establish `h : ndE K r n l j = ∑ a, (X (a, l) : MvPolynomial (Fin r × Fin n) K) • pderiv (a, j)`. Apply `derivation_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[hwA_sum_app, ndE, mkDerivation_X]`. Simplify using `only [pderiv_X, Pi.single_apply]`.

Distinguish the cases in `hv : v.2 = j`. Rewrite using `[if_pos hv, Finset.sum_eq_single v.1]`. Rewrite using `[if_pos (by rw [← hv]), mul_one]`. Introduce `b _ hb`. Rewrite using `[if_neg (by intro h; exact hb (by rw [h])), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[if_neg hv]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[if_neg (by intro h; exact hv (by rw [h])), mul_zero]`. Rewrite using `[h, hwA_sum_app]`.
-/
theorem hwA_ndE_sum {K : Type} [Field K] {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) K) :
    ndE K r n l j f = ∑ a, X (a, l) * pderiv (a, j) f := by
  classical
  have h : ndE K r n l j = ∑ a, (X (a, l) : MvPolynomial (Fin r × Fin n) K) • pderiv (a, j) := by
    apply derivation_ext
    intro v
    rw [hwA_sum_app, ndE, mkDerivation_X]
    simp only [pderiv_X, Pi.single_apply]
    by_cases hv : v.2 = j
    · rw [if_pos hv, Finset.sum_eq_single v.1]
      · rw [if_pos (by rw [← hv]), mul_one]
      · intro b _ hb
        rw [if_neg (by intro h; exact hb (by rw [h])), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hv]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg (by intro h; exact hv (by rw [h])), mul_zero]
  rw [h, hwA_sum_app]

/- English proof (translation)
Establish `h : rE K r n a a' = ∑ s, (X (a, s) : MvPolynomial (Fin r × Fin n) K) • pderiv (a', s)`. Apply `derivation_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[hwA_sum_app, rE, mkDerivation_X]`. Simplify using `only [pderiv_X, Pi.single_apply]`.

Distinguish the cases in `hv : v.1 = a'`. Rewrite using `[if_pos hv, Finset.sum_eq_single v.2]`. Rewrite using `[if_pos (by rw [← hv]), mul_one]`. Introduce `b _ hb`. Rewrite using `[if_neg (by intro h; exact hb (by rw [h])), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[if_neg hv]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[if_neg (by intro h; exact hv (by rw [h])), mul_zero]`. Rewrite using `[h, hwA_sum_app]`.
-/
theorem hwA_rE_sum {K : Type} [Field K] {r n : ℕ} (a a' : Fin r) (f : MvPolynomial (Fin r × Fin n) K) :
    rE K r n a a' f = ∑ s, X (a, s) * pderiv (a', s) f := by
  classical
  have h : rE K r n a a' = ∑ s, (X (a, s) : MvPolynomial (Fin r × Fin n) K) • pderiv (a', s) := by
    apply derivation_ext
    intro v
    rw [hwA_sum_app, rE, mkDerivation_X]
    simp only [pderiv_X, Pi.single_apply]
    by_cases hv : v.1 = a'
    · rw [if_pos hv, Finset.sum_eq_single v.2]
      · rw [if_pos (by rw [← hv]), mul_one]
      · intro b _ hb
        rw [if_neg (by intro h; exact hb (by rw [h])), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hv]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg (by intro h; exact hv (by rw [h])), mul_zero]
  rw [h, hwA_sum_app]

/- English proof (translation)
Rewrite using `[hwA_rE_sum, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_X_mul']`. Use `split_ifs with hmem`. Establish `hle : Finsupp.single (a, s) 1 ≤ m` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hmem))`.

Rewrite using `[coeff_pderiv, tsub_add_cancel_of_le hle, mul_comm]`. Use `congr 1`. Establish `: (m - Finsupp.single (a, s) 1 : Fin r × Fin n →₀ ℕ) (a, s) + 1 = m (a, s)`. Use `congrArg (fun x => x (a, s)) (tsub_add_cancel_of_le hle)` as an intermediate fact. Simplify using `using this`.

Establish `h2` using `congrArg (Nat.cast : ℕ → K) this`. Move the coercions through the operations in `at h2`. Conclude with `h2`. Rewrite using `[Finsupp.notMem_support_iff.1 hmem]`. Simplify using the standard rewrite rules.
-/
theorem hwA_coeff_euler {K : Type} [Field K] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) K)
    (m : Fin r × Fin n →₀ ℕ) : coeff m (rE K r n a a f) = (rowDeg m a : K) * coeff m f := by
  classical
  rw [hwA_rE_sum, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_X_mul']
  split_ifs with hmem
  · have hle : Finsupp.single (a, s) 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hmem))
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, mul_comm]
    congr 1
    have : (m - Finsupp.single (a, s) 1 : Fin r × Fin n →₀ ℕ) (a, s) + 1 = m (a, s) := by
      have := congrArg (fun x => x (a, s)) (tsub_add_cancel_of_le hle)
      simpa using this
    have h2 := congrArg (Nat.cast : ℕ → K) this
    push_cast at h2
    exact h2
  · rw [Finsupp.notMem_support_iff.1 hmem]; simp

section Slice

variable {K : Type} [Field K] [CharZero K] {N n : ℕ} (hN : N = n + 1)

def hwASlice (ν : Fin N → ℕ) (ρ : Fin n → ℕ) (m : Fin N × Fin N →₀ ℕ) : Prop :=
  (∀ a j : Fin N, a ≠ iL hN → a ≠ j → m (a, j) = 0) ∧ (∀ a : Fin n, rowDeg m (iC hN a) = ρ a) ∧
    ∀ s : Fin N, ∑ a : Fin N, m (a, s) = ν s

/- English proof (translation)
Establish `key : ∀ (μ : Fin N × Fin N →₀ ℕ), hwASlice hN ν ρ μ → ∀ a : Fin n, μ (iC hN a, iC hN a) = ρ a`. Introduce `μ hμ a`. Rewrite using `[← hμ.2.1 a, rowDeg, Finset.sum_eq_single (iC hN a)]`. Introduce `b _ hb`. Conclude with `hμ.1 _ _ (lx_iC_ne_iL hN a) (Ne.symm hb)`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Establish `h1 : ∀ a j : Fin N, a ≠ iL hN → m (a, j) = m' (a, j)`. Introduce `a j ha`. Distinguish the cases in `haj : a = j`.

Take `⟨i, rfl⟩` from `lx_eq_iC_of_ne hN a ha`. Rewrite using `[← haj, key m h i, key m' h' i]`. Rewrite using `[h.1 a j ha haj, h'.1 a j ha haj]`. Use extensionality with `⟨a, j⟩`. Distinguish the cases in `ha : a = iL hN`.

Substitute `ha` using the available equality. Establish `e` using `h.2.2 j`. Establish `e'` using `h'.2.2 j`. Rewrite `e`, `e'` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (iL hN))]`. Establish `: ∑ x ∈ Finset.univ.erase (iL hN), m (x, j) = ∑ x ∈ Finset.univ.erase (iL hN), m' (x, j)` using `Finset.sum_congr rfl fun x hx => h1 x j (Finset.ne_of_mem_erase hx)`.

Use linear arithmetic over natural numbers and integers. Conclude with `h1 a j ha`.
-/
theorem hwA_slice_unique (ν : Fin N → ℕ) (ρ : Fin n → ℕ) (m m' : Fin N × Fin N →₀ ℕ)
    (h : hwASlice hN ν ρ m) (h' : hwASlice hN ν ρ m') : m = m' := by
  classical
  have key : ∀ (μ : Fin N × Fin N →₀ ℕ), hwASlice hN ν ρ μ → ∀ a : Fin n, μ (iC hN a, iC hN a) = ρ a := by
    intro μ hμ a
    rw [← hμ.2.1 a, rowDeg, Finset.sum_eq_single (iC hN a)]
    · intro b _ hb
      exact hμ.1 _ _ (lx_iC_ne_iL hN a) (Ne.symm hb)
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have h1 : ∀ a j : Fin N, a ≠ iL hN → m (a, j) = m' (a, j) := by
    intro a j ha
    by_cases haj : a = j
    · obtain ⟨i, rfl⟩ := lx_eq_iC_of_ne hN a ha
      rw [← haj, key m h i, key m' h' i]
    · rw [h.1 a j ha haj, h'.1 a j ha haj]
  ext ⟨a, j⟩
  by_cases ha : a = iL hN
  · subst ha
    have e := h.2.2 j
    have e' := h'.2.2 j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (iL hN))] at e e'
    have : ∑ x ∈ Finset.univ.erase (iL hN), m (x, j) = ∑ x ∈ Finset.univ.erase (iL hN), m' (x, j) :=
      Finset.sum_congr rfl fun x hx => h1 x j (Finset.ne_of_mem_erase hx)
    omega
  · exact h1 a j ha

open Classical in

def hwAw : Fin N × Fin N → ℕ := fun v => if v.1 = v.2 ∧ v.1 ≠ iL hN then 1 else 0

/- English proof (translation)
The claim follows from `if_pos ⟨rfl, ha⟩`.
-/
theorem hwAw_diag (a : Fin N) (ha : a ≠ iL hN) : hwAw hN (a, a) = 1 := if_pos ⟨rfl, ha⟩

/- English proof (translation)
The claim follows from `if_neg fun h' => h h'.1`.
-/
theorem hwAw_off (a j : Fin N) (h : a ≠ j) : hwAw hN (a, j) = 0 := if_neg fun h' => h h'.1

/- English proof (translation)
Establish `hsupp : f.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hne (support_eq_empty.1 h)`. Take `⟨m, hm, hmax⟩` from `Finset.exists_max_image f.support (fun m => Finsupp.weight (hwAw hN) m) hsupp`.

Use `⟨m, hm, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a j ha haj`. Break down `lt_or_gt_of_ne haj with hlt | hgt` into its components or cases. Establish `hE` using `(Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff.1 hf).2 a j hlt`. Rewrite `hE` using `[hwA_ndE_sum]`.

Conclude with `hwA_key Finset.univ (fun b : Fin N => (b, a)) (fun b => (b, j)) (hwAw hN) f hE _ hmax a (Finset.mem_univ _) (by show hwAw hN (a, a) = hwAw hN (a, j) + 1; rw [hwAw_diag hN a ha, hwAw_off hN a j haj]) (by intro s _ hs; show hwAw hN (s, a) ≤ _; rw [hwAw_off hN s a hs]; exact Nat.zer …`. Take `⟨a1, rfl⟩` from `lx_eq_iC_of_ne hN a ha`. Establish `hj : j ≠ iL hN`. Introduce `h`. Rewrite `hgt` using `[h]`.

Use `a1.2` as an intermediate fact. Simplify using `[iC, iL, Fin.lt_def] at hgt`. Use linear arithmetic over natural numbers and integers. Take `⟨j1, rfl⟩` from `lx_eq_iC_of_ne hN j hj`. Establish `hE` using `hw.1 j1 a1 (Fin.lt_def.2 (show j1.1 < a1.1 from hgt))`.

Rewrite `hE` using `[hwA_rE_sum]`. Conclude with `hwA_key Finset.univ (fun s : Fin N => (iC hN j1, s)) (fun s => (iC hN a1, s)) (hwAw hN) f hE _ hmax (iC hN j1) (Finset.mem_univ _) (by show hwAw hN (iC hN j1, iC hN j1) = hwAw hN (iC hN a1, iC hN j1) + 1; rw [hwAw_diag hN _ hj, hwAw_off hN _ _ haj]) (by intro s _ hs; show hwAw hN …`. Introduce `a`. Establish `h` using `congrArg (coeff m) (hw.2 a)`. Rewrite `h` using `[hwA_coeff_euler, coeff_smul, smul_eq_mul]`.

Use `mul_right_cancel₀ (mem_support_iff.1 hm) h` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `s`. Conclude with `colSums K N N lam.natW f hf m hm s`.
-/
theorem hwA_top (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K)
    (hf : f ∈ nablaSq K N lam) (hw : IsHwRow hN sg f) (hne : f ≠ 0) :
    ∃ m ∈ f.support, hwASlice hN lam.natW sg.natW m := by
  classical
  have hsupp : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hne (support_eq_empty.1 h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support (fun m => Finsupp.weight (hwAw hN) m) hsupp
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · intro a j ha haj
    rcases lt_or_gt_of_ne haj with hlt | hgt
    ·
      have hE := (Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff.1 hf).2 a j hlt
      rw [hwA_ndE_sum] at hE
      exact hwA_key Finset.univ (fun b : Fin N => (b, a)) (fun b => (b, j)) (hwAw hN) f hE _ hmax a (Finset.mem_univ _)
        (by show hwAw hN (a, a) = hwAw hN (a, j) + 1; rw [hwAw_diag hN a ha, hwAw_off hN a j haj])
        (by intro s _ hs; show hwAw hN (s, a) ≤ _; rw [hwAw_off hN s a hs]; exact Nat.zero_le _) m hm rfl
    ·
      obtain ⟨a1, rfl⟩ := lx_eq_iC_of_ne hN a ha
      have hj : j ≠ iL hN := by
        intro h; rw [h] at hgt
        have := a1.2
        simp [iC, iL, Fin.lt_def] at hgt
        omega
      obtain ⟨j1, rfl⟩ := lx_eq_iC_of_ne hN j hj
      have hE := hw.1 j1 a1 (Fin.lt_def.2 (show j1.1 < a1.1 from hgt))
      rw [hwA_rE_sum] at hE
      exact hwA_key Finset.univ (fun s : Fin N => (iC hN j1, s)) (fun s => (iC hN a1, s)) (hwAw hN) f hE _ hmax (iC hN j1)
        (Finset.mem_univ _) (by show hwAw hN (iC hN j1, iC hN j1) = hwAw hN (iC hN a1, iC hN j1) + 1; rw [hwAw_diag hN _ hj, hwAw_off hN _ _ haj])
        (by intro s _ hs; show hwAw hN (iC hN j1, s) ≤ _; rw [hwAw_off hN _ s (Ne.symm hs)]; exact Nat.zero_le _) m hm rfl
  · intro a
    have h := congrArg (coeff m) (hw.2 a)
    rw [hwA_coeff_euler, coeff_smul, smul_eq_mul] at h
    have := mul_right_cancel₀ (mem_support_iff.1 hm) h
    exact_mod_cast this
  · intro s
    exact colSums K N N lam.natW f hf m hm s

/- English proof (translation)
Use `⟨fun a a' h => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, Derivation.map_smul, hf.1 a a' h, hg.1 a a' h, smul_zero, sub_zero]`. Rewrite using `[map_sub, Derivation.map_smul, hf.2 a, hg.2 a, smul_sub, smul_comm]`.
-/
theorem hwA_isHwRow_sub (sg : DomWeight n) (f g : MvPolynomial (Fin N × Fin N) K) (c : K)
    (hf : IsHwRow hN sg f) (hg : IsHwRow hN sg g) : IsHwRow hN sg (f - c • g) := by
  refine ⟨fun a a' h => ?_, fun a => ?_⟩
  · rw [map_sub, Derivation.map_smul, hf.1 a a' h, hg.1 a a' h, smul_zero, sub_zero]
  · rw [map_sub, Derivation.map_smul, hf.2 a, hg.2 a, smul_sub, smul_comm]

/- English proof (translation)
Take `⟨m, hm, hs⟩` from `hwA_top hN lam sg ξ hξ hwξ hne`. Use `⟨coeff m f / coeff m ξ, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Establish `hH : f - (coeff m f / coeff m ξ) • ξ ≠ 0` using `fun h => hcon (sub_eq_zero.1 h)`. Take `⟨m', hm', hs'⟩` from `hwA_top hN lam sg _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hξ)) (hwA_isHwRow_sub hN sg f ξ _ hw hwξ) hH`.

Rewrite `hm'` using `[hwA_slice_unique hN _ _ m' m hs' hs]`. Apply `mem_support_iff.1 hm'` to reduce the goal to its premises. Rewrite using `[coeff_sub, coeff_smul, smul_eq_mul, div_mul_cancel₀ _ (mem_support_iff.1 hm), sub_self]`.
-/
theorem hwA_mult_one (lam : DomWeight N) (sg : DomWeight n) (f ξ : MvPolynomial (Fin N × Fin N) K)
    (hf : f ∈ nablaSq K N lam) (hw : IsHwRow hN sg f) (hξ : ξ ∈ nablaSq K N lam) (hwξ : IsHwRow hN sg ξ) (hne : ξ ≠ 0) :
    ∃ κ : K, f = κ • ξ := by
  obtain ⟨m, hm, hs⟩ := hwA_top hN lam sg ξ hξ hwξ hne
  refine ⟨coeff m f / coeff m ξ, ?_⟩
  by_contra hcon
  have hH : f - (coeff m f / coeff m ξ) • ξ ≠ 0 := fun h => hcon (sub_eq_zero.1 h)
  obtain ⟨m', hm', hs'⟩ := hwA_top hN lam sg _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hξ))
    (hwA_isHwRow_sub hN sg f ξ _ hw hwξ) hH
  rw [hwA_slice_unique hN _ _ m' m hs' hs] at hm'
  apply mem_support_iff.1 hm'
  rw [coeff_sub, coeff_smul, smul_eq_mul, div_mul_cancel₀ _ (mem_support_iff.1 hm), sub_self]

end Slice

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

section Gen

variable {K : Type} [Field K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[add_comm]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : a ≠ i` using `fun h => ha (h ▸ hi)`. Rewrite using `[Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hwB_prod {A : Type} [CommRing A] [Algebra K A] {ι : Type} [DecidableEq ι] (D : Derivation K A A)
    (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul,
      smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/- English proof (translation)
Rewrite using `[hwB_prod]`. Conclude with `Finset.sum_eq_zero fun i hi => by rw [h i hi, mul_zero]`.
-/
theorem hwB_prod_zero {A : Type} [CommRing A] [Algebra K A] {ι : Type} (D : Derivation K A A)
    (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  rw [hwB_prod]
  exact Finset.sum_eq_zero fun i hi => by rw [h i hi, mul_zero]

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, h, smul_zero, smul_zero]`.
-/
theorem hwB_pow_zero {A : Type} [CommRing A] [Algebra K A] (D : Derivation K A A) (x : A) (k : ℕ) (h : D x = 0) :
    D (x ^ k) = 0 := by
  rw [Derivation.leibniz_pow, h, smul_zero, smul_zero]

/- English proof (translation)
Rewrite using `[Derivation.leibniz, h, h', smul_zero, smul_zero, add_zero]`.
-/
theorem hwB_mul_zero {A : Type} [CommRing A] [Algebra K A] (D : Derivation K A A) (x y : A) (h : D x = 0) (h' : D y = 0) :
    D (x * y) = 0 := by
  rw [Derivation.leibniz, h, h', smul_zero, smul_zero, add_zero]

/- English proof (translation)
Establish `key : ∀ M : Matrix (Fin s) (Fin s) A, D M.det = ∑ p, (M.updateCol p fun q => D (M q p)).det`. Introduce `M`. Simplify using `only [Matrix.det_apply']`. Rewrite using `[map_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Establish `hε : D ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * ∏ i, M (σ i) i) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * D (∏ i, M (σ i) i)`. Rewrite using `[Derivation.leibniz, Derivation.map_intCast, smul_zero, add_zero, smul_eq_mul]`. Rewrite using `[hε, hwB_prod, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]`. Rewrite using `[Matrix.updateCol_self, mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]`.

Rewrite using `[← Matrix.det_transpose, key]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `show (Matrix.updateCol M.transpose p fun q => D (M p q)).det = _`. Rewrite using `[Matrix.updateCol_transpose, Matrix.det_transpose]`.
-/
theorem hwB_det {A : Type} [CommRing A] [Algebra K A] {s : ℕ} (D : Derivation K A A) (M : Matrix (Fin s) (Fin s) A) :
    D M.det = ∑ p, (M.updateRow p fun q => D (M p q)).det := by
  have key : ∀ M : Matrix (Fin s) (Fin s) A, D M.det = ∑ p, (M.updateCol p fun q => D (M q p)).det := by
    intro M
    simp only [Matrix.det_apply']
    rw [map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hε : D ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * ∏ i, M (σ i) i) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * D (∏ i, M (σ i) i) := by
      rw [Derivation.leibniz, Derivation.map_intCast, smul_zero, add_zero, smul_eq_mul]
    rw [hε, hwB_prod, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
    rw [Matrix.updateCol_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [← Matrix.det_transpose, key]
  refine Finset.sum_congr rfl fun p _ => ?_
  show (Matrix.updateCol M.transpose p fun q => D (M p q)).det = _
  rw [Matrix.updateCol_transpose, Matrix.det_transpose]

/- English proof (translation)
Unfold `rE`. Rewrite using `[mkDerivation_X]`.
-/
theorem hwB_rE_X (r n : ℕ) (a a' : Fin r) (v : Fin r × Fin n) :
    rE K r n a a' (X v) = if v.1 = a' then X (a, v.2) else 0 := by
  unfold rE
  rw [mkDerivation_X]

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[hwB_det]`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp : I p = a'`. Take `⟨p1, hp1⟩` from `h p hp`.

Establish `hpp : p ≠ p1`. Introduce and unpack `rfl`. Conclude with `hne (hp1.symm.trans hp)`. Use `Matrix.det_zero_of_row_eq hpp ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Rewrite using `[Matrix.updateRow_self, Matrix.updateRow_ne hpp.symm]`. Simplify using `[hwB_rE_X, hp, hp1]`. Use `Matrix.det_eq_zero_of_row_eq_zero p fun q => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_self]`. Simplify using `[hwB_rE_X, hp]`.
-/
theorem hwB_minor_raise {r n s : ℕ} (a a' : Fin r) (hne : a ≠ a') (I : Fin s → Fin r) (hs : s ≤ n)
    (h : ∀ p, I p = a' → ∃ p1, I p1 = a) : rE K r n a a' (initMinor K I hs) = 0 := by
  unfold initMinor
  rw [hwB_det]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : I p = a'
  · obtain ⟨p1, hp1⟩ := h p hp
    have hpp : p ≠ p1 := by
      rintro rfl
      exact hne (hp1.symm.trans hp)
    refine Matrix.det_zero_of_row_eq hpp ?_
    funext q
    rw [Matrix.updateRow_self, Matrix.updateRow_ne hpp.symm]
    simp [hwB_rE_X, hp, hp1]
  · refine Matrix.det_eq_zero_of_row_eq_zero p fun q => ?_
    rw [Matrix.updateRow_self]
    simp [hwB_rE_X, hp]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]`. Consider the case `mul_X p i hp`. Simplify using `only [Derivation.leibniz, smul_eq_mul, hp, hwB_rE_X, pderiv_X, mul_add, Finset.sum_add_distrib]`.

Use `congr 1`. Distinguish the cases in `hi : i.1 = a'`. Rewrite using `[if_pos hi, Finset.sum_eq_single i.2]`. Establish `: ((a', i.2) : Fin r × Fin n) = i` using `Prod.ext hi.symm rfl`. Rewrite using `[this, Pi.single_eq_same]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `s _ hs`. Rewrite using `[Pi.single_eq_of_ne (fun h => hs (by rw [h])), mul_zero, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[if_neg hi, mul_zero]`. Use `symm`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne (fun h => hi (by rw [h])), mul_zero, mul_zero]`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hwB_rE_sum (r n : ℕ) (a a' : Fin r) (f : MvPolynomial (Fin r × Fin n) K) :
    rE K r n a a' f = ∑ s : Fin n, X (a, s) * pderiv (a', s) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, hp, hwB_rE_X, pderiv_X, mul_add, Finset.sum_add_distrib]
    congr 1
    · by_cases hi : i.1 = a'
      · rw [if_pos hi, Finset.sum_eq_single i.2]
        · have : ((a', i.2) : Fin r × Fin n) = i := Prod.ext hi.symm rfl
          rw [this, Pi.single_eq_same]
          ring
        · intro s _ hs
          rw [Pi.single_eq_of_ne (fun h => hs (by rw [h])), mul_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [if_neg hi, mul_zero]
        symm
        refine Finset.sum_eq_zero fun s _ => ?_
        rw [Pi.single_eq_of_ne (fun h => hi (by rw [h])), mul_zero, mul_zero]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring

/- English proof (translation)
Rewrite using `[coeff_X_mul']`. Use `split_ifs with h`. Establish `h1 : 1 ≤ m i` using `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)`. Establish `h2 : m - Finsupp.single i 1 + Finsupp.single i 1 = m` using `tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1)`. Rewrite using `[coeff_pderiv, h2]`.

Establish `h3 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : K) + 1 = (m i : K)`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel h1]`. Rewrite using `[h3, mul_comm]`. Rewrite using `[Finsupp.notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.
-/
theorem hwB_coeff_X_pderiv {σ : Type} (i : σ) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i f) = (m i : K) * coeff m f := by
  classical
  rw [coeff_X_mul']
  split_ifs with h
  · have h1 : 1 ≤ m i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    have h2 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1)
    rw [coeff_pderiv, h2]
    have h3 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : K) + 1 = (m i : K) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel h1]
    rw [h3, mul_comm]
  · rw [Finsupp.notMem_support_iff.1 h]
    simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[hwB_rE_sum, coeff_sum, coeff_smul, smul_eq_mul]`. Simplify using `only [hwB_coeff_X_pderiv]`. Rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `hm : coeff m f = 0`.

Rewrite using `[hm, mul_zero, mul_zero]`. Establish `h1` using `hf hm`. Establish `h2` using `Formalism.BranchingDeterminantCap.bm_weight_rowW m a`. Rewrite `h2` using `[h1]`. Rewrite using `[h2]`.

Unfold `rowDeg`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem hwB_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) K) (ρ : Fin r → ℕ)
    (hf : IsWeightedHomogeneous (rowW r n) f ρ) : rE K r n a a f = (ρ a : K) • f := by
  ext m
  rw [hwB_rE_sum, coeff_sum, coeff_smul, smul_eq_mul]
  simp only [hwB_coeff_X_pderiv]
  rw [← Finset.sum_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, mul_zero, mul_zero]
  · have h1 := hf hm
    have h2 := Formalism.BranchingDeterminantCap.bm_weight_rowW m a
    rw [h1] at h2
    rw [h2]
    unfold rowDeg
    push_cast
    rfl

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul, hp, h, map_add]`.
-/
theorem hwB_rename {σ σ' : Type} (g : σ → σ') (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (D' : Derivation K (MvPolynomial σ' K) (MvPolynomial σ' K)) (h : ∀ i, D' (X (g i)) = rename g (D (X i)))
    (f : MvPolynomial σ K) : D' (rename g f) = rename g (D f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul, hp, h, map_add]

end Gen

section BPlevel

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.xiB`. Use `hwB_prod_zero _ _ _ fun i _ => ?_` and prove the remaining obligations. Establish `hne : a.castSucc ≠ a'.castSucc` using `fun e => (ne_of_lt h) (Fin.castSucc_injective _ e)`. Establish `hlt` using `Fin.lt_def.1 h`. Use `hwB_mul_zero _ _ _ (hwB_pow_zero _ _ _ ?_) (hwB_pow_zero _ _ _ ?_)` and prove the remaining obligations.

Use `hwB_minor_raise _ _ hne _ _ fun p hp => ?_` and prove the remaining obligations. Establish `hv : p.val = a'.val`. Use `congrArg Fin.val hp` as an intermediate fact. Simplify `this` using `[Formalism.BranchingDeterminantCap.rowsA]`. Conclude with `⟨⟨a.val, by have := p.2; omega⟩, Fin.ext (by simp [Formalism.BranchingDeterminantCap.rowsA])⟩`.

Use `hwB_minor_raise _ _ hne _ _ fun p hp => ?_` and prove the remaining obligations. Establish `hpl : p.val < i.val`. Assume the negation of the conclusion as `hc`. Establish `e : Formalism.BranchingDeterminantCap.rowsB i p = Fin.last n` using `by simp [Formalism.BranchingDeterminantCap.rowsB, hc]`. Rewrite `hp` using `[e]`.

Conclude with `(Fin.castSucc_lt_last a').ne hp.symm`. Establish `hv : p.val = a'.val`. Use `congrArg Fin.val hp` as an intermediate fact. Simplify `this` using `[Formalism.BranchingDeterminantCap.rowsB, hpl]`. Establish `h2 : a.val < i.val` using `by omega`.

Conclude with `⟨⟨a.val, by omega⟩, Fin.ext (by simp [Formalism.BranchingDeterminantCap.rowsB, h2])⟩`.
-/
theorem hwB_xiB_raise (lam sg : Fin n → ℕ) (a a' : Fin n) (h : a < a') :
    rE K (n + 1) n a.castSucc a'.castSucc (Formalism.BranchingDeterminantCap.xiB K lam sg) = 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  refine hwB_prod_zero _ _ _ fun i _ => ?_
  have hne : a.castSucc ≠ a'.castSucc := fun e => (ne_of_lt h) (Fin.castSucc_injective _ e)
  have hlt := Fin.lt_def.1 h
  refine hwB_mul_zero _ _ _ (hwB_pow_zero _ _ _ ?_) (hwB_pow_zero _ _ _ ?_)
  · refine hwB_minor_raise _ _ hne _ _ fun p hp => ?_
    have hv : p.val = a'.val := by
      have := congrArg Fin.val hp
      simpa [Formalism.BranchingDeterminantCap.rowsA] using this
    exact ⟨⟨a.val, by have := p.2; omega⟩, Fin.ext (by simp [Formalism.BranchingDeterminantCap.rowsA])⟩
  · refine hwB_minor_raise _ _ hne _ _ fun p hp => ?_
    have hpl : p.val < i.val := by
      by_contra hc
      have e : Formalism.BranchingDeterminantCap.rowsB i p = Fin.last n := by simp [Formalism.BranchingDeterminantCap.rowsB, hc]
      rw [e] at hp
      exact (Fin.castSucc_lt_last a').ne hp.symm
    have hv : p.val = a'.val := by
      have := congrArg Fin.val hp
      simpa [Formalism.BranchingDeterminantCap.rowsB, hpl] using this
    have h2 : a.val < i.val := by omega
    exact ⟨⟨a.val, by omega⟩, Fin.ext (by simp [Formalism.BranchingDeterminantCap.rowsB, h2])⟩

/- English proof (translation)
Establish `e : Formalism.BranchingDeterminantCap.bmRho lam sg a.castSucc = sg a`. Unfold `Formalism.BranchingDeterminantCap.bmRho`. Rewrite using `[dif_pos (show (a.castSucc).val < n from a.2)]`. Both sides reduce to the same expression. Rewrite using `[hwB_euler a.castSucc _ _ (Formalism.BranchingDeterminantCap.bm_xi_row (R := K) lam sg hIL), e]`.
-/
theorem hwB_xiB_euler (lam sg : Fin n → ℕ) (hIL : Formalism.BranchingDeterminantCap.bmIL lam sg) (a : Fin n) :
    rE K (n + 1) n a.castSucc a.castSucc (Formalism.BranchingDeterminantCap.xiB K lam sg) = (sg a : K) • Formalism.BranchingDeterminantCap.xiB K lam sg := by
  have e : Formalism.BranchingDeterminantCap.bmRho lam sg a.castSucc = sg a := by
    unfold Formalism.BranchingDeterminantCap.bmRho
    rw [dif_pos (show (a.castSucc).val < n from a.2)]
    rfl
  rw [hwB_euler a.castSucc _ _ (Formalism.BranchingDeterminantCap.bm_xi_row (R := K) lam sg hIL), e]

variable {N : ℕ} (hN : N = n + 1)

/- English proof (translation)
Use `hwB_rename _ _ _ (fun v => ?_) f` and prove the remaining obligations. Rewrite using `[hwB_rE_X, hwB_rE_X]`. Establish `e : ((lxRho hN v).1 = iC hN a') ↔ v.1 = a'.castSucc`. Simplify using `only [lxRho]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `Fin.ext (by have := congrArg Fin.val h; simpa [iC] using this)`. Introduce `h`. Rewrite using `[h]`. Conclude with `Fin.ext rfl`.

Distinguish the cases in `hv : v.1 = a'.castSucc`. Rewrite using `[if_pos hv, if_pos (e.2 hv), rename_X]`. Conclude with `congrArg X (Prod.ext (Fin.ext rfl) rfl)`. Rewrite using `[if_neg hv, if_neg (fun h => hv (e.1 h)), map_zero]`.
-/
theorem hwB_rename_rho (a a' : Fin n) (f : MvPolynomial (Fin (n + 1) × Fin n) K) :
    rE K N N (iC hN a) (iC hN a') (rename (lxRho hN) f) =
      rename (lxRho hN) (rE K (n + 1) n a.castSucc a'.castSucc f) := by
  refine hwB_rename _ _ _ (fun v => ?_) f
  rw [hwB_rE_X, hwB_rE_X]
  have e : ((lxRho hN v).1 = iC hN a') ↔ v.1 = a'.castSucc := by
    simp only [lxRho]
    constructor
    · intro h
      exact Fin.ext (by have := congrArg Fin.val h; simpa [iC] using this)
    · intro h
      rw [h]
      exact Fin.ext rfl
  by_cases hv : v.1 = a'.castSucc
  · rw [if_pos hv, if_pos (e.2 hv), rename_X]
    exact congrArg X (Prod.ext (Fin.ext rfl) rfl)
  · rw [if_neg hv, if_neg (fun h => hv (e.1 h)), map_zero]

/- English proof (translation)
Rewrite using `[← lx_xi_rename hN lam sg hI hS]`. Prove the components needed by the constructor for the conclusion. Introduce `a a' h`. Rewrite using `[hwB_rename_rho, hwB_xiB_raise _ _ _ _ h, map_zero]`. Introduce `a`.

Rewrite using `[hwB_rename_rho, hwB_xiB_euler _ _ (lx_il hN lam sg hI hS), map_smul]`.
-/
theorem hwB_xi (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace hN lam sg) (hS : SameShift lam sg) :
    IsHwRow hN sg (xiBr K hN lam sg) := by
  rw [← lx_xi_rename hN lam sg hI hS]
  constructor
  · intro a a' h
    rw [hwB_rename_rho, hwB_xiB_raise _ _ _ _ h, map_zero]
  · intro a
    rw [hwB_rename_rho, hwB_xiB_euler _ _ (lx_il hN lam sg hI hS), map_smul]

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]`.

Both sides reduce to the same expression.
-/
theorem hwB_rename_lp (i : Fin n) :
    rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2))
        (lpMinor K (r := n) (n := n) (i.val + 1) (by have := i.2; omega) (by have := i.2; omega)) =
      lpMinor K (r := N) (n := N) (i.val + 1) (by have := i.2; omega) (by have := i.2; omega) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

/- English proof (translation)
Unfold `extremal hw Formalism.BranchingDeterminantCap.xiB`. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.sub_self, pow_zero, mul_one, map_pow, map_pow, lx_rename_minorA, hwB_rename_lp]`.
-/
theorem hwB_ext_rename (sg : DomWeight n) :
    rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2)) (extremal K n sg) =
      rename (lxRho hN) (Formalism.BranchingDeterminantCap.xiB K sg.natW sg.natW) := by
  unfold extremal hw Formalism.BranchingDeterminantCap.xiB
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.sub_self, pow_zero, mul_one, map_pow, map_pow, lx_rename_minorA, hwB_rename_lp]

/- English proof (translation)
Introduce `i`. Use `⟨le_rfl, ?_⟩` and prove the remaining obligations. Unfold `nuNext`. Use `split_ifs with h`. Unfold `DomWeight.natW`.

Use `sg.anti (show i ≤ ⟨i.val + 1, h⟩ from Fin.le_def.2 (by simp))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.zero_le _`.
-/
theorem hwB_il (sg : DomWeight n) : Formalism.BranchingDeterminantCap.bmIL sg.natW sg.natW := by
  intro i
  refine ⟨le_rfl, ?_⟩
  unfold nuNext
  split_ifs with h
  · unfold DomWeight.natW
    have := sg.anti (show i ≤ ⟨i.val + 1, h⟩ from Fin.le_def.2 (by simp))
    omega
  · exact Nat.zero_le _

/- English proof (translation)
Establish `hz : ∀ a a' : Fin n, rE K N N (iC hN a) (iC hN a') (∏ s : Fin n, X (iL hN, iC hN s) ^ (bBr hN lam sg s).toNat) = 0`. Introduce `a a'`. Use `hwB_prod_zero _ _ _ fun s _ => hwB_pow_zero _ _ _ ?_` and prove the remaining obligations. Rewrite using `[hwB_rE_X, if_neg]`. Conclude with `fun h => lx_iC_ne_iL hN a' h.symm`.

Unfold `pOne`. Rewrite using `[hwB_ext_rename]`. Prove the components needed by the constructor for the conclusion. Introduce `a a' h`. Conclude with `hwB_mul_zero _ _ _ (by rw [hwB_rename_rho, hwB_xiB_raise _ _ _ _ h, map_zero]) (hz a a')`.

Introduce `a`. Rewrite using `[Derivation.leibniz, hz, smul_zero, zero_add, hwB_rename_rho, hwB_xiB_euler _ _ (hwB_il sg), map_smul, smul_eq_mul, mul_smul_comm, mul_comm]`.
-/
theorem hwB_pOne (lam : DomWeight N) (sg : DomWeight n) : IsHwRow hN sg (pOne K hN lam sg) := by
  have hz : ∀ a a' : Fin n, rE K N N (iC hN a) (iC hN a')
      (∏ s : Fin n, X (iL hN, iC hN s) ^ (bBr hN lam sg s).toNat) = 0 := by
    intro a a'
    refine hwB_prod_zero _ _ _ fun s _ => hwB_pow_zero _ _ _ ?_
    rw [hwB_rE_X, if_neg]
    exact fun h => lx_iC_ne_iL hN a' h.symm
  unfold pOne
  rw [hwB_ext_rename]
  constructor
  · intro a a' h
    exact hwB_mul_zero _ _ _ (by rw [hwB_rename_rho, hwB_xiB_raise _ _ _ _ h, map_zero]) (hz a a')
  · intro a
    rw [Derivation.leibniz, hz, smul_zero, zero_add, hwB_rename_rho, hwB_xiB_euler _ _ (hwB_il sg), map_smul,
      smul_eq_mul, mul_smul_comm, mul_comm]

end BPlevel

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section TenStep

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Unfold `raise hTen ten pOne`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[lx_zExp_prod, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_prod, mul_comm]`.

Use `congr 1`. Unfold `upperParabolic Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[rename_rename, rename_rename]`. Both sides reduce to the same expression. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow]`. Unfold `Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[rename_X]`. Both sides reduce to the same expression.
-/
theorem hwC_raise : raise hN (bExp hN lam sg) (hTen K sg) = ten fun τ => pOne K hN (lam τ) (sg τ) := by
  unfold raise hTen ten pOne
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [lx_zExp_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_prod, mul_comm]
  congr 1
  · unfold upperParabolic Formalism.GradedWeylDivisibility.blockEmb
    rw [rename_rename, rename_rename]
    rfl
  · refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow]
    unfold Formalism.GradedWeylDivisibility.blockEmb
    rw [rename_X]
    rfl

/- English proof (translation)
Introduce `v hv`. Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`.

Establish `e : (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (F s)) = ten F` using `rfl`. Rewrite using `[e, fockB_smul_left', xiTen, sd_fockB_ten, sd_fockB_ten, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[fockB_comm (pOne K hN (lam τ) (sg τ)), hκ τ _ (hF τ), fockB_comm (F τ)]`. Consider the case `zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]`.

Consider the case `add x y _ _ hx hy => rw [lb_fockB_add_right, lb_fockB_add_right, hx, hy]`. Consider the case `smul c x _ hx => rw [lb_fockB_smul_right, lb_fockB_smul_right, hx]`.
-/
theorem hwC_fock (κ : ι → K)
    (hκ : ∀ τ, ∀ f ∈ nablaSq K N (lam τ), fockB f (pOne K hN (lam τ) (sg τ)) = κ τ * fockB f (xiBr K hN (lam τ) (sg τ))) :
    ∀ v ∈ VV K lam, fockB ((∏ τ, κ τ) • xiTen hN K lam sg) v = fockB (ten fun τ => pOne K hN (lam τ) (sg τ)) v := by
  intro v hv
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have e : (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (F s)) = ten F := rfl
    rw [e, fockB_smul_left', xiTen, sd_fockB_ten, sd_fockB_ten, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [fockB_comm (pOne K hN (lam τ) (sg τ)), hκ τ _ (hF τ), fockB_comm (F τ)]
  | zero => rw [lb_fockB_zero_right, lb_fockB_zero_right]
  | add x y _ _ hx hy => rw [lb_fockB_add_right, lb_fockB_add_right, hx, hy]
  | smul c x _ hx => rw [lb_fockB_smul_right, lb_fockB_smul_right, hx]

/- English proof (translation)
Unfold `IoHw`. Introduce `hI hS h`. Use `choose κ hκ using H1 hI hS`. Establish `hξ : xiTen hN K lam sg ∈ VV K lam` using `xiTen_mem hN lam sg hI hS`. Establish `hp : ((projVV lam (raise hN (bExp hN lam sg) (hTen K sg)) : VV K lam) : Pol K ι N) = (∏ τ, κ τ) • xiTen hN K lam sg`.

Apply `lb_proj_unique lam _ _ (Submodule.smul_mem _ _ hξ)` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[hwC_raise]`. Conclude with `hwC_fock hN lam sg κ hκ v hv`. Establish `hio : ((ioStd hN lam sg ⟨hTen K sg, h⟩ : VV K lam) : Pol K ι N) = (ioConst hN K lam sg * ∏ τ, κ τ) • xiTen hN K lam sg`.

Establish `e : ((ioStd hN lam sg ⟨hTen K sg, h⟩ : VV K lam) : Pol K ι N) = ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (hTen K sg)) : Pol K ι N)`. Simplify using `[ioStd]`. Rewrite using `[e, hp, smul_smul]`. Establish `h1` using `ioHw_on_xi hN lam sg hI hS hξ h`. Rewrite `h1` using `[pairBK_apply, pairBK_apply, pairB_apply, pairB_apply]`.

Simplify using `only [] at h1`. Rewrite `h1` using `[hio, fockB_smul_right']`. Establish `hF : fockB (xiTen hN K lam sg) (xiTen hN K lam sg) ≠ 0`. Unfold `xiTen`. Rewrite using `[sd_fockB_ten]`.

Use `Finset.prod_ne_zero_iff.mpr fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← lb_map_xiBr (algebraMap ℚ K)]`. Conclude with `lm_fockB_ne _ (xiBr_ne hN _ _ (hI τ) (hS τ))`. Establish `hE` using `inv_ne_zero (pb_extNormB_ne K lam)`. Establish `hk : ioConst hN K lam sg * ∏ τ, κ τ = ((∏ τ, (cBr hN (lam τ) (sg τ) : ℤ) : ℤ) : K)`.

Apply `mul_right_cancel₀ hF` to reduce the goal to its premises. Apply `mul_left_cancel₀ hE` to reduce the goal to its premises. Take the linear combination `h1`. Rewrite using `[hio, hk]`.
-/
theorem hwC_ioHw_of_single
    (H1 : InterlaceAll hN lam sg → SameShiftAll lam sg → ∀ τ, ∃ κ : K, ∀ f ∈ nablaSq K N (lam τ),
      fockB f (pOne K hN (lam τ) (sg τ)) = κ * fockB f (xiBr K hN (lam τ) (sg τ))) : IoHw hN lam sg K := by
  unfold IoHw
  intro hI hS h
  choose κ hκ using H1 hI hS
  have hξ : xiTen hN K lam sg ∈ VV K lam := xiTen_mem hN lam sg hI hS
  have hp : ((projVV lam (raise hN (bExp hN lam sg) (hTen K sg)) : VV K lam) : Pol K ι N) =
      (∏ τ, κ τ) • xiTen hN K lam sg := by
    apply lb_proj_unique lam _ _ (Submodule.smul_mem _ _ hξ)
    intro v hv
    rw [hwC_raise]
    exact hwC_fock hN lam sg κ hκ v hv
  have hio : ((ioStd hN lam sg ⟨hTen K sg, h⟩ : VV K lam) : Pol K ι N) =
      (ioConst hN K lam sg * ∏ τ, κ τ) • xiTen hN K lam sg := by
    have e : ((ioStd hN lam sg ⟨hTen K sg, h⟩ : VV K lam) : Pol K ι N) =
        ioConst hN K lam sg • (projVV lam (raise hN (bExp hN lam sg) (hTen K sg)) : Pol K ι N) := by
      simp [ioStd]
    rw [e, hp, smul_smul]
  have h1 := ioHw_on_xi hN lam sg hI hS hξ h
  rw [pairBK_apply, pairBK_apply, pairB_apply, pairB_apply] at h1
  simp only [] at h1
  rw [hio, fockB_smul_right'] at h1
  have hF : fockB (xiTen hN K lam sg) (xiTen hN K lam sg) ≠ 0 := by
    unfold xiTen
    rw [sd_fockB_ten]
    refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    rw [← lb_map_xiBr (algebraMap ℚ K)]
    exact lm_fockB_ne _ (xiBr_ne hN _ _ (hI τ) (hS τ))
  have hE := inv_ne_zero (pb_extNormB_ne K lam)
  have hk : ioConst hN K lam sg * ∏ τ, κ τ = ((∏ τ, (cBr hN (lam τ) (sg τ) : ℤ) : ℤ) : K) := by
    apply mul_right_cancel₀ hF
    apply mul_left_cancel₀ hE
    linear_combination h1
  rw [hio, hk]

end TenStep

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

/- English proof (translation)
Take `⟨v, hv, hvp⟩` from `RZ (pOne K hN lam sg)`. Take `⟨κ, hκ⟩` from `MO v hv _ (xiBr_mem hN lam sg hI hS) (HW _ v hP hv hvp) hX (xiBr_ne hN lam sg hI hS)`. Use `⟨κ, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[← hvp f hf, hκ, lb_fockB_smul_right]`.
-/
theorem hwC_single_of {K : Type} [Field K] [CharZero K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace hN lam sg) (hS : SameShift lam sg)
    (MO : ∀ v ∈ nablaSq K N lam, ∀ x ∈ nablaSq K N lam, IsHwRow hN sg v → IsHwRow hN sg x → x ≠ 0 → ∃ κ : K, v = κ • x)
    (RZ : ∀ p : MvPolynomial (Fin N × Fin N) K, ∃ v ∈ nablaSq K N lam, ∀ f ∈ nablaSq K N lam, fockB f v = fockB f p)
    (HW : ∀ p v : MvPolynomial (Fin N × Fin N) K, IsHwRow hN sg p → v ∈ nablaSq K N lam →
      (∀ f ∈ nablaSq K N lam, fockB f v = fockB f p) → IsHwRow hN sg v)
    (hP : IsHwRow hN sg (pOne K hN lam sg)) (hX : IsHwRow hN sg (xiBr K hN lam sg)) :
    ∃ κ : K, ∀ f ∈ nablaSq K N lam, fockB f (pOne K hN lam sg) = κ * fockB f (xiBr K hN lam sg) := by
  obtain ⟨v, hv, hvp⟩ := RZ (pOne K hN lam sg)
  obtain ⟨κ, hκ⟩ := MO v hv _ (xiBr_mem hN lam sg hI hS) (HW _ v hP hv hvp) hX (xiBr_ne hN lam sg hI hS)
  refine ⟨κ, fun f hf => ?_⟩
  rw [← hvp f hf, hκ, lb_fockB_smul_right]

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

section A

variable {K : Type} [Field K] {σ : Type}

/- English proof (translation)
Unfold `mfact`. Use `Finset.prod_subset hs ?_` and prove the remaining obligations. Introduce `x _ hx`. Rewrite using `[Finsupp.notMem_support_iff.mp hx]`. Both sides reduce to the same expression.
-/
theorem hwD_mfact_sub (m : σ →₀ ℕ) (s : Finset σ) (hs : m.support ⊆ s) : mfact m = ∏ k ∈ s, (m k).factorial := by
  unfold mfact
  refine Finset.prod_subset hs ?_
  intro x _ hx
  rw [Finsupp.notMem_support_iff.mp hx]
  rfl

/- English proof (translation)
Establish `h1 : (m + Finsupp.single i 1).support ⊆ insert i m.support`. Introduce `x hx`. Distinguish the cases in `hxi : x = i`. Simplify using `[hxi]`. Rewrite `hx` using `[Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxi), add_zero]`.

Conclude with `Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hx)`. Rewrite using `[hwD_mfact_sub _ _ h1, hwD_mfact_sub m _ (Finset.subset_insert i m.support), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support), ← Finset.mul_prod_erase (insert i m.support) (fun k => (m k).factorial) (Finset.mem_insert_self i m.support)]`. Establish `h2 : ∏ k ∈ (insert i m.support).erase i, ((m + Finsupp.single i 1 : σ →₀ ℕ) k).factorial = ∏ k ∈ (insert i m.support).erase i, (m k).factorial`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hki : k ≠ i` using `Finset.ne_of_mem_erase hk`.

Rewrite using `[Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hki), add_zero]`. Rewrite using `[h2, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hwD_mfact_add_single (m : σ →₀ ℕ) (i : σ) : mfact (m + Finsupp.single i 1) = (m i + 1) * mfact m := by
  classical
  have h1 : (m + Finsupp.single i 1).support ⊆ insert i m.support := by
    intro x hx
    by_cases hxi : x = i
    · simp [hxi]
    · rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxi), add_zero] at hx
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hx)
  rw [hwD_mfact_sub _ _ h1, hwD_mfact_sub m _ (Finset.subset_insert i m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support),
    ← Finset.mul_prod_erase (insert i m.support) (fun k => (m k).factorial) (Finset.mem_insert_self i m.support)]
  have h2 : ∏ k ∈ (insert i m.support).erase i, ((m + Finsupp.single i 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert i m.support).erase i, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hki), add_zero]
  rw [h2, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

/- English proof (translation)
Rewrite using `[← fockBL_apply, map_add, LinearMap.add_apply, fockBL_apply, fockBL_apply]`.
-/
theorem hwD_fockB_add_left (f f' g : MvPolynomial σ K) : fockB (f + f') g = fockB f g + fockB f' g := by
  rw [← fockBL_apply, map_add, LinearMap.add_apply, fockBL_apply, fockBL_apply]

/- English proof (translation)
Rewrite using `[← fockBL_apply, map_sum, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem hwD_fockB_sum_left {ι' : Type} (s : Finset ι') (F : ι' → MvPolynomial σ K) (g : MvPolynomial σ K) :
    fockB (∑ i ∈ s, F i) g = ∑ i ∈ s, fockB (F i) g := by
  rw [← fockBL_apply, map_sum, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m a`. Establish `h : X i * monomial m a = monomial (m + Finsupp.single i 1) a`. Rewrite using `[mul_comm, X, monomial_mul, mul_one]`. Rewrite using `[h, fockB_monomial_left, fockB_monomial_left, coeff_pderiv, hwD_mfact_add_single]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq`. Rewrite using `[mul_add, hwD_fockB_add_left, hp, hq, hwD_fockB_add_left]`.
-/
theorem hwD_fockB_X_mul (i : σ) (f g : MvPolynomial σ K) : fockB (X i * f) g = fockB f (pderiv i g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    have h : X i * monomial m a = monomial (m + Finsupp.single i 1) a := by
      rw [mul_comm, X, monomial_mul, mul_one]
    rw [h, fockB_monomial_left, fockB_monomial_left, coeff_pderiv, hwD_mfact_add_single]
    push_cast
    ring
  | add p q hp hq =>
    rw [mul_add, hwD_fockB_add_left, hp, hq, hwD_fockB_add_left]

end A

section B

variable {K : Type} [Field K] {r n : ℕ}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`.
-/
theorem hwD_sum_apply {ι' A : Type} [CommRing A] [Algebra K A] (s : Finset ι') (D : ι' → Derivation K A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

/- English proof (translation)
Establish `h : rE K r n a a' = ∑ s : Fin n, (X (a, s) : MvPolynomial (Fin r × Fin n) K) • pderiv (a', s)`. Apply `derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨v1, v2⟩`. Rewrite using `[rE, mkDerivation_X, hwD_sum_apply]`. Simplify using `only [Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]`.

Rewrite using `[Finset.sum_eq_single v2]`. Apply the tactic sequence `by_cases h2 : v1 = a' <;> simp [h2]`. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Introduce `hb`.

Conclude with `absurd (Finset.mem_univ _) hb`. Rewrite using `[h, hwD_sum_apply]`. Simplify using `only [Derivation.smul_apply, smul_eq_mul]`.
-/
theorem hwD_rE_eq (a a' : Fin r) (f : MvPolynomial (Fin r × Fin n) K) :
    rE K r n a a' f = ∑ s, X (a, s) * pderiv (a', s) f := by
  classical
  have h : rE K r n a a' = ∑ s : Fin n, (X (a, s) : MvPolynomial (Fin r × Fin n) K) • pderiv (a', s) := by
    apply derivation_ext
    rintro ⟨v1, v2⟩
    rw [rE, mkDerivation_X, hwD_sum_apply]
    simp only [Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single v2]
    · by_cases h2 : v1 = a' <;> simp [h2]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  rw [h, hwD_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[hwD_rE_eq, hwD_rE_eq, hwD_fockB_sum_left, fockB_comm f, hwD_fockB_sum_left]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hwD_fockB_X_mul, hwD_fockB_X_mul, fockB_comm]`.
-/
theorem hwD_fockB_rE (a a' : Fin r) (f g : MvPolynomial (Fin r × Fin n) K) :
    fockB (rE K r n a a' f) g = fockB f (rE K r n a' a g) := by
  rw [hwD_rE_eq, hwD_rE_eq, hwD_fockB_sum_left, fockB_comm f, hwD_fockB_sum_left]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hwD_fockB_X_mul, hwD_fockB_X_mul, fockB_comm]

/- English proof (translation)
Establish `h : ⁅rE K r n a a', ndE K r n l j⁆ = 0`. Apply `derivation_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Derivation.commutator_apply]`. Simplify using `only [rE, ndE, mkDerivation_X, Derivation.coe_zero, Pi.zero_apply]`.

Apply the tactic sequence `by_cases h1 : v.2 = j <;> by_cases h2 : v.1 = a' <;> simp [h1, h2, mkDerivation_X]`. Establish `h'` using `congrArg (fun D => D f) h`. Simplify using `only [Derivation.commutator_apply, Derivation.coe_zero, Pi.zero_apply] at h'`. Conclude with `sub_eq_zero.mp h'`.
-/
theorem hwD_comm_ndE (a a' : Fin r) (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) K) :
    rE K r n a a' (ndE K r n l j f) = ndE K r n l j (rE K r n a a' f) := by
  have h : ⁅rE K r n a a', ndE K r n l j⁆ = 0 := by
    apply derivation_ext
    intro v
    rw [Derivation.commutator_apply]
    simp only [rE, ndE, mkDerivation_X, Derivation.coe_zero, Pi.zero_apply]
    by_cases h1 : v.2 = j <;> by_cases h2 : v.1 = a' <;> simp [h1, h2, mkDerivation_X]
  have h' := congrArg (fun D => D f) h
  simp only [Derivation.commutator_apply, Derivation.coe_zero, Pi.zero_apply] at h'
  exact sub_eq_zero.mp h'

/- English proof (translation)
Establish `h : ⁅rE K r n a a', ndEul K r n s⁆ = 0`. Apply `derivation_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Derivation.commutator_apply]`. Simplify using `only [rE, ndEul, mkDerivation_X, Derivation.coe_zero, Pi.zero_apply]`.

Apply the tactic sequence `by_cases h2 : v.1 = a' <;> simp [h2, mkDerivation_X, colW]`. Establish `h'` using `congrArg (fun D => D f) h`. Simplify using `only [Derivation.commutator_apply, Derivation.coe_zero, Pi.zero_apply] at h'`. Conclude with `sub_eq_zero.mp h'`.
-/
theorem hwD_comm_ndEul (a a' : Fin r) (s : Fin n) (f : MvPolynomial (Fin r × Fin n) K) :
    rE K r n a a' (ndEul K r n s f) = ndEul K r n s (rE K r n a a' f) := by
  have h : ⁅rE K r n a a', ndEul K r n s⁆ = 0 := by
    apply derivation_ext
    intro v
    rw [Derivation.commutator_apply]
    simp only [rE, ndEul, mkDerivation_X, Derivation.coe_zero, Pi.zero_apply]
    by_cases h2 : v.1 = a' <;> simp [h2, mkDerivation_X, colW]
  have h' := congrArg (fun D => D f) h
  simp only [Derivation.commutator_apply, Derivation.coe_zero, Pi.zero_apply] at h'
  exact sub_eq_zero.mp h'

/- English proof (translation)
Rewrite `hf`, the goal using `[Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff]`. Use `⟨fun s => ?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Rewrite using `[← hwD_comm_ndEul, hf.1 s, Derivation.map_smul]`. Rewrite using `[← hwD_comm_ndE, hf.2 l j hlj, map_zero]`.
-/
theorem hwD_rE_mem [CharZero K] {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) K} (hf : f ∈ dualWeyl K r n ν)
    (a a' : Fin r) : rE K r n a a' f ∈ dualWeyl K r n ν := by
  rw [Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff] at hf ⊢
  refine ⟨fun s => ?_, fun l j hlj => ?_⟩
  · rw [← hwD_comm_ndEul, hf.1 s, Derivation.map_smul]
  · rw [← hwD_comm_ndE, hf.2 l j hlj, map_zero]

end B

section C

variable {K : Type} [Field K] [CharZero K] {N : ℕ}

/- English proof (translation)
Simplify using `[ten]`.
-/
theorem hwD_ten_unit (f : MvPolynomial (Fin N × Fin N) K) : ten (fun _ : Unit => f) = blockEmb K () f := by
  simp [ten]

/- English proof (translation)
Rewrite using `[sd_fockB_ten]`. Simplify using the standard rewrite rules.
-/
theorem hwD_fockB_unit (f g : MvPolynomial (Fin N × Fin N) K) :
    fockB (ten fun _ : Unit => f) (ten fun _ : Unit => g) = fockB f g := by
  rw [sd_fockB_ten]
  simp

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hY`. Proceed by induction on `hY using Submodule.span_induction with`. Consider the case `mem Y hY`. Take `⟨F, hF, rfl⟩` from `hY`. Conclude with `⟨F (), hF (), by simp [ten]⟩`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp [ten]⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨va, hva, rfl⟩` from `ha`. Take `⟨vb, hvb, rfl⟩` from `hb`. Conclude with `⟨va + vb, Submodule.add_mem _ hva hvb, by simp [ten]⟩`.

Consider the case `smul c a _ ha`. Take `⟨va, hva, rfl⟩` from `ha`. Conclude with `⟨c • va, Submodule.smul_mem _ c hva, by simp [ten]⟩`.
-/
theorem hwD_VV_unit (lam : DomWeight N) (Y : Pol K Unit N) (hY : Y ∈ VV K (fun _ : Unit => lam)) :
    ∃ v ∈ nablaSq K N lam, Y = ten (fun _ : Unit => v) := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hY
  induction hY using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨F, hF, rfl⟩ := hY
    exact ⟨F (), hF (), by simp [ten]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [ten]⟩
  | add a b _ _ ha hb =>
    obtain ⟨va, hva, rfl⟩ := ha
    obtain ⟨vb, hvb, rfl⟩ := hb
    exact ⟨va + vb, Submodule.add_mem _ hva hvb, by simp [ten]⟩
  | smul c a _ ha =>
    obtain ⟨va, hva, rfl⟩ := ha
    exact ⟨c • va, Submodule.smul_mem _ c hva, by simp [ten]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : ten (fun _ : Unit => x) ∈ VV K (fun _ : Unit => lam)` using `lm_ten_mem _ _ (fun _ => hx)`. Establish `h2 : ∀ Y ∈ VV K (fun _ : Unit => lam), fockB (ten (fun _ : Unit => x)) Y = 0`. Introduce `Y hY`. Take `⟨v, hv, rfl⟩` from `hwD_VV_unit lam Y hY`.

Rewrite using `[hwD_fockB_unit, h v hv]`. Conclude with `lm_ten_ne _ (fun _ => hne) (lb_sep _ _ h1 h2)`.
-/
theorem hwD_sep (lam : DomWeight N) (x : MvPolynomial (Fin N × Fin N) K) (hx : x ∈ nablaSq K N lam)
    (h : ∀ y ∈ nablaSq K N lam, fockB x y = 0) : x = 0 := by
  by_contra hne
  have h1 : ten (fun _ : Unit => x) ∈ VV K (fun _ : Unit => lam) := lm_ten_mem _ _ (fun _ => hx)
  have h2 : ∀ Y ∈ VV K (fun _ : Unit => lam), fockB (ten (fun _ : Unit => x)) Y = 0 := by
    intro Y hY
    obtain ⟨v, hv, rfl⟩ := hwD_VV_unit lam Y hY
    rw [hwD_fockB_unit, h v hv]
  exact lm_ten_ne _ (fun _ => hne) (lb_sep _ _ h1 h2)

/- English proof (translation)
Take `⟨v, hv, hvY⟩` from `hwD_VV_unit lam _ (projVV (fun _ : Unit => lam) (ten fun _ : Unit => p)).2`. Use `⟨v, hv, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h` using `lb_proj_spec (fun _ : Unit => lam) (ten fun _ : Unit => p) (ten fun _ : Unit => f) (lm_ten_mem _ _ (fun _ => hf))`. Rewrite `h` using `[hvY, hwD_fockB_unit, hwD_fockB_unit]`. Rewrite using `[fockB_comm f v, h, fockB_comm]`.
-/
theorem hwD_riesz (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) K) :
    ∃ v ∈ nablaSq K N lam, ∀ f ∈ nablaSq K N lam, fockB f v = fockB f p := by
  obtain ⟨v, hv, hvY⟩ := hwD_VV_unit lam _ (projVV (fun _ : Unit => lam) (ten fun _ : Unit => p)).2
  refine ⟨v, hv, fun f hf => ?_⟩
  have h := lb_proj_spec (fun _ : Unit => lam) (ten fun _ : Unit => p) (ten fun _ : Unit => f)
    (lm_ten_mem _ _ (fun _ => hf))
  rw [hvY, hwD_fockB_unit, hwD_fockB_unit] at h
  rw [fockB_comm f v, h, fockB_comm]

variable {n : ℕ}

/- English proof (translation)
Establish `hmem : ∀ (a a' : Fin N) (f : MvPolynomial (Fin N × Fin N) K), f ∈ nablaSq K N lam → rE K N N a a' f ∈ nablaSq K N lam` using `fun a a' f hf => hwD_rE_mem (ν := lam.natW) hf a a'`. Establish `key : ∀ (a a' : Fin N) (f : MvPolynomial (Fin N × Fin N) K), f ∈ nablaSq K N lam → fockB f (rE K N N a a' v) = fockB f (rE K N N a a' p)`. Introduce `a a' f hf`. Rewrite using `[← hwD_fockB_rE a' a f v, ← hwD_fockB_rE a' a f p]`. Conclude with `h _ (hmem _ _ f hf)`.

Prove the components needed by the constructor for the conclusion. Introduce `a a' haa`. Apply `hwD_sep lam _ (hmem _ _ v hv)` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[fockB_comm, key _ _ y hy, hp.1 a a' haa, lb_fockB_zero_right]`.

Introduce `a`. Establish `h0 : rE K N N (iC hN a) (iC hN a) v - (sg.natW a : K) • v = 0`. Apply `hwD_sep lam _ (Submodule.sub_mem _ (hmem _ _ v hv) (Submodule.smul_mem _ _ hv))` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[lb_fockB_sub_left, fockB_comm, key _ _ y hy, hp.2 a, lb_fockB_smul_right, fockB_comm _ y, lb_fockB_smul_right, h y hy, sub_self]`.

Conclude with `sub_eq_zero.mp h0`.
-/
theorem hwD_hw (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (p v : MvPolynomial (Fin N × Fin N) K)
    (hp : IsHwRow hN sg p) (hv : v ∈ nablaSq K N lam) (h : ∀ f ∈ nablaSq K N lam, fockB f v = fockB f p) :
    IsHwRow hN sg v := by
  have hmem : ∀ (a a' : Fin N) (f : MvPolynomial (Fin N × Fin N) K), f ∈ nablaSq K N lam →
      rE K N N a a' f ∈ nablaSq K N lam := fun a a' f hf => hwD_rE_mem (ν := lam.natW) hf a a'
  have key : ∀ (a a' : Fin N) (f : MvPolynomial (Fin N × Fin N) K), f ∈ nablaSq K N lam →
      fockB f (rE K N N a a' v) = fockB f (rE K N N a a' p) := by
    intro a a' f hf
    rw [← hwD_fockB_rE a' a f v, ← hwD_fockB_rE a' a f p]
    exact h _ (hmem _ _ f hf)
  constructor
  · intro a a' haa
    apply hwD_sep lam _ (hmem _ _ v hv)
    intro y hy
    rw [fockB_comm, key _ _ y hy, hp.1 a a' haa, lb_fockB_zero_right]
  · intro a
    have h0 : rE K N N (iC hN a) (iC hN a) v - (sg.natW a : K) • v = 0 := by
      apply hwD_sep lam _ (Submodule.sub_mem _ (hmem _ _ v hv) (Submodule.smul_mem _ _ hv))
      intro y hy
      rw [lb_fockB_sub_left, fockB_comm, key _ _ y hy, hp.2 a, lb_fockB_smul_right, fockB_comm _ y,
        lb_fockB_smul_right, h y hy, sub_self]
    exact sub_eq_zero.mp h0

end C

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

/- English proof (translation)
The claim follows from `hwC_ioHw_of_single hN lam sg fun hI hS τ => hwC_single_of hN (lam τ) (sg τ) (hI τ) (hS τ) (fun v hv x hx hwv hwx hne => hwA_mult_one hN (lam τ) (sg τ) v x hv hwv hx hwx hne) (hwD_riesz (lam τ)) (fun p v hp hv h => hwD_hw hN (lam τ) (sg τ) p v hp hv h) (hwB_pOne hN (lam τ) (sg τ)) …`.
-/
theorem highest_weight_isotypic_unique {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) : IoHw hN lam sg K :=
  hwC_ioHw_of_single hN lam sg fun hI hS τ =>
    hwC_single_of hN (lam τ) (sg τ) (hI τ) (hS τ)
      (fun v hv x hx hwv hwx hne => hwA_mult_one hN (lam τ) (sg τ) v x hv hwv hx hwx hne)
      (hwD_riesz (lam τ))
      (fun p v hp hv h => hwD_hw hN (lam τ) (sg τ) p v hp hv h)
      (hwB_pOne hN (lam τ) (sg τ))
      (hwB_xi hN (lam τ) (sg τ) (hI τ) (hS τ))

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section BrEquiv

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem invTrK_inv_coe {k : ℕ} (g : ι → GL (Fin k) K) (τ : ι) : (((invTrK g)⁻¹) τ).1 = Matrix.transpose ((g τ).1) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[invTrK_inv_coe]`. Use extensionality with `i j`. Rewrite using `[Matrix.transpose_apply]`.

Apply the tactic sequence `by_cases hi : i = iL hN <;> by_cases hj : j = iL hN`. Substitute `hi` using the available equality. Substitute `hj` using the available equality. Simplify using `only [embAll, embGL_LL]`. Take `⟨j', rfl⟩` from `lx_eq_iC_of_ne hN j hj`.

Substitute `hi` using the available equality. Simplify using `only [embAll, embGL_CL, embGL_LC]`. Take `⟨i', rfl⟩` from `lx_eq_iC_of_ne hN i hi`. Substitute `hj` using the available equality. Simplify using `only [embAll, embGL_CL, embGL_LC]`.

Take `⟨i', rfl⟩` from `lx_eq_iC_of_ne hN i hi`. Take `⟨j', rfl⟩` from `lx_eq_iC_of_ne hN j hj`. Simplify using `only [embAll, embGL_CC]`. Rewrite using `[invTrK_inv_coe, Matrix.transpose_apply]`.
-/
theorem embAll_tr (g : ι → GL (Fin n) K) : (invTrK (embAll hN g))⁻¹ = embAll hN ((invTrK g)⁻¹) := by
  funext τ
  apply Units.ext
  rw [invTrK_inv_coe]
  ext i j
  rw [Matrix.transpose_apply]
  by_cases hi : i = iL hN <;> by_cases hj : j = iL hN
  · subst hi; subst hj; simp only [embAll, embGL_LL]
  · obtain ⟨j', rfl⟩ := lx_eq_iC_of_ne hN j hj
    subst hi; simp only [embAll, embGL_CL, embGL_LC]
  · obtain ⟨i', rfl⟩ := lx_eq_iC_of_ne hN i hi
    subst hj; simp only [embAll, embGL_CL, embGL_LC]
  · obtain ⟨i', rfl⟩ := lx_eq_iC_of_ne hN i hi
    obtain ⟨j', rfl⟩ := lx_eq_iC_of_ne hN j hj
    simp only [embAll, embGL_CC]
    rw [invTrK_inv_coe, Matrix.transpose_apply]

variable [CharZero K] (lam : ι → DomWeight N) (sg : ι → DomWeight n)

/- English proof (translation)
Unfold `bFac`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _` after adjusting the coercions.
-/
theorem bFac_ne (b : ι → Fin n → ℕ) : (bFac b : K) ≠ 0 := by
  unfold bFac
  exact_mod_cast Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _

/- English proof (translation)
Unfold `brStdP`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, map_smul]`. Use `congr 1`. Apply `lb_proj_unique sg _ _ (polyAction_mem_VV sg h (Subtype.coe_prop _))` to reduce the goal to its premises. Introduce `v hv`.

Rewrite using `[fockB_adj, lb_proj_spec sg _ _ (polyAction_mem_VV sg _ hv)]`. Apply `mul_right_cancel₀ (bFac_ne (K := K) (bExp hN lam sg))` to reduce the goal to its premises. Rewrite using `[fockB_coefLast, fockB_coefLast, raise_actP hN lam sg hS, fockB_adj, embAll_tr]`.
-/
theorem branchingProjection_act (hS : SameShiftAll lam sg) (h : ι → GL (Fin n) K) (F : Pol K ι N) :
    (brStdP hN lam sg (actP lam (embAll hN h) F) : Pol K ι n) = actP sg h (brStdP hN lam sg F : Pol K ι n) := by
  unfold brStdP
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, map_smul]
  congr 1
  apply lb_proj_unique sg _ _ (polyAction_mem_VV sg h (Subtype.coe_prop _))
  intro v hv
  rw [fockB_adj, lb_proj_spec sg _ _ (polyAction_mem_VV sg _ hv)]
  apply mul_right_cancel₀ (bFac_ne (K := K) (bExp hN lam sg))
  rw [fockB_coefLast, fockB_coefLast, raise_actP hN lam sg hS, fockB_adj, embAll_tr]

def lastAll (N : ℕ) (a : ι → Kˣ) : ι → GL (Fin N) K := fun τ => Formalism.MainNotions.PrimeDegreeVariant.lastGL K N (a τ)

/- English proof (translation)
Unfold `Formalism.MainNotions.PrimeDegreeVariant.lastGL diagGL`. Simplify using `only [Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem lastGL_apply (a : Kˣ) (i j : Fin N) :
    (Formalism.MainNotions.PrimeDegreeVariant.lastGL K N a).1 i j = if i = j then (if i.1 + 1 = N then (a : K) else 1) else 0 := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.lastGL diagGL
  simp only [Matrix.diagonal_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[invTrK_inv_coe]`. Use extensionality with `i j`. Rewrite using `[Matrix.transpose_apply]`.

Simplify using `only [lastAll, lastGL_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`.
-/
theorem lastAll_tr (a : ι → Kˣ) : (invTrK (lastAll N a))⁻¹ = lastAll N a := by
  funext τ
  apply Units.ext
  rw [invTrK_inv_coe]
  ext i j
  rw [Matrix.transpose_apply]
  simp only [lastAll, lastGL_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

/- English proof (translation)
Rewrite using `[trAct_X, Finset.sum_eq_single (iL hN)]`. Simplify using `only [lastAll, lastGL_apply, if_true]`. Rewrite using `[if_pos (by simp [iL, hN]), smul_eq_C_mul]`. Introduce `b _ hb`. Simplify using `only [lastAll, lastGL_apply]`.

Rewrite using `[if_neg hb, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem torus_action_last_row_var (a : ι → Kˣ) (τ : ι) (s : Fin n) :
    trAct (lastAll N a) (X (τ, iL hN, iC hN s) : Pol K ι N) = (a τ : K) • X (τ, iL hN, iC hN s) := by
  rw [trAct_X, Finset.sum_eq_single (iL hN)]
  · simp only [lastAll, lastGL_apply, if_true]
    rw [if_pos (by simp [iL, hN]), smul_eq_C_mul]
  · intro b _ hb
    simp only [lastAll, lastGL_apply]
    rw [if_neg hb, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `: (trAct (lastAll N a)).comp (upperParabolic (K` using `K) (ι := ι) hN) = upperParabolic hN := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply]`. Unfold `upperParabolic`.

Rewrite using `[rename_X, trAct_X, Finset.sum_eq_single (iC hN v.2.1)]`. Simplify using `only [upVar, lastAll, lastGL_apply, if_true]`. Rewrite using `[if_neg (by have := v.2.1.2; simp [iC, hN]; omega), map_one, one_mul]`. Introduce `b _ hb`. Simplify using `only [upVar, lastAll, lastGL_apply]`.

Rewrite using `[if_neg hb, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Conclude with `AlgHom.congr_fun this p`.
-/
theorem trAct_last_up (a : ι → Kˣ) (p : Pol K ι n) : trAct (lastAll N a) (upperParabolic hN p) = upperParabolic hN p := by
  have : (trAct (lastAll N a)).comp (upperParabolic (K := K) (ι := ι) hN) = upperParabolic hN := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply]
    unfold upperParabolic
    rw [rename_X, trAct_X, Finset.sum_eq_single (iC hN v.2.1)]
    · simp only [upVar, lastAll, lastGL_apply, if_true]
      rw [if_neg (by have := v.2.1.2; simp [iC, hN]; omega), map_one, one_mul]
    · intro b _ hb
      simp only [upVar, lastAll, lastGL_apply]
      rw [if_neg hb, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact AlgHom.congr_fun this p

/- English proof (translation)
Unfold `raise`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[map_mul, trAct_last_up, lx_zExp_prod, ← smul_mul_assoc]`. Use `congr 1`. Rewrite using `[map_prod, ← Finset.prod_smul]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, ← Finset.prod_smul]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, torus_action_last_row_var, smul_pow]`.
-/
theorem raise_last (b : ι → Fin n → ℕ) (a : ι → Kˣ) (p : Pol K ι n) :
    trAct (lastAll N a) (raise hN b p) = (∏ τ, ∏ s, (a τ : K) ^ b τ s) • raise hN b p := by
  unfold raise
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [map_mul, trAct_last_up, lx_zExp_prod, ← smul_mul_assoc]
  congr 1
  rw [map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, torus_action_last_row_var, smul_pow]

/- English proof (translation)
Unfold `brStdP`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]`. Rewrite using `[smul_comm]`. Use `congr 1`. Apply `lb_proj_unique sg _ _ (Submodule.smul_mem _ _ (Subtype.coe_prop _))` to reduce the goal to its premises.

Introduce `v hv`. Rewrite using `[fockB_smul_left', lb_proj_spec sg _ _ hv]`. Apply `mul_right_cancel₀ (bFac_ne (K := K) (bExp hN lam sg))` to reduce the goal to its premises. Rewrite using `[mul_assoc, fockB_coefLast, fockB_coefLast, fockB_adj, lastAll_tr]`. Unfold `actP`.

Rewrite using `[LinearMap.smul_apply, AlgHom.toLinearMap_apply, raise_last, smul_smul, fockB_smul_right']`.
-/
theorem branchingProjection_last (a : ι → Kˣ) (F : Pol K ι N) :
    (brStdP hN lam sg (actP lam (lastAll N a) F) : Pol K ι n) =
      (detTwK lam (lastAll N a) * ∏ τ, ∏ s, (a τ : K) ^ bExp hN lam sg τ s) • (brStdP hN lam sg F : Pol K ι n) := by
  unfold brStdP
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [smul_comm]
  congr 1
  apply lb_proj_unique sg _ _ (Submodule.smul_mem _ _ (Subtype.coe_prop _))
  intro v hv
  rw [fockB_smul_left', lb_proj_spec sg _ _ hv]
  apply mul_right_cancel₀ (bFac_ne (K := K) (bExp hN lam sg))
  rw [mul_assoc, fockB_coefLast, fockB_coefLast, fockB_adj, lastAll_tr]
  unfold actP
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, raise_last, smul_smul, fockB_smul_right']

end BrEquiv

section OneEquiv

variable {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1)

/- English proof (translation)
Simplify using `only [toUnit, renameEquiv_apply, rename_X]`. Both sides reduce to the same expression.
-/
theorem toUnit_X (k : ℕ) (v : Fin k × Fin k) : toUnit K k (X v) = X ((), v) := by
  simp only [toUnit, renameEquiv_apply, rename_X]
  rfl

/- English proof (translation)
Establish `: ((toUnit K k : _ ≃ₐ[K] _) : _ →ₐ[K] _).comp (Formalism.GradedWeylDivisibility.rowAct K (n` using `k) (Matrix.transpose g.1)) = (trAct (fun _ : Unit => g)).comp ((toUnit K k : _ ≃ₐ[K] _) : _ →ₐ[K] _) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply]`. Express the relevant statement in the definitionally equal form `toUnit K k _ = trAct _ (toUnit K k (X v))`.

Rewrite using `[toUnit_X, trAct_X]`. Unfold `Formalism.GradedWeylDivisibility.rowAct`. Rewrite using `[aeval_X, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, toUnit_X, Matrix.transpose_apply]`.

Use `congr 1`. Conclude with `(toUnit K k).commutes _`. Conclude with `AlgHom.congr_fun this f`.
-/
theorem toUnit_rowAct (k : ℕ) (g : GL (Fin k) K) (f : MvPolynomial (Fin k × Fin k) K) :
    toUnit K k (Formalism.GradedWeylDivisibility.rowAct K (n := k) (Matrix.transpose g.1) f) = trAct (fun _ : Unit => g) (toUnit K k f) := by
  have : ((toUnit K k : _ ≃ₐ[K] _) : _ →ₐ[K] _).comp (Formalism.GradedWeylDivisibility.rowAct K (n := k) (Matrix.transpose g.1)) =
      (trAct (fun _ : Unit => g)).comp ((toUnit K k : _ ≃ₐ[K] _) : _ →ₐ[K] _) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply]
    change toUnit K k _ = trAct _ (toUnit K k (X v))
    rw [toUnit_X, trAct_X]
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, toUnit_X, Matrix.transpose_apply]
    congr 1
    exact (toUnit K k).commutes _
  exact AlgHom.congr_fun this f

/- English proof (translation)
Unfold `sqAct actP detTwK`. Rewrite using `[map_smul, toUnit_rowAct]`. Simplify using the standard rewrite rules.
-/
theorem toUnit_sqAct (k : ℕ) (l : DomWeight k) (g : GL (Fin k) K) (f : MvPolynomial (Fin k × Fin k) K) :
    toUnit K k (sqAct K k l g f) = actP (fun _ : Unit => l) (fun _ => g) (toUnit K k f) := by
  unfold sqAct actP detTwK
  rw [map_smul, toUnit_rowAct]
  simp

/- English proof (translation)
Simplify using `[brOne]`.
-/
theorem toUnit_brOne (l : DomWeight N) (s : DomWeight n) (F : MvPolynomial (Fin N × Fin N) K) :
    toUnit K n (brOne K hN l s F) = (brStdP hN (fun _ : Unit => l) (fun _ => s) (toUnit K N F) : Pol K Unit n) := by
  simp [brOne]

include hN in
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Formalism.MainNotions.PrimeDegreeVariant.lastGL, diagGL, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_eq_single (iL hN)]`. Rewrite using `[if_pos (by simp [iL, hN])]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Both sides reduce to the same expression. Introduce `h`. Apply `hb` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [iL]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem det_lastGL' (a : Kˣ) : Matrix.GeneralLinearGroup.det (Formalism.MainNotions.PrimeDegreeVariant.lastGL K N a) = a := by
  apply Units.ext
  simp only [Formalism.MainNotions.PrimeDegreeVariant.lastGL, diagGL, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (iL hN)]
  · rw [if_pos (by simp [iL, hN])]
  · intro b _ hb
    rw [if_neg]
    · rfl
    · intro h
      apply hb
      apply Fin.ext
      simp only [iL]
      omega
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `Formalism.MainNotions.PrimeDegreeVariant.degZ Formalism.MainNotions.PrimeDegreeVariant.wsum`. Rewrite using `[sum_split_CL hN (fun i => l.w i), lx_detShift_N hN l]`. Use `push_cast`. Establish `: ∀ i, ((bBr hN l s i).toNat : ℤ) = l.w (iC hN i) - s.w i` using `fun i => Int.toNat_of_nonneg (hI i).2`. Simplify using `only [this, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem degZ_eq (l : DomWeight N) (s : DomWeight n) (hI : Interlace hN l s) :
    Formalism.MainNotions.PrimeDegreeVariant.degZ l s = l.detShift + ((∑ i, (bBr hN l s i).toNat : ℕ) : ℤ) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.degZ Formalism.MainNotions.PrimeDegreeVariant.wsum
  rw [sum_split_CL hN (fun i => l.w i), lx_detShift_N hN l]
  push_cast
  have : ∀ i, ((bBr hN l s i).toNat : ℤ) = l.w (iC hN i) - s.w i := fun i => Int.toNat_of_nonneg (hI i).2
  simp only [this, Finset.sum_sub_distrib]
  ring

variable [CharZero K] (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Apply `(toUnit K n).injective` to reduce the goal to its premises. Rewrite using `[toUnit_sqAct, toUnit_brOne, toUnit_brOne, toUnit_sqAct]`. Conclude with `branchingProjection_act hN (fun _ : Unit => l) (fun _ => s) (fun _ => hS) (fun _ => g) _`.
-/
theorem brOne_sqAct (hS : SameShift l s) (g : GL (Fin n) K) (f : MvPolynomial (Fin N × Fin N) K) :
    brOne K hN l s (sqAct K N l (Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm g) f) = sqAct K n s g (brOne K hN l s f) := by
  apply (toUnit K n).injective
  rw [toUnit_sqAct, toUnit_brOne, toUnit_brOne, toUnit_sqAct]
  exact branchingProjection_act hN (fun _ : Unit => l) (fun _ => s) (fun _ => hS) (fun _ => g) _

/- English proof (translation)
Apply `(toUnit K n).injective` to reduce the goal to its premises. Rewrite using `[map_smul, toUnit_brOne, toUnit_brOne, toUnit_sqAct]`. Establish `h` using `branchingProjection_last hN (fun _ : Unit => l) (fun _ => s) (fun _ => a) (toUnit K N f)`. Establish `e : (lastAll N (fun _ : Unit => a)) = fun _ => Formalism.MainNotions.PrimeDegreeVariant.lastGL K N a` using `rfl`. Rewrite `h` using `[e]`.

Rewrite using `[h]`. Use `congr 1`. Rewrite using `[degZ_eq hN l s hI, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, ← Finset.prod_pow_eq_pow_sum]`. Simplify using `only [detTwK, detPow, Finset.univ_unique, Finset.prod_singleton, det_lastGL' hN, bExp]`.
-/
theorem brOne_last (hI : Interlace hN l s) (a : Kˣ) (f : MvPolynomial (Fin N × Fin N) K) :
    brOne K hN l s (sqAct K N l (Formalism.MainNotions.PrimeDegreeVariant.lastGL K N a) f) =
      ((a ^ Formalism.MainNotions.PrimeDegreeVariant.degZ l s : Kˣ) : K) • brOne K hN l s f := by
  apply (toUnit K n).injective
  rw [map_smul, toUnit_brOne, toUnit_brOne, toUnit_sqAct]
  have h := branchingProjection_last hN (fun _ : Unit => l) (fun _ => s) (fun _ => a) (toUnit K N f)
  have e : (lastAll N (fun _ : Unit => a)) = fun _ => Formalism.MainNotions.PrimeDegreeVariant.lastGL K N a := rfl
  rw [e] at h
  rw [h]
  congr 1
  rw [degZ_eq hN l s hI, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, ← Finset.prod_pow_eq_pow_sum]
  simp only [detTwK, detPow, Finset.univ_unique, Finset.prod_singleton, det_lastGL' hN, bExp]

end OneEquiv

section RecP4

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f _ => (brOne_member D u τ hI).1 f, (brOne_member D u τ hI).2, fun g f _ => brOne_sqAct _ _ _ (sameShiftTr D u τ hI) g f, fun a f _ => brOne_last _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) a f⟩`.
-/
theorem brOne_member4 (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ)) :
    (∀ f ∈ delSq ℂ _ (lamTr D u τ), brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f ∈ delSq ℂ _ (sgTr D u τ)) ∧
    (∃ f ∈ delSq ℂ _ (lamTr D u τ), brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f ≠ 0) ∧
    (∀ (g : GL (Fin (D.R.N D.R.m - 1)) ℂ), ∀ f ∈ delSq ℂ _ (lamTr D u τ),
      brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
          (sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g) f) =
        sqAct ℂ _ (sgTr D u τ) g (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)) ∧
    (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ _ (lamTr D u τ),
      brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ a) f) =
        ((a ^ Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℂˣ) : ℂ) •
          brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f) :=
  ⟨fun f _ => (brOne_member D u τ hI).1 f, (brOne_member D u τ hI).2,
    fun g f _ => brOne_sqAct _ _ _ (sameShiftTr D u τ hI) g f,
    fun a f _ => brOne_last _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) a f⟩

/- English proof (translation)
Introduce `τ hI`. Take `⟨h2, h3, h4, h5⟩` from `brOne_member4 D u τ hI`. Conclude with `⟨hZ τ hI, h2, h3, h4, h5, hB τ hI⟩`.
-/
theorem brOneIsBr_of (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (hZ : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) → ∀ f ∈ delSq ℤ _ (lamTr D u τ), ∃ g ∈ delSq ℤ _ (sgTr D u τ),
      brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (MvPolynomial.map (Int.castRingHom ℂ) f) =
        MvPolynomial.map (Int.castRingHom ℂ) g)
    (hB : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) → ∀ f ∈ delSq ℂ _ (lamTr D u τ),
      (normFock (sgTr D u τ) (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
        (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤
        Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) ^ 2 * (normFock (lamTr D u τ) f f).re) :
    BrOneIsBr D u := by
  intro τ hI
  obtain ⟨h2, h3, h4, h5⟩ := brOne_member4 D u τ hI
  exact ⟨hZ τ hI, h2, h3, h4, h5, hB τ hI⟩

end RecP4

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

def in_ioOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n) :
    MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin N × Fin N) K :=
  ioConst hN K (fun _ : Unit => l) (fun _ : Unit => s) •
    ((toUnit K N).symm.toLinearMap ∘ₗ (VV K (fun _ : Unit => l)).subtype ∘ₗ projVV (fun _ : Unit => l) ∘ₗ
      raise hN (bExp hN (fun _ : Unit => l) (fun _ : Unit => s)) ∘ₗ (toUnit K n).toLinearMap)

/- English proof (translation)
Rewrite using `[toUnit_eq_ten]`. Conclude with `lm_ten_mem (fun _ : Unit => s) _ fun _ => hv`.
-/
theorem in_toUnit_mem {K : Type} [Field K] {k : ℕ} (s : DomWeight k) (v : MvPolynomial (Fin k × Fin k) K)
    (hv : v ∈ nablaSq K k s) : toUnit K k v ∈ VV K (fun _ : Unit => s) := by
  rw [toUnit_eq_ten]
  exact lm_ten_mem (fun _ : Unit => s) _ fun _ => hv

/- English proof (translation)
Simplify using `[in_ioOne, ioStd]`.
-/
theorem in_toUnit_ioOne {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)
    (v : MvPolynomial (Fin n × Fin n) K) (hv : toUnit K n v ∈ VV K (fun _ : Unit => s)) :
    toUnit K N (in_ioOne K hN l s v) = (ioStd hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨toUnit K n v, hv⟩ : Pol K Unit N) := by
  simp [in_ioOne, ioStd]

/- English proof (translation)
Unfold `in_ioOne`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (unit_mem l _ (Subtype.coe_prop _))`.
-/
theorem in_ioOne_mem {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)
    (v : MvPolynomial (Fin n × Fin n) K) : in_ioOne K hN l s v ∈ nablaSq K N l := by
  unfold in_ioOne
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (unit_mem l _ (Subtype.coe_prop _))

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap

def inB_Comm {n : ℕ} (A : Module.End ℤ (BP ℤ n)) (B : Module.End ℚ (BP ℚ n)) : Prop :=
  ∀ p, map (Int.castRingHom ℚ) (A p) = B (map (Int.castRingHom ℚ) p)

/- English proof (translation)
Introduce `p`. Simplify using the standard rewrite rules.
-/
theorem inB_comm_zero {n : ℕ} : inB_Comm (n := n) 0 0 := by
  intro p; simp

/- English proof (translation)
Introduce `p`. Simplify using the standard rewrite rules.
-/
theorem inB_comm_one {n : ℕ} : inB_Comm (n := n) 1 1 := by
  intro p; simp

/- English proof (translation)
Introduce `p`. Rewrite using `[LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h p, h' p]`.
-/
theorem inB_comm_sub {n : ℕ} {A A' : Module.End ℤ (BP ℤ n)} {B B' : Module.End ℚ (BP ℚ n)}
    (h : inB_Comm A B) (h' : inB_Comm A' B') : inB_Comm (A - A') (B - B') := by
  intro p
  rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h p, h' p]

/- English proof (translation)
Introduce `p`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, map_add, h p, h' p]`.
-/
theorem inB_comm_add {n : ℕ} {A A' : Module.End ℤ (BP ℤ n)} {B B' : Module.End ℚ (BP ℚ n)}
    (h : inB_Comm A B) (h' : inB_Comm A' B') : inB_Comm (A + A') (B + B') := by
  intro p
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, h p, h' p]

/- English proof (translation)
Introduce `p`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, h, h']`.
-/
theorem inB_comm_mul {n : ℕ} {A A' : Module.End ℤ (BP ℤ n)} {B B' : Module.End ℚ (BP ℚ n)}
    (h : inB_Comm A B) (h' : inB_Comm A' B') : inB_Comm (A * A') (B * B') := by
  intro p
  rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

/- English proof (translation)
Introduce `p`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h p]`.
-/
theorem inB_comm_zsmul {n : ℕ} {A : Module.End ℤ (BP ℤ n)} {B : Module.End ℚ (BP ℚ n)} (z : ℤ)
    (h : inB_Comm A B) : inB_Comm (z • A) (z • B) := by
  intro p
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h p]

/- English proof (translation)
Establish `h1 : ((z : ℤ) : Module.End ℤ (BP ℤ n)) = z • 1` using `by simp`. Establish `h2 : ((z : ℤ) : Module.End ℚ (BP ℚ n)) = z • 1` using `by simp`. Rewrite using `[h1, h2]`. Conclude with `inB_comm_zsmul z inB_comm_one`.
-/
theorem inB_comm_intCast {n : ℕ} (z : ℤ) :
    inB_Comm (n := n) ((z : ℤ) : Module.End ℤ (BP ℤ n)) ((z : ℤ) : Module.End ℚ (BP ℚ n)) := by
  have h1 : ((z : ℤ) : Module.End ℤ (BP ℤ n)) = z • 1 := by simp
  have h2 : ((z : ℤ) : Module.End ℚ (BP ℚ n)) = z • 1 := by simp
  rw [h1, h2]
  exact inB_comm_zsmul z inB_comm_one

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using inB_comm_zero`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `inB_comm_add (h a) ih`.
-/
theorem inB_comm_sum {n : ℕ} {ι : Type} (S : Finset ι) (A : ι → Module.End ℤ (BP ℤ n)) (B : ι → Module.End ℚ (BP ℚ n))
    (h : ∀ i, inB_Comm (A i) (B i)) : inB_Comm (∑ i ∈ S, A i) (∑ i ∈ S, B i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using inB_comm_zero
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact inB_comm_add (h a) ih

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simpa using inB_comm_one`. Consider the case `cons a L ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]`. Conclude with `inB_comm_mul (h a) ih`.
-/
theorem inB_comm_listProd {n : ℕ} {ι : Type} (L : List ι) (A : ι → Module.End ℤ (BP ℤ n)) (B : ι → Module.End ℚ (BP ℚ n))
    (h : ∀ i, inB_Comm (A i) (B i)) : inB_Comm (L.map A).prod (L.map B).prod := by
  induction L with
  | nil => simpa using inB_comm_one
  | cons a L ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]; exact inB_comm_mul (h a) ih

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h1 : bmE ℤ n s t (C a) = 0`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `Derivation.map_algebraMap _ _`.

Establish `h2 : bmE ℚ n s t (C ((Int.castRingHom ℚ) a)) = 0`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `Derivation.map_algebraMap _ _`. Rewrite using `[map_C, h1, h2, map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p v hp`. Rewrite using `[Derivation.leibniz, map_mul, map_X, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp, map_X]`. Use `congr 2`. Unfold `bmE`. Rewrite using `[mkDerivation_X, mkDerivation_X]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inB_bmE (n : ℕ) (s t : Fin n) (p : BP ℤ n) :
    map (Int.castRingHom ℚ) (bmE ℤ n s t p) = bmE ℚ n s t (map (Int.castRingHom ℚ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 : bmE ℤ n s t (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    have h2 : bmE ℚ n s t (C ((Int.castRingHom ℚ) a)) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    rw [map_C, h1, h2, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [Derivation.leibniz, map_mul, map_X, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, map_X]
    congr 2
    unfold bmE
    rw [mkDerivation_X, mkDerivation_X]
    split_ifs <;> simp

/- English proof (translation)
Introduce `p` and use `inB_bmE n s t p`.
-/
theorem inB_comm_bmEL (n : ℕ) (s t : Fin n) : inB_Comm (bmEL ℤ n s t) (bmEL ℚ n s t) := fun p => inB_bmE n s t p

/- English proof (translation)
Unfold `bmF`. Use `inB_comm_sub ?_ (inB_comm_bmEL n a i)` and prove the remaining obligations. Use `split_ifs`. Conclude with `inB_comm_intCast _`. Conclude with `inB_comm_zero`.
-/
theorem inB_comm_bmF (n : ℕ) (u : ℤ) (k a i : Fin n) : inB_Comm (bmF (bmEL ℤ n) u k a i) (bmF (bmEL ℚ n) u k a i) := by
  unfold bmF
  refine inB_comm_sub ?_ (inB_comm_bmEL n a i)
  split_ifs
  · exact inB_comm_intCast _
  · exact inB_comm_zero

/- English proof (translation)
Unfold `bmM`. Rewrite using `[List.ofFn_eq_map, List.ofFn_eq_map]`. Conclude with `inB_comm_listProd _ _ _ fun k => inB_comm_bmF n u k _ _`.
-/
theorem inB_comm_bmM (n : ℕ) (u : ℤ) (α β : Fin n → Fin n) : inB_Comm (bmM (bmEL ℤ n) u α β) (bmM (bmEL ℚ n) u α β) := by
  unfold bmM
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact inB_comm_listProd _ _ _ fun k => inB_comm_bmF n u k _ _

/- English proof (translation)
Unfold `bmCap capDet bmPi`. Conclude with `inB_comm_sum _ _ _ fun α => inB_comm_zsmul _ (inB_comm_bmM n u _ _)`.
-/
theorem inB_comm_cap (n : ℕ) (u : ℤ) : inB_Comm (bmCap ℤ n u) (bmCap ℚ n u) := by
  unfold bmCap capDet bmPi
  exact inB_comm_sum _ _ _ fun α => inB_comm_zsmul _ (inB_comm_bmM n u _ _)

/- English proof (translation)
Unfold `bmZop`. Conclude with `inB_comm_listProd _ _ _ fun u => inB_comm_cap n u`.
-/
theorem inB_comm_Zop (n : ℕ) (lam sg : Fin n → ℕ) : inB_Comm (bmZop ℤ n lam sg) (bmZop ℚ n lam sg) := by
  unfold bmZop
  exact inB_comm_listProd _ _ _ fun u => inB_comm_cap n u

/- English proof (translation)
Unfold `zmon`. Simplify using `[map_prod, map_pow]`.
-/
theorem inB_map_zmon (n : ℕ) (b : Fin n → ℕ) : map (Int.castRingHom ℚ) (zmon ℤ n b) = zmon ℚ n b := by
  unfold zmon
  simp [map_prod, map_pow]

/- English proof (translation)
Unfold `emb`. Conclude with `MvPolynomial.map_rename _ _ _`.
-/
theorem inB_map_emb (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (emb ℤ n f) = emb ℚ n (map (Int.castRingHom ℚ) f) := by
  unfold emb
  exact MvPolynomial.map_rename _ _ _

/- English proof (translation)
Use `⟨dualWeylMap ℤ ℚ (Int.castRingHom ℚ) (n + 1) n lam G h.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Apply `h.2.1` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[coeff_map, h0, map_zero]`. Establish `e : map (Int.castRingHom ℚ) G - zmon ℚ n b * emb ℚ n (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (G - zmon ℤ n b * emb ℤ n f)`. Rewrite using `[map_sub, map_mul, inB_map_zmon, inB_map_emb]`. Rewrite using `[e]`. Introduce `m hm`.

Conclude with `h.2.2 m (MvPolynomial.support_map_subset _ _ hm)`.
-/
theorem inB_lift {n : ℕ} (lam b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) (G : BP ℤ n)
    (h : bmLift ℤ n lam b f G) : bmLift ℚ n lam b (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) G) := by
  refine ⟨dualWeylMap ℤ ℚ (Int.castRingHom ℚ) (n + 1) n lam G h.1, ?_, ?_⟩
  · intro d hd
    apply h.2.1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · have e : map (Int.castRingHom ℚ) G - zmon ℚ n b * emb ℚ n (map (Int.castRingHom ℚ) f) =
        map (Int.castRingHom ℚ) (G - zmon ℤ n b * emb ℤ n f) := by
      rw [map_sub, map_mul, inB_map_zmon, inB_map_emb]
    rw [e]
    intro m hm
    exact h.2.2 m (MvPolynomial.support_map_subset _ _ hm)

/- English proof (translation)
Establish `hIL` using `bm_IL_of lam sg hI`. Take `⟨io, hio⟩` from `bmK_io (R := ℚ) lam sg hI`. Use `⟨io, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Take `⟨G, hG⟩` from `bmK_rel_ex lam sg hIL f`.

Rewrite using `[hio f G hG]`. Conclude with `(bmK_mem_alt.1 (bmK_ZW lam sg _ _ (bmK_liftW hG))).1`. Introduce `g f f' hff'`. Take `⟨G, hG⟩` from `bmK_rel_ex lam sg hIL f`. Establish `hG' : bmRel ℚ n lam sg f' (rowAct ℚ (extM ℚ g) G)`.

Unfold `bmRel at *`. Rewrite using `[hff']`. Conclude with `bmLift_rowAct g hG`. Rewrite using `[hio f G hG, hio f' _ hG']`. Conclude with `(LinearMap.congr_fun (bmK_Zc ℚ n lam sg _ (bm_rowAct_comm_bmEL ℚ n g)).eq G).symm`.

Introduce `h hh`. Establish `hG' : bmRel ℚ n lam sg h (xiB ℚ lam sg)`. Unfold `bmRel`. Rewrite using `[hh]`. Conclude with `bmLift_xi lam sg hIL`.

Rewrite using `[hio h _ hG']`. Conclude with `bmK_xi lam sg hI`. Introduce `v₀ hv₀ hv`. Take `⟨G, hG⟩` from `bmK_rel_ex (R := ℤ) lam sg hIL ⟨v₀, hv₀⟩`. Establish `hG' : bmRel ℚ n lam sg ⟨map (Int.castRingHom ℚ) v₀, hv⟩ (map (Int.castRingHom ℚ) G)`.

Unfold `bmRel at *`. Conclude with `inB_lift lam _ v₀ G hG`. Use `⟨bmZop ℤ n lam sg G, ?_⟩` and prove the remaining obligations. Rewrite using `[hio _ _ hG']`. Conclude with `(inB_comm_Zop n lam sg G).symm`.
-/
theorem inB_capInt {n : ℕ} (lam sg : Fin n → ℕ) (hI : Formalism.BranchingDeterminantCap.Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ∃ io : ↥(dualWeyl ℚ n n sg) →ₗ[ℚ] MvPolynomial (Fin (n + 1) × Fin n) ℚ,
      (∀ f, io f ∈ dualWeyl ℚ (n + 1) n lam) ∧
      (∀ (g : Matrix (Fin n) (Fin n) ℚ) (f f' : ↥(dualWeyl ℚ n n sg)),
        (f' : MvPolynomial (Fin n × Fin n) ℚ) = rowAct ℚ g (f : MvPolynomial (Fin n × Fin n) ℚ) →
          io f' = rowAct ℚ (extM ℚ g) (io f)) ∧
      (∀ h : ↥(dualWeyl ℚ n n sg), (h : MvPolynomial (Fin n × Fin n) ℚ) = hw ℚ le_rfl sg →
        io h = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℚ) • xiB ℚ lam sg) ∧
      (∀ v₀ ∈ dualWeyl ℤ n n sg, ∀ hv : map (Int.castRingHom ℚ) v₀ ∈ dualWeyl ℚ n n sg,
        ∃ w₀ : MvPolynomial (Fin (n + 1) × Fin n) ℤ, io ⟨map (Int.castRingHom ℚ) v₀, hv⟩ = map (Int.castRingHom ℚ) w₀) := by
  have hIL := bm_IL_of lam sg hI
  obtain ⟨io, hio⟩ := bmK_io (R := ℚ) lam sg hI
  refine ⟨io, ?_, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    rw [hio f G hG]
    exact (bmK_mem_alt.1 (bmK_ZW lam sg _ _ (bmK_liftW hG))).1
  · intro g f f' hff'
    obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    have hG' : bmRel ℚ n lam sg f' (rowAct ℚ (extM ℚ g) G) := by
      unfold bmRel at *
      rw [hff']
      exact bmLift_rowAct g hG
    rw [hio f G hG, hio f' _ hG']
    exact (LinearMap.congr_fun (bmK_Zc ℚ n lam sg _ (bm_rowAct_comm_bmEL ℚ n g)).eq G).symm
  · intro h hh
    have hG' : bmRel ℚ n lam sg h (xiB ℚ lam sg) := by
      unfold bmRel
      rw [hh]
      exact bmLift_xi lam sg hIL
    rw [hio h _ hG']
    exact bmK_xi lam sg hI
  · intro v₀ hv₀ hv
    obtain ⟨G, hG⟩ := bmK_rel_ex (R := ℤ) lam sg hIL ⟨v₀, hv₀⟩
    have hG' : bmRel ℚ n lam sg ⟨map (Int.castRingHom ℚ) v₀, hv⟩ (map (Int.castRingHom ℚ) G) := by
      unfold bmRel at *
      exact inB_lift lam _ v₀ G hG
    refine ⟨bmZop ℤ n lam sg G, ?_⟩
    rw [hio _ _ hG']
    exact (inB_comm_Zop n lam sg G).symm

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

def inC_mat {r : ℕ} (a b : Fin r) (t : ℚ) : Matrix (Fin r) (Fin r) ℚ :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)

/- English proof (translation)
Establish `: (Polynomial.evalRingHom (C t)).comp (rowGen ℚ (n` using `n) a b).toRingHom = (rowAct ℚ (n := n) (inC_mat a b t)).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[rowGen, rowAct]`. Introduce `v`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen, rowAct, aeval_X, Polynomial.coe_evalRingHom, inC_mat, map_add, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using the standard rewrite rules. Distinguish the cases in `hb : v.1 = b`. Simplify using `only [hb, true_and, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]`.

Rewrite using `[Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]`. Simplify using `[hb]`. Conclude with `congrArg (fun φ => φ f) this`.
-/
lemma inC_eval_rowGen {r n : ℕ} (a b : Fin r) (t : ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    Polynomial.eval (C t) (rowGen ℚ a b f) = rowAct ℚ (inC_mat a b t) f := by
  have : (Polynomial.evalRingHom (C t)).comp (rowGen ℚ (n := n) a b).toRingHom =
      (rowAct ℚ (n := n) (inC_mat a b t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen, rowAct,
        aeval_X, Polynomial.coe_evalRingHom, inC_mat, map_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · simp
      · by_cases hb : v.1 = b
        · simp only [hb, true_and, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
          rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
        · simp [hb]
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Rewrite using `[Polynomial.eval_eq_sum_range' hN]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, mul_comm]`.
-/
lemma inC_eval_C {σ : Type*} (P : Polynomial (MvPolynomial σ ℚ)) (N : ℕ) (hN : P.natDegree < N)
    (t : ℚ) : Polynomial.eval (C t) P = ∑ i ∈ Finset.range N, C (t ^ i) * P.coeff i := by
  rw [Polynomial.eval_eq_sum_range' hN]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mul_comm]

/- English proof (translation)
Use extensionality with `c d`. Simplify using `only [inC_mat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Use `congr 1`. Distinguish the cases in `h : c = b ∧ d = a`. Rewrite using `[if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]`.

Rewrite using `[if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]`.
-/
lemma inC_mat_eq {r : ℕ} (a b : Fin r) (t : ℚ) : inC_mat a b t = 1 + Matrix.single b a t := by
  ext c d
  simp only [inC_mat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h : c = b ∧ d = a
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

/- English proof (translation)
Distinguish the cases in `hab : b = a`. Substitute `hab` using the available equality. Establish `: inC_mat b b t = Matrix.diagonal fun c => if c = b then 1 + t else 1`. Use extensionality with `c d`. Simplify using `only [inC_mat, Matrix.diagonal_apply]`.

Distinguish the cases in `h1 : c = d`. Substitute `h1` using the available equality. Distinguish the cases in `h2 : c = b`. Simplify using `[h2]`. Simplify using `[h2]`.

Distinguish the cases in `h2 : c = b ∧ d = b`. Conclude with `absurd (h2.1.trans h2.2.symm) h1`. Simplify using `[h1, h2]`. Rewrite using `[this, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ b (fun _ => 1 + t)]`. Simplify using `only [Finset.mem_univ, if_true]`.

Introduce `h`. Apply `ht` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[inC_mat_eq]`. Use `Matrix.det_transvection_of_ne b a hab t` as an intermediate fact.

Unfold `Matrix.transvection at this`. Rewrite using `[this]`. Conclude with `one_ne_zero`.
-/
lemma inC_mat_det {r : ℕ} (a b : Fin r) (t : ℚ) (ht : t ≠ -1) : (inC_mat a b t).det ≠ 0 := by
  by_cases hab : b = a
  · subst hab
    have : inC_mat b b t = Matrix.diagonal fun c => if c = b then 1 + t else 1 := by
      ext c d
      simp only [inC_mat, Matrix.diagonal_apply]
      by_cases h1 : c = d
      · subst h1
        by_cases h2 : c = b
        · simp [h2]
        · simp [h2]
      · by_cases h2 : c = b ∧ d = b
        · exact absurd (h2.1.trans h2.2.symm) h1
        · simp [h1, h2]
    rw [this, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ b (fun _ => 1 + t)]
    simp only [Finset.mem_univ, if_true]
    intro h
    apply ht
    linarith
  · rw [inC_mat_eq]
    have := Matrix.det_transvection_of_ne b a hab t
    unfold Matrix.transvection at this
    rw [this]
    exact one_ne_zero

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_zero]`. Use `set N := (rowGen ℚ a b p).natDegree + k + 1 with hN`. Establish `h1 : (rowGen ℚ a b p).natDegree < N` using `by omega`. Establish `hk : k ∈ Finset.range N` using `Finset.mem_range.mpr (by omega)`.

Use `set P : Polynomial ℚ := ∑ i ∈ Finset.range N, Polynomial.monomial i (coeff m (d (rowDiv ℚ a b i p))) with hP`. Establish `hroot : ∀ c : ℚ, c ≠ -1 → P.IsRoot c`. Introduce `c hc`. Establish `e` using `hst (Matrix.GeneralLinearGroup.mkOfDetNeZero (inC_mat a b c) (inC_mat_det a b c hc)) p hp h0`. Establish `e' : d (rowAct ℚ (inC_mat a b c) p) = 0` using `e`.

Rewrite `e'` using `[← inC_eval_rowGen, inC_eval_C _ N h1, map_sum]`. Establish `e2` using `congrArg (coeff m) e'`. Rewrite `e2` using `[coeff_zero, coeff_sum]`. Rewrite using `[Polynomial.IsRoot, hP, Polynomial.eval_finsetSum]`. Rewrite using `[← e2]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eval_monomial, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hP0 : P = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Use `Set.Infinite.mono (s := ({-1} : Set ℚ)ᶜ) (fun c hc => hroot c hc) ?_` and prove the remaining obligations. Conclude with `(Set.finite_singleton _).infinite_compl`. Use `congrArg (fun p => Polynomial.coeff p k) hP0` as an intermediate fact. Simplify using `only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hk, Polynomial.coeff_zero] at this`. Conclude with `this`.
-/
lemma inC_ker_rowDiv {n : ℕ} {σ : Type} (sg : Fin n → ℕ)
    (d : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (hst : ∀ (g : GL (Fin n) ℚ), ∀ p ∈ dualWeyl ℚ n n sg, d p = 0 → d (rowAct ℚ g.1 p) = 0)
    (p : MvPolynomial (Fin n × Fin n) ℚ) (hp : p ∈ dualWeyl ℚ n n sg) (h0 : d p = 0) (a b : Fin n) (k : ℕ) :
    d (rowDiv ℚ a b k p) = 0 := by
  ext m
  rw [coeff_zero]
  set N := (rowGen ℚ a b p).natDegree + k + 1 with hN
  have h1 : (rowGen ℚ a b p).natDegree < N := by omega
  have hk : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℚ := ∑ i ∈ Finset.range N, Polynomial.monomial i (coeff m (d (rowDiv ℚ a b i p))) with hP
  have hroot : ∀ c : ℚ, c ≠ -1 → P.IsRoot c := by
    intro c hc
    have e := hst (Matrix.GeneralLinearGroup.mkOfDetNeZero (inC_mat a b c) (inC_mat_det a b c hc)) p hp h0
    have e' : d (rowAct ℚ (inC_mat a b c) p) = 0 := e
    rw [← inC_eval_rowGen, inC_eval_C _ N h1, map_sum] at e'
    have e2 := congrArg (coeff m) e'
    rw [coeff_zero, coeff_sum] at e2
    rw [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum]
    rw [← e2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul, mul_comm]
    rfl
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := ({-1} : Set ℚ)ᶜ) (fun c hc => hroot c hc) ?_
    exact (Set.finite_singleton _).infinite_compl
  have := congrArg (fun p => Polynomial.coeff p k) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

/- English proof (translation)
Establish `W : ∀ w : List (Fin n × Fin n × ℕ), applyWord ℚ w (hw ℚ le_rfl sg) ∈ dualWeyl ℚ n n sg ∧ d (applyWord ℚ w (hw ℚ le_rfl sg)) = 0`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => exact ⟨hwMem ℚ n n le_rfl sg hsg, h0⟩`. Consider the case `cons x w ih`.

Rewrite using `[applyWord_cons]`. Conclude with `⟨rowDivStable ℚ n n sg _ _ _ _ ih.1, inC_ker_rowDiv sg d hst _ ih.1 ih.2 _ _ _⟩`. Introduce `p hp`. Rewrite `hp` using `[dualWeyl_eq_weyl ℚ le_rfl sg hsg]`. Unfold `weyl at hp`.

Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Conclude with `(W w).2`. Consider the case `zero => exact map_zero d`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero]`.
-/
theorem inC_cyc {n : ℕ} {σ : Type} (sg : Fin n → ℕ) (hsg : Antitone sg)
    (d : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (h0 : d (hw ℚ le_rfl sg) = 0)
    (hst : ∀ (g : GL (Fin n) ℚ), ∀ p ∈ dualWeyl ℚ n n sg, d p = 0 → d (rowAct ℚ g.1 p) = 0) :
    ∀ p ∈ dualWeyl ℚ n n sg, d p = 0 := by
  have W : ∀ w : List (Fin n × Fin n × ℕ), applyWord ℚ w (hw ℚ le_rfl sg) ∈ dualWeyl ℚ n n sg ∧
      d (applyWord ℚ w (hw ℚ le_rfl sg)) = 0 := by
    intro w
    induction w with
    | nil => exact ⟨hwMem ℚ n n le_rfl sg hsg, h0⟩
    | cons x w ih =>
      rw [applyWord_cons]
      exact ⟨rowDivStable ℚ n n sg _ _ _ _ ih.1, inC_ker_rowDiv sg d hst _ ih.1 ih.2 _ _ _⟩
  intro p hp
  rw [dualWeyl_eq_weyl ℚ le_rfl sg hsg] at hp
  unfold weyl at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (W w).2
  | zero => exact map_zero d
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

section Ident

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.d0`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma interlace_difference_shift_invariant {n : ℕ} (L : Fin (n + 1) → ℤ) (S : Fin n → ℤ) (e : ℤ) :
    Formalism.BranchingDeterminantCap.d0 (fun a => L a - e) (fun i => S i - e) = Formalism.BranchingDeterminantCap.d0 L S := by
  unfold Formalism.BranchingDeterminantCap.d0
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `Finset.prod_nbij' (fun v => v + e) (fun v => v - e) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Formalism.BranchingDeterminantCap.rset, interlace_difference_shift_invariant, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢`.

Take `⟨h1, h2, h3, h4⟩` from `hv`. Conclude with `⟨by omega, by omega, by omega, by omega⟩`. Introduce `v hv`. Simplify using `only [Formalism.BranchingDeterminantCap.rset, interlace_difference_shift_invariant, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢`. Take `⟨h1, h2, h3, h4⟩` from `hv`.

Conclude with `⟨by omega, by omega, by omega, by omega⟩`. Introduce `v _`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `v _`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma inC_cCap_shift {n : ℕ} (L : Fin (n + 1) → ℤ) (S : Fin n → ℤ) (e : ℤ) :
    Formalism.BranchingDeterminantCap.cCap (fun a => L a - e) (fun i => S i - e) = Formalism.BranchingDeterminantCap.cCap L S := by
  unfold Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Finset.prod_nbij' (fun v => v + e) (fun v => v - e) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Formalism.BranchingDeterminantCap.rset, interlace_difference_shift_invariant, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hv
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro v hv
    simp only [Formalism.BranchingDeterminantCap.rset, interlace_difference_shift_invariant, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hv
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro v _; ring
  · intro v _; ring
  · intro v _
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Rewrite using `[cBr_eq_cCap, ← inC_cCap_shift (lxLamF hN l) s.w l.detShift]`. Establish `e1` using `lx_detShift_N hN l`. Use `congr 1`. Use function extensionality and compare the values at `a`. Unfold `Formalism.BranchingDeterminantCap.lamZ`.

Use `split_ifs with h`. Simplify using `only [lamN, lxLamF]`. Establish `e3 : iC hN ⟨a.val, h⟩ = Fin.cast hN.symm a` using `Fin.ext rfl`. Rewrite using `[e3]`. Establish `hle : l.w (iL hN) ≤ l.w (Fin.cast hN.symm a)` using `l.anti (Fin.le_def.2 (by simp [iL]; omega))`.

Rewrite using `[Int.toNat_of_nonneg (by omega)]`. Simplify using `only [lxLamF]`. Establish `e3 : Fin.cast hN.symm a = iL hN` using `Fin.ext (by simp [iL]; omega)`. Rewrite using `[e3, e1, sub_self]`. Use function extensionality and compare the values at `i`.

Establish `hn : 0 < n` using `by have := i.2; omega`. Establish `e2` using `lx_detShift_n (N := N) s hn`. Establish `hd : s.detShift = l.detShift` using `hS`. Establish `hlast : s.w ⟨n - 1, by omega⟩ ≤ s.w i` using `s.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))`. Simplify using `only [DomWeight.natW]`.

Rewrite using `[Int.toNat_of_nonneg (by omega), hd]`.
-/
lemma inC_cBr (hS : SameShift l s) :
    Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamN hN l)) (fun i => (s.natW i : ℤ)) = cBr hN l s := by
  rw [cBr_eq_cCap, ← inC_cCap_shift (lxLamF hN l) s.w l.detShift]
  have e1 := lx_detShift_N hN l
  congr 1
  · funext a
    unfold Formalism.BranchingDeterminantCap.lamZ
    split_ifs with h
    · simp only [lamN, lxLamF]
      have e3 : iC hN ⟨a.val, h⟩ = Fin.cast hN.symm a := Fin.ext rfl
      rw [e3]
      have hle : l.w (iL hN) ≤ l.w (Fin.cast hN.symm a) := l.anti (Fin.le_def.2 (by simp [iL]; omega))
      rw [Int.toNat_of_nonneg (by omega)]
    · simp only [lxLamF]
      have e3 : Fin.cast hN.symm a = iL hN := Fin.ext (by simp [iL]; omega)
      rw [e3, e1, sub_self]
  · funext i
    have hn : 0 < n := by have := i.2; omega
    have e2 := lx_detShift_n (N := N) s hn
    have hd : s.detShift = l.detShift := hS
    have hlast : s.w ⟨n - 1, by omega⟩ ≤ s.w i := s.anti (Fin.le_def.2 (by show i.val ≤ n - 1; omega))
    simp only [DomWeight.natW]
    rw [Int.toNat_of_nonneg (by omega), hd]

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b`. Use `embGL_LL (K := ℚ) (rfl : n + 1 = n + 1) g` as an intermediate fact. Rewrite `this` using `[iL_eq]`. Rewrite using `[this]`.

Simplify using `[Formalism.BranchingDeterminantCap.extM]`. Use `embGL_LC (K := ℚ) (rfl : n + 1 = n + 1) g b'` as an intermediate fact. Rewrite `this` using `[iL_eq, iC_eq]`. Rewrite using `[this]`. Establish `hne : Fin.last n ≠ b'.castSucc` using `(Fin.castSucc_lt_last b').ne'`.

Simplify using `[Formalism.BranchingDeterminantCap.extM, hne]`. Use `embGL_CL (K := ℚ) (rfl : n + 1 = n + 1) g a'` as an intermediate fact. Rewrite `this` using `[iL_eq, iC_eq]`. Rewrite using `[this]`. Establish `hne : a'.castSucc ≠ Fin.last n` using `(Fin.castSucc_lt_last a').ne`.

Simplify using `[Formalism.BranchingDeterminantCap.extM, hne]`. Use `embGL_CC (K := ℚ) (rfl : n + 1 = n + 1) g a' b'` as an intermediate fact. Rewrite `this` using `[iC_eq, iC_eq]`. Rewrite using `[this]`. Simplify using `[Formalism.BranchingDeterminantCap.extM]`.
-/
lemma inC_emb_extM (g : GL (Fin n) ℚ) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n (n + 1) (rfl : n + 1 = n + 1) g : GL (Fin (n + 1)) ℚ).1 = Formalism.BranchingDeterminantCap.extM ℚ g.1 := by
  ext a b
  refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
  · have := embGL_LL (K := ℚ) (rfl : n + 1 = n + 1) g
    rw [iL_eq] at this
    rw [this]; simp [Formalism.BranchingDeterminantCap.extM]
  · have := embGL_LC (K := ℚ) (rfl : n + 1 = n + 1) g b'
    rw [iL_eq, iC_eq] at this
    rw [this]
    have hne : Fin.last n ≠ b'.castSucc := (Fin.castSucc_lt_last b').ne'
    simp [Formalism.BranchingDeterminantCap.extM, hne]
  · have := embGL_CL (K := ℚ) (rfl : n + 1 = n + 1) g a'
    rw [iL_eq, iC_eq] at this
    rw [this]
    have hne : a'.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last a').ne
    simp [Formalism.BranchingDeterminantCap.extM, hne]
  · have := embGL_CC (K := ℚ) (rfl : n + 1 = n + 1) g a' b'
    rw [iC_eq, iC_eq] at this
    rw [this]
    simp [Formalism.BranchingDeterminantCap.extM]

/- English proof (translation)
Substitute `hN` using the available equality. Establish `: (rename (lxRho (rfl : n + 1 = n + 1)) : _ →ₐ[ℚ] _).comp (rowAct ℚ (n` using `n) (Formalism.BranchingDeterminantCap.extM ℚ g.1)) = (rowAct ℚ (n := n + 1) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n (n + 1) rfl g : GL (Fin (n + 1)) ℚ).1).comp (rename (lxRho (rfl : n + 1 = n + 1))) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X]`.

Unfold `rowAct`. Rewrite using `[aeval_X, aeval_X, map_sum, inC_emb_extM]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, rename_C, rename_X]`. Both sides reduce to the same expression.

Conclude with `AlgHom.congr_fun this G`.
-/
lemma inC_rename_rowAct (g : GL (Fin n) ℚ) (G : MvPolynomial (Fin (n + 1) × Fin n) ℚ) :
    rename (lxRho hN) (rowAct ℚ (Formalism.BranchingDeterminantCap.extM ℚ g.1) G) =
      rowAct ℚ (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1 (rename (lxRho hN) G) := by
  subst hN
  have : (rename (lxRho (rfl : n + 1 = n + 1)) : _ →ₐ[ℚ] _).comp (rowAct ℚ (n := n) (Formalism.BranchingDeterminantCap.extM ℚ g.1)) =
      (rowAct ℚ (n := n + 1) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n (n + 1) rfl g : GL (Fin (n + 1)) ℚ).1).comp
        (rename (lxRho (rfl : n + 1 = n + 1))) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X]
    unfold rowAct
    rw [aeval_X, aeval_X, map_sum, inC_emb_extM]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, rename_C, rename_X]
    rfl
  exact AlgHom.congr_fun this G

/- English proof (translation)
Apply `(toUnit ℚ N).injective` to reduce the goal to its premises. Establish `hm` using `in_toUnit_mem s (extremal ℚ n s) (lm_extremal_mem s)`. Rewrite using `[in_toUnit_ioOne hN l s _ hm, map_smul]`. Establish `key : ∀ (x : Pol ℚ Unit n) (hx : x ∈ VV ℚ (fun _ : Unit => s)), x = hTen ℚ (fun _ : Unit => s) → (ioStd hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨x, hx⟩ : Pol ℚ Unit N) = ((∏ τ : Unit, (cBr hN l s : ℤ) : ℤ) : ℚ) • xiTen hN ℚ (fun _ : Unit => l) (fun _ : Unit => s)`. Introduce and unpack `x hx rfl`.

Conclude with `highest_weight_isotypic_unique (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) (fun _ => hI) (fun _ => hS) hx`. Rewrite using `[key _ hm (toUnit_eq_ten n _), toUnit_eq_ten]`. Simplify using `[xiTen]`.
-/
lemma inC_ioOne_hw (hI : Interlace hN l s) (hS : SameShift l s) :
    in_ioOne ℚ hN l s (extremal ℚ n s) = ((cBr hN l s : ℤ) : ℚ) • xiBr ℚ hN l s := by
  apply (toUnit ℚ N).injective
  have hm := in_toUnit_mem s (extremal ℚ n s) (lm_extremal_mem s)
  rw [in_toUnit_ioOne hN l s _ hm, map_smul]
  have key : ∀ (x : Pol ℚ Unit n) (hx : x ∈ VV ℚ (fun _ : Unit => s)), x = hTen ℚ (fun _ : Unit => s) →
      (ioStd hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨x, hx⟩ : Pol ℚ Unit N) =
        ((∏ τ : Unit, (cBr hN l s : ℤ) : ℤ) : ℚ) • xiTen hN ℚ (fun _ : Unit => l) (fun _ : Unit => s) := by
    rintro x hx rfl
    exact highest_weight_isotypic_unique (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) (fun _ => hI) (fun _ => hS) hx
  rw [key _ hm (toUnit_eq_ten n _), toUnit_eq_ten]
  simp [xiTen]

/- English proof (translation)
Apply `(toUnit ℚ N).injective` to reduce the goal to its premises. Establish `hp'` using `in_toUnit_mem s p hp`. Establish `hq' : toUnit ℚ n (sqAct ℚ n s h p) ∈ VV ℚ (fun _ : Unit => s)`. Rewrite using `[toUnit_sqAct]`. Conclude with `polyAction_mem_VV _ _ hp'`.

Rewrite using `[in_toUnit_ioOne hN l s _ hq', toUnit_sqAct N l, in_toUnit_ioOne hN l s _ hp']`. Establish `e` using `ioEquiv (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) (fun _ => hS) (fun _ => h) ⟨toUnit ℚ n p, hp'⟩ (polyAction_mem_VV _ _ hp')`. Rewrite using `[← e]`. Establish `e2 : (⟨toUnit ℚ n (sqAct ℚ n s h p), hq'⟩ : VV ℚ (fun _ : Unit => s)) = ⟨actP (fun _ : Unit => s) (fun _ => h) (toUnit ℚ n p), polyAction_mem_VV _ _ hp'⟩` using `Subtype.ext (toUnit_sqAct n s h p)`. Rewrite using `[e2]`.
-/
lemma inC_ioOne_sqAct (hS : SameShift l s) (h : GL (Fin n) ℚ) (p : MvPolynomial (Fin n × Fin n) ℚ)
    (hp : p ∈ nablaSq ℚ n s) :
    in_ioOne ℚ hN l s (sqAct ℚ n s h p) =
      sqAct ℚ N l (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h) (in_ioOne ℚ hN l s p) := by
  apply (toUnit ℚ N).injective
  have hp' := in_toUnit_mem s p hp
  have hq' : toUnit ℚ n (sqAct ℚ n s h p) ∈ VV ℚ (fun _ : Unit => s) := by
    rw [toUnit_sqAct]; exact polyAction_mem_VV _ _ hp'
  rw [in_toUnit_ioOne hN l s _ hq', toUnit_sqAct N l, in_toUnit_ioOne hN l s _ hp']
  have e := ioEquiv (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) (fun _ => hS) (fun _ => h)
    ⟨toUnit ℚ n p, hp'⟩ (polyAction_mem_VV _ _ hp')
  rw [← e]
  have e2 : (⟨toUnit ℚ n (sqAct ℚ n s h p), hq'⟩ : VV ℚ (fun _ : Unit => s)) =
      ⟨actP (fun _ : Unit => s) (fun _ => h) (toUnit ℚ n p), polyAction_mem_VV _ _ hp'⟩ := Subtype.ext (toUnit_sqAct n s h p)
  rw [e2]

/- English proof (translation)
Use `set h : GL (Fin n) ℚ := (inside₂ ℚ n g)⁻¹ with hh`. Establish `h1 : Matrix.transpose h.1 = g.1` using `Matrix.transpose_transpose _`. Establish `h2 : Matrix.transpose (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h : GL (Fin N) ℚ).1 = (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1`. Establish `e` using `congrArg Units.val (congrFun (embAll_tr (K := ℚ) hN (fun _ : Unit => g)) ())`. Rewrite `e` using `[invTrK_inv_coe]`.

Establish `e' : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h : GL (Fin N) ℚ).1 = Matrix.transpose (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1` using `e.symm`. Rewrite using `[e', Matrix.transpose_transpose]`. Establish `e` using `inC_ioOne_sqAct hN l s hS h p hp`. Unfold `sqAct at e`. Rewrite `e` using `[h1, h2, map_smul]`.

Establish `hd : detPow ℚ N (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h) l.detShift = detPow ℚ n h s.detShift`. Unfold `detPow`. Rewrite using `[det_embGL' hN, hS]`. Rewrite `e` using `[hd]`. Establish `hne : detPow ℚ n h s.detShift ≠ 0` using `by unfold detPow; exact Units.ne_zero _`.

Conclude with `smul_right_injective _ hne e`.
-/
lemma inC_ioOne_rowAct (hS : SameShift l s) (g : GL (Fin n) ℚ) (p : MvPolynomial (Fin n × Fin n) ℚ)
    (hp : p ∈ nablaSq ℚ n s) :
    in_ioOne ℚ hN l s (rowAct ℚ g.1 p) =
      rowAct ℚ (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1 (in_ioOne ℚ hN l s p) := by
  set h : GL (Fin n) ℚ := (inside₂ ℚ n g)⁻¹ with hh
  have h1 : Matrix.transpose h.1 = g.1 := Matrix.transpose_transpose _
  have h2 : Matrix.transpose (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h : GL (Fin N) ℚ).1 =
      (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1 := by
    have e := congrArg Units.val (congrFun (embAll_tr (K := ℚ) hN (fun _ : Unit => g)) ())
    rw [invTrK_inv_coe] at e
    have e' : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h : GL (Fin N) ℚ).1 =
        Matrix.transpose (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm g : GL (Fin N) ℚ).1 := e.symm
    rw [e', Matrix.transpose_transpose]
  have e := inC_ioOne_sqAct hN l s hS h p hp
  unfold sqAct at e
  rw [h1, h2, map_smul] at e
  have hd : detPow ℚ N (Formalism.MainNotions.PrimeDegreeVariant.embGL ℚ n N hN.symm h) l.detShift = detPow ℚ n h s.detShift := by
    unfold detPow
    rw [det_embGL' hN, hS]
  rw [hd] at e
  have hne : detPow ℚ n h s.detShift ≠ 0 := by unfold detPow; exact Units.ne_zero _
  exact smul_right_injective _ hne e

/- English proof (translation)
Take `⟨io', hio'⟩` from `LinearMap.exists_extend io`. Establish `hio : ∀ p (hp : p ∈ dualWeyl ℚ n n s.natW), io' p = io ⟨p, hp⟩`. Introduce `p hp`. Rewrite using `[← hio']`. Both sides reduce to the same expression.

Use `set d : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin N × Fin N) ℚ := (rename (lxRho hN) : _ →ₐ[ℚ] _).toLinearMap ∘ₗ io' - in_ioOne ℚ hN l s with hd`. Establish `hdv : ∀ p, d p = rename (lxRho hN) (io' p) - in_ioOne ℚ hN l s p` using `fun p => rfl`. Establish `hsg : Antitone s.natW` using `natW_antitone s`. Establish `key` using `inC_cyc s.natW hsg d ?_ ?_`. Introduce `v hv`.

Use `key v hv` as an intermediate fact. Rewrite `this` using `[hdv, hio v hv, sub_eq_zero]`. Conclude with `this`. Rewrite using `[hdv, hio _ (hwMem ℚ n n le_rfl s.natW hsg), hhw _ rfl, map_smul, lx_xi_rename hN l s hI hS, inC_cBr hN l s hS]`. Use `inC_ioOne_hw hN l s hI hS` as an intermediate fact.

Unfold `extremal at this`. Rewrite using `[this, sub_self]`. Introduce `g p hp h0`. Rewrite `h0` using `[hdv, hio p hp, sub_eq_zero]`. Establish `hp2` using `dualWeylRowStable ℚ n n s.natW g.1 p hp`.

Rewrite using `[hdv, hio _ hp2, heq g.1 ⟨p, hp⟩ ⟨_, hp2⟩ rfl, inC_rename_rowAct, h0, inC_ioOne_rowAct hN l s hS g p hp, sub_self]`.
-/
theorem inC_ident (hI : Interlace hN l s) (hS : SameShift l s)
    (io : ↥(dualWeyl ℚ n n s.natW) →ₗ[ℚ] MvPolynomial (Fin (n + 1) × Fin n) ℚ)
    (heq : ∀ (g : Matrix (Fin n) (Fin n) ℚ) (f f' : ↥(dualWeyl ℚ n n s.natW)),
      (f' : MvPolynomial (Fin n × Fin n) ℚ) = rowAct ℚ g (f : MvPolynomial (Fin n × Fin n) ℚ) →
        io f' = rowAct ℚ (Formalism.BranchingDeterminantCap.extM ℚ g) (io f))
    (hhw : ∀ h : ↥(dualWeyl ℚ n n s.natW), (h : MvPolynomial (Fin n × Fin n) ℚ) = hw ℚ le_rfl s.natW →
      io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamN hN l)) (fun i => (s.natW i : ℤ)) : ℤ) : ℚ) •
        Formalism.BranchingDeterminantCap.xiB ℚ (lamN hN l) s.natW) :
    ∀ (v : MvPolynomial (Fin n × Fin n) ℚ) (hv : v ∈ dualWeyl ℚ n n s.natW),
      rename (lxRho hN) (io ⟨v, hv⟩) = in_ioOne ℚ hN l s v := by
  obtain ⟨io', hio'⟩ := LinearMap.exists_extend io
  have hio : ∀ p (hp : p ∈ dualWeyl ℚ n n s.natW), io' p = io ⟨p, hp⟩ := by
    intro p hp
    rw [← hio']
    rfl
  set d : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin N × Fin N) ℚ :=
    (rename (lxRho hN) : _ →ₐ[ℚ] _).toLinearMap ∘ₗ io' - in_ioOne ℚ hN l s with hd
  have hdv : ∀ p, d p = rename (lxRho hN) (io' p) - in_ioOne ℚ hN l s p := fun p => rfl
  have hsg : Antitone s.natW := natW_antitone s
  have key := inC_cyc s.natW hsg d ?_ ?_
  · intro v hv
    have := key v hv
    rw [hdv, hio v hv, sub_eq_zero] at this
    exact this
  · rw [hdv, hio _ (hwMem ℚ n n le_rfl s.natW hsg), hhw _ rfl, map_smul, lx_xi_rename hN l s hI hS, inC_cBr hN l s hS]
    have := inC_ioOne_hw hN l s hI hS
    unfold extremal at this
    rw [this, sub_self]
  · intro g p hp h0
    rw [hdv, hio p hp, sub_eq_zero] at h0
    have hp2 := dualWeylRowStable ℚ n n s.natW g.1 p hp
    rw [hdv, hio _ hp2, heq g.1 ⟨p, hp⟩ ⟨_, hp2⟩ rfl, inC_rename_rowAct, h0, inC_ioOne_rowAct hN l s hS g p hp, sub_self]

end Ident

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

section D

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inD_fockQ {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockB f g := rfl

/- English proof (translation)
Rewrite using `[toUnit_eq_ten, toUnit_eq_ten, sd_fockB_ten]`. Simplify using the standard rewrite rules.
-/
theorem inD_fockB_toUnit {K : Type} [Field K] {k : ℕ} (f g : MvPolynomial (Fin k × Fin k) K) :
    fockB (toUnit K k f) (toUnit K k g) = fockB f g := by
  rw [toUnit_eq_ten, toUnit_eq_ten, sd_fockB_ten]
  simp

/- English proof (translation)
Establish `h` using `brTranspose (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨toUnit ℚ N F, in_toUnit_mem l F hF⟩ ⟨toUnit ℚ n v, in_toUnit_mem s v hv⟩`. Rewrite `h` using `[pairBK_apply, pairBK_apply, pairB_apply, pairB_apply, ← in_toUnit_ioOne]`. Establish `e : ((brStd hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨toUnit ℚ N F, in_toUnit_mem l F hF⟩ : VV ℚ (fun _ : Unit => s)) : Pol ℚ Unit n) = toUnit ℚ n (brOne ℚ hN l s F)`. Rewrite using `[toUnit_brOne]`. Both sides reduce to the same expression.

Rewrite `h` using `[e]`. Simplify using `only [inD_fockB_toUnit, extNormB, Finset.univ_unique, Finset.prod_singleton] at h`. Unfold `normFockQ`. Rewrite using `[inD_fockQ, inD_fockQ, inD_fockQ, inD_fockQ, div_eq_inv_mul, div_eq_inv_mul]`. Conclude with `h`.
-/
theorem inD_adj (F : MvPolynomial (Fin N × Fin N) ℚ) (hF : F ∈ nablaSq ℚ N l)
    (v : MvPolynomial (Fin n × Fin n) ℚ) (hv : v ∈ nablaSq ℚ n s) :
    normFockQ s (brOne ℚ hN l s F) v = normFockQ l F (in_ioOne ℚ hN l s v) := by
  have h := brTranspose (K := ℚ) hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨toUnit ℚ N F, in_toUnit_mem l F hF⟩
    ⟨toUnit ℚ n v, in_toUnit_mem s v hv⟩
  rw [pairBK_apply, pairBK_apply, pairB_apply, pairB_apply, ← in_toUnit_ioOne] at h
  have e : ((brStd hN (fun _ : Unit => l) (fun _ : Unit => s) ⟨toUnit ℚ N F, in_toUnit_mem l F hF⟩ :
      VV ℚ (fun _ : Unit => s)) : Pol ℚ Unit n) = toUnit ℚ n (brOne ℚ hN l s F) := by
    rw [toUnit_brOne]; rfl
  rw [e] at h
  simp only [inD_fockB_toUnit, extNormB, Finset.univ_unique, Finset.prod_singleton] at h
  unfold normFockQ
  rw [inD_fockQ, inD_fockQ, inD_fockQ, inD_fockQ, div_eq_inv_mul, div_eq_inv_mul]
  exact h

def inD_IoInt : Prop :=
  ∀ v₀ ∈ nablaSq ℤ n s, ∃ w₀ : MvPolynomial (Fin N × Fin N) ℤ,
    in_ioOne ℚ hN l s (map (Int.castRingHom ℚ) v₀) = map (Int.castRingHom ℚ) w₀

/- English proof (translation)
Establish `hF : map (Int.castRingHom ℚ) f₀ ∈ nablaSq ℚ N l` using `dualWeylMap ℤ ℚ _ N N _ f₀ (weylLeDual ℤ N N le_rfl _ (natW_antitone l) hf₀)`. Use `(factDelDualNabla n s _ (brOne_mem hN l s _)).1 fun g hg => ?_` and prove the remaining obligations. Take `⟨w₀, hw₀⟩` from `H g hg`. Establish `hg' : map (Int.castRingHom ℚ) g ∈ nablaSq ℚ n s` using `dualWeylMap ℤ ℚ _ n n _ g hg`. Rewrite using `[inD_adj hN l s _ hF _ hg', hw₀]`.

Establish `hw : w₀ ∈ nablaSq ℤ N l`. Use `(dualWeylIntRat N N _ w₀).2 ?_` and prove the remaining obligations. Rewrite using `[← hw₀]`. Conclude with `in_ioOne_mem hN l s _`. Conclude with `(factDelDualNabla N l _ hF).2 ⟨f₀, hf₀, rfl⟩ w₀ hw`.
-/
theorem inD_brInt_Q (H : inD_IoInt hN l s) (f₀ : MvPolynomial (Fin N × Fin N) ℤ) (hf₀ : f₀ ∈ delSq ℤ N l) :
    ∃ g ∈ delSq ℤ n s, map (Int.castRingHom ℚ) g = brOne ℚ hN l s (map (Int.castRingHom ℚ) f₀) := by
  have hF : map (Int.castRingHom ℚ) f₀ ∈ nablaSq ℚ N l :=
    dualWeylMap ℤ ℚ _ N N _ f₀ (weylLeDual ℤ N N le_rfl _ (natW_antitone l) hf₀)
  refine (factDelDualNabla n s _ (brOne_mem hN l s _)).1 fun g hg => ?_
  obtain ⟨w₀, hw₀⟩ := H g hg
  have hg' : map (Int.castRingHom ℚ) g ∈ nablaSq ℚ n s := dualWeylMap ℤ ℚ _ n n _ g hg
  rw [inD_adj hN l s _ hF _ hg', hw₀]
  have hw : w₀ ∈ nablaSq ℤ N l := by
    refine (dualWeylIntRat N N _ w₀).2 ?_
    rw [← hw₀]
    exact in_ioOne_mem hN l s _
  exact (factDelDualNabla N l _ hF).2 ⟨f₀, hf₀, rfl⟩ w₀ hw

/- English proof (translation)
Simplify using `only [toUnit, renameEquiv_apply, map_rename]`.
-/
theorem inD_map_toUnit {K K' : Type} [Field K] [Field K'] (j : K →+* K') (k : ℕ) (f : MvPolynomial (Fin k × Fin k) K) :
    map j (toUnit K k f) = toUnit K' k (map j f) := by
  simp only [toUnit, renameEquiv_apply, map_rename]

/- English proof (translation)
Apply `(toUnit K' n).injective` to reduce the goal to its premises. Rewrite using `[← inD_map_toUnit, toUnit_brOne, toUnit_brOne, ← inD_map_toUnit]`. Simplify using `only [brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, bc_map_smul]`. Rewrite using `[lb_map_projVV, lb_map_coefLast, lb_map_brConst]`.
-/
theorem inD_map_brOne {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] (j : K →+* K')
    (F : MvPolynomial (Fin N × Fin N) K) : map j (brOne K hN l s F) = brOne K' hN l s (map j F) := by
  apply (toUnit K' n).injective
  rw [← inD_map_toUnit, toUnit_brOne, toUnit_brOne, ← inD_map_toUnit]
  simp only [brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, bc_map_smul]
  rw [lb_map_projVV, lb_map_coefLast, lb_map_brConst]

/- English proof (translation)
Take `⟨g, hg, e⟩` from `inD_brInt_Q hN l s H f₀ hf₀`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Establish `hc : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ` using `RingHom.ext_int _ _`. Rewrite using `[← hc, ← map_map, ← map_map, e, inD_map_brOne]`.
-/
theorem inD_brInt (H : inD_IoInt hN l s) (f₀ : MvPolynomial (Fin N × Fin N) ℤ) (hf₀ : f₀ ∈ delSq ℤ N l) :
    ∃ g ∈ delSq ℤ n s, brOne ℂ hN l s (map (Int.castRingHom ℂ) f₀) = map (Int.castRingHom ℂ) g := by
  obtain ⟨g, hg, e⟩ := inD_brInt_Q hN l s H f₀ hf₀
  refine ⟨g, hg, ?_⟩
  have hc : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [← hc, ← map_map, ← map_map, e, inD_map_brOne]

end D

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility

section E

/- English proof (translation)
Introduce `i` and use `⟨by rw [Formalism.BranchingDeterminantCap.bmH_lamZ_castSucc]; exact Int.ofNat_le.mpr (h i).1, by rw [Formalism.BranchingDeterminantCap.bmH_lamZ_succ]; exact Int.ofNat_le.mpr (h i).2⟩`.
-/
theorem inE_il {n : ℕ} (lam sg : Fin n → ℕ) (h : Formalism.BranchingDeterminantCap.bmIL lam sg) :
    Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (sg i : ℤ)) := fun i =>
  ⟨by rw [Formalism.BranchingDeterminantCap.bmH_lamZ_castSucc]; exact Int.ofNat_le.mpr (h i).1, by rw [Formalism.BranchingDeterminantCap.bmH_lamZ_succ]; exact Int.ofNat_le.mpr (h i).2⟩

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Introduce `v₀ hv₀`. Take `⟨io, -, heq, hhw, hint⟩` from `inB_capInt (lamN hN l) s.natW (inE_il _ _ (lx_il hN l s hI hS))`. Establish `hv : map (Int.castRingHom ℚ) v₀ ∈ dualWeyl ℚ n n s.natW` using `dualWeylMap ℤ ℚ _ n n _ v₀ hv₀`. Take `⟨w₀, hw₀⟩` from `hint v₀ hv₀ hv`. Use `⟨rename (lxRho hN) w₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[← inC_ident hN l s hI hS io heq hhw _ hv, hw₀, map_rename]`.
-/
theorem inE_ioInt (hI : Interlace hN l s) (hS : SameShift l s) : inD_IoInt hN l s := by
  intro v₀ hv₀
  obtain ⟨io, -, heq, hhw, hint⟩ := inB_capInt (lamN hN l) s.natW (inE_il _ _ (lx_il hN l s hI hS))
  have hv : map (Int.castRingHom ℚ) v₀ ∈ dualWeyl ℚ n n s.natW := dualWeylMap ℤ ℚ _ n n _ v₀ hv₀
  obtain ⟨w₀, hw₀⟩ := hint v₀ hv₀ hv
  refine ⟨rename (lxRho hN) w₀, ?_⟩
  rw [← inC_ident hN l s hI hS io heq hhw _ hv, hw₀, map_rename]

/- English proof (translation)
The claim follows from `inD_brInt hN l s (inE_ioInt hN l s hI hS) f₀ hf₀`.
-/
theorem int_brOne (hI : Interlace hN l s) (hS : SameShift l s) (f₀ : MvPolynomial (Fin N × Fin N) ℤ)
    (hf₀ : f₀ ∈ delSq ℤ N l) :
    ∃ g ∈ delSq ℤ n s, brOne ℂ hN l s (map (Int.castRingHom ℂ) f₀) = map (Int.castRingHom ℂ) g :=
  inD_brInt hN l s (inE_ioInt hN l s hI hS) f₀ hf₀

open Formalism.MainNotions.product_first_zeroth_parts in

/- English proof (translation)
Introduce `f hf` and use `int_brOne _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI) f hf`.
-/
theorem int_member (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ)) :
    ∀ f ∈ delSq ℤ _ (lamTr D u τ), ∃ g ∈ delSq ℤ _ (sgTr D u τ),
      brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (MvPolynomial.map (Int.castRingHom ℂ) f) =
        MvPolynomial.map (Int.castRingHom ℂ) g :=
  fun f hf => int_brOne _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI) f hf

end E

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section NmA

/- English proof (translation)
Unfold `fockF fockB mfact`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map]`. Both sides reduce to the same expression.
-/
theorem nm_fockF_eq {σ : Type} (p q : MvPolynomial σ ℂ) :
    fockF p q = fockB p (MvPolynomial.map (starRingEnd ℂ) q) := by
  unfold fockF fockB mfact
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map]; rfl

/- English proof (translation)
Establish `h1` using `lm_ten_mem (fun _ : Unit => l) (fun _ => x) (fun _ => hx)`. Establish `h2` using `((Formalism.L2.DIV.baseChangeSpace_holds ℂ ℂ (starRingEnd ℂ) Unit k (fun _ => l)).1 _).1 h1`. Establish `h3` using `unit_mem l _ h2`. Rewrite `h3` using `[← toUnit_eq_ten]`. Establish `e : MvPolynomial.map (starRingEnd ℂ) (toUnit ℂ k x) = toUnit ℂ k (MvPolynomial.map (starRingEnd ℂ) x)`.

Simplify using `only [toUnit, renameEquiv_apply, map_rename]`. Rewrite `h3` using `[e, AlgEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem nm_conj_mem {k : ℕ} (l : DomWeight k) (x : MvPolynomial (Fin k × Fin k) ℂ) (hx : x ∈ nablaSq ℂ k l) :
    MvPolynomial.map (starRingEnd ℂ) x ∈ nablaSq ℂ k l := by
  have h1 := lm_ten_mem (fun _ : Unit => l) (fun _ => x) (fun _ => hx)
  have h2 := ((Formalism.L2.DIV.baseChangeSpace_holds ℂ ℂ (starRingEnd ℂ) Unit k (fun _ => l)).1 _).1 h1
  have h3 := unit_mem l _ h2
  rw [← toUnit_eq_ten] at h3
  have e : MvPolynomial.map (starRingEnd ℂ) (toUnit ℂ k x) = toUnit ℂ k (MvPolynomial.map (starRingEnd ℂ) x) := by
    simp only [toUnit, renameEquiv_apply, map_rename]
  rwa [e, AlgEquiv.symm_apply_apply] at h3

variable {N n : ℕ} (hN : N = n + 1)

def nmR (c : Fin n → ℕ) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
  LinearMap.mulLeft ℂ (∏ s : Fin n, (X (iL hN, iC hN s) : MvPolynomial (Fin N × Fin N) ℂ) ^ c s) ∘ₗ
    (rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2))).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nmR_apply (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) : nmR hN c p = raiseOne hN c p := rfl

/- English proof (translation)
Unfold `raiseOne`. Simplify using `only [map_mul, map_prod, map_pow, map_X, map_rename]`.
-/
theorem nm_R_conj (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (raiseOne hN c p) = raiseOne hN c (MvPolynomial.map (starRingEnd ℂ) p) := by
  unfold raiseOne
  simp only [map_mul, map_prod, map_pow, map_X, map_rename]

def nmJ (l : DomWeight N) (c : Fin n → ℕ) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
  (toUnit ℂ N).symm.toLinearMap ∘ₗ (VV ℂ (fun _ : Unit => l)).subtype ∘ₗ projVV (fun _ : Unit => l) ∘ₗ
    (toUnit ℂ N).toLinearMap ∘ₗ nmR hN c

/- English proof (translation)
The claim follows from `unit_mem l _ (Subtype.coe_prop _)`.
-/
theorem nmJ_mem (l : DomWeight N) (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) : nmJ hN l c p ∈ nablaSq ℂ N l :=
  unit_mem l _ (Subtype.coe_prop _)

/- English proof (translation)
Simplify using `[nmJ, nmR_apply]`.
-/
theorem nmJ_toUnit (l : DomWeight N) (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    toUnit ℂ N (nmJ hN l c p) = (projVV (fun _ : Unit => l) (toUnit ℂ N (raiseOne hN c p)) : Pol ℂ Unit N) := by
  simp [nmJ, nmR_apply]

/- English proof (translation)
Rewrite using `[← hwD_fockB_unit, ← toUnit_eq_ten, nmJ_toUnit, lb_proj_spec (fun _ : Unit => l) _ _ (lm_ten_mem (fun _ : Unit => l) _ fun _ => hf), toUnit_eq_ten, hwD_fockB_unit]`.
-/
theorem nmJ_fockB (l : DomWeight N) (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ nablaSq ℂ N l) :
    fockB (nmJ hN l c p) f = fockB (raiseOne hN c p) f := by
  rw [← hwD_fockB_unit, ← toUnit_eq_ten, nmJ_toUnit,
    lb_proj_spec (fun _ : Unit => l) _ _ (lm_ten_mem (fun _ : Unit => l) _ fun _ => hf), toUnit_eq_ten, hwD_fockB_unit]

/- English proof (translation)
Rewrite using `[nm_fockF_eq, nm_fockF_eq, nmJ_fockB hN l c p _ (nm_conj_mem l f hf)]`.
-/
theorem nmJ_fockF (l : DomWeight N) (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ nablaSq ℂ N l) :
    fockF (nmJ hN l c p) f = fockF (raiseOne hN c p) f := by
  rw [nm_fockF_eq, nm_fockF_eq, nmJ_fockB hN l c p _ (nm_conj_mem l f hf)]

def nmB (l : DomWeight N) (s : DomWeight n) : Fin n → ℕ := fun i => (bBr hN l s i).toNat

/- English proof (translation)
Rewrite using `[brOne_eq, fockB_smul_left', mul_assoc]`. Use `congr 1`. Establish `h1` using `fock_coef_ten (K := ℂ) (ι := Unit) hN (fun _ => nmB hN l s) (fun _ => F) (fun _ => v)`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton] at h1`. Rewrite using `[← h1]`.

Use `congr 1`. Rewrite using `[← hwD_fockB_unit, ← toUnit_eq_ten, prCoefOne, AlgEquiv.apply_symm_apply, lb_proj_spec (fun _ : Unit => s) _ _ (lm_ten_mem (fun _ : Unit => s) _ fun _ => hv), toUnit_eq_ten]`. Both sides reduce to the same expression.
-/
theorem nm_br_fockB (l : DomWeight N) (s : DomWeight n) (F : MvPolynomial (Fin N × Fin N) ℂ)
    (v : MvPolynomial (Fin n × Fin n) ℂ) (hv : v ∈ nablaSq ℂ n s) :
    fockB (brOne ℂ hN l s F) v * (bFac (fun _ : Unit => nmB hN l s) : ℂ) =
      (((cBr hN l s : ℤ) : ℂ) * kapBr ℂ hN l s) * fockB F (raiseOne hN (nmB hN l s) v) := by
  rw [brOne_eq, fockB_smul_left', mul_assoc]
  congr 1
  have h1 := fock_coef_ten (K := ℂ) (ι := Unit) hN (fun _ => nmB hN l s) (fun _ => F) (fun _ => v)
  simp only [Finset.univ_unique, Finset.prod_singleton] at h1
  rw [← h1]
  congr 1
  rw [← hwD_fockB_unit, ← toUnit_eq_ten, prCoefOne, AlgEquiv.apply_symm_apply,
    lb_proj_spec (fun _ : Unit => s) _ _ (lm_ten_mem (fun _ : Unit => s) _ fun _ => hv), toUnit_eq_ten]
  rfl

/- English proof (translation)
Rewrite using `[nm_fockF_eq, nm_fockF_eq, nm_R_conj, nm_br_fockB hN l s F _ (nm_conj_mem s v hv)]`.
-/
theorem nm_br_fockF (l : DomWeight N) (s : DomWeight n) (F : MvPolynomial (Fin N × Fin N) ℂ)
    (v : MvPolynomial (Fin n × Fin n) ℂ) (hv : v ∈ nablaSq ℂ n s) :
    fockF (brOne ℂ hN l s F) v * (bFac (fun _ : Unit => nmB hN l s) : ℂ) =
      (((cBr hN l s : ℤ) : ℂ) * kapBr ℂ hN l s) * fockF F (raiseOne hN (nmB hN l s) v) := by
  rw [nm_fockF_eq, nm_fockF_eq, nm_R_conj, nm_br_fockB hN l s F _ (nm_conj_mem s v hv)]

def nmExt (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
    (finSumFinEquiv.trans (finCongr hN.symm)).symm (finSumFinEquiv.trans (finCongr hN.symm)).symm

/- English proof (translation)
Rewrite using `[nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iC]`. Both sides reduce to the same expression.
-/
theorem nmExt_CC (g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : nmExt hN g (iC hN a) (iC hN b) = g a b := by
  rw [nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iC]; rfl

/- English proof (translation)
Rewrite using `[nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]`. Both sides reduce to the same expression.
-/
theorem nmExt_CL (g : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) : nmExt hN g (iC hN a) (iL hN) = 0 := by
  rw [nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]; rfl

/- English proof (translation)
Rewrite using `[nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]`. Both sides reduce to the same expression.
-/
theorem nmExt_LC (g : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) : nmExt hN g (iL hN) (iC hN a) = 0 := by
  rw [nmExt, Matrix.submatrix_apply, emb_symm_iC, emb_symm_iL]; rfl

/- English proof (translation)
Rewrite using `[nmExt, Matrix.submatrix_apply, emb_symm_iL]`. Simplify using the standard rewrite rules.
-/
theorem nmExt_LL (g : Matrix (Fin n) (Fin n) ℂ) : nmExt hN g (iL hN) (iL hN) = 1 := by
  rw [nmExt, Matrix.submatrix_apply, emb_symm_iL]; simp

/- English proof (translation)
Unfold `nmExt`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`. Simplify using the standard rewrite rules.
-/
theorem nmExt_conj (g : Matrix (Fin n) (Fin n) ℂ) : (nmExt hN g).conjTranspose = nmExt hN g.conjTranspose := by
  unfold nmExt
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

/- English proof (translation)
Unfold `rowAct`. Rewrite using `[aeval_X]`.
-/
theorem nm_rowAct_X {r k : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) (v : Fin r × Fin k) :
    rowAct ℂ g (X v) = ∑ b : Fin r, C (g v.1 b) * X (b, v.2) := by
  unfold rowAct
  rw [aeval_X]

/- English proof (translation)
Unfold `raiseOne`. Rewrite using `[map_mul, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, nm_rowAct_X, sum_split_CL hN]`.

Simplify using `only [nmExt_LC, nmExt_LL, map_zero, zero_mul, Finset.sum_const_zero, zero_add, map_one, one_mul]`. Establish `: (rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2))).comp (rowAct ℂ g) = (rowAct ℂ (nmExt hN g)).comp (rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2)))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply]`.

Rewrite using `[nm_rowAct_X, rename_X, nm_rowAct_X, sum_split_CL hN, map_sum]`. Simplify using `only [nmExt_CC, nmExt_CL, map_zero, zero_mul, add_zero, map_mul, rename_C, rename_X]`. Conclude with `AlgHom.congr_fun this p`.
-/
theorem nm_R_rowAct (c : Fin n → ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    raiseOne hN c (rowAct ℂ g p) = rowAct ℂ (nmExt hN g) (raiseOne hN c p) := by
  unfold raiseOne
  rw [map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, nm_rowAct_X, sum_split_CL hN]
    simp only [nmExt_LC, nmExt_LL, map_zero, zero_mul, Finset.sum_const_zero, zero_add, map_one, one_mul]
  · have : (rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2))).comp (rowAct ℂ g) =
        (rowAct ℂ (nmExt hN g)).comp (rename (fun v : Fin n × Fin n => (iC hN v.1, iC hN v.2))) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply]
      rw [nm_rowAct_X, rename_X, nm_rowAct_X, sum_split_CL hN, map_sum]
      simp only [nmExt_CC, nmExt_CL, map_zero, zero_mul, add_zero, map_mul, rename_C, rename_X]
    exact AlgHom.congr_fun this p

end NmA

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL Formalism.BranchingDeterminantCap

section NmB

/- English proof (translation)
Simplify using `[fockF]`.
-/
theorem nm_fockF_zero_left {σ : Type} (g : MvPolynomial σ ℂ) : fockF 0 g = 0 := by simp [fockF]

/- English proof (translation)
Distinguish the cases in `h : y = 0`. Substitute `h` using the available equality. Rewrite using `[nm_fockF_zero_left]`. Simplify using the standard rewrite rules. Conclude with `(fockPos σ y h).1.le`.
-/
theorem nm_fockF_nonneg {σ : Type} (y : MvPolynomial σ ℂ) : 0 ≤ (fockF y y).re := by
  by_cases h : y = 0
  · subst h; rw [nm_fockF_zero_left]; simp
  · exact (fockPos σ y h).1.le

/- English proof (translation)
Distinguish the cases in `h : y = 0`. Substitute `h` using the available equality. Rewrite using `[nm_fockF_zero_left]`. Simplify using the standard rewrite rules. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using `[(fockPos σ y h).2]`.
-/
theorem nm_fockF_self {σ : Type} (y : MvPolynomial σ ℂ) : fockF y y = (((fockF y y).re : ℝ) : ℂ) := by
  by_cases h : y = 0
  · subst h; rw [nm_fockF_zero_left]; simp
  · apply Complex.ext
    · simp
    · simp [(fockPos σ y h).2]

/- English proof (translation)
Rewrite using `[nm_fockF_eq, nm_fockF_eq, nm_fockF_eq, lb_fockB_sub_left]`.
-/
theorem nm_fockF_sub_left {σ : Type} (a b g : MvPolynomial σ ℂ) : fockF (a - b) g = fockF a g - fockF b g := by
  rw [nm_fockF_eq, nm_fockF_eq, nm_fockF_eq, lb_fockB_sub_left]

/- English proof (translation)
Distinguish the cases in `hg : g = 0`. Substitute `hg` using the available equality. Establish `: fockF f (0 : MvPolynomial σ ℂ) = 0` using `by rw [fischerInner_eq_star, nm_fockF_zero_left]; simp`. Rewrite `h` using `[this]`. Establish `hr : r = 0` using `by exact_mod_cast h.symm`.

Rewrite using `[hr, nm_fockF_zero_left]`. Simplify using the standard rewrite rules. Establish `hG` using `(fockPos σ g hg).1 set G := (fockF g g).re with hGdef set Fv := (fockF f f).re with hFdef`. Establish `h' : fockF g f = (r : ℂ)` using `by rw [fischerInner_eq_star, h]; simp`. Establish `key` using `nm_fockF_nonneg (f + ((-(r / G) : ℝ) : ℂ) • g)`.

Rewrite `key` using `[fischerInner_add_left, fischerInner_add_right, fischerInner_add_right, bs_fock_smul_left, bs_fock_smul_right, bs_fock_smul_left, bs_fock_smul_right, h, h', nm_fockF_self f, nm_fockF_self g, ← hGdef, ← hFdef]`. Establish `e : ((Fv : ℂ) + star ((-(r / G) : ℝ) : ℂ) * (r : ℂ) + (((-(r / G) : ℝ) : ℂ) * (r : ℂ) + ((-(r / G) : ℝ) : ℂ) * (star ((-(r / G) : ℝ) : ℂ) * (G : ℂ)))).re = Fv - r ^ 2 / G`. Establish `: star ((-(r / G) : ℝ) : ℂ) = ((-(r / G) : ℝ) : ℂ)` using `by simp`. Rewrite using `[this]`. Establish `: ((Fv : ℂ) + ((-(r / G) : ℝ) : ℂ) * (r : ℂ) + (((-(r / G) : ℝ) : ℂ) * (r : ℂ) + ((-(r / G) : ℝ) : ℂ) * (((-(r / G) : ℝ) : ℂ) * (G : ℂ)))) = ((Fv + -(r / G) * r + (-(r / G) * r + -(r / G) * (-(r / G) * G)) : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[this, Complex.ofReal_re]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[e]`. Establish `: r ^ 2 / G ≤ Fv` using `by linarith`.

Rewrite `this` using `[div_le_iff₀ hG]`. Then use the resulting hypothesis.
-/
theorem nm_cs_real {σ : Type} (f g : MvPolynomial σ ℂ) (r : ℝ) (h : fockF f g = (r : ℂ)) :
    r ^ 2 ≤ (fockF f f).re * (fockF g g).re := by
  by_cases hg : g = 0
  · subst hg
    have : fockF f (0 : MvPolynomial σ ℂ) = 0 := by rw [fischerInner_eq_star, nm_fockF_zero_left]; simp
    rw [this] at h
    have hr : r = 0 := by exact_mod_cast h.symm
    rw [hr, nm_fockF_zero_left]; simp
  · have hG := (fockPos σ g hg).1
    set G := (fockF g g).re with hGdef
    set Fv := (fockF f f).re with hFdef
    have h' : fockF g f = (r : ℂ) := by rw [fischerInner_eq_star, h]; simp
    have key := nm_fockF_nonneg (f + ((-(r / G) : ℝ) : ℂ) • g)
    rw [fischerInner_add_left, fischerInner_add_right, fischerInner_add_right, bs_fock_smul_left, bs_fock_smul_right, bs_fock_smul_left,
      bs_fock_smul_right, h, h', nm_fockF_self f, nm_fockF_self g, ← hGdef, ← hFdef] at key
    have e : ((Fv : ℂ) + star ((-(r / G) : ℝ) : ℂ) * (r : ℂ) + (((-(r / G) : ℝ) : ℂ) * (r : ℂ) +
        ((-(r / G) : ℝ) : ℂ) * (star ((-(r / G) : ℝ) : ℂ) * (G : ℂ)))).re = Fv - r ^ 2 / G := by
      have : star ((-(r / G) : ℝ) : ℂ) = ((-(r / G) : ℝ) : ℂ) := by simp
      rw [this]
      have : ((Fv : ℂ) + ((-(r / G) : ℝ) : ℂ) * (r : ℂ) + (((-(r / G) : ℝ) : ℂ) * (r : ℂ) +
        ((-(r / G) : ℝ) : ℂ) * (((-(r / G) : ℝ) : ℂ) * (G : ℂ)))) =
          ((Fv + -(r / G) * r + (-(r / G) * r + -(r / G) * (-(r / G) * G)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
      field_simp
      ring
    rw [e] at key
    have : r ^ 2 / G ≤ Fv := by linarith
    rwa [div_le_iff₀ hG] at this

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `(fockPos _ x hne).1` as an intermediate fact. Rewrite `this` using `[h x hx]`. Simplify using `at this`.
-/
theorem nm_zero_of {k : ℕ} (l : DomWeight k) (x : MvPolynomial (Fin k × Fin k) ℂ) (hx : x ∈ nablaSq ℂ k l)
    (h : ∀ f ∈ nablaSq ℂ k l, fockF x f = 0) : x = 0 := by
  by_contra hne
  have := (fockPos _ x hne).1
  rw [h x hx] at this
  simp at this

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
The claim follows from `dualWeylRowStable ℂ k k l.natW g f hf`.
-/
theorem nm_row_mem {k : ℕ} (l : DomWeight k) (g : Matrix (Fin k) (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ)
    (hf : f ∈ nablaSq ℂ k l) : rowAct ℂ g f ∈ nablaSq ℂ k l := dualWeylRowStable ℂ k k l.natW g f hf

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `nm_zero_of l _ (Submodule.sub_mem _ (nmJ_mem hN l c _) (nm_row_mem l _ _ (nmJ_mem hN l c _)))` to reduce the goal to its premises. Introduce `f hf`. Rewrite using `[nm_fockF_sub_left, nmJ_fockF hN l c _ f hf, nm_R_rowAct, fockRowAdj, fockRowAdj, nmJ_fockF hN l c _ _ (nm_row_mem l _ _ hf), sub_self]`.
-/
theorem nmJ_rowAct (c : Fin n → ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    nmJ hN l c (rowAct ℂ g p) = rowAct ℂ (nmExt hN g) (nmJ hN l c p) := by
  rw [← sub_eq_zero]
  apply nm_zero_of l _ (Submodule.sub_mem _ (nmJ_mem hN l c _) (nm_row_mem l _ _ (nmJ_mem hN l c _)))
  intro f hf
  rw [nm_fockF_sub_left, nmJ_fockF hN l c _ f hf, nm_R_rowAct, fockRowAdj, fockRowAdj,
    nmJ_fockF hN l c _ _ (nm_row_mem l _ _ hf), sub_self]

/- English proof (translation)
Set `D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ` to `fun p q => fockF (nmJ hN l c p) (nmJ hN l c q) * fockF (extremal ℂ n s) (extremal ℂ n s) - fockF (nmJ hN l c (extremal ℂ n s)) (nmJ hN l c (extremal ℂ n s)) * fockF p q`. Establish `H : BsForm s.natW D`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p p' q`. Simplify using `only [D, map_add, fischerInner_add_left]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c p q`. Simplify using `only [D, map_smul, bs_fock_smul_left]`. Expand and normalize the polynomial expressions, which then agree. Introduce `p q q'`.

Simplify using `only [D, map_add, fischerInner_add_right]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c p q`. Simplify using `only [D, map_smul, bs_fock_smul_right]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `g p _ q _`. Simplify using `only [D]`. Rewrite using `[nmJ_rowAct, nmJ_rowAct, fockRowAdj N N, fockRowAdj n n, nmExt_conj]`. Establish `h0 : D (hw ℂ le_rfl s.natW) (hw ℂ le_rfl s.natW) = 0`. Simplify using `only [D, extremal]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e` using `H.eq_zero (natW_antitone s) h0 p hp p hp`. Simplify using `only [D] at e`. Conclude with `sub_eq_zero.mp e`.
-/
theorem nmJ_iso (c : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ nablaSq ℂ n s) :
    fockF (nmJ hN l c p) (nmJ hN l c p) * fockF (extremal ℂ n s) (extremal ℂ n s) =
      fockF (nmJ hN l c (extremal ℂ n s)) (nmJ hN l c (extremal ℂ n s)) * fockF p p := by
  let D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ := fun p q =>
    fockF (nmJ hN l c p) (nmJ hN l c q) * fockF (extremal ℂ n s) (extremal ℂ n s) -
      fockF (nmJ hN l c (extremal ℂ n s)) (nmJ hN l c (extremal ℂ n s)) * fockF p q
  have H : BsForm s.natW D := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p p' q
      simp only [D, map_add, fischerInner_add_left]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_left]; ring
    · intro p q q'
      simp only [D, map_add, fischerInner_add_right]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_right]; ring
    · intro g p _ q _
      simp only [D]
      rw [nmJ_rowAct, nmJ_rowAct, fockRowAdj N N, fockRowAdj n n, nmExt_conj]
  have h0 : D (hw ℂ le_rfl s.natW) (hw ℂ le_rfl s.natW) = 0 := by
    simp only [D, extremal]; ring
  have e := H.eq_zero (natW_antitone s) h0 p hp p hp
  simp only [D] at e
  exact sub_eq_zero.mp e

end NmB

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL Formalism.BranchingDeterminantCap

section NmC

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Establish `h` using `highest_weight_isotypic_unique (K := ℂ) (ι := Unit) hN (fun _ => l) (fun _ => s) (fun _ => hI) (fun _ => hS) (hTen_mem _)`. Establish `h2 : ((ioStd hN (fun _ : Unit => l) (fun _ => s) ⟨hTen ℂ (fun _ : Unit => s), hTen_mem _⟩ : VV ℂ (fun _ : Unit => l)) : Pol ℂ Unit N) = ioConst hN ℂ (fun _ : Unit => l) (fun _ => s) • (projVV (fun _ : Unit => l) (raise hN (bExp hN (fun _ : Unit => l) (fun _ => s)) (hTen ℂ (fun _ …`. Simplify using `[ioStd]`. Rewrite `h` using `[h2]`. Establish `e : raise hN (bExp hN (fun _ : Unit => l) (fun _ => s)) (hTen ℂ (fun _ : Unit => s)) = ten fun _ : Unit => raiseOne hN (nmB hN l s) (extremal ℂ n s)`.

Unfold `hTen`. Rewrite using `[raise_ten]`. Both sides reduce to the same expression. Rewrite `h` using `[e]`. Apply `(toUnit ℂ N).injective` to reduce the goal to its premises.

Rewrite using `[map_smul, map_smul, nmJ_toUnit, toUnit_eq_ten, toUnit_eq_ten]`. Simplify `h` using `[xiTen]`.
-/
theorem nmJ_h (hI : Interlace hN l s) (hS : SameShift l s) :
    (ioConst hN ℂ (fun _ : Unit => l) (fun _ => s)) • nmJ hN l (nmB hN l s) (extremal ℂ n s) =
      ((cBr hN l s : ℤ) : ℂ) • xiBr ℂ hN l s := by
  have h := highest_weight_isotypic_unique (K := ℂ) (ι := Unit) hN (fun _ => l) (fun _ => s) (fun _ => hI) (fun _ => hS) (hTen_mem _)
  have h2 : ((ioStd hN (fun _ : Unit => l) (fun _ => s) ⟨hTen ℂ (fun _ : Unit => s), hTen_mem _⟩ :
      VV ℂ (fun _ : Unit => l)) : Pol ℂ Unit N) = ioConst hN ℂ (fun _ : Unit => l) (fun _ => s) •
        (projVV (fun _ : Unit => l) (raise hN (bExp hN (fun _ : Unit => l) (fun _ => s)) (hTen ℂ (fun _ : Unit => s))) :
          Pol ℂ Unit N) := by
    simp [ioStd]
  rw [h2] at h
  have e : raise hN (bExp hN (fun _ : Unit => l) (fun _ => s)) (hTen ℂ (fun _ : Unit => s)) =
      ten fun _ : Unit => raiseOne hN (nmB hN l s) (extremal ℂ n s) := by
    unfold hTen; rw [raise_ten]; rfl
  rw [e] at h
  apply (toUnit ℂ N).injective
  rw [map_smul, map_smul, nmJ_toUnit, toUnit_eq_ten, toUnit_eq_ten]
  simpa [xiTen] using h

/- English proof (translation)
Rewrite using `[← nm_fockF_self, nm_fockF_eq, lb_map_xiBr]`.
-/
theorem nm_fockB_xi : fockB (xiBr ℂ hN l s) (xiBr ℂ hN l s) = (((fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re : ℝ) : ℂ) := by
  rw [← nm_fockF_self, nm_fockF_eq, lb_map_xiBr]

/- English proof (translation)
Rewrite using `[← nm_fockF_self, nm_fockF_eq, lb_map_extremal]`.
-/
theorem nm_fockB_ext {k : ℕ} (l : DomWeight k) :
    fockB (extremal ℂ k l) (extremal ℂ k l) = (((fockF (extremal ℂ k l) (extremal ℂ k l)).re : ℝ) : ℂ) := by
  rw [← nm_fockF_self, nm_fockF_eq, lb_map_extremal]

/- English proof (translation)
Unfold `kapBr`. Rewrite using `[nm_fockB_xi, nm_fockB_ext]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nm_kap : kapBr ℂ hN l s = (((fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re /
    (fockF (extremal ℂ N l) (extremal ℂ N l)).re : ℝ) : ℂ) := by
  unfold kapBr
  rw [nm_fockB_xi, nm_fockB_ext]
  push_cast; rfl

/- English proof (translation)
Establish `h : ((kapBr ℝ hN l s : ℝ) : ℂ) = kapBr ℂ hN l s` using `lb_map_kapBr (K := ℝ) (K' := ℂ) Complex.ofRealHom hN l s`. Rewrite `h` using `[nm_kap]`. Conclude with `h` after adjusting the coercions.
-/
theorem nm_kapR : kapBr ℝ hN l s = (fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re /
    (fockF (extremal ℂ N l) (extremal ℂ N l)).re := by
  have h : ((kapBr ℝ hN l s : ℝ) : ℂ) = kapBr ℂ hN l s := lb_map_kapBr (K := ℝ) (K' := ℂ) Complex.ofRealHom hN l s
  rw [nm_kap] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `ioConst`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton]`. Rewrite using `[nm_fockB_xi, nm_fockB_ext]`. Establish `: (bFac (fun _ : Unit => nmB hN l s)) = ∏ i, (bExp hN (fun _ : Unit => l) (fun _ => s) default i).factorial`. Simplify using `[bFac, nmB, bExp]`.

Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nm_ioConst : ioConst hN ℂ (fun _ : Unit => l) (fun _ => s) =
    (((((cBr hN l s : ℤ) : ℝ)) * (fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re /
      ((fockF (extremal ℂ n s) (extremal ℂ n s)).re * ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ)) : ℝ) : ℂ) := by
  unfold ioConst
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [nm_fockB_xi, nm_fockB_ext]
  have : (bFac (fun _ : Unit => nmB hN l s)) = ∏ i, (bExp hN (fun _ : Unit => l) (fun _ => s) default i).factorial := by
    simp [bFac, nmB, bExp]
  rw [this]
  push_cast
  rfl

/- English proof (translation)
Establish `JHv : JH = hs ^ 2 * b ^ 2 / x`. Establish `h1 : (cR * x / (hs * b)) * (cR * x / (hs * b)) = cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2)` using `by field_simp`. Rewrite `e4` using `[h1]`. Establish `h2 : cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2) ≠ 0` using `by positivity`. Establish `h3 : JH = cR * cR * x / (cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2))`.

Rewrite using `[eq_div_iff h2, mul_comm]`. Conclude with `e4`. Rewrite using `[h3]`. Clear the denominators using the available nonvanishing facts. Establish `JWv : JW = hs * b ^ 2 * W / x`.

Establish `: JW = JH * W / hs` using `by rw [← e3]; field_simp`. Rewrite using `[this, JHv]`. Clear the denominators using the available nonvanishing facts. Break down `W0.eq_or_lt with h0 | hWpos` into its components or cases. Rewrite using `[← h0, zero_div]`.

Check the signs of the components of the expression. Rewrite `e2` using `[JWv]`. Establish `e5 : W * hl ^ 2 ≤ cR ^ 2 * x * Fv * hs`. Establish `e6 : (W * b / (cR * (x / hl))) ^ 2 = W ^ 2 * b ^ 2 * hl ^ 2 / (cR ^ 2 * x ^ 2)` using `by field_simp`. Rewrite `e2` using `[e6, div_le_iff₀ (by positivity)]`.

Establish `e7 : Fv * (hs * b ^ 2 * W / x) * (cR ^ 2 * x ^ 2) = (cR ^ 2 * x * Fv * hs) * (W * b ^ 2)` using `by field_simp`. Rewrite `e2` using `[e7]`. Establish `e8 : W ^ 2 * b ^ 2 * hl ^ 2 = (W * hl ^ 2) * (W * b ^ 2)` using `by ring`. Rewrite `e2` using `[e8]`. Conclude with `le_of_mul_le_mul_right e2 (by positivity)`.

Rewrite using `[div_le_iff₀ hspos]`. Establish `: cR ^ 2 * (x / hl) * (Fv / hl) * hs = (cR ^ 2 * x * Fv * hs) / hl ^ 2` using `by field_simp`. Rewrite using `[this, le_div_iff₀ (by positivity)]`. Conclude with `e5`.
-/
theorem nm_alg (W Fv JW JH x hs hl b cR : ℝ) (xpos : 0 < x) (hspos : 0 < hs) (hlpos : 0 < hl) (bpos : 0 < b)
    (cne : cR ≠ 0) (W0 : 0 ≤ W) (F0 : 0 ≤ Fv) (e2 : (W * b / (cR * (x / hl))) ^ 2 ≤ Fv * JW) (e3 : JW * hs = JH * W)
    (e4 : (cR * x / (hs * b)) * (cR * x / (hs * b)) * JH = cR * cR * x) :
    W / hs ≤ cR ^ 2 * (x / hl) * (Fv / hl) := by
  have JHv : JH = hs ^ 2 * b ^ 2 / x := by
    have h1 : (cR * x / (hs * b)) * (cR * x / (hs * b)) = cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2) := by field_simp
    rw [h1] at e4
    have h2 : cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2) ≠ 0 := by positivity
    have h3 : JH = cR * cR * x / (cR ^ 2 * x ^ 2 / (hs ^ 2 * b ^ 2)) := by
      rw [eq_div_iff h2, mul_comm]; exact e4
    rw [h3]; field_simp
  have JWv : JW = hs * b ^ 2 * W / x := by
    have : JW = JH * W / hs := by rw [← e3]; field_simp
    rw [this, JHv]; field_simp
  rcases W0.eq_or_lt with h0 | hWpos
  · rw [← h0, zero_div]; positivity
  · rw [JWv] at e2
    have e5 : W * hl ^ 2 ≤ cR ^ 2 * x * Fv * hs := by
      have e6 : (W * b / (cR * (x / hl))) ^ 2 = W ^ 2 * b ^ 2 * hl ^ 2 / (cR ^ 2 * x ^ 2) := by field_simp
      rw [e6, div_le_iff₀ (by positivity)] at e2
      have e7 : Fv * (hs * b ^ 2 * W / x) * (cR ^ 2 * x ^ 2) = (cR ^ 2 * x * Fv * hs) * (W * b ^ 2) := by field_simp
      rw [e7] at e2
      have e8 : W ^ 2 * b ^ 2 * hl ^ 2 = (W * hl ^ 2) * (W * b ^ 2) := by ring
      rw [e8] at e2
      exact le_of_mul_le_mul_right e2 (by positivity)
    rw [div_le_iff₀ hspos]
    have : cR ^ 2 * (x / hl) * (Fv / hl) * hs = (cR ^ 2 * x * Fv * hs) / hl ^ 2 := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact e5

/- English proof (translation)
Use `set w := brOne ℂ hN l s f with hw`. Establish `hwm : w ∈ nablaSq ℂ n s` using `brOne_mem hN l s f`. Use `set x := (fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re with hx`. Use `set hs := (fockF (extremal ℂ n s) (extremal ℂ n s)).re with hhs`. Use `set hl := (fockF (extremal ℂ N l) (extremal ℂ N l)).re with hhl`.

Use `set b := ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ) with hb`. Use `set cR := ((cBr hN l s : ℤ) : ℝ) with hcR`. Use `set W := (fockF w w).re with hW`. Use `set Fv := (fockF f f).re with hFv`. Use `set JW := (fockF (nmJ hN l (nmB hN l s) w) (nmJ hN l (nmB hN l s) w)).re with hJW`.

Use `set JH := (fockF (nmJ hN l (nmB hN l s) (extremal ℂ n s)) (nmJ hN l (nmB hN l s) (extremal ℂ n s))).re with hJH`. Establish `xpos : 0 < x` using `(fockPos _ _ (xiBr_ne hN l s hI hS)).1`. Establish `hspos : 0 < hs` using `(fockPos _ _ (lm_extremal_ne s)).1`. Establish `hlpos : 0 < hl` using `(fockPos _ _ (lm_extremal_ne l)).1`. Establish `bpos : 0 < b`.

Rewrite using `[hb]`. Establish `: bFac (fun _ : Unit => nmB hN l s) ≠ 0`. Unfold `bFac`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions.

Establish `cne : cR ≠ 0` using `by rw [hcR]; exact_mod_cast cBr_ne_zero hN l s hI`. Establish `W0 : 0 ≤ W` using `nm_fockF_nonneg w`. Establish `F0 : 0 ≤ Fv` using `nm_fockF_nonneg f`. Establish `E1` using `nm_br_fockF hN l s f w hwm`. Establish `E1' : fockF f (raiseOne hN (nmB hN l s) w) = fockF f (nmJ hN l (nmB hN l s) w)`.

Rewrite using `[fischerInner_eq_star, fischerInner_eq_star f, nmJ_fockF hN l _ w f hf]`. Rewrite `E1` using `[← hw, E1', nm_fockF_self w, ← hW, nm_kap, ← hx, ← hhl]`. Establish `hr : fockF f (nmJ hN l (nmB hN l s) w) = ((W * b / (cR * (x / hl)) : ℝ) : ℂ)`. Establish `hne : ((cBr hN l s : ℤ) : ℂ) * ((x / hl : ℝ) : ℂ) ≠ 0`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations.

Conclude with `cBr_ne_zero hN l s hI` after adjusting the coercions. Conclude with `(div_pos xpos hlpos).ne'` after adjusting the coercions. Establish `: fockF f (nmJ hN l (nmB hN l s) w) = ((W : ℝ) : ℂ) * ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℂ) / (((cBr hN l s : ℤ) : ℂ) * ((x / hl : ℝ) : ℂ))`. Rewrite using `[eq_div_iff hne, E1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hb, hcR]`. Use `push_cast`. Both sides reduce to the same expression. Establish `e2` using `nm_cs_real f _ _ hr`. Rewrite `e2` using `[← hFv, ← hJW]`.

Establish `E3` using `nmJ_iso hN l s (nmB hN l s) w hwm`. Rewrite `E3` using `[nm_fockF_self (nmJ hN l (nmB hN l s) w), nm_fockF_self (extremal ℂ n s), nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s)), nm_fockF_self w, ← hJW, ← hhs, ← hJH, ← hW]`. Establish `e3 : JW * hs = JH * W` using `by exact_mod_cast E3`. Establish `E4` using `congrArg (fun y => fockF y y) (nmJ_h hN l s hI hS)`. Simplify using `only [fockF_smul_smul] at E4`.

Rewrite `E4` using `[nm_ioConst, ← hx, ← hhs, ← hb, ← hcR, nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s)), ← hJH, nm_fockF_self (xiBr ℂ hN l s), ← hx]`. Establish `e4 : (cR * x / (hs * b)) * (cR * x / (hs * b)) * JH = cR * cR * x`. Establish `s1 : star ((cR * x / (hs * b) : ℝ) : ℂ) = ((cR * x / (hs * b) : ℝ) : ℂ)` using `by simp`. Establish `s2 : star ((cBr hN l s : ℤ) : ℂ) = ((cBr hN l s : ℤ) : ℂ)` using `by simp`. Rewrite `E4` using `[s1, s2]`.

Establish `c2 : ((cBr hN l s : ℤ) : ℂ) = ((cR : ℝ) : ℂ)` using `by rw [hcR]; push_cast; rfl`. Rewrite `E4` using `[c2]`. Conclude with `E4` after adjusting the coercions. Establish `g1 : (normFock s w w).re = W / hs`. Unfold `normFock`.

Rewrite using `[nm_fockF_self w, nm_fockF_self (extremal ℂ n s), ← hW, ← hhs, ← Complex.ofReal_div, Complex.ofReal_re]`. Establish `g2 : (normFock l f f).re = Fv / hl`. Unfold `normFock`. Rewrite using `[nm_fockF_self f, nm_fockF_self (extremal ℂ N l), ← hFv, ← hhl, ← Complex.ofReal_div, Complex.ofReal_re]`. Rewrite using `[g1, g2, nm_kapR, ← hx, ← hhl]`.

Conclude with `nm_alg W Fv JW JH x hs hl b cR xpos hspos hlpos bpos cne W0 F0 e2 e3 e4`.
-/
theorem nm_le (hI : Interlace hN l s) (hS : SameShift l s) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ nablaSq ℂ N l) :
    (normFock s (brOne ℂ hN l s f) (brOne ℂ hN l s f)).re ≤
      (((cBr hN l s : ℤ) : ℝ) ^ 2 * kapBr ℝ hN l s) * (normFock l f f).re := by
  set w := brOne ℂ hN l s f with hw
  have hwm : w ∈ nablaSq ℂ n s := brOne_mem hN l s f
  set x := (fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re with hx
  set hs := (fockF (extremal ℂ n s) (extremal ℂ n s)).re with hhs
  set hl := (fockF (extremal ℂ N l) (extremal ℂ N l)).re with hhl
  set b := ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ) with hb
  set cR := ((cBr hN l s : ℤ) : ℝ) with hcR
  set W := (fockF w w).re with hW
  set Fv := (fockF f f).re with hFv
  set JW := (fockF (nmJ hN l (nmB hN l s) w) (nmJ hN l (nmB hN l s) w)).re with hJW
  set JH := (fockF (nmJ hN l (nmB hN l s) (extremal ℂ n s)) (nmJ hN l (nmB hN l s) (extremal ℂ n s))).re with hJH
  have xpos : 0 < x := (fockPos _ _ (xiBr_ne hN l s hI hS)).1
  have hspos : 0 < hs := (fockPos _ _ (lm_extremal_ne s)).1
  have hlpos : 0 < hl := (fockPos _ _ (lm_extremal_ne l)).1
  have bpos : 0 < b := by
    rw [hb]
    have : bFac (fun _ : Unit => nmB hN l s) ≠ 0 := by
      unfold bFac
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _
    exact_mod_cast Nat.pos_of_ne_zero this
  have cne : cR ≠ 0 := by rw [hcR]; exact_mod_cast cBr_ne_zero hN l s hI
  have W0 : 0 ≤ W := nm_fockF_nonneg w
  have F0 : 0 ≤ Fv := nm_fockF_nonneg f

  have E1 := nm_br_fockF hN l s f w hwm
  have E1' : fockF f (raiseOne hN (nmB hN l s) w) = fockF f (nmJ hN l (nmB hN l s) w) := by
    rw [fischerInner_eq_star, fischerInner_eq_star f, nmJ_fockF hN l _ w f hf]
  rw [← hw, E1', nm_fockF_self w, ← hW, nm_kap, ← hx, ← hhl] at E1
  have hr : fockF f (nmJ hN l (nmB hN l s) w) = ((W * b / (cR * (x / hl)) : ℝ) : ℂ) := by
    have hne : ((cBr hN l s : ℤ) : ℂ) * ((x / hl : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast cBr_ne_zero hN l s hI
      · exact_mod_cast (div_pos xpos hlpos).ne'
    have : fockF f (nmJ hN l (nmB hN l s) w) = ((W : ℝ) : ℂ) * ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℂ) /
        (((cBr hN l s : ℤ) : ℂ) * ((x / hl : ℝ) : ℂ)) := by
      rw [eq_div_iff hne, E1]; ring
    rw [this, hb, hcR]
    push_cast
    rfl
  have e2 := nm_cs_real f _ _ hr
  rw [← hFv, ← hJW] at e2

  have E3 := nmJ_iso hN l s (nmB hN l s) w hwm
  rw [nm_fockF_self (nmJ hN l (nmB hN l s) w), nm_fockF_self (extremal ℂ n s),
    nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s)), nm_fockF_self w, ← hJW, ← hhs, ← hJH, ← hW] at E3
  have e3 : JW * hs = JH * W := by exact_mod_cast E3

  have E4 := congrArg (fun y => fockF y y) (nmJ_h hN l s hI hS)
  simp only [fockF_smul_smul] at E4
  rw [nm_ioConst, ← hx, ← hhs, ← hb, ← hcR, nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s)), ← hJH,
    nm_fockF_self (xiBr ℂ hN l s), ← hx] at E4
  have e4 : (cR * x / (hs * b)) * (cR * x / (hs * b)) * JH = cR * cR * x := by
    have s1 : star ((cR * x / (hs * b) : ℝ) : ℂ) = ((cR * x / (hs * b) : ℝ) : ℂ) := by simp
    have s2 : star ((cBr hN l s : ℤ) : ℂ) = ((cBr hN l s : ℤ) : ℂ) := by simp
    rw [s1, s2] at E4
    have c2 : ((cBr hN l s : ℤ) : ℂ) = ((cR : ℝ) : ℂ) := by rw [hcR]; push_cast; rfl
    rw [c2] at E4
    exact_mod_cast E4

  have g1 : (normFock s w w).re = W / hs := by
    unfold normFock
    rw [nm_fockF_self w, nm_fockF_self (extremal ℂ n s), ← hW, ← hhs, ← Complex.ofReal_div, Complex.ofReal_re]
  have g2 : (normFock l f f).re = Fv / hl := by
    unfold normFock
    rw [nm_fockF_self f, nm_fockF_self (extremal ℂ N l), ← hFv, ← hhl, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [g1, g2, nm_kapR, ← hx, ← hhl]
  exact nm_alg W Fv JW JH x hs hl b cR xpos hspos hlpos bpos cne W0 F0 e2 e3 e4

end NmC

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL Formalism.BranchingDeterminantCap

section NmD

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Unfold `normFock`. Rewrite using `[nm_fockF_self f, nm_fockF_self (extremal ℂ k l), ← Complex.ofReal_div, Complex.ofReal_re]`. Conclude with `div_pos (fockPos _ f hf).1 (fockPos _ _ (lm_extremal_ne l)).1`.
-/
theorem nm_normFock_pos {k : ℕ} (l : DomWeight k) (f : MvPolynomial (Fin k × Fin k) ℂ) (hf : f ≠ 0) :
    0 < (normFock l f f).re := by
  unfold normFock
  rw [nm_fockF_self f, nm_fockF_self (extremal ℂ k l), ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_pos (fockPos _ f hf).1 (fockPos _ _ (lm_extremal_ne l)).1

/- English proof (translation)
Rewrite using `[nm_kapR]`. Conclude with `div_pos (fockPos _ _ (xiBr_ne hN l s hI hS)).1 (fockPos _ _ (lm_extremal_ne l)).1`.
-/
theorem nm_kapR_pos (hI : Interlace hN l s) (hS : SameShift l s) : 0 < kapBr ℝ hN l s := by
  rw [nm_kapR]
  exact div_pos (fockPos _ _ (xiBr_ne hN l s hI hS)).1 (fockPos _ _ (lm_extremal_ne l)).1

/- English proof (translation)
Rewrite using `[nm_kapR]`. Unfold `normFock`. Use `conv_lhs => rw [nm_fockF_self (xiBr ℂ hN l s), nm_fockF_self (extremal ℂ N l)]`. Rewrite using `[← Complex.ofReal_div, Complex.ofReal_re]`.
-/
theorem nm_norm_xi : (normFock l (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re = kapBr ℝ hN l s := by
  rw [nm_kapR]
  unfold normFock
  conv_lhs => rw [nm_fockF_self (xiBr ℂ hN l s), nm_fockF_self (extremal ℂ N l)]
  rw [← Complex.ofReal_div, Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[brOne_xi hN l s hI hS]`. Unfold `normFock`. Rewrite using `[fockF_smul_smul, mul_div_assoc, div_self]`. Establish `e : ((cBr hN l s : ℤ) : ℂ) * kapBr ℂ hN l s = ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ)`. Establish `h : ((kapBr ℝ hN l s : ℝ) : ℂ) = kapBr ℂ hN l s` using `lb_map_kapBr (K := ℝ) (K' := ℂ) Complex.ofRealHom hN l s`.

Rewrite using `[← h]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `s1 : star ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ) = ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ)` using `by simp`.

Rewrite using `[s1, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h0`. Use `(fockPos _ _ (lm_extremal_ne (K := ℂ) s)).1` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`.
-/
theorem nm_norm_br_xi (hI : Interlace hN l s) (hS : SameShift l s) :
    (normFock s (brOne ℂ hN l s (xiBr ℂ hN l s)) (brOne ℂ hN l s (xiBr ℂ hN l s))).re =
      (((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s) ^ 2 := by
  rw [brOne_xi hN l s hI hS]
  unfold normFock
  rw [fockF_smul_smul, mul_div_assoc, div_self]
  · have e : ((cBr hN l s : ℤ) : ℂ) * kapBr ℂ hN l s = ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ) := by
      have h : ((kapBr ℝ hN l s : ℝ) : ℂ) = kapBr ℂ hN l s := lb_map_kapBr (K := ℝ) (K' := ℂ) Complex.ofRealHom hN l s
      rw [← h]; push_cast; rfl
    rw [e]
    have s1 : star ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ) = ((((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s : ℝ) : ℂ) := by simp
    rw [s1, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · intro h0
    have := (fockPos _ _ (lm_extremal_ne (K := ℂ) s)).1
    rw [h0] at this
    simp at this

/- English proof (translation)
Establish `kpos` using `nm_kapR_pos hN l s hI hS`. Establish `hval : Real.sqrt (((cBr hN l s : ℤ) : ℝ) ^ 2 * kapBr ℝ hN l s) = |((cBr hN l s : ℤ) : ℝ)| * Real.sqrt (kapBr ℝ hN l s)`. Rewrite using `[Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]`. Prove the components needed by the constructor for the conclusion. Use `⟨xiBr ℂ hN l s, ⟨xiBr_mem hN l s hI hS, xiBr_ne hN l s hI hS⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[nm_norm_br_xi hN l s hI hS, nm_norm_xi, ← hval]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `_ ⟨f, ⟨hf, hne⟩, rfl⟩`.

Simplify using `only`. Rewrite using `[← hval]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ (nm_normFock_pos l f hne)]`. Conclude with `nm_le hN l s hI hS f hf`.
-/
theorem nm_sup (hI : Interlace hN l s) (hS : SameShift l s) :
    IsGreatest ((fun f => Real.sqrt ((normFock s (brOne ℂ hN l s f) (brOne ℂ hN l s f)).re / (normFock l f f).re)) ''
      {f | f ∈ nablaSq ℂ N l ∧ f ≠ 0}) (|((cBr hN l s : ℤ) : ℝ)| * Real.sqrt (kapBr ℝ hN l s)) := by
  have kpos := nm_kapR_pos hN l s hI hS
  have hval : Real.sqrt (((cBr hN l s : ℤ) : ℝ) ^ 2 * kapBr ℝ hN l s) =
      |((cBr hN l s : ℤ) : ℝ)| * Real.sqrt (kapBr ℝ hN l s) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  constructor
  · refine ⟨xiBr ℂ hN l s, ⟨xiBr_mem hN l s hI hS, xiBr_ne hN l s hI hS⟩, ?_⟩
    simp only
    rw [nm_norm_br_xi hN l s hI hS, nm_norm_xi, ← hval]
    congr 1
    field_simp
  · rintro _ ⟨f, ⟨hf, hne⟩, rfl⟩
    simp only
    rw [← hval]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (nm_normFock_pos l f hne)]
    exact nm_le hN l s hI hS f hf

end NmD

section NmRec

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Introduce `τ hI`. Establish `hI'` using `(interlace_iff _ _ (Nm_succ D.R)).1 hI`. Establish `hS` using `sameShiftTr D u τ hI`. Unfold `opNorm beOnVal`. Establish `e1 : normFock ((D.fm u).sg τ) = normFock (sgTr D u τ)`.

Use function extensionality and compare the values at `a b`. Unfold `normFock sgTr`. Rewrite using `[extremal_wSh]`. Establish `e2 : normFock ((D.fm u).lam D.R.m τ) = normFock (lamTr D u τ)`. Use function extensionality and compare the values at `a b`.

Unfold `normFock lamTr`. Rewrite using `[extremal_wSh]`. Establish `e3 : delSq ℂ _ ((D.fm u).lam D.R.m τ) = nablaSq ℂ _ (lamTr D u τ)`. Rewrite using `[nablaSq_eq_delSq]`. Unfold `lamTr`.

Rewrite using `[delSq_wSh]`. Rewrite using `[e1, e2, e3]`. Conclude with `(nm_sup _ _ _ hI' hS).csSup_eq`.
-/
theorem nm_beOnEq (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : BeOnEq D u := by
  intro τ hI
  have hI' := (interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := sameShiftTr D u τ hI
  unfold opNorm beOnVal
  have e1 : normFock ((D.fm u).sg τ) = normFock (sgTr D u τ) := by
    funext a b; unfold normFock sgTr; rw [extremal_wSh]
  have e2 : normFock ((D.fm u).lam D.R.m τ) = normFock (lamTr D u τ) := by
    funext a b; unfold normFock lamTr; rw [extremal_wSh]
  have e3 : delSq ℂ _ ((D.fm u).lam D.R.m τ) = nablaSq ℂ _ (lamTr D u τ) := by
    rw [nablaSq_eq_delSq]; unfold lamTr; rw [delSq_wSh]
  rw [e1, e2, e3]
  exact (nm_sup _ _ _ hI' hS).csSup_eq

/- English proof (translation)
Introduce `f hf`. Establish `hI'` using `(interlace_iff _ _ (Nm_succ D.R)).1 hI`. Establish `hS` using `sameShiftTr D u τ hI`. Rewrite `hf` using `[← nablaSq_eq_delSq]`. Use `(nm_le _ _ _ hI' hS f hf).trans (mul_le_mul_of_nonneg_right hc ?_)` and prove the remaining obligations.

Distinguish the cases in `h0 : f = 0`. Substitute `h0` using the available equality. Simplify using `[normFock, nm_fockF_zero_left]`. Conclude with `(nm_normFock_pos _ f h0).le`.
-/
theorem nm_hB_of (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ))
    (hc : ((cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ≤
      Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) ^ 2) :
    ∀ f ∈ delSq ℂ _ (lamTr D u τ),
      (normFock (sgTr D u τ) (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
        (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤
        Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) ^ 2 * (normFock (lamTr D u τ) f f).re := by
  intro f hf
  have hI' := (interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := sameShiftTr D u τ hI
  rw [← nablaSq_eq_delSq] at hf
  refine (nm_le _ _ _ hI' hS f hf).trans (mul_le_mul_of_nonneg_right hc ?_)
  by_cases h0 : f = 0
  · subst h0; simp [normFock, nm_fockF_zero_left]
  · exact (nm_normFock_pos _ f h0).le

end NmRec

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL Formalism.BranchingDeterminantCap

section NmE

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Introduce `i`. Establish `h` using `hI i`. Unfold `aBr bBr at h`. Rewrite using `[lx_lamF_castSucc, lx_lamF_succ]`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem nm_il (hI : Br.Interlace hN l s) : Formalism.BranchingDeterminantCap.Interlace (lxLamF hN l) s.w := by
  intro i
  have h := hI i
  unfold aBr bBr at h
  rw [lx_lamF_castSucc, lx_lamF_succ]
  constructor <;> omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normalized_first_difference_eq : Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w = Formalism.MainNotions.PrimeDegreeVariant.D1 hN.symm l s := rfl

/- English proof (translation)
Establish `hil` using `nm_il hN l s hI`. Establish `hc` using `(Formalism.BranchingDeterminantCap.capacity_constant_bound n _ _ hil).2`. Establish `hd1 : 0 ≤ Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w` using `(Formalism.BranchingDeterminantCap.interlaceIdent n _ _ hil).2.2.2.1`. Rewrite `hc` using `[← cBr_eq_cCap]`. Establish `hNpos : 0 < N` using `by omega`.

Use `set a : ℤ := lxLamF hN l 0 - lxLamF hN l (Fin.last n) with ha`. Establish `ha0 : 0 ≤ a`. Establish `: lxLamF hN l (Fin.last n) ≤ lxLamF hN l 0` using `l.anti (by rw [Fin.le_def]; simp)`. Use linear arithmetic over natural numbers and integers. Establish `hsp : l.spread = a + N`.

Unfold `DomWeight.spread`. Rewrite using `[dif_pos hNpos, ha]`. Establish `e1 : lxLamF hN l 0 = l.w ⟨0, hNpos⟩` using `congrArg l.w (Fin.ext rfl)`. Establish `e2 : lxLamF hN l (Fin.last n) = l.w ⟨N - 1, by omega⟩` using `congrArg l.w (Fin.ext (by simp; omega))`. Rewrite using `[e1, e2]`.

Use `set e : ℕ := (Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w).toNat with he`. Establish `hcR : |((cBr hN l s : ℤ) : ℝ)| ≤ ((a + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * e)` using `by exact_mod_cast hc`. Establish `h1 : ((a + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * e) ≤ |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ^ (n * e)`. Rewrite using `[← abs_pow]`. Conclude with `le_abs_self _`.

Establish `h2 : |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ≤ ((2 * l.spread : ℤ) : ℝ)`. Rewrite using `[hsp, ← Int.cast_abs]`. Establish `: |a + (n : ℤ) - 1| ≤ 2 * (a + N)`. Apply the tactic sequence `rw [abs_le]; constructor <;> omega`. Conclude with `this` after adjusting the coercions.

Establish `h3 : (1 : ℝ) ≤ ((2 * l.spread : ℤ) : ℝ)`. Rewrite using `[hsp]`. Establish `: (1 : ℤ) ≤ 2 * (a + N)` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h4 : |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ^ (n * e) ≤ ((2 * l.spread : ℤ) : ℝ) ^ (n * e)` using `pow_le_pow_left₀ (abs_nonneg _) h2 _`.

Establish `h5 : ((2 * l.spread : ℤ) : ℝ) ^ (n * e) ≤ ((2 * l.spread : ℤ) : ℝ) ^ (N * e)` using `pow_le_pow_right₀ h3 (Nat.mul_le_mul_right _ (by omega))`. Establish `h6 : Formalism.MainNotions.PrimeDegreeVariant.cBd hN.symm l s = ((2 * l.spread : ℤ) : ℝ) ^ (N * e)`. Unfold `Formalism.MainNotions.PrimeDegreeVariant.cBd`. Rewrite using `[← normalized_first_difference_eq hN l s]`. Establish `: (((N : ℤ) * Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w : ℤ) : ℝ) = ((N * e : ℕ) : ℝ)`.

Establish `h7 : ((e : ℕ) : ℤ) = Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w` using `Int.toNat_of_nonneg hd1`. Rewrite using `[← h7]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Real.rpow_natCast]`.

Rewrite using `[h6]`. Conclude with `hcR.trans (h1.trans (h4.trans h5))`.
-/
theorem nm_c_le (hI : Br.Interlace hN l s) : |((cBr hN l s : ℤ) : ℝ)| ≤ Formalism.MainNotions.PrimeDegreeVariant.cBd hN.symm l s := by
  have hil := nm_il hN l s hI
  have hc := (Formalism.BranchingDeterminantCap.capacity_constant_bound n _ _ hil).2
  have hd1 : 0 ≤ Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w := (Formalism.BranchingDeterminantCap.interlaceIdent n _ _ hil).2.2.2.1
  rw [← cBr_eq_cCap] at hc
  have hNpos : 0 < N := by omega
  set a : ℤ := lxLamF hN l 0 - lxLamF hN l (Fin.last n) with ha
  have ha0 : 0 ≤ a := by
    have : lxLamF hN l (Fin.last n) ≤ lxLamF hN l 0 := l.anti (by rw [Fin.le_def]; simp)
    omega
  have hsp : l.spread = a + N := by
    unfold DomWeight.spread
    rw [dif_pos hNpos, ha]
    have e1 : lxLamF hN l 0 = l.w ⟨0, hNpos⟩ := congrArg l.w (Fin.ext rfl)
    have e2 : lxLamF hN l (Fin.last n) = l.w ⟨N - 1, by omega⟩ := congrArg l.w (Fin.ext (by simp; omega))
    rw [e1, e2]
  set e : ℕ := (Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w).toNat with he
  have hcR : |((cBr hN l s : ℤ) : ℝ)| ≤ ((a + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * e) := by exact_mod_cast hc
  have h1 : ((a + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * e) ≤ |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ^ (n * e) := by
    rw [← abs_pow]; exact le_abs_self _
  have h2 : |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ≤ ((2 * l.spread : ℤ) : ℝ) := by
    rw [hsp, ← Int.cast_abs]
    have : |a + (n : ℤ) - 1| ≤ 2 * (a + N) := by
      rw [abs_le]; constructor <;> omega
    exact_mod_cast this
  have h3 : (1 : ℝ) ≤ ((2 * l.spread : ℤ) : ℝ) := by
    rw [hsp]
    have : (1 : ℤ) ≤ 2 * (a + N) := by omega
    exact_mod_cast this
  have h4 : |((a + (n : ℤ) - 1 : ℤ) : ℝ)| ^ (n * e) ≤ ((2 * l.spread : ℤ) : ℝ) ^ (n * e) :=
    pow_le_pow_left₀ (abs_nonneg _) h2 _
  have h5 : ((2 * l.spread : ℤ) : ℝ) ^ (n * e) ≤ ((2 * l.spread : ℤ) : ℝ) ^ (N * e) :=
    pow_le_pow_right₀ h3 (Nat.mul_le_mul_right _ (by omega))
  have h6 : Formalism.MainNotions.PrimeDegreeVariant.cBd hN.symm l s = ((2 * l.spread : ℤ) : ℝ) ^ (N * e) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.cBd
    rw [← normalized_first_difference_eq hN l s]
    have : (((N : ℤ) * Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w : ℤ) : ℝ) = ((N * e : ℕ) : ℝ) := by
      have h7 : ((e : ℕ) : ℤ) = Formalism.BranchingDeterminantCap.d1 (lxLamF hN l) s.w := Int.toNat_of_nonneg hd1
      rw [← h7]; push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [h6]
  exact hcR.trans (h1.trans (h4.trans h5))

/- English proof (translation)
Unfold `Formalism.MainNotions.PrimeDegreeVariant.brBd`. Rewrite using `[mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Establish `h1 : ((cBr hN l s : ℤ) : ℝ) ^ 2 ≤ Formalism.MainNotions.PrimeDegreeVariant.cBd hN.symm l s ^ 2`. Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (nm_c_le hN l s hI) 2`.

Conclude with `mul_le_mul h1 hk (nm_kapR_pos hN l s hI hS).le (sq_nonneg _)`.
-/
theorem nm_bd_of (hI : Br.Interlace hN l s) (hS : SameShift l s)
    (hk : kapBr ℝ hN l s ≤ (Module.finrank ℂ (delSq ℂ N l) : ℝ)) :
    ((cBr hN l s : ℤ) : ℝ) ^ 2 * kapBr ℝ hN l s ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm l s ^ 2 := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h1 : ((cBr hN l s : ℤ) : ℝ) ^ 2 ≤ Formalism.MainNotions.PrimeDegreeVariant.cBd hN.symm l s ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (nm_c_le hN l s hI) 2
  exact mul_le_mul h1 hk (nm_kapR_pos hN l s hI hS).le (sq_nonneg _)

end NmE

end Formalism.L2.Ker

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL Formalism.BranchingDeterminantCap

section NmF

/- English proof (translation)
Unfold `fockF`. Rewrite using `[support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]`. Establish `hp` using `Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he`.

Unfold `Finsupp.prod at hp`. Rewrite using `[hp]`.
-/
theorem nm_fockF_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockF (rename e f) (rename e g) = fockF f g := by
  classical
  unfold fockF
  rw [support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  have hp := Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he
  unfold Finsupp.prod at hp
  rw [hp]

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

/- English proof (translation)
Unfold `DomWeight.natW`. Rewrite using `[lx_detShift_N hN l, sub_self]`. Both sides reduce to the same expression.
-/
theorem nm_natW_last : l.natW (iL hN) = 0 := by
  unfold DomWeight.natW
  rw [lx_detShift_N hN l, sub_self]; rfl

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]`.

Both sides reduce to the same expression.
-/
theorem nm_rename_lp (i : Fin n) :
    rename (lxRho hN) (lpMinor ℂ (r := n + 1) (n := n) (i.val + 1) (by have := i.2; omega) (by have := i.2; omega)) =
      lpMinor ℂ (r := N) (n := N) (i.val + 1) (by have := i.2; omega) (by have := i.2; omega) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

/- English proof (translation)
Unfold `nuNext`. Establish `hi` using `i.2`. Distinguish the cases in `h : i.val + 1 < n`. Rewrite using `[dif_pos h, dif_pos (by simp only [iC]; omega)]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg h, dif_pos (by simp only [iC]; omega)]`. Establish `: (⟨(iC hN i).val + 1, by simp only [iC]; omega⟩ : Fin N) = iL hN` using `Fin.ext (by simp only [iC, iL]; omega)`. Rewrite using `[this, nm_natW_last]`.
-/
theorem nm_nuNext (i : Fin n) : nuNext l.natW (iC hN i) = nuNext (lamN hN l) i := by
  unfold nuNext
  have hi := i.2
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, dif_pos (by simp only [iC]; omega)]
    rfl
  · rw [dif_neg h, dif_pos (by simp only [iC]; omega)]
    have : (⟨(iC hN i).val + 1, by simp only [iC]; omega⟩ : Fin N) = iL hN := Fin.ext (by simp only [iC, iL]; omega)
    rw [this, nm_natW_last]

/- English proof (translation)
Unfold `extremal hw`. Rewrite using `[map_prod]`. Establish `split : ∀ F : Fin N → MvPolynomial (Fin N × Fin N) ℂ, ∏ b, F b = (∏ b : Fin n, F (iC hN b)) * F (iL hN)`. Introduce `F`. Substitute `hN` using the available equality.

Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `only [iC_eq, iL_eq]`. Rewrite using `[split, nm_natW_last, Nat.zero_sub, pow_zero, mul_one]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, nm_rename_lp, nm_nuNext]`.

Both sides reduce to the same expression.
-/
theorem nm_rename_hw : rename (lxRho hN) (hw ℂ (Nat.le_succ n) (lamN hN l)) = extremal ℂ N l := by
  unfold extremal hw
  rw [map_prod]
  have split : ∀ F : Fin N → MvPolynomial (Fin N × Fin N) ℂ, ∏ b, F b = (∏ b : Fin n, F (iC hN b)) * F (iL hN) := by
    intro F
    subst hN
    rw [Fin.prod_univ_castSucc]
    simp only [iC_eq, iL_eq]
  rw [split, nm_natW_last, Nat.zero_sub, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, nm_rename_lp, nm_nuNext]
  rfl

/- English proof (translation)
Introduce `i`. Establish `h` using `lx_il hN l s hI hS i`. Rewrite using `[bmH_lamZ_castSucc, bmH_lamZ_succ]`. Conclude with `⟨by show ((s.natW i : ℕ) : ℤ) ≤ _; exact_mod_cast h.1, by show _ ≤ ((s.natW i : ℕ) : ℤ); exact_mod_cast h.2⟩`.
-/
theorem nm_ilZ (hI : Br.Interlace hN l s) (hS : SameShift l s) :
    Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN hN l)) (fun i => (s.natW i : ℤ)) := by
  intro i
  have h := lx_il hN l s hI hS i
  rw [bmH_lamZ_castSucc, bmH_lamZ_succ]
  exact ⟨by show ((s.natW i : ℕ) : ℤ) ≤ _; exact_mod_cast h.1, by show _ ≤ ((s.natW i : ℕ) : ℤ); exact_mod_cast h.2⟩

/- English proof (translation)
Establish `h` using `xi_norm_bound n (lamN hN l) s.natW (nm_ilZ hN l s hI hS)`. Rewrite `h` using `[← nm_fockF_rename (lxRho hN) (lxRho_inj hN) (xiB ℂ (lamN hN l) s.natW), lx_xi_rename hN l s hI hS, ← nm_fockF_rename (lxRho hN) (lxRho_inj hN) (hw ℂ (Nat.le_succ n) (lamN hN l)), nm_rename_hw]`. Rewrite using `[nm_kapR, div_le_iff₀ (fockPos _ _ (lm_extremal_ne l)).1]`. Conclude with `h`.
-/
theorem nm_kap_le_weyl (hI : Br.Interlace hN l s) (hS : SameShift l s) :
    kapBr ℝ hN l s ≤ weylProd (lamZ (lamN hN l)) := by
  have h := xi_norm_bound n (lamN hN l) s.natW (nm_ilZ hN l s hI hS)
  rw [← nm_fockF_rename (lxRho hN) (lxRho_inj hN) (xiB ℂ (lamN hN l) s.natW), lx_xi_rename hN l s hI hS,
    ← nm_fockF_rename (lxRho hN) (lxRho_inj hN) (hw ℂ (Nat.le_succ n) (lamN hN l)), nm_rename_hw] at h
  rw [nm_kapR, div_le_iff₀ (fockPos _ _ (lm_extremal_ne l)).1]
  exact h

/- English proof (translation)
Unfold `lamZ`. Distinguish the cases in `h : a.val < n`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h]`.

Establish `: Fin.cast hN.symm a = iL hN` using `Fin.ext (by have := a.2; simp only [iL, Fin.val_cast]; omega)`. Rewrite using `[this, nm_natW_last]`. Both sides reduce to the same expression.
-/
theorem nm_lamZ (a : Fin (n + 1)) : lamZ (lamN hN l) a = (l.natW (Fin.cast hN.symm a) : ℤ) := by
  unfold lamZ
  by_cases h : a.val < n
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    have : Fin.cast hN.symm a = iL hN := Fin.ext (by have := a.2; simp only [iL, Fin.val_cast]; omega)
    rw [this, nm_natW_last]; rfl

/- English proof (translation)
Substitute `hN` using the available equality. Rewrite using `[← nablaSq_eq_delSq]`. Unfold `nablaSq`. Rewrite using `[Formalism.L2.G.Model.finrank_dualWeyl]`. Establish `hanti : Antitone (fun t => ((l.natW t : ℕ) : ℤ))`.

Introduce `a b hab`. Use `show ((l.natW b : ℕ) : ℤ) ≤ ((l.natW a : ℕ) : ℤ)`. Conclude with `natW_antitone l hab` after adjusting the coercions. Establish `h` using `Formalism.L2.G.Model.weylQ (n + 1) _ hanti`. Rewrite using `[← Rat.cast_natCast, h]`.

Unfold `weylProd`. Rewrite using `[Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product, Rat.cast_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.cast_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [nm_lamZ rfl l]`. Use `split_ifs`. Use `push_cast`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem nm_weyl_finrank : weylProd (lamZ (lamN hN l)) = (Module.finrank ℂ (delSq ℂ N l) : ℝ) := by
  subst hN
  rw [← nablaSq_eq_delSq]
  unfold nablaSq
  rw [Formalism.L2.G.Model.finrank_dualWeyl]
  have hanti : Antitone (fun t => ((l.natW t : ℕ) : ℤ)) := by
    intro a b hab
    show ((l.natW b : ℕ) : ℤ) ≤ ((l.natW a : ℕ) : ℤ)
    exact_mod_cast natW_antitone l hab
  have h := Formalism.L2.G.Model.weylQ (n + 1) _ hanti
  rw [← Rat.cast_natCast, h]
  unfold weylProd
  rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product, Rat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Rat.cast_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [nm_lamZ rfl l]
  split_ifs
  · push_cast
    simp
  · simp

/- English proof (translation)
The claim follows from `(nm_kap_le_weyl hN l s hI hS).trans (nm_weyl_finrank hN l).le`.
-/
theorem nm_kap_le (hI : Br.Interlace hN l s) (hS : SameShift l s) :
    kapBr ℝ hN l s ≤ (Module.finrank ℂ (delSq ℂ N l) : ℝ) :=
  (nm_kap_le_weyl hN l s hI hS).trans (nm_weyl_finrank hN l).le

end NmF

section NmRec2

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
The claim follows from `nm_hB_of D u τ hI (nm_bd_of _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI) (nm_kap_le _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI)))`.
-/
theorem nm_hB (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ)) :
    ∀ f ∈ delSq ℂ _ (lamTr D u τ),
      (normFock (sgTr D u τ) (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
        (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤
        Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) ^ 2 * (normFock (lamTr D u τ) f f).re :=
  nm_hB_of D u τ hI (nm_bd_of _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI)
    (nm_kap_le _ _ _ ((interlace_iff _ _ (Nm_succ D.R)).1 hI) (sameShiftTr D u τ hI)))

end NmRec2

end Formalism.L2.Ker

namespace Formalism.L2.Ker

section Final

open Formalism.MainNotions.product_first_zeroth_parts

/- English proof (translation)
Use `⟨int_brOne hN l s hI hS, fun f _ => ?_, ⟨Formalism.L2.Col.Br.xiBr ℂ hN l s, ?_, brOne_xi_ne hN l s hI hS⟩, fun g f _ => brOne_sqAct hN l s hS g f, fun a f _ => brOne_last hN l s hI a f, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[← Formalism.L2.Col.nablaSq_eq_delSq]`. Conclude with `brOne_mem hN l s f`. Rewrite using `[← Formalism.L2.Col.nablaSq_eq_delSq]`. Conclude with `xiBr_mem hN l s hI hS`.

Rewrite `hf` using `[← Formalism.L2.Col.nablaSq_eq_delSq]`. Use `(nm_le hN l s hI hS f hf).trans (mul_le_mul_of_nonneg_right (nm_bd_of hN l s hI hS (nm_kap_le hN l s hI hS)) ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : f = 0`. Substitute `h0` using the available equality. Simplify using `[Formalism.BasicNotions.normFock, nm_fockF_zero_left]`.

Conclude with `(nm_normFock_pos _ f h0).le`.
-/
theorem brOne_isBr {N n : ℕ} (hN : N = n + 1) (l : Formalism.BasicNotions.DomWeight N) (s : Formalism.BasicNotions.DomWeight n)
    (hI : Formalism.L2.Col.Br.Interlace hN l s) (hS : Formalism.L2.Col.Br.SameShift l s) :
    Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm l s (brOne ℂ hN l s) := by
  refine ⟨int_brOne hN l s hI hS, fun f _ => ?_, ⟨Formalism.L2.Col.Br.xiBr ℂ hN l s, ?_, brOne_xi_ne hN l s hI hS⟩,
    fun g f _ => brOne_sqAct hN l s hS g f, fun a f _ => brOne_last hN l s hI a f, fun f hf => ?_⟩
  · rw [← Formalism.L2.Col.nablaSq_eq_delSq]; exact brOne_mem hN l s f
  · rw [← Formalism.L2.Col.nablaSq_eq_delSq]; exact xiBr_mem hN l s hI hS
  · rw [← Formalism.L2.Col.nablaSq_eq_delSq] at hf
    refine (nm_le hN l s hI hS f hf).trans (mul_le_mul_of_nonneg_right (nm_bd_of hN l s hI hS (nm_kap_le hN l s hI hS)) ?_)
    by_cases h0 : f = 0
    · subst h0; simp [Formalism.BasicNotions.normFock, nm_fockF_zero_left]
    · exact (nm_normFock_pos _ f h0).le

/- English proof (translation)
The claim follows from `brOne_isBr rfl weightTwoZeroZero wt10 (small3_interlace ()) (small3_sameShift ())`.
-/
theorem small3_isBr : Formalism.MainNotions.PrimeDegreeVariant.IsBr (rfl : 2 + 1 = 3) weightTwoZeroZero wt10 (brOne ℂ (rfl : 3 = 2 + 1) weightTwoZeroZero wt10) :=
  brOne_isBr rfl weightTwoZeroZero wt10 (small3_interlace ()) (small3_sameShift ())

/- English proof (translation)
Unfold `beOnVal`. Rewrite using `[small3_cBr]`. Use `nm_kapR_pos (rfl : 3 = 2 + 1) weightTwoZeroZero wt10 (small3_interlace ()) (small3_sameShift ())` as an intermediate fact. Establish `h2` using `Real.sqrt_pos.mpr this`. Simplify using `using h2`.
-/
theorem small3_norm_pos : 0 < beOnVal (rfl : 3 = 2 + 1) weightTwoZeroZero wt10 := by
  unfold beOnVal
  rw [small3_cBr]
  have := nm_kapR_pos (rfl : 3 = 2 + 1) weightTwoZeroZero wt10 (small3_interlace ()) (small3_sameShift ())
  have h2 := Real.sqrt_pos.mpr this
  simpa using h2

/- English proof (translation)
The claim follows from `brOneIsBr_of D u (fun τ hI => int_member D u τ hI) (fun τ hI => nm_hB D u τ hI)`.
-/
theorem brOneIsBr (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : BrOneIsBr D u :=
  brOneIsBr_of D u (fun τ hI => int_member D u τ hI) (fun τ hI => nm_hB D u τ hI)

/- English proof (translation)
The claim follows from `nm_beOnEq D u`.
-/
theorem beOnEq (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : BeOnEq D u := nm_beOnEq D u

/- English proof (translation)
Take `⟨P, hP⟩` from `h`. Use `⟨P, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[hP τ]`. Conclude with `brOneIsBr D u τ (interlaceTr D u P.interlace τ)`.
-/
theorem lowerTie_isBr {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (h : LowerTie D u) : ∃ P : Pend D u, ArchimedeanSignatureMatching P := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun τ => ?_⟩
  rw [hP τ]
  exact brOneIsBr D u τ (interlaceTr D u P.interlace τ)

/- English proof (translation)
Establish `h1` using `lowerTie_beOn h τ`. Take `⟨P, -⟩` from `h`. Rewrite using `[h1]`. Conclude with `beOnEq D u τ (interlaceTr D u P.interlace τ)`.
-/
theorem lowerTie_beOnVal {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (h : LowerTie D u) (τ : D.what₂.Tau) :
    (D.fm u).beOn τ = beOnVal (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
  have h1 := lowerTie_beOn h τ
  obtain ⟨P, -⟩ := h
  rw [h1]
  exact beOnEq D u τ (interlaceTr D u P.interlace τ)

/- English proof (translation)
Rewrite using `[lowerTie_eval P hP w φ hφ c, blk_brOne]`.
-/
theorem lowerTie_brStdP {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (P : Pend D u)
    (hP : ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (w : D.what₂.places.Pl)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    P.coP w ((D.mem u).P.lowerMap ((D.mem u).P.evz φ)) c =
      (Formalism.L2.Col.Br.brStdP (Nm_succ D.R).symm (lamTr D u) (sgTr D u) (P.coM w c (φ ((D.fm u).til c))) :
        Formalism.L2.DIV.Pol ℂ D.what₂.Tau (D.R.N D.R.m - 1)) := by
  rw [lowerTie_eval P hP w φ hφ c, blk_brOne]

end Final

end Formalism.L2.Ker

namespace Formalism.L2.Ker

section At

open Formalism.MainNotions.product_first_zeroth_parts

section BlkCalc

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Use `(MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).constr_basis ℂ (fun mon => Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => F τ (MvPolynomial.monomial (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1)) mon` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coe_basisMonomials]`. Conclude with `this`.
-/
theorem ta_blk_monomial {n n' : ℕ} (F : ι → MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n' × Fin n') ℂ)
    (mon : ι × Fin n × Fin n →₀ ℕ) :
    blk F (MvPolynomial.monomial mon 1) = Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => F τ (MvPolynomial.monomial
      (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1) := by
  have := (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).constr_basis ℂ
    (fun mon => Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => F τ (MvPolynomial.monomial
      (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1)) mon
  rw [MvPolynomial.coe_basisMonomials] at this
  exact this

/- English proof (translation)
Use extensionality with `⟨τ, x⟩`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single τ]`. Rewrite using `[Finsupp.mapDomain_apply (Prod.mk_right_injective τ), Finsupp.comapDomain_apply]`. Introduce `σ _ hσ`. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises.

Introduce and unpack `⟨y, hy⟩`. Conclude with `hσ (congrArg Prod.fst hy)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ τ) h`.
-/
theorem ta_sum_map_comap {α : Type} (mon : ι × α →₀ ℕ) :
    ∑ σ, (mon.comapDomain (Prod.mk σ) (Prod.mk_right_injective σ).injOn).mapDomain (Prod.mk σ) = mon := by
  ext ⟨τ, x⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · rw [Finsupp.mapDomain_apply (Prod.mk_right_injective τ), Finsupp.comapDomain_apply]
  · intro σ _ hσ
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h; exact absurd (Finset.mem_univ τ) h

/- English proof (translation)
Establish `h : blk (fun _ : ι => (id : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ)) = LinearMap.id`. Apply `(MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext` to reduce the goal to its premises. Introduce `mon`. Rewrite using `[MvPolynomial.coe_basisMonomials, ta_blk_monomial]`. Simplify using `only [id, LinearMap.id_apply]`.

Rewrite using `[ten_monomial, ta_sum_map_comap]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem ta_blk_id {n : ℕ} (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blk (fun _ : ι => (id : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ)) p = p := by
  have h : blk (fun _ : ι => (id : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ)) = LinearMap.id := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [MvPolynomial.coe_basisMonomials, ta_blk_monomial]
    simp only [id, LinearMap.id_apply]
    rw [ten_monomial, ta_sum_map_comap]
  rw [h]; rfl

/- English proof (translation)
Establish `h : blk (fun τ => ⇑(G τ)) ∘ₗ blk (fun τ => ⇑(F τ)) = blk (fun τ => ⇑(G τ ∘ₗ F τ))`. Apply `(MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext` to reduce the goal to its premises. Introduce `mon`. Rewrite using `[MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, ta_blk_monomial, ta_blk_monomial, blk_ten]`. Both sides reduce to the same expression.

Conclude with `LinearMap.congr_fun h p`.
-/
theorem ta_blk_comp {n n' n'' : ℕ} (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (G : ι → MvPolynomial (Fin n' × Fin n') ℂ →ₗ[ℂ] MvPolynomial (Fin n'' × Fin n'') ℂ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blk (fun τ => ⇑(G τ)) (blk (fun τ => ⇑(F τ)) p) = blk (fun τ => ⇑(G τ ∘ₗ F τ)) p := by
  have h : blk (fun τ => ⇑(G τ)) ∘ₗ blk (fun τ => ⇑(F τ)) = blk (fun τ => ⇑(G τ ∘ₗ F τ)) := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, ta_blk_monomial, ta_blk_monomial, blk_ten]
    rfl
  exact LinearMap.congr_fun h p

def ta_sqActL {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  Formalism.BasicNotions.detPow ℂ n g l.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ta_sqActL_coe {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) ℂ) : ⇑(ta_sqActL l g) = Formalism.BasicNotions.sqAct ℂ n l g := rfl

/- English proof (translation)
Unfold `Formalism.BasicNotions.sqAct`. Rewrite using `[map_smul, smul_smul, Formalism.L2.DIV.rd_rowAct_rowAct, ← Matrix.transpose_mul]`. Establish `e1 : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `e2 : Formalism.BasicNotions.detPow ℂ n g⁻¹ l.detShift * Formalism.BasicNotions.detPow ℂ n g l.detShift = 1`.

Unfold `Formalism.BasicNotions.detPow`. Rewrite using `[← Units.val_mul, ← mul_zpow, ← map_mul, inv_mul_cancel, map_one, one_zpow, Units.val_one]`. Rewrite using `[e1, e2, Matrix.transpose_one, Formalism.L2.DIV.rd_rowAct_one, one_smul]`.
-/
theorem ta_sqAct_inv {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.BasicNotions.sqAct ℂ n l g⁻¹ (Formalism.BasicNotions.sqAct ℂ n l g f) = f := by
  unfold Formalism.BasicNotions.sqAct
  rw [map_smul, smul_smul, Formalism.L2.DIV.rd_rowAct_rowAct, ← Matrix.transpose_mul]
  have e1 : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 : Formalism.BasicNotions.detPow ℂ n g⁻¹ l.detShift * Formalism.BasicNotions.detPow ℂ n g l.detShift = 1 := by
    unfold Formalism.BasicNotions.detPow
    rw [← Units.val_mul, ← mul_zpow, ← map_mul, inv_mul_cancel, map_one, one_zpow, Units.val_one]
  rw [e1, e2, Matrix.transpose_one, Formalism.L2.DIV.rd_rowAct_one, one_smul]

/- English proof (translation)
Establish `h1` using `ta_blk_comp (fun τ => ta_sqActL (l τ) (g τ)) (fun τ => ta_sqActL (l τ) (g τ)⁻¹) x`. Establish `h2 : (fun τ => ⇑(ta_sqActL (l τ) (g τ)⁻¹ ∘ₗ ta_sqActL (l τ) (g τ))) = fun _ : ι => (id : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ)`. Use function extensionality and compare the values at `τ f`. Conclude with `ta_sqAct_inv (l τ) (g τ) f`. Rewrite `h1` using `[h2, ta_blk_id]`.

Simplify using `only [ta_sqActL_coe] at h1`. Rewrite `h1` using `[h, map_zero]`. Conclude with `h1.symm`.
-/
theorem ta_blk_sqAct_inj {n : ℕ} (l : ι → Formalism.BasicNotions.DomWeight n) (g : ι → GL (Fin n) ℂ) (x : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : blk (fun τ => Formalism.BasicNotions.sqAct ℂ n (l τ) (g τ)) x = 0) : x = 0 := by
  have h1 := ta_blk_comp (fun τ => ta_sqActL (l τ) (g τ)) (fun τ => ta_sqActL (l τ) (g τ)⁻¹) x
  have h2 : (fun τ => ⇑(ta_sqActL (l τ) (g τ)⁻¹ ∘ₗ ta_sqActL (l τ) (g τ))) =
      fun _ : ι => (id : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ) := by
    funext τ f
    exact ta_sqAct_inv (l τ) (g τ) f
  rw [h2, ta_blk_id] at h1
  simp only [ta_sqActL_coe] at h1
  rw [h, map_zero] at h1
  exact h1.symm

/- English proof (translation)
Unfold `nfAll`. Establish `e : ∏ τ, Formalism.REAL.fockF (Formalism.BasicNotions.extremal ℂ n (l τ)) (Formalism.BasicNotions.extremal ℂ n (l τ)) = ((∏ τ, (Formalism.REAL.fockF (Formalism.BasicNotions.extremal ℂ n (l τ)) (Formalism.BasicNotions.extremal ℂ n (l τ))).re : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_prod]`. Conclude with `Finset.prod_congr rfl fun τ _ => nm_fockF_self _`. Rewrite using `[nm_fockF_self x, e, ← Complex.ofReal_div, Complex.ofReal_re]`.

Conclude with `div_pos (Formalism.GradedWeylDivisibility.fockPos _ x hx).1 (Finset.prod_pos fun τ _ => (Formalism.GradedWeylDivisibility.fockPos _ _ (lm_extremal_ne (l τ))).1)`.
-/
theorem ta_nfAll_pos {n : ℕ} (l : ι → Formalism.BasicNotions.DomWeight n) (x : MvPolynomial (ι × Fin n × Fin n) ℂ) (hx : x ≠ 0) :
    0 < (nfAll l x x).re := by
  unfold nfAll
  have e : ∏ τ, Formalism.REAL.fockF (Formalism.BasicNotions.extremal ℂ n (l τ)) (Formalism.BasicNotions.extremal ℂ n (l τ)) =
      ((∏ τ, (Formalism.REAL.fockF (Formalism.BasicNotions.extremal ℂ n (l τ)) (Formalism.BasicNotions.extremal ℂ n (l τ))).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => nm_fockF_self _
  rw [nm_fockF_self x, e, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_pos (Formalism.GradedWeylDivisibility.fockPos _ x hx).1 (Finset.prod_pos fun τ _ => (Formalism.GradedWeylDivisibility.fockPos _ _ (lm_extremal_ne (l τ))).1)

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[nfAll, nm_fockF_zero_left]`. Conclude with `(ta_nfAll_pos l x hx).le`.
-/
theorem ta_nfAll_nonneg {n : ℕ} (l : ι → Formalism.BasicNotions.DomWeight n) (x : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    0 ≤ (nfAll l x x).re := by
  by_cases hx : x = 0
  · subst hx; simp [nfAll, nm_fockF_zero_left]
  · exact (ta_nfAll_pos l x hx).le

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.ten`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `τ _`. Conclude with `(map_ne_zero_iff _ (MvPolynomial.rename_injective _ (Prod.mk_right_injective τ))).2 (hf τ)`.
-/
theorem ta_ten_ne {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (hf : ∀ τ, f τ ≠ 0) : Formalism.MainNotions.product_first_zeroth_parts.ten f ≠ 0 := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  exact (map_ne_zero_iff _ (MvPolynomial.rename_injective _ (Prod.mk_right_injective τ))).2 (hf τ)

end BlkCalc

section TieAt

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}
  {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
  {gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ}

/- English proof (translation)
Take `⟨-, P, -, -, hP⟩` from `h`. Conclude with `⟨P, hP⟩`.
-/
theorem lowerTieAt_weak (h : LowerTieAt D u coM gP) : LowerTie D u := by
  obtain ⟨-, P, -, -, hP⟩ := h
  exact ⟨P, hP⟩

/- English proof (translation)
The claim follows from `h.1 φ hφ`.
-/
theorem lowerTieAt_mem (h : LowerTieAt D u coM gP) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    (D.mem u).P.lowerMap ((D.mem u).P.evz φ) ∈ (D.fm u).ptC := h.1 φ hφ

/- English proof (translation)
Use `choose f hf hne using fun τ => (brOneIsBr D u τ (interlaceTr D u hI τ)).2.2.1`. Use `⟨Formalism.MainNotions.product_first_zeroth_parts.ten f, Submodule.subset_span ⟨f, fun τ => ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `hf τ` as an intermediate fact. Rewrite `this` using `[lamTr, delSq_wSh]`. Then use the resulting hypothesis. Unfold `brTen`.

Rewrite using `[blk_ten]`. Conclude with `ta_ten_ne _ hne`.
-/
theorem brTen_ne (hI : (D.fm u).SgInterlace) : ∃ p ∈ CSpan ((D.fm u).lam D.R.m), brTen D u p ≠ 0 := by
  choose f hf hne using fun τ => (brOneIsBr D u τ (interlaceTr D u hI τ)).2.2.1
  refine ⟨Formalism.MainNotions.product_first_zeroth_parts.ten f, Submodule.subset_span ⟨f, fun τ => ?_, rfl⟩, ?_⟩
  · have := hf τ
    rwa [lamTr, delSq_wSh] at this
  · unfold brTen
    rw [blk_ten]
    exact ta_ten_ne _ hne

/- English proof (translation)
Take `⟨p, hp, hne⟩` from `brTen_ne (D := D) (u := u) hI`. Take `⟨φ, hφ, e⟩` from `hF p hp`. Conclude with `⟨φ, hφ, by rw [e]; exact hne⟩`.
-/
theorem seenAt_of_fullAt (hI : (D.fm u).SgInterlace) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hF : FullAt D u coM w c) :
    SeenAt D u coM w c := by
  obtain ⟨p, hp, hne⟩ := brTen_ne (D := D) (u := u) hI
  obtain ⟨φ, hφ, e⟩ := hF p hp
  exact ⟨φ, hφ, by rw [e]; exact hne⟩

/- English proof (translation)
Take `⟨hz, P, rfl, rfl, hP⟩` from `h`. Rewrite using `[P.re_petersson_self_eq_sum_coord w _ (hz φ hφ)]`. Unfold `lowerNormAt brTen`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[P.Pt_eq w φ hφ c]`.

Simplify using `only [hP]`.
-/
theorem lowerTieAt_norm (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = lowerNormAt D u coM gP w φ := by
  obtain ⟨hz, P, rfl, rfl, hP⟩ := h
  rw [P.re_petersson_self_eq_sum_coord w _ (hz φ hφ)]
  unfold lowerNormAt brTen
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [P.Pt_eq w φ hφ c]
  simp only [hP]

/- English proof (translation)
Take `⟨hz, P, rfl, rfl, hP⟩` from `h`. Establish `e : ∀ c, P.coP w (Pt D u φ) c = brTen D u (P.coM w c (φ ((D.fm u).til c)))`. Introduce `c`. Rewrite using `[P.Pt_eq w φ hφ c]`. Unfold `brTen`.

Simplify using `only [hP]`. Prove the components needed by the constructor for the conclusion. Introduce `h0 c`. Rewrite using `[← e c, h0, map_zero]`. Both sides reduce to the same expression.

Introduce `h0`. Conclude with `P.coP_inj w _ (hz φ hφ) (funext fun c => by rw [e c, h0 c]; rfl)`.
-/
theorem lowerTieAt_zero_iff (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    Pt D u φ = 0 ↔ ∀ c, brTen D u (coM w c (φ ((D.fm u).til c))) = 0 := by
  obtain ⟨hz, P, rfl, rfl, hP⟩ := h
  have e : ∀ c, P.coP w (Pt D u φ) c = brTen D u (P.coM w c (φ ((D.fm u).til c))) := by
    intro c
    rw [P.Pt_eq w φ hφ c]
    unfold brTen
    simp only [hP]
  constructor
  · intro h0 c
    rw [← e c, h0, map_zero]; rfl
  · intro h0
    exact P.coP_inj w _ (hz φ hφ) (funext fun c => by rw [e c, h0 c]; rfl)

/- English proof (translation)
Take `⟨hz, P, rfl, rfl, hP⟩` from `h`. Rewrite using `[P.pt_co w _ (hz φ hφ)]`. Use `forall_congr' fun c => ?_` and prove the remaining obligations. Rewrite using `[P.Pt_eq w φ hφ c]`. Unfold `brTen`.

Simplify using `only [hP]`.
-/
theorem lowerTieAt_int (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = Pt D u φ) ↔
      ∀ c, brTen D u (coM w c (φ ((D.fm u).til c))) ∈ IntSpan D w (D.fm u).sg := by
  obtain ⟨hz, P, rfl, rfl, hP⟩ := h
  rw [P.pt_co w _ (hz φ hφ)]
  refine forall_congr' fun c => ?_
  rw [P.Pt_eq w φ hφ c]
  unfold brTen
  simp only [hP]

/- English proof (translation)
Unfold `lowerNormAt`. Establish `hc : ∀ c', 0 < ((Nat.card ((D.fm u).stabilizer₂ c') : ℝ))⁻¹` using `fun c' => inv_pos.2 (by exact_mod_cast Nat.card_pos)`. Use `Finset.sum_pos' (fun c' _ => mul_nonneg (hc c').le (ta_nfAll_nonneg _ _)) ⟨c, Finset.mem_univ c, mul_pos (hc c) ?_⟩` and prove the remaining obligations. Conclude with `ta_nfAll_pos _ _ fun h0 => hne (ta_blk_sqAct_inj _ _ _ h0)`.
-/
theorem lowerNormAt_pos (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (φ : Fn D u D.R.m)
    (hne : brTen D u (coM w c (φ ((D.fm u).til c))) ≠ 0) : 0 < lowerNormAt D u coM gP w φ := by
  unfold lowerNormAt
  have hc : ∀ c', 0 < ((Nat.card ((D.fm u).stabilizer₂ c') : ℝ))⁻¹ := fun c' => inv_pos.2 (by exact_mod_cast Nat.card_pos)
  refine Finset.sum_pos' (fun c' _ => mul_nonneg (hc c').le (ta_nfAll_nonneg _ _)) ⟨c, Finset.mem_univ c, mul_pos (hc c) ?_⟩
  exact ta_nfAll_pos _ _ fun h0 => hne (ta_blk_sqAct_inj _ _ _ h0)

/- English proof (translation)
Take `⟨φ, hφ, hne⟩` from `hS`. Conclude with `⟨φ, hφ, by rw [lowerTieAt_norm h w φ hφ]; exact lowerNormAt_pos w c φ hne⟩`.
-/
theorem lowerTieAt_pos (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hS : SeenAt D u coM w c) :
    ∃ φ ∈ (D.fm u).Fi D.R.m, 0 < ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re := by
  obtain ⟨φ, hφ, hne⟩ := hS
  exact ⟨φ, hφ, by rw [lowerTieAt_norm h w φ hφ]; exact lowerNormAt_pos w c φ hne⟩

/- English proof (translation)
Take `⟨φ, hφ, hpos⟩` from `lowerTieAt_pos h w c hS`. Take `⟨hz, P, hPM, hPg, hP⟩` from `h`. Conclude with `pend_rigid P P' a (hM.trans hPM.symm) (hg.trans hPg.symm) (fun τ => by rw [hb τ, hP τ]) w φ hφ (hz φ hφ) hpos.ne'`.
-/
theorem lowerTieAt_rigid_seen (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hS : SeenAt D u coM w c)
    (P' : Pend D u) (a : D.what₂.Tau → ℂ) (hM : P'.coM = coM) (hg : P'.gP = gP)
    (hb : ∀ τ, P'.br τ = a τ • brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) : ‖∏ τ, a τ‖ = 1 := by
  obtain ⟨φ, hφ, hpos⟩ := lowerTieAt_pos h w c hS
  obtain ⟨hz, P, hPM, hPg, hP⟩ := h
  exact pend_rigid P P' a (hM.trans hPM.symm) (hg.trans hPg.symm) (fun τ => by rw [hb τ, hP τ]) w φ hφ (hz φ hφ) hpos.ne'

/- English proof (translation)
The claim follows from `lowerTieAt_rigid_seen h w c (seenAt_of_fullAt P'.interlace w c hF) P' a hM hg hb`.
-/
theorem lowerTieAt_rigid (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hF : FullAt D u coM w c)
    (P' : Pend D u) (a : D.what₂.Tau → ℂ) (hM : P'.coM = coM) (hg : P'.gP = gP)
    (hb : ∀ τ, P'.br τ = a τ • brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) : ‖∏ τ, a τ‖ = 1 :=
  lowerTieAt_rigid_seen h w c (seenAt_of_fullAt P'.interlace w c hF) P' a hM hg hb

/- English proof (translation)
Rewrite using `[lowerTieAt_norm h w φ hφ, h3 z hz]`. Simplify using `only [h1]`. Both sides reduce to the same expression.
-/
theorem lowerTieAt_other (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m)
    (coP' : (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (h3 : ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (nfAll (D.fm u).sg (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))
        (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))).re)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (h1 : ∀ c, coP' z c = brTen D u (coM w c (φ ((D.fm u).til c)))) :
    ((D.fm u).ipP z z).re = ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re := by
  rw [lowerTieAt_norm h w φ hφ, h3 z hz]
  simp only [h1]
  rfl

/- English proof (translation)
Take `⟨φ, hφ, hpos⟩` from `lowerTieAt_pos h w c hS`. Establish `h4` using `lowerTieAt_other h w φ hφ coP' h3 (t • Pt D u φ) ((D.fm u).ptC.smul_mem t (h.1 φ hφ)) (h1 φ hφ)`. Rewrite `h4` using `[((D.fm u).ipP (t • Pt D u φ)).map_smul t (Pt D u φ), (D.fm u).ipP.map_smulₛₗ t (Pt D u φ), LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]`. Establish `h5 : ‖t‖ ^ 2 = 1`. Establish `: (‖t‖ ^ 2 - 1) * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = 0` using `by linarith`.

Break down `mul_eq_zero.mp this with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h hpos.ne'`. Establish `h6 : 0 ≤ ‖t‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lowerTieAt_scalar (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hS : SeenAt D u coM w c) (t : ℂ)
    (coP' : (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (h1 : ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, coP' (t • Pt D u φ) c = brTen D u (coM w c (φ ((D.fm u).til c))))
    (h3 : ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (nfAll (D.fm u).sg (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))
        (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))).re) : ‖t‖ = 1 := by
  obtain ⟨φ, hφ, hpos⟩ := lowerTieAt_pos h w c hS
  have h4 := lowerTieAt_other h w φ hφ coP' h3 (t • Pt D u φ) ((D.fm u).ptC.smul_mem t (h.1 φ hφ)) (h1 φ hφ)
  rw [((D.fm u).ipP (t • Pt D u φ)).map_smul t (Pt D u φ), (D.fm u).ipP.map_smulₛₗ t (Pt D u φ), LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul] at h4
  have h5 : ‖t‖ ^ 2 = 1 := by
    have : (‖t‖ ^ 2 - 1) * ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'
  have h6 : 0 ≤ ‖t‖ := norm_nonneg _
  nlinarith

/- English proof (translation)
Take `⟨-, P, rfl, rfl, hP⟩` from `h`. Use `⟨P.coP w, fun φ hφ c => ?_, P.re_petersson_self_eq_sum_coord w⟩` and prove the remaining obligations. Rewrite using `[one_smul, P.Pt_eq w φ hφ c]`. Unfold `brTen`. Simplify using `only [hP]`.
-/
theorem lowerTieAt_scalar_one (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) :
    ∃ coP' : (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
      (∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, coP' ((1 : ℂ) • Pt D u φ) c = brTen D u (coM w c (φ ((D.fm u).til c)))) ∧
      ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
        (nfAll (D.fm u).sg (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))
          (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))).re := by
  obtain ⟨-, P, rfl, rfl, hP⟩ := h
  refine ⟨P.coP w, fun φ hφ c => ?_, P.re_petersson_self_eq_sum_coord w⟩
  rw [one_smul, P.Pt_eq w φ hφ c]
  unfold brTen
  simp only [hP]

/- English proof (translation)
Take `⟨hz, P, -, -, hP⟩` from `h`. Establish `h4 : ArchimedeanSignatureMatching P` using `fun τ => by rw [hP τ]; exact brOneIsBr D u τ (interlaceTr D u P.interlace τ)`. Conclude with `⟨PRat_of P h4 hz, Pt_integral P h4 hz _⟩`.
-/
theorem lowerTieAt_integral (h : LowerTieAt D u coM gP) : ∃ hr : (D.fm u).PRat, (D.fm u).PtilIntegral hr := by
  obtain ⟨hz, P, -, -, hP⟩ := h
  have h4 : ArchimedeanSignatureMatching P := fun τ => by rw [hP τ]; exact brOneIsBr D u τ (interlaceTr D u P.interlace τ)
  exact ⟨PRat_of P h4 hz, Pt_integral P h4 hz _⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, φ, hφ, hne⟩`. Conclude with `⟨φ, hφ, fun h0 => hne ((lowerTieAt_zero_iff h w φ hφ).1 h0 c)⟩`. Introduce and unpack `⟨φ, hφ, hne⟩`. Assume the negation of the conclusion as `H`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[lowerTieAt_zero_iff h w φ hφ]`. Introduce `c`. Assume the negation of the conclusion as `H2`. Conclude with `H ⟨c, φ, hφ, H2⟩`.
-/
theorem seenAt_iff (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) :
    (∃ c, SeenAt D u coM w c) ↔ ∃ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ≠ 0 := by
  constructor
  · rintro ⟨c, φ, hφ, hne⟩
    exact ⟨φ, hφ, fun h0 => hne ((lowerTieAt_zero_iff h w φ hφ).1 h0 c)⟩
  · rintro ⟨φ, hφ, hne⟩
    by_contra H
    apply hne
    rw [lowerTieAt_zero_iff h w φ hφ]
    intro c
    by_contra H2
    exact H ⟨c, φ, hφ, H2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, _, h⟩ => ⟨lowerTieAt_weak h, h.1⟩, fun ⟨⟨P, hP⟩, hz⟩ => ⟨P.coM, P.gP, hz, P, rfl, rfl, hP⟩⟩`.
-/
theorem lowerTieAt_ex_iff : (∃ coM gP, LowerTieAt D u coM gP) ↔ (LowerTie D u ∧ ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC) :=
  ⟨fun ⟨_, _, h⟩ => ⟨lowerTieAt_weak h, h.1⟩, fun ⟨⟨P, hP⟩, hz⟩ => ⟨P.coM, P.gP, hz, P, rfl, rfl, hP⟩⟩

/- English proof (translation)
Take `⟨P, -⟩` from `h.2`. Conclude with `lowerTieAt_pos h w c (seenAt_of_fullAt P.interlace w c hF)`.
-/
theorem lowerTieAt_pos_full (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hF : FullAt D u coM w c) :
    ∃ φ ∈ (D.fm u).Fi D.R.m, 0 < ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re := by
  obtain ⟨P, -⟩ := h.2
  exact lowerTieAt_pos h w c (seenAt_of_fullAt P.interlace w c hF)

/- English proof (translation)
Take `⟨P, -⟩` from `h.2`. Conclude with `lowerTieAt_scalar h w c (seenAt_of_fullAt P.interlace w c hF) t coP' h1 h3`.
-/
theorem lowerTieAt_scalar_full (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (hF : FullAt D u coM w c) (t : ℂ)
    (coP' : (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (h1 : ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, coP' (t • Pt D u φ) c = brTen D u (coM w c (φ ((D.fm u).til c))))
    (h3 : ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (nfAll (D.fm u).sg (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))
        (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))).re) : ‖t‖ = 1 := by
  obtain ⟨P, -⟩ := h.2
  exact lowerTieAt_scalar h w c (seenAt_of_fullAt P.interlace w c hF) t coP' h1 h3

/- English proof (translation)
Unfold `opNorm`. Rewrite using `[← smul_eq_mul, ← Real.sSup_smul_of_nonneg (norm_nonneg a)]`. Use `congr 1`. Rewrite using `[← Set.image_smul, Set.image_image]`. Use `Set.image_congr fun f _ => ?_` and prove the remaining obligations.

Establish `hn : (a * star a) = ((‖a‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [LinearMap.smul_apply, Formalism.BasicNotions.normFock, fockF_smul_smul, hn, smul_eq_mul]`. Rewrite using `[mul_div_assoc, Complex.re_ofReal_mul, mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem ta_opNorm_smul (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (a : ℂ)
    (b : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ] MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) :
    opNorm D u τ (a • b) = ‖a‖ * opNorm D u τ b := by
  unfold opNorm
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg (norm_nonneg a)]
  congr 1
  rw [← Set.image_smul, Set.image_image]
  refine Set.image_congr fun f _ => ?_
  have hn : (a * star a) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [LinearMap.smul_apply, Formalism.BasicNotions.normFock, fockF_smul_smul, hn, smul_eq_mul]
  rw [mul_div_assoc, Complex.re_ofReal_mul, mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Establish `h1` using `P.beOn_eq τ`. Establish `h2` using `P'.beOn_eq τ`. Rewrite `h2` using `[hb τ, ta_opNorm_smul, ← h1]`. Establish `h3 : (‖a τ‖ - 1) * (D.fm u).beOn τ = 0` using `by linarith`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h h0`.
-/
theorem pend_rigid_br (P P' : Pend D u) (a : D.what₂.Tau → ℂ) (hb : ∀ τ, P'.br τ = a τ • P.br τ)
    (τ : D.what₂.Tau) (h0 : (D.fm u).beOn τ ≠ 0) : ‖a τ‖ = 1 := by
  have h1 := P.beOn_eq τ
  have h2 := P'.beOn_eq τ
  rw [hb τ, ta_opNorm_smul, ← h1] at h2
  have h3 : (‖a τ‖ - 1) * (D.fm u).beOn τ = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact absurd h h0

/- English proof (translation)
Establish `hI` using `interlaceTr D u P'.interlace τ`. Establish `hI'` using `(interlace_iff _ _ (Nm_succ D.R)).1 hI`. Establish `hS` using `sameShiftTr D u τ hI`. Establish `hb0 : (D.fm u).beOn τ ≠ 0`. Rewrite using `[lowerTie_beOnVal h τ]`.

Unfold `beOnVal`. Use `mul_ne_zero (abs_ne_zero.2 ?_) (Real.sqrt_pos.2 (nm_kapR_pos _ _ _ hI' hS)).ne'` and prove the remaining obligations. Conclude with `cBr_ne_zero _ _ _ hI'` after adjusting the coercions. Establish `h1` using `lowerTie_beOn h τ`. Establish `h2` using `P'.beOn_eq τ`.

Rewrite `h2` using `[hb τ, ta_opNorm_smul, ← h1]`. Establish `h3 : (‖a τ‖ - 1) * (D.fm u).beOn τ = 0` using `by linarith`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h hb0`.
-/
theorem lowerTie_rigid_br (h : LowerTie D u) (P' : Pend D u) (a : D.what₂.Tau → ℂ)
    (hb : ∀ τ, P'.br τ = a τ • brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (τ : D.what₂.Tau) : ‖a τ‖ = 1 := by
  have hI := interlaceTr D u P'.interlace τ
  have hI' := (interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := sameShiftTr D u τ hI
  have hb0 : (D.fm u).beOn τ ≠ 0 := by
    rw [lowerTie_beOnVal h τ]
    unfold beOnVal
    refine mul_ne_zero (abs_ne_zero.2 ?_) (Real.sqrt_pos.2 (nm_kapR_pos _ _ _ hI' hS)).ne'
    exact_mod_cast cBr_ne_zero _ _ _ hI'
  have h1 := lowerTie_beOn h τ
  have h2 := P'.beOn_eq τ
  rw [hb τ, ta_opNorm_smul, ← h1] at h2
  have h3 : (‖a τ‖ - 1) * (D.fm u).beOn τ = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact absurd h hb0

/- English proof (translation)
Establish `h0 : P.coP w (z - Pt D u φ) = 0`. Use function extensionality and compare the values at `c`. Rewrite using `[map_sub, Pi.sub_apply, h1 c, P.Pt_eq w φ hφ c, sub_self]`. Both sides reduce to the same expression. Conclude with `sub_eq_zero.1 (P.coP_inj w _ ((D.fm u).ptC.sub_mem hz' hz) h0)`.
-/
theorem pend_unique (P : Pend D u) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (hz : Pt D u φ ∈ (D.fm u).ptC)
    (z : (D.mem u).P.Wrow) (hz' : z ∈ (D.fm u).ptC)
    (h1 : ∀ c, P.coP w z c = blk (fun τ => P.br τ) (P.coM w c (φ ((D.fm u).til c)))) : z = Pt D u φ := by
  have h0 : P.coP w (z - Pt D u φ) = 0 := by
    funext c
    rw [map_sub, Pi.sub_apply, h1 c, P.Pt_eq w φ hφ c, sub_self]; rfl
  exact sub_eq_zero.1 (P.coP_inj w _ ((D.fm u).ptC.sub_mem hz' hz) h0)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun φ hφ => by rw [h0 φ hφ]; exact Submodule.zero_mem _, Formalism.MainNotions.GlobalTheoryTheory.Inhab.pendJunk D u hE hC hI _ hb, funext fun _ => funext fun c => hE.elim c, funext fun _ => funext fun c => hE.elim c, fun _ => rfl⟩`.
-/
theorem lowerTieAt_of_isEmpty (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace) (hb : BeOnTie D u) (h0 : ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ = 0)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : LowerTieAt D u coM gP :=
  ⟨fun φ hφ => by rw [h0 φ hφ]; exact Submodule.zero_mem _,
    Formalism.MainNotions.GlobalTheoryTheory.Inhab.pendJunk D u hE hC hI _ hb, funext fun _ => funext fun c => hE.elim c,
    funext fun _ => funext fun c => hE.elim c, fun _ => rfl⟩

/- English proof (translation)
Use `h.1 φ hφ` as an intermediate fact. Rewrite `this` using `[hC]`. Conclude with `(Submodule.mem_bot ℂ).1 this`.
-/
theorem lowerTieAt_zero_of_bot (h : LowerTieAt D u coM gP) (hC : (D.fm u).ptC = ⊥) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    Pt D u φ = 0 := by
  have := h.1 φ hφ
  rw [hC] at this
  exact (Submodule.mem_bot ℂ).1 this

end TieAt

section Kill

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

/- English proof (translation)
Rewrite using `[coefLast_monomial, if_neg]`. Introduce `h`. Establish `h1` using `h.1 () 0`. Simplify using `[bExp, bBr, wt10, wt0, iC, iL, Finsupp.single_apply] at h1`.
-/
theorem small2_coef_kill : coefLast (K := ℂ) (rfl : 2 = 1 + 1) (bExp rfl (fun _ : Unit => wt10) (fun _ : Unit => wt0))
    (monomial (Finsupp.single ((), (0 : Fin 2), (0 : Fin 2)) 1) 1) = 0 := by
  rw [coefLast_monomial, if_neg]
  intro h
  have h1 := h.1 () 0
  simp [bExp, bBr, wt10, wt0, iC, iL, Finsupp.single_apply] at h1

/- English proof (translation)
Establish `e : (toUnit ℂ 2) (X (0, 0)) = monomial (Finsupp.single ((), (0 : Fin 2), (0 : Fin 2)) 1) 1`. Simplify using `only [toUnit, renameEquiv_apply, rename_X]`. Both sides reduce to the same expression. Simplify using `only [brOne, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e, brStdP, LinearMap.smul_apply, small2_coef_kill, map_zero, smul_zero]`.
-/
theorem small2_brOne_kill : brOne ℂ (rfl : 2 = 1 + 1) wt10 wt0 (X (0, 0)) = 0 := by
  have e : (toUnit ℂ 2) (X (0, 0)) = monomial (Finsupp.single ((), (0 : Fin 2), (0 : Fin 2)) 1) 1 := by
    simp only [toUnit, renameEquiv_apply, rename_X]
    rfl
  simp only [brOne, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e, brStdP, LinearMap.smul_apply, small2_coef_kill, map_zero, smul_zero]

end Kill

end At

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.MainNotions.product_first_zeroth_parts

section Eps

/- English proof (translation)
Introduce `_ _ h` and use `Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)`.
-/
theorem eps_natW_anti {n : ℕ} (l : DomWeight n) : Antitone l.natW :=
  fun _ _ h => Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

/- English proof (translation)
Establish `hd : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n l.natW` using `Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl l.natW (eps_natW_anti l) hf`. Establish `h1 : f ∈ weightedHomogeneousSubmodule ℂ (Formalism.GradedWeylDivisibility.colW n n) l.natW` using `(Submodule.mem_inf.mp hd).1`. Rewrite `h1` using `[mem_weightedHomogeneousSubmodule]`. Establish `h2 : f ∈ homogeneousSubmodule (Fin n × Fin n) ℂ (∑ s, l.natW s)`. Rewrite using `[mem_homogeneousSubmodule]`.

Introduce `m hm`. Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_weight_sum, h1 hm]`. Conclude with `(mem_homogeneousSubmodule _ _).1 h2`.
-/
theorem eps_homog {n : ℕ} (l : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ) (hf : f ∈ delSq ℂ n l) :
    f.IsHomogeneous (∑ s, l.natW s) := by
  have hd : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n l.natW := Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl l.natW (eps_natW_anti l) hf
  have h1 : f ∈ weightedHomogeneousSubmodule ℂ (Formalism.GradedWeylDivisibility.colW n n) l.natW := (Submodule.mem_inf.mp hd).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  have h2 : f ∈ homogeneousSubmodule (Fin n × Fin n) ℂ (∑ s, l.natW s) := by
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_weight_sum, h1 hm]
  exact (mem_homogeneousSubmodule _ _).1 h2

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hdeg : (Finsupp.weight 1) m = d` using `hf (mem_support_iff.1 hm)`.

Establish `e : ∑ i ∈ m.support, m i = d`. Rewrite using `[← hdeg, Finsupp.weight_apply, Finsupp.sum]`. Simplify using the standard rewrite rules. Establish `hp : (m.prod fun i k => (-X i : MvPolynomial σ ℂ) ^ k) = (-1 : MvPolynomial σ ℂ) ^ d * m.prod fun i k => X i ^ k`. Unfold `Finsupp.prod`.

Rewrite using `[Finset.prod_congr rfl fun i _ => neg_pow (X i : MvPolynomial σ ℂ) (m i), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, e]`. Rewrite using `[aeval_monomial, monomial_eq, hp, smul_eq_C_mul, algebraMap_eq]`. Simplify using `only [map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_aeval_neg {σ : Type} (f : MvPolynomial σ ℂ) (d : ℕ) (hf : f.IsHomogeneous d) :
    aeval (fun v => -X v) f = ((-1 : ℂ) ^ d) • f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : (Finsupp.weight 1) m = d := hf (mem_support_iff.1 hm)
  have e : ∑ i ∈ m.support, m i = d := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]; simp
  have hp : (m.prod fun i k => (-X i : MvPolynomial σ ℂ) ^ k) = (-1 : MvPolynomial σ ℂ) ^ d * m.prod fun i k => X i ^ k := by
    unfold Finsupp.prod
    rw [Finset.prod_congr rfl fun i _ => neg_pow (X i : MvPolynomial σ ℂ) (m i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, e]
  rw [aeval_monomial, monomial_eq, hp, smul_eq_C_mul, algebraMap_eq]
  simp only [map_pow, map_neg, map_one]
  ring

/- English proof (translation)
Establish `hr : Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `n) ((-1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = aeval (fun v => -X v) := by`. Unfold `Formalism.GradedWeylDivisibility.rowAct`. Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `[Matrix.one_apply, apply_ite C, ite_mul]`.

Unfold `sqAct detPow`. Rewrite using `[hr, eps_aeval_neg f _ (eps_homog l f hf), smul_smul]`. Use `congr 1`. Rewrite using `[Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`. Use `congr 1`.

Unfold `Formalism.MainNotions.PrimeDegreeVariant.wsum DomWeight.natW`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Establish `hge : ∀ i : Fin n, l.detShift ≤ l.w i`.

Introduce `i`. Simplify using `only [DomWeight.detShift, hn, dite_true]`. Conclude with `l.anti (Fin.mk_le_mk.2 (by omega))`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (sub_nonneg.2 (hge i)), Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_sqAct_neg_one {n : ℕ} (l : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ) (hf : f ∈ delSq ℂ n l) :
    sqAct ℂ n l (-1) f = ((-1 : ℂ) ^ Formalism.MainNotions.PrimeDegreeVariant.wsum l) • f := by
  have hr : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) ((-1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose =
      aeval (fun v => -X v) := by
    unfold Formalism.GradedWeylDivisibility.rowAct
    congr 1
    funext v
    simp [Matrix.one_apply, apply_ite C, ite_mul]
  unfold sqAct detPow
  rw [hr, eps_aeval_neg f _ (eps_homog l f hf), smul_smul]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one,
    Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin, ← zpow_natCast, ← zpow_mul, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1
  unfold Formalism.MainNotions.PrimeDegreeVariant.wsum DomWeight.natW
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hge : ∀ i : Fin n, l.detShift ≤ l.w i := by
      intro i
      simp only [DomWeight.detShift, hn, dite_true]
      exact l.anti (Fin.mk_le_mk.2 (by omega))
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (sub_nonneg.2 (hge i)), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/- English proof (translation)
Unfold `sqAct`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `Formalism.UG.P.weyl_module_GL_stable ℂ N N le_rfl lam.natW (inside₂ ℂ N g) f hf` as an intermediate fact. Simplify `this` using `[Formalism.UG.dwAct, inside₂, delSq]`.
-/
theorem eps_sqAct_mem (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ delSq ℂ N lam) : sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  unfold sqAct; refine Submodule.smul_mem _ _ ?_
  have := Formalism.UG.P.weyl_module_GL_stable ℂ N N le_rfl lam.natW (inside₂ ℂ N g) f hf
  simpa [Formalism.UG.dwAct, inside₂, delSq] using this

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.ten`. Simplify using `only [Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]`.
-/
theorem eps_ten_smul {ι : Type} [Fintype ι] {n : ℕ} (c : ι → ℂ) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => c τ • g τ) = (∏ τ, c τ) • Formalism.MainNotions.product_first_zeroth_parts.ten g := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}

/- English proof (translation)
The claim follows from `blk_ten (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))) f`.
-/
theorem negOp_ten (f : D.what₂.Tau → MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    negOp D u (Formalism.MainNotions.product_first_zeroth_parts.ten f) =
      Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) (f τ) :=
  blk_ten (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))) f

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Rewrite using `[negOp_ten]`. Use `Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩` and prove the remaining obligations.

Use `eps_sqAct_mem _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) (f τ) (by rw [lamTr, delSq_wSh]; exact hf τ)` as an intermediate fact. Rewrite `this` using `[lamTr, delSq_wSh]`. Then use the resulting hypothesis. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem negOp_mem {p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ}
    (hp : p ∈ CSpan ((D.fm u).lam D.R.m)) : negOp D u p ∈ CSpan ((D.fm u).lam D.R.m) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [negOp_ten]
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have := eps_sqAct_mem _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) (f τ)
      (by rw [lamTr, delSq_wSh]; exact hf τ)
    rwa [lamTr, delSq_wSh] at this
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Establish `hinv : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))⁻¹ = Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)`. Rewrite using `[← map_inv, inv_neg_one]`. Establish `e` using `ta_blk_comp (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))) (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))) p`. Establish `h2 : (fun τ => ⇑(ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) ∘ₗ ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)))) = fun _ : D.what₂.Tau => (id : MvPolynomial (Fin (D.R.N D.R.m) …`. Use function extensionality and compare the values at `τ f`.

Use `ta_sqAct_inv (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) f` as an intermediate fact. Rewrite `this` using `[hinv]`. Conclude with `this`. Rewrite `e` using `[h2, ta_blk_id]`. Conclude with `e`.
-/
theorem negOp_negOp (p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    negOp D u (negOp D u p) = p := by
  have hinv : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))⁻¹ = Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1) := by
    rw [← map_inv, inv_neg_one]
  have e := ta_blk_comp (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)))
    (fun τ => ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))) p
  have h2 : (fun τ => ⇑(ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) ∘ₗ
      ta_sqActL (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)))) =
      fun _ : D.what₂.Tau => (id : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ → _) := by
    funext τ f
    have := ta_sqAct_inv (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) f
    rw [hinv] at this
    exact this
  rw [h2, ta_blk_id] at e
  exact e

/- English proof (translation)
Unfold `sgnSg`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow]`. Evaluate the numerical expressions.
-/
theorem sgnSg_mul_self : sgnSg D u * sgnSg D u = 1 := by
  unfold sgnSg
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [← mul_zpow]; norm_num

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Establish `hf' : ∀ τ, f τ ∈ delSq ℂ _ (lamTr D u τ)` using `fun τ => by rw [lamTr, delSq_wSh]; exact hf τ`. Rewrite using `[negOp_ten]`.

Unfold `brTen`. Rewrite using `[blk_ten, blk_ten]`. Establish `e : ∀ τ, brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) (f τ)) = ((-1 : ℂ) ^ Formalism.MainNotions.PrimeDegreeVariant.wsum (sgTr D u τ)) • brOne ℂ (Nm_succ D.R).symm (lamTr D …`. Introduce `τ`. Establish `h4` using `brOne_member4 D u τ (interlaceTr D u hI τ)`.

Rewrite using `[h4.2.2.1 (-1) (f τ) (hf' τ)]`. Conclude with `eps_sqAct_neg_one _ _ (h4.1 (f τ) (hf' τ))`. Simplify using `only [e]`. Rewrite using `[eps_ten_smul]`. Both sides reduce to the same expression.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]`. Consider the case `smul a x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_comm]`.
-/
theorem brTen_negOp (hI : (D.fm u).SgInterlace) {p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ}
    (hp : p ∈ CSpan ((D.fm u).lam D.R.m)) : brTen D u (negOp D u p) = sgnSg D u • brTen D u p := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have hf' : ∀ τ, f τ ∈ delSq ℂ _ (lamTr D u τ) := fun τ => by rw [lamTr, delSq_wSh]; exact hf τ
    rw [negOp_ten]
    unfold brTen
    rw [blk_ten, blk_ten]
    have e : ∀ τ, brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
        (sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1)) (f τ)) =
        ((-1 : ℂ) ^ Formalism.MainNotions.PrimeDegreeVariant.wsum (sgTr D u τ)) • brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (f τ) := by
      intro τ
      have h4 := brOne_member4 D u τ (interlaceTr D u hI τ)
      rw [h4.2.2.1 (-1) (f τ) (hf' τ)]
      exact eps_sqAct_neg_one _ _ (h4.1 (f τ) (hf' τ))
    simp only [e]
    rw [eps_ten_smul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | smul a x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_comm]

/- English proof (translation)
Establish `h` using `brTen_negOp hI hp`. Rewrite `h` using `[he, map_smul]`. Establish `h2 : (ε - sgnSg D u) • brTen D u p = 0` using `by rw [sub_smul, h, sub_self]`. Conclude with `(smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)`.
-/
theorem brTen_eps_zero (hI : (D.fm u).SgInterlace) {p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ}
    (hp : p ∈ CSpan ((D.fm u).lam D.R.m)) {ε : ℂ} (he : negOp D u p = ε • p) (hne : ε ≠ sgnSg D u) : brTen D u p = 0 := by
  have h := brTen_negOp hI hp
  rw [he, map_smul] at h
  have h2 : (ε - sgnSg D u) • brTen D u p = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

/- English proof (translation)
Take `⟨p, hp, hne⟩` from `brTen_ne (D := D) (u := u) hI`. Establish `hs` using `sgnSg_mul_self (D := D) (u := u)`. Use `⟨(1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p), Submodule.smul_mem _ _ (add_mem hp (Submodule.smul_mem _ _ (negOp_mem hp))), ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : negOp D u ((1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p)) = (1 / 2 : ℂ) • (negOp D u p + sgnSg D u • p)`. Rewrite using `[map_smul, map_add, map_smul, negOp_negOp]`.

Establish `e2 : sgnSg D u • ((1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p)) = (1 / 2 : ℂ) • (negOp D u p + sgnSg D u • p)`. Rewrite using `[smul_comm, smul_add, smul_smul, hs, one_smul, add_comm]`. Rewrite using `[e1, e2]`. Rewrite using `[map_smul, map_add, map_smul, brTen_negOp hI hp, smul_smul, hs, one_smul, ← two_smul ℂ, smul_smul]`. Evaluate the numerical expressions.

Conclude with `hne`.
-/
theorem brTen_ne_eps (hI : (D.fm u).SgInterlace) :
    ∃ q ∈ CSpan ((D.fm u).lam D.R.m), negOp D u q = sgnSg D u • q ∧ brTen D u q ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := brTen_ne (D := D) (u := u) hI
  have hs := sgnSg_mul_self (D := D) (u := u)
  refine ⟨(1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p),
    Submodule.smul_mem _ _ (add_mem hp (Submodule.smul_mem _ _ (negOp_mem hp))), ?_, ?_⟩
  · have e1 : negOp D u ((1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p)) = (1 / 2 : ℂ) • (negOp D u p + sgnSg D u • p) := by
      rw [map_smul, map_add, map_smul, negOp_negOp]
    have e2 : sgnSg D u • ((1 / 2 : ℂ) • (p + sgnSg D u • negOp D u p)) = (1 / 2 : ℂ) • (negOp D u p + sgnSg D u • p) := by
      rw [smul_comm, smul_add, smul_smul, hs, one_smul, add_comm]
    rw [e1, e2]
  · rw [map_smul, map_add, map_smul, brTen_negOp hI hp, smul_smul, hs, one_smul, ← two_smul ℂ, smul_smul]
    norm_num
    exact hne

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ, h⟩` from `hS`. Conclude with `h (brTen_eps_zero hI (hC φ hφ) (hV φ hφ) hne)`.
-/
theorem parityAt_of_seenAt {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)} (hI : (D.fm u).SgInterlace)
    {w : D.what₂.places.Pl} {c : (D.fm u).clsP} {ε : ℂ}
    (hC : ∀ φ ∈ (D.fm u).Fi D.R.m, coM w c (φ ((D.fm u).til c)) ∈ CSpan ((D.fm u).lam D.R.m))
    (hV : ValEps D u coM w c ε) (hS : SeenAt D u coM w c) : ParityAt D u ε := by
  by_contra hne
  obtain ⟨φ, hφ, h⟩ := hS
  exact h (brTen_eps_zero hI (hC φ hφ) (hV φ hφ) hne)

/- English proof (translation)
Take `⟨q, hq, he, hne⟩` from `brTen_ne_eps (D := D) (u := u) hI`. Take `⟨φ, hφ, e⟩` from `hF q hq (by rw [hP]; exact he)`. Conclude with `⟨φ, hφ, by rw [e]; exact hne⟩`.
-/
theorem seenAt_of_fullAtEps {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)} (hI : (D.fm u).SgInterlace)
    {w : D.what₂.places.Pl} {c : (D.fm u).clsP} {ε : ℂ} (hP : ParityAt D u ε) (hF : FullAtEps D u coM w c ε) :
    SeenAt D u coM w c := by
  obtain ⟨q, hq, he, hne⟩ := brTen_ne_eps (D := D) (u := u) hI
  obtain ⟨φ, hφ, e⟩ := hF q hq (by rw [hP]; exact he)
  exact ⟨φ, hφ, by rw [e]; exact hne⟩

/- English proof (translation)
Introduce `p hp _` and use `hF p hp`.
-/
theorem fullAtEps_of_fullAt {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
    {w : D.what₂.places.Pl} {c : (D.fm u).clsP} (hF : FullAt D u coM w c) (ε : ℂ) : FullAtEps D u coM w c ε :=
  fun p hp _ => hF p hp

/- English proof (translation)
Take `⟨P, -⟩` from `h.2`. Conclude with `lowerTieAt_pos h w c (seenAt_of_fullAtEps P.interlace hP hF)`.
-/
theorem lowerTieAt_pos_eps {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
    {gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ}
    (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) {ε : ℂ} (hP : ParityAt D u ε)
    (hF : FullAtEps D u coM w c ε) : ∃ φ ∈ (D.fm u).Fi D.R.m, 0 < ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re := by
  obtain ⟨P, -⟩ := h.2
  exact lowerTieAt_pos h w c (seenAt_of_fullAtEps P.interlace hP hF)

/- English proof (translation)
Take `⟨P, -⟩` from `h.2`. Conclude with `lowerTieAt_scalar h w c (seenAt_of_fullAtEps P.interlace hP hF) t coP' h1 h3`.
-/
theorem lowerTieAt_scalar_eps {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
    {gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ}
    (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) {ε : ℂ} (hP : ParityAt D u ε)
    (hF : FullAtEps D u coM w c ε) (t : ℂ)
    (coP' : (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (h1 : ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, coP' (t • Pt D u φ) c = brTen D u (coM w c (φ ((D.fm u).til c))))
    (h3 : ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (nfAll (D.fm u).sg (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))
        (blk (fun τ => Formalism.BasicNotions.sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP' z c))).re) : ‖t‖ = 1 := by
  obtain ⟨P, -⟩ := h.2
  exact lowerTieAt_scalar h w c (seenAt_of_fullAtEps P.interlace hP hF) t coP' h1 h3

end Eps

end Formalism.L2.Ker
