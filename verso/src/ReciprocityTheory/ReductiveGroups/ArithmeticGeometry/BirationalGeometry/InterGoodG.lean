import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodF

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segQ (P : Ideal (MRing ι)) (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
  Ideal.Quotient.mk _ (segMon i)

/- English proof (translation)
Use `conv_rhs => rw [H.as_sum]`. Use `conv_lhs => rw [H.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]`.

Simplify using `only [map_mul, map_prod, map_pow, aeval_C, aeval_X, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, rename_C, rename_X, algebraMap_eq, hc m hm, mul_assoc]`.
-/
private lemma rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support {r : ℕ} {S : Type} [Fintype S] (c : S → ℕ)
    (H : MvPolynomial (Fin r ⊕ S) ℚ) (hc : ∀ m ∈ H.support, ∀ s, m (Sum.inr s) = c s) :
    rename Sum.inl (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) *
      ∏ s, (X (Sum.inr s) : MvPolynomial (Fin r ⊕ S) ℚ) ^ c s = H := by
  classical
  conv_rhs => rw [H.as_sum]
  conv_lhs => rw [H.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, aeval_C, aeval_X, Sum.elim_inl, Sum.elim_inr,
    Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, rename_C, rename_X, algebraMap_eq,
    hc m hm, mul_assoc]

/- English proof (translation)
Establish `hf : (fun i : Fin r ⊕ S => aeval a (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1 i)) = Sum.elim a (1 : S → B)`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> simp`. Rewrite using `[← AlgHom.comp_apply, comp_aeval, hf]`.
-/
private lemma aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one {r : ℕ} {S : Type} {B : Type*} [CommRing B] [Algebra ℚ B]
    (a : Fin r → B) (H : MvPolynomial (Fin r ⊕ S) ℚ) :
    aeval (Sum.elim a 1) H = aeval a (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) := by
  have hf : (fun i : Fin r ⊕ S => aeval a (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1 i)) =
      Sum.elim a (1 : S → B) := by
    funext i
    cases i <;> simp
  rw [← AlgHom.comp_apply, comp_aeval, hf]

/- English proof (translation)
Establish `: IsDomain (MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P)` using `isDomain_qQuot P hP hH`. Use `set b : {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P := fun k' => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩) with hbdef`. Set `yt : Fin r ⊕ {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ` to `Sum.elim (fun j => ∑ t, L j t • segMon t) (fun k' => X ⟨k'.1, i0 k'.1⟩)`. Establish `hyt : (fun e => Ideal.Quotient.mkₐ ℚ (qIdeal P) (yt e)) = Sum.elim (forms (segQ P) L) b`. Use function extensionality and compare the values at `e`.

Consider the cases of `e with`. Consider the case `inl j => simp [yt, forms, segQ, map_sum, Ideal.Quotient.mkₐ_eq_mk]`. Consider the case `inr k' => simp [yt, b, Ideal.Quotient.mkₐ_eq_mk]`. Establish `hhomY : ∀ e, IsWeightedHomogeneous (blkWt (ι` using `ι)) (yt e) (sWt k0 r e) := by`. Introduce and unpack `(j | k')`.

Establish `hmem : (∑ t, L j t • segMon t) ∈ weightedHomogeneousSubmodule ℚ (blkWt (ι` using `ι)) oneK := Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (segMon_isWeightedHomogeneous t)`. Conclude with `hmem`. Conclude with `isWeightedHomogeneous_X ℚ (blkWt (ι := ι)) ⟨k'.1, i0 k'.1⟩`. Establish `hb : ∀ k', b k' ≠ 0`. Introduce `k' h`.

Rewrite `h` using `[hbdef, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hi0 k'.1 (mem_of_qmap_mem_qIdeal P hP hH (by simpa using h))`. Establish `hev : ∀ G, aeval (Sum.elim (forms (segQ P) L) b) G = Ideal.Quotient.mk (qIdeal P) (aeval (R` using `ℚ) yt G) := by`. Introduce `G`. Rewrite using `[← hyt, ← comp_aeval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`.

Rewrite using `[algebraicIndependent_iff]`. Introduce `H hH0`. Establish `hmem : aeval (R` using `ℚ) yt H ∈ qIdeal P := by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hev]`. Conclude with `hH0`.

Establish `key : ∀ δ, weightedHomogeneousComponent (sWt k0 r) δ H = 0`. Introduce `δ`. Establish `hHd : IsWeightedHomogeneous (sWt k0 r) (weightedHomogeneousComponent (sWt k0 r) δ H) δ` using `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Establish `hcomp` using `weightedHomogeneousComponent_mem_of_mem ℚ (blkWt (ι := ι)) (qIdeal_isHomogeneous P hhom) hmem δ`. Rewrite `hcomp` using `[component_aeval (sWt k0 r) yt hhomY H δ]`.

Establish `h0 : aeval (Sum.elim (forms (segQ P) L) b) (weightedHomogeneousComponent (sWt k0 r) δ H) = 0`. Rewrite using `[hev, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hcomp`. Assume the negation of the conclusion as `hne`. Take `⟨n0, hn0⟩` from `Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hne)`.

Rewrite `h0` using `[aeval_sumElim_factor k0 hHd hn0]`. Establish `hprod : (∏ k', b k' ^ n0 (Sum.inr k')) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hb k')`. Establish `h1` using `(mul_eq_zero.mp h0).resolve_left hprod`. Rewrite `h1` using `[aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one]`. Establish `h2` using `algebraicIndependent_iff.mp hind _ h1`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support (fun s => n0 (Sum.inr s)) (weightedHomogeneousComponent (sWt k0 r) δ H) ?_, h2, map_zero, zero_mul]`. Introduce `m hm s`. Conclude with `inr_eq_of_weight_eq k0 ((hHd (mem_support_iff.mp hm)).trans (hHd (mem_support_iff.mp hn0)).symm) s`. Use extensionality with `n`.

Use `congrArg (coeff n) (key (Finsupp.weight (sWt k0 r) n))` as an intermediate fact. Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos rfl]`. Simplify using `using this`.
-/
theorem algebraicIndependent_sumElim (P : Ideal (MRing ι)) (hP : P.IsPrime) (hH : IsHorizontal P)
    (hhom : IsMultiHomogIdeal P) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRing ι) ∉ P) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (segQ P) L)) :
    AlgebraicIndependent ℚ (Sum.elim (forms (segQ P) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩))) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) := isDomain_qQuot P hP hH
  set b : {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
    fun k' => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩) with hbdef
  let yt : Fin r ⊕ {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ :=
    Sum.elim (fun j => ∑ t, L j t • segMon t) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : (fun e => Ideal.Quotient.mkₐ ℚ (qIdeal P) (yt e)) = Sum.elim (forms (segQ P) L) b := by
    funext e
    cases e with
    | inl j => simp [yt, forms, segQ, map_sum, Ideal.Quotient.mkₐ_eq_mk]
    | inr k' => simp [yt, b, Ideal.Quotient.mkₐ_eq_mk]
  have hhomY : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · have hmem : (∑ t, L j t • segMon t) ∈
          weightedHomogeneousSubmodule ℚ (blkWt (ι := ι)) oneK :=
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (segMon_isWeightedHomogeneous t)
      exact hmem
    · exact isWeightedHomogeneous_X ℚ (blkWt (ι := ι)) ⟨k'.1, i0 k'.1⟩
  have hb : ∀ k', b k' ≠ 0 := by
    intro k' h
    rw [hbdef, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 (mem_of_qmap_mem_qIdeal P hP hH (by simpa using h))
  have hev : ∀ G, aeval (Sum.elim (forms (segQ P) L) b) G =
      Ideal.Quotient.mk (qIdeal P) (aeval (R := ℚ) yt G) := by
    intro G
    rw [← hyt, ← comp_aeval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [algebraicIndependent_iff]
  intro H hH0
  have hmem : aeval (R := ℚ) yt H ∈ qIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev]
    exact hH0
  have key : ∀ δ, weightedHomogeneousComponent (sWt k0 r) δ H = 0 := by
    intro δ
    have hHd : IsWeightedHomogeneous (sWt k0 r) (weightedHomogeneousComponent (sWt k0 r) δ H) δ :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hcomp := weightedHomogeneousComponent_mem_of_mem ℚ (blkWt (ι := ι))
      (qIdeal_isHomogeneous P hhom) hmem δ
    rw [component_aeval (sWt k0 r) yt hhomY H δ] at hcomp
    have h0 : aeval (Sum.elim (forms (segQ P) L) b) (weightedHomogeneousComponent (sWt k0 r) δ H) = 0 := by
      rw [hev, Ideal.Quotient.eq_zero_iff_mem]
      exact hcomp
    by_contra hne
    obtain ⟨n0, hn0⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hne)
    rw [aeval_sumElim_factor k0 hHd hn0] at h0
    have hprod : (∏ k', b k' ^ n0 (Sum.inr k')) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hb k')
    have h1 := (mul_eq_zero.mp h0).resolve_left hprod
    rw [aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one] at h1
    have h2 := algebraicIndependent_iff.mp hind _ h1
    apply hne
    rw [← rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support (fun s => n0 (Sum.inr s))
      (weightedHomogeneousComponent (sWt k0 r) δ H) ?_, h2, map_zero, zero_mul]
    intro m hm s
    exact inr_eq_of_weight_eq k0 ((hHd (mem_support_iff.mp hm)).trans
      (hHd (mem_support_iff.mp hn0)).symm) s
  ext n
  have := congrArg (coeff n) (key (Finsupp.weight (sWt k0 r) n))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
  simpa using this

/- English proof (translation)
Introduce `hind`. Take `⟨hne, ⟨hprime, hhom, hrel⟩, hH, hdim⟩` from `hP`. Take `⟨k0⟩` from `hne`. Use `choose i0 hi0 using hrel`. Establish `hall` using `algebraicIndependent_sumElim P hprime hH hhom k0 i0 hi0 L hind`.

Use `set n := Fintype.card (Fin r ⊕ {k // k ≠ k0})`. Establish `hall'` using `hall.comp _ (Fintype.equivFin (Fin r ⊕ {k // k ≠ k0})).symm.injective`. Establish `hle` using `succ_le_ringKrullDim_of_algebraicIndependent P hprime hH _ hall'`. Rewrite `hle` using `[hdim]`. Establish `hle' : n + 1 ≤ e + 1 + Fintype.card K` using `by exact_mod_cast hle`.

Establish `hcard : n + 1 = r + Fintype.card K`. Establish `h1 : Fintype.card {k // k ≠ k0} = Fintype.card K - 1`. Simplify using `[Fintype.card_subtype_compl]`. Establish `h2 : 0 < Fintype.card K` using `Fintype.card_pos_iff.mpr ⟨k0⟩`. Simplify using `only [n, Fintype.card_sum, Fintype.card_fin, h1]`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem forms_not_algebraicIndependent (P : Ideal (MRing ι)) (e : ℕ) (hP : IsArithVar P (e + 1))
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℚ) :
    ¬ AlgebraicIndependent ℚ (forms (segQ P) L) := by
  classical
  intro hind
  obtain ⟨hne, ⟨hprime, hhom, hrel⟩, hH, hdim⟩ := hP
  obtain ⟨k0⟩ := hne
  choose i0 hi0 using hrel
  have hall := algebraicIndependent_sumElim P hprime hH hhom k0 i0 hi0 L hind
  set n := Fintype.card (Fin r ⊕ {k // k ≠ k0})
  have hall' := hall.comp _ (Fintype.equivFin (Fin r ⊕ {k // k ≠ k0})).symm.injective
  have hle := succ_le_ringKrullDim_of_algebraicIndependent P hprime hH _ hall'
  rw [hdim] at hle
  have hle' : n + 1 ≤ e + 1 + Fintype.card K := by exact_mod_cast hle
  have hcard : n + 1 = r + Fintype.card K := by
    have h1 : Fintype.card {k // k ≠ k0} = Fintype.card K - 1 := by
      simp [Fintype.card_subtype_compl]
    have h2 : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [n, Fintype.card_sum, Fintype.card_fin, h1]
    omega
  omega

end

end ReciprocityTheory.ChartRestriction.G.Geo
