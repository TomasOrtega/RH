import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

def IsConst (L : HermLB (𝟙 (Sp ℤ))) (t : ℝ) : Prop :=
  ∀ i, (∀ x, x ∈ L.B.U i) ∧ ∀ σ y, (L.φ σ).φ i y = 2 * t

/- English proof (translation)
Introduce `_` and use `⟨fun _ => trivial, fun _ _ => zero_add _⟩`.
-/
theorem isConst_trivShift (t : ℝ) : IsConst (trivShift t) t :=
  fun _ => ⟨fun _ => trivial, fun _ _ => zero_add _⟩

/- English proof (translation)
Introduce `_` and use `⟨fun _ => trivial, fun _ _ => (mul_zero _).symm⟩`.
-/
theorem isConst_triv : IsConst (HermLB.triv _) 0 :=
  fun _ => ⟨fun _ => trivial, fun _ _ => (mul_zero _).symm⟩

variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}

/- English proof (translation)
Introduce `i` and use `⟨fun x => ⟨(h i.1).1 x, (h' i.2).1 x⟩, fun σ y => (congrArg₂ (· + ·) ((h i.1).2 σ y) ((h' i.2).2 σ y)).trans (by ring)⟩`.
-/
theorem IsConst.tens (h : IsConst L s) (h' : IsConst M t) : IsConst (L.tens M) (s + t) :=
  fun i => ⟨fun x => ⟨(h i.1).1 x, (h' i.2).1 x⟩, fun σ y =>
    (congrArg₂ (· + ·) ((h i.1).2 σ y) ((h' i.2).2 σ y)).trans (by ring)⟩

/- English proof (translation)
Introduce `i` and use `⟨(h i).1, fun σ y => (congrArg (- ·) ((h i).2 σ y)).trans (by ring)⟩`.
-/
theorem IsConst.dual (h : IsConst L s) : IsConst L.dual (-s) :=
  fun i => ⟨(h i).1, fun σ y => (congrArg (- ·) ((h i).2 σ y)).trans (by ring)⟩

/- English proof (translation)
Introduce `i` and use `⟨fun x => Set.mem_iInter.2 fun _ => (h _).1 x, fun σ y => ((L.φ σ).zpow_φ _ i y).trans (by rw [(h _).2]; push_cast; ring)⟩`.
-/
theorem IsConst.pow (h : IsConst L s) (m : ℕ) : IsConst (L.pow m) (m * s) :=
  fun i => ⟨fun x => Set.mem_iInter.2 fun _ => (h _).1 x, fun σ y =>
    ((L.φ σ).zpow_φ _ i y).trans (by rw [(h _).2]; push_cast; ring)⟩

/- English proof (translation)
Use `(h.pow n.toNat).tens (h.pow (-n).toNat).dual` as an intermediate fact. Establish `e : (n : ℝ) = (n.toNat : ℝ) - ((-n).toNat : ℝ)` using `by exact_mod_cast (Int.toNat_sub_toNat_neg n).symm`. Rewrite using `[show (n : ℝ) * s = n.toNat * s + -((-n).toNat * s) by rw [← sub_eq_add_neg, ← sub_mul, ← e]]`. Conclude with `this`.
-/
theorem IsConst.zp (h : IsConst L s) (n : ℤ) : IsConst (zp L n) (n * s) := by
  have := (h.pow n.toNat).tens (h.pow (-n).toNat).dual
  have e : (n : ℝ) = (n.toNat : ℝ) - ((-n).toNat : ℝ) := by exact_mod_cast (Int.toNat_sub_toNat_neg n).symm
  rw [show (n : ℝ) * s = n.toNat * s + -((-n).toNat * s) by rw [← sub_eq_add_neg, ← sub_mul, ← e]]
  exact this

/- English proof (translation)
Rewrite using `[← Finset.sum_map_toList, comb]`. Proceed by induction on `(Finset.univ : Finset ι).toList with`. Consider the case `nil => exact isConst_triv`. Consider the case `cons a l ih => exact ((h a).zp _).tens ih`.
-/
theorem isConst_comb {ι : Type} [Fintype ι] {L : ι → HermLB (𝟙 (Sp ℤ))} {t : ι → ℝ} (h : ∀ i, IsConst (L i) (t i))
    (n : ι → ℤ) : IsConst (comb L n) (∑ i, n i * t i) := by
  rw [← Finset.sum_map_toList, comb]
  induction (Finset.univ : Finset ι).toList with
  | nil => exact isConst_triv
  | cons a l ih => exact ((h a).zp _).tens ih

open Classical in

/- English proof (translation)
Use `(IsClosedImmersion.isAffine_surjective_of_isAffine i).1` as an intermediate fact. Establish `hinj` using `(algebraMap κ Γ(Z, ⊤)).injective`. Establish `hb : Function.Bijective (algebraMap κ Γ(Z, ⊤))` using `⟨hinj, fun a =>`. Establish `⟨n, hn⟩` using `surjective_intCast i a`. Use the proof step `⟨n, (map_intCast _ n).trans hn⟩⟩`.

Choose the witnesses or unpack the hypotheses as in `rfl : d = 0 := by`. Rewrite `hd` using `[IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph]`. Use `hd.symm.trans ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans ((ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)).symm.trans (ringKrullDim_eq_zero_of_field κ)))` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h0` using `(isArithHeight_trivShift t).vertical Z i κ 0 hd`.

Rewrite `h0`, the goal using `[topSelfIntersection, interNum_of_isEmpty]`. Conclude with `h0`. Use `point Z i _ _ _ hc _ r hr := by`. Use `(IsClosedImmersion.isAffine_surjective_of_isAffine i).1` as an intermediate fact. Set `e` to `RingEquiv.ofBijective (Int.castRingHom Γ(Z, ⊤)) ⟨Int.cast_injective, surjective_intCast i⟩`.

Establish `h0 : (i (genericPoint Z)).asIdeal = ⊥` using `eq_bot_iff.2 fun n hn => Int.cast_eq_zero.1 ((mem_asIdeal_iff i n).1 hn)`. Set `σ` to `Int.castRingHom ℂ`. Set `y : CxPts (i ≫ 𝟙 _) σ` to `ofHom (isAffineOpen_top Z) (σ.comp e.symm) fun a => RingHom.congr_fun (RingHom.ext_int ((σ.comp e.symm.toRingHom).comp (DVR.FlatBC.algX (i ≫ 𝟙 _) ⊤)) σ) a`. Establish `hy (y' : CxPts (i ≫ 𝟙 _) σ) : y' = y` using `Subtype.ext ((cancel_mono (i ≫ 𝟙 _)).1 (y'.2.trans y.2.symm))`. Set `j` to `pick ((L.restr i).φ σ).isLB y`.

Establish `hj (z : Z) : ((L.restr i).div hr).mult z = Scheme.ord (r j : Z.functionField) z` using `((presents_divOfRatSec _ hr).isEqn j z (Set.mem_iInter.2 fun _ => (h _).1 _)).mult_eq`. Establish `e' : ((L.restr i).φ σ).φ j y = 2 * t` using `((L.φ σ).pull_φ i rfl j y).trans ((h _).2 _ _)`. Rewrite using `[if_pos h0, HermLB.curveDeg, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h, finsum_eq_single _ y fun y' h => absurd (hy y') h, logNorm]`. Simplify using `only [hj]`. Rewrite using `[(product_formula e y (r j).ne_zero).2]`.

Rewrite using `[e']`. Expand and normalize the polynomial expressions, which then agree. Use `recursion Z i _ _ _ _ e he hd := by`. Use `hd.ge.trans (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans isArithVar_int.dim_eq.le)` as an intermediate fact. Normalize the coercions in `at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem IsConst.isArithHeight (h : IsConst L t) : L.IsArithHeight fun x =>
    if x.asIdeal = ⊥ then t else Real.log (Nat.card (ℤ ⧸ x.asIdeal)) where
  vertical Z i _ _ κ _ _ _ d hd := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    have hinj := (algebraMap κ Γ(Z, ⊤)).injective
    have hb : Function.Bijective (algebraMap κ Γ(Z, ⊤)) := ⟨hinj, fun a =>
      have ⟨n, hn⟩ := surjective_intCast i a
      ⟨n, (map_intCast _ n).trans hn⟩⟩
    obtain rfl : d = 0 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph] at hd
      have := hd.symm.trans ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
        ((ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)).symm.trans (ringKrullDim_eq_zero_of_field κ)))
      exact_mod_cast this
    have h0 := (isArithHeight_trivShift t).vertical Z i κ 0 hd
    rw [topSelfIntersection, interNum_of_isEmpty] at h0 ⊢
    exact h0
  point Z i _ _ _ hc _ r hr := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    let e := RingEquiv.ofBijective (Int.castRingHom Γ(Z, ⊤))
      ⟨Int.cast_injective, surjective_intCast i⟩
    have h0 : (i (genericPoint Z)).asIdeal = ⊥ := eq_bot_iff.2 fun n hn =>
      Int.cast_eq_zero.1 ((mem_asIdeal_iff i n).1 hn)
    let σ := Int.castRingHom ℂ
    let y : CxPts (i ≫ 𝟙 _) σ := ofHom (isAffineOpen_top Z) (σ.comp e.symm) fun a =>
      RingHom.congr_fun (RingHom.ext_int ((σ.comp e.symm.toRingHom).comp
        (DVR.FlatBC.algX (i ≫ 𝟙 _) ⊤)) σ) a
    have hy (y' : CxPts (i ≫ 𝟙 _) σ) : y' = y :=
      Subtype.ext ((cancel_mono (i ≫ 𝟙 _)).1 (y'.2.trans y.2.symm))
    let j := pick ((L.restr i).φ σ).isLB y
    have hj (z : Z) : ((L.restr i).div hr).mult z = Scheme.ord (r j : Z.functionField) z :=
      ((presents_divOfRatSec _ hr).isEqn j z (Set.mem_iInter.2 fun _ => (h _).1 _)).mult_eq
    have e' : ((L.restr i).φ σ).φ j y = 2 * t := ((L.φ σ).pull_φ i rfl j y).trans ((h _).2 _ _)
    rw [if_pos h0, HermLB.curveDeg, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h,
      finsum_eq_single _ y fun y' h => absurd (hy y') h, logNorm]
    simp only [hj]
    rw [(product_formula e y (r j).ne_zero).2]
    rw [e']
    ring
  recursion Z i _ _ _ _ e he hd := by
    have := hd.ge.trans (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      isArithVar_int.dim_eq.le)
    norm_cast at this
    omega

/- English proof (translation)
The claim follows from `Ideal.ext fun n => (mem_asIdeal_iff (𝟙 (Sp ℤ)) n).trans (have := isArithVar_int.charZero; Int.cast_eq_zero)`.
-/
theorem genericPoint_asIdeal : (genericPoint (Sp ℤ)).asIdeal = ⊥ := Ideal.ext fun n =>
    (mem_asIdeal_iff (𝟙 (Sp ℤ)) n).trans (have := isArithVar_int.charZero; Int.cast_eq_zero)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, h.isArithHeight, if_pos genericPoint_asIdeal⟩`.
-/
theorem IsConst.isSelfInter (h : IsConst L t) : L.IsSelfInter t :=
  ⟨_, h.isArithHeight, if_pos genericPoint_asIdeal⟩

def linFun {ι : Type} [Fintype ι] (t : ι → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  ∑ i, t i • lcoeff ℝ (Finsupp.single i 1)

/- English proof (translation)
Use `⟨fun n => ?_, fun P d hd hP => ?_⟩` and prove the remaining obligations. Use `(isConst_comb (fun i => isConst_trivShift (t i)) n).isSelfInter using 1` and compare the differences between its conclusion and the goal. Simplify using `only [linFun, lin, zero_add, pow_one, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply, coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero]`. Simplify using `[mul_comm]`. Simplify using `only [linFun, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hP.coeff_eq_zero (by simpa using hd.symm), smul_zero]`.
-/
theorem isArFun_trivShift {ι : Type} [Fintype ι] (t : ι → ℝ) : IsArFun (fun i => trivShift (t i)) 0 (linFun t) := by
  classical
  refine ⟨fun n => ?_, fun P d hd hP => ?_⟩
  · convert (isConst_comb (fun i => isConst_trivShift (t i)) n).isSelfInter using 1
    simp only [linFun, lin, zero_add, pow_one, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply, coeff_sum,
      coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero]
    simp [mul_comm]
  · simp only [linFun, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hP.coeff_eq_zero (by simpa using hd.symm), smul_zero]

/- English proof (translation)
Simplify using `[linFun, coeff_X', Finsupp.single_left_inj]`.
-/
theorem linFun_X {ι : Type} [Fintype ι] (t : ι → ℝ) (i : ι) : linFun t (MvPolynomial.X i) = t i := by
  classical
  simp [linFun, coeff_X', Finsupp.single_left_inj]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: CharZero (Sp ℤ).functionField`. Use `isArithVar_int.charZero` as an intermediate fact. Conclude with `((fnOf ⊤ (Opens.mem_top (genericPoint (Sp ℤ)))).charZero_iff (fnOf_injective ⊤ _)).1 this`. Conclude with `((algebraMap (Sp ℤ).functionField ((Sp ℤ).residueField (genericPoint _))).charZero_iff (RingHom.injective _)).1 this`.

Rewrite using `[(genericPoint_spec (Sp ℤ)).def]`. Conclude with `(IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans isArithVar_int.dim_eq`.
-/
theorem isAlgPt_generic : IsAlgPt (genericPoint (Sp ℤ)) := by
  refine ⟨?_, ?_⟩
  · have : CharZero (Sp ℤ).functionField := by
      have := isArithVar_int.charZero
      exact ((fnOf ⊤ (Opens.mem_top (genericPoint (Sp ℤ)))).charZero_iff (fnOf_injective ⊤ _)).1 this
    exact ((algebraMap (Sp ℤ).functionField ((Sp ℤ).residueField (genericPoint _))).charZero_iff
      (RingHom.injective _)).1 this
  · rw [(genericPoint_spec (Sp ℤ)).def]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans isArithVar_int.dim_eq

/- English proof (translation)
Use `le_limsup_of_frequently_le (Frequently.of_forall fun m => ?_)` and prove the remaining obligations. Use `mul_nonneg ?_ (EReal.coe_nonneg.2 (by positivity))` and prove the remaining obligations. Rewrite using `[ENNReal.zero_le_log_iff]`. Conclude with `Set.one_le_encard_iff_nonempty.2 ⟨_, (L.pow m).zero_mem_smallSec⟩` after adjusting the coercions.
-/
theorem arVol_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) : 0 ≤ arVol L D := by
  refine le_limsup_of_frequently_le (Frequently.of_forall fun m => ?_)
  refine mul_nonneg ?_ (EReal.coe_nonneg.2 (by positivity))
  rw [ENNReal.zero_le_log_iff]
  exact_mod_cast Set.one_le_encard_iff_nonempty.2 ⟨_, (L.pow m).zero_mem_smallSec⟩

/- English proof (translation)
Set `Q : MvPolynomial ι ℝ` to `∑ a ∈ (Finset.univ : Finset ι).piAntidiag d, monomial (Finsupp.equivFunOnFinite.symm a) ((Nat.multinomial Finset.univ a : ℝ) * Φ (monomial (Finsupp.equivFunOnFinite.symm a) 1))`. Establish `hQ (x : ι → ℝ) : eval x Q = Φ (lin x ^ d)`. Rewrite using `[lin, Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `e : (Nat.multinomial Finset.univ a : MvPolynomial ι ℝ) * ∏ i, (C (x i) * MvPolynomial.X i) ^ a i = ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, x i ^ a i) • monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℝ)`.

Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (by simp), smul_eq_C_mul]`. Simplify using `[mul_pow, Finset.prod_mul_distrib, mul_assoc]`. Rewrite using `[e, map_smul, eval_monomial, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : Q = 0`. Use `funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ)) (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_` and prove the remaining obligations. Use `choose n hn using fun i => hx i trivial`. Rewrite using `[hQ, map_zero, ← h n]`. Use `congr 3`.

Conclude with `funext fun i => (hn i).symm`. Use `(basisMonomials ι ℝ).ext fun a => ?_` and prove the remaining obligations. Rewrite using `[coe_basisMonomials]`. Distinguish the cases in `ha : a.degree = d`. Use `congrArg (coeff a) h0` as an intermediate fact.

Simplify using `only [Q, coeff_sum, coeff_monomial, Equiv.symm_apply_eq, Finset.sum_ite_eq', coeff_zero] at this`. Rewrite `this` using `[if_pos (by simp [← ha, Finsupp.degree_eq_sum])]`. Simplify `this` using `[(Nat.multinomial_pos _ _).ne']`. Conclude with `h' _ _ ha (isHomogeneous_monomial _ rfl)`.
-/
theorem eq_zero_of_pow {ι : Type} [Fintype ι] (d : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Φ (lin (fun i => (n i : ℝ)) ^ d) = 0)
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → Φ P = 0) : Φ = 0 := by
  classical
  let Q : MvPolynomial ι ℝ := ∑ a ∈ (Finset.univ : Finset ι).piAntidiag d,
    monomial (Finsupp.equivFunOnFinite.symm a) ((Nat.multinomial Finset.univ a : ℝ) *
      Φ (monomial (Finsupp.equivFunOnFinite.symm a) 1))
  have hQ (x : ι → ℝ) : eval x Q = Φ (lin x ^ d) := by
    rw [lin, Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : (Nat.multinomial Finset.univ a : MvPolynomial ι ℝ) * ∏ i, (C (x i) * MvPolynomial.X i) ^ a i =
        ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, x i ^ a i) • monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℝ) := by
      rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), smul_eq_C_mul]
      simp [mul_pow, Finset.prod_mul_distrib, mul_assoc]
    rw [e, map_smul, eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]
    ring
  have h0 : Q = 0 := by
    refine funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i trivial
    rw [hQ, map_zero, ← h n]
    congr 3
    exact funext fun i => (hn i).symm
  refine (basisMonomials ι ℝ).ext fun a => ?_
  rw [coe_basisMonomials]
  by_cases ha : a.degree = d
  · have := congrArg (coeff a) h0
    simp only [Q, coeff_sum, coeff_monomial, Equiv.symm_apply_eq, Finset.sum_ite_eq', coeff_zero] at this
    rw [if_pos (by simp [← ha, Finsupp.degree_eq_sum])] at this
    simpa [(Nat.multinomial_pos _ _).ne'] using this
  · exact h' _ _ ha (isHomogeneous_monomial _ rfl)

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.ArInt.lin`. Rewrite using `[Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i = MvPolynomial.C (∏ i, r i ^ k i) * MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ)`. Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Simplify using `[mul_pow, Finset.prod_mul_distrib, map_prod]`. Rewrite using `[hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Rewrite using `[← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin
  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
/- English proof (translation)
Use `set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) ((Nat.multinomial Finset.univ k : ℝ) * Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef`. Establish `hQ : Q = 0`. Use `MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ)) (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_` and prove the remaining obligations. Use `choose n hn using fun i => hx i (Set.mem_univ i)`. Establish `hxn : x = fun i => (n i : ℝ)` using `funext fun i => (hn i).symm`.

Rewrite using `[map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]`. Establish `hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m → Ψ (MvPolynomial.monomial d 1) = 0`. Introduce `d hd`. Establish `hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m`. Rewrite using `[Finset.mem_piAntidiag]`.

Use `⟨?_, fun i _ => Finset.mem_univ i⟩` and prove the remaining obligations. Rewrite using `[← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules. Establish `hc` using `congrArg (MvPolynomial.coeff d) hQ`. Rewrite `hc` using `[hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)]`.

Rewrite `hc` using `[Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_zero]`. Establish `hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0`. Conclude with `(Nat.multinomial_pos _ _).ne'` after adjusting the coercions. Conclude with `(mul_eq_zero.mp hc).resolve_left hne`. Introduce `b _ hb`.

Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Introduce `heq`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← heq]`. Simplify using the standard rewrite rules.

Introduce `h`. Conclude with `absurd hmem h`. Rewrite using `[P.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `hP (MvPolynomial.mem_support_iff.mp hd)`.

Establish `hsm : MvPolynomial.monomial d (MvPolynomial.coeff d P) = MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℝ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hsm, map_smul, hmon d hw, smul_zero]`.
-/
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (MvPolynomial.coeff d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (MvPolynomial.coeff d P) =
      MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Take `⟨h1', h2'⟩` from `h'`. Establish `hpow : ∀ n : ι → ℤ, (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0`. Introduce `n`. Rewrite using `[LinearMap.sub_apply, sub_eq_zero]`.

Conclude with `_root_.GlobalTheory.HermLB.IsSelfInter.unique hX (h1 n) (h1' n)`. Establish `hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P`. Introduce `P d hP`. Distinguish the cases in `hd : d = D + 1`. Substitute `hd` using the available equality.

Conclude with `sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)`. Rewrite using `[h2 P d hd hP, h2' P d hd hP]`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Rewrite using `[← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)`.
-/
theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_
  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (eq_zero_of_pow D _ (fun n => sub_eq_zero.2 ((h.1 n).trans (h'.1 n).symm)) fun P e he hP => sub_eq_zero.2 ((h.2 P e he hP).trans (h'.2 P e he hP).symm))`.
-/
theorem isGeoFun_unique {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    {ι : Type} [Fintype ι] {L : ι → HermLB p} {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : IsGeoFun L D Φ) (h' : IsGeoFun L D Φ') :
    Φ = Φ' :=
  sub_eq_zero.1 (eq_zero_of_pow D _ (fun n => sub_eq_zero.2 ((h.1 n).trans (h'.1 n).symm))
    fun P e he hP => sub_eq_zero.2 ((h.2 P e he hP).trans (h'.2 P e he hP).symm))

/- English proof (translation)
Use `⟨_, h.isArithHeight, (if_pos genericPoint_asIdeal).trans ?_⟩` and prove the remaining obligations. Use `isAlgPt_generic.1` as an intermediate fact. Establish `hA` using `functionField_isFractionRing_of_isAffineOpen (Sp ℤ) ⊤ (isAffineOpen_top _)`. Set `e` to `RingEquiv.ofBijective (Int.castRingHom Γ(Sp ℤ, ⊤)) ⟨have := isArithVar_int.charZero; Int.cast_injective, surjective_intCast (𝟙 _)⟩`. Establish `hs : Function.Surjective (algebraMap ℚ ((Sp ℤ).residueField (genericPoint (Sp ℤ))))` using `fun x => by`.

Take `⟨f, rfl⟩` from `IsLocalRing.residue_surjective x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := Γ(Sp ℤ, ⊤)) (K := (Sp ℤ).functionField) f`. Take `⟨a, rfl⟩` from `e.surjective a`. Take `⟨b, rfl⟩` from `e.surjective b`. Use `⟨a / b, ?_⟩` and prove the remaining obligations.

Establish `(n : ℤ) : e n = n` using `rfl`. Rewrite using `[this, this, map_intCast, map_intCast, map_div₀, map_intCast, map_intCast]`. Conclude with `((map_div₀ (IsLocalRing.residue (Sp ℤ).functionField) _ _).trans (by rw [map_intCast, map_intCast]; rfl)).symm`. Set `q` to `RingEquiv.ofBijective _ ⟨RingHom.injective _, hs⟩`. Establish `: Nat.card ((Sp ℤ).residueField (genericPoint (Sp ℤ)) →+* ℂ) = 1`.

Use `Nat.card_eq_one_iff_unique.2 ⟨⟨fun f g => RingHom.ext fun x => ?_⟩, ⟨(Rat.castHom ℂ).comp q.symm⟩⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hs x`. Simplify using the standard rewrite rules. Rewrite using `[this, Nat.cast_one, mul_one]`.
-/
theorem IsConst.isPtHt (h : IsConst L t) : IsPtHt L (genericPoint (Sp ℤ)) t := by
  refine ⟨_, h.isArithHeight, (if_pos genericPoint_asIdeal).trans ?_⟩
  have := isAlgPt_generic.1
  have hA := functionField_isFractionRing_of_isAffineOpen (Sp ℤ) ⊤ (isAffineOpen_top _)
  let e := RingEquiv.ofBijective (Int.castRingHom Γ(Sp ℤ, ⊤))
      ⟨have := isArithVar_int.charZero; Int.cast_injective, surjective_intCast (𝟙 _)⟩
  have hs : Function.Surjective (algebraMap ℚ ((Sp ℤ).residueField (genericPoint (Sp ℤ)))) := fun x => by
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Sp ℤ, ⊤)) (K := (Sp ℤ).functionField) f
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    refine ⟨a / b, ?_⟩
    have (n : ℤ) : e n = n := rfl
    rw [this, this, map_intCast, map_intCast, map_div₀, map_intCast, map_intCast]
    exact ((map_div₀ (IsLocalRing.residue (Sp ℤ).functionField) _ _).trans (by rw [map_intCast, map_intCast]; rfl)).symm
  let q := RingEquiv.ofBijective _ ⟨RingHom.injective _, hs⟩
  have : Nat.card ((Sp ℤ).residueField (genericPoint (Sp ℤ)) →+* ℂ) = 1 := by
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun f g => RingHom.ext fun x => ?_⟩, ⟨(Rat.castHom ℂ).comp q.symm⟩⟩
    obtain ⟨a, rfl⟩ := hs x
    simp
  rw [this, Nat.cast_one, mul_one]

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective (Int.castRingHom Γ(Sp ℤ, ⊤)) ⟨have := isArithVar_int.charZero; Int.cast_injective, surjective_intCast (𝟙 _)⟩`. Establish `hU (i) : L.B.U i = ⊤` using `top_le_iff.1 fun x _ => (h i).1 x`. Establish `hb (U : (Sp ℤ).Opens) (hU : U = ⊤) : Function.Bijective (Int.cast : ℤ → Γ(Sp ℤ, U))`. Substitute `hU` using the available equality. Conclude with `e.bijective`.

Set `s (n : ℤ) : L.B.Sec` to `⟨fun i => n, fun i j => by`. Take `rfl : i = j` from `Subsingleton.elim _ _`. Use `LB.resG_g_self L.isLB i (le_refl _)` as an intermediate fact. Rewrite using `[map_intCast, show ((L.B.g i i : Γ(Sp ℤ, L.B.U i ⊓ L.B.U i))) = 1 by simpa [resG] using this, one_mul]⟩`. Set `σ` to `Int.castRingHom ℂ`.

Set `y₀ : CxPts (𝟙 (Sp ℤ)) σ` to `⟨spMap σ, Category.comp_id _⟩`. Set `i₀` to `pick L.isLB y₀`. Establish `hs : Function.Bijective s` using `⟨fun a b hab => (hb _ (hU i₀)).1 (congrArg (·.f i₀) hab), fun u => by`. Take `⟨n, hn⟩` from `(hb _ (hU i₀)).2 (u.f i₀)`. Conclude with `⟨n, DVR.SecOps.sec_ext fun i => by obtain rfl : i = i₀ := Subsingleton.elim _ _; exact hn⟩⟩`.

Establish `hn (n : ℤ) (τ) (y : CxPts (𝟙 (Sp ℤ)) τ) : (L.φ τ).nsq (secVal _ τ (s n)) y ≤ 1 ↔ |(n : ℝ)| ≤ Real.exp t`. Rewrite using `[Weight.nsq, (h _).2, secVal_apply, ev_eq (mem_pick _ y)]`. Simplify using `only [s, map_intCast, Complex.norm_intCast]`. Rewrite using `[Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul, show 2 * t = (2 : ℕ) * t by norm_num, Real.exp_nat_mul, pow_le_pow_iff_left₀ (abs_nonneg _) (Real.exp_pos _).le two_ne_zero]`. Rewrite using `[← hs.1.encard_image]`.

Use `congr 1`. Use extensionality with `u`. Take `⟨n, rfl⟩` from `hs.2 u`. Rewrite using `[hs.1.mem_set_image]`. Conclude with `⟨fun H => (hn n σ y₀).1 (H σ y₀), fun H τ y => (hn n τ y).2 H⟩`.
-/
theorem IsConst.encard_smallSec (h : IsConst L t) [Subsingleton L.B.ι] :
    L.smallSec.encard = {n : ℤ | |(n : ℝ)| ≤ Real.exp t}.encard := by
  let e := RingEquiv.ofBijective (Int.castRingHom Γ(Sp ℤ, ⊤))
      ⟨have := isArithVar_int.charZero; Int.cast_injective, surjective_intCast (𝟙 _)⟩
  have hU (i) : L.B.U i = ⊤ := top_le_iff.1 fun x _ => (h i).1 x
  have hb (U : (Sp ℤ).Opens) (hU : U = ⊤) : Function.Bijective (Int.cast : ℤ → Γ(Sp ℤ, U)) := by
    subst hU; exact e.bijective
  let s (n : ℤ) : L.B.Sec := ⟨fun i => n, fun i j => by
    obtain rfl : i = j := Subsingleton.elim _ _
    have := LB.resG_g_self L.isLB i (le_refl _)
    rw [map_intCast, show ((L.B.g i i : Γ(Sp ℤ, L.B.U i ⊓ L.B.U i))) = 1 by simpa [resG] using this, one_mul]⟩
  let σ := Int.castRingHom ℂ
  let y₀ : CxPts (𝟙 (Sp ℤ)) σ := ⟨spMap σ, Category.comp_id _⟩
  let i₀ := pick L.isLB y₀
  have hs : Function.Bijective s := ⟨fun a b hab => (hb _ (hU i₀)).1 (congrArg (·.f i₀) hab), fun u => by
    obtain ⟨n, hn⟩ := (hb _ (hU i₀)).2 (u.f i₀)
    exact ⟨n, DVR.SecOps.sec_ext fun i => by obtain rfl : i = i₀ := Subsingleton.elim _ _; exact hn⟩⟩
  have hn (n : ℤ) (τ) (y : CxPts (𝟙 (Sp ℤ)) τ) : (L.φ τ).nsq (secVal _ τ (s n)) y ≤ 1 ↔ |(n : ℝ)| ≤ Real.exp t := by
    rw [Weight.nsq, (h _).2, secVal_apply, ev_eq (mem_pick _ y)]
    simp only [s, map_intCast, Complex.norm_intCast]
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul, show 2 * t = (2 : ℕ) * t by norm_num, Real.exp_nat_mul,
      pow_le_pow_iff_left₀ (abs_nonneg _) (Real.exp_pos _).le two_ne_zero]
  rw [← hs.1.encard_image]
  congr 1
  ext u
  obtain ⟨n, rfl⟩ := hs.2 u
  rw [hs.1.mem_set_image]
  exact ⟨fun H => (hn n σ y₀).1 (H σ y₀), fun H τ y => (hn n τ y).2 H⟩

/- English proof (translation)
Establish `hc (m : ℕ) : ((trivShift t).pow m).smallSec.encard = (2 * ⌊Real.exp (m * t)⌋₊ + 1 : ℕ)`. Establish `: Subsingleton ((trivShift t).pow m).B.ι` using `inferInstanceAs (Subsingleton (PUnit → PUnit))`. Rewrite using `[((isConst_trivShift t).pow m).encard_smallSec]`. Establish `: {n : ℤ | |(n : ℝ)| ≤ Real.exp (m * t)} = (Finset.Icc (-(⌊Real.exp (m * t)⌋₊ : ℤ)) ⌊Real.exp (m * t)⌋₊ : Finset ℤ)`. Use extensionality with `n`.

Rewrite using `[Finset.coe_Icc, Set.mem_Icc, ← abs_le, Int.natCast_floor_eq_floor (Real.exp_pos _).le, Int.le_floor, Int.cast_abs, Set.mem_setOf_eq]`. Rewrite using `[this, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hl : Tendsto (fun m : ℕ => Real.log (2 * ⌊Real.exp (m * t)⌋₊ + 1 : ℕ) * (1 / m)) atTop (𝓝 t)`.

Establish `h3 : Tendsto (fun m : ℕ => t + Real.log 3 / m) atTop (𝓝 t)`. Simplify using `using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 3)).const_add t`. Apply the tactic sequence `refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_ <;> filter_upwards [eventually_gt_atTop 0] with m hm`. Use `all_goals`. Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`.

Establish `h1 : 1 ≤ Real.exp (m * t)` using `Real.one_le_exp (by positivity)`. Establish `h2` using `Nat.floor_le (Real.exp_pos (m * t)).le`. Establish `h4` using `Nat.lt_floor_add_one (Real.exp (m * t))`. Establish `h5 : (0 : ℝ) ≤ ⌊Real.exp (m * t)⌋₊` using `Nat.cast_nonneg _`. Use `push_cast`.

Rewrite using `[mul_one_div]`. Rewrite using `[le_div_iff₀ hm', Real.le_log_iff_exp_le (by positivity), mul_comm t]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne', Real.log_le_iff_le_exp (by positivity), Real.exp_add, Real.exp_log (by norm_num), mul_comm t]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Tendsto.limsup_eq ((EReal.tendsto_coe.2 hl).congr fun m => ?_)` and prove the remaining obligations. Rewrite using `[hc, EReal.coe_mul, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos (by positivity)]`. Simplify using the standard rewrite rules.
-/
theorem arVol_trivShift (ht : 0 ≤ t) : arVol (trivShift t) 0 = (t : EReal) := by
  have hc (m : ℕ) : ((trivShift t).pow m).smallSec.encard = (2 * ⌊Real.exp (m * t)⌋₊ + 1 : ℕ) := by
    have : Subsingleton ((trivShift t).pow m).B.ι := inferInstanceAs (Subsingleton (PUnit → PUnit))
    rw [((isConst_trivShift t).pow m).encard_smallSec]
    have : {n : ℤ | |(n : ℝ)| ≤ Real.exp (m * t)} =
        (Finset.Icc (-(⌊Real.exp (m * t)⌋₊ : ℤ)) ⌊Real.exp (m * t)⌋₊ : Finset ℤ) := by
      ext n
      rw [Finset.coe_Icc, Set.mem_Icc, ← abs_le, Int.natCast_floor_eq_floor (Real.exp_pos _).le, Int.le_floor,
        Int.cast_abs, Set.mem_setOf_eq]
    rw [this, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
    congr 1
    omega
  have hl : Tendsto (fun m : ℕ => Real.log (2 * ⌊Real.exp (m * t)⌋₊ + 1 : ℕ) * (1 / m)) atTop (𝓝 t) := by
    have h3 : Tendsto (fun m : ℕ => t + Real.log 3 / m) atTop (𝓝 t) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 3)).const_add t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_ <;>
      filter_upwards [eventually_gt_atTop 0] with m hm
    all_goals
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      have h1 : 1 ≤ Real.exp (m * t) := Real.one_le_exp (by positivity)
      have h2 := Nat.floor_le (Real.exp_pos (m * t)).le
      have h4 := Nat.lt_floor_add_one (Real.exp (m * t))
      have h5 : (0 : ℝ) ≤ ⌊Real.exp (m * t)⌋₊ := Nat.cast_nonneg _
      push_cast
      rw [mul_one_div]
    · rw [le_div_iff₀ hm', Real.le_log_iff_exp_le (by positivity), mul_comm t]
      linarith
    · rw [div_le_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne', Real.log_le_iff_le_exp (by positivity), Real.exp_add,
        Real.exp_log (by norm_num), mul_comm t]
      linarith
  refine Tendsto.limsup_eq ((EReal.tendsto_coe.2 hl).congr fun m => ?_)
  rw [hc, EReal.coe_mul, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos (by positivity)]
  simp

/- English proof (translation)
The claim follows from `IsConst.isSelfInter fun _ => ⟨fun _ => trivial, fun _ _ => show u = _ by ring⟩`.
-/
theorem isSelfInter_fnB (u : ℝ) :
    (fnB (p := 𝟙 (Sp ℤ)) (fun _ _ => u) (fun _ => cInfAt_const u) fun _ _ _ _ _ _ _ => rfl).IsSelfInter (u / 2) :=
  IsConst.isSelfInter fun _ => ⟨fun _ => trivial, fun _ _ => show u = _ by ring⟩

/- English proof (translation)
Set `σ` to `Int.castRingHom ℂ`. Set `y : CxPts (𝟙 (Sp ℤ)) σ` to `⟨spMap σ, Category.comp_id _⟩`. Establish `: Subsingleton (CxPts (𝟙 (Sp ℤ)) σ)` using `⟨fun a b => Subtype.ext ((cancel_mono (𝟙 _)).1 (a.2.trans b.2.symm))⟩`. Take `⟨R⟩` from `genSmooth_of_smooth (𝟙 (Sp ℤ)) 0 σ`. Take `⟨a, ha⟩` from `R.cover y`.

Establish `hm (ε : ℤˣ) : (L.φ σ).chernPart 0 ε Set.univ = ENNReal.ofReal (ε : ℤ)`. Rewrite using `[Weight.chernPart_apply (L.cInf σ) ε (R.chart a) MeasurableSet.univ fun z _ => Subsingleton.elim y z ▸ ha]`. Simplify using `only [AlgChart.chernDens_zero, mul_one]`. Rewrite using `[show (R.chart a).e '' Set.univ = Set.univ from Set.eq_univ_of_forall fun v => ⟨y, trivial, Subsingleton.elim _ _⟩]`. Establish `hv : (MeasureTheory.volume : MeasureTheory.Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1`.

Use `(stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped` as an intermediate fact. Rewrite `this` using `[Set.eq_univ_of_forall (s := parallelepiped _) fun v => (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩]`. Then use the resulting hypothesis. Simplify using `[hv]`. Rewrite using `[chInt, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h, Weight.chernInt]`. Simplify using `[MeasureTheory.Measure.real, hm, ENNReal.toReal_ofReal']`.
-/
theorem chInt_const (L : HermLB (𝟙 (Sp ℤ))) (u : ℝ) : chInt L 0 (fun _ _ => u) = u := by
  let σ := Int.castRingHom ℂ
  let y : CxPts (𝟙 (Sp ℤ)) σ := ⟨spMap σ, Category.comp_id _⟩
  have : Subsingleton (CxPts (𝟙 (Sp ℤ)) σ) :=
    ⟨fun a b => Subtype.ext ((cancel_mono (𝟙 _)).1 (a.2.trans b.2.symm))⟩
  obtain ⟨R⟩ := genSmooth_of_smooth (𝟙 (Sp ℤ)) 0 σ
  obtain ⟨a, ha⟩ := R.cover y
  have hm (ε : ℤˣ) : (L.φ σ).chernPart 0 ε Set.univ = ENNReal.ofReal (ε : ℤ) := by
    rw [Weight.chernPart_apply (L.cInf σ) ε (R.chart a) MeasurableSet.univ fun z _ => Subsingleton.elim y z ▸ ha]
    simp only [AlgChart.chernDens_zero, mul_one]
    rw [show (R.chart a).e '' Set.univ = Set.univ from
      Set.eq_univ_of_forall fun v => ⟨y, trivial, Subsingleton.elim _ _⟩]
    have hv : (MeasureTheory.volume : MeasureTheory.Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
      have := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
      rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
        (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
    simp [hv]
  rw [chInt, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h, Weight.chernInt]
  simp [MeasureTheory.Measure.real, hm, ENNReal.toReal_ofReal']

/- English proof (translation)
The claim follows from `chInt_const L 1`.
-/
theorem gdeg_eq_one (L : HermLB (𝟙 (Sp ℤ))) : gdeg L 0 = 1 := chInt_const L 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n => by simp [gdeg_eq_one], fun P d hd hP => hP.coeff_eq_zero (by simpa using hd.symm)⟩`.
-/
theorem isGeoFun_int {ι : Type} [Fintype ι] (L : ι → HermLB (𝟙 (Sp ℤ))) : IsGeoFun L 0 (lcoeff ℝ 0) :=
  ⟨fun n => by simp [gdeg_eq_one], fun P d hd hP => hP.coeff_eq_zero (by simpa using hd.symm)⟩

end GlobalTheory.ArInt.Model
