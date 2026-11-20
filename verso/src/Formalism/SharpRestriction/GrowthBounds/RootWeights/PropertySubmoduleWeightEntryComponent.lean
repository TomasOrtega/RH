import Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentCoefficientsMemProperty

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

/- English proof (translation)
Establish `key` using `laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y ((Finset.range (y.totalDegree + k + 1)).image (fun i : ℕ => (i : ℤ))) (fun z => divPow R LL S a b z.toNat y) ?_ hy`. Establish `hk` using `key (k : ℤ) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)`. Simplify using `using hk`. Introduce `k1 _ φ`. Use `⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.transvection_mul_transvection_same (h := hab), neg_add_cancel, Matrix.transvection_zero]`. Rewrite using `[hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y (y.totalDegree + k + 1) (by omega)]`. Rewrite using `[Finset.sum_image (fun x _ z _ h => by exact_mod_cast h)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[LaurentPolynomial.T_pow]`.
-/
theorem propertySubmodule_dividedPower_stable (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : divPow R LL S a b k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  have key := laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y
    ((Finset.range (y.totalDegree + k + 1)).image (fun i : ℕ => (i : ℤ)))
    (fun z => divPow R LL S a b z.toNat y) ?_ hy
  · have hk := key (k : ℤ) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)
    simpa using hk
  intro k1 _ φ
  refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1),
    ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same (h := hab), neg_add_cancel, Matrix.transvection_zero]
  · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
      (y.totalDegree + k + 1) (by omega)]
    rw [Finset.sum_image (fun x _ z _ h => by exact_mod_cast h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [LaurentPolynomial.T_pow]

open Classical in

def weightEntryComponent (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ y.support.filter (fun m => wtS LL S m a = w), monomial m (y.coeff m)

/- English proof (translation)
Proceed by induction on `z using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [zpow_add_one, Units.val_mul, ih, ← LaurentPolynomial.T_add]`. Consider the case `pred i ih`. Rewrite using `[zpow_sub_one, Units.val_mul, ih, Units.inv_mk, ← LaurentPolynomial.T_add]`.

Both sides reduce to the same expression.
-/
private theorem laurent_T_unit_zpow_eq_T {k1 : Type} [CommRing k1] (z : ℤ) :
    (((⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
      by rw [← LaurentPolynomial.T_add]; simp⟩ : (LaurentPolynomial k1)ˣ) ^ z :
        (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1) = LaurentPolynomial.T z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, Units.inv_mk, ← LaurentPolynomial.T_add]
    rfl

/- English proof (translation)
Use `set K : Finset ℤ := y.support.image (fun m => wtS LL S m a) with hK`. Distinguish the cases in `hw : w ∈ K`. Use `swap`. Establish `h0 : weightEntryComponent LL S a w y = 0`. Unfold `weightEntryComponent`.

Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[Finset.mem_filter]`. Conclude with `absurd (Finset.mem_image.2 ⟨m, hm.1, hm.2⟩) hw`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`.

Use `laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y K (fun w => weightEntryComponent LL S a w y) ?_ hy w hw` and prove the remaining obligations. Introduce `k1 _ φ`. Set `u : (LaurentPolynomial k1)ˣ` to `⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩`. Set `D : Fin n → (LaurentPolynomial k1)ˣ` to `fun b => if b = a then u else 1`. Use `⟨Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using the standard rewrite rules. Establish `hmono : ∀ m : ι × Fin n →₀ ℕ, ∀ c : R, matrixSubst LL S (LaurentPolynomial.C.comp φ) (Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1)) (Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1)) (monomial m c) = C (Lau …`. Introduce `m c`. Rewrite using `[hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m c, C_mul_monomial]`.

Use `congr 1`. Establish `hp : (∏ b, D b ^ (wtS LL S m b) : (LaurentPolynomial k1)ˣ) = u ^ (wtS LL S m a)`. Rewrite using `[Finset.prod_eq_single a (fun b _ hb => by simp [D, hb]) (fun h => absurd (Finset.mem_univ a) h)]`. Simplify using `[D]`. Rewrite using `[hp, laurent_T_unit_zpow_eq_T, mul_comm]`.

Both sides reduce to the same expression. Use `conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[hmono]`. Unfold `weightEntryComponent`.

Repeatedly rewrite using `[map_sum, MvPolynomial.map_monomial, Finset.mul_sum]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := K) (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]`. Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[Finset.mem_filter]`. Rewrite using `[hm.2]`.

Both sides reduce to the same expression.
-/
theorem propertySubmodule_weightEntryComponent (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : weightEntryComponent LL S a w y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  set K : Finset ℤ := y.support.image (fun m => wtS LL S m a) with hK
  by_cases hw : w ∈ K
  swap
  · have h0 : weightEntryComponent LL S a w y = 0 := by
      unfold weightEntryComponent
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter] at hm
      exact absurd (Finset.mem_image.2 ⟨m, hm.1, hm.2⟩) hw
    rw [h0]
    exact Submodule.zero_mem _
  refine laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y K (fun w => weightEntryComponent LL S a w y) ?_ hy w hw
  intro k1 _ φ
  let u : (LaurentPolynomial k1)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (LaurentPolynomial k1)ˣ := fun b => if b = a then u else 1
  refine ⟨Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
    Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  ·
    have hmono : ∀ m : ι × Fin n →₀ ℕ, ∀ c : R,
        matrixSubst LL S (LaurentPolynomial.C.comp φ)
          (Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (monomial m c) = C (LaurentPolynomial.T (wtS LL S m a)) *
            monomial m (LaurentPolynomial.C (φ c)) := by
      intro m c
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m c, C_mul_monomial]
      congr 1
      have hp : (∏ b, D b ^ (wtS LL S m b) : (LaurentPolynomial k1)ˣ) = u ^ (wtS LL S m a) := by
        rw [Finset.prod_eq_single a (fun b _ hb => by simp [D, hb]) (fun h => absurd (Finset.mem_univ a) h)]
        simp [D]
      rw [hp, laurent_T_unit_zpow_eq_T, mul_comm]
      rfl
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    rw [map_sum]
    simp_rw [hmono]
    unfold weightEntryComponent
    simp_rw [map_sum, MvPolynomial.map_monomial, Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := K) (g := fun m => wtS LL S m a)
      (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [hm.2]
    rfl

/- English proof (translation)
Establish `hdec : binomPol R LL S a k y = ∑ w ∈ y.support.image (fun m => wtS LL S m a), (((Ring.choose w k : ℤ) : R)) • weightEntryComponent LL S a w y` using `by conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]`. Rewrite using `[map_sum]`. Unfold `weightEntryComponent`. Repeatedly rewrite using `[Finset.smul_sum]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a)) (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]`.

Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[Finset.mem_filter]`. Establish `h1 : monomial m (y.coeff m) = (y.coeff m) • (MvPolynomial.basisMonomials (ι × Fin n) R) m`. Rewrite using `[MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, hm.2]`.

Use `congr 1`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdec]`. Conclude with `Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (propertySubmodule_weightEntryComponent LL S j Pr hTo a w y hy)`.
-/
theorem propertySubmodule_binomial_stable (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : binomPol R LL S a k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical

  have hdec : binomPol R LL S a k y = ∑ w ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose w k : ℤ) : R)) • weightEntryComponent LL S a w y := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    rw [map_sum]
    unfold weightEntryComponent
    simp_rw [Finset.smul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
      (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have h1 : monomial m (y.coeff m) = (y.coeff m) • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials,
      MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, hm.2]
    congr 1
    simp only [smul_eq_mul]
    ring
  rw [hdec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (propertySubmodule_weightEntryComponent LL S j Pr hTo a w y hy)

/- English proof (translation)
Establish `hG0 : G ∈ weightEntryPropertySubmodule LL S j Pr`. Introduce `k1 _ φ g0 g0inv h m hm`. Conclude with `hG m (hSp R ι LL n S k1 φ g0 g0inv h G hm)`. Establish `hclos : ∀ u ∈ Submonoid.closure (polUZgens R LL S), ∀ x ∈ weightEntryPropertySubmodule LL S j Pr, u x ∈ weightEntryPropertySubmodule LL S j Pr`. Introduce `u hu`.

Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem u hu`. Break down `hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩` into its components or cases. Conclude with `fun x hx => propertySubmodule_dividedPower_stable LL S j Pr hT a b hab k x hx`. Conclude with `fun x hx => propertySubmodule_binomial_stable LL S j Pr hTo a k x hx`.

Consider the case `one => exact fun x hx => hx`. Consider the case `mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)`. Establish `hsub : polGenSub R LL S G ≤ weightEntryPropertySubmodule LL S j Pr`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, rfl⟩`.

Conclude with `hclos u hu G hG0`. Introduce and unpack `mu ⟨x, hx, hx0, hxw⟩`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.1 hx0`. Rewrite `hm` using `[← MvPolynomial.mem_support_iff]`. Establish `h1` using `hsub hx R (RingHom.id R) 1 1 (mul_one 1) m`.

Rewrite `h1` using `[matrixSubst_one, MvPolynomial.map_id]`. Rewrite using `[← hxw m hm]`. Conclude with `h1 hm`.
-/
theorem weights_property_of_generic_translate (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hSp : GenericMonomialsSpecialise) (G : MvPolynomial (ι × Fin n) R)
    (hG : ∀ m ∈ (genericTranslate LL S G).support, Pr (wtS LL S m j)) :
    ∀ mu ∈ polWts LL S (polGenSub R LL S G), Pr (mu j) := by
  classical

  have hG0 : G ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro k1 _ φ g0 g0inv h m hm
    exact hG m (hSp R ι LL n S k1 φ g0 g0inv h G hm)

  have hclos : ∀ u ∈ Submonoid.closure (polUZgens R LL S),
      ∀ x ∈ weightEntryPropertySubmodule LL S j Pr, u x ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact fun x hx => propertySubmodule_dividedPower_stable LL S j Pr hT a b hab k x hx
      · exact fun x hx => propertySubmodule_binomial_stable LL S j Pr hTo a k x hx
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  have hsub : polGenSub R LL S G ≤ weightEntryPropertySubmodule LL S j Pr := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, rfl⟩
    exact hclos u hu G hG0
  rintro mu ⟨x, hx, hx0, hxw⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hx0
  rw [← MvPolynomial.mem_support_iff] at hm
  have h1 := hsub hx R (RingHom.id R) 1 1 (mul_one 1) m
  rw [matrixSubst_one, MvPolynomial.map_id] at h1
  rw [← hxw m hm]
  exact h1 hm

end fwd

end Formalism.MainNotions.G.GLWeightTheory
