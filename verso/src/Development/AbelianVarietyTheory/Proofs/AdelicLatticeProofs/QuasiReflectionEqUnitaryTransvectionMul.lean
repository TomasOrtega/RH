import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Chain

/- English proof (translation)
Use `set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp`. Establish `hp0 : p ≠ 0`. Introduce `h`. Establish `h0` using `congrArg (fun q : Polynomial E => q.coeff 0) h`. Simplify using `[p] at h0`.

Conclude with `ha h0`. Rewrite using `[Filter.eventually_cofinite]`. Use `(Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h) (Finset.finite_toSet p.roots.toFinset)).subset ?_` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [Set.mem_setOf_eq, not_not] at ht`.

Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_roots hp0]`. Use `show Polynomial.eval (t : E) p = 0`. Simplify using `only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`. Take the linear combination `ht`.
-/
theorem eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by
  classical
  set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Polynomial E => q.coeff 0) h
    simp [p] at h0
    exact ha h0
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h)
    (Finset.finite_toSet p.roots.toFinset)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, not_not] at ht
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp0]
  show Polynomial.eval (t : E) p = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  linear_combination ht

variable {E : Type} [Field E] [CharZero E] {n : ℕ}

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_line_right (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use `filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx] with t ht`. Establish `hσ : σ (t : E) = t` using `map_ratCast σ t`. Rewrite using `[hf_line_left, hf_line_right, hf_line_right, hσ]`. Introduce `h`. Apply `ht` to reduce the goal to its premises.

Take the linear combination `h`.
-/
theorem eventually_aniso (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w : Fin n → E)
    (hx : hf σ G x x ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) (x + (t : E) • w) ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx]
    with t ht
  have hσ : σ (t : E) = t := map_ratCast σ t
  rw [hf_line_left, hf_line_right, hf_line_right, hσ]
  intro h
  apply ht
  linear_combination h

/- English proof (translation)
Use `filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht`. Rewrite using `[hf_line_left]`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Take the linear combination `h`.
-/
theorem eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht
  rw [hf_line_left]
  intro h
  apply ht
  linear_combination h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `@insert j S hj ih`.

Establish `hpair` using `eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)`. Establish `ha1` using `eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx`. Establish `ha2` using `eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx`. Use `filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3`. Take `⟨m, hm, hmeq⟩` from `hih`.

Establish `hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i = (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j`. Rewrite using `[Finset.sum_insert hj, smul_add, mul_smul]`. Normalize the expressions using the abelian group laws. Rewrite `h3`, the goal using `[hsplit]`. Take `⟨m', hm', hm'eq⟩` from `GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu`.

Conclude with `⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩`.
-/
theorem eventually_chain (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩

end GlobalTheory.UTrans.Chain

/- English proof (translation)
Introduce `E _ _ n σ G hG hiso x y u hx hy hu`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx (by simp [hf])`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hy (by simp [hf])`. Take `⟨z, hli, hzp⟩` from `GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0`. Establish `: Nonempty (Fin n)`. Assume the negation of the conclusion as `hne`.

Conclude with `hx0 (funext fun i => (hne ⟨i⟩).elim)`. Establish `hspan : Submodule.span E (Set.range z) = ⊤` using `hli.span_eq_top_of_card_eq_finrank (by simp)`. Establish `hmem : y - x ∈ Submodule.span E (Set.range z)`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Take `⟨l, hl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hmem`. Establish `hz : ∀ i, hf σ G (z i) (z i) = 0` using `fun i => (hzp i).1`. Establish `hxz : ∀ i, hf σ G x (z i) ≠ 0` using `fun i => (hzp i).2.1`. Establish `hyz : ∀ i, hf σ G y (z i) ≠ 0` using `fun i => (hzp i).2.2`. Establish `h1` using `GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ`.

Establish `h2` using `GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz Finset.univ`. Establish `hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite` using `(sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite`. Take `⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩` from `(h1.and (hT.eventually h2)).exists`. Establish `hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i = x + (t : E) • ∑ i ∈ Finset.univ, l i • z i`. Simplify using `only [neg_smul, Finset.sum_neg_distrib, hl]`.

Use `push_cast`. Use `module`. Establish `e2' : tv σ G y ((u - 1) / hf σ G y y) = m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i) ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i) (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i))`. Rewrite using `[← hv]`. Conclude with `e2`.

Take `⟨-, hdet, hinv, -⟩` from `(GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n σ G hG).2 m2 hm2`. Establish `hunit : IsUnit m2.det`. Rewrite using `[hdet]`. Conclude with `isUnit_one`. Use `⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]`.
-/
theorem GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ (x y : Fin n → E) (u : E), hf σ G x x ≠ 0 → hf σ G y y ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G y ((u - 1) / hf σ G y y) := by
  intro E _ _ n σ G hG hiso x y u hx hy hu
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [hf])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp [hf])
  obtain ⟨z, hli, hzp⟩ := GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0
  have : Nonempty (Fin n) := by
    by_contra hne
    exact hx0 (funext fun i => (hne ⟨i⟩).elim)
  have hspan : Submodule.span E (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : y - x ∈ Submodule.span E (Set.range z) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hz : ∀ i, hf σ G (z i) (z i) = 0 := fun i => (hzp i).1
  have hxz : ∀ i, hf σ G x (z i) ≠ 0 := fun i => (hzp i).2.1
  have hyz : ∀ i, hf σ G y (z i) ≠ 0 := fun i => (hzp i).2.2
  have h1 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ
  have h2 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz
    Finset.univ
  have hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite :=
    (sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite
  obtain ⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := (h1.and (hT.eventually h2)).exists
  have hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i =
      x + (t : E) • ∑ i ∈ Finset.univ, l i • z i := by
    simp only [neg_smul, Finset.sum_neg_distrib, hl]
    push_cast
    module
  have e2' : tv σ G y ((u - 1) / hf σ G y y) =
      m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
          (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)) := by
    rw [← hv]
    exact e2
  obtain ⟨-, hdet, hinv, -⟩ := (GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n σ G hG).2 m2 hm2
  have hunit : IsUnit m2.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩
  rw [e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]
