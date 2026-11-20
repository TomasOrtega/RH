import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (x : ∀ i, MonoidAlgebra k (G i)) : MonoidAlgebra k (∀ i, G i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tens_coeff (x : ∀ i, MonoidAlgebra k (G i)) (g : ∀ i, G i) :
    (tens x).coeff g = ∏ i, (x i).coeff (g i) := rfl

/- English proof (translation)
Rewrite using `[coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]`.
-/
theorem coeff_mul_fintype {Γ : Type} [Group Γ] [Fintype Γ] (x y : MonoidAlgebra k Γ) (g : Γ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

/- English proof (translation)
Establish `: ∀ i, Fintype (G i)` using `fun i => Fintype.ofFinite _`. Apply `MonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `g`. Rewrite using `[coeff_mul_fintype, tens_coeff]`. Simplify using `only [tens_coeff, coeff_mul_fintype, ← Finset.prod_mul_distrib]`.

Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Both sides reduce to the same expression.
-/
theorem tens_mul (x y : ∀ i, MonoidAlgebra k (G i)) : tens x * tens y = tens fun i => x i * y i := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype, tens_coeff]
  simp only [tens_coeff, coeff_mul_fintype, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/- English proof (translation)
Apply `MonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `g`. Rewrite using `[tens_coeff]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)`.
-/
theorem tens_eq_zero (x : ∀ i, MonoidAlgebra k (G i)) (i : I) (h : x i = 0) : tens x = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [tens_coeff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)

/- English proof (translation)
Establish `h1 : ∀ i, ∃ g : G i, (x i).coeff g ≠ 0` using `fun i => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h i (MonoidAlgebra.coeff_injective (Finsupp.ext hc))`. Use `choose g hg using h1`.

Introduce `h0`. Use `congrArg (fun z => z.coeff g) h0` as an intermediate fact. Simplify using `only [tens_coeff] at this`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun i _ => hg i) this`.
-/
theorem tens_ne_zero (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i, x i ≠ 0) : tens x ≠ 0 := by
  have h1 : ∀ i, ∃ g : G i, (x i).coeff g ≠ 0 := fun i => by
    by_contra hc
    push Not at hc
    exact h i (MonoidAlgebra.coeff_injective (Finsupp.ext hc))
  choose g hg using h1
  intro h0
  have := congrArg (fun z => z.coeff g) h0
  simp only [tens_coeff] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hg i) this

/- English proof (translation)
Apply `MonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `h`. Rewrite using `[tens_coeff, MonoidAlgebra.coeff_single_apply]`. Simplify using `only [MonoidAlgebra.coeff_single_apply]`. Distinguish the cases in `e : g = h`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg e]`. Take `⟨i, hi⟩` from `Function.ne_iff.mp e`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)`.
-/
theorem tens_single [DecidableEq I] (g : ∀ i, G i) : tens (fun i => (single (g i) 1 : MonoidAlgebra k (G i))) = single g 1 := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext h
  rw [tens_coeff, MonoidAlgebra.coeff_single_apply]
  simp only [MonoidAlgebra.coeff_single_apply]
  by_cases e : g = h
  · subst e; simp
  · rw [if_neg e]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [mul_add, add_mul, hx, hy]`. Consider the case `single g r`. Establish `e : (single g r : MonoidAlgebra k Γ) = r • single g 1` using `by rw [smul_single', mul_one]`.

Rewrite using `[e, mul_smul_comm, smul_mul_assoc, h]`.
-/
theorem commute_of_single {Γ : Type} [Group Γ] (z : MonoidAlgebra k Γ)
    (h : ∀ g : Γ, z * single g 1 = single g 1 * z) (a : MonoidAlgebra k Γ) : z * a = a * z := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | single g r =>
    have e : (single g r : MonoidAlgebra k Γ) = r • single g 1 := by rw [smul_single', mul_one]
    rw [e, mul_smul_comm, smul_mul_assoc, h]

/- English proof (translation)
Use `commute_of_single _ (fun g => ?_) a` and prove the remaining obligations. Rewrite using `[← tens_single, tens_mul, tens_mul]`. Conclude with `congrArg tens (funext fun i => h i _)`.
-/
theorem tens_central (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i a, x i * a = a * x i)
    (a : MonoidAlgebra k (∀ i, G i)) : tens x * a = a * tens x := by
  classical
  refine commute_of_single _ (fun g => ?_) a
  rw [← tens_single, tens_mul, tens_mul]
  exact congrArg tens (funext fun i => h i _)

variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)

open Classical in

def eSum : MonoidAlgebra k (∀ i, G i) := ∑ a : (∀ i, L i), if S a then tens (fun i => E i (a i)) else 0

variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)

include hcen in
/- English proof (translation)
Unfold `eSum`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `tens_central _ (fun i => hcen i _) a`.

Simplify using the standard rewrite rules.
-/
theorem eSum_central (a : MonoidAlgebra k (∀ i, G i)) : eSum E S * a = a * eSum E S := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact tens_central _ (fun i => hcen i _) a
  · simp

include hidem horth in
/- English proof (translation)
Rewrite using `[tens_mul]`. Use `split_ifs with e`. Substitute `e` using the available equality. Conclude with `congrArg tens (funext fun i => hidem i _)`. Take `⟨i, hi⟩` from `Function.ne_iff.mp e`.

Conclude with `tens_eq_zero _ i (horth i _ _ hi)`.
-/
theorem tens_mul_tens (a b : ∀ i, L i) : tens (fun i => E i (a i)) * tens (fun i => E i (b i)) =
    open Classical in if a = b then tens (fun i => E i (a i)) else 0 := by
  rw [tens_mul]
  split_ifs with e
  · subst e; exact congrArg tens (funext fun i => hidem i _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact tens_eq_zero _ i (horth i _ _ hi)

include hidem horth in
/- English proof (translation)
Unfold `eSum`. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single b]`. Use `split_ifs`. Rewrite using `[tens_mul_tens E hidem horth, if_pos rfl]`. Simplify using the standard rewrite rules.

Introduce `a _ hab split_ifs`. Rewrite using `[tens_mul_tens E hidem horth, if_neg hab]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
theorem eSum_mul_tens (b : ∀ i, L i) : eSum E S * tens (fun i => E i (b i)) =
    open Classical in if S b then tens (fun i => E i (b i)) else 0 := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.sum_eq_single b]
  · split_ifs
    · rw [tens_mul_tens E hidem horth, if_pos rfl]
    · simp
  · intro a _ hab
    split_ifs
    · rw [tens_mul_tens E hidem horth, if_neg hab]
    · simp
  · intro h; exact absurd (Finset.mem_univ b) h

include hidem horth in
/- English proof (translation)
Use `conv_lhs => rhs`. Unfold `eSum`. Rewrite using `[Finset.mul_sum]`. Unfold `eSum`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs with hb`. Use `eSum_mul_tens E S hidem horth b` as an intermediate fact. Rewrite `this` using `[if_pos hb]`. Conclude with `this`. Simplify using the standard rewrite rules.
-/
theorem eSum_idem : eSum E S * eSum E S = eSum E S := by
  classical
  conv_lhs => rhs; unfold eSum
  rw [Finset.mul_sum]
  unfold eSum
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · have := eSum_mul_tens E S hidem horth b
    rw [if_pos hb] at this
    exact this
  · simp

include hidem horth in
/- English proof (translation)
Introduce `h0`. Use `eSum_mul_tens E S hidem horth b` as an intermediate fact. Rewrite `this` using `[if_pos hb, h0, zero_mul]`. Conclude with `tens_ne_zero _ hne this.symm`.
-/
theorem eSum_ne_zero (b : ∀ i, L i) (hb : S b) (hne : ∀ i, E i (b i) ≠ 0) : eSum E S ≠ 0 := by
  intro h0
  have := eSum_mul_tens E S hidem horth b
  rw [if_pos hb, h0, zero_mul] at this
  exact tens_ne_zero _ hne this.symm

/- English proof (translation)
Unfold `eSum`. Rewrite using `[MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`. Both sides reduce to the same expression.

Both sides reduce to the same expression.
-/
theorem eSum_coeff (g : ∀ i, G i) : (eSum E S).coeff g =
    open Classical in ∑ a : (∀ i, L i), if S a then ∏ i, (E i (a i)).coeff (g i) else 0 := by
  classical
  unfold eSum
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rfl

/- English proof (translation)
Establish `hne : Ideal.span {1 - e} ≠ ⊤`. Introduce `h`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)`. Apply `h0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `_ : Field (Z ⧸ m)` to `Ideal.Quotient.field m`. Establish `: FiniteDimensional ℂ (Z ⧸ m)` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap (Ideal.Quotient.mkₐ_surjective ℂ m)`. Establish `hb` using `IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Z ⧸ m)`. Set `φ : ℂ ≃ₐ[ℂ] (Z ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId ℂ (Z ⧸ m)) hb`.

Use `⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mkₐ ℂ m e = 1`. Establish `: Ideal.Quotient.mk m (1 - e) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self _))`. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `this.symm`.

Use `show φ.symm (Ideal.Quotient.mkₐ ℂ m e) = 1`. Rewrite using `[h1, map_one]`.
-/
theorem exists_char_comm (Z : Type) [CommRing Z] [Algebra ℂ Z] [FiniteDimensional ℂ Z] (e : Z)
    (hi : e * e = e) (h0 : e ≠ 0) : ∃ ω : Z →ₐ[ℂ] ℂ, ω e = 1 := by
  have hne : Ideal.span {1 - e} ≠ ⊤ := by
    intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
    apply h0
    calc e = (c * (1 - e)) * e := by rw [hc, one_mul]
      _ = c * (e - e * e) := by ring
      _ = 0 := by rw [hi, sub_self, mul_zero]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (Z ⧸ m) := Ideal.Quotient.field m
  have : FiniteDimensional ℂ (Z ⧸ m) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℂ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Z ⧸ m)
  let φ : ℂ ≃ₐ[ℂ] (Z ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (Z ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩
  have h1 : Ideal.Quotient.mkₐ ℂ m e = 1 := by
    have : Ideal.Quotient.mk m (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  show φ.symm (Ideal.Quotient.mkₐ ℂ m e) = 1
  rw [h1, map_one]

/- English proof (translation)
Establish `hfd : FiniteDimensional ℂ (MonoidAlgebra ℂ Γ)` using `Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm`. Conclude with `exists_char_comm _ ⟨e, hc⟩ (Subtype.ext hi) (fun h => h0 (congrArg Subtype.val h))`.
-/
theorem exists_char {Γ : Type} [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ)
    (hc : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ Γ)) (hi : e * e = e) (h0 : e ≠ 0) :
    ∃ ω : Subalgebra.center ℂ (MonoidAlgebra ℂ Γ) →ₐ[ℂ] ℂ, ω ⟨e, hc⟩ = 1 := by
  have hfd : FiniteDimensional ℂ (MonoidAlgebra ℂ Γ) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  exact exists_char_comm _ ⟨e, hc⟩ (Subtype.ext hi) (fun h => h0 (congrArg Subtype.val h))

end Formalism.BasicNotions.Examples₂.NZ
