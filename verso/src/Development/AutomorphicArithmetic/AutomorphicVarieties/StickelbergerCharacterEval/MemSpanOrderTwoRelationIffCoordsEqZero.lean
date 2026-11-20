import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Rewrite using `[rel, MonoidAlgebra.intCast_def, mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_comm g c, mul_comm b, MonoidAlgebra.single_neg, sub_eq_add_neg, add_comm]`.
-/
private theorem single_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (g : Γ) (b : A) :
    MonoidAlgebra.single g b * rel A c ε =
      MonoidAlgebra.single g (-((ε : A) * b)) + MonoidAlgebra.single (c * g) b := by
  rw [rel, MonoidAlgebra.intCast_def, mul_sub, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_comm g c, mul_comm b,
    MonoidAlgebra.single_neg, sub_eq_add_neg, add_comm]

/- English proof (translation)
Proceed by induction on `u using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy`. Rewrite using `[add_mul]`. Simplify using `only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `single a b`. Rewrite using `[single_mul_rel]`. Establish `h : (c * a = g) ↔ (a = c * g)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Rewrite using `[← mul_assoc, h2, one_mul]`. Introduce and unpack `rfl`. Rewrite using `[← mul_assoc, h2, one_mul]`. Simplify using `only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
private theorem coeff_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] {c : Γ} (h2 : c * c = 1) (ε : ℤ)
    (u : MonoidAlgebra A Γ) (g : Γ) :
    (u * rel A c ε).coeff g = u.coeff (c * g) - (ε : A) * u.coeff g := by
  classical
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [add_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    ring
  | single a b =>
    rw [single_mul_rel]
    have h : (c * a = g) ↔ (a = c * g) := by
      constructor
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]
    split_ifs <;> ring

/- English proof (translation)
Introduce `A _ Γ _ _ c ε h2 hc hε w`. Use `letI := Fintype.ofFinite Γ`. Establish `hε' : (ε : A) * ε = 1`. Use `congrArg (fun n : ℤ => (n : A)) hε` as an intermediate fact. Simplify using `using this`.

Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Use function extensionality and compare the values at `i`. Simplify using `only [coord, coeff_mul_rel h2, Pi.zero_apply]`.

Rewrite using `[← mul_assoc c c, h2, one_mul]`. Take the linear combination `(-(u.coeff (c * rep i))) * hε'`. Introduce `hw`. Use `⟨∑ i : Qc c, MonoidAlgebra.single (rep i) (w.coeff (c * rep i)), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Simplify using `only [single_mul_rel]`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use `conv_rhs => rw [← Finsupp.univ_sum_single w.coeff]`. Rewrite using `[sum_rep h2 hc (fun g => Finsupp.single g (w.coeff g)), MonoidAlgebra.coeff_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Establish `hi` using `congrFun hw i`. Simplify using `only [coord, Pi.zero_apply] at hi`. Rewrite using `[MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, show -((ε : A) * w.coeff (c * rep i)) = w.coeff (rep i) by linear_combination -hi]`.
-/
theorem UpperTheory.V.B5.mem_span_orderTwoRelation_iff_coords_eq_zero :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ w : MonoidAlgebra A Γ, w ∈ Ideal.span {rel A c ε} ↔ coord c ε w = 0 := by
  intro A _ Γ _ _ c ε h2 hc hε w
  classical
  letI := Fintype.ofFinite Γ
  have hε' : (ε : A) * ε = 1 := by
    have := congrArg (fun n : ℤ => (n : A)) hε
    simpa using this
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨u, rfl⟩
    funext i
    simp only [coord, coeff_mul_rel h2, Pi.zero_apply]
    rw [← mul_assoc c c, h2, one_mul]
    linear_combination (-(u.coeff (c * rep i))) * hε'
  · intro hw
    refine ⟨∑ i : Qc c, MonoidAlgebra.single (rep i) (w.coeff (c * rep i)), ?_⟩
    rw [Finset.sum_mul]
    simp only [single_mul_rel]
    apply MonoidAlgebra.ext
    conv_rhs => rw [← Finsupp.univ_sum_single w.coeff]
    rw [sum_rep h2 hc (fun g => Finsupp.single g (w.coeff g)), MonoidAlgebra.coeff_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := congrFun hw i
    simp only [coord, Pi.zero_apply] at hi
    rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      show -((ε : A) * w.coeff (c * rep i)) = w.coeff (rep i) by linear_combination -hi]
