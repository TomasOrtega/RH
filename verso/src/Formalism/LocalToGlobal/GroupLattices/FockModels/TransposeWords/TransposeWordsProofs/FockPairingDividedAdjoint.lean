import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
import Formalism.GradedWeylDivisibility.FinalB

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

/- English proof (translation)
Unfold `fockR`. Apply `Finset.sum_subset h` to reduce the goal to its premises. Introduce `m _ hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, not_not]`. Rewrite using `[hm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma adj_fockR_of_subset {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ))
    (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

/- English proof (translation)
Rewrite using `[adj_fockR_of_subset _ _ (f.support ∪ f'.support) MvPolynomial.support_add, adj_fockR_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left, adj_fockR_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma adj_fockR_add_left {σ R : Type*} [CommRing R] (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [adj_fockR_of_subset _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    adj_fockR_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    adj_fockR_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Rewrite using `[adj_fockR_of_subset _ _ f.support MvPolynomial.support_smul, fockR, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma adj_fockR_smul_left {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := by
  rw [adj_fockR_of_subset _ _ f.support MvPolynomial.support_smul, fockR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[adj_fockR_of_subset f g (f.support ∪ g.support) Finset.subset_union_left, adj_fockR_of_subset g f (f.support ∪ g.support) Finset.subset_union_right]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma adj_fockR_symm {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) :
    fockR f g = fockR g f := by
  classical
  rw [adj_fockR_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    adj_fockR_of_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  apply Finset.sum_congr rfl
  intro m _
  ring

/- English proof (translation)
Rewrite using `[adj_fockR_symm, adj_fockR_add_left, adj_fockR_symm g, adj_fockR_symm g']`.
-/
lemma adj_fockR_add_right {σ R : Type*} [CommRing R] (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [adj_fockR_symm, adj_fockR_add_left, adj_fockR_symm g, adj_fockR_symm g']

/- English proof (translation)
Rewrite using `[adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]`.
-/
lemma adj_fockR_smul_right {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]

/- English proof (translation)
Rewrite using `[adj_fockR_of_subset _ _ f.support (MvPolynomial.support_map_subset _ _), fockR, map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`. Simplify using `[MvPolynomial.coeff_map]`.
-/
lemma adj_fockR_map {σ R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  rw [adj_fockR_of_subset _ _ f.support (MvPolynomial.support_map_subset _ _), fockR, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp [MvPolynomial.coeff_map]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma adj_fockR_rat {σ : Type*} (f g : MvPolynomial σ ℚ) : fockR f g = fockQ f g := rfl

/- English proof (translation)
Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Establish `e1` using `adj_fockR_map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) g`. Establish `e2` using `adj_fockR_map (Int.castRingHom ℚ) f (rowDiv ℤ b a k g)`. Simplify using `only [eq_intCast] at e1 e2`. Rewrite using `[← e1, ← e2, ← lclosedeq_rowDiv_map, ← lclosedeq_rowDiv_map, adj_fockR_rat, adj_fockR_rat]`.

Conclude with `fockQRowDivAdj r n a b k _ _`.
-/
lemma adj_rowDiv_int {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℤ) :
    fockR (rowDiv ℤ a b k f) g = fockR f (rowDiv ℤ b a k g) := by
  apply Int.cast_injective (α := ℚ)
  have e1 := adj_fockR_map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) g
  have e2 := adj_fockR_map (Int.castRingHom ℚ) f (rowDiv ℤ b a k g)
  simp only [eq_intCast] at e1 e2
  rw [← e1, ← e2, ← lclosedeq_rowDiv_map, ← lclosedeq_rowDiv_map, adj_fockR_rat, adj_fockR_rat]
  exact fockQRowDivAdj r n a b k _ _

/- English proof (translation)
Rewrite using `[MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`.
-/
lemma adj_monomial_eq {σ R : Type*} [CommRing R] (m : σ →₀ ℕ) (c : R) :
    (monomial m c : MvPolynomial σ R) = c • map (Int.castRingHom R) (monomial m (1 : ℤ)) := by
  rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/- English proof (translation)
Introduce `R _ r n a b k f g`. Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Proceed by induction on `g using MvPolynomial.induction_on' with`. Consider the case `monomial m' c'`.

Rewrite using `[adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul, lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]`. Rewrite using `[adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_map, adj_fockR_map, adj_rowDiv_int]`. Consider the case `add g1 g2 h1 h2`. Rewrite using `[rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]`. Consider the case `add f1 f2 h1 h2`.

Rewrite using `[rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]`.
-/
theorem fock_pairing_divided_adjoint : FockRRowDivAdj := by
  intro R _ r n a b k f g
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m' c' =>
      rw [adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul,
        lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]
      rw [adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right,
        adj_fockR_map, adj_fockR_map, adj_rowDiv_int]
    | add g1 g2 h1 h2 =>
      rw [rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]
  | add f1 f2 h1 h2 =>
    rw [rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma adj_applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) F = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w F) := by
  rfl

/- English proof (translation)
Unfold `applyWord`. Rewrite using `[List.foldr_append]`.
-/
lemma adj_applyWord_append {R : Type*} [CommRing R] {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (l1 ++ l2) F = applyWord R l1 (applyWord R l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

/- English proof (translation)
Simplify using `[transposeWord]`.
-/
lemma adj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

/- English proof (translation)
Introduce `R _ r n w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `F G`. Both sides reduce to the same expression.

Consider the case `cons x w ih`. Introduce `F G`. Rewrite using `[adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons, adj_applyWord_append]`. Both sides reduce to the same expression.
-/
theorem fock_pairing_word_adjoint : FockRWordAdj := by
  intro R _ r n w
  induction w with
  | nil =>
    intro F G
    rfl
  | cons x w ih =>
    intro F G
    rw [adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons,
      adj_applyWord_append]
    rfl

end Formalism.L2.G.Model.TS
