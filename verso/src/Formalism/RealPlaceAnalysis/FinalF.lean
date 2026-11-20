import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SatisfiesGlRelationsBilinearLeft
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `exp_indefinite_unitary_holds`.
-/
theorem expUJ : ExpUJ := exp_indefinite_unitary_holds
/- English proof (translation)
The claim follows from `indefinite_unitary_inv_closed`.
-/
theorem uJInv : UJInv := indefinite_unitary_inv_closed
/- English proof (translation)
The claim follows from `one_parameter_subgroup_holds`.
-/
theorem oneParam : OneParam := one_parameter_subgroup_holds
/- English proof (translation)
The claim follows from `maximal_compact_facts`.
-/
theorem kFacts : KFacts := maximal_compact_facts
/- English proof (translation)
The claim follows from `parabolic_character_holds`.
-/
theorem pChar : PChar := parabolic_character_holds
/- English proof (translation)
The claim follows from `polar_decomposition_holds`.
-/
theorem polar : Polar := polar_decomposition_holds
/- English proof (translation)
The claim follows from `hermitian_small_ball`.
-/
theorem hSBall : HSBall := hermitian_small_ball
/- English proof (translation)
The claim follows from `ball_open_holds`.
-/
theorem ballOpen : BallOpen := ball_open_holds
/- English proof (translation)
The claim follows from `isClosedEmbeddingMatrix`.
-/
theorem uJEmb : UJEmb := isClosedEmbeddingMatrix
/- English proof (translation)
The claim follows from `indefinite_unitary_unimodular`.
-/
theorem unimodular : Unimodular := indefinite_unitary_unimodular
/- English proof (translation)
Introduce `n ε`. Establish `hR` using `indefinite_unitary_unimodular n ε`. Use `haveI : (muG ε).IsMulRightInvariant := ⟨hR⟩`. Use `show (muG ε).inv = muG ε`. Establish `key : (muG ε).inv = MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) • muG ε`.

Conclude with `MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _`. Generalize the expression as in `MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) = c at key`. Establish `h2 : muG ε = (c * c) • muG ε`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : c = 1`.

Take `⟨K, hKc, hK1⟩` from `exists_compact_mem_nhds (1 : ↥(UJ ε))`. Establish `hpos : muG ε K ≠ 0` using `(MeasureTheory.Measure.measure_pos_of_mem_nhds (muG ε) hK1).ne'`. Establish `hfin : muG ε K ≠ ⊤` using `hKc.measure_lt_top.ne`. Establish `hK : muG ε K = ((c * c : NNReal) : ENNReal) * muG ε K` using `by conv_lhs => rw [h2]`. Both sides reduce to the same expression.

Establish `h3 : ((c * c : NNReal) : ENNReal) = 1`. Establish `h4 : ((c * c : NNReal) : ENNReal) * muG ε K = 1 * muG ε K`. Rewrite using `[one_mul]`. Conclude with `hK.symm`. Conclude with `(ENNReal.mul_left_inj hpos hfin).mp h4`.

Establish `h5 : (c : ℝ) * c = 1` using `by exact_mod_cast h3`. Establish `h6 : (0 : ℝ) ≤ c` using `c.2`. Apply `NNReal.eq` to reduce the goal to its premises. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[key, hc1, one_smul]`.
-/
theorem invInvariant : InvInvariant := by
  intro n ε
  have hR := indefinite_unitary_unimodular n ε
  haveI : (muG ε).IsMulRightInvariant := ⟨hR⟩
  show (muG ε).inv = muG ε
  have key : (muG ε).inv =
      MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) • muG ε := by
    exact MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  generalize MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) = c at key
  have h2 : muG ε = (c * c) • muG ε := by
    calc muG ε = (muG ε).inv.inv := (MeasureTheory.Measure.inv_inv _).symm
      _ = (c • muG ε).inv := by rw [← key]
      _ = c • (muG ε).inv := MeasureTheory.Measure.map_smul _ _ _
      _ = (c * c) • muG ε := by rw [key, smul_smul]
  have hc1 : c = 1 := by
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : ↥(UJ ε))
    have hpos : muG ε K ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds (muG ε) hK1).ne'
    have hfin : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
    have hK : muG ε K = ((c * c : NNReal) : ENNReal) * muG ε K := by
      conv_lhs => rw [h2]
      rfl
    have h3 : ((c * c : NNReal) : ENNReal) = 1 := by
      have h4 : ((c * c : NNReal) : ENNReal) * muG ε K = 1 * muG ε K := by
        rw [one_mul]
        exact hK.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h4
    have h5 : (c : ℝ) * c = 1 := by exact_mod_cast h3
    have h6 : (0 : ℝ) ≤ c := c.2
    apply NNReal.eq
    push_cast
    nlinarith
  rw [key, hc1, one_smul]
/- English proof (translation)
The claim follows from `ball_finite_measure_holds`.
-/
theorem ballFinite : BallFinite := ball_finite_measure_holds
/- English proof (translation)
The claim follows from `volume_growth`.
-/
theorem volGrowth : VolGrowth := volume_growth
/- English proof (translation)
The claim follows from `complex_parts_mem_lie_algebra_holds`.
-/
theorem cpartMem : CpartMem := complex_parts_mem_lie_algebra_holds
/- English proof (translation)
The claim follows from `right_derivative_extends`.
-/
theorem rdExt : RdExt := right_derivative_extends
/- English proof (translation)
The claim follows from `right_derivative_left_invariant`.
-/
theorem rdLeft : RdLeft := right_derivative_left_invariant
/- English proof (translation)
The claim follows from `right_derivative_linear`.
-/
theorem rdLin : RdLin := right_derivative_linear
/- English proof (translation)
The claim follows from `rdSmooth_of right_derivative_extends`.
-/
theorem rdSmooth : RdSmooth := rdSmooth_of right_derivative_extends
/- English proof (translation)
The claim follows from `eabGl_of complex_parts_mem_lie_algebra_holds (rdLin_of right_derivative_extends) (rdBracket_of right_derivative_extends (rdSmooth_of right_derivative_extends)) (rdSmooth_of right_derivative_extends)`.
-/
theorem eabGl : EabGl := eabGl_of complex_parts_mem_lie_algebra_holds (rdLin_of right_derivative_extends)
  (rdBracket_of right_derivative_extends (rdSmooth_of right_derivative_extends)) (rdSmooth_of right_derivative_extends)
end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `canonicalCommutation_holds`.
-/
theorem cCR : CCR := canonicalCommutation_holds
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_mul_commutator_eq_of_commutator_relations {A : Type*} [Ring A] (x y z w d1 d2 : A) (e1 : y * z = z * y + d1)
    (e2 : w * x = x * w + d2) (hxz : x * z = z * x) (hyw : y * w = w * y) :
    x * y * (z * w) - z * w * (x * y) = x * d1 * w - z * d2 * y := by
  calc x * y * (z * w) - z * w * (x * y) = x * (y * z) * w - z * (w * x) * y := by noncomm_ring
    _ = x * (z * y + d1) * w - z * (x * w + d2) * y := by rw [e1, e2]
    _ = (x * z) * (y * w) + x * d1 * w - ((z * x) * (w * y) + z * d2 * y) := by noncomm_ring
    _ = x * d1 * w - z * d2 * y := by rw [hxz, hyw]; abel

/- English proof (translation)
Introduce `i j k l`. Use `show (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) = (if j = k then ∑ a, p i a * q l a else 0) - (if l = i then ∑ a, p k a * q j a else 0)`. Establish `h1 : (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) = ∑ a, ∑ c, (p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a))`. Simplify using `only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `hterm : ∀ a c, p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a) = (if j = k ∧ a = c then p i a * q l c else 0) - (if l = i ∧ c = a then p k c * q j a else 0)`. Introduce `a c`. Rewrite using `[mul_mul_commutator_eq_of_commutator_relations (p i a) (q j a) (p k c) (q l c) _ _ (sub_eq_iff_eq_add'.mp (hqp j k a c)) (sub_eq_iff_eq_add'.mp (hqp l i c a)) (hpp i k a c) (hqq j l a c)]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1]`.

Simplify using `only [hterm, Finset.sum_sub_distrib]`. Apply the tactic sequence `by_cases hjk : j = k <;> by_cases hli : l = i <;> simp [hjk, hli]`.
-/
private theorem glRel_sum_p_mul_q_of_canonical_relations {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a)
    (hpp : ∀ i j a b, p i a * p j b = p j b * p i a) :
    GlRel (fun i j => ∑ a, p i a * q j a) := by
  intro i j k l
  show (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) =
    (if j = k then ∑ a, p i a * q l a else 0) - (if l = i then ∑ a, p k a * q j a else 0)
  have h1 : (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) =
      ∑ a, ∑ c, (p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hterm : ∀ a c, p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a) =
      (if j = k ∧ a = c then p i a * q l c else 0) - (if l = i ∧ c = a then p k c * q j a else 0) := by
    intro a c
    rw [mul_mul_commutator_eq_of_commutator_relations (p i a) (q j a) (p k c) (q l c) _ _ (sub_eq_iff_eq_add'.mp (hqp j k a c))
      (sub_eq_iff_eq_add'.mp (hqp l i c a)) (hpp i k a c) (hqq j l a c)]
    split_ifs <;> simp
  rw [h1]
  simp only [hterm, Finset.sum_sub_distrib]
  by_cases hjk : j = k <;> by_cases hli : l = i <;> simp [hjk, hli]

/- English proof (translation)
Introduce `a b c d`. Use `show -F b a * -F d c - -F d c * -F b a = (if b = c then -F d a else 0) - (if d = a then -F b c else 0)`. Establish `h'` using `h b a d c`. Rewrite using `[neg_mul_neg, neg_mul_neg, h']`. Establish `e1 : (a = d) ↔ (d = a)` using `eq_comm`.

Establish `e2 : (c = b) ↔ (b = c)` using `eq_comm`. Rewrite using `[if_congr e1 rfl rfl, if_congr e2 rfl rfl]`. Apply the tactic sequence `split_ifs <;> abel`.
-/
private theorem glRel_neg_transpose {A : Type*} [Ring A] {n : ℕ} (F : Fin n → Fin n → A) (h : GlRel F) :
    GlRel (fun a b => -F b a) := by
  intro a b c d
  show -F b a * -F d c - -F d c * -F b a = (if b = c then -F d a else 0) - (if d = a then -F b c else 0)
  have h' := h b a d c
  rw [neg_mul_neg, neg_mul_neg, h']
  have e1 : (a = d) ↔ (d = a) := eq_comm
  have e2 : (c = b) ↔ (b = c) := eq_comm
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  split_ifs <;> abel

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Establish `h1 : (∑ c, p i c * q j c) * (∑ k, p k b * q k a) - (∑ k, p k b * q k a) * (∑ c, p i c * q j c) = ∑ c, ∑ k, (p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c))`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun k c => p k b * q k a * (p i c * q j c))]`. Simplify using `only [Finset.sum_sub_distrib]`. Establish `hterm : ∀ c k, p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c) = (if j = k ∧ c = b then p i c * q k a else 0) - (if k = i ∧ a = c then p k b * q j c else 0)`.

Introduce `c k`. Rewrite using `[mul_mul_commutator_eq_of_commutator_relations (p i c) (q j c) (p k b) (q k a) _ _ (sub_eq_iff_eq_add'.mp (hqp j k c b)) (sub_eq_iff_eq_add'.mp (hqp k i a c)) (hpp i k c b) (hqq j k c a)]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1]`. Simplify using `only [hterm, Finset.sum_sub_distrib, ite_and]`.

Simplify using the standard rewrite rules.
-/
private theorem sum_pq_commute_sum_pq_of_canonical_relations {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a)
    (hpp : ∀ i j a b, p i a * p j b = p j b * p i a) (i j : Fin M) (a b : Fin N) :
    (∑ c, p i c * q j c) * (∑ k, p k b * q k a) = (∑ k, p k b * q k a) * (∑ c, p i c * q j c) := by
  rw [← sub_eq_zero]
  have h1 : (∑ c, p i c * q j c) * (∑ k, p k b * q k a) - (∑ k, p k b * q k a) * (∑ c, p i c * q j c) =
      ∑ c, ∑ k, (p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun k c => p k b * q k a * (p i c * q j c))]
    simp only [Finset.sum_sub_distrib]
  have hterm : ∀ c k, p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c) =
      (if j = k ∧ c = b then p i c * q k a else 0) - (if k = i ∧ a = c then p k b * q j c else 0) := by
    intro c k
    rw [mul_mul_commutator_eq_of_commutator_relations (p i c) (q j c) (p k b) (q k a) _ _ (sub_eq_iff_eq_add'.mp (hqp j k c b))
      (sub_eq_iff_eq_add'.mp (hqp k i a c)) (hpp i k c b) (hqq j k c a)]
    split_ifs <;> simp
  rw [h1]
  simp only [hterm, Finset.sum_sub_distrib, ite_and]
  simp

/- English proof (translation)
Introduce `M n' ε ε'`. Establish `hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a = if i = j ∧ a = b then 1 else 0` using `fun i j a b => (cCR M n' ε ε' i j a b).1`. Establish `hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a` using `fun i j a b => (cCR M n' ε ε' i j a b).2.1`. Establish `hpp : ∀ i j a b, bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a` using `fun i j a b => (cCR M n' ε ε' i j a b).2.2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `glRel_sum_p_mul_q_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp`. Establish `hqp' : ∀ x y i k, bop ε ε' i x * bpl ε ε' k y - bpl ε ε' k y * bop ε ε' i x = if x = y ∧ i = k then 1 else 0`. Introduce `x y i k`. Rewrite using `[hqp i k x y]`. Conclude with `if_congr and_comm rfl rfl`.

Conclude with `glRel_neg_transpose _ (glRel_sum_p_mul_q_of_canonical_relations (fun a i => bpl ε ε' i a) (fun a i => bop ε ε' i a) hqp' (fun x y i k => hqq i k x y) (fun x y i k => hpp i k x y))`. Introduce `i j a b show (∑ c, bpl ε ε' i c * bop ε ε' j c) * (-∑ k, bpl ε ε' k b * bop ε ε' k a) = (-∑ k, bpl ε ε' k b * bop ε ε' k a) * (∑ c, bpl ε ε' i c * bop ε ε' j c)`. Rewrite using `[mul_neg, neg_mul, sum_pq_commute_sum_pq_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp i j a b]`.
-/
theorem fockPairGl : FockPairGl := by
  intro M n' ε ε'
  have hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (cCR M n' ε ε' i j a b).1
  have hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.1
  have hpp : ∀ i j a b, bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.2
  refine ⟨?_, ?_, ?_⟩
  · exact glRel_sum_p_mul_q_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp
  · have hqp' : ∀ x y i k, bop ε ε' i x * bpl ε ε' k y - bpl ε ε' k y * bop ε ε' i x =
        if x = y ∧ i = k then 1 else 0 := by
      intro x y i k
      rw [hqp i k x y]
      exact if_congr and_comm rfl rfl
    exact glRel_neg_transpose _ (glRel_sum_p_mul_q_of_canonical_relations (fun a i => bpl ε ε' i a) (fun a i => bop ε ε' i a)
      hqp' (fun x y i k => hqq i k x y) (fun x y i k => hpp i k x y))
  · intro i j a b
    show (∑ c, bpl ε ε' i c * bop ε ε' j c) * (-∑ k, bpl ε ε' k b * bop ε ε' k a) =
      (-∑ k, bpl ε ε' k b * bop ε ε' k a) * (∑ c, bpl ε ε' i c * bop ε ε' j c)
    rw [mul_neg, neg_mul, sum_pq_commute_sum_pq_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp i j a b]
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sum_four_comm_unipotent_moves {A : Type*} [AddCommMonoid A] {α β γ δ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] (f : α → β → γ → δ → A) :
    ∑ c, ∑ a, ∑ i, ∑ j, f c a i j = ∑ i, ∑ j, ∑ a, ∑ c, f c a i j := by
  calc ∑ c, ∑ a, ∑ i, ∑ j, f c a i j = ∑ c, ∑ i, ∑ a, ∑ j, f c a i j :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, ∑ a, f c a i j :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ j, ∑ a, f c a i j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ c, ∑ a, f c a i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ c, f c a i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

/- English proof (translation)
Establish `hE : Cas (fun i j => ∑ a, p i a * q j a) = (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + M • (∑ i, ∑ a, p i a * q i a)`. Establish `t : ∀ i j a c, p i a * q j a * (p j c * q i c) = p i a * p j c * (q j a * q i c) + (if a = c then p i a * q i c else 0)`. Introduce `i j a c`. Establish `e : q j a * p j c = p j c * q j a + (if a = c then 1 else 0)`. Establish `h0` using `hqp j j a c`.

Simplify using `only [true_and] at h0`. Conclude with `sub_eq_iff_eq_add'.mp h0`. Combine the equalities or inequalities in the displayed calculation. Use `show ∑ i, ∑ j, (∑ a, p i a * q j a) * (∑ c, p j c * q i c) = _`. Simplify using `only [Finset.sum_mul_sum, t, Finset.sum_add_distrib]`.

Use `congr 1`. Simplify using `[Finset.smul_sum]`. Establish `hE' : Cas (fun a b => -∑ i, p i b * q i a) = (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + N • (∑ i, ∑ a, p i a * q i a)`. Establish `t : ∀ a b i k, p i b * q i a * (p k a * q k b) = p i b * p k a * (q i a * q k b) + (if i = k then p i b * q k b else 0)`. Introduce `a b i k`.

Establish `e : q i a * p k a = p k a * q i a + (if i = k then 1 else 0)`. Establish `h0` using `hqp i k a a`. Simplify using `only [and_true] at h0`. Conclude with `sub_eq_iff_eq_add'.mp h0`. Combine the equalities or inequalities in the displayed calculation.

Use `show ∑ a, ∑ b, (-∑ i, p i b * q i a) * (-∑ k, p k a * q k b) = _`. Simplify using `only [neg_mul_neg, Finset.sum_mul_sum, t, Finset.sum_add_distrib]`. Use `congr 1`. Use `(sum_four_comm_unipotent_moves (fun c a i j => p i a * p j c * (q i c * q j a))).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => congrArg (p i a * p j c * ·) (hqq i j c a)`.

Simplify using `[Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[hE, hE', add_sub_cancel_right, add_sub_cancel_right]`.
-/
private theorem cas_sum_pq_sub_smul_eq_cas_neg_sum_sub_smul {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a) :
    Cas (fun i j => ∑ a, p i a * q j a) - M • (∑ i, ∑ a, p i a * q i a) =
      Cas (fun a b => -∑ i, p i b * q i a) - N • (∑ i, ∑ a, p i a * q i a) := by
  have hE : Cas (fun i j => ∑ a, p i a * q j a) =
      (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + M • (∑ i, ∑ a, p i a * q i a) := by
    have t : ∀ i j a c, p i a * q j a * (p j c * q i c) =
        p i a * p j c * (q j a * q i c) + (if a = c then p i a * q i c else 0) := by
      intro i j a c
      have e : q j a * p j c = p j c * q j a + (if a = c then 1 else 0) := by
        have h0 := hqp j j a c
        simp only [true_and] at h0
        exact sub_eq_iff_eq_add'.mp h0
      calc p i a * q j a * (p j c * q i c) = p i a * (q j a * p j c) * q i c := by noncomm_ring
        _ = _ := by rw [e]; split_ifs <;> noncomm_ring
    show ∑ i, ∑ j, (∑ a, p i a * q j a) * (∑ c, p j c * q i c) = _
    simp only [Finset.sum_mul_sum, t, Finset.sum_add_distrib]
    congr 1
    simp [Finset.smul_sum]
  have hE' : Cas (fun a b => -∑ i, p i b * q i a) =
      (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + N • (∑ i, ∑ a, p i a * q i a) := by
    have t : ∀ a b i k, p i b * q i a * (p k a * q k b) =
        p i b * p k a * (q i a * q k b) + (if i = k then p i b * q k b else 0) := by
      intro a b i k
      have e : q i a * p k a = p k a * q i a + (if i = k then 1 else 0) := by
        have h0 := hqp i k a a
        simp only [and_true] at h0
        exact sub_eq_iff_eq_add'.mp h0
      calc p i b * q i a * (p k a * q k b) = p i b * (q i a * p k a) * q k b := by noncomm_ring
        _ = _ := by rw [e]; split_ifs <;> noncomm_ring
    show ∑ a, ∑ b, (-∑ i, p i b * q i a) * (-∑ k, p k a * q k b) = _
    simp only [neg_mul_neg, Finset.sum_mul_sum, t, Finset.sum_add_distrib]
    congr 1
    · refine (sum_four_comm_unipotent_moves (fun c a i j => p i a * p j c * (q i c * q j a))).trans ?_
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
          congrArg (p i a * p j c * ·) (hqq i j c a)
    · simp [Finset.smul_sum]
      rw [Finset.sum_comm]
  rw [hE, hE', add_sub_cancel_right, add_sub_cancel_right]

/- English proof (translation)
Introduce `M n' ε ε'`. Establish `hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a = if i = j ∧ a = b then 1 else 0` using `fun i j a b => (cCR M n' ε ε' i j a b).1`. Establish `hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a` using `fun i j a b => (cCR M n' ε ε' i j a b).2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ∑ i, ∑ a, bpl ε ε' i a * bop ε ε' i a = -∑ a, -∑ i, bpl ε ε' i a * bop ε ε' i a`.

Rewrite using `[Finset.sum_neg_distrib, neg_neg, Finset.sum_comm]`. Rewrite using `[Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `cas_sum_pq_sub_smul_eq_cas_neg_sum_sub_smul (bpl ε ε') (bop ε ε') hqp hqq`.
-/
theorem fockCas : FockCas := by
  intro M n' ε ε'
  have hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (cCR M n' ε ε' i j a b).1
  have hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.1
  refine ⟨?_, ?_⟩
  · show ∑ i, ∑ a, bpl ε ε' i a * bop ε ε' i a = -∑ a, -∑ i, bpl ε ε' i a * bop ε ε' i a
    rw [Finset.sum_neg_distrib, neg_neg, Finset.sum_comm]
  · rw [Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]
    exact cas_sum_pq_sub_smul_eq_cas_neg_sum_sub_smul (bpl ε ε') (bop ε ε') hqp hqq
/- English proof (translation)
The claim follows from `fischerAdjointness_holds`.
-/
theorem fockAdj : FockAdj := fischerAdjointness_holds
end Formalism.REAL
