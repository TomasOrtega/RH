import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen

set_option autoImplicit false

noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `LinearMap.BilinForm.dualBasis_repr_apply (traceForm_nondegenerate ℚ E) b x j`. Rewrite `h` using `[Algebra.traceForm_apply]`. Conclude with `h`.
-/
private theorem repr_trDual_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E)
    (x : E) (j : ι) : (TB.trDual b).repr x j = Algebra.trace ℚ E (x * b j) := by
  have h := LinearMap.BilinForm.dualBasis_repr_apply
    (traceForm_nondegenerate ℚ E) b x j
  rw [Algebra.traceForm_apply] at h
  exact h

/- English proof (translation)
Establish `key : ∀ y : E, Algebra.trace ℚ E ((∑ i, TB.trDual b i * b i - 1) * y) = 0`. Introduce `y`. Rewrite using `[sub_mul, one_mul, map_sub, Algebra.trace_eq_matrix_trace (TB.trDual b) y, Matrix.trace, Finset.sum_mul, map_sum, sub_eq_zero]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_trDual_lemma]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ∑ i, TB.trDual b i * b i - 1 = 0`. Apply `(TB.trDual b).ext_elem` to reduce the goal to its premises. Introduce `j`.

Rewrite using `[repr_trDual_lemma, key, map_zero, Finsupp.zero_apply]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem sum_dual_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    ∑ i, TB.trDual b i * b i = 1 := by
  have key : ∀ y : E, Algebra.trace ℚ E ((∑ i, TB.trDual b i * b i - 1) * y) = 0 := by
    intro y
    rw [sub_mul, one_mul, map_sub, Algebra.trace_eq_matrix_trace (TB.trDual b) y, Matrix.trace,
      Finset.sum_mul, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_trDual_lemma]
    congr 1
    ring
  have h0 : ∑ i, TB.trDual b i * b i - 1 = 0 := by
    apply (TB.trDual b).ext_elem
    intro j
    rw [repr_trDual_lemma, key, map_zero, Finsupp.zero_apply]
  exact sub_eq_zero.1 h0

/- English proof (translation)
Use `conv_lhs => rw [← (TB.trDual b).sum_repr x]`. Simplify using `only [repr_trDual_lemma]`.
-/
theorem dual_expand {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (x : E) :
    x = ∑ j, Algebra.trace ℚ E (x * b j) • TB.trDual b j := by
  conv_lhs => rw [← (TB.trDual b).sum_repr x]
  simp only [repr_trDual_lemma]

/- English proof (translation)
Rewrite using `[← repr_trDual_lemma, Module.Basis.repr_self]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hki, Finsupp.single_apply, if_neg (Ne.symm hki)]`.
-/
theorem trace_dual_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (i k : ι) :
    Algebra.trace ℚ E (TB.trDual b i * b k) = if k = i then 1 else 0 := by
  rw [← repr_trDual_lemma, Module.Basis.repr_self]
  by_cases hki : k = i
  · subst hki; simp
  · rw [if_neg hki, Finsupp.single_apply, if_neg (Ne.symm hki)]

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `trace_dual_mul b i k`.
-/
theorem trace_mul_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (k i : ι) :
    Algebra.trace ℚ E (b k * TB.trDual b i) = if k = i then 1 else 0 := by
  rw [mul_comm]
  exact trace_dual_mul b i k

/- English proof (translation)
Use `set bZ := NumberField.RingOfIntegers.basis E with hbZdef`. Use `set bQ := NumberField.integralBasis E with hbQdef`. Establish `hbQ_apply : ∀ i, bQ i = algebraMap (𝓞 E) E (bZ i)` using `fun i => NumberField.integralBasis_apply E i`. Establish `hint_tr : ∀ x : 𝓞 E, ∃ g : ℤ, (g : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E x)`. Introduce `x`.

Establish `hx : IsIntegral ℤ (algebraMap (𝓞 E) E x)` using `(Algebra.IsIntegral.isIntegral x).algebraMap`. Establish `ht : IsIntegral ℤ (Algebra.trace ℚ E (algebraMap (𝓞 E) E x))` using `Algebra.isIntegral_trace hx`. Take `⟨g, hg⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 ht`. Conclude with `⟨g, by rw [← hg, eq_intCast]⟩`. Take `⟨G, hG⟩ : ∃ G : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℤ, ∀ i j, (G i j : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E (bZ i) * algebraMap (𝓞 E) E (bZ j))` from `⟨fun i j => (hint_tr (bZ i * bZ j)).choose, fun i j => by`.

Rewrite using `[← map_mul]`. Conclude with `(hint_tr (bZ i * bZ j)).choose_spec⟩`. Establish `hD : G.det = NumberField.discr E`. Establish `hm : (Int.castRingHom ℚ).mapMatrix G = Algebra.traceMatrix ℚ bQ`. Use extensionality with `i j`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hbQ_apply, hbQ_apply, ← hG]`. Simplify using the standard rewrite rules. Establish `h1 : ((G.det : ℤ) : ℚ) = (NumberField.discr E : ℚ)`. Rewrite using `[NumberField.coe_discr, ← hbQdef, Algebra.discr_def, ← hm, ← RingHom.map_det]`. Simplify using the standard rewrite rules.

Conclude with `h1` after adjusting the coercions. Take `⟨z, hzdef⟩ : ∃ z : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E, ∀ i, z i = ∑ j, G.adjugate i j • bZ j` from `⟨_, fun i => rfl⟩`. Establish `key : ∀ i k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = if i = k then (G.det : ℚ) else 0`. Introduce `i k`. Establish `h1 : (G.adjugate * G) i k = if i = k then G.det else 0`.

Rewrite using `[Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2 : Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = (((G.adjugate * G) i k : ℤ) : ℚ)`. Rewrite using `[hzdef, hbQ_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, map_sum, Int.cast_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_zsmul, smul_mul_assoc, map_zsmul, ← hG, zsmul_eq_mul, Int.cast_mul]`. Rewrite using `[h2, h1]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hz : ∀ i, algebraMap (𝓞 E) E (z i) = (G.det : E) * TB.trDual bQ i`. Introduce `i`.

Apply `(TB.trDual bQ).ext_elem` to reduce the goal to its premises. Introduce `j`. Rewrite using `[repr_trDual_lemma, repr_trDual_lemma, key i j, mul_assoc, ← zsmul_eq_mul, map_zsmul, trace_dual_mul bQ i j]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, if_neg (Ne.symm hij), smul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε⟩ : ∃ ε : ℤ, ε * G.det = (((NumberField.discr E).natAbs : ℕ) : ℤ) := by`. Rewrite using `[hD]`. Break down `Int.natAbs_eq (NumberField.discr E) with h | h` into its components or cases.

Conclude with `⟨1, by linarith⟩`. Conclude with `⟨-1, by linarith⟩`. Use `choose v hv using fun i => hint ((ε : 𝓞 E) * z i)`. Establish `hc : ∀ i, algebraMap V k (w * v i) = ψ (TB.trDual bQ i)`. Introduce `i`.

Establish `e1 : algebraMap (𝓞 E) E ((ε : 𝓞 E) * z i) = (((NumberField.discr E).natAbs : ℕ) : E) * TB.trDual bQ i`. Rewrite using `[map_mul, map_intCast, hz i, ← mul_assoc, ← Int.cast_mul, hε, Int.cast_natCast]`. Rewrite using `[map_mul, hv i, e1, map_mul, map_natCast, ← mul_assoc, hw, one_mul]`. Use `⟨bZ, fun i => w * v i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_one ψ, ← sum_dual_mul bQ, map_sum]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hc i, map_mul, hbQ_apply]`. Introduce `a`. Use `⟨fun i j => bZ.repr (a * bZ i) j, fun i => (bZ.sum_repr (a * bZ i)).symm, fun j => ?_⟩` and prove the remaining obligations. Establish `hm : ∀ i, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * TB.trDual bQ j * bQ i) = ((bZ.repr (a * bZ i) j : ℤ) : ℚ)`.

Introduce `i`. Establish `hs` using `bZ.sum_repr (a * bZ i)`. Rewrite using `[mul_comm (algebraMap (𝓞 E) E a), mul_assoc, hbQ_apply i, ← map_mul (algebraMap (𝓞 E) E)]`. Use `conv_lhs => rw [← hs]`. Rewrite using `[map_sum, Finset.mul_sum, map_sum]`.

Simplify using `only [map_zsmul, mul_smul_comm, ← hbQ_apply, trace_dual_mul]`. Simplify using the standard rewrite rules. Simplify using `only [hc]`. Rewrite using `[← map_mul ψ, dual_expand bQ (algebraMap (𝓞 E) E a * TB.trDual bQ j), map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[hm i, Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]`.
-/
theorem idem_data_basis {k V : Type} [Field k] [CommRing V] [Algebra V k] (ψ : E →+* k)
    (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E) (c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
        (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  set bZ := NumberField.RingOfIntegers.basis E with hbZdef
  set bQ := NumberField.integralBasis E with hbQdef
  have hbQ_apply : ∀ i, bQ i = algebraMap (𝓞 E) E (bZ i) := fun i => NumberField.integralBasis_apply E i
  have hint_tr : ∀ x : 𝓞 E, ∃ g : ℤ, (g : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E x) := by
    intro x
    have hx : IsIntegral ℤ (algebraMap (𝓞 E) E x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    have ht : IsIntegral ℤ (Algebra.trace ℚ E (algebraMap (𝓞 E) E x)) := Algebra.isIntegral_trace hx
    obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 ht
    exact ⟨g, by rw [← hg, eq_intCast]⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℤ,
      ∀ i j, (G i j : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E (bZ i) * algebraMap (𝓞 E) E (bZ j)) :=
    ⟨fun i j => (hint_tr (bZ i * bZ j)).choose, fun i j => by
      rw [← map_mul]; exact (hint_tr (bZ i * bZ j)).choose_spec⟩
  have hD : G.det = NumberField.discr E := by
    have hm : (Int.castRingHom ℚ).mapMatrix G = Algebra.traceMatrix ℚ bQ := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        hbQ_apply, hbQ_apply, ← hG]
      simp
    have h1 : ((G.det : ℤ) : ℚ) = (NumberField.discr E : ℚ) := by
      rw [NumberField.coe_discr, ← hbQdef, Algebra.discr_def, ← hm, ← RingHom.map_det]
      simp
    exact_mod_cast h1
  obtain ⟨z, hzdef⟩ : ∃ z : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E,
      ∀ i, z i = ∑ j, G.adjugate i j • bZ j := ⟨_, fun i => rfl⟩
  have key : ∀ i k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = if i = k then (G.det : ℚ) else 0 := by
    intro i k
    have h1 : (G.adjugate * G) i k = if i = k then G.det else 0 := by
      rw [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h2 : Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = (((G.adjugate * G) i k : ℤ) : ℚ) := by
      rw [hzdef, hbQ_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zsmul, smul_mul_assoc, map_zsmul, ← hG, zsmul_eq_mul, Int.cast_mul]
    rw [h2, h1]
    split_ifs <;> simp
  have hz : ∀ i, algebraMap (𝓞 E) E (z i) = (G.det : E) * TB.trDual bQ i := by
    intro i
    apply (TB.trDual bQ).ext_elem
    intro j
    rw [repr_trDual_lemma, repr_trDual_lemma, key i j, mul_assoc, ← zsmul_eq_mul, map_zsmul, trace_dual_mul bQ i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), smul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε * G.det = (((NumberField.discr E).natAbs : ℕ) : ℤ) := by
    rw [hD]
    rcases Int.natAbs_eq (NumberField.discr E) with h | h
    · exact ⟨1, by linarith⟩
    · exact ⟨-1, by linarith⟩
  choose v hv using fun i => hint ((ε : 𝓞 E) * z i)
  have hc : ∀ i, algebraMap V k (w * v i) = ψ (TB.trDual bQ i) := by
    intro i
    have e1 : algebraMap (𝓞 E) E ((ε : 𝓞 E) * z i) =
        (((NumberField.discr E).natAbs : ℕ) : E) * TB.trDual bQ i := by
      rw [map_mul, map_intCast, hz i, ← mul_assoc, ← Int.cast_mul, hε, Int.cast_natCast]
    rw [map_mul, hv i, e1, map_mul, map_natCast, ← mul_assoc, hw, one_mul]
  refine ⟨bZ, fun i => w * v i, ?_, ?_⟩
  · rw [← map_one ψ, ← sum_dual_mul bQ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc i, map_mul, hbQ_apply]
  · intro a
    refine ⟨fun i j => bZ.repr (a * bZ i) j, fun i => (bZ.sum_repr (a * bZ i)).symm, fun j => ?_⟩
    have hm : ∀ i, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * TB.trDual bQ j * bQ i) =
        ((bZ.repr (a * bZ i) j : ℤ) : ℚ) := by
      intro i
      have hs := bZ.sum_repr (a * bZ i)
      rw [mul_comm (algebraMap (𝓞 E) E a), mul_assoc, hbQ_apply i, ← map_mul (algebraMap (𝓞 E) E)]
      conv_lhs => rw [← hs]
      rw [map_sum, Finset.mul_sum, map_sum]
      simp only [map_zsmul, mul_smul_comm, ← hbQ_apply, trace_dual_mul]
      simp
    simp only [hc]
    rw [← map_mul ψ, dual_expand bQ (algebraMap (𝓞 E) E a * TB.trDual bQ j), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i, Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
