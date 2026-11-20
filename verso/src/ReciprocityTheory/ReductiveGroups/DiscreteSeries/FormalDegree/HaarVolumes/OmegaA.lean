import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Formalism.LocalRingCardinality.DataCD

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`.
-/
theorem jpq_N_zero_om : Formalism.UG.Jpq N 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Xᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * X = 0 ↔ _`. Rewrite using `[jpq_N_zero_om, Matrix.mul_one, Matrix.one_mul, eq_neg_iff_add_eq_zero]`.
-/
theorem mem_lieU_zero_iff_om (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) :
    X ∈ Formalism.BasicNotions.lieU N 0 ↔ Xᴴ = -X := by
  change Xᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * X = 0 ↔ _
  rw [jpq_N_zero_om, Matrix.mul_one, Matrix.one_mul, eq_neg_iff_add_eq_zero]

/- English proof (translation)
Simplify using `[skMat]`.
-/
theorem skMat_diag_om (x : UCo N) (a : Fin N) : skMat x a a = Complex.I * ((x.1 a : ℝ) : ℂ) := by
  simp [skMat]

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `l`. Use `show skMat x a b = x.2 ⟨(a, b), h⟩`. Simplify using `only [skMat, if_neg (ne_of_gt h), dif_pos h]`.
-/
theorem skMat_low_om (x : UCo N) (l : {ab : Fin N × Fin N // ab.2 < ab.1}) :
    skMat x l.1.1 l.1.2 = x.2 l := by
  obtain ⟨⟨a, b⟩, h⟩ := l
  show skMat x a b = x.2 ⟨(a, b), h⟩
  simp only [skMat, if_neg (ne_of_gt h), dif_pos h]

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `l`. Use `show skMat x b a = -star (x.2 ⟨(a, b), h⟩)`. Simplify using `only [skMat, if_neg (ne_of_lt h), dif_neg (not_lt.2 h.le), dif_pos h]`.
-/
theorem skMat_up_om (x : UCo N) (l : {ab : Fin N × Fin N // ab.2 < ab.1}) :
    skMat x l.1.2 l.1.1 = -star (x.2 l) := by
  obtain ⟨⟨a, b⟩, h⟩ := l
  show skMat x b a = -star (x.2 ⟨(a, b), h⟩)
  simp only [skMat, if_neg (ne_of_lt h), dif_neg (not_lt.2 h.le), dif_pos h]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.neg_apply]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Establish `h1 : skMat x b a = x.2 ⟨(b, a), h⟩` using `skMat_low_om x ⟨(b, a), h⟩`. Establish `h2 : skMat x a b = -star (x.2 ⟨(b, a), h⟩)` using `skMat_up_om x ⟨(b, a), h⟩`.

Rewrite using `[h1, h2, neg_neg]`. Rewrite using `[skMat_diag_om]`. Simplify using `[Complex.conj_ofReal]`. Establish `h1 : skMat x a b = x.2 ⟨(a, b), h⟩` using `skMat_low_om x ⟨(a, b), h⟩`. Establish `h2 : skMat x b a = -star (x.2 ⟨(a, b), h⟩)` using `skMat_up_om x ⟨(a, b), h⟩`.

Rewrite using `[h1, h2, star_neg, star_star]`.
-/
theorem skMat_conjTranspose_om (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : skMat x b a = x.2 ⟨(b, a), h⟩ := skMat_low_om x ⟨(b, a), h⟩
    have h2 : skMat x a b = -star (x.2 ⟨(b, a), h⟩) := skMat_up_om x ⟨(b, a), h⟩
    rw [h1, h2, neg_neg]
  · rw [skMat_diag_om]
    simp [Complex.conj_ofReal]
  · have h1 : skMat x a b = x.2 ⟨(a, b), h⟩ := skMat_low_om x ⟨(a, b), h⟩
    have h2 : skMat x b a = -star (x.2 ⟨(a, b), h⟩) := skMat_up_om x ⟨(a, b), h⟩
    rw [h1, h2, star_neg, star_star]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [skMat, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> simp [mul_add, star_add, neg_add] <;> ring`.
-/
theorem skMat_add_om (x y : UCo N) : skMat (x + y) = skMat x + skMat y := by
  ext a b
  simp only [skMat, Matrix.add_apply]
  split_ifs <;> simp [mul_add, star_add, neg_add] <;> ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [skMat, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp [Complex.real_smul] <;> ring`.
-/
theorem skMat_smul_om (c : ℝ) (x : UCo N) : skMat (c • x) = (c : ℂ) • skMat x := by
  ext a b
  simp only [skMat, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.real_smul] <;> ring

instance instBorelSpaceUnitaryLie : BorelSpace (Formalism.BasicNotions.lieU N 0) := ⟨rfl⟩

def complexifyLie : (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) →ₗ[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) where
  toFun ab := Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
    Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))
  map_add' x y := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring
  map_smul' c x := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨⟨A, hA⟩, ⟨B, hB⟩⟩ h`. Establish `hA'` using `(mem_lieU_zero_iff_om A).1 hA`. Establish `hB'` using `(mem_lieU_zero_iff_om B).1 hB`.

Establish `h0 : A + Complex.I • B = 0`. Use extensionality with `i j`. Conclude with `congrFun h (i, j)`. Establish `h1 : -A + Complex.I • B = 0`. Establish `e` using `congrArg Matrix.conjTranspose h0`.

Rewrite `e` using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA', hB', Matrix.conjTranspose_zero]`. Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`. Rewrite `e` using `[hI, neg_smul_neg]`. Conclude with `e`. Establish `hA0 : A = 0`.

Establish `e : (2 : ℂ) • A = 0`. Rewrite using `[two_smul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(smul_eq_zero.1 e).resolve_left two_ne_zero`. Establish `hB0 : B = 0`.

Establish `e : Complex.I • B = 0`. Rewrite `h0` using `[hA0, zero_add]`. Conclude with `h0`. Conclude with `(smul_eq_zero.1 e).resolve_left Complex.I_ne_zero`. Conclude with `Prod.ext (Subtype.ext hA0) (Subtype.ext hB0)`.

Introduce `Z`. Set `M : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ` to `Matrix.of fun i j => Z (i, j)`. Establish `hA : ((1 / 2 : ℝ) • (M - Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0`. Rewrite using `[mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, star_trivial, ← smul_neg, neg_sub]`. Establish `hs : star (-Complex.I / 2) = -(-Complex.I / 2)`.

Rewrite using `[star_div₀, star_neg]`. Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`. Rewrite using `[hI]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.

Establish `hB : ((-Complex.I / 2) • (M + Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0`. Rewrite using `[mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm Mᴴ M, hs, neg_smul]`. Use `⟨(⟨_, hA⟩, ⟨_, hB⟩), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ij`. Use `show ((1 / 2 : ℝ) • (M - Mᴴ) + Complex.I • ((-Complex.I / 2) • (M + Mᴴ))) ij.1 ij.2 = Z ij`.

Simplify using `only [M, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.real_smul, smul_eq_mul]`. Use `push_cast`. Take the linear combination `(-(Z ij + star (Z (ij.2, ij.1))) / 2) * Complex.I_sq`.
-/
theorem complexifyLie_bijective : Function.Bijective (complexifyLie (N := N)) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ h
    have hA' := (mem_lieU_zero_iff_om A).1 hA
    have hB' := (mem_lieU_zero_iff_om B).1 hB
    have h0 : A + Complex.I • B = 0 := by
      ext i j
      exact congrFun h (i, j)
    have h1 : -A + Complex.I • B = 0 := by
      have e := congrArg Matrix.conjTranspose h0
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA', hB', Matrix.conjTranspose_zero] at e
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      rw [hI, neg_smul_neg] at e
      exact e
    have hA0 : A = 0 := by
      have e : (2 : ℂ) • A = 0 := by
        rw [two_smul]
        calc A + A = (A + Complex.I • B) - (-A + Complex.I • B) := by abel
          _ = 0 := by rw [h0, h1, sub_zero]
      exact (smul_eq_zero.1 e).resolve_left two_ne_zero
    have hB0 : B = 0 := by
      have e : Complex.I • B = 0 := by
        rw [hA0, zero_add] at h0
        exact h0
      exact (smul_eq_zero.1 e).resolve_left Complex.I_ne_zero
    exact Prod.ext (Subtype.ext hA0) (Subtype.ext hB0)
  · intro Z
    let M : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ := Matrix.of fun i j => Z (i, j)
    have hA : ((1 / 2 : ℝ) • (M - Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0 := by
      rw [mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, star_trivial, ← smul_neg, neg_sub]
    have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      rw [star_div₀, star_neg]
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      rw [hI]
      norm_num
      ring
    have hB : ((-Complex.I / 2) • (M + Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0 := by
      rw [mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose, add_comm Mᴴ M, hs, neg_smul]
    refine ⟨(⟨_, hA⟩, ⟨_, hB⟩), ?_⟩
    funext ij
    show ((1 / 2 : ℝ) • (M - Mᴴ) + Complex.I • ((-Complex.I / 2) • (M + Mᴴ))) ij.1 ij.2 = Z ij
    simp only [M, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    linear_combination (-(Z ij + star (Z (ij.2, ij.1))) / 2) * Complex.I_sq

def complexifyLieEquiv : (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  haveI : FiniteDimensional ℝ (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) := Module.Finite.prod
  (LinearEquiv.ofBijective complexifyLie complexifyLie_bijective).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem complexifyLieEquiv_coe : ⇑(complexifyLieEquiv (N := N)) = fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
    Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
      Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) := rfl

instance instHaarUCoOm : (volume : Measure (UCo N)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

instance instHaarUCo2Om : (volume : Measure (UCo N × UCo N)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

/- English proof (translation)
Establish `hc : Continuous (fun X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ => Xᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * X)` using `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add (continuous_const.matrix_mul continuous_id)`. Conclude with `isClosed_eq hc continuous_const`.
-/
theorem isClosed_unitaryLie :
    IsClosed (Formalism.BasicNotions.lieU N 0 : Set (Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) := by
  have hc : Continuous (fun X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ =>
      Xᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * X) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)
  exact isClosed_eq hc continuous_const

instance instLocallyCompactSpaceUnitaryLie : LocallyCompactSpace (Formalism.BasicNotions.lieU N 0) :=
  haveI : LocallyCompactSpace (Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin N ⊕ Fin 0 → Fin N ⊕ Fin 0 → ℂ))
  isClosed_unitaryLie.isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instSecondCountableTopologyUnitaryLie : SecondCountableTopology (Formalism.BasicNotions.lieU N 0) :=
  haveI : SecondCountableTopology (Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N ⊕ Fin 0 → Fin N ⊕ Fin 0 → ℂ))
  Topology.IsInducing.subtypeVal.secondCountableTopology

/- English proof (translation)
Establish `hn : ∀ p : ℝ × ℝ, Complex.normSq (Complex.measurableEquivRealProd.symm p) = p.1 ^ 2 + p.2 ^ 2`. Introduce `p`. Use `show Complex.normSq ⟨p.1, p.2⟩ = _`. Rewrite using `[Complex.normSq_mk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e` using `(MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z : ℂ => Real.exp (-c * Complex.normSq z))`. Rewrite using `[← e]`. Establish `hrw : (fun p : ℝ × ℝ => Real.exp (-c * Complex.normSq (Complex.measurableEquivRealProd.symm p))) = fun p => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2)`. Use function extensionality and compare the values at `p`. Rewrite using `[hn p, ← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrw, Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2)), integral_gaussian, Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)]`.
-/
theorem integral_exp_neg_mul_normSq {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-c * Complex.normSq z) = Real.pi / c := by
  have hn : ∀ p : ℝ × ℝ, Complex.normSq (Complex.measurableEquivRealProd.symm p) = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    show Complex.normSq ⟨p.1, p.2⟩ = _
    rw [Complex.normSq_mk]
    ring
  have e := (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z : ℂ => Real.exp (-c * Complex.normSq z))
  rw [← e]
  have hrw : (fun p : ℝ × ℝ => Real.exp (-c * Complex.normSq (Complex.measurableEquivRealProd.symm p))) =
      fun p => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
    funext p
    rw [hn p, ← Real.exp_add]
    congr 1
    ring
  rw [hrw, Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2)),
    integral_gaussian, Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)]

abbrev LoOm (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

/- English proof (translation)
Establish `h3 : ∀ p : Fin N × Fin N, f p.1 p.2 = ((if p.1 = p.2 then f p.1 p.2 else 0) + (if p.2 < p.1 then f p.1 p.2 else 0)) + (if p.1 < p.2 then f p.1 p.2 else 0)`. Introduce `p`. Break down `lt_trichotomy p.1 p.2 with h | h | h` into its components or cases. Simplify using `[h, h.ne, not_lt.2 h.le]`. Simplify using `[h]`.

Simplify using `[h, h.ne', not_lt.2 h.le]`. Rewrite using `[Finset.sum_congr rfl (fun p _ => h3 p), Finset.sum_add_distrib, Finset.sum_add_distrib]`. Establish `hd : ∑ p : Fin N × Fin N, (if p.1 = p.2 then f p.1 p.2 else 0) = ∑ a, f a a`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `[Finset.sum_ite_eq]`.

Establish `hgen : ∀ g : Fin N → Fin N → ℝ, ∑ p : Fin N × Fin N, (if p.2 < p.1 then g p.1 p.2 else 0) = ∑ l : LoOm N, g l.1.1 l.1.2`. Introduce `g`. Rewrite using `[← Finset.sum_filter]`. Conclude with `Finset.sum_subtype _ (fun p => by simp) (fun p : Fin N × Fin N => g p.1 p.2)`. Establish `hl` using `hgen f`.

Establish `hu : ∑ p : Fin N × Fin N, (if p.1 < p.2 then f p.1 p.2 else 0) = ∑ l : LoOm N, f l.1.2 l.1.1`. Establish `e` using `hgen (fun a b => f b a)`. Apply the tactic sequence `try simp only at e`. Rewrite using `[← e]`. Conclude with `Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => rfl)`.

Rewrite using `[hd, hl, hu, add_assoc, ← Finset.sum_add_distrib]`.
-/
theorem sum_split_diag_low (f : Fin N → Fin N → ℝ) :
    ∑ p : Fin N × Fin N, f p.1 p.2 = ∑ a, f a a + ∑ l : LoOm N, (f l.1.1 l.1.2 + f l.1.2 l.1.1) := by
  classical
  have h3 : ∀ p : Fin N × Fin N, f p.1 p.2 = ((if p.1 = p.2 then f p.1 p.2 else 0) +
      (if p.2 < p.1 then f p.1 p.2 else 0)) + (if p.1 < p.2 then f p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun p _ => h3 p), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hd : ∑ p : Fin N × Fin N, (if p.1 = p.2 then f p.1 p.2 else 0) = ∑ a, f a a := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_ite_eq]
  have hgen : ∀ g : Fin N → Fin N → ℝ,
      ∑ p : Fin N × Fin N, (if p.2 < p.1 then g p.1 p.2 else 0) = ∑ l : LoOm N, g l.1.1 l.1.2 := by
    intro g
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p => by simp) (fun p : Fin N × Fin N => g p.1 p.2)
  have hl := hgen f
  have hu : ∑ p : Fin N × Fin N, (if p.1 < p.2 then f p.1 p.2 else 0) = ∑ l : LoOm N, f l.1.2 l.1.1 := by
    have e := hgen (fun a b => f b a)
    try simp only at e
    rw [← e]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => rfl)
  rw [hd, hl, hu, add_assoc, ← Finset.sum_add_distrib]

/- English proof (translation)
Establish `h` using `sum_split_diag_low (N := N) (fun _ _ => (1 : ℝ))`. Simplify using `at h`. Establish `e : ((N + 2 * Fintype.card (LoOm N) : ℕ) : ℝ) = ((N * N : ℕ) : ℝ)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `e` after adjusting the coercions.
-/
theorem card_LoOm : N + 2 * Fintype.card (LoOm N) = N * N := by
  have h := sum_split_diag_low (N := N) (fun _ _ => (1 : ℝ))
  simp at h
  have e : ((N + 2 * Fintype.card (LoOm N) : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast e

/- English proof (translation)
Establish `h` using `sum_split_diag_low (N := N) (fun a b => Complex.normSq (skMat x a b + Complex.I * skMat y a b))`. Apply the tactic sequence `try simp only at h`. Rewrite using `[h]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[skMat_diag_om, skMat_diag_om]`. Simplify using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[skMat_low_om x l, skMat_low_om y l, skMat_up_om x l, skMat_up_om y l]`.

Simplify using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_skMat_sum (x y : UCo N) :
    ∑ p : Fin N × Fin N, Complex.normSq (skMat x p.1 p.2 + Complex.I * skMat y p.1 p.2) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
  have h := sum_split_diag_low (N := N) (fun a b => Complex.normSq (skMat x a b + Complex.I * skMat y a b))
  try simp only at h
  rw [h]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [skMat_diag_om, skMat_diag_om]
    simp [Complex.normSq_apply]
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [skMat_low_om x l, skMat_low_om y l, skMat_up_om x l, skMat_up_om y l]
    simp [Complex.normSq_apply]
    ring

def gaussEOm (Z : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) : ℝ := ∏ p, Real.exp (-1 * Complex.normSq (Z p))

/- English proof (translation)
Unfold `gaussEOm`. Conclude with `continuous_finset_prod _ fun p _ => Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply p)))`.
-/
theorem continuous_gaussEOm : Continuous (gaussEOm (N := N)) := by
  unfold gaussEOm
  exact continuous_finset_prod _ fun p _ => Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply p)))

/- English proof (translation)
Unfold `gaussEOm`. Rewrite using `[MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ z => Real.exp (-1 * Complex.normSq z))]`. Simplify using `only [integral_exp_neg_mul_normSq one_pos, div_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, add_zero]`.
-/
theorem integral_gaussEOm : ∫ Z, gaussEOm (N := N) Z = Real.pi ^ (N * N) := by
  unfold gaussEOm
  rw [MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ z => Real.exp (-1 * Complex.normSq z))]
  simp only [integral_exp_neg_mul_normSq one_pos, div_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, add_zero]

def gaussUOm (x : UCo N) : ℝ :=
  (∏ a, Real.exp (-1 * x.1 a ^ 2)) * ∏ l, Real.exp (-2 * Complex.normSq (x.2 l))

/- English proof (translation)
Unfold `gaussUOm`. Rewrite using `[Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (fun y : Fin N → ℝ => ∏ a, Real.exp (-1 * y a ^ 2)) (fun z : LoOm N → ℂ => ∏ l, Real.exp (-2 * Complex.normSq (z l))), MeasureTheory.volume_pi, MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun …`. Simplify using `only [integral_gaussian, integral_exp_neg_mul_normSq two_pos, div_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem integral_gaussUOm : ∫ x, gaussUOm (N := N) x = Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N) := by
  unfold gaussUOm
  rw [Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun y : Fin N → ℝ => ∏ a, Real.exp (-1 * y a ^ 2))
      (fun z : LoOm N → ℂ => ∏ l, Real.exp (-2 * Complex.normSq (z l))),
    MeasureTheory.volume_pi, MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ (t : ℝ) => Real.exp (-1 * t ^ 2)),
    MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ (z : ℂ) => Real.exp (-2 * Complex.normSq z))]
  simp only [integral_gaussian, integral_exp_neg_mul_normSq two_pos, div_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `hK : Fintype.card (LoOm N) = N * (N - 1) / 2`. Establish `h` using `card_LoOm (N := N)`. Rewrite using `[Nat.mul_sub_one]`. Generalize the expression as in `N * N = M at h ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← hK]`. Establish `h` using `card_LoOm (N := N)`. Use `set K := Fintype.card (LoOm N)`. Establish `hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi` using `Real.sq_sqrt Real.pi_pos.le`. Establish `e1 : (Real.sqrt Real.pi ^ N) ^ 2 = Real.pi ^ N`.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hpi]`. Establish `e3 : Real.pi ^ (N * N) = Real.pi ^ N * Real.pi ^ K * Real.pi ^ K`. Rewrite using `[← h, pow_add, two_mul, pow_add, mul_assoc]`. Rewrite using `[mul_pow, e1, e3, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem omega_key_real : (2 : ℝ) ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2) *
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 = Real.pi ^ (N * N) := by
  have hK : Fintype.card (LoOm N) = N * (N - 1) / 2 := by
    have h := card_LoOm (N := N)
    rw [Nat.mul_sub_one]
    generalize N * N = M at h ⊢
    omega
  rw [← hK]
  have h := card_LoOm (N := N)
  set K := Fintype.card (LoOm N)
  have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have e1 : (Real.sqrt Real.pi ^ N) ^ 2 = Real.pi ^ N := by
    rw [← pow_mul, mul_comm, pow_mul, hpi]
  have e3 : Real.pi ^ (N * N) = Real.pi ^ N * Real.pi ^ K * Real.pi ^ K := by
    rw [← h, pow_add, two_mul, pow_add, mul_assoc]
  rw [mul_pow, e1, e3, div_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
