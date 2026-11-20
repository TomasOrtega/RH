import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace BranchOffHypersurface

/- English proof (translation)
Establish `h : J ⊔ Ideal.span {b} ≤ RingHom.ker (eval x)`. Use `sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `RingHom.mem_ker.2 hb`. Conclude with `fun q hq => RingHom.mem_ker.1 (h hq)`.
-/
theorem eval_eq_zero_of_mem_sup {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {b : MvPolynomial (Fin n) ℂ}
    {x : Fin n → ℂ} (hx : x ∈ zeroSetIn J) (hb : eval x b = 0) :
    ∀ q ∈ J ⊔ Ideal.span {b}, eval x q = 0 := by
  have h : J ⊔ Ideal.span {b} ≤ RingHom.ker (eval x) := by
    refine sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.2 hb
  exact fun q hq => RingHom.mem_ker.1 (h hq)

/- English proof (translation)
Establish `hle : Q ≤ Q ⊔ Ideal.span {x}` using `le_sup_left`. Establish `hx : x ∈ Q ⊔ Ideal.span {x}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)`. Establish `hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Use `le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)` and prove the remaining obligations. Use `gcongr`.

Use `ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))` and prove the remaining obligations. Introduce `y hy`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[map_mul]`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Simplify using `only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]`.
-/
theorem ringKrullDim_sup_span_add_one_le {R : Type*} [CommRing R] {Q : Ideal R} [Q.IsPrime] {x : R}
    (hxQ : x ∉ Q) : ringKrullDim (R ⧸ (Q ⊔ Ideal.span {x})) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hle : Q ≤ Q ⊔ Ideal.span {x} := le_sup_left
  have hx : x ∈ Q ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[GroundTheory.Heights₂.Heights.ComplexSets.pullback]`. Introduce `i`. Simplify using `[GroundTheory.Heights₂.Heights.ComplexSets.pullback, GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]`.
-/
theorem eval_comp_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) :
    (eval x).comp (GroundTheory.Heights₂.Heights.ComplexSets.pullback A).toRingHom = eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.pullback, GroundTheory.Heights₂.Heights.ComplexSets.linPoly,
      Matrix.mulVec, dotProduct]

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I)` to `(GroundTheory.Heights₂.Heights.ComplexSets.projHom I A).toRingHom.toAlgebra`. Set `_ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I)` to `Algebra.toModule`. Establish `: Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I)` using `hA.finite`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I)` using `Algebra.IsIntegral.of_finite _ _`. Establish `key : ∀ i : Fin n, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧ Polynomial.eval₂ (GroundTheory.Heights₂.Heights.ComplexSets.pullback A).toRingHom (X i) f ∈ I`.

Introduce `i`. Take `⟨f, hfm, hf⟩` from `Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk I (X i))`. Use `⟨f, hfm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]`. Conclude with `hf`.

Use `choose f hfm hfI using key`. Use `(Set.Finite.pi (t := fun i => {z : ℂ | z ∈ ((f i).map (eval y)).roots}) (fun i => Multiset.finite_toSet _)).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hAx⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]`. Introduce `i`.

Establish `h0` using `hx _ (hfI i)`. Rewrite `h0` using `[Polynomial.hom_eval₂, eval_comp_pullback, hAx, eval_X]`. Rewrite using `[Polynomial.mem_roots ((hfm i).map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map]`. Conclude with `h0`.
-/
theorem fibre_finite {n d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection I A) (y : Fin d → ℂ) :
    {x : Fin n → ℂ | (∀ q ∈ I, eval x q = 0) ∧ A.mulVec x = y}.Finite := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (GroundTheory.Heights₂.Heights.ComplexSets.projHom I A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Algebra.IsIntegral.of_finite _ _
  have key : ∀ i : Fin n, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      Polynomial.eval₂ (GroundTheory.Heights₂.Heights.ComplexSets.pullback A).toRingHom (X i) f ∈ I := by
    intro i
    obtain ⟨f, hfm, hf⟩ :=
      Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk I (X i))
    refine ⟨f, hfm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    exact hf
  choose f hfm hfI using key
  refine (Set.Finite.pi (t := fun i => {z : ℂ | z ∈ ((f i).map (eval y)).roots})
    (fun i => Multiset.finite_toSet _)).subset ?_
  rintro x ⟨hx, hAx⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro i
  have h0 := hx _ (hfI i)
  rw [Polynomial.hom_eval₂, eval_comp_pullback, hAx, eval_X] at h0
  rw [Polynomial.mem_roots ((hfm i).map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map]
  exact h0

/- English proof (translation)
Introduce `n k J b U φ hJ hdim hb hU hne hφd hφi hφJ`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hZ : ∀ t ∈ U, ∀ q ∈ J ⊔ Ideal.span {b}, eval (φ t) q = 0` using `fun t ht => eval_eq_zero_of_mem_sup (hφJ ht) (hall t ht)`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) + 1 ≤ (k : WithBot ℕ∞)` using `hdim ▸ ringKrullDim_sup_span_add_one_le hb`.

Take `⟨t₀, ht₀⟩` from `hne`. Establish `hI : J ⊔ Ideal.span {b} ≠ ⊤`. Introduce `h`. Establish `h1` using `hZ t₀ ht₀ 1 (h ▸ Submodule.mem_top)`. Simplify using `at h1`.

Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b}))` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Establish `h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b}))` using `ringKrullDim_nonneg_of_nontrivial`. Establish `hlek : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) ≤ (k : WithBot ℕ∞)` using `le_trans (le_add_of_nonneg_right zero_le_one) hle`. Take `⟨d, -, hd⟩` from `GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.exists_nat_of_le h0 hlek`. Establish `hdk : d < k`.

Rewrite `hle` using `[hd]`. Establish `: ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞)` using `by exact_mod_cast hle`. Use `WithBot.coe_le_coe.mp this` as an intermediate fact. Conclude with `this` after adjusting the coercions. Take `⟨A, hA⟩` from `GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.proof n d _ hd`.

Establish `hL : Differentiable ℂ (fun x : Fin n → ℂ => A.mulVec x)` using `(LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable`. Take `⟨y, hy⟩` from `hF k d U (fun t => A.mulVec (φ t)) hdk hU ⟨t₀, ht₀⟩ (hL.comp_differentiableOn hφd)`. Apply `hy` to reduce the goal to its premises. Use `Set.Finite.of_finite_image ((fibre_finite _ A hA y).subset ?_) (hφi.mono fun t ht => ht.1)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ⟨ht, hty⟩, rfl⟩`.

Conclude with `⟨hZ t ht, hty⟩`.
-/
theorem proof (hF : HolomorphicFibreInfinite.Statement) : BranchOffHypersurface.Statement := by
  intro n k J b U φ hJ hdim hb hU hne hφd hφi hφJ
  by_contra hall
  push Not at hall
  have hZ : ∀ t ∈ U, ∀ q ∈ J ⊔ Ideal.span {b}, eval (φ t) q = 0 :=
    fun t ht => eval_eq_zero_of_mem_sup (hφJ ht) (hall t ht)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) + 1 ≤ (k : WithBot ℕ∞) :=
    hdim ▸ ringKrullDim_sup_span_add_one_le hb
  obtain ⟨t₀, ht₀⟩ := hne
  have hI : J ⊔ Ideal.span {b} ≠ ⊤ := by
    intro h
    have h1 := hZ t₀ ht₀ 1 (h ▸ Submodule.mem_top)
    simp at h1
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) :=
    ringKrullDim_nonneg_of_nontrivial
  have hlek : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) ≤ (k : WithBot ℕ∞) :=
    le_trans (le_add_of_nonneg_right zero_le_one) hle
  obtain ⟨d, -, hd⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.exists_nat_of_le h0 hlek
  have hdk : d < k := by
    rw [hd] at hle
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by exact_mod_cast hle
    have := WithBot.coe_le_coe.mp this
    exact_mod_cast this
  obtain ⟨A, hA⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.proof n d _ hd
  have hL : Differentiable ℂ (fun x : Fin n → ℂ => A.mulVec x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  obtain ⟨y, hy⟩ := hF k d U (fun t => A.mulVec (φ t)) hdk hU ⟨t₀, ht₀⟩ (hL.comp_differentiableOn hφd)
  apply hy
  refine Set.Finite.of_finite_image ((fibre_finite _ A hA y).subset ?_) (hφi.mono fun t ht => ht.1)
  rintro _ ⟨t, ⟨ht, hty⟩, rfl⟩
  exact ⟨hZ t ht, hty⟩

end BranchOffHypersurface

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
