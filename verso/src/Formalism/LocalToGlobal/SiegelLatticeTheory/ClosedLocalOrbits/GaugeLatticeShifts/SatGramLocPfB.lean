import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLoc

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev rcIntAlg (v : HeightOneSpectrum (𝓞 F)) :
    Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
  ((algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)).comp
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra

/- English proof (translation)
Use `letI := rcIntAlg (E := E) v`. Unfold `Formalism.UG.tensInt Formalism.UG.intOE at hx`. Use `(Subring.closure_le (t := (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring).2 ?_) hx` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨y, rfl⟩)`. Establish `ha : IsIntegral ℤ (a : E)`.

Take `⟨b, hb⟩` from `a.2`. Rewrite using `[← hb]`. Use `first`. Consider the case `exact b.isIntegral_coe`. Consider the case `exact b.2`.

Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe b`. Conclude with `IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F)) (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F)) (RingHom.ext_int _ _) ha`. Use `show IsIntegral _ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) y)`. Conclude with `isIntegral_algebraMap`.
-/
theorem rc_isIntegral (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
      (v.adicCompletionIntegers F).toSubring) :
    letI := rcIntAlg (E := E) v
    IsIntegral (v.adicCompletionIntegers F) x := by
  letI := rcIntAlg (E := E) v
  unfold Formalism.UG.tensInt Formalism.UG.intOE at hx
  refine (Subring.closure_le (t := (integralClosure (v.adicCompletionIntegers F)
    (E ⊗[F] v.adicCompletion F)).toSubring).2 ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
  · have ha : IsIntegral ℤ (a : E) := by
      obtain ⟨b, hb⟩ := a.2
      rw [← hb]
      first
      | exact b.isIntegral_coe
      | exact b.2
      | exact NumberField.RingOfIntegers.isIntegral_coe b
    exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F))
      (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
      (RingHom.ext_int _ _) ha
  · show IsIntegral _ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) y)
    exact isIntegral_algebraMap

/- English proof (translation)
Use `letI := rcIntAlg (E := E) v`. Take `⟨p, hpm, hp⟩` from `ht`. Establish `hc1 : Valued.v c ≤ 1` using `le_of_lt hc`. Take `⟨c', hc'⟩ : ∃ c' : v.adicCompletionIntegers F, (c' : v.adicCompletion F) = c` from `⟨⟨c, by first`. Consider the case `exact hc1`.

Consider the case `exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc1`. Consider the case `simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hc1⟩, rfl⟩`. Substitute `hc'` using the available equality. Establish `hC : algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) c' = (1 : E) ⊗ₜ[F] (c' : v.adicCompletion F)` using `rfl`. Establish `hq0 : (p.scaleRoots c').eval₂ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)) f = 0`.

Rewrite using `[hft, ← hC, Polynomial.scaleRoots_eval₂_mul, hp, mul_zero]`. Establish `hidem : ∀ i : ℕ, f * f ^ i = f` using `fun i => by`. Rewrite using `[← pow_succ']`. Conclude with `IsIdempotentElem.pow_succ_eq i hf`. Establish `key : f * algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) ((p.scaleRoots c').eval 1) = 0`.

Establish `h` using `congrArg (f * ·) hq0`. Simplify using `only [mul_zero] at h`. Rewrite `h` using `[Polynomial.eval₂_eq_sum_range, Finset.mul_sum]`. Rewrite using `[Polynomial.eval_eq_sum_range, map_sum, Finset.mul_sum, ← h]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[one_pow, mul_one, mul_left_comm, hidem, mul_comm]`. Establish `hsplit : (p.scaleRoots c').eval 1 = (∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i)) + 1`. Rewrite using `[Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, Finset.sum_range_succ]`. Simplify using `[Polynomial.coeff_scaleRoots, hpm.coeff_natDegree]`. Establish `hlt : Valued.v ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) : v.adicCompletionIntegers F) : v.adicCompletion F) < 1`.

Use `push_cast`. Use `Valuation.map_sum_lt _ one_ne_zero (fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Establish `h1 : Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1` using `by first`. Consider the case `exact (p.coeff i).2`.

Consider the case `exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2`. Establish `hm : p.natDegree - i = (p.natDegree - i - 1) + 1` using `by omega`. Rewrite using `[Valuation.map_mul, Valuation.map_pow, hm, pow_succ]`. Combine the equalities or inequalities in the displayed calculation. Establish `hU : (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0`.

Rewrite using `[hsplit]`. Introduce `h0`. Establish `h0' : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) : v.adicCompletionIntegers F) : v.adicCompletion F) = -1`. Establish `: ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) : v.adicCompletionIntegers F) : v.adicCompletion F) + 1 = 0`. Rewrite using `[← h0]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `eq_neg_of_add_eq_zero_left this`. Establish `hv` using `hlt`. Rewrite `hv` using `[h0', Valuation.map_neg, Valuation.map_one]`.

Conclude with `lt_irrefl _ hv`. Establish `hunit : IsUnit (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F))` using `(Ne.isUnit hU).map _`. Conclude with `hunit.mul_left_eq_zero.mp key`.
-/
theorem rc_idem_zero (v : HeightOneSpectrum (𝓞 F)) (f t : E ⊗[F] v.adicCompletion F)
    (c : v.adicCompletion F) (hc : Valued.v c < 1) (hf : f * f = f)
    (hft : f = ((1 : E) ⊗ₜ[F] c) * t)
    (ht : letI := rcIntAlg (E := E) v; IsIntegral (v.adicCompletionIntegers F) t) : f = 0 := by
  letI := rcIntAlg (E := E) v
  obtain ⟨p, hpm, hp⟩ := ht
  have hc1 : Valued.v c ≤ 1 := le_of_lt hc
  obtain ⟨c', hc'⟩ : ∃ c' : v.adicCompletionIntegers F, (c' : v.adicCompletion F) = c :=
    ⟨⟨c, by
      first
      | exact hc1
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc1
      | simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hc1⟩, rfl⟩
  subst hc'
  have hC : algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) c' =
      (1 : E) ⊗ₜ[F] (c' : v.adicCompletion F) := rfl

  have hq0 : (p.scaleRoots c').eval₂ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)) f = 0 := by
    rw [hft, ← hC, Polynomial.scaleRoots_eval₂_mul, hp, mul_zero]
  have hidem : ∀ i : ℕ, f * f ^ i = f := fun i => by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq i hf

  have key : f * algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) ((p.scaleRoots c').eval 1) = 0 := by
    have h := congrArg (f * ·) hq0
    simp only [mul_zero] at h
    rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum] at h
    rw [Polynomial.eval_eq_sum_range, map_sum, Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_pow, mul_one, mul_left_comm, hidem, mul_comm]
  have hsplit : (p.scaleRoots c').eval 1 =
      (∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i)) + 1 := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, Finset.sum_range_succ]
    simp [Polynomial.coeff_scaleRoots, hpm.coeff_natDegree]

  have hlt : Valued.v ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
      v.adicCompletionIntegers F) : v.adicCompletion F) < 1 := by
    push_cast
    refine Valuation.map_sum_lt _ one_ne_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h1 : Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 := by
      first
      | exact (p.coeff i).2
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have hm : p.natDegree - i = (p.natDegree - i - 1) + 1 := by omega
    rw [Valuation.map_mul, Valuation.map_pow, hm, pow_succ]
    calc Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) *
          (Valued.v (c' : v.adicCompletion F) ^ (p.natDegree - i - 1) * Valued.v (c' : v.adicCompletion F))
        ≤ 1 * (1 * Valued.v (c' : v.adicCompletion F)) :=
          mul_le_mul' h1 (mul_le_mul' (pow_le_one' hc1 _) le_rfl)
      _ < 1 := by rw [one_mul, one_mul]; exact hc
  have hU : (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [hsplit]
    intro h0
    have h0' : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
        v.adicCompletionIntegers F) : v.adicCompletion F) = -1 := by
      have : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
          v.adicCompletionIntegers F) : v.adicCompletion F) + 1 = 0 := by
        rw [← h0]; push_cast; ring
      exact eq_neg_of_add_eq_zero_left this
    have hv := hlt
    rw [h0', Valuation.map_neg, Valuation.map_one] at hv
    exact lt_irrefl _ hv
  have hunit : IsUnit (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)
      (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F)) :=
    (Ne.isUnit hU).map _
  exact hunit.mul_left_eq_zero.mp key

/- English proof (translation)
Set `e : (v.adicCompletion F ⊗[F] E) ≃ₗ[v.adicCompletion F] (E ⊗[F] v.adicCompletion F)` to `{ TensorProduct.comm F (v.adicCompletion F) E with map_smul' := fun a x => by show TensorProduct.comm F _ _ (a • x) = a • TensorProduct.comm F _ _ x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b y`. Rewrite using `[TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul]`.

Use `first`. Consider the case `(show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])`. Consider the case `(rw [Algebra.smul_def] show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])`.

Consider the case `(simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]; done)`. Consider the case `add x y hx hy`. Rewrite using `[smul_add, map_add, map_add, hx, hy, smul_add] }`. Rewrite using `[← e.finrank_eq, Module.finrank_baseChange]`.
-/
theorem rc_finrank (v : HeightOneSpectrum (𝓞 F)) :
    Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = Module.finrank F E := by
  let e : (v.adicCompletion F ⊗[F] E) ≃ₗ[v.adicCompletion F] (E ⊗[F] v.adicCompletion F) :=
    { TensorProduct.comm F (v.adicCompletion F) E with
      map_smul' := fun a x => by
        show TensorProduct.comm F _ _ (a • x) = a • TensorProduct.comm F _ _ x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
          rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul]
          first
          | (show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (rw [Algebra.smul_def]
             show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]; done)
        | add x y hx hy =>
          rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  rw [← e.finrank_eq, Module.finrank_baseChange]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ h2 v e he hee hes hct`. Take `⟨c, hc, t, ht, hft⟩` from `hct`. Use `set e' := Formalism.UG.sigR σ (v.adicCompletion F) e with he'`. Establish `he'e' : e' * e' = e'` using `by rw [he', ← map_mul, hee]`. Establish `hee' : e * e' = 0` using `hes`.

Establish `he'e : e' * e = 0` using `by rw [mul_comm]; exact hee'`. Establish `hidem : (1 - e - e') * (1 - e - e') = 1 - e - e'`. Take the linear combination `hee + he'e' + 2 * hee'`. Establish `hf0 : 1 - e - e' = 0` using `rc_idem_zero v (1 - e - e') t c hc hidem hft (rc_isIntegral v t ht)`. Establish `hsum : e + e' = 1` using `by linear_combination -hf0`.

Establish `hfr : Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = 2`. Rewrite using `[rc_finrank, h2]`. Use `haveI : Nontrivial (E ⊗[F] v.adicCompletion F) := by`. Establish `hpos : 0 < Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)`. Rewrite using `[hfr]`.

Evaluate the numerical expressions. Conclude with `Module.nontrivial_of_finrank_pos hpos`. Establish `he0 : e ≠ 0`. Introduce `h0`. Establish `h3 : e' = 0` using `by rw [he', h0, map_zero]`.

Establish `h1 : (1 : E ⊗[F] v.adicCompletion F) = 0` using `by rw [← hsum, h0, h3, add_zero]`. Conclude with `one_ne_zero h1`. Establish `hli : LinearIndependent (v.adicCompletion F) ![e, e']`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s s' hst`.

Establish `h1 : s • e = 0`. Establish `h` using `congrArg (e * ·) hst`. Simplify `h` using `only [mul_add, mul_smul_comm, hee, hee', smul_zero, add_zero, mul_zero]`. Establish `h3 : s' • e' = 0`. Establish `h` using `congrArg (e' * ·) hst`.

Simplify `h` using `only [mul_add, mul_smul_comm, he'e, he'e', smul_zero, zero_add, mul_zero]`. Establish `he'0 : e' ≠ 0`. Introduce `h0`. Establish `h4 : e = 1` using `by rw [← hsum, h0, add_zero]`. Establish `h5 : e' = 1` using `by rw [he', h4, map_one]`.

Rewrite `h5` using `[h0]`. Conclude with `zero_ne_one h5`. Conclude with `⟨(smul_eq_zero.mp h1).resolve_right he0, (smul_eq_zero.mp h3).resolve_right he'0⟩`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)`. Rewrite using `[hfr]`.

Both sides reduce to the same expression. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hb0 : b 0 = e` using `by simp [b]`. Establish `hb1 : b 1 = e'` using `by simp [b]`. Set `r0 : E ⊗[F] v.adicCompletion F → v.adicCompletion F` to `fun x => b.repr x 0`.

Establish `hr : ∀ x, e * x = r0 x • e`. Introduce `x`. Establish `hx` using `b.sum_repr x`. Rewrite `hx` using `[Fin.sum_univ_two, hb0, hb1]`. Use `conv_lhs => rw [← hx]`.

Rewrite using `[mul_add, mul_smul_comm, mul_smul_comm, hee, hee', smul_zero, add_zero]`. Establish `huniq : ∀ α β : v.adicCompletion F, α • e = β • e → α = β` using `fun α β h => smul_left_injective (v.adicCompletion F) he0 h`. Establish `halg : ∀ a : v.adicCompletion F, ((1 : E) ⊗ₜ[F] a) * e = a • e`. Introduce `a`. Rewrite using `[Algebra.smul_def]`.

Both sides reduce to the same expression. Establish `hr1 : r0 1 = 1` using `huniq _ _ (by rw [← hr, mul_one, one_smul])`. Establish `hr0 : r0 0 = 0` using `huniq _ _ (by rw [← hr, mul_zero, zero_smul])`. Establish `hra : ∀ x y, r0 (x + y) = r0 x + r0 y` using `fun x y => huniq _ _ (by rw [← hr, mul_add, hr, hr, add_smul])`. Establish `hrm : ∀ x y, r0 (x * y) = r0 x * r0 y` using `fun x y => huniq _ _ (calc r0 (x * y) • e = e * (x * y) := (hr _).symm _ = (e * x) * y := (mul_assoc _ _ _).symm _ = (r0 x • e) * y := by rw [hr] _ = r0 x • (e * y) := smul_mul_assoc _ _ _ _ = r0 x • (r0 y • e) := by rw [hr] _ = (r0 x * r0 y) • e := (mul_smul _ _ _).symm)`.

Establish `hr2 : ∀ a : v.adicCompletion F, r0 ((1 : E) ⊗ₜ[F] a) = a` using `fun a => huniq _ _ (by rw [← hr, mul_comm, halg])`. Set `r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F` to `{ toFun := r0, map_one' := hr1, map_mul' := hrm, map_zero' := hr0, map_add' := hra }`. Use `⟨r, ?_, hr2, ?_, ?_⟩` and prove the remaining obligations. Use `show r0 e = 1`. Conclude with `huniq _ _ (by rw [← hr, hee, one_smul])`.

Introduce `x hx`. Establish `hint` using `rc_isIntegral v x hx`. Use `letI := rcIntAlg (E := E) v`. Establish `hint' : IsIntegral (v.adicCompletionIntegers F) (r x)`. Use `IsIntegral.map_of_comp_eq (RingHom.id _) r ?_ hint` and prove the remaining obligations.

Use `RingHom.ext fun y => ?_` and prove the remaining obligations. Use `show ((y : v.adicCompletionIntegers F) : v.adicCompletion F) = r0 ((1 : E) ⊗ₜ[F] ((y : v.adicCompletionIntegers F) : v.adicCompletion F))`. Conclude with `(hr2 _).symm`. Use `first`. Consider the case `(obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'; rw [← hy]; exact y.2)`.

Consider the case `exact ValuationSubring.mem_of_isIntegral _ hint'`. Consider the case `exact (Valuation.integer.integers _).mem_of_integral hint'`. Introduce `x hx show x = ((1 : E) ⊗ₜ[F] r0 x) * e`. Rewrite using `[halg, ← hr, hx]`.
-/
theorem reduction_structure_holds : RedCore := by
  intro F E _ _ _ _ _ σ hσ h2 v e he hee hes hct
  obtain ⟨c, hc, t, ht, hft⟩ := hct
  set e' := Formalism.UG.sigR σ (v.adicCompletion F) e with he'
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have hee' : e * e' = 0 := hes
  have he'e : e' * e = 0 := by rw [mul_comm]; exact hee'

  have hidem : (1 - e - e') * (1 - e - e') = 1 - e - e' := by
    linear_combination hee + he'e' + 2 * hee'
  have hf0 : 1 - e - e' = 0 := rc_idem_zero v (1 - e - e') t c hc hidem hft (rc_isIntegral v t ht)
  have hsum : e + e' = 1 := by linear_combination -hf0
  have hfr : Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = 2 := by
    rw [rc_finrank, h2]
  haveI : Nontrivial (E ⊗[F] v.adicCompletion F) := by
    have hpos : 0 < Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
      rw [hfr]; norm_num
    exact Module.nontrivial_of_finrank_pos hpos
  have he0 : e ≠ 0 := by
    intro h0
    have h3 : e' = 0 := by rw [he', h0, map_zero]
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = 0 := by rw [← hsum, h0, h3, add_zero]
    exact one_ne_zero h1

  have hli : LinearIndependent (v.adicCompletion F) ![e, e'] := by
    rw [LinearIndependent.pair_iff]
    intro s s' hst
    have h1 : s • e = 0 := by
      have h := congrArg (e * ·) hst
      simpa only [mul_add, mul_smul_comm, hee, hee', smul_zero, add_zero, mul_zero] using h
    have h3 : s' • e' = 0 := by
      have h := congrArg (e' * ·) hst
      simpa only [mul_add, mul_smul_comm, he'e, he'e', smul_zero, zero_add, mul_zero] using h
    have he'0 : e' ≠ 0 := by
      intro h0
      have h4 : e = 1 := by rw [← hsum, h0, add_zero]
      have h5 : e' = 1 := by rw [he', h4, map_one]
      rw [h0] at h5
      exact zero_ne_one h5
    exact ⟨(smul_eq_zero.mp h1).resolve_right he0, (smul_eq_zero.mp h3).resolve_right he'0⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
    rw [hfr]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = e := by simp [b]
  have hb1 : b 1 = e' := by simp [b]
  let r0 : E ⊗[F] v.adicCompletion F → v.adicCompletion F := fun x => b.repr x 0
  have hr : ∀ x, e * x = r0 x • e := by
    intro x
    have hx := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at hx
    conv_lhs => rw [← hx]
    rw [mul_add, mul_smul_comm, mul_smul_comm, hee, hee', smul_zero, add_zero]
  have huniq : ∀ α β : v.adicCompletion F, α • e = β • e → α = β :=
    fun α β h => smul_left_injective (v.adicCompletion F) he0 h
  have halg : ∀ a : v.adicCompletion F, ((1 : E) ⊗ₜ[F] a) * e = a • e := by
    intro a; rw [Algebra.smul_def]; rfl
  have hr1 : r0 1 = 1 := huniq _ _ (by rw [← hr, mul_one, one_smul])
  have hr0 : r0 0 = 0 := huniq _ _ (by rw [← hr, mul_zero, zero_smul])
  have hra : ∀ x y, r0 (x + y) = r0 x + r0 y := fun x y =>
    huniq _ _ (by rw [← hr, mul_add, hr, hr, add_smul])
  have hrm : ∀ x y, r0 (x * y) = r0 x * r0 y := fun x y =>
    huniq _ _ (calc r0 (x * y) • e = e * (x * y) := (hr _).symm
      _ = (e * x) * y := (mul_assoc _ _ _).symm
      _ = (r0 x • e) * y := by rw [hr]
      _ = r0 x • (e * y) := smul_mul_assoc _ _ _
      _ = r0 x • (r0 y • e) := by rw [hr]
      _ = (r0 x * r0 y) • e := (mul_smul _ _ _).symm)
  have hr2 : ∀ a : v.adicCompletion F, r0 ((1 : E) ⊗ₜ[F] a) = a := fun a =>
    huniq _ _ (by rw [← hr, mul_comm, halg])
  let r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
    { toFun := r0, map_one' := hr1, map_mul' := hrm, map_zero' := hr0, map_add' := hra }
  refine ⟨r, ?_, hr2, ?_, ?_⟩
  · show r0 e = 1
    exact huniq _ _ (by rw [← hr, hee, one_smul])
  · intro x hx
    have hint := rc_isIntegral v x hx
    letI := rcIntAlg (E := E) v
    have hint' : IsIntegral (v.adicCompletionIntegers F) (r x) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) r ?_ hint
      refine RingHom.ext fun y => ?_
      show ((y : v.adicCompletionIntegers F) : v.adicCompletion F) =
        r0 ((1 : E) ⊗ₜ[F] ((y : v.adicCompletionIntegers F) : v.adicCompletion F))
      exact (hr2 _).symm
    first
    | (obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'; rw [← hy]; exact y.2)
    | exact ValuationSubring.mem_of_isIntegral _ hint'
    | exact (Valuation.integer.integers _).mem_of_integral hint'
  · intro x hx
    show x = ((1 : E) ⊗ₜ[F] r0 x) * e
    rw [halg, ← hr, hx]

end Formalism.L2.SG.Pf.SatGramLoc
