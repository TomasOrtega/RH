import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNoetherProjection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsLiftToZeros
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

namespace FiniteSeparatingModel

variable {σ : Type} {e : ℕ}

/- English proof (translation)
Establish `hc : (aeval (R` using `ℚ) z).toRingHom.comp (aeval (R := ℚ) ℓ).toRingHom = (aeval fun j => aeval z (ℓ j)).toRingHom := by`. Apply the tactic sequence `apply MvPolynomial.ringHom_ext <;> intro <;> simp`. Use `Polynomial.hom_eval₂ Q (aeval (R := ℚ) ℓ).toRingHom (aeval (R := ℚ) z).toRingHom g` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `this`.
-/
theorem aeval_eval₂ (ℓ : Fin e → MvPolynomial σ ℚ) (Q : Polynomial (MvPolynomial (Fin e) ℚ))
    (g : MvPolynomial σ ℚ) (z : σ → ℂ) :
    aeval z (Q.eval₂ (aeval ℓ).toRingHom g) =
      Q.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z g) := by
  have hc : (aeval (R := ℚ) z).toRingHom.comp (aeval (R := ℚ) ℓ).toRingHom =
      (aeval fun j => aeval z (ℓ j)).toRingHom := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  have := Polynomial.hom_eval₂ Q (aeval (R := ℚ) ℓ).toRingHom (aeval (R := ℚ) z).toRingHom g
  rw [hc] at this
  exact this

/- English proof (translation)
Take `⟨q, hpq, hdvd⟩` from `p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp.ne_zero 0`. Simplify using `only [map_zero, sub_zero] at hpq hdvd`. Use `⟨q, ?_, ?_, fun h => hdvd (Polynomial.X_dvd_iff.mpr h)⟩` and prove the remaining obligations. Rewrite `hp` using `[hpq]`. Conclude with `(Polynomial.monic_X.pow _).of_mul_monic_left hp`.

Rewrite `hpf` using `[hpq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]`. Conclude with `(hP.mem_or_mem hpf).resolve_left fun h => hf (hP.mem_of_pow_mem _ h)`.
-/
theorem exists_monic_coeff_zero_ne {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) {f : MvPolynomial σ ℚ} (hf : f ∉ P)
    {p : Polynomial (MvPolynomial (Fin e) ℚ)} (hp : p.Monic) (hpf : p.eval₂ (aeval ℓ).toRingHom f ∈ P) :
    ∃ q : Polynomial (MvPolynomial (Fin e) ℚ),
      q.Monic ∧ q.eval₂ (aeval ℓ).toRingHom f ∈ P ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨q, hpq, hdvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hdvd
  refine ⟨q, ?_, ?_, fun h => hdvd (Polynomial.X_dvd_iff.mpr h)⟩
  · rw [hpq] at hp
    exact (Polynomial.monic_X.pow _).of_mul_monic_left hp
  · rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hpf
    exact (hP.mem_or_mem hpf).resolve_left fun h => hf (hP.mem_of_pow_mem _ h)

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Set `φ : MvPolynomial (Fin e) ℚ →+* MvPolynomial σ ℚ ⧸ P` to `(Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom`. Set `_ : Algebra (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)` to `φ.toAlgebra`. Establish `key : ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Polynomial.aeval (Ideal.Quotient.mk P u) Q = Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u)` using `fun Q => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl`. Establish `hφ : Function.Injective (algebraMap (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `q hq`. Conclude with `hinj q (Ideal.Quotient.eq_zero_iff_mem.mp hq)`. Establish `: Module.IsTorsionFree (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hφ`. Take `⟨p, hpm, hp⟩` from `hint u`. Establish `hu : IsIntegral (MvPolynomial (Fin e) ℚ) (Ideal.Quotient.mk P u)` using `⟨p, hpm, by rw [← Polynomial.aeval_def, key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩`.

Use `⟨minpoly _ (Ideal.Quotient.mk P u), minpoly.monic hu, ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← key]`. Conclude with `minpoly.aeval _ _`. Conclude with `minpoly.isIntegrallyClosed_dvd hu (by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ)`.
-/
theorem exists_minpoly {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) (hinj : ∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0)
    (hint : ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) (u : MvPolynomial σ ℚ) :
    ∃ G : Polynomial (MvPolynomial (Fin e) ℚ), G.Monic ∧ G.eval₂ (aeval ℓ).toRingHom u ∈ P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q := by
  let φ : MvPolynomial (Fin e) ℚ →+* MvPolynomial σ ℚ ⧸ P :=
    (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom
  let _ : Algebra (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) := φ.toAlgebra
  have key : ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ),
      Polynomial.aeval (Ideal.Quotient.mk P u) Q = Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) :=
    fun Q => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl
  have hφ : Function.Injective (algebraMap (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    exact hinj q (Ideal.Quotient.eq_zero_iff_mem.mp hq)
  have : Module.IsTorsionFree (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  obtain ⟨p, hpm, hp⟩ := hint u
  have hu : IsIntegral (MvPolynomial (Fin e) ℚ) (Ideal.Quotient.mk P u) :=
    ⟨p, hpm, by rw [← Polynomial.aeval_def, key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩
  refine ⟨minpoly _ (Ideal.Quotient.mk P u), minpoly.monic hu, ?_, fun Q hQ => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← key]
    exact minpoly.aeval _ _
  · exact minpoly.isIntegrallyClosed_dvd hu (by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ)

/- English proof (translation)
Set `k : σ ≃ Fin (Fintype.card σ)` to `Fintype.equivFin σ`. Set `q : (σ → ℂ) → Polynomial ℂ` to `fun z => ∑ i, Polynomial.C (z i - x i) * Polynomial.X ^ (k i : ℕ)`. Establish `hq : ∀ z, z ≠ x → q z ≠ 0`. Introduce `z hz h`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hz`.

Establish `h1` using `congrArg (fun r => Polynomial.coeff r (k i : ℕ)) h`. Simplify using `only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1`. Rewrite `h1` using `[Finset.sum_eq_single i]`. Rewrite `h1` using `[if_pos rfl]`. Conclude with `hi (sub_eq_zero.mp h1)`.

Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce `h'`. Conclude with `hj (k.injective (Fin.ext h'.symm))`. Simplify using the standard rewrite rules.

Set `Q : Polynomial ℂ` to `∏ z ∈ S.erase x, q z`. Establish `hQ : Q ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun z hz => hq z (Finset.ne_of_mem_erase hz)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℚ, Q.eval (c : ℂ) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Apply `Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))` to reduce the goal to its premises. Use `(Q.roots.toFinset.finite_toSet).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Simplify using `[Polynomial.mem_roots hQ, h c]`. Use `⟨∑ i, C (c ^ (k i : ℕ)) * X i, fun z hz hzu => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hzx`. Establish `hev : aeval z (∑ i, C (c ^ (k i : ℕ)) * X i) - aeval x (∑ i, C (c ^ (k i : ℕ)) * X i) = (q z).eval (c : ℂ)`. Simplify using `only [map_sum, map_mul, aeval_C, aeval_X, q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eq_ratCast (algebraMap ℚ ℂ)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hev` using `[hzu, sub_self]`. Rewrite `hc` using `[Polynomial.eval_prod]`. Conclude with `Finset.prod_ne_zero_iff.mp hc z (Finset.mem_erase.mpr ⟨hzx, hz⟩) hev.symm`.
-/
theorem exists_separating [Fintype σ] (S : Finset (σ → ℂ)) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℚ, ∀ z ∈ S, aeval z u = aeval x u → z = x := by
  classical
  let k : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q : (σ → ℂ) → Polynomial ℂ :=
    fun z => ∑ i, Polynomial.C (z i - x i) * Polynomial.X ^ (k i : ℕ)
  have hq : ∀ z, z ≠ x → q z ≠ 0 := by
    intro z hz h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have h1 := congrArg (fun r => Polynomial.coeff r (k i : ℕ)) h
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [if_pos rfl] at h1
      exact hi (sub_eq_zero.mp h1)
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (k.injective (Fin.ext h'.symm))
    · simp
  let Q : Polynomial ℂ := ∏ z ∈ S.erase x, q z
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z hz => hq z (Finset.ne_of_mem_erase hz)
  obtain ⟨c, hc⟩ : ∃ c : ℚ, Q.eval (c : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    apply Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))
    refine (Q.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨c, rfl⟩
    simp [Polynomial.mem_roots hQ, h c]
  refine ⟨∑ i, C (c ^ (k i : ℕ)) * X i, fun z hz hzu => ?_⟩
  by_contra hzx
  have hev : aeval z (∑ i, C (c ^ (k i : ℕ)) * X i) - aeval x (∑ i, C (c ^ (k i : ℕ)) * X i) =
      (q z).eval (c : ℂ) := by
    simp only [map_sum, map_mul, aeval_C, aeval_X, q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    push_cast
    ring
  rw [hzu, sub_self] at hev
  rw [Polynomial.eval_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc z (Finset.mem_erase.mpr ⟨hzx, hz⟩) hev.symm

end FiniteSeparatingModel

/- English proof (translation)
Introduce `σ _ P f x hP hf _`. Take `⟨e, ℓ, hinj, hint⟩` from `hN σ P hP.ne_top`. Use `choose p hpm hp using hint`. Set `yx : Fin e → ℂ` to `fun j => aeval x (ℓ j)`. Set `S : Finset (σ → ℂ)` to `Fintype.piFinset fun i => ((p (X i)).map (aeval yx).toRingHom).roots.toFinset`.

Establish `hS : ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) → (fun j => aeval z (ℓ j)) = yx → z ∈ S`. Introduce `z hz hzl`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots ((hpm _).map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map, ← hzl]`.

Use `hz _ (hp (X i))` as an intermediate fact. Rewrite `this` using `[FiniteSeparatingModel.aeval_eval₂, aeval_X]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `FiniteSeparatingModel.exists_separating S x`. Take `⟨G, hGm, hGu, hGdvd⟩` from `FiniteSeparatingModel.exists_minpoly hP ℓ hinj (fun g => ⟨p g, hpm g, hp g⟩) u`. Take `⟨q, -, hqf, hq0⟩` from `FiniteSeparatingModel.exists_monic_coeff_zero_ne hP ℓ hf (hpm f) (hp f)`.

Use `⟨e, ℓ, u, G, q.coeff 0, 1, hGm, hq0, one_ne_zero, fun i => ⟨p (X i), hpm _, fun z hz => ?_⟩, fun z hz => ?_, fun z hz hc hfz => ?_, fun y t _ ht => hL σ P e ℓ u G (fun g => ⟨p g, hpm g, hp g⟩) hGdvd y t ht, fun z hz hzl hzu => hu z (hS z hz hzl) hzu⟩` and prove the remaining obligations. Use `hz _ (hp (X i))` as an intermediate fact. Rewrite `this` using `[FiniteSeparatingModel.aeval_eval₂, aeval_X]`. Then use the resulting hypothesis. Use `hz _ hGu` as an intermediate fact. Rewrite `this` using `[FiniteSeparatingModel.aeval_eval₂]`. Then use the resulting hypothesis.

Apply `hc` to reduce the goal to its premises. Use `hz _ hqf` as an intermediate fact. Rewrite `this` using `[FiniteSeparatingModel.aeval_eval₂, hfz, Polynomial.eval₂_at_zero]`. Conclude with `this`.
-/
theorem FiniteSeparatingModel.proof (hN : NoetherProjection.Statement)
    (hL : RootsLiftToZeros.Statement) : FiniteSeparatingModel.Statement := by
  classical
  intro σ _ P f x hP hf _
  obtain ⟨e, ℓ, hinj, hint⟩ := hN σ P hP.ne_top
  choose p hpm hp using hint
  let yx : Fin e → ℂ := fun j => aeval x (ℓ j)
  let S : Finset (σ → ℂ) := Fintype.piFinset fun i =>
    ((p (X i)).map (aeval yx).toRingHom).roots.toFinset
  have hS : ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) → (fun j => aeval z (ℓ j)) = yx → z ∈ S := by
    intro z hz hzl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hpm _).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hzl]
    have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  obtain ⟨u, hu⟩ := FiniteSeparatingModel.exists_separating S x
  obtain ⟨G, hGm, hGu, hGdvd⟩ :=
    FiniteSeparatingModel.exists_minpoly hP ℓ hinj (fun g => ⟨p g, hpm g, hp g⟩) u
  obtain ⟨q, -, hqf, hq0⟩ :=
    FiniteSeparatingModel.exists_monic_coeff_zero_ne hP ℓ hf (hpm f) (hp f)
  refine ⟨e, ℓ, u, G, q.coeff 0, 1, hGm, hq0, one_ne_zero,
    fun i => ⟨p (X i), hpm _, fun z hz => ?_⟩, fun z hz => ?_, fun z hz hc hfz => ?_,
    fun y t _ ht => hL σ P e ℓ u G (fun g => ⟨p g, hpm g, hp g⟩) hGdvd y t ht,
    fun z hz hzl hzu => hu z (hS z hz hzl) hzu⟩
  · have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  · have := hz _ hGu
    rwa [FiniteSeparatingModel.aeval_eval₂] at this
  · apply hc
    have := hz _ hqf
    rw [FiniteSeparatingModel.aeval_eval₂, hfz, Polynomial.eval₂_at_zero] at this
    exact this

end GroundTheory.Heights₂.Heights.HilbertSamuel
