import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

/- English proof (translation)
Take `⟨Q, hQm, hQ⟩` from `hu`. Take `⟨r0, hr0⟩` from `hw`. Establish `hcommon : ∃ e : ℕ, ∀ k, ∃ r : A, algebraMap A Ω r = w ^ e * (Q.coeff k : Ω)` using `by choose ef rf hf using fun k => hR _ (Q.coeff k).2`. Use `⟨(Finset.range (Q.natDegree + 1)).sup ef, fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ Finset.range (Q.natDegree + 1)`.

Establish `hle` using `Finset.le_sup (f := ef) hk`. Use `⟨r0 ^ ((Finset.range (Q.natDegree + 1)).sup ef - ef k) * rf k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hr0, hf, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Establish `: Q.coeff k = 0` using `Polynomial.coeff_eq_zero_of_natDegree_lt (by`. Simplify `hk)` using `[Nat.lt_succ_iff]`.

Conclude with `⟨0, by simp [this]⟩`. Take `⟨e, he⟩` from `hcommon`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `hQ'm : (Q.map (algebraMap R Ω)).Monic` using `hQm.map _`. Establish `hl : (Q.map (algebraMap R Ω)).scaleRoots (w ^ e) ∈ Polynomial.lifts (algebraMap A Ω)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `k`. Rewrite using `[Polynomial.coeff_scaleRoots, Polynomial.coeff_map]`. Break down `lt_trichotomy k (Q.map (algebraMap R Ω)).natDegree with h | h | h` into its components or cases. Take `⟨r, hr⟩` from `he k`.

Use `⟨r0 ^ (e * ((Q.map (algebraMap R Ω)).natDegree - k - 1)) * r, ?_⟩` and prove the remaining obligations. Establish `h1 : (Q.map (algebraMap R Ω)).natDegree - k = ((Q.map (algebraMap R Ω)).natDegree - k - 1) + 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_mul, map_pow, hr0, hr]`. Use `conv_rhs => rw [h1]`.

Rewrite using `[pow_succ, ← pow_mul]`. Use `show _ = (Q.coeff k : Ω) * _`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : algebraMap R Ω (Q.coeff k) = 1`. Rewrite using `[← Polynomial.coeff_map, h]`.

Conclude with `hQ'm.coeff_natDegree`. Conclude with `⟨1, by rw [h2, h]; simp⟩`. Establish `h2 : algebraMap R Ω (Q.coeff k) = 0`. Rewrite using `[← Polynomial.coeff_map]`. Conclude with `Polynomial.coeff_eq_zero_of_natDegree_lt h`.

Conclude with `⟨0, by rw [h2]; simp⟩`. Take `⟨Q', hQ', -, hQ'mon⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (Polynomial.monic_scaleRoots_iff _ |>.mpr hQ'm)`. Use `⟨Q', hQ'mon, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hQ']`. Establish `h3 : Polynomial.eval₂ (RingHom.id Ω) u (Q.map (algebraMap R Ω)) = 0`.

Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hQ`. Use `Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := w ^ e) h3` as an intermediate fact. Simplify `this` using `[Polynomial.eval₂_id]`.
-/
theorem isIntegral_pow_mul_of_subring {A Ω : Type*} [CommRing A] [CommRing Ω] [Algebra A Ω] (R : Subring Ω)
    (w : Ω) (hw : ∃ r, algebraMap A Ω r = w)
    (hR : ∀ a ∈ R, ∃ e : ℕ, ∃ r : A, algebraMap A Ω r = w ^ e * a) {u : Ω} (hu : IsIntegral R u) :
    ∃ e : ℕ, IsIntegral A (w ^ e * u) := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hu
  obtain ⟨r0, hr0⟩ := hw
  have hcommon : ∃ e : ℕ, ∀ k, ∃ r : A, algebraMap A Ω r = w ^ e * (Q.coeff k : Ω) := by
    choose ef rf hf using fun k => hR _ (Q.coeff k).2
    refine ⟨(Finset.range (Q.natDegree + 1)).sup ef, fun k => ?_⟩
    by_cases hk : k ∈ Finset.range (Q.natDegree + 1)
    · have hle := Finset.le_sup (f := ef) hk
      refine ⟨r0 ^ ((Finset.range (Q.natDegree + 1)).sup ef - ef k) * rf k, ?_⟩
      rw [map_mul, map_pow, hr0, hf, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · have : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
        simpa [Nat.lt_succ_iff] using hk)
      exact ⟨0, by simp [this]⟩
  obtain ⟨e, he⟩ := hcommon
  refine ⟨e, ?_⟩
  have hQ'm : (Q.map (algebraMap R Ω)).Monic := hQm.map _
  have hl : (Q.map (algebraMap R Ω)).scaleRoots (w ^ e) ∈ Polynomial.lifts (algebraMap A Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_scaleRoots, Polynomial.coeff_map]
    rcases lt_trichotomy k (Q.map (algebraMap R Ω)).natDegree with h | h | h
    · obtain ⟨r, hr⟩ := he k
      refine ⟨r0 ^ (e * ((Q.map (algebraMap R Ω)).natDegree - k - 1)) * r, ?_⟩
      have h1 : (Q.map (algebraMap R Ω)).natDegree - k = ((Q.map (algebraMap R Ω)).natDegree - k - 1) + 1 := by
        omega
      rw [map_mul, map_pow, hr0, hr]
      conv_rhs => rw [h1]
      rw [pow_succ, ← pow_mul]
      show _ = (Q.coeff k : Ω) * _
      ring
    · have h2 : algebraMap R Ω (Q.coeff k) = 1 := by
        rw [← Polynomial.coeff_map, h]
        exact hQ'm.coeff_natDegree
      exact ⟨1, by rw [h2, h]; simp⟩
    · have h2 : algebraMap R Ω (Q.coeff k) = 0 := by
        rw [← Polynomial.coeff_map]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt h
      exact ⟨0, by rw [h2]; simp⟩
  obtain ⟨Q', hQ', -, hQ'mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (Polynomial.monic_scaleRoots_iff _ |>.mpr hQ'm)
  refine ⟨Q', hQ'mon, ?_⟩
  rw [← Polynomial.eval_map, hQ']
  have h3 : Polynomial.eval₂ (RingHom.id Ω) u (Q.map (algebraMap R Ω)) = 0 := by
    rw [Polynomial.eval₂_map]
    exact hQ
  have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := w ^ e) h3
  simpa [Polynomial.eval₂_id] using this

/- English proof (translation)
Introduce `Ω _ _ D l P _ hP hgen p hp j K d x c hchom hcp hint μ`. Use `Fact.mk hp` as an intermediate fact. Establish `hl` using `DehomCharpolyForms.ne_zero_of_generic hgen`. Use `set n := Module.finrank P Ω with hn`. Use `set f := LinearMap.charpoly (Algebra.lmul P Ω x) with hf`.

Establish `h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n)`. Use `congrArg (fun g => Polynomial.coeff g 0) hcp` as an intermediate fact. Simplify using `only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this`. Rewrite using `[this, Finset.sum_eq_single n]`. Simplify using the standard rewrite rules.

Introduce `b hb hbn`. Establish `: b < n` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn`. Rewrite using `[if_neg (by omega)]`. Introduce `h`. Simplify using `at h`.

Establish `hdet` using `LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω x)`. Rewrite `hdet` using `[← Algebra.norm_apply, ← hf]`. Establish `hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P x`. Rewrite using `[hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]`. Set `V` to `(Rat.padicValuation p).valuationSubring`.

Set `σ` to `{i // i ≠ j}`. Establish `hmemP : ∀ i, l i / l j ∈ P` using `fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩`. Set `tP : σ → P` to `fun i => ⟨l i / l j, hmemP i⟩`. Set `ω : σ → Ω` to `fun i => l i / l j`. Set `_ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ)` to `MvPolynomial.algebraMvPolynomial`.

Set `ψP : MvPolynomial σ V →+* P` to `(aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))`. Set `_ : Algebra (MvPolynomial σ V) P` to `ψP.toAlgebra`. Set `_ : Algebra (MvPolynomial σ V) Ω` to `(P.val.toRingHom.comp ψP).toAlgebra`. Establish `_ : IsScalarTower (MvPolynomial σ V) P Ω` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω` to `{ (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with commutes' := fun r => by show aeval ω _ = P.val (aeval tP _)`.

Conclude with `(DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }`. Establish `hfA : ∀ G, fA G = aeval ω G` using `fun _ => rfl`. Establish `hinj : Function.Injective fA`. Introduce `a b hab`. Conclude with `DehomCharpolyForms.injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)`.

Establish `halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r = aeval ω (map (algebraMap V ℚ) r)` using `fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl`. Set `ν₀ : σ →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun _ => 1`. Set `W : MvPolynomial σ V` to `monomial ν₀ 1`. Set `w : Ω` to `algebraMap (MvPolynomial σ V) Ω W`. Establish `hwq : aeval ω (monomial ν₀ (1 : ℚ)) = w` using `by show _ = algebraMap (MvPolynomial σ V) Ω W`.

Rewrite using `[halg]`. Simplify using `[W, map_monomial]`. Establish `hX : ∀ i : σ, algebraMap (MvPolynomial σ V) Ω (X i) = l i / l j`. Introduce `i`. Rewrite using `[halg]`.

Simplify using `[ω]`. Establish `hcut : ∀ k : σ, ∃ r, algebraMap (MvPolynomial σ V) Ω r * (l k / l j) = w`. Introduce `k`. Use `⟨monomial (ν₀ - Finsupp.single k 1) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hX k, ← map_mul]`.

Use `show _ = algebraMap (MvPolynomial σ V) Ω W`. Use `congr 1`. Establish `hν : (ν₀ - Finsupp.single k 1) + Finsupp.single k 1 = ν₀` using `tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by simp [ν₀]))`. Use `show monomial (ν₀ - Finsupp.single k 1) 1 * monomial (Finsupp.single k 1) 1 = monomial ν₀ 1`. Rewrite using `[monomial_mul, hν, one_mul]`.

Establish `hratio : ∀ i, ∃ r, algebraMap (MvPolynomial σ V) Ω r = l i / l j`. Introduce `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Conclude with `⟨1, by rw [map_one, div_self (hl i)]⟩`.

Conclude with `⟨X ⟨i, h⟩, hX ⟨i, h⟩⟩`. Establish `hinv : ∀ k, ∃ r, algebraMap (MvPolynomial σ V) Ω r = w * (l j / l k)`. Introduce `k`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality.

Conclude with `⟨W, by rw [div_self (hl k), mul_one]⟩`. Take `⟨r, hr⟩` from `hcut ⟨k, h⟩`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr]`. Establish `h1` using `hl k`.

Establish `h2` using `hl j`. Use `show _ = algebraMap (MvPolynomial σ V) Ω r * (l k / l j) * (l j / l k)`. Clear the denominators using the available nonvanishing facts. Establish `hR : ∀ a ∈ Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}), ∃ e : ℕ, ∃ r : MvPolynomial σ V, algebraMap (MvPolynomial σ V) Ω r = w ^ e * a`. Introduce `a ha`.

Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem z hz`. Break down `hz with ⟨i, k, rfl⟩ | ⟨r, hr, rfl⟩` into its components or cases. Take `⟨r1, h1⟩` from `hratio i`. Take `⟨r2, h2⟩` from `hinv k`.

Use `⟨1, r1 * r2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h1, h2, pow_one]`. Establish `h3` using `hl k`. Establish `h4` using `hl j`. Clear the denominators using the available nonvanishing facts.

Use `⟨0, C ⟨(r : ℚ)⁻¹, DehomNormPIntegral.inv_natCast_mem hr⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[halg]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `one => exact ⟨0, 1, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨e1, r1, h1⟩` from `ha`. Take `⟨e2, r2, h2⟩` from `hb`. Use `⟨e1 + e2, W ^ e2 * r1 + W ^ e1 * r2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, h1, h2]`.

Use `show w ^ e2 * _ + w ^ e1 * _ = _`. Expand and normalize the polynomial expressions, which then agree. Consider the case `neg a _ ha`. Take `⟨e1, r1, h1⟩` from `ha`. Conclude with `⟨e1, -r1, by rw [map_neg, h1]; ring⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨e1, r1, h1⟩` from `ha`. Take `⟨e2, r2, h2⟩` from `hb`. Conclude with `⟨e1 + e2, r1 * r2, by rw [map_mul, h1, h2]; ring⟩`. Take `⟨e, hu'⟩` from `isIntegral_pow_mul_of_subring (A := MvPolynomial σ V) _ w ⟨W, rfl⟩ hR ((mem_integralClosure_iff _ _).mp hint)`.

Establish `hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))))` using `(Algebra.isIntegral_norm P hu').algebraMap`. Set `sP : P` to `(algebraMap (MvPolynomial σ V) P W) ^ e * (p : P) ^ K`. Establish `hsP : algebraMap P Ω sP = w ^ e * (p : Ω) ^ K`. Simplify using `only [sP, map_mul, map_pow, map_natCast]`. Both sides reduce to the same expression.

Establish `hnorm : algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))) = (w ^ e * (p : Ω) ^ K) ^ n * algebraMap P Ω (Algebra.norm P x)`. Rewrite using `[← mul_assoc, ← hsP, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]`. Use `set G := PullFormsGeneric.dehom j (c n) with hGdef`. Establish `hdeh : aeval ω G = aeval (fun i => l i / l j) (c n)`. Rewrite using `[hGdef, PullFormsGeneric.aeval_dehom]`.

Use `congrArg (fun g => aeval g (c n)) (funext fun i => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `(div_self (hl _)).symm`. Both sides reduce to the same expression.

Set `E : MvPolynomial σ ℚ` to `monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) * G`. Establish `hEval : fA E = (-1) ^ n * algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x)))`. Establish `hmon : (monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) : MvPolynomial σ ℚ) = C ((p : ℚ) ^ (n * K)) * (monomial ν₀ (1 : ℚ)) ^ (e * n)`. Rewrite using `[monomial_pow, one_pow, C_mul_monomial, mul_one]`. Rewrite using `[hfA, map_mul, hmon, map_mul, aeval_C, map_pow (aeval ω), hwq, hdeh, ← h0, hc0, hnorm]`.

Simplify using `only [map_mul, map_pow, map_neg, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hEint : IsIntegral (MvPolynomial σ V) E`. Use `(isIntegral_algHom_iff fA hinj).mp ?_` and prove the remaining obligations. Rewrite using `[hEval]`.

Conclude with `(isIntegral_one.neg.pow n).mul hN`. Establish `hEc : ∀ ν, E.coeff ν ∈ V.toSubring`. Introduce `ν`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hEint ν)`. Rewrite using `[← hy]`.

Conclude with `y.2`. Establish `hF : (C ((p : ℚ) ^ (n * K)) * c n).IsHomogeneous d`. Simplify using `using (isHomogeneous_C (Fin (D + 1)) ((p : ℚ) ^ (n * K))).mul hchom`. Establish `hG : ∀ ν, (PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n)).coeff ν ∈ V.toSubring`. Introduce `ν`.

Establish `h1 : PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n) = C ((p : ℚ) ^ (n * K)) * G`. Simplify using `[PullFormsGeneric.dehom, hGdef]`. Establish `h2` using `hEc ((e * n) • ν₀ + ν)`. Rewrite `h2` using `[coeff_monomial_mul]`. Rewrite using `[h1, coeff_C_mul]`.

Conclude with `h2`. Establish `hm` using `DehomNormPIntegral.coeff_mem_of_dehom_coeff_mem hgen j hF V.toSubring hG μ`. Rewrite `hm` using `[coeff_C_mul]`. Establish `hv` using `DehomNormPIntegral.padicValRat_nonneg_of_mem hm`. Distinguish the cases in `hc : (c n).coeff μ = 0`.

Rewrite using `[hc, padicValRat.zero]`. Conclude with `neg_nonpos.mpr (Int.natCast_nonneg _)`. Establish `hp0 : (p : ℚ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Rewrite `hv` using `[padicValRat.mul (pow_ne_zero _ hp0) hc, padicValRat.pow _, padicValRat.self hp.one_lt]`. Move the coercions through the operations in `at hv ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem normFormGaussBound : NormFormGaussBound.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp j K d x c hchom hcp hint μ
  classical
  have := Fact.mk hp
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω x) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => Polynomial.coeff g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω x)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P x := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact DehomCharpolyForms.injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  let ν₀ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  let W : MvPolynomial σ V := monomial ν₀ 1
  let w : Ω := algebraMap (MvPolynomial σ V) Ω W
  have hwq : aeval ω (monomial ν₀ (1 : ℚ)) = w := by
    show _ = algebraMap (MvPolynomial σ V) Ω W
    rw [halg]
    simp [W, map_monomial]
  have hX : ∀ i : σ, algebraMap (MvPolynomial σ V) Ω (X i) = l i / l j := by
    intro i
    rw [halg]
    simp [ω]
  have hcut : ∀ k : σ, ∃ r, algebraMap (MvPolynomial σ V) Ω r * (l k / l j) = w := by
    intro k
    refine ⟨monomial (ν₀ - Finsupp.single k 1) 1, ?_⟩
    rw [← hX k, ← map_mul]
    show _ = algebraMap (MvPolynomial σ V) Ω W
    congr 1
    have hν : (ν₀ - Finsupp.single k 1) + Finsupp.single k 1 = ν₀ :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by simp [ν₀]))
    show monomial (ν₀ - Finsupp.single k 1) 1 * monomial (Finsupp.single k 1) 1 = monomial ν₀ 1
    rw [monomial_mul, hν, one_mul]
  have hratio : ∀ i, ∃ r, algebraMap (MvPolynomial σ V) Ω r = l i / l j := by
    intro i
    by_cases h : i = j
    · subst h
      exact ⟨1, by rw [map_one, div_self (hl i)]⟩
    · exact ⟨X ⟨i, h⟩, hX ⟨i, h⟩⟩
  have hinv : ∀ k, ∃ r, algebraMap (MvPolynomial σ V) Ω r = w * (l j / l k) := by
    intro k
    by_cases h : k = j
    · subst h
      exact ⟨W, by rw [div_self (hl k), mul_one]⟩
    · obtain ⟨r, hr⟩ := hcut ⟨k, h⟩
      refine ⟨r, ?_⟩
      rw [← hr]
      have h1 := hl k
      have h2 := hl j
      show _ = algebraMap (MvPolynomial σ V) Ω r * (l k / l j) * (l j / l k)
      field_simp

  have hR : ∀ a ∈ Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}),
      ∃ e : ℕ, ∃ r : MvPolynomial σ V, algebraMap (MvPolynomial σ V) Ω r = w ^ e * a := by
    intro a ha
    induction ha using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨i, k, rfl⟩ | ⟨r, hr, rfl⟩
      · obtain ⟨r1, h1⟩ := hratio i
        obtain ⟨r2, h2⟩ := hinv k
        refine ⟨1, r1 * r2, ?_⟩
        rw [map_mul, h1, h2, pow_one]
        have h3 := hl k
        have h4 := hl j
        field_simp
      · refine ⟨0, C ⟨(r : ℚ)⁻¹, DehomNormPIntegral.inv_natCast_mem hr⟩, ?_⟩
        rw [halg]
        simp
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨e1, r1, h1⟩ := ha
      obtain ⟨e2, r2, h2⟩ := hb
      refine ⟨e1 + e2, W ^ e2 * r1 + W ^ e1 * r2, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, h1, h2]
      show w ^ e2 * _ + w ^ e1 * _ = _
      ring
    | neg a _ ha =>
      obtain ⟨e1, r1, h1⟩ := ha
      exact ⟨e1, -r1, by rw [map_neg, h1]; ring⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e1, r1, h1⟩ := ha
      obtain ⟨e2, r2, h2⟩ := hb
      exact ⟨e1 + e2, r1 * r2, by rw [map_mul, h1, h2]; ring⟩
  obtain ⟨e, hu'⟩ := isIntegral_pow_mul_of_subring (A := MvPolynomial σ V) _ w ⟨W, rfl⟩ hR
    ((mem_integralClosure_iff _ _).mp hint)

  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x)))) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  let sP : P := (algebraMap (MvPolynomial σ V) P W) ^ e * (p : P) ^ K
  have hsP : algebraMap P Ω sP = w ^ e * (p : Ω) ^ K := by
    simp only [sP, map_mul, map_pow, map_natCast]
    rfl
  have hnorm : algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))) =
      (w ^ e * (p : Ω) ^ K) ^ n * algebraMap P Ω (Algebra.norm P x) := by
    rw [← mul_assoc, ← hsP, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
  set G := PullFormsGeneric.dehom j (c n) with hGdef
  have hdeh : aeval ω G = aeval (fun i => l i / l j) (c n) := by
    rw [hGdef, PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  let E : MvPolynomial σ ℚ := monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) * G
  have hEval : fA E = (-1) ^ n * algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))) := by
    have hmon : (monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) : MvPolynomial σ ℚ) =
        C ((p : ℚ) ^ (n * K)) * (monomial ν₀ (1 : ℚ)) ^ (e * n) := by
      rw [monomial_pow, one_pow, C_mul_monomial, mul_one]
    rw [hfA, map_mul, hmon, map_mul, aeval_C, map_pow (aeval ω), hwq, hdeh, ← h0, hc0, hnorm]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  have hEint : IsIntegral (MvPolynomial σ V) E := by
    refine (isIntegral_algHom_iff fA hinj).mp ?_
    rw [hEval]
    exact (isIntegral_one.neg.pow n).mul hN
  have hEc : ∀ ν, E.coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hEint ν)
    rw [← hy]
    exact y.2
  have hF : (C ((p : ℚ) ^ (n * K)) * c n).IsHomogeneous d := by
    simpa using (isHomogeneous_C (Fin (D + 1)) ((p : ℚ) ^ (n * K))).mul hchom
  have hG : ∀ ν, (PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n)).coeff ν ∈ V.toSubring := by
    intro ν
    have h1 : PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n) = C ((p : ℚ) ^ (n * K)) * G := by
      simp [PullFormsGeneric.dehom, hGdef]
    have h2 := hEc ((e * n) • ν₀ + ν)
    rw [coeff_monomial_mul] at h2
    rw [h1, coeff_C_mul]
    exact h2
  have hm := DehomNormPIntegral.coeff_mem_of_dehom_coeff_mem hgen j hF V.toSubring hG μ
  rw [coeff_C_mul] at hm
  have hv := DehomNormPIntegral.padicValRat_nonneg_of_mem hm
  by_cases hc : (c n).coeff μ = 0
  · rw [hc, padicValRat.zero]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hp0) hc, padicValRat.pow _, padicValRat.self hp.one_lt] at hv
    push_cast at hv ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
