import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (c : E)`. Rewrite `h` using `[show (u.valuation E) (c : E) = u.intValuation c from HeightOneSpectrum.valuation_of_algebraMap u c]`. Conclude with `h`.
-/
private theorem val_alg (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) = u.intValuation c := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (c : E)
  rw [show (u.valuation E) (c : E) = u.intValuation c from HeightOneSpectrum.valuation_of_algebraMap u c] at h
  exact h

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, val_alg]`. Conclude with `u.intValuation_le_one c`.
-/
private theorem alg_int (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    algebraMap (𝓞 E) (u.adicCompletion E) c ∈ u.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_alg]
  exact u.intValuation_le_one c

/- English proof (translation)
Establish `hI : Ideal.span {c} ≠ ⊥` using `by simpa using hc`. Use `w.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hIQ⟩` from `Ideal.eq_prime_pow_mul_coprime hI w.asIdeal`. Establish `hex : ∃ s ∈ Q, s ∉ w.asIdeal`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `: Q ≤ w.asIdeal` using `hcon`. Rewrite `hQ` using `[sup_eq_left.2 this]`. Conclude with `w.isPrime.ne_top hQ`. Take `⟨s, hsQ, hsw⟩` from `hex`.

Use `⟨s, hsw, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[val_alg, val_alg]`. Rewrite using `[HeightOneSpectrum.intValuation_if_neg u hc]`. Use `(HeightOneSpectrum.intValuation_le_pow_iff_mem u s _).2 ?_` and prove the remaining obligations. Use `set e := (Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he`.

Establish `hce : c ∈ u.asIdeal ^ e`. Use `(HeightOneSpectrum.intValuation_le_pow_iff_mem u c e).1 ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.intValuation_if_neg u hc]`. Establish `hle : Ideal.span {c} ≤ u.asIdeal ^ e` using `(Ideal.span_singleton_le_iff_mem _).2 hce`. Generalize the expression as in `Multiset.count w.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})) = m at hIQ`.

Establish `hdvd : u.asIdeal ^ e ∣ w.asIdeal ^ m * Q`. Rewrite using `[← hIQ]`. Conclude with `Ideal.dvd_iff_le.2 hle`. Establish `hcop : IsCoprime (u.asIdeal ^ e) (w.asIdeal ^ m)`. Use `IsCoprime.pow ?_` and prove the remaining obligations.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal (fun h => hu (HeightOneSpectrum.ext h))`. Conclude with `Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_left hdvd) hsQ`.
-/
private theorem exS (w : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ u : HeightOneSpectrum (𝓞 E), u ≠ w →
      Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s) ≤ Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) := by
  classical
  have hI : Ideal.span {c} ≠ ⊥ := by simpa using hc
  have := w.isMaximal
  obtain ⟨Q, hQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hI w.asIdeal
  have hex : ∃ s ∈ Q, s ∉ w.asIdeal := by
    by_contra hcon
    push_neg at hcon
    have : Q ≤ w.asIdeal := hcon
    rw [sup_eq_left.2 this] at hQ
    exact w.isPrime.ne_top hQ
  obtain ⟨s, hsQ, hsw⟩ := hex
  refine ⟨s, hsw, fun u hu => ?_⟩
  rw [val_alg, val_alg]
  rw [HeightOneSpectrum.intValuation_if_neg u hc]
  refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u s _).2 ?_
  set e := (Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hce : c ∈ u.asIdeal ^ e := by
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u c e).1 ?_
    rw [HeightOneSpectrum.intValuation_if_neg u hc]
  have hle : Ideal.span {c} ≤ u.asIdeal ^ e := (Ideal.span_singleton_le_iff_mem _).2 hce
  generalize Multiset.count w.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})) = m at hIQ
  have hdvd : u.asIdeal ^ e ∣ w.asIdeal ^ m * Q := by
    rw [← hIQ]; exact Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime (u.asIdeal ^ e) (w.asIdeal ^ m) := by
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal (fun h => hu (HeightOneSpectrum.ext h))
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_left hdvd) hsQ

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha`. Establish `e : t * (a * h * a⁻¹).val i k = (a.val * (t • h.val) * (a⁻¹).val) i k`. Simplify using `only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[e, Matrix.mul_apply]`. Use `sum_mem fun l _ => mul_mem ?_ (h2 _ _)` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun m _ => mul_mem (h1 _ _) (ht _ _)`.
-/
private theorem conj_int [IsCMField E] {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (a h : GL (Fin n) (u.adicCompletion E)) (ha : a ∈ KGL u n)
    (t : u.adicCompletion E) (ht : ∀ i k, (t • h.val) i k ∈ u.adicCompletionIntegers E) (i k : Fin n) :
    t * (a * h * a⁻¹).val i k ∈ u.adicCompletionIntegers E := by
  obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha
  have e : t * (a * h * a⁻¹).val i k = (a.val * (t • h.val) * (a⁻¹).val) i k := by
    simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ (h2 _ _)
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem (h1 _ _) (ht _ _)

/- English proof (translation)
Rewrite using `[Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]`. Use `split_ifs with h1 h2`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, val_alg]`. Establish `h3 : u.intValuation y ≤ Valued.v ϖ`. Rewrite using `[hϖ]`.

Use `(HeightOneSpectrum.intValuation_le_pow_iff_mem u y 1).2 (by rwa [pow_one])` as an intermediate fact. Conclude with `this`. Conclude with `mul_inv_le_one_of_le₀ h3 zero_le'`. Rewrite using `[mul_one]`. Conclude with `alg_int u y`.

Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.
-/
private theorem diag_int {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (ϖ : u.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E u ϖ) (i : ℕ)
    (y : 𝓞 E) (hy : y ∈ u.asIdeal) (a b : Fin n) :
    (algebraMap (𝓞 E) (u.adicCompletion E) y •
      Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) a b ∈ u.adicCompletionIntegers E := by
  rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h1 h2
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, val_alg]
    have h3 : u.intValuation y ≤ Valued.v ϖ := by
      rw [hϖ]
      have := (HeightOneSpectrum.intValuation_le_pow_iff_mem u y 1).2 (by rwa [pow_one])
      exact this
    exact mul_inv_le_one_of_le₀ h3 zero_le'
  · rw [mul_one]; exact alg_int u y
  · rw [mul_zero]; exact zero_mem _

end UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

open UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling in
/- English proof (translation)
Introduce `hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg`. Establish `hqp` using `σ.atp.prime`. Establish `hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal` using `σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))`. Establish `hN0 : Ideal.absNorm w.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `w.ne_bot`. Establish `hc : ((Ideal.absNorm w.asIdeal ^ i : ℕ) : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)`. Take `⟨s, hsw, hs⟩` from `exS w _ hc`. Use `⟨s, hsw, fun y hy v hv => ?_⟩` and prove the remaining obligations. Establish `key : ∀ (u : Plc E) (a b : Fin n), algebraMap (𝓞 E) (u.adicCompletion E) (s * y) * F.cmp u g⁻¹ a b ∈ u.adicCompletionIntegers E`.

Introduce `u a b`. Distinguish the cases in `hqu : ((σ.q : ℕ) : 𝓞 E) ∈ u.asIdeal`. Establish `ha` using `F.a_int u σ.q hqp σ.good hqu`. Distinguish the cases in `huw : u = w`. Substitute `huw` using the available equality.

Take `⟨ϖ, hϖ, ht⟩` from `hg.at_w`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ` using `[Formalism.UG.IsUnifV, h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`.

Establish `hinv : (comp u g⁻¹).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1`. Establish `h1 : (comp u g⁻¹).val * (comp u g).val = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `h2 : (comp u g).val * (Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) = 1`. Rewrite using `[ht, Matrix.diagonal_mul_diagonal]`.

Establish `hk : ∀ k : Fin n, (if (k : ℕ) < i then ϖ else 1) * (if (k : ℕ) < i then ϖ⁻¹ else 1) = (1 : u.adicCompletion E)`. Introduce `k`. Use `split_ifs`. Conclude with `mul_inv_cancel₀ (G₀ := u.adicCompletion E) hϖ0`. Conclude with `mul_one 1`.

Simplify using `only [hk]`. Conclude with `Matrix.diagonal_one`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, mul_assoc]`. Use `mul_mem (alg_int u s) (conj_int u _ _ ha _ (fun a b => ?_) a b)` and prove the remaining obligations.

Rewrite using `[hinv]`. Conclude with `diag_int u ϖ hϖ i y hy a b`. Establish `h1` using `conj_int u (F.a u) (comp u g⁻¹) ha ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) (hg.back u) a b`. Rewrite `h1`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[map_mul, map_mul, map_mul, mul_comm (Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s)), mul_assoc]`.

Establish `h2` using `hs u huw`. Rewrite `h2` using `[map_natCast]`. Establish `h3 : Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) y) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (alg_int u y)`. Rewrite `h1` using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hne : u ≠ w` using `fun h => hqu (h ▸ hqw)`. Establish `hoff : comp u g = 1` using `hg.off u hne fun hK => hqu ?_`. Establish `h1 : F.cmp u g⁻¹ = 1`. Simplify using `[Frame.cmp, map_inv, hoff]`. Rewrite using `[h1, Matrix.one_apply]`.

Use `split_ifs`. Rewrite using `[mul_one]`. Conclude with `alg_int u _`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.

Establish `hq' : ((σ.q : ℕ) : 𝓞 E) ∈ (cj u).asIdeal` using `(hK _ (by simp)).2 hqw`. Establish `e : (cj u).asIdeal = _` using `(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)`. Rewrite `hq'` using `[e, Ideal.mem_comap, map_natCast]`. Conclude with `hq'`. Set `Y : ∀ u : Plc E, Fin n → u.adicCompletion E` to `fun u => if (p : 𝓞 E) ∈ u.asIdeal then 0 else algebraMap (𝓞 E) (u.adicCompletion E) (s * y) • (F.cmp u g⁻¹ *ᵥ F.vec u (v))`.

Establish `hY : ∀ u k, Y u k ∈ u.adicCompletionIntegers E`. Introduce `u k`. Distinguish the cases in `hp : (p : 𝓞 E) ∈ u.asIdeal`. Simplify using `only [Y, if_pos hp]`. Conclude with `zero_mem _`.

Simplify using `only [Y, if_neg hp, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]`. Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `mul_mem (key u k l) ((F.vec_hat v).1 hv u hp l)`. Take `⟨v', hv'⟩` from `F.vec_surj Y hY`.

Use `⟨v', (F.vec_hat v').2 fun u hu k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv' u hu]`. Conclude with `hY u k`. Use `sub_eq_zero.1 (F.vec_inj _ fun u hu => ?_)` and prove the remaining obligations. Establish `hmul : (F.a u * comp u g * (F.a u)⁻¹).val * F.cmp u g⁻¹ = 1`.

Rewrite using `[Frame.cmp, ← Units.val_mul, map_inv]`. Simplify using the standard rewrite rules. Rewrite using `[map_sub, F.vec_act u hu, F.vec_mul u hu, hv' u hu]`. Simplify using `only [Y, if_neg hu]`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, sub_self]`.
-/
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tKill :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TKill := by
  intro hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg
  have hqp := σ.atp.prime
  have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hc : ((Ideal.absNorm w.asIdeal ^ i : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)
  obtain ⟨s, hsw, hs⟩ := exS w _ hc
  refine ⟨s, hsw, fun y hy v hv => ?_⟩
  have key : ∀ (u : Plc E) (a b : Fin n), algebraMap (𝓞 E) (u.adicCompletion E) (s * y) * F.cmp u g⁻¹ a b ∈ u.adicCompletionIntegers E := by
    intro u a b
    by_cases hqu : ((σ.q : ℕ) : 𝓞 E) ∈ u.asIdeal
    · have ha := F.a_int u σ.q hqp σ.good hqu
      by_cases huw : u = w
      · subst huw
        obtain ⟨ϖ, hϖ, ht⟩ := hg.at_w
        have hϖ0 : ϖ ≠ 0 := by
          intro h0
          rw [Formalism.UG.IsUnifV, h0, map_zero] at hϖ
          exact WithZero.zero_ne_coe hϖ
        have hinv : (comp u g⁻¹).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1 := by
          have h1 : (comp u g⁻¹).val * (comp u g).val = 1 := by
            rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
          have h2 : (comp u g).val * (Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) = 1 := by
            rw [ht, Matrix.diagonal_mul_diagonal]
            have hk : ∀ k : Fin n, (if (k : ℕ) < i then ϖ else 1) * (if (k : ℕ) < i then ϖ⁻¹ else 1) = (1 : u.adicCompletion E) := by
              intro k
              split_ifs
              · exact mul_inv_cancel₀ (G₀ := u.adicCompletion E) hϖ0
              · exact mul_one 1
            simp only [hk]
            exact Matrix.diagonal_one
          calc (comp u g⁻¹).val = (comp u g⁻¹).val * ((comp u g).val * _) := by rw [h2, Matrix.mul_one]
            _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rw [map_mul, mul_assoc]
        refine mul_mem (alg_int u s) (conj_int u _ _ ha _ (fun a b => ?_) a b)
        rw [hinv]
        exact diag_int u ϖ hϖ i y hy a b
      · have h1 := conj_int u (F.a u) (comp u g⁻¹) ha ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) (hg.back u) a b
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
        rw [map_mul, map_mul, map_mul, mul_comm (Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s)), mul_assoc]
        have h2 := hs u huw
        rw [map_natCast] at h2
        have h3 : Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) y) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (alg_int u y)
        rw [map_mul] at h1
        calc _ ≤ 1 * (Valued.v (((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E)) * Valued.v (F.cmp u g⁻¹ a b)) :=
              mul_le_mul' h3 (mul_le_mul' h2 le_rfl)
          _ ≤ 1 := by rw [one_mul]; exact h1
    · have hne : u ≠ w := fun h => hqu (h ▸ hqw)
      have hoff : comp u g = 1 := hg.off u hne fun hK => hqu ?_
      · have h1 : F.cmp u g⁻¹ = 1 := by
          simp [Frame.cmp, map_inv, hoff]
        rw [h1, Matrix.one_apply]
        split_ifs
        · rw [mul_one]; exact alg_int u _
        · rw [mul_zero]; exact zero_mem _
      · have hq' : ((σ.q : ℕ) : 𝓞 E) ∈ (cj u).asIdeal := (hK _ (by simp)).2 hqw
        have e : (cj u).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
        rw [e, Ideal.mem_comap, map_natCast] at hq'
        exact hq'
  classical
  let Y : ∀ u : Plc E, Fin n → u.adicCompletion E := fun u =>
    if (p : 𝓞 E) ∈ u.asIdeal then 0 else algebraMap (𝓞 E) (u.adicCompletion E) (s * y) • (F.cmp u g⁻¹ *ᵥ F.vec u (v))
  have hY : ∀ u k, Y u k ∈ u.adicCompletionIntegers E := by
    intro u k
    by_cases hp : (p : 𝓞 E) ∈ u.asIdeal
    · simp only [Y, if_pos hp]; exact zero_mem _
    · simp only [Y, if_neg hp, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun l _ => ?_
      rw [← mul_assoc]
      exact mul_mem (key u k l) ((F.vec_hat v).1 hv u hp l)
  obtain ⟨v', hv'⟩ := F.vec_surj Y hY
  refine ⟨v', (F.vec_hat v').2 fun u hu k => ?_, ?_⟩
  · rw [hv' u hu]; exact hY u k
  · refine sub_eq_zero.1 (F.vec_inj _ fun u hu => ?_)
    have hmul : (F.a u * comp u g * (F.a u)⁻¹).val * F.cmp u g⁻¹ = 1 := by
      rw [Frame.cmp, ← Units.val_mul, map_inv]
      simp
    rw [map_sub, F.vec_act u hu, F.vec_mul u hu, hv' u hu]
    simp only [Y, if_neg hu]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, sub_self]
