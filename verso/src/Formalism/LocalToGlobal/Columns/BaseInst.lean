import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
import Formalism.LocalToGlobal.UnitaryNorms.Lemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

instance fin_KQ (d : ℕ) : FiniteDimensional ℚ (KQ d) := fin_sqQ _

instance normal_KQ (d : ℕ) : Normal ℚ (KQ d) := normal_sqQ _

def quadFields (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL) : Fields where
  F := ℚ
  E := KQ d
  K := CoF ι LL
  nfE := { to_charZero := inferInstance, to_finiteDimensional := fin_KQ d }
  starE := starLL ι (KQ d)
  Tau := Unit
  emb := fun _ => (tauLL hE (KQ d).val).toRingHom

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_sqrt (-(d : ℤ))`. Establish `hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb)` using `hw`. Establish `hint : IsIntegral ℚ w` using `Algebra.IsIntegral.isIntegral w`. Unfold `KQ`. Rewrite using `[sqQ_eq hw2, adjoin.finrank hint]`.

Apply `le_antisymm` to reduce the goal to its premises. Establish `hdvd : minpoly ℚ w ∣ (Polynomial.X ^ 2 + Polynomial.C (d : ℚ))`. Apply `minpoly.dvd` to reduce the goal to its premises. Simplify using `[hw2]`. Establish `hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2` using `by compute_degree!`.

Establish `hne : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) ≠ 0`. Introduce `h`. Rewrite `hdeg` using `[h]`. Simplify using `at hdeg`. Rewrite using `[← hdeg]`.

Conclude with `Polynomial.natDegree_le_of_dvd hdvd hne`. Rewrite using `[minpoly.two_le_natDegree_iff hint]`. Introduce and unpack `⟨r, hr⟩`. Establish `h1 : ((r ^ 2 : ℚ) : Qb) = ((-(d : ℚ) : ℚ) : Qb)`. Establish `: (algebraMap ℚ Qb r) ^ 2 = ((-(d : ℤ) : ℤ) : Qb)` using `by rw [hr]; exact hw2`.

Move the coercions through the operations in `at this ⊢`. Simplify using `using this`. Establish `h2 : r ^ 2 = -(d : ℚ)` using `by exact_mod_cast h1`. Establish `h3 : (0 : ℚ) < d` using `by exact_mod_cast hd`. Use polynomial arithmetic with `[sq_nonneg r]`.
-/
theorem finrank_KQ {d : ℕ} (hd : 0 < d) : Module.finrank ℚ (KQ d) = 2 := by
  obtain ⟨w, hw⟩ := exists_sqrt (-(d : ℤ))
  have hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hw
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  unfold KQ
  rw [sqQ_eq hw2, adjoin.finrank hint]
  apply le_antisymm
  · have hdvd : minpoly ℚ w ∣ (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
      apply minpoly.dvd
      simp [hw2]
    have hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2 := by
      compute_degree!
    have hne : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) ≠ 0 := by
      intro h; rw [h] at hdeg; simp at hdeg
    rw [← hdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hne
  · rw [minpoly.two_le_natDegree_iff hint]
    rintro ⟨r, hr⟩
    have h1 : ((r ^ 2 : ℚ) : Qb) = ((-(d : ℚ) : ℚ) : Qb) := by
      have : (algebraMap ℚ Qb r) ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := by rw [hr]; exact hw2
      push_cast at this ⊢
      simpa using this
    have h2 : r ^ 2 = -(d : ℚ) := by exact_mod_cast h1
    have h3 : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]

section QuadOk

variable (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL)

def quadInc : KQ d →+* CoF ι LL := (tauLL hE (KQ d).val).toRingHom

/- English proof (translation)
The claim follows from `tauLL_coe hE (KQ d).val x`.
-/
theorem quadInc_val (x : KQ d) : CoF.val ι LL (quadInc d ι LL hE x) = (x : Qb) :=
  tauLL_coe hE (KQ d).val x

/- English proof (translation)
Use `algHom_ext_of_eq_adjoin _ (rfl : KQ d = adjoin ℚ (sqrts (-(d : ℤ)))) ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hz' : z ^ 2 = w ^ 2`. Rewrite using `[show z ^ 2 = ((-(d : ℤ) : ℤ) : Qb) from hz, show w ^ 2 = ((-(d : ℤ) : ℤ) : Qb) from hw]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hz' with h1 | h1` into its components or cases.

Substitute `h1` using the available equality. Conclude with `h`. Substitute `h1` using the available equality. Conclude with `(map_neg s ⟨w, sqrts_sub _ hw⟩).trans ((congrArg Neg.neg h).trans (map_neg s' ⟨w, sqrts_sub _ hw⟩).symm)`.
-/
theorem quad_ext {w : Qb} (hw : w ∈ sqrts (-(d : ℤ))) (s s' : KQ d →ₐ[ℚ] Qb)
    (h : s ⟨w, sqrts_sub _ hw⟩ = s' ⟨w, sqrts_sub _ hw⟩) : s = s' := by
  refine algHom_ext_of_eq_adjoin _ (rfl : KQ d = adjoin ℚ (sqrts (-(d : ℤ)))) ?_
  intro z hz
  have hz' : z ^ 2 = w ^ 2 := by
    rw [show z ^ 2 = ((-(d : ℤ) : ℤ) : Qb) from hz, show w ^ 2 = ((-(d : ℤ) : ℤ) : Qb) from hw]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz' with h1 | h1
  · subst h1; exact h
  · subst h1
    exact (map_neg s ⟨w, sqrts_sub _ hw⟩).trans ((congrArg Neg.neg h).trans (map_neg s' ⟨w, sqrts_sub _ hw⟩).symm)

/- English proof (translation)
Take `⟨τ, hτ⟩` from `exists_ext ι (KQ d) φ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem quad_conjE (φ : KQ d →+* ℂ) (x : KQ d) : φ (cLL ι (KQ d) x) = starRingEnd ℂ (φ x) := by
  obtain ⟨τ, hτ⟩ := exists_ext ι (KQ d) φ
  calc φ (cLL ι (KQ d) x) = τ ((cLL ι (KQ d) x : KQ d) : Qb) := (hτ _).symm
    _ = τ (conjQb ι x) := congrArg τ (cLL_coe ι (KQ d) x)
    _ = starRingEnd ℂ (τ x) := sqLeCm ι _ x.2 τ
    _ = starRingEnd ℂ (φ x) := congrArg _ (hτ x)

/- English proof (translation)
Apply `CoF.val_injective ι LL` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem quad_emb_star (x : KQ d) :
    quadInc d ι LL hE (cLL ι (KQ d) x) = (star (quadInc d ι LL hE x) : CoF ι LL) := by
  apply CoF.val_injective ι LL
  calc CoF.val ι LL (quadInc d ι LL hE (cLL ι (KQ d) x)) = ((cLL ι (KQ d) x : KQ d) : Qb) := quadInc_val d ι LL hE _
    _ = conjQb ι x := cLL_coe ι (KQ d) x
    _ = conjQb ι (CoF.val ι LL (quadInc d ι LL hE x)) := congrArg _ (quadInc_val d ι LL hE x).symm
    _ = CoF.val ι LL (star (quadInc d ι LL hE x)) := (CoF.val_star ι LL _).symm

/- English proof (translation)
Establish `hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb)` using `hw`. Establish `hneg : (-(d : ℝ)) < 0`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast hd`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hιw : (ι w) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ)`.

Rewrite using `[← map_pow, hw2, map_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Apply `conj_ne_of_sq_neg hneg hιw` to reduce the goal to its premises.

Rewrite using `[← conjQb_spec, h]`.
-/
theorem conj_sqrt_ne {d : ℕ} (hd : 0 < d) {w : Qb} (hw : w ∈ sqrts (-(d : ℤ))) : conjQb ι w ≠ w := by
  have hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hw
  have hneg : (-(d : ℝ)) < 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hιw : (ι w) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ) := by
    rw [← map_pow, hw2, map_intCast]; push_cast; ring
  intro h
  apply conj_ne_of_sq_neg hneg hιw
  rw [← conjQb_spec, h]

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_sqrt (-(d : ℤ))`. Apply `conj_sqrt_ne ι hd hw` to reduce the goal to its premises. Establish `h1` using `congrArg (CoF.val ι LL) (h ⟨w, sqrts_sub _ hw⟩)`. Conclude with `((cLL_coe ι (KQ d) ⟨w, sqrts_sub _ hw⟩).symm.trans (quadInc_val d ι LL hE _).symm).trans (h1.symm.trans (quadInc_val d ι LL hE _))`.
-/
theorem quad_emb_ne (hd : 0 < d) (h : ∀ x : KQ d, quadInc d ι LL hE x = quadInc d ι LL hE (cLL ι (KQ d) x)) : False := by
  obtain ⟨w, hw⟩ := exists_sqrt (-(d : ℤ))
  apply conj_sqrt_ne ι hd hw
  have h1 := congrArg (CoF.val ι LL) (h ⟨w, sqrts_sub _ hw⟩)
  exact ((cLL_coe ι (KQ d) ⟨w, sqrts_sub _ hw⟩).symm.trans (quadInc_val d ι LL hE _).symm).trans
    (h1.symm.trans (quadInc_val d ι LL hE _))

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_sqrt (-(d : ℤ))`. Establish `hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb)` using `hw`. Establish `hcw` using `conj_sqrt_ne ι hd hw`. Set `s : KQ d →ₐ[ℚ] Qb` to `RingHom.toRatAlgHom ((CoF.val ι LL).comp φ)`. Establish `hs : ∀ x, s x = CoF.val ι LL (φ x)` using `fun _ => rfl`.

Establish `hsw : (s ⟨w, sqrts_sub _ hw⟩) ^ 2 = w ^ 2`. Establish `e1 : (⟨w, sqrts_sub _ hw⟩ : KQ d) ^ 2 = ((-(d : ℤ) : ℤ) : KQ d)` using `Subtype.val_injective (by show w ^ 2 = _`. Rewrite using `[hw2]`. Use the proof step `simp)`. Conclude with `(map_pow s _ 2).symm.trans ((congrArg s e1).trans ((map_intCast s _).trans hw2.symm))`.

Establish `hcw2 : conjQb ι w = -w`. Establish `: (conjQb ι w) ^ 2 = w ^ 2` using `by rw [← map_pow, hw2, map_intCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h` into its components or cases. Conclude with `absurd h hcw`. Conclude with `h`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsw with h | h` into its components or cases. Use `left`. Establish `e : s = (KQ d).val` using `quad_ext d hw s _ h`. Introduce `x`. Apply `CoF.val_injective ι LL` to reduce the goal to its premises.

Conclude with `(hs x).symm.trans ((DFunLike.congr_fun e x).trans (quadInc_val d ι LL hE x).symm)`. Use `right`. Establish `e : s = (KQ d).val.comp ((cLL ι (KQ d) : KQ d ≃ₐ[ℚ] KQ d) : KQ d →ₐ[ℚ] KQ d)`. Apply `quad_ext d hw` to reduce the goal to its premises. Conclude with `h.trans (hcw2.symm.trans (cLL_coe ι (KQ d) ⟨w, sqrts_sub _ hw⟩).symm)`.

Introduce `x`. Apply `CoF.val_injective ι LL` to reduce the goal to its premises. Conclude with `(hs x).symm.trans ((DFunLike.congr_fun e x).trans (quadInc_val d ι LL hE _).symm)`.
-/
theorem quad_emb_all (hd : 0 < d) (φ : KQ d →+* CoF ι LL) :
    (∀ x, φ x = quadInc d ι LL hE x) ∨ ∀ x, φ x = quadInc d ι LL hE (cLL ι (KQ d) x) := by
  obtain ⟨w, hw⟩ := exists_sqrt (-(d : ℤ))
  have hw2 : w ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hw
  have hcw := conj_sqrt_ne ι hd hw
  let s : KQ d →ₐ[ℚ] Qb := RingHom.toRatAlgHom ((CoF.val ι LL).comp φ)
  have hs : ∀ x, s x = CoF.val ι LL (φ x) := fun _ => rfl
  have hsw : (s ⟨w, sqrts_sub _ hw⟩) ^ 2 = w ^ 2 := by
    have e1 : (⟨w, sqrts_sub _ hw⟩ : KQ d) ^ 2 = ((-(d : ℤ) : ℤ) : KQ d) := Subtype.val_injective (by
      show w ^ 2 = _
      rw [hw2]; simp)
    exact (map_pow s _ 2).symm.trans ((congrArg s e1).trans ((map_intCast s _).trans hw2.symm))
  have hcw2 : conjQb ι w = -w := by
    have : (conjQb ι w) ^ 2 = w ^ 2 := by rw [← map_pow, hw2, map_intCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
    · exact absurd h hcw
    · exact h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsw with h | h
  · left
    have e : s = (KQ d).val := quad_ext d hw s _ h
    intro x
    apply CoF.val_injective ι LL
    exact (hs x).symm.trans ((DFunLike.congr_fun e x).trans (quadInc_val d ι LL hE x).symm)
  · right
    have e : s = (KQ d).val.comp ((cLL ι (KQ d) : KQ d ≃ₐ[ℚ] KQ d) : KQ d →ₐ[ℚ] KQ d) := by
      apply quad_ext d hw
      exact h.trans (hcw2.symm.trans (cLL_coe ι (KQ d) ⟨w, sqrts_sub _ hw⟩).symm)
    intro x
    apply CoF.val_injective ι LL
    exact (hs x).symm.trans ((DFunLike.congr_fun e x).trans (quadInc_val d ι LL hE _).symm)

/- English proof (translation)
The claim follows from `inferInstanceAs (IsTotallyReal ℚ) rankE := finrank_KQ hd star_F := fun x => (congrArg (cLL ι (KQ d)) (eq_ratCast (algebraMap ℚ (KQ d)) x)).trans ((map_ratCast (cLL ι (KQ d)) x).trans (eq_ratCast (algebraMap ℚ (KQ d)) x).symm) conjE := quad_conjE d ι cplxE := totComplex ι (KQ d) d …`.
-/
theorem quadFields_ok (hd : 0 < d) : (quadFields d ι LL hE).Ok where
  realF := inferInstanceAs (IsTotallyReal ℚ)
  rankE := finrank_KQ hd
  star_F := fun x => (congrArg (cLL ι (KQ d)) (eq_ratCast (algebraMap ℚ (KQ d)) x)).trans
    ((map_ratCast (cLL ι (KQ d)) x).trans (eq_ratCast (algebraMap ℚ (KQ d)) x).symm)
  conjE := quad_conjE d ι
  cplxE := totComplex ι (KQ d) d hd le_rfl
  emb_star := fun _ x => quad_emb_star d ι LL hE x
  card_Tau := (Module.finrank_self ℚ).symm
  emb_inj := fun _ _ _ => rfl
  emb_ne := fun _ _ h => quad_emb_ne d ι LL hE hd fun x => RingHom.congr_fun h x
  emb_all := fun φ => ⟨(), (quad_emb_all d ι LL hE hd φ).imp (fun h => RingHom.ext h) (fun h => RingHom.ext h)⟩
  cplxK := totComplex ι LL d hd hE
  normalK := ‹Normal ℚ LL›
  conjK := ⟨sig0 ι LL, sig0Conj ι LL⟩
  quad := by
    have htop : ∀ x : (quadFields d ι LL hE).E, x ∈ (quadFields d ι LL hE).Kq := fun x _ _ => rfl
    let f : (quadFields d ι LL hE).Kq →ₗ[ℚ] KQ d := (RingHom.toRatAlgHom (quadFields d ι LL hE).Kq.subtype).toLinearMap
    have hf : Function.Bijective f := ⟨Subtype.val_injective, fun x => ⟨⟨x, htop x⟩, rfl⟩⟩
    exact (LinearEquiv.ofBijective f hf).finrank_eq.trans (finrank_KQ hd)

end QuadOk

section DegTwo

variable (X : Fields)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjO_coe (x : 𝓞 X.E) : ((X.conjO x : 𝓞 X.E) : X.E) = star (x : X.E) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[conjO_coe, conjO_coe, star_star]`.
-/
theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `h : (p : 𝓞 X.E) = algebraMap ℤ (𝓞 X.E) (p : ℤ)` using `by simp`. Rewrite using `[h, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]`. Simplify using `[Int.natAbs_pow]`.
-/
theorem absNorm_natCast (hrank : Module.finrank ℚ X.E = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 X.E)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (p : 𝓞 X.E) = algebraMap ℤ (𝓞 X.E) (p : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
  simp [Int.natAbs_pow]

/- English proof (translation)
Establish `hp0 : (p : 𝓞 X.E) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_mul]`. Conclude with `hp0 h.symm`.

Establish `hmul : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {X.conjO π}) = p ^ 2`. Rewrite using `[← map_mul, Ideal.span_singleton_mul_span_singleton, h, absNorm_natCast X hrank]`. Establish `hpu : ¬ IsUnit (p : 𝓞 X.E)`. Introduce `hu`. Establish `h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 X.E)}) = 1`.

Rewrite using `[Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]`. Conclude with `hu`. Rewrite `h1` using `[absNorm_natCast X hrank]`. Use `hp.one_lt` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hu1 : Ideal.absNorm (Ideal.span {π}) ≠ 1`. Introduce `h1`. Rewrite `h1` using `[Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]`. Conclude with `hpu (h ▸ h1.mul (h1.map X.conjO))`. Establish `hu2 : Ideal.absNorm (Ideal.span {X.conjO π}) ≠ 1`.

Introduce `h1`. Rewrite `h1` using `[Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]`. Establish `h2 : IsUnit π`. Use `h1.map X.conjO` as an intermediate fact. Rewrite `this` using `[conjO_conjO]`. Then use the resulting hypothesis.

Conclude with `hpu (h ▸ h2.mul h1)`. Establish `hN : Ideal.absNorm (Ideal.span {π}) = p`. Take `⟨k, hk, hk'⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro _ hmul)`. Use `interval_cases k`. Conclude with `absurd (by simpa using hk') hu1`.

Simplify using `using hk'`. It suffices to derive a contradiction. Rewrite `hmul` using `[hk']`. Establish `hpos : 0 < p ^ 2` using `by have := hp.pos; positivity`. Conclude with `hu2 (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmul, mul_one]))`.

Establish `hprime : (Ideal.span {π}).IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp.prime.irreducible)`. Establish `hbot : Ideal.span {π} ≠ ⊥` using `by simpa using hπ0`. Use `⟨⟨Ideal.span {π}, hprime, hbot⟩, ?_, hN⟩` and prove the remaining obligations. Use extensionality with `Q`. Rewrite using `[mem_divs hπ0, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `hQ`. Establish `hle : Ideal.span {π} ≤ Q.asIdeal` using `by rwa [Ideal.span_singleton_le_iff_mem]`. Establish `hmax : (Ideal.span {π}).IsMaximal` using `hprime.isMaximal hbot`. Conclude with `HeightOneSpectrum.ext (hmax.eq_of_le Q.isPrime.ne_top hle).symm`.

Introduce and unpack `rfl`. Conclude with `Ideal.mem_span_singleton_self π`.
-/
theorem divs_of_norm (hrank : Module.finrank ℚ X.E = 2) {π : 𝓞 X.E} {p : ℕ} (hp : p.Prime)
    (h : π * X.conjO π = (p : 𝓞 X.E)) :
    ∃ P : HeightOneSpectrum (𝓞 X.E), divs π = {P} ∧ Ideal.absNorm P.asIdeal = p := by
  have hp0 : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact hp0 h.symm
  have hmul : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {X.conjO π}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, absNorm_natCast X hrank]
  have hpu : ¬ IsUnit (p : 𝓞 X.E) := by
    intro hu
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 X.E)}) = 1 := by
      rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hu
    rw [absNorm_natCast X hrank] at h1
    have := hp.one_lt
    nlinarith
  have hu1 : Ideal.absNorm (Ideal.span {π}) ≠ 1 := by
    intro h1
    rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
    exact hpu (h ▸ h1.mul (h1.map X.conjO))
  have hu2 : Ideal.absNorm (Ideal.span {X.conjO π}) ≠ 1 := by
    intro h1
    rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
    have h2 : IsUnit π := by
      have := h1.map X.conjO
      rwa [conjO_conjO] at this
    exact hpu (h ▸ h2.mul h1)
  have hN : Ideal.absNorm (Ideal.span {π}) = p := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hmul)
    interval_cases k
    · exact absurd (by simpa using hk') hu1
    · simpa using hk'
    · exfalso
      rw [hk'] at hmul
      have hpos : 0 < p ^ 2 := by have := hp.pos; positivity
      exact hu2 (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmul, mul_one]))
  have hprime : (Ideal.span {π}).IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp.prime.irreducible)
  have hbot : Ideal.span {π} ≠ ⊥ := by simpa using hπ0
  refine ⟨⟨Ideal.span {π}, hprime, hbot⟩, ?_, hN⟩
  ext Q
  rw [mem_divs hπ0, Finset.mem_singleton]
  constructor
  · intro hQ
    have hle : Ideal.span {π} ≤ Q.asIdeal := by rwa [Ideal.span_singleton_le_iff_mem]
    have hmax : (Ideal.span {π}).IsMaximal := hprime.isMaximal hbot
    exact HeightOneSpectrum.ext (hmax.eq_of_le Q.isPrime.ne_top hle).symm
  · rintro rfl
    exact Ideal.mem_span_singleton_self π

/- English proof (translation)
Take `⟨P, hP, _⟩` from `divs_of_norm X hrank hp h`. Rewrite using `[hP, Finset.card_singleton]`.
-/
theorem card_divs_of_norm (hrank : Module.finrank ℚ X.E = 2) {π : 𝓞 X.E} {p : ℕ} (hp : p.Prime)
    (h : π * X.conjO π = (p : 𝓞 X.E)) : (divs π).card = 1 := by
  obtain ⟨P, hP, _⟩ := divs_of_norm X hrank hp h
  rw [hP, Finset.card_singleton]

/- English proof (translation)
Take `⟨P, hP, hN⟩` from `divs_of_norm X hrank hp h`. Rewrite `hQ` using `[hP, Finset.mem_singleton]`. Rewrite using `[hQ, hN]`.
-/
theorem norm_divs_of_norm (hrank : Module.finrank ℚ X.E = 2) {π : 𝓞 X.E} {p : ℕ} (hp : p.Prime)
    (h : π * X.conjO π = (p : 𝓞 X.E)) (Q : HeightOneSpectrum (𝓞 X.E)) (hQ : Q ∈ divs π) :
    Ideal.absNorm Q.asIdeal = p := by
  obtain ⟨P, hP, hN⟩ := divs_of_norm X hrank hp h
  rw [hP, Finset.mem_singleton] at hQ
  rw [hQ, hN]

/- English proof (translation)
Rewrite using `[conjO_conjO, mul_comm, h]`.
-/
theorem conj_norm {π : 𝓞 X.E} {p : ℕ} (h : π * X.conjO π = (p : 𝓞 X.E)) :
    X.conjO π * X.conjO (X.conjO π) = (p : 𝓞 X.E) := by
  rw [conjO_conjO, mul_comm, h]

end DegTwo

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def iQb : Qb := Classical.choose (exists_sqrt (-((1 : ℕ) : ℤ)))

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_sqrt (-((1 : ℕ) : ℤ)))`.
-/
theorem iQb_mem : iQb ∈ sqrts (-((1 : ℕ) : ℤ)) := Classical.choose_spec (exists_sqrt (-((1 : ℕ) : ℤ)))

/- English proof (translation)
Establish `h : iQb ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb)` using `iQb_mem`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem iQb_sq : iQb ^ 2 = -1 := by
  have h : iQb ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := iQb_mem
  rw [h]; simp

/- English proof (translation)
Establish `h : (conjQb ι iQb) ^ 2 = iQb ^ 2` using `by rw [← map_pow, iQb_sq, map_neg, map_one]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1` into its components or cases. Conclude with `absurd h1 (conj_sqrt_ne ι one_pos iQb_mem)`. Conclude with `h1`.
-/
theorem conj_iQb : conjQb ι iQb = -iQb := by
  have h : (conjQb ι iQb) ^ 2 = iQb ^ 2 := by rw [← map_pow, iQb_sq, map_neg, map_one]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact absurd h1 (conj_sqrt_ne ι one_pos iQb_mem)
  · exact h1

abbrev gaussFields : Fields := quadFields 1 ι LL hE

def iE : (gaussFields ι LL hE).E := (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)

/- English proof (translation)
Establish `h : ((⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)) ^ 2 = -1` using `Subtype.val_injective iQb_sq`. Conclude with `h`.
-/
theorem iE_sq : iE ι LL hE ^ 2 = -1 := by
  have h : ((⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)) ^ 2 = -1 := Subtype.val_injective iQb_sq
  exact h

/- English proof (translation)
Establish `h : cLL ι (KQ 1) (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1) = -(⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)` using `Subtype.val_injective ((cLL_coe ι (KQ 1) _).trans (conj_iQb ι))`. Conclude with `h`.
-/
theorem star_iE : star (iE ι LL hE) = -iE ι LL hE := by
  have h : cLL ι (KQ 1) (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1) = -(⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1) :=
    Subtype.val_injective ((cLL_coe ι (KQ 1) _).trans (conj_iQb ι))
  exact h

def iO : 𝓞 (gaussFields ι LL hE).E :=
  ⟨iE ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [iE_sq]; exact isIntegral_one.neg)⟩

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (iE_sq ι LL hE)`.
-/
theorem iO_sq : iO ι LL hE ^ 2 = -1 := RingOfIntegers.ext (iE_sq ι LL hE)

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (star_iE ι LL hE)`.
-/
theorem conjO_iO : (gaussFields ι LL hE).conjO (iO ι LL hE) = -iO ι LL hE :=
  RingOfIntegers.ext (star_iE ι LL hE)

def gz (a b : ℤ) : 𝓞 (gaussFields ι LL hE).E := (a : 𝓞 (gaussFields ι LL hE).E) + (b : 𝓞 (gaussFields ι LL hE).E) * iO ι LL hE

/- English proof (translation)
Unfold `gz`. Rewrite using `[map_add, map_mul, map_intCast, map_intCast, conjO_iO]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjO_gz (a b : ℤ) : (gaussFields ι LL hE).conjO (gz ι LL hE a b) = gz ι LL hE a (-b) := by
  unfold gz
  rw [map_add, map_mul, map_intCast, map_intCast, conjO_iO]
  push_cast
  ring

/- English proof (translation)
Establish `hc : ((a ^ 2 + b ^ 2 : ℤ) : 𝓞 (gaussFields ι LL hE).E) = (p : 𝓞 (gaussFields ι LL hE).E)`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Move the coercions through the operations in `at hc`. Rewrite using `[conjO_gz]`.

Unfold `gz`. Use `push_cast`. Take the linear combination `(-(b : 𝓞 (gaussFields ι LL hE).E) ^ 2) * iO_sq ι LL hE + hc`.
-/
theorem gz_norm (a b : ℤ) (p : ℕ) (h : a ^ 2 + b ^ 2 = p) :
    gz ι LL hE a b * (gaussFields ι LL hE).conjO (gz ι LL hE a b) = (p : 𝓞 (gaussFields ι LL hE).E) := by
  have hc : ((a ^ 2 + b ^ 2 : ℤ) : 𝓞 (gaussFields ι LL hE).E) = (p : 𝓞 (gaussFields ι LL hE).E) := by
    rw [h]; simp
  push_cast at hc
  rw [conjO_gz]
  unfold gz
  push_cast
  linear_combination (-(b : 𝓞 (gaussFields ι LL hE).E) ^ 2) * iO_sq ι LL hE + hc

/- English proof (translation)
Establish `hc : ((x * (2 * a) + y * (a ^ 2 + b ^ 2) : ℤ) : 𝓞 (gaussFields ι LL hE).E) = 1`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Move the coercions through the operations in `at hc`. Use `⟨(x : 𝓞 (gaussFields ι LL hE).E) + (y : 𝓞 (gaussFields ι LL hE).E) * gz ι LL hE a (-b), (x : 𝓞 (gaussFields ι LL hE).E), ?_⟩` and prove the remaining obligations.

Rewrite using `[conjO_gz]`. Unfold `gz`. Use `push_cast`. Take the linear combination `(-(y : 𝓞 (gaussFields ι LL hE).E) * (b : 𝓞 (gaussFields ι LL hE).E) ^ 2) * iO_sq ι LL hE + hc`.
-/
theorem gz_cop (a b x y : ℤ) (h : x * (2 * a) + y * (a ^ 2 + b ^ 2) = 1) :
    IsCoprime (gz ι LL hE a b) ((gaussFields ι LL hE).conjO (gz ι LL hE a b)) := by
  have hc : ((x * (2 * a) + y * (a ^ 2 + b ^ 2) : ℤ) : 𝓞 (gaussFields ι LL hE).E) = 1 := by
    rw [h]; simp
  push_cast at hc
  refine ⟨(x : 𝓞 (gaussFields ι LL hE).E) + (y : 𝓞 (gaussFields ι LL hE).E) * gz ι LL hE a (-b), (x : 𝓞 (gaussFields ι LL hE).E), ?_⟩
  rw [conjO_gz]
  unfold gz
  push_cast
  linear_combination (-(y : 𝓞 (gaussFields ι LL hE).E) * (b : 𝓞 (gaussFields ι LL hE).E) ^ 2) * iO_sq ι LL hE + hc

/- English proof (translation)
The claim follows from `finrank_KQ one_pos`.
-/
theorem gauss_rank : Module.finrank ℚ (gaussFields ι LL hE).E = 2 := finrank_KQ one_pos

/- English proof (translation)
The claim follows from `Fintype.card_unit`.
-/
theorem gauss_f : (gaussFields ι LL hE).f = 1 := Fintype.card_unit

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem gauss_Kq (x : (gaussFields ι LL hE).E) : x ∈ (gaussFields ι LL hE).Kq := fun _ _ => rfl

def gaussPrimes : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![5, 13]
  piG := ![gz ι LL hE 2 1, gz ι LL hE 3 2]
  Word := Unit
  T := fun _ => 571253801
  piT := fun _ => gz ι LL hE 16901 16900

set_option maxRecDepth 100000 in
/- English proof (translation)
Evaluate the numerical expressions.
-/
theorem siteGood_prime_torsion : Nat.Prime 571253801 := by norm_num

end Gauss

def exampleWeights (X : Fields) (Word : Type) : Wts X Word Examples₂.R0 where
  row := fun _ => RowPar.of Examples₂.hc0
  hc := fun _ _ => Examples₂.hc0
  tops := ∅

section Roots

/- English proof (translation)
Establish `hn0 : 0 < n` using `Nat.pos_of_dvd_of_pos hn hN`. Establish `: NeZero n` using `⟨hn0.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Qb n`. Establish `hmem : ζ ∈ LL`. Apply `hLL` to reduce the goal to its premises.

Apply `subset_adjoin` to reduce the goal to its premises. Use `show ζ ^ N = 1`. Take `⟨c, rfl⟩` from `hn`. Rewrite using `[pow_mul, hζ.pow_eq_one, one_pow]`. Use `⟨⟨CoF.mk ι LL ζ hmem, ?_⟩, inferInstance⟩` and prove the remaining obligations.

Conclude with `IsPrimitiveRoot.of_map_of_injective (f := CoF.val ι LL) (by simpa using hζ) (CoF.val_injective ι LL)`.
-/
theorem hasEnoughRoots (ι : Qb →+* ℂ) (LL : Fld) {N n : ℕ} (hN : 0 < N) (hn : n ∣ N) (hLL : cycQ N ≤ LL) :
    HasEnoughRootsOfUnity (CoF ι LL) n := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn hN
  have : NeZero n := ⟨hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb n
  have hmem : ζ ∈ LL := by
    apply hLL
    apply subset_adjoin
    show ζ ^ N = 1
    obtain ⟨c, rfl⟩ := hn
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨⟨CoF.mk ι LL ζ hmem, ?_⟩, inferInstance⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := CoF.val ι LL) (by simpa using hζ) (CoF.val_injective ι LL)

/- English proof (translation)
Establish `ha : (Multiplicative.ofAdd (1 : A)) ≠ 1`. Introduce `h`. Conclude with `one_ne_zero (Multiplicative.ofAdd.injective h)`. Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative A) M ha`. Use `⟨AddChar.toMonoidHomEquiv.symm ((Units.coeHom M).comp φ), fun h => hφ ?_⟩` and prove the remaining obligations.

Establish `h1` using `DFunLike.congr_fun h 1`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `h1`.
-/
theorem exists_addChar_ne {A M : Type} [CommRing A] [Finite A] [Nontrivial A] [Field M]
    [HasEnoughRootsOfUnity M (Monoid.exponent (Multiplicative A))] : ∃ ψ : AddChar A M, ψ ≠ 1 := by
  have ha : (Multiplicative.ofAdd (1 : A)) ≠ 1 := by
    intro h
    exact one_ne_zero (Multiplicative.ofAdd.injective h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative A) M ha
  refine ⟨AddChar.toMonoidHomEquiv.symm ((Units.coeHom M).comp φ), fun h => hφ ?_⟩
  have h1 := DFunLike.congr_fun h 1
  apply Units.ext
  exact h1

/- English proof (translation)
Take `⟨e⟩` from `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M`. Establish `hc : IsCyclic (G →* Mˣ)` using `isCyclic_of_surjective e.symm e.symm.surjective`. Take `⟨φ, hφ⟩` from `hc.exists_generator`. Use `⟨φ, (injective_iff_map_eq_one φ).2 fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Take `⟨ψ, hψ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hne`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 (hφ ψ)`. Apply `hψ` to reduce the goal to its premises. Rewrite using `[← hk, MonoidHom.zpow_apply, ha, one_zpow]`.
-/
theorem exists_faithful (G M : Type) [CommGroup G] [Finite G] [IsCyclic G] [Field M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] : ∃ om : G →* Mˣ, Function.Injective om := by
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M
  have hc : IsCyclic (G →* Mˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  obtain ⟨φ, hφ⟩ := hc.exists_generator
  refine ⟨φ, (injective_iff_map_eq_one φ).2 fun a ha => ?_⟩
  by_contra hne
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hφ ψ)
  apply hψ
  rw [← hk, MonoidHom.zpow_apply, ha, one_zpow]

/- English proof (translation)
Establish `: Fintype A` using `Fintype.ofFinite A`. Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Set `e : ZMod p ≃+* A` to `ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card, hA])`. Use `⟨Units.map e.symm.toRingHom.toMonoidHom, fun a => ⟨Units.map e.toRingHom.toMonoidHom a, ?_⟩, fun a x hx => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `e.symm_apply_apply _`. Apply `Units.ext show e.symm (x : A) = (a : ZMod p)` to reduce the goal to its premises. Rewrite using `[hx, map_natCast, ZMod.natCast_zmod_val]`.
-/
theorem exists_theta {A : Type} [CommRing A] [Finite A] {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p) :
    ∃ θ : Aˣ →* (ZMod p)ˣ, Function.Surjective θ ∧
      ∀ (a : (ZMod p)ˣ) (x : Aˣ), (x : A) = (((a : ZMod p).val : ℕ) : A) → θ x = a := by
  have : Fintype A := Fintype.ofFinite A
  have : NeZero p := ⟨hp.ne_zero⟩
  let e : ZMod p ≃+* A := ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card, hA])
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom, fun a => ⟨Units.map e.toRingHom.toMonoidHom a, ?_⟩, fun a x hx => ?_⟩
  · apply Units.ext
    exact e.symm_apply_apply _
  · apply Units.ext
    show e.symm (x : A) = (a : ZMod p)
    rw [hx, map_natCast, ZMod.natCast_zmod_val]

end Roots

section GaussChars

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

/- English proof (translation)
Establish `hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Set `_ : Field (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)` to `Ideal.Quotient.field w.asIdeal`. Establish `hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = p`. Rewrite using `[← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Prove the components needed by the constructor for the conclusion.

Establish `hex : Monoid.exponent (Multiplicative (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)) ∣ N`. Use `dvd_trans ?_ hpN` and prove the remaining obligations. Rewrite using `[← hcard]`. Conclude with `Group.exponent_dvd_nat_card`. Use `hasEnoughRoots ι LL hN hex hLL` as an intermediate fact.

Conclude with `exists_addChar_ne`. Establish `hcu : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ = p - 1`. Rewrite using `[Nat.card_units, hcard]`. Establish `hex : Monoid.exponent (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ ∣ N`. Use `dvd_trans ?_ hp1N` and prove the remaining obligations.

Rewrite using `[← hcu]`. Conclude with `Group.exponent_dvd_nat_card`. Use `hasEnoughRoots ι LL hN hex hLL` as an intermediate fact. Establish `hne : (-1 : (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ) ≠ 1`. Introduce `h`.

Establish `h2 : ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = 0`. Establish `h3` using `congrArg Units.val h`. Simplify using `only [Units.val_neg, Units.val_one] at h3`. Use `push_cast`. Take the linear combination `-h3`.

Establish `h4 : ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E) ∈ w.asIdeal`. Establish `h6 : Ideal.Quotient.mk w.asIdeal ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E) = 0`. Rewrite using `[map_natCast]`. Conclude with `h2`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h6`.

Establish `h5 : Ideal.absNorm w.asIdeal ∣ Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E)})` using `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h4)`. Rewrite `h5` using `[absNorm_natCast _ (gauss_rank ι LL hE), hw]`. Use `(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5)` as an intermediate fact. Conclude with `hp2 this`. Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ (CoF ι LL) hne`.

Conclude with `⟨φ, fun h => hφ (by rw [h]; rfl)⟩`.
-/
theorem chars_at (w : HeightOneSpectrum (𝓞 (gaussFields ι LL hE).E)) {p N : ℕ} (hN : 0 < N) (hp : p.Prime) (hp2 : p ≠ 2)
    (hw : Ideal.absNorm w.asIdeal = p) (hpN : p ∣ N) (hp1N : p - 1 ∣ N) (hLL : cycQ N ≤ LL) :
    (∃ ψ : AddChar (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) (CoF ι LL), ψ ≠ 1) ∧
      ∃ φ : (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ →* (CoF ι LL)ˣ, φ ≠ 1 := by
  have hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let _ : Field (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  constructor
  · have hex : Monoid.exponent (Multiplicative (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)) ∣ N := by
      refine dvd_trans ?_ hpN
      rw [← hcard]
      exact Group.exponent_dvd_nat_card
    have := hasEnoughRoots ι LL hN hex hLL
    exact exists_addChar_ne
  · have hcu : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ = p - 1 := by
      rw [Nat.card_units, hcard]
    have hex : Monoid.exponent (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ ∣ N := by
      refine dvd_trans ?_ hp1N
      rw [← hcu]
      exact Group.exponent_dvd_nat_card
    have := hasEnoughRoots ι LL hN hex hLL
    have hne : (-1 : (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ) ≠ 1 := by
      intro h
      have h2 : ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = 0 := by
        have h3 := congrArg Units.val h
        simp only [Units.val_neg, Units.val_one] at h3
        push_cast
        linear_combination -h3
      have h4 : ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E) ∈ w.asIdeal := by
        have h6 : Ideal.Quotient.mk w.asIdeal ((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E) = 0 := by
          rw [map_natCast]; exact h2
        exact Ideal.Quotient.eq_zero_iff_mem.1 h6
      have h5 : Ideal.absNorm w.asIdeal ∣ Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 (gaussFields ι LL hE).E)}) :=
        Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h4)
      rw [absNorm_natCast _ (gauss_rank ι LL hE), hw] at h5
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5)
      exact hp2 this
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ (CoF ι LL) hne
    exact ⟨φ, fun h => hφ (by rw [h]; rfl)⟩

end GaussChars

section GaussChars2

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

/- English proof (translation)
Establish `hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Establish `hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = p`. Rewrite using `[← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Take `⟨θ, hθs, hθ⟩` from `exists_theta hp hcard`. Establish `key : ∀ n n' : ℕ, ((om p).comp θ) ^ n = ((om p).comp θ) ^ n' → (2 : ZMod p) ^ n = 2 ^ n'`.

Introduce `n n' h`. Take `⟨x, hx⟩` from `hθs (ZMod.unitOfCoprime 2 h2)`. Establish `h1` using `DFunLike.congr_fun h x`. Rewrite `h1` using `[MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hx, ← map_pow, ← map_pow]`. Establish `h3` using `congrArg Units.val (hom h1)`.

Rewrite `h3` using `[Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]`. Conclude with `h3` after adjusting the coercions. Use `⟨fun j => ((om p).comp θ) ^ (2 * (j.1 + 1)), ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro j j' h fin_cases j <;> fin_cases j'`. Both sides reduce to the same expression.

Conclude with `(h24 (key 2 4 h)).elim`. Conclude with `(h24 (key 4 2 h).symm).elim`. Both sides reduce to the same expression. Introduce `q hq j a x hx`. Take `rfl : p = q` from `hw.symm.trans hq`.

Rewrite using `[MonoidHom.pow_apply, MonoidHom.comp_apply, hθ a x hx]`.
-/
theorem chi_at (w : HeightOneSpectrum (𝓞 (gaussFields ι LL hE).E)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (h2 : Nat.Coprime 2 p) (h24 : (2 : ZMod p) ^ 2 ≠ 2 ^ 4)
    (om : ∀ q : ℕ, (ZMod q)ˣ →* (CoF ι LL)ˣ) (hom : Function.Injective (om p)) :
    ∃ χ : Fin 2 → ((𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ →* (CoF ι LL)ˣ), Function.Injective χ ∧
      ∀ q : ℕ, Ideal.absNorm w.asIdeal = q → ∀ (j : Fin 2) (a : (ZMod q)ˣ)
        (x : (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal)ˣ),
        (x : 𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) =
          (((a : ZMod q).val : ℕ) : 𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) →
        χ j x = om q a ^ (2 * (j.1 + 1)) := by
  have hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨θ, hθs, hθ⟩ := exists_theta hp hcard
  have key : ∀ n n' : ℕ, ((om p).comp θ) ^ n = ((om p).comp θ) ^ n' → (2 : ZMod p) ^ n = 2 ^ n' := by
    intro n n' h
    obtain ⟨x, hx⟩ := hθs (ZMod.unitOfCoprime 2 h2)
    have h1 := DFunLike.congr_fun h x
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hx, ← map_pow, ← map_pow] at h1
    have h3 := congrArg Units.val (hom h1)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at h3
    exact_mod_cast h3
  refine ⟨fun j => ((om p).comp θ) ^ (2 * (j.1 + 1)), ?_, ?_⟩
  · intro j j' h
    fin_cases j <;> fin_cases j'
    · rfl
    · exact (h24 (key 2 4 h)).elim
    · exact (h24 (key 4 2 h).symm).elim
    · rfl
  · intro q hq j a x hx
    obtain rfl : p = q := hw.symm.trans hq
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, hθ a x hx]

end GaussChars2

/- English proof (translation)
Unfold `KQ sqQ cycQ`. Apply `adjoin.mono` to reduce the goal to its premises. Introduce `z hz`. Establish `h : z ^ 2 = -1`. Establish `h1 : z ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb)` using `hz`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Use `show z ^ 780 = 1`. Establish `: z ^ 780 = (z ^ 2) ^ 390` using `by rw [← pow_mul]`. Rewrite using `[this, h]`.

Evaluate the numerical expressions.
-/
theorem gaussian_field_le_cyclotomic : KQ 1 ≤ cycQ 780 := by
  unfold KQ sqQ cycQ
  apply adjoin.mono
  intro z hz
  have h : z ^ 2 = -1 := by
    have h1 : z ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := hz
    rw [h1]; simp
  show z ^ 780 = 1
  have : z ^ 780 = (z ^ 2) ^ 390 := by rw [← pow_mul]
  rw [this, h]
  norm_num

instance fin_cyc : FiniteDimensional ℚ (cycQ 780) := fin_adjoin (finite_pow_eq 780 (by norm_num) 1)

instance normal_cyc : Normal ℚ (cycQ 780) := normal_adjoin fun s x hx => by
  show (s x) ^ 780 = 1
  rw [← map_pow, show x ^ 780 = 1 from hx, map_one]

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def gaussianPrimesExample : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![41, 73]
  piG := ![gz ι LL hE 5 4, gz ι LL hE (-3) 8]
  Word := Unit
  T := fun _ => 20543140322918657
  piT := fun _ => gz ι LL hE 1 143328784

end Gauss

end Formalism.L2.Col
