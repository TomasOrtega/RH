import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Formalism.LocalToGlobal.UnitaryNorms.PowValCast

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

/- English proof (translation)
Introduce `ι LL _ x`. Use `show ι (CoF.val ι LL (star x)) = _`. Rewrite using `[CoF.val_star, conjQb_spec]`. Both sides reduce to the same expression.
-/
theorem sig0Conj : DistinguishedEmbeddingConjugation := by
  intro ι LL _ x
  show ι (CoF.val ι LL (star x)) = _
  rw [CoF.val_star, conjQb_spec]
  rfl

/- English proof (translation)
Introduce `h`. Take `⟨t, rfl⟩` from `Complex.conj_eq_iff_real.1 h`. Establish `: t ^ 2 = r` using `by exact_mod_cast hw`. Use polynomial arithmetic with `[sq_nonneg t]`.
-/
theorem conj_ne_of_sq_neg {w : ℂ} {r : ℝ} (hr : r < 0) (hw : w ^ 2 = (r : ℂ)) : starRingEnd ℂ w ≠ w := by
  intro h
  obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.1 h
  have : t ^ 2 = r := by exact_mod_cast hw
  nlinarith [sq_nonneg t]

/- English proof (translation)
Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)`. Conclude with `⟨x, hx⟩`.
-/
theorem exists_sqrt (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩

/- English proof (translation)
The claim follows from `subset_adjoin ℚ _`.
-/
theorem sqrts_sub (m : ℤ) : sqrts m ⊆ (sqQ m : Set Qb) := subset_adjoin ℚ _

/- English proof (translation)
Introduce `ι LL d hd hK`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isComplex_iff]`. Introduce `hreal`. Take `⟨x, hx⟩` from `exists_sqrt (-(d : ℤ))`.

Establish `hxL : x ∈ LL` using `hK (sqrts_sub _ hx)`. Use `set y : CoF ι LL := CoF.mk ι LL x hxL with hy`. Establish `hy2 : y ^ 2 = ((-(d : ℤ) : ℤ) : CoF ι LL)`. Apply `CoF.val_injective ι LL` to reduce the goal to its premises. Rewrite using `[map_pow, CoF.val_mk, map_intCast]`.

Conclude with `hx`. Establish `h2 : (v.embedding y) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ)`. Rewrite using `[← map_pow, hy2, map_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hneg : (-(d : ℝ)) < 0`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast hd`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `conj_ne_of_sq_neg hneg h2 (RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hreal) y)`.
-/
theorem totComplex : TotComplex := by
  intro ι LL d hd hK
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  obtain ⟨x, hx⟩ := exists_sqrt (-(d : ℤ))
  have hxL : x ∈ LL := hK (sqrts_sub _ hx)
  set y : CoF ι LL := CoF.mk ι LL x hxL with hy
  have hy2 : y ^ 2 = ((-(d : ℤ) : ℤ) : CoF ι LL) := by
    apply CoF.val_injective ι LL
    rw [map_pow, CoF.val_mk, map_intCast]
    exact hx
  have h2 : (v.embedding y) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ) := by
    rw [← map_pow, hy2, map_intCast]; push_cast; ring
  have hneg : (-(d : ℝ)) < 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  exact conj_ne_of_sq_neg hneg h2 (RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hreal) y)

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℚ Qb` using `AlgebraicClosure.isAlgebraic ℚ`. Conclude with `Algebra.IsAlgebraic.tower_top (K := ℚ) LL`.
-/
theorem isAlgebraicQb (LL : Fld) : Algebra.IsAlgebraic LL Qb := by
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) LL

/- English proof (translation)
Use `isAlgebraicQb LL` as an intermediate fact. Set `f : LL →ₐ[ℚ] ℂ` to `RingHom.toRatAlgHom (R := LL) σ`. Take `⟨φ, hφ⟩` from `IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f`. Use `⟨φ.toRingHom, fun x => ?_⟩` and prove the remaining obligations. Conclude with `DFunLike.congr_fun hφ x`.
-/
theorem exists_ext (ι : Qb →+* ℂ) (LL : Fld) (σ : CoF ι LL →+* ℂ) :
    ∃ τ : Qb →+* ℂ, ∀ x : CoF ι LL, τ (CoF.val ι LL x) = σ x := by
  have := isAlgebraicQb LL
  let f : LL →ₐ[ℚ] ℂ := RingHom.toRatAlgHom (R := LL) σ
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f
  refine ⟨φ.toRingHom, fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

/- English proof (translation)
Use `⟨AlgEquiv.ofRingEquiv (f := (algC τ).trans (algC ι).symm) (fun r => by simp), fun x => ?_⟩` and prove the remaining obligations. Establish `h : ((algC ι ((algC ι).symm (algC τ x)) : algebraicClosure ℚ ℂ) : ℂ) = τ x`. Rewrite using `[RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Conclude with `h.symm`.
-/
theorem exists_aut (ι τ : Qb →+* ℂ) : ∃ σ : Qb ≃ₐ[ℚ] Qb, ∀ x, τ x = ι (σ x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (algC τ).trans (algC ι).symm) (fun r => by simp), fun x => ?_⟩
  have h : ((algC ι ((algC ι).symm (algC τ x)) : algebraicClosure ℚ ℂ) : ℂ) = τ x := by
    rw [RingEquiv.apply_symm_apply]; rfl
  exact h.symm

/- English proof (translation)
Establish `key : ∀ ι ι' : Qb →+* ℂ, ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x`. Introduce `ι ι' x hx`. Apply `ι'.injective` to reduce the goal to its premises. Rewrite using `[conjQb_spec]`. Conclude with `hx ι'`.

Establish `le : ∀ ι ι' : Qb →+* ℂ, cmQb ι ≤ cmQb ι'`. Introduce `ι ι' x hx τ`. Rewrite using `[← key ι ι' x hx]`. Conclude with `hx τ`. Conclude with `fun ι ι' => ⟨le_antisymm (le ι ι') (le ι' ι), key ι ι'⟩`.
-/
theorem cmQbIndep : CmQbIndep := by
  have key : ∀ ι ι' : Qb →+* ℂ, ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x := by
    intro ι ι' x hx
    apply ι'.injective
    rw [conjQb_spec]
    exact hx ι'
  have le : ∀ ι ι' : Qb →+* ℂ, cmQb ι ≤ cmQb ι' := by
    intro ι ι' x hx τ
    rw [← key ι ι' x hx]
    exact hx τ
  exact fun ι ι' => ⟨le_antisymm (le ι ι') (le ι' ι), key ι ι'⟩

/- English proof (translation)
Establish `h1 : (τ z) ^ N = 1` using `by rw [← map_pow, show z ^ N = 1 from hz, map_one]`. Rewrite using `[map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hN.ne')]`.
-/
theorem conj_root (τ : Qb →+* ℂ) {N : ℕ} (hN : 0 < N) {z : Qb} (hz : z ∈ mus N) :
    starRingEnd ℂ (τ z) = τ z⁻¹ := by
  have h1 : (τ z) ^ N = 1 := by rw [← map_pow, show z ^ N = 1 from hz, map_one]
  rw [map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hN.ne')]

/- English proof (translation)
Introduce `ι N hN`. Rewrite using `[cycQ, adjoin_le_iff]`. Introduce `z hz τ`. Establish `hc : conjQb ι z = z⁻¹`. Apply `ι.injective` to reduce the goal to its premises.

Rewrite using `[conjQb_spec, conj_root ι hN hz]`. Rewrite using `[hc, conj_root τ hN hz]`.
-/
theorem cycLeCm : CycLeCm := by
  intro ι N hN
  rw [cycQ, adjoin_le_iff]
  intro z hz τ
  have hc : conjQb ι z = z⁻¹ := by
    apply ι.injective
    rw [conjQb_spec, conj_root ι hN hz]
  rw [hc, conj_root τ hN hz]

/- English proof (translation)
Establish `h2 : (starRingEnd ℂ w) ^ 2 = w ^ 2` using `by rw [← map_pow, hw, Complex.conj_ofReal]`. Use `split_ifs with hr`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. Conclude with `absurd h (conj_ne_of_sq_neg hr hw)`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : w.re = 0`.

Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : w.im = 0`. Use `congrArg Complex.re hw` as an intermediate fact.

Rewrite `this` using `[sq, Complex.mul_re, hre, Complex.ofReal_re]`. Establish `h0 : w.im * w.im ≤ 0` using `by have := not_lt.1 hr; linarith`. Use polynomial arithmetic with `[mul_self_nonneg w.im]`. Establish `hw0 : w = 0` using `Complex.ext hre him`. Rewrite using `[hw0]`.

Simplify using the standard rewrite rules.
-/
theorem conj_sqrt {w : ℂ} {r : ℝ} (hw : w ^ 2 = (r : ℂ)) :
    starRingEnd ℂ w = (if r < 0 then -1 else 1) * w := by
  have h2 : (starRingEnd ℂ w) ^ 2 = w ^ 2 := by rw [← map_pow, hw, Complex.conj_ofReal]
  split_ifs with hr
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact absurd h (conj_ne_of_sq_neg hr hw)
    · rw [h]; ring
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · rw [h]; ring
    · have hre : w.re = 0 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      have him : w.im = 0 := by
        have := congrArg Complex.re hw
        rw [sq, Complex.mul_re, hre, Complex.ofReal_re] at this
        have h0 : w.im * w.im ≤ 0 := by have := not_lt.1 hr; linarith
        nlinarith [mul_self_nonneg w.im]
      have hw0 : w = 0 := Complex.ext hre him
      rw [hw0]; simp

/- English proof (translation)
Introduce `ι m`. Rewrite using `[sqQ, adjoin_le_iff]`. Introduce `x hx τ`. Establish `hτ : ∀ τ : Qb →+* ℂ, (τ x) ^ 2 = ((m : ℝ) : ℂ)`. Introduce `τ`.

Rewrite using `[← map_pow, show x ^ 2 = (m : Qb) from hx, map_intCast]`. Use `push_cast`. Both sides reduce to the same expression. Distinguish the cases in `hm : (m : ℝ) < 0`. Establish `hc : conjQb ι x = -x`.

Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[conjQb_spec, conj_sqrt (hτ ι), if_pos hm, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, conj_sqrt (hτ τ), if_pos hm, map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc : conjQb ι x = x`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[conjQb_spec, conj_sqrt (hτ ι), if_neg hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, conj_sqrt (hτ τ), if_neg hm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqLeCm : SqLeCm := by
  intro ι m
  rw [sqQ, adjoin_le_iff]
  intro x hx τ
  have hτ : ∀ τ : Qb →+* ℂ, (τ x) ^ 2 = ((m : ℝ) : ℂ) := by
    intro τ
    rw [← map_pow, show x ^ 2 = (m : Qb) from hx, map_intCast]; push_cast; rfl
  by_cases hm : (m : ℝ) < 0
  · have hc : conjQb ι x = -x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_pos hm, map_neg]; ring
    rw [hc, conj_sqrt (hτ τ), if_pos hm, map_neg]; ring
  · have hc : conjQb ι x = x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_neg hm]; ring
    rw [hc, conj_sqrt (hτ τ), if_neg hm]; ring

/- English proof (translation)
Introduce `ι L LL _ h hL s x y hy`. Apply `CoF.val_injective ι LL` to reduce the goal to its premises. Rewrite using `[CoF.val_star, val_tauCo, val_tauCo]`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[conjQb_spec]`.

Establish `h1` using `hL x.2 (ι.comp (s.liftNormal Qb).toRingHom)`. Establish `h2 : ∀ u : L, s.liftNormal Qb (u : Qb) = s u` using `fun u => AlgHom.liftNormal_commutes s Qb u`. Establish `h3 : ι (s.liftNormal Qb (conjQb ι x)) = starRingEnd ℂ (ι (s.liftNormal Qb (x : Qb)))` using `h1`. Rewrite `h3` using `[← hy, h2, h2]`. Conclude with `h3.symm`.
-/
theorem tauStar : TauStar := by
  intro ι L LL _ h hL s x y hy
  apply CoF.val_injective ι LL
  rw [CoF.val_star, val_tauCo, val_tauCo]
  apply ι.injective
  rw [conjQb_spec]
  have h1 := hL x.2 (ι.comp (s.liftNormal Qb).toRingHom)
  have h2 : ∀ u : L, s.liftNormal Qb (u : Qb) = s u := fun u => AlgHom.liftNormal_commutes s Qb u
  have h3 : ι (s.liftNormal Qb (conjQb ι x)) = starRingEnd ℂ (ι (s.liftNormal Qb (x : Qb))) := h1
  rw [← hy, h2, h2] at h3
  exact h3.symm

/- English proof (translation)
Use `(Polynomial.nthRoots n a).toFinset.finite_toSet.subset fun z hz => ?_` and prove the remaining obligations. Simplify `hz` using `[Polynomial.mem_nthRoots hn]`.
-/
theorem finite_pow_eq {n : ℕ} (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by
  classical
  refine (Polynomial.nthRoots n a).toFinset.finite_toSet.subset fun z hz => ?_
  simpa [Polynomial.mem_nthRoots hn] using hz

/- English proof (translation)
The claim follows from `((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral`.
-/
theorem isIntegralQb (x : Qb) : IsIntegral ℚ x := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral

/- English proof (translation)
Establish `: Finite S` using `hS`. Conclude with `finiteDimensional_adjoin fun x _ => isIntegralQb x`.
-/
theorem fin_adjoin {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by
  have : Finite S := hS
  exact finiteDimensional_adjoin fun x _ => isIntegralQb x

end Formalism.L2.DIV
