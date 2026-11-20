import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

open Polynomial IsLocalRing in
/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Establish `hq2 : 2 ≤ p ^ f`. Combine the equalities or inequalities in the displayed calculation. Establish `hq0 : p ^ f ≠ 0` using `by omega`. Use `set q := p ^ f with hq`.

Use `set P : k[X] := X ^ (q + 1) with hP`. Establish `hdeg : P.degree ≠ 0`. Rewrite using `[hP, degree_X_pow]`. Conclude with `Nat.succ_ne_zero q` after adjusting the coercions. Use `haveI : Nontrivial (AdjoinRoot P) := AdjoinRoot.nontrivial P hdeg`.

Use `haveI : CharP (AdjoinRoot P) p := charP_of_injective_algebraMap (algebraMap k (AdjoinRoot P)).injective p`. Use `set r := AdjoinRoot.root P with hr`. Establish `hr0 : r ^ (q + 1) = 0`. Rewrite using `[hr, AdjoinRoot.root, ← map_pow]`. Conclude with `AdjoinRoot.mk_self`.

Establish `hrr : r ^ q * r ^ q = 0`. Establish `: q + q = (q + 1) + (q - 1)` using `by omega`. Rewrite using `[← pow_add, this, pow_add, hr0, zero_mul]`. Establish `he2 : (DualNumber.eps : DualNumber k) ^ 2 = 0`. Rewrite using `[pow_two, DualNumber.eps_mul_eps]`.

Establish `heq : ∀ n, 2 ≤ n → (DualNumber.eps : DualNumber k) ^ n = 0` using `fun n hn => by`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Rewrite using `[pow_add, he2, zero_mul]`. Set `τ : AdjoinRoot P →ₐ[k] DualNumber k` to `AdjoinRoot.liftAlgHom P (Algebra.ofId k (DualNumber k)) DualNumber.eps (by`. Simplify using `[hP, heq (q + 1) (by omega)])`.

Establish `hτr : τ r = DualNumber.eps`. Simplify using `[τ, hr, AdjoinRoot.liftAlgHom_root]`. Set `of` to `algebraMap k (AdjoinRoot P)`. Set `j : DualNumber k →+* AdjoinRoot P` to `{ toFun := fun z => of (z.fst ^ q) + of (z.snd ^ q) * r ^ q map_one' := by simp [hq0] map_zero' := by simp [hq0] map_add' := fun z w => by`. Simplify using `only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hq, add_pow_char_pow, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_mul' := fun z w => by`. Simplify using `only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hq, add_pow_char_pow, mul_pow, map_add, map_mul]`. Rewrite using `[← hq]`. Take the linear combination `(-(of (z.snd ^ q) * of (w.snd ^ q))) * hrr }`.

Establish `hj : ∀ z, j z = of (z.fst ^ q) + of (z.snd ^ q) * r ^ q` using `fun _ => rfl`. Use `⟨τ, j, ?_, ?_, hτr⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero j).2 fun z hz => ?_` and prove the remaining obligations. Establish `h1 : z.fst = 0`. Establish `h0 : τ (j z) = algebraMap k (DualNumber k) (z.fst ^ q)`.

Establish `e : τ (r ^ q) = 0` using `by rw [map_pow, hτr, heq q hq2]`. Rewrite using `[hj, map_add, map_mul, e, mul_zero, add_zero]`. Conclude with `τ.commutes _`. Rewrite `h0` using `[hz, map_zero]`. Establish `h0'` using `congrArg TrivSqZeroExt.fst h0`.

Rewrite `h0'` using `[TrivSqZeroExt.fst_zero, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]`. Conclude with `(pow_eq_zero_iff hq0).1 h0'.symm`. Rewrite `hz` using `[hj, h1]`. Establish `h2 : of (z.snd ^ q) * r ^ q = 0`. Rewrite `hz` using `[zero_pow hq0, map_zero, zero_add]`. Then use the resulting hypothesis.

Establish `h3 : AdjoinRoot.mk P (C (z.snd ^ q) * X ^ q) = 0`. Rewrite using `[map_mul, map_pow (AdjoinRoot.mk P) X q]`. Conclude with `h2`. Rewrite `h3` using `[AdjoinRoot.mk_eq_zero, hP, X_pow_dvd_iff]`. Establish `h4` using `h3 q (by omega)`.

Rewrite `h4` using `[coeff_C_mul, coeff_X_pow_self, _root_.mul_one]`. Establish `h5 : z.snd = 0` using `(pow_eq_zero_iff hq0).1 h4`. Conclude with `TrivSqZeroExt.ext h1 h5`. Establish `key : j.comp (τ : AdjoinRoot P →+* DualNumber k) = iterateFrobenius (AdjoinRoot P) p f`. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises.

Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a show j (τ (of a)) = iterateFrobenius (AdjoinRoot P) p f (of a)`. Rewrite using `[τ.commutes, hj, iterateFrobenius_def, ← map_pow, ← hq]`. Simplify using `only [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_pow hq0, map_zero, zero_mul, add_zero, map_pow]`. Use `show j (τ r) = iterateFrobenius (AdjoinRoot P) p f r`.

Rewrite using `[hτr, hj, iterateFrobenius_def, ← hq]`. Simplify using `[hq0]`. Introduce `x`. Use `RingHom.congr_fun key x` as an intermediate fact. Simplify `this` using `[iterateFrobenius_def]`.
-/
private lemma art_tangent (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (f : ℕ) (hf : 0 < f) :
    ∃ (τ : AdjoinRoot (X ^ (p ^ f + 1) : k[X]) →ₐ[k] DualNumber k)
      (j : DualNumber k →+* AdjoinRoot (X ^ (p ^ f + 1) : k[X])),
      Function.Injective j ∧ (∀ x, j (τ x) = x ^ p ^ f) ∧
        τ (AdjoinRoot.root (X ^ (p ^ f + 1) : k[X])) = DualNumber.eps := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
  have hq0 : p ^ f ≠ 0 := by omega
  set q := p ^ f with hq
  set P : k[X] := X ^ (q + 1) with hP
  have hdeg : P.degree ≠ 0 := by
    rw [hP, degree_X_pow]
    exact_mod_cast Nat.succ_ne_zero q
  haveI : Nontrivial (AdjoinRoot P) := AdjoinRoot.nontrivial P hdeg
  haveI : CharP (AdjoinRoot P) p := charP_of_injective_algebraMap (algebraMap k (AdjoinRoot P)).injective p
  set r := AdjoinRoot.root P with hr
  have hr0 : r ^ (q + 1) = 0 := by
    rw [hr, AdjoinRoot.root, ← map_pow]
    exact AdjoinRoot.mk_self
  have hrr : r ^ q * r ^ q = 0 := by
    have : q + q = (q + 1) + (q - 1) := by omega
    rw [← pow_add, this, pow_add, hr0, zero_mul]
  have he2 : (DualNumber.eps : DualNumber k) ^ 2 = 0 := by
    rw [pow_two, DualNumber.eps_mul_eps]
  have heq : ∀ n, 2 ≤ n → (DualNumber.eps : DualNumber k) ^ n = 0 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, he2, zero_mul]
  let τ : AdjoinRoot P →ₐ[k] DualNumber k :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId k (DualNumber k)) DualNumber.eps (by
      simp [hP, heq (q + 1) (by omega)])
  have hτr : τ r = DualNumber.eps := by
    simp [τ, hr, AdjoinRoot.liftAlgHom_root]
  let of := algebraMap k (AdjoinRoot P)
  let j : DualNumber k →+* AdjoinRoot P :=
    { toFun := fun z => of (z.fst ^ q) + of (z.snd ^ q) * r ^ q
      map_one' := by simp [hq0]
      map_zero' := by simp [hq0]
      map_add' := fun z w => by
        simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hq, add_pow_char_pow, map_add]
        ring
      map_mul' := fun z w => by
        simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
          MulOpposite.unop_op, hq, add_pow_char_pow, mul_pow, map_add, map_mul]
        rw [← hq]
        linear_combination (-(of (z.snd ^ q) * of (w.snd ^ q))) * hrr }
  have hj : ∀ z, j z = of (z.fst ^ q) + of (z.snd ^ q) * r ^ q := fun _ => rfl
  refine ⟨τ, j, ?_, ?_, hτr⟩
  · refine (injective_iff_map_eq_zero j).2 fun z hz => ?_
    have h1 : z.fst = 0 := by
      have h0 : τ (j z) = algebraMap k (DualNumber k) (z.fst ^ q) := by
        have e : τ (r ^ q) = 0 := by rw [map_pow, hτr, heq q hq2]
        rw [hj, map_add, map_mul, e, mul_zero, add_zero]
        exact τ.commutes _
      rw [hz, map_zero] at h0
      have h0' := congrArg TrivSqZeroExt.fst h0
      rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] at h0'
      exact (pow_eq_zero_iff hq0).1 h0'.symm
    rw [hj, h1] at hz
    have h2 : of (z.snd ^ q) * r ^ q = 0 := by
      rwa [zero_pow hq0, map_zero, zero_add] at hz
    have h3 : AdjoinRoot.mk P (C (z.snd ^ q) * X ^ q) = 0 := by
      rw [map_mul, map_pow (AdjoinRoot.mk P) X q]
      exact h2
    rw [AdjoinRoot.mk_eq_zero, hP, X_pow_dvd_iff] at h3
    have h4 := h3 q (by omega)
    rw [coeff_C_mul, coeff_X_pow_self, _root_.mul_one] at h4
    have h5 : z.snd = 0 := (pow_eq_zero_iff hq0).1 h4
    exact TrivSqZeroExt.ext h1 h5
  · have key : j.comp (τ : AdjoinRoot P →+* DualNumber k) = iterateFrobenius (AdjoinRoot P) p f := by
      apply Ideal.Quotient.ringHom_ext
      apply Polynomial.ringHom_ext
      · intro a
        show j (τ (of a)) = iterateFrobenius (AdjoinRoot P) p f (of a)
        rw [τ.commutes, hj, iterateFrobenius_def, ← map_pow, ← hq]
        simp only [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_pow hq0,
          map_zero, zero_mul, add_zero, map_pow]
      · show j (τ r) = iterateFrobenius (AdjoinRoot P) p f r
        rw [hτr, hj, iterateFrobenius_def, ← hq]
        simp [hq0]
    intro x
    have := RingHom.congr_fun key x
    simpa [iterateFrobenius_def] using this

end UpperTheory.Gal.Ord

namespace UpperTheory.Gal.Ord

section ArtB

open Polynomial IsLocalRing
open scoped Classical

variable {k : Type} [Field k] {B : Type} [CommRing B] [IsLocalRing B] [Algebra k B]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Conclude with `(mem_maximalIdeal _).1 h ((IsUnit.mk0 c hc).map (algebraMap k B))`.
-/
private lemma art_alg_mem {c : k} (h : algebraMap k B c ∈ maximalIdeal B) : c = 0 := by
  by_contra hc
  exact (mem_maximalIdeal _).1 h ((IsUnit.mk0 c hc).map (algebraMap k B))

/- English proof (translation)
Set `K` to `B ⧸ maximalIdeal B`. Use `letI : Field K := Ideal.Quotient.field _`. Use `haveI : Algebra.IsIntegral k K := Algebra.IsIntegral.of_finite k K`. Establish `hbij : Function.Bijective (algebraMap k K)` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : k ≃ₐ[k] K` to `AlgEquiv.ofBijective (Algebra.ofId k K) hbij`.

Use `⟨(e.symm : K →ₐ[k] k).comp (Ideal.Quotient.mkₐ k _), fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]`. Establish `h` using `e.apply_symm_apply (Ideal.Quotient.mk (maximalIdeal B) b)`. Conclude with `h.symm`.
-/
private lemma art_res [IsAlgClosed k] [Module.Finite k B] :
    ∃ π : B →ₐ[k] k, ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B := by
  let K := B ⧸ maximalIdeal B
  letI : Field K := Ideal.Quotient.field _
  haveI : Algebra.IsIntegral k K := Algebra.IsIntegral.of_finite k K
  have hbij : Function.Bijective (algebraMap k K) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) hbij
  refine ⟨(e.symm : K →ₐ[k] k).comp (Ideal.Quotient.mkₐ k _), fun b => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have h := e.apply_symm_apply (Ideal.Quotient.mk (maximalIdeal B) b)
  exact h.symm

/- English proof (translation)
Establish `halg : ∀ c b, φ (algebraMap k B c * b) = c * φ b` using `fun c b => by`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`. Establish `halg1 : ∀ c, φ (algebraMap k B c) = 0` using `fun c => by`. Use `halg c 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one, h1, mul_zero]`. Then use the resulting hypothesis.

Establish `hmul : ∀ a b, φ (a * b) = π a * φ b + π b * φ a` using `fun a b => by`. Establish `h` using `h2 _ (Ideal.mul_mem_mul (hπ a) (hπ b))`. Establish `e : (a - algebraMap k B (π a)) * (b - algebraMap k B (π b)) = a * b - algebraMap k B (π a) * b - algebraMap k B (π b) * a + algebraMap k B (π a * π b)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e, map_add, map_sub, map_sub, halg, halg, halg1]`. Take the linear combination `h`. Set `L : B →ₗ[k] DualNumber k` to `{ toFun := fun b => TrivSqZeroExt.inl (π b) + TrivSqZeroExt.inr (φ b) map_add' := fun a b => by`. Apply the tactic sequence `ext <;> simp`. Use the proof step `map_smul' := fun c b => by`.

Apply the tactic sequence `ext <;> simp }`. Use `⟨AlgHom.ofLinearMap L ?_ ?_, fun b => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [L, h1]`. Introduce `a b`. Use `ext`.

Simplify using `[L]`. Simplify using `[L, hmul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[L]`.
-/
private lemma art_der (π : B →ₐ[k] k) (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    (φ : B →ₗ[k] k) (h1 : φ 1 = 0) (h2 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ z = 0) :
    ∃ u : B →ₐ[k] DualNumber k, ∀ b, TrivSqZeroExt.snd (u b) = φ b := by
  have halg : ∀ c b, φ (algebraMap k B c * b) = c * φ b := fun c b => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have halg1 : ∀ c, φ (algebraMap k B c) = 0 := fun c => by
    have := halg c 1
    rwa [_root_.mul_one, h1, mul_zero] at this
  have hmul : ∀ a b, φ (a * b) = π a * φ b + π b * φ a := fun a b => by
    have h := h2 _ (Ideal.mul_mem_mul (hπ a) (hπ b))
    have e : (a - algebraMap k B (π a)) * (b - algebraMap k B (π b)) =
        a * b - algebraMap k B (π a) * b - algebraMap k B (π b) * a + algebraMap k B (π a * π b) := by
      rw [map_mul]; ring
    rw [e, map_add, map_sub, map_sub, halg, halg, halg1] at h
    linear_combination h
  let L : B →ₗ[k] DualNumber k :=
    { toFun := fun b => TrivSqZeroExt.inl (π b) + TrivSqZeroExt.inr (φ b)
      map_add' := fun a b => by
        ext <;> simp
      map_smul' := fun c b => by
        ext <;> simp }
  refine ⟨AlgHom.ofLinearMap L ?_ ?_, fun b => ?_⟩
  · ext <;> simp [L, h1]
  · intro a b
    ext
    · simp [L]
    · simp [L, hmul]
      ring
  · simp [L]

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite k B`. Establish `hfg : (maximalIdeal B).FG` using `IsNoetherian.noetherian _`. Establish `hjac : maximalIdeal B ≤ (⊥ : Ideal B).jacobson` using `(jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge`. Establish `nak : ∀ x, maximalIdeal B ≤ Ideal.span {x} ⊔ maximalIdeal B * maximalIdeal B → maximalIdeal B ≤ Ideal.span {x}` using `fun x h => Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac h`. Distinguish the cases in `hm : maximalIdeal B ≤ maximalIdeal B * maximalIdeal B`.

Conclude with `⟨0, Ideal.zero_mem _, nak 0 (hm.trans le_sup_right)⟩`. Take `⟨x, hxm, hx2⟩` from `SetLike.not_le_iff_exists.1 hm`. Use `⟨x, hxm, nak x fun y hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hy2`. Set `M2 : Submodule k B` to `(maximalIdeal B * maximalIdeal B).restrictScalars k`.

Establish `hM2 : ∀ z ∈ M2, z ∈ maximalIdeal B` using `fun z hz => Ideal.mul_le_left hz`. Set `W1 : Submodule k B` to `(k ∙ (1 : B)) ⊔ M2`. Establish `hW1 : ∀ z ∈ W1, ∃ c : k, ∃ t ∈ M2, z = algebraMap k B c + t` using `fun z hz => by`. Take `⟨a, ha, t, ht, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 ha`.

Conclude with `⟨c, t, ht, by rw [Algebra.algebraMap_eq_smul_one]⟩`. Establish `hxW : x ∉ W1` using `fun h => by`. Take `⟨c, t, ht, rfl⟩` from `hW1 _ h`. Establish `hc : algebraMap k B c ∈ maximalIdeal B`. Simplify using `using Ideal.sub_mem _ hxm (hM2 t ht)`.

Rewrite `hx2` using `[art_alg_mem hc, map_zero, zero_add]`. Conclude with `hx2 ht`. Set `W2 : Submodule k B` to `W1 ⊔ (k ∙ x)`. Establish `hyW : y ∉ W2` using `fun h => by`. Take `⟨a, ha, t, ht, rfl⟩` from `Submodule.mem_sup.1 h`.

Take `⟨d, rfl⟩` from `Submodule.mem_span_singleton.1 ht`. Take `⟨c, s, hs, rfl⟩` from `hW1 _ ha`. Establish `hdx : d • x ∈ maximalIdeal B`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ hxm`.

Establish `hc : algebraMap k B c ∈ maximalIdeal B`. Establish `h3` using `Ideal.sub_mem _ (Ideal.sub_mem _ hy (hM2 s hs)) hdx`. Establish `e : algebraMap k B c + s + d • x - s - d • x = algebraMap k B c` using `by abel`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Rewrite `hy2` using `[art_alg_mem hc, map_zero, zero_add]`.

Apply `hy2` to reduce the goal to its premises. Use `Submodule.mem_sup.2 ⟨d • x, ?_, s, hs, add_comm _ _⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)`. Take `⟨φ₁, hφ₁x, hφ₁⟩` from `Submodule.exists_le_ker_of_notMem hxW`.

Take `⟨φ₂, hφ₂y, hφ₂⟩` from `Submodule.exists_le_ker_of_notMem hyW`. Establish `h11 : φ₁ 1 = 0` using `hφ₁ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1))`. Establish `h12 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₁ z = 0` using `fun z hz => hφ₁ (Submodule.mem_sup_right hz)`. Establish `hW12 : W1 ≤ W2` using `le_sup_left`. Establish `h21 : φ₂ 1 = 0` using `hφ₂ (hW12 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1)))`.

Establish `h22 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₂ z = 0` using `fun z hz => hφ₂ (hW12 (Submodule.mem_sup_right hz))`. Establish `h2x : φ₂ x = 0` using `hφ₂ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))`. Take `⟨u, hu⟩` from `art_der π hπ φ₁ h11 h12`. Take `⟨v, hv⟩` from `art_der π hπ φ₂ h21 h22`. Take `⟨l, hl⟩` from `H u v ⟨x, by rwa [hu]⟩`.

Establish `hl0 : l = 0`. Use `hl x` as an intermediate fact. Rewrite `this` using `[hu, hv, h2x]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_right hφ₁x`. Use `hl y` as an intermediate fact.

Rewrite `this` using `[hu, hv, hl0, zero_mul]`. Conclude with `hφ₂y this`.
-/
private lemma art_gen [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    (H : ∀ u v : B →ₐ[k] DualNumber k, (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) →
      ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x)) :
    ∃ x ∈ maximalIdeal B, maximalIdeal B ≤ Ideal.span {x} := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hfg : (maximalIdeal B).FG := IsNoetherian.noetherian _
  have hjac : maximalIdeal B ≤ (⊥ : Ideal B).jacobson :=
    (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have nak : ∀ x, maximalIdeal B ≤ Ideal.span {x} ⊔ maximalIdeal B * maximalIdeal B →
      maximalIdeal B ≤ Ideal.span {x} := fun x h =>
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac h
  by_cases hm : maximalIdeal B ≤ maximalIdeal B * maximalIdeal B
  · exact ⟨0, Ideal.zero_mem _, nak 0 (hm.trans le_sup_right)⟩
  obtain ⟨x, hxm, hx2⟩ := SetLike.not_le_iff_exists.1 hm
  refine ⟨x, hxm, nak x fun y hy => ?_⟩
  by_contra hy2
  let M2 : Submodule k B := (maximalIdeal B * maximalIdeal B).restrictScalars k
  have hM2 : ∀ z ∈ M2, z ∈ maximalIdeal B := fun z hz => Ideal.mul_le_left hz
  let W1 : Submodule k B := (k ∙ (1 : B)) ⊔ M2
  have hW1 : ∀ z ∈ W1, ∃ c : k, ∃ t ∈ M2, z = algebraMap k B c + t := fun z hz => by
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, t, ht, by rw [Algebra.algebraMap_eq_smul_one]⟩
  have hxW : x ∉ W1 := fun h => by
    obtain ⟨c, t, ht, rfl⟩ := hW1 _ h
    have hc : algebraMap k B c ∈ maximalIdeal B := by
      simpa using Ideal.sub_mem _ hxm (hM2 t ht)
    rw [art_alg_mem hc, map_zero, zero_add] at hx2
    exact hx2 ht
  let W2 : Submodule k B := W1 ⊔ (k ∙ x)
  have hyW : y ∉ W2 := fun h => by
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 ht
    obtain ⟨c, s, hs, rfl⟩ := hW1 _ ha
    have hdx : d • x ∈ maximalIdeal B := by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hxm
    have hc : algebraMap k B c ∈ maximalIdeal B := by
      have h3 := Ideal.sub_mem _ (Ideal.sub_mem _ hy (hM2 s hs)) hdx
      have e : algebraMap k B c + s + d • x - s - d • x = algebraMap k B c := by abel
      rwa [e] at h3
    rw [art_alg_mem hc, map_zero, zero_add] at hy2
    apply hy2
    refine Submodule.mem_sup.2 ⟨d • x, ?_, s, hs, add_comm _ _⟩
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨φ₁, hφ₁x, hφ₁⟩ := Submodule.exists_le_ker_of_notMem hxW
  obtain ⟨φ₂, hφ₂y, hφ₂⟩ := Submodule.exists_le_ker_of_notMem hyW
  have h11 : φ₁ 1 = 0 := hφ₁ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1))
  have h12 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₁ z = 0 := fun z hz =>
    hφ₁ (Submodule.mem_sup_right hz)
  have hW12 : W1 ≤ W2 := le_sup_left
  have h21 : φ₂ 1 = 0 :=
    hφ₂ (hW12 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1)))
  have h22 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₂ z = 0 := fun z hz =>
    hφ₂ (hW12 (Submodule.mem_sup_right hz))
  have h2x : φ₂ x = 0 := hφ₂ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  obtain ⟨u, hu⟩ := art_der π hπ φ₁ h11 h12
  obtain ⟨v, hv⟩ := art_der π hπ φ₂ h21 h22
  obtain ⟨l, hl⟩ := H u v ⟨x, by rwa [hu]⟩
  have hl0 : l = 0 := by
    have := hl x
    rw [hu, hv, h2x] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hφ₁x
  have := hl y
  rw [hu, hv, hl0, zero_mul] at this
  exact hφ₂y this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, b, by simp⟩`. Consider the case `succ n ih`. Take `⟨s, hs, r, rfl⟩` from `ih`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 (hx (hπ r))`.

Establish `hmono : Submodule.span k (((Finset.range n).image fun i => x ^ i : Finset B) : Set B) ≤ Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B)`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz ⊢`. Take `⟨i, hi, rfl⟩` from `hz`.

Conclude with `⟨i, by omega, rfl⟩`. Establish `hxn : x ^ n ∈ Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B)`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]`. Conclude with `⟨n, by omega, rfl⟩`.

Use `⟨s + π r • x ^ n, Submodule.add_mem _ (hmono hs) (Submodule.smul_mem _ _ hxn), t, ?_⟩` and prove the remaining obligations. Establish `hr : r = algebraMap k B (π r) + t * x` using `by rw [ht]; ring`. Rewrite using `[Algebra.smul_def]`. Use `conv_lhs => rw [hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma art_span (π : B →ₐ[k] k) (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hx : maximalIdeal B ≤ Ideal.span {x}) (n : ℕ) (b : B) :
    ∃ s ∈ Submodule.span k (((Finset.range n).image fun i => x ^ i : Finset B) : Set B),
      ∃ r, b = s + x ^ n * r := by
  induction n with
  | zero => exact ⟨0, Submodule.zero_mem _, b, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, r, rfl⟩ := ih
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hx (hπ r))
    have hmono : Submodule.span k (((Finset.range n).image fun i => x ^ i : Finset B) : Set B) ≤
        Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B) := by
      refine Submodule.span_mono ?_
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz ⊢
      obtain ⟨i, hi, rfl⟩ := hz
      exact ⟨i, by omega, rfl⟩
    have hxn : x ^ n ∈ Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B) := by
      refine Submodule.subset_span ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨n, by omega, rfl⟩
    refine ⟨s + π r • x ^ n, Submodule.add_mem _ (hmono hs) (Submodule.smul_mem _ _ hxn), t, ?_⟩
    have hr : r = algebraMap k B (π r) + t * x := by rw [ht]; ring
    rw [Algebra.smul_def]
    conv_lhs => rw [hr]
    ring

/- English proof (translation)
Establish `hle : Module.length B B ≤ Module.length k B`. Rewrite using `[Module.length_eq_height, Module.length_eq_height]`. Establish `hs : StrictMono (fun I : Submodule B B => I.restrictScalars k)` using `fun I J h => by`. Use `lt_of_le_of_ne (fun z hz => h.le hz) fun e => h.ne ?_` and prove the remaining obligations. Conclude with `Submodule.restrictScalars_injective k B B e`.

Conclude with `Order.height_le_height_apply_of_strictMono _ hs ⊤`. Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[Module.length_eq_finrank]`. Establish `htop : Submodule.span k (((Finset.range q).image fun i => x ^ i : Finset B) : Set B) = ⊤`. Use `eq_top_iff.2 fun b _ => ?_` and prove the remaining obligations.

Take `⟨s, hs, r, rfl⟩` from `art_span π hπ hx q b`. Rewrite using `[h0, zero_mul, add_zero]` and apply the resulting hypothesis. Establish `h1` using `finrank_span_finset_le_card (R := k) ((Finset.range q).image fun i => x ^ i)`. Establish `h2 : Module.finrank k B ≤ q`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Set.finrank, htop, finrank_top]`. Use `_ ≤ _ := h1`. Use `_ ≤ (Finset.range q).card := Finset.card_image_le`. Use `_ = q := Finset.card_range q`. Conclude with `h2` after adjusting the coercions.
-/
private lemma art_length [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hx : maximalIdeal B ≤ Ideal.span {x}) {q : ℕ} (h0 : x ^ q = 0) :
    Module.length B B ≤ (q : ℕ∞) := by
  have hle : Module.length B B ≤ Module.length k B := by
    rw [Module.length_eq_height, Module.length_eq_height]
    have hs : StrictMono (fun I : Submodule B B => I.restrictScalars k) := fun I J h => by
      refine lt_of_le_of_ne (fun z hz => h.le hz) fun e => h.ne ?_
      exact Submodule.restrictScalars_injective k B B e
    exact Order.height_le_height_apply_of_strictMono _ hs ⊤
  refine hle.trans ?_
  rw [Module.length_eq_finrank]
  have htop : Submodule.span k (((Finset.range q).image fun i => x ^ i : Finset B) : Set B) = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨s, hs, r, rfl⟩ := art_span π hπ hx q b
    rwa [h0, zero_mul, add_zero]
  have h1 := finrank_span_finset_le_card (R := k) ((Finset.range q).image fun i => x ^ i)
  have h2 : Module.finrank k B ≤ q := by
    calc Module.finrank k B = Set.finrank k (((Finset.range q).image fun i => x ^ i : Finset B) : Set B) := by
          rw [Set.finrank, htop, finrank_top]
      _ ≤ _ := h1
      _ ≤ (Finset.range q).card := Finset.card_image_le
      _ = q := Finset.card_range q
  exact_mod_cast h2

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite k B`. Take `⟨N, hN⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := B)`. Rewrite `hN` using `[jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Establish `hxN : x ^ N = 0`. Use `Ideal.pow_mem_pow hxm N` as an intermediate fact.

Rewrite `this` using `[hN]`. Simplify using `using this`. Set `ψ : k[X] →ₐ[k] B` to `aeval x`. Establish `hsurj : Function.Surjective ψ` using `fun b => by`. Take `⟨s, hs, r, rfl⟩` from `art_span π hπ hx N b`.

Rewrite using `[hxN, zero_mul, add_zero]`. Establish `: Submodule.span k (((Finset.range N).image fun i => x ^ i : Finset B) : Set B) ≤ LinearMap.range ψ.toLinearMap`. Use `Submodule.span_le.2 fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz`. Take `⟨i, -, rfl⟩` from `hz`.

Conclude with `⟨X ^ i, by simp [ψ]⟩`. Take `⟨P, hP⟩` from `this hs`. Conclude with `⟨P, hP⟩`. Establish `hker : RingHom.ker ψ.toRingHom ≤ RingHom.ker (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _).toRingHom` using `fun P hP => by`. Establish `hP0 : aeval x P = 0` using `hP`.

Establish `hdvd : (X ^ (q + 1) : k[X]) ∣ P`. Distinguish the cases in `hne : P = 0`. Simplify using `[hne]`. Take `⟨Q, hQ, hnd⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hne 0`. Rewrite `hQ`, `hnd` using `[C_0, sub_zero]`.

Use `set e := rootMultiplicity 0 P`. Establish `hc : Q.coeff 0 ≠ 0` using `fun h => hnd (X_dvd_iff.2 h)`. Establish `hunit : IsUnit (aeval x Q)`. Assume the negation of the conclusion as `hu`. Establish `hmem : aeval x Q ∈ maximalIdeal B` using `(mem_maximalIdeal _).2 hu`.

Establish `hdiv` using `congrArg (aeval x) (divX_mul_X_add Q)`. Rewrite `hdiv` using `[map_add, map_mul, aeval_X, aeval_C]`. Establish `: algebraMap k B (Q.coeff 0) ∈ maximalIdeal B`. Establish `h3` using `Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (aeval x (divX Q)) hxm)`. Rewrite `h3` using `[← hdiv, add_sub_cancel_left]`. Then use the resulting hypothesis.

Conclude with `hc (art_alg_mem this)`. Establish `hxe : x ^ e = 0`. Rewrite `hP0` using `[hQ, map_mul, map_pow, aeval_X]`. Conclude with `(hunit.mul_left_eq_zero).1 hP0`. Establish `hqe : q + 1 ≤ e`.

Assume the negation of the conclusion as `hlt`. Apply `hq` to reduce the goal to its premises. Establish `: q = e + (q - e)` using `by omega`. Rewrite using `[this, pow_add, hxe, zero_mul]`. Rewrite using `[hQ]`.

Conclude with `(pow_dvd_pow X hqe).mul_right Q`. Use `show (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _) P = 0`. Rewrite using `[AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]`. Conclude with `hdvd`. Use `⟨AlgHom.liftOfSurjective ψ hsurj _ hker, ?_⟩` and prove the remaining obligations.

Use `AlgHom.liftOfSurjective_apply ψ hsurj (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X]))) hker X` as an intermediate fact. Establish `hX : ψ X = x` using `by simp [ψ]`. Rewrite `this` using `[hX]`. Rewrite using `[this, aeval_X]`.
-/
private lemma art_map [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hxm : x ∈ maximalIdeal B) (hx : maximalIdeal B ≤ Ideal.span {x}) {q : ℕ} (hq : x ^ q ≠ 0) :
    ∃ u : B →ₐ[k] AdjoinRoot (X ^ (q + 1) : k[X]), u x = AdjoinRoot.root (X ^ (q + 1) : k[X]) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  have hxN : x ^ N = 0 := by
    have := Ideal.pow_mem_pow hxm N
    rw [hN] at this
    simpa using this
  let ψ : k[X] →ₐ[k] B := aeval x
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨s, hs, r, rfl⟩ := art_span π hπ hx N b
    rw [hxN, zero_mul, add_zero]
    have : Submodule.span k (((Finset.range N).image fun i => x ^ i : Finset B) : Set B) ≤
        LinearMap.range ψ.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz
      obtain ⟨i, -, rfl⟩ := hz
      exact ⟨X ^ i, by simp [ψ]⟩
    obtain ⟨P, hP⟩ := this hs
    exact ⟨P, hP⟩
  have hker : RingHom.ker ψ.toRingHom ≤
      RingHom.ker (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _).toRingHom := fun P hP => by
    have hP0 : aeval x P = 0 := hP
    have hdvd : (X ^ (q + 1) : k[X]) ∣ P := by
      by_cases hne : P = 0
      · simp [hne]
      obtain ⟨Q, hQ, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hne 0
      rw [C_0, sub_zero] at hQ hnd
      set e := rootMultiplicity 0 P
      have hc : Q.coeff 0 ≠ 0 := fun h => hnd (X_dvd_iff.2 h)
      have hunit : IsUnit (aeval x Q) := by
        by_contra hu
        have hmem : aeval x Q ∈ maximalIdeal B := (mem_maximalIdeal _).2 hu
        have hdiv := congrArg (aeval x) (divX_mul_X_add Q)
        rw [map_add, map_mul, aeval_X, aeval_C] at hdiv
        have : algebraMap k B (Q.coeff 0) ∈ maximalIdeal B := by
          have h3 := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (aeval x (divX Q)) hxm)
          rwa [← hdiv, add_sub_cancel_left] at h3
        exact hc (art_alg_mem this)
      have hxe : x ^ e = 0 := by
        rw [hQ, map_mul, map_pow, aeval_X] at hP0
        exact (hunit.mul_left_eq_zero).1 hP0
      have hqe : q + 1 ≤ e := by
        by_contra hlt
        apply hq
        have : q = e + (q - e) := by omega
        rw [this, pow_add, hxe, zero_mul]
      rw [hQ]
      exact (pow_dvd_pow X hqe).mul_right Q
    show (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _) P = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hdvd
  refine ⟨AlgHom.liftOfSurjective ψ hsurj _ hker, ?_⟩
  have := AlgHom.liftOfSurjective_apply ψ hsurj (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X]))) hker X
  have hX : ψ X = x := by simp [ψ]
  rw [hX] at this
  rw [this, aeval_X]

end ArtB

end UpperTheory.Gal.Ord

/- English proof (translation)
Introduce `p _ k _ _ _ B _ _ _ _ f hf H hL`. Take `⟨π, hπ⟩` from `art_res (k := k) (B := B)`. Take `⟨x, hxm, hx⟩` from `art_gen π hπ H`. Establish `hxq : x ^ p ^ f ≠ 0` using `fun h => not_le.2 hL (art_length π hπ hx h)`. Take `⟨τ, j, hj, hjτ, hτ⟩` from `art_tangent p k f hf`.

Take `⟨u, hu⟩` from `art_map π hπ hxm hx hxq`. Use `⟨_, inferInstance, inferInstance, τ, j, u, hj, hjτ, x, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hτ]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.Ord.art :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (B : Type) [CommRing B] [IsLocalRing B] [Algebra k B] [Module.Finite k B] (f : ℕ), 0 < f →
      (∀ u v : B →ₐ[k] DualNumber k, (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) → ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x)) →
      ((p ^ f : ℕ) : ℕ∞) < Module.length B B →
      ∃ (T : Type) (_ : CommRing T) (_ : Algebra k T) (τ : T →ₐ[k] DualNumber k) (j : DualNumber k →+* T) (u : B →ₐ[k] T),
        Function.Injective j ∧ (∀ x, j (τ x) = x ^ p ^ f) ∧ ∃ x, TrivSqZeroExt.snd (τ (u x)) ≠ 0 := by
  intro p _ k _ _ _ B _ _ _ _ f hf H hL
  obtain ⟨π, hπ⟩ := art_res (k := k) (B := B)
  obtain ⟨x, hxm, hx⟩ := art_gen π hπ H
  have hxq : x ^ p ^ f ≠ 0 := fun h => not_le.2 hL (art_length π hπ hx h)
  obtain ⟨τ, j, hj, hjτ, hτ⟩ := art_tangent p k f hf
  obtain ⟨u, hu⟩ := art_map π hπ hxm hx hxq
  refine ⟨_, inferInstance, inferInstance, τ, j, u, hj, hjτ, x, ?_⟩
  rw [hu, hτ]
  simp
