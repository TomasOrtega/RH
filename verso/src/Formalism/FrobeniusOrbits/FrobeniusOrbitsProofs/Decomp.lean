import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois

namespace Decomp

/- English proof (translation)
Establish `hn : Nat.card (ℤ ⧸ Q.under ℤ) = p`. Rewrite using `[← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ), Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]`. Establish `key : ∀ y : 𝓞 M, Ideal.Quotient.mk Q (F • y) = Ideal.Quotient.mk Q y ^ p`. Introduce `y`. Rewrite using `[← map_pow, Ideal.Quotient.eq, ← hn]`.

Conclude with `hF y`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ' F k, mul_smul, key, ih, ← pow_mul, ← pow_succ p k]`.
-/
theorem frob_pow_mk {M : Type} [Field M] [NumberField M] (p : ℕ)
    (Q : Ideal (𝓞 M)) [Q.LiesOver (span {(p : ℤ)})] (F : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (k : ℕ) (x : 𝓞 M) :
    Ideal.Quotient.mk Q ((F ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (p ^ k) := by
  have hn : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ),
      Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have key : ∀ y : 𝓞 M, Ideal.Quotient.mk Q (F • y) = Ideal.Quotient.mk Q y ^ p := by
    intro y
    rw [← map_pow, Ideal.Quotient.eq, ← hn]
    exact hF y
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' F k, mul_smul, key, ih, ← pow_mul, ← pow_succ p k]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Establish `hund : span {(p : ℤ)} = Q.under ℤ` using `Ideal.LiesOver.over`. Establish `hQ0 : Q ≠ ⊥`. Introduce `hQ`.

Establish `h1 : (p : ℤ) ∈ Q.under ℤ`. Rewrite using `[← hund]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `h2` using `Ideal.mem_comap.mp h1`. Rewrite `h2` using `[hQ, Ideal.mem_bot]`.

Conclude with `hp.ne_zero (by simpa using h2)`. Use `haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0`. Use `letI : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q`. Use `haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0`. Use `haveI : CharP (𝓞 M ⧸ Q) p := by`.

Use `⟨fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (Ideal.Quotient.mk Q) n, Ideal.Quotient.eq_zero_iff_mem]`. Establish `e1 : (n : 𝓞 M) ∈ Q ↔ (n : ℤ) ∈ Q.under ℤ` using `⟨fun h => Ideal.mem_comap.mpr (by rwa [map_natCast]), fun h => by simpa using Ideal.mem_comap.mp h⟩`. Rewrite using `[e1, ← hund, Ideal.mem_span_singleton]`. Use `norm_cast`.

Use `letI : Algebra (ZMod p) (𝓞 M ⧸ Q) := ZMod.algebra _ p`. Establish `hσQ : Q ≤ Q.comap (MulSemiringAction.toRingHom _ (𝓞 M) σ)`. Introduce `y hy`. Rewrite using `[Ideal.mem_comap, MulSemiringAction.toRingHom_apply]`. Establish `hσ' : σ • Q = Q` using `MulAction.mem_stabilizer_iff.mp hσ`.

Rewrite using `[← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]`. Conclude with `hy`. Set `sb : (𝓞 M ⧸ Q) →+* (𝓞 M ⧸ Q)` to `Ideal.quotientMap Q (MulSemiringAction.toRingHom _ (𝓞 M) σ) hσQ`. Set `sa : (𝓞 M ⧸ Q) →ₐ[ZMod p] (𝓞 M ⧸ Q)` to `{ sb with commutes' := fun c => by`. Express the relevant statement in the definitionally equal form `sb (algebraMap (ZMod p) _ c) = algebraMap (ZMod p) _ c`.

Rewrite using `[← ZMod.natCast_zmod_val c, map_natCast, map_natCast] }`. Take `⟨⟨n, hlt⟩, hn⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (𝓞 M ⧸ Q)).2 sa`. Establish `hn' : FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ n = sa` using `hn`. Establish `key : ∀ m : ℕ, ∀ y : 𝓞 M ⧸ Q, (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ m) y = y ^ (p ^ m)`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `y`.

Rewrite using `[pow_succ' (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q)) m, AlgHom.mul_apply, ih, FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, ← pow_succ p m]`. Use `⟨n, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Establish `h1 : sa (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q (σ • x)` using `rfl`. Rewrite using `[← h1, ← hn', key, frob_pow_mk p Q F hF n x]`.
-/
theorem stab_frob_pow {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∀ x : 𝓞 M, σ • x - (F ^ k) • x ∈ Q := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hund : span {(p : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hQ0 : Q ≠ ⊥ := by
    intro hQ
    have h1 : (p : ℤ) ∈ Q.under ℤ := by
      rw [← hund]
      exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.mp h1
    rw [hQ, Ideal.mem_bot] at h2
    exact hp.ne_zero (by simpa using h2)
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  letI : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  haveI : CharP (𝓞 M ⧸ Q) p := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk Q) n, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : (n : 𝓞 M) ∈ Q ↔ (n : ℤ) ∈ Q.under ℤ :=
      ⟨fun h => Ideal.mem_comap.mpr (by rwa [map_natCast]),
        fun h => by simpa using Ideal.mem_comap.mp h⟩
    rw [e1, ← hund, Ideal.mem_span_singleton]
    norm_cast
  letI : Algebra (ZMod p) (𝓞 M ⧸ Q) := ZMod.algebra _ p
  have hσQ : Q ≤ Q.comap (MulSemiringAction.toRingHom _ (𝓞 M) σ) := by
    intro y hy
    rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
    have hσ' : σ • Q = Q := MulAction.mem_stabilizer_iff.mp hσ
    rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
    exact hy
  let sb : (𝓞 M ⧸ Q) →+* (𝓞 M ⧸ Q) :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ (𝓞 M) σ) hσQ
  let sa : (𝓞 M ⧸ Q) →ₐ[ZMod p] (𝓞 M ⧸ Q) :=
    { sb with
      commutes' := fun c => by
        change sb (algebraMap (ZMod p) _ c) = algebraMap (ZMod p) _ c
        rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast] }
  obtain ⟨⟨n, hlt⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (𝓞 M ⧸ Q)).2 sa
  have hn' : FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ n = sa := hn
  have key : ∀ m : ℕ, ∀ y : 𝓞 M ⧸ Q,
      (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ m) y = y ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ' (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q)) m, AlgHom.mul_apply, ih,
        FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, ← pow_succ p m]
  refine ⟨n, fun x => ?_⟩
  rw [← Ideal.Quotient.eq]
  have h1 : sa (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q (σ • x) := rfl
  rw [← h1, ← hn', key, frob_pow_mk p Q F hF n x]

/- English proof (translation)
Take `⟨k, hk⟩` from `stab_frob_pow p Q F σ hF hσ`. Use `⟨k, σ * (F ^ k)⁻¹, fun x => ?_, by simp⟩` and prove the remaining obligations. Establish `hx` using `hk ((F ^ k)⁻¹ • x)`. Rewrite `hx` using `[smul_inv_smul, ← mul_smul]`. Then use the resulting hypothesis.
-/
theorem stab_eq_inertia_mul {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∃ ρ : Gal(M/ℚ), (∀ x : 𝓞 M, ρ • x - x ∈ Q) ∧ σ = ρ * F ^ k := by
  obtain ⟨k, hk⟩ := stab_frob_pow p Q F σ hF hσ
  refine ⟨k, σ * (F ^ k)⁻¹, fun x => ?_, by simp⟩
  have hx := hk ((F ^ k)⁻¹ • x)
  rwa [smul_inv_smul, ← mul_smul] at hx

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `z`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h (g⁻¹ • z), smul_inv_smul]`.
-/
theorem mem_stab_of {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G)
    (I : Ideal S) (h : ∀ z : S, g • z ∈ I ↔ z ∈ I) : g ∈ MulAction.stabilizer G I := by
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h (g⁻¹ • z), smul_inv_smul]

/- English proof (translation)
Rewrite `hg` using `[MulAction.mem_stabilizer_iff]`. Use `conv_lhs => rw [← hg]`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]`.
-/
theorem smul_mem_iff_of_stab {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
    (g : G) (I : Ideal S) (hg : g ∈ MulAction.stabilizer G I) (z : S) : g • z ∈ I ↔ z ∈ I := by
  rw [MulAction.mem_stabilizer_iff] at hg
  conv_lhs => rw [← hg]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

section Host

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Use `ext`. Use `first`. Consider the case `exact hστ x`. Consider the case `simpa using hστ x`.
-/
theorem restrict_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : 𝓞 (hostE ζ a b)) :
    algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x := by
  ext
  first
    | exact hστ x
    | simpa using hστ x

/- English proof (translation)
Apply the tactic sequence `rw [(Ideal.LiesOver.over : P = Q.under (𝓞 (hostE ζ a b)))] <;> exact Ideal.mem_comap`.
-/
theorem mem_P_iff (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (x : 𝓞 (hostE ζ a b)) : x ∈ P ↔ algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x ∈ Q := by
  rw [(Ideal.LiesOver.over : P = Q.under (𝓞 (hostE ζ a b)))] <;> exact Ideal.mem_comap

/- English proof (translation)
Apply `mem_stab_of` to reduce the goal to its premises. Introduce `z`. Rewrite using `[mem_P_iff P Q, mem_P_iff P Q, restrict_smul σ τ hστ, smul_mem_iff_of_stab τ Q hτ]`.
-/
theorem stab_restrict (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) Q) :
    σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P := by
  apply mem_stab_of
  intro z
  rw [mem_P_iff P Q, mem_P_iff P Q, restrict_smul σ τ hστ, smul_mem_iff_of_stab τ Q hτ]

/- English proof (translation)
Establish `hPQ : P.under ℤ = Q.under ℤ` using `(Ideal.LiesOver.over : span {(p : ℤ)} = P.under ℤ).symm.trans (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ)`. Introduce `x`. Establish `h2` using `hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)`. Rewrite using `[mem_P_iff P Q, map_sub, map_pow, hPQ]`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Conclude with `restrict_smul σ τ hστ x`.
-/
theorem frob_restrict (p : ℕ) (Q : Ideal (𝓞 L)) [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (hτ : IsArithFrobAt ℤ τ Q) :
    IsArithFrobAt ℤ σ P := by
  have hPQ : P.under ℤ = Q.under ℤ :=
    (Ideal.LiesOver.over : span {(p : ℤ)} = P.under ℤ).symm.trans
      (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ)
  intro x
  have h2 := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
  rw [mem_P_iff P Q, map_sub, map_pow, hPQ]
  convert h2 using 2
  exact restrict_smul σ τ hστ x

/- English proof (translation)
The claim follows from `QuotientGroup.mk_one _`.
-/
theorem hcl_at_one (e : ℕ) : hcl e 1 = 1 := QuotientGroup.mk_one _

/- English proof (translation)
Unfold `hcl`. Rewrite using `[QuotientGroup.eq_one_iff]`. Conclude with `Subgroup.mem_zpowers _`.
-/
theorem hcl_neg_one' (e : ℕ) : hcl e (-1) = 1 := by
  unfold hcl
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

/- English proof (translation)
Use `show hPart e ζ a b ρ = 1`. Unfold `hPart`. Use `split_ifs with hex`. Use `swap`. Both sides reduce to the same expression.

Establish `hu` using `Classical.choose_spec hex`. Generalize the expression as in `Classical.choose hex = u at hu ⊢`. Take `⟨n, hn⟩ : ∃ n, (u : ZMod (2 ^ (e + 2))).val = n` from `⟨_, rfl⟩`. Rewrite `hu` using `[hn]`. Establish `hnu : ((n : ℕ) : ZMod (2 ^ (e + 2))) = u`.

Rewrite using `[← hn]`. Conclude with `ZMod.natCast_zmod_val _`. Establish `hprim : IsPrimitiveRoot ζ (2 ^ (e + 2))` using `h.1`. Establish `hN1 : 1 ≤ 2 ^ (e + 2)` using `Nat.one_le_two_pow`. Establish `hζN : ζ ^ (2 ^ (e + 2)) = 1` using `hprim.pow_eq_one`.

Establish `hinv : ζ⁻¹ = ζ ^ (2 ^ (e + 2) - 1)`. Use `(eq_inv_of_mul_eq_one_right ?_).symm` and prove the remaining obligations. Rewrite using `[← pow_succ', Nat.sub_add_cancel hN1, hζN]`. Establish `hζint : IsIntegral ℤ ζ` using `hprim.isIntegral (by positivity)`. Establish `hζiint : IsIntegral ℤ ζ⁻¹`.

Rewrite using `[hinv]`. Conclude with `hζint.pow _`. Establish `hθint : IsIntegral ℤ (thE ζ a b)` using `(isIntegral_algebraMap_iff (algebraMap (hostE ζ a b) L).injective).mp (hζint.add hζiint)`. Take `⟨zz, hzz⟩ : ∃ z : 𝓞 L, (z : L) = ζ` from `⟨⟨ζ, hζint⟩, rfl⟩`. Take `⟨tt, htt⟩ : ∃ t : 𝓞 (hostE ζ a b), (t : hostE ζ a b) = thE ζ a b` from `⟨⟨_, hθint⟩, rfl⟩`.

Establish `hth : ((thE ζ a b : hostE ζ a b) : L) = ζ + ζ⁻¹` using `rfl`. Establish `hmemQ : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) ∈ Q` using `(mem_P_iff P Q _).mp (hρ tt)`. Establish `heq : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) = zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1)` using `by ext1`. Establish `e1 : ((algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) : 𝓞 L) : L) = ((ρ (tt : hostE ζ a b) : hostE ζ a b) : L) - ((tt : hostE ζ a b) : L)` using `by first`. Consider the case `rfl`.

Consider the case `simp`. Establish `e2 : ((zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) : 𝓞 L) : L) = (zz : L) ^ n + (zz : L) ^ ((2 ^ (e + 2) - 1) * n) - (zz : L) - (zz : L) ^ (2 ^ (e + 2) - 1)` using `by first`. Consider the case `rfl`. Consider the case `simp`. Rewrite using `[e1, e2, htt, hth, hu, hzz, pow_mul, ← hinv]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨zq, hzq⟩ : ∃ w, Ideal.Quotient.mk Q zz = w` from `⟨_, rfl⟩`. Establish `hrel : zq ^ n + zq ^ ((2 ^ (e + 2) - 1) * n) = zq + zq ^ (2 ^ (e + 2) - 1)`. Establish `h0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmemQ`. Rewrite `h0` using `[heq]`.

Simplify using `only [map_sub, map_add, map_pow, hzq] at h0`. Take the linear combination `h0`. Establish `hzzN : zz ^ (2 ^ (e + 2)) = 1` using `by ext1`. Establish `e3 : ((zz ^ (2 ^ (e + 2)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 2))` using `by first`. Consider the case `rfl`.

Consider the case `simp`. Rewrite using `[e3, hzz, hζN]`. Apply the tactic sequence `all_goals first | rfl | simp`. Establish `hneg : ζ ^ (2 ^ (e + 1)) = -1`. Establish `hsq : ζ ^ (2 ^ (e + 1)) * ζ ^ (2 ^ (e + 1)) = 1`.

Rewrite using `[← pow_add, ← two_mul, ← pow_succ']`. Conclude with `hζN`. Break down `mul_self_eq_one_iff.mp hsq with h1 | h1` into its components or cases. It suffices to derive a contradiction. Establish `hdv` using `(hprim.pow_eq_one_iff_dvd _).mp h1`.

Establish `h4` using `Nat.le_of_dvd (by positivity) hdv`. Establish `hx : 0 < 2 ^ (e + 1)` using `by positivity`. Establish `h5 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1)` using `by ring`. Use linear arithmetic over natural numbers and integers. Conclude with `h1`.

Establish `hzzneg : zz ^ (2 ^ (e + 1)) = -1` using `by ext1`. Establish `e4 : ((zz ^ (2 ^ (e + 1)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 1))` using `by first`. Consider the case `rfl`. Consider the case `simp`. Rewrite using `[e4, hzz, hneg]`.

Apply the tactic sequence `all_goals first | rfl | simp`. Establish `h2notQ : (2 : 𝓞 L) ∉ Q`. Introduce `h2`. Establish `h2' : (2 : ℤ) ∈ Q.under ℤ` using `Ideal.mem_comap.mpr (by simpa using h2)`. Rewrite `h2'` using `[← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ), Ideal.mem_span_singleton]`.

Establish `h6 : p ∣ 2` using `by exact_mod_cast h2'`. Break down `Nat.prime_two.eq_one_or_self_of_dvd p h6 with h3 | h3` into its components or cases. Conclude with `hp.one_lt.ne' h3`. Conclude with `hp2 h3`. Establish `hfin : zq ^ (2 ^ (e + 2)) = 1`.

Rewrite using `[← hzq, ← map_pow, hzzN, map_one]`. Establish `hnot : ¬ zq ^ (2 ^ (e + 1)) = 1`. Introduce `h1`. Rewrite `h1` using `[← hzq, ← map_pow, hzzneg, map_neg, map_one]`. Apply `h2notQ` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]`. Establish `h7 : (2 : 𝓞 L ⧸ Q) = 1 - (-1)` using `by ring`. Rewrite using `[h7, h1, sub_self]`. Establish `horder : orderOf zq = 2 ^ (e + 2)` using `orderOf_eq_prime_pow hnot hfin`. Establish `hpz : IsPrimitiveRoot zq (2 ^ (e + 2))` using `horder ▸ IsPrimitiveRoot.orderOf zq`.

Establish `hCD : zq * zq ^ (2 ^ (e + 2) - 1) = 1`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hN1, hfin]`. Establish `hAB : zq ^ n * zq ^ ((2 ^ (e + 2) - 1) * n) = 1`. Rewrite using `[pow_mul, ← mul_pow, hCD, one_pow]`. Establish `hkey : (zq ^ n * zq - 1) * (zq ^ n * zq ^ (2 ^ (e + 2) - 1) - 1) = 0`.

Take the linear combination `(zq ^ n) * hrel - hAB + (zq ^ n) ^ 2 * hCD`. Break down `mul_eq_zero.mp hkey with h1 | h1` into its components or cases. Establish `h1' : zq ^ (n + 1) = 1`. Rewrite using `[pow_succ]`. Conclude with `sub_eq_zero.mp h1`.

Establish `hd` using `(hpz.pow_eq_one_iff_dvd _).mp h1'`. Establish `hc : ((n + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0` using `(CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd`. Establish `hu' : (u : ZMod (2 ^ (e + 2))) = -1`. Rewrite using `[← hnu]`. Move the coercions through the operations in `at hc`.

Take the linear combination `hc`. Establish `hu1 : u = -1` using `Units.ext (by rw [hu', Units.val_neg, Units.val_one])`. Rewrite using `[hu1]`. Conclude with `hcl_neg_one' e`. Establish `h1' : zq ^ (n + (2 ^ (e + 2) - 1)) = 1`.

Rewrite using `[pow_add]`. Conclude with `sub_eq_zero.mp h1`. Establish `hd` using `(hpz.pow_eq_one_iff_dvd _).mp h1'`. Establish `hc : ((n + (2 ^ (e + 2) - 1) : ℕ) : ZMod (2 ^ (e + 2))) = 0` using `(CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd`. Establish `hu' : (u : ZMod (2 ^ (e + 2))) = 1`.

Rewrite `hc` using `[Nat.cast_add, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, hnu]`. Take the linear combination `hc`. Establish `hu1 : u = 1` using `Units.ext (by rw [hu', Units.val_one])`. Rewrite using `[hu1]`. Conclude with `hcl_at_one e`.
-/
theorem hPart_inertia (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] (ρ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hρ : ∀ x : 𝓞 (hostE ζ a b), ρ • x - x ∈ P) : (galE e ζ a b ρ).2 = 1 := by
  show hPart e ζ a b ρ = 1
  unfold hPart
  split_ifs with hex
  swap
  · rfl
  have hu := Classical.choose_spec hex
  generalize Classical.choose hex = u at hu ⊢
  obtain ⟨n, hn⟩ : ∃ n, (u : ZMod (2 ^ (e + 2))).val = n := ⟨_, rfl⟩
  rw [hn] at hu
  have hnu : ((n : ℕ) : ZMod (2 ^ (e + 2))) = u := by
    rw [← hn]
    exact ZMod.natCast_zmod_val _
  have hprim : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1
  have hN1 : 1 ≤ 2 ^ (e + 2) := Nat.one_le_two_pow
  have hζN : ζ ^ (2 ^ (e + 2)) = 1 := hprim.pow_eq_one
  have hinv : ζ⁻¹ = ζ ^ (2 ^ (e + 2) - 1) := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hN1, hζN]
  have hζint : IsIntegral ℤ ζ := hprim.isIntegral (by positivity)
  have hζiint : IsIntegral ℤ ζ⁻¹ := by
    rw [hinv]
    exact hζint.pow _
  have hθint : IsIntegral ℤ (thE ζ a b) :=
    (isIntegral_algebraMap_iff (algebraMap (hostE ζ a b) L).injective).mp (hζint.add hζiint)
  obtain ⟨zz, hzz⟩ : ∃ z : 𝓞 L, (z : L) = ζ := ⟨⟨ζ, hζint⟩, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ t : 𝓞 (hostE ζ a b), (t : hostE ζ a b) = thE ζ a b := ⟨⟨_, hθint⟩, rfl⟩
  have hth : ((thE ζ a b : hostE ζ a b) : L) = ζ + ζ⁻¹ := rfl
  have hmemQ : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) ∈ Q := (mem_P_iff P Q _).mp (hρ tt)
  have heq : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) =
      zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) := by
    ext1
    have e1 : ((algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) : 𝓞 L) : L) =
        ((ρ (tt : hostE ζ a b) : hostE ζ a b) : L) - ((tt : hostE ζ a b) : L) := by
      first
        | rfl
        | simp
    have e2 : ((zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) : 𝓞 L) : L) =
        (zz : L) ^ n + (zz : L) ^ ((2 ^ (e + 2) - 1) * n) - (zz : L) - (zz : L) ^ (2 ^ (e + 2) - 1) := by
      first
        | rfl
        | simp
    rw [e1, e2, htt, hth, hu, hzz, pow_mul, ← hinv]
    ring
  obtain ⟨zq, hzq⟩ : ∃ w, Ideal.Quotient.mk Q zz = w := ⟨_, rfl⟩
  have hrel : zq ^ n + zq ^ ((2 ^ (e + 2) - 1) * n) = zq + zq ^ (2 ^ (e + 2) - 1) := by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemQ
    rw [heq] at h0
    simp only [map_sub, map_add, map_pow, hzq] at h0
    linear_combination h0
  have hzzN : zz ^ (2 ^ (e + 2)) = 1 := by
    ext1
    have e3 : ((zz ^ (2 ^ (e + 2)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 2)) := by
      first
        | rfl
        | simp
    rw [e3, hzz, hζN]
    all_goals first | rfl | simp
  have hneg : ζ ^ (2 ^ (e + 1)) = -1 := by
    have hsq : ζ ^ (2 ^ (e + 1)) * ζ ^ (2 ^ (e + 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hζN
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have hdv := (hprim.pow_eq_one_iff_dvd _).mp h1
      have h4 := Nat.le_of_dvd (by positivity) hdv
      have hx : 0 < 2 ^ (e + 1) := by positivity
      have h5 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by ring
      omega
    · exact h1
  have hzzneg : zz ^ (2 ^ (e + 1)) = -1 := by
    ext1
    have e4 : ((zz ^ (2 ^ (e + 1)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 1)) := by
      first
        | rfl
        | simp
    rw [e4, hzz, hneg]
    all_goals first | rfl | simp
  have h2notQ : (2 : 𝓞 L) ∉ Q := by
    intro h2
    have h2' : (2 : ℤ) ∈ Q.under ℤ := Ideal.mem_comap.mpr (by simpa using h2)
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ), Ideal.mem_span_singleton] at h2'
    have h6 : p ∣ 2 := by exact_mod_cast h2'
    rcases Nat.prime_two.eq_one_or_self_of_dvd p h6 with h3 | h3
    · exact hp.one_lt.ne' h3
    · exact hp2 h3
  have hfin : zq ^ (2 ^ (e + 2)) = 1 := by
    rw [← hzq, ← map_pow, hzzN, map_one]
  have hnot : ¬ zq ^ (2 ^ (e + 1)) = 1 := by
    intro h1
    rw [← hzq, ← map_pow, hzzneg, map_neg, map_one] at h1
    apply h2notQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    have h7 : (2 : 𝓞 L ⧸ Q) = 1 - (-1) := by ring
    rw [h7, h1, sub_self]
  have horder : orderOf zq = 2 ^ (e + 2) := orderOf_eq_prime_pow hnot hfin
  have hpz : IsPrimitiveRoot zq (2 ^ (e + 2)) := horder ▸ IsPrimitiveRoot.orderOf zq
  have hCD : zq * zq ^ (2 ^ (e + 2) - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hN1, hfin]
  have hAB : zq ^ n * zq ^ ((2 ^ (e + 2) - 1) * n) = 1 := by
    rw [pow_mul, ← mul_pow, hCD, one_pow]
  have hkey : (zq ^ n * zq - 1) * (zq ^ n * zq ^ (2 ^ (e + 2) - 1) - 1) = 0 := by
    linear_combination (zq ^ n) * hrel - hAB + (zq ^ n) ^ 2 * hCD
  rcases mul_eq_zero.mp hkey with h1 | h1
  · have h1' : zq ^ (n + 1) = 1 := by
      rw [pow_succ]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = -1 := by
      rw [← hnu]
      push_cast at hc
      linear_combination hc
    have hu1 : u = -1 := Units.ext (by rw [hu', Units.val_neg, Units.val_one])
    rw [hu1]
    exact hcl_neg_one' e
  · have h1' : zq ^ (n + (2 ^ (e + 2) - 1)) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + (2 ^ (e + 2) - 1) : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Nat.cast_add, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, hnu] at hc
      linear_combination hc
    have hu1 : u = 1 := Units.ext (by rw [hu', Units.val_one])
    rw [hu1]
    exact hcl_at_one e

end Host

section Two

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Establish `h2 : (2 : ℤ) ∈ P.under ℤ`. Rewrite using `[← (Ideal.LiesOver.over : span {(2 : ℤ)} = P.under ℤ)]`. Conclude with `Ideal.mem_span_singleton_self 2`. Simplify using `using Ideal.mem_comap.mp h2`.
-/
theorem two_mem {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M))
    [P.LiesOver (span {(2 : ℤ)})] : (2 : 𝓞 M) ∈ P := by
  have h2 : (2 : ℤ) ∈ P.under ℤ := by
    rw [← (Ideal.LiesOver.over : span {(2 : ℤ)} = P.under ℤ)]
    exact Ideal.mem_span_singleton_self 2
  simpa using Ideal.mem_comap.mp h2

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, r + 1 = 4 * m` from `⟨(r + 1) / 4, by omega⟩`. Establish `hm' : (r : F) + 1 = 4 * (m : F)` using `by exact_mod_cast hm`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Simplify using the standard rewrite rules.

Take the linear combination `(1 / 4 : F) * hX - (1 / 4 : F) * hm'`.
-/
theorem omega_integral {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r + 1 = 4 * m := ⟨(r + 1) / 4, by omega⟩
  have hm' : (r : F) + 1 = 4 * (m : F) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · simp
    linear_combination (1 / 4 : F) * hX - (1 / 4 : F) * hm'

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[aE, h.2.1]`.
-/
theorem aE_sq_eq_neg_q (h : IsLayer (e + 2) q d ζ a b) :
    aE ζ a b ^ 2 = ((-(q : ℤ) : ℤ) : hostE ζ a b) := by
  apply Subtype.ext
  simp [aE, h.2.1]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[bE, h.2.2.1]`.
-/
theorem bE_sq' (h : IsLayer (e + 2) q d ζ a b) :
    bE ζ a b ^ 2 = ((-(d : ℤ) : ℤ) : hostE ζ a b) := by
  apply Subtype.ext
  simp [bE, h.2.2.1]

/- English proof (translation)
Establish `hbsq : bE ζ a b ^ 2 = -((d : ℕ) : hostE ζ a b)` using `by simpa using bE_sq' h`. Establish `hfix : σ (bE ζ a b) = bE ζ a b`. Assume the negation of the conclusion as `hne`. Establish `hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2`. Rewrite using `[← map_pow, hbsq, map_neg, map_natCast]`.

Establish `hσb : σ (bE ζ a b) = -(bE ζ a b)`. Establish `hm0 : (σ (bE ζ a b) - bE ζ a b) * (σ (bE ζ a b) + bE ζ a b) = 0`. Take the linear combination `hsq`. Break down `mul_eq_zero.mp hm0 with h1 | h1` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h1) hne`.

Conclude with `eq_neg_of_add_eq_zero_left h1`. Establish `hint : IsIntegral ℤ ((1 + bE ζ a b) / 2)` using `omega_integral (by omega) hbsq`. Take `⟨ω, hωv⟩ : ∃ ω : 𝓞 (hostE ζ a b), (ω : hostE ζ a b) = (1 + bE ζ a b) / 2` from `⟨⟨_, hint⟩, rfl⟩`. Take `⟨m2, hm2⟩ : ∃ m2 : ℕ, d + 1 = 8 * m2` from `⟨(d + 1) / 8, by omega⟩`. Establish `hm : (d : hostE ζ a b) + 1 = 8 * (m2 : hostE ζ a b)` using `by exact_mod_cast hm2`.

Establish `hprod : ω * (1 - ω) = 2 * (m2 : 𝓞 (hostE ζ a b))` using `by ext1`. Establish `e3 : ((ω * (1 - ω) : 𝓞 (hostE ζ a b)) : hostE ζ a b) = (ω : hostE ζ a b) * (1 - (ω : hostE ζ a b))` using `by first`. Consider the case `rfl`. Consider the case `push_cast`. Both sides reduce to the same expression.

Consider the case `simp`. Establish `e4 : ((2 * (m2 : 𝓞 (hostE ζ a b)) : 𝓞 (hostE ζ a b)) : hostE ζ a b) = 2 * (m2 : hostE ζ a b)` using `by first`. Consider the case `rfl`. Consider the case `push_cast`. Both sides reduce to the same expression.

Consider the case `simp`. Rewrite using `[e3, e4, hωv]`. Establish `hb2 : bE ζ a b ^ 2 = 1 - 8 * (m2 : hostE ζ a b)`. Rewrite using `[hbsq, ← hm]`. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `(-1 / 4 : hostE ζ a b) * hb2`. Establish `hsw : σ • ω = 1 - ω`. Use `ext`. Establish `e1 : ((σ • ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (ω : hostE ζ a b)` using `by first`. Consider the case `rfl`.

Consider the case `simp`. Establish `e2 : ((1 - ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = 1 - (ω : hostE ζ a b)` using `by first`. Consider the case `rfl`. Consider the case `push_cast`. Both sides reduce to the same expression.

Consider the case `simp`. Rewrite using `[e1, e2, hωv, map_div₀, map_add, map_one, hσb, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsmul : ∀ z, σ • z ∈ P ↔ z ∈ P` using `smul_mem_iff_of_stab σ P hσ`. Establish `hprodP : ω * (1 - ω) ∈ P`.

Rewrite using `[hprod]`. Conclude with `Ideal.mul_mem_right _ _ (two_mem P)`. Establish `hboth : ω ∈ P ∧ 1 - ω ∈ P`. Break down `(inferInstance : P.IsPrime).mem_or_mem hprodP with h1 | h1` into its components or cases. Conclude with `⟨h1, by rw [← hsw]; exact (hsmul ω).mpr h1⟩`.

Use `⟨?_, h1⟩` and prove the remaining obligations. Establish `h3` using `(hsmul (1 - ω)).mpr h1`. Rewrite `h3` using `[smul_sub, smul_one, hsw, sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1P : (1 : 𝓞 (hostE ζ a b)) ∈ P`. Simplify using `using P.add_mem hboth.1 hboth.2`.

Conclude with `(inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one P).mpr h1P)`. Use `show sgn σ (bE ζ a b) = 1`. Unfold `sgn`. Conclude with `if_pos hfix`.
-/
theorem stab_two_sgn (hqd : HypOdd q d) (hd16 : d % 16 = 7) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b σ).1.2 = 1 := by
  have hbsq : bE ζ a b ^ 2 = -((d : ℕ) : hostE ζ a b) := by simpa using bE_sq' h
  have hfix : σ (bE ζ a b) = bE ζ a b := by
    by_contra hne
    have hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
      rw [← map_pow, hbsq, map_neg, map_natCast]
    have hσb : σ (bE ζ a b) = -(bE ζ a b) := by
      have hm0 : (σ (bE ζ a b) - bE ζ a b) * (σ (bE ζ a b) + bE ζ a b) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hm0 with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hne
      · exact eq_neg_of_add_eq_zero_left h1
    have hint : IsIntegral ℤ ((1 + bE ζ a b) / 2) := omega_integral (by omega) hbsq
    obtain ⟨ω, hωv⟩ : ∃ ω : 𝓞 (hostE ζ a b), (ω : hostE ζ a b) = (1 + bE ζ a b) / 2 :=
      ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m2 : ℕ, d + 1 = 8 * m2 := ⟨(d + 1) / 8, by omega⟩
    have hm : (d : hostE ζ a b) + 1 = 8 * (m2 : hostE ζ a b) := by exact_mod_cast hm2
    have hprod : ω * (1 - ω) = 2 * (m2 : 𝓞 (hostE ζ a b)) := by
      ext1
      have e3 : ((ω * (1 - ω) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          (ω : hostE ζ a b) * (1 - (ω : hostE ζ a b)) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      have e4 : ((2 * (m2 : 𝓞 (hostE ζ a b)) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          2 * (m2 : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e3, e4, hωv]
      have hb2 : bE ζ a b ^ 2 = 1 - 8 * (m2 : hostE ζ a b) := by
        rw [hbsq, ← hm]
        ring
      linear_combination (-1 / 4 : hostE ζ a b) * hb2
    have hsw : σ • ω = 1 - ω := by
      ext
      have e1 : ((σ • ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (ω : hostE ζ a b) := by
        first
          | rfl
          | simp
      have e2 : ((1 - ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = 1 - (ω : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e1, e2, hωv, map_div₀, map_add, map_one, hσb, map_ofNat]
      ring
    have hsmul : ∀ z, σ • z ∈ P ↔ z ∈ P := smul_mem_iff_of_stab σ P hσ
    have hprodP : ω * (1 - ω) ∈ P := by
      rw [hprod]
      exact Ideal.mul_mem_right _ _ (two_mem P)
    have hboth : ω ∈ P ∧ 1 - ω ∈ P := by
      rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h1 | h1
      · exact ⟨h1, by rw [← hsw]; exact (hsmul ω).mpr h1⟩
      · refine ⟨?_, h1⟩
        have h3 := (hsmul (1 - ω)).mpr h1
        rwa [smul_sub, smul_one, hsw, sub_sub_cancel] at h3
    have h1P : (1 : 𝓞 (hostE ζ a b)) ∈ P := by
      simpa using P.add_mem hboth.1 hboth.2
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one P).mpr h1P)
  show sgn σ (bE ζ a b) = 1
  unfold sgn
  exact if_pos hfix

end Two

end Decomp

open Decomp

/- English proof (translation)
Introduce `e q d hH L _ _ ζ a b h uq ud huq hud σ`. Establish `hqd` using `hH.toHypOdd`. Establish `hQD` using `hH.toHypQD`. Establish `hrec` using `hostRecip q d hH`. Take `⟨hq, hd, -, hd16, hjac⟩` from `hH`.

Establish `hq2 : q ≠ 2` using `hqd.2.2.2.1`. Establish `hd2 : d ≠ 2` using `hqd.2.2.2.2`. Establish `hqd' : q ≠ d` using `hqd.2.2.1`. Take `⟨hLgal, -, hmulL, hbijL⟩` from `layer_galois hqd h`. Use `hLgal` as an intermediate fact.

Take `⟨hEgal, -, hmulE, hbijE⟩` from `hostGalois e q d hqd L ζ a b h`. Use `hEgal` as an intermediate fact. Set `gE : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) →* GG e` to `MonoidHom.mk' (galE e ζ a b) hmulE`. Set `gL : Gal(L/ℚ) →* GalL (e + 2)` to `MonoidHom.mk' (galMap h.1 a b) hmulL`. Establish `hpowE : ∀ (x : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ), galE e ζ a b (x ^ k) = galE e ζ a b x ^ k` using `fun x k => map_pow gE x k`.

Establish `hpowL : ∀ (x : Gal(L/ℚ)) (k : ℕ), galMap h.1 a b (x ^ k) = galMap h.1 a b x ^ k` using `fun x k => map_pow gL x k`. Establish `ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L)` using `by rw [h.2.1]; push_cast; rfl`. Establish `hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L)` using `by rw [h.2.2.1]; push_cast; rfl`. Establish `hqnd : ¬ q ∣ d` using `fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv)`. Establish `hdnq : ¬ d ∣ q` using `fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm`.

Establish `hIT` using `layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h`. Use `⟨fun P _ _ => ?_, fun P _ _ => ?_, fun P _ _ => ?_⟩` and prove the remaining obligations. Take `⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L))` from `inferInstance`. Establish `: Q.LiesOver (span {(2 : ℤ)})` using `Ideal.LiesOver.trans Q P (span {(2 : ℤ)})`. Rewrite using `[mem_Psi_iff]`.

Use `⟨stab_two_sgn hqd hd16 h P σ, fun hs => ?_⟩` and prove the remaining obligations. Take `⟨τ, hστ⟩` from `exists_lift hqd h σ`. Establish `hgl` using `galE_lift h hστ`. Apply `stab_restrict P Q σ τ hστ` to reduce the goal to its premises. Rewrite using `[layerDecompTwo (e + 2) q d (by omega) hQD L ζ a b h Q τ, D2, MonoidHom.mem_ker]`.

Establish `h1` using `congrArg (fun g : GG e => g.1.2) hgl`. Simplify using `only at h1`. Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_snd]`. Rewrite using `[← h1]`. Conclude with `hs`.

Establish `: Fact q.Prime` using `⟨hq⟩`. Take `⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L))` from `inferInstance`. Establish `: Q.LiesOver (span {(q : ℤ)})` using `Ideal.LiesOver.trans Q P (span {(q : ℤ)})`. Establish `: Finite (𝓞 L ⧸ Q)`. Establish `hpb : span {(q : ℤ)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hq.ne_zero` after adjusting the coercions. Conclude with `Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)`. Take `⟨F, hF⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q`. Take `⟨σF, hσF⟩` from `exists_restrict hqd h F`.

Establish `hFE : IsArithFrobAt ℤ σF P` using `frob_restrict q Q P σF F hσF hF`. Establish `hF1 : (galMap h.1 a b F).1 = uq` using `Units.ext ((odd_cyc_frob h.1 q hq2 Q F hF).trans huq.symm)`. Establish `hF3 : (galMap h.1 a b F).2.2 = 1`. Use `odd_frob_sgn q hq2 Q F hF b _ hb (by rw [dvd_neg]; intro h'; exact hqnd (by exact_mod_cast h'))` as an intermediate fact. Rewrite `this` using `[hjac]`.

Conclude with `Units.ext this`. Establish `hgF : galE e ζ a b σF = (((galMap h.1 a b F).2.1, 1), hcl e uq)`. Rewrite using `[galE_lift h hσF, hF3, hF1]`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`.

Take `⟨k, ρ, hρ, rfl⟩` from `stab_eq_inertia_mul q P σF σ hFE hσ`. Establish `e2 : (galE e ζ a b ρ).2 = 1` using `hPart_inertia hqd h q hq hq2 Q P ρ hρ`. Establish `e1 : (galE e ζ a b ρ).1.2 = 1` using `odd_sgn_inertia q hq hq2 P ρ hρ (bE ζ a b) d (bE_sq' h) hqnd`. Rewrite using `[hmulE, hpowE, hgF]`. Use `⟨?_, k, ?_⟩` and prove the remaining obligations.

Simplify using `[e1]`. Simplify using `[e2]`. Introduce and unpack `⟨hs2, k, hk⟩ set s' : ℤˣ := (galE e ζ a b σ).1.1 * ((galMap h.1 a b F).2.1 ^ k)⁻¹ with hs'`. Take `⟨ι, hι⟩` from `hbijL.2 ((1, s', 1) : GalL (e + 2))`. Establish `hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q`.

Rewrite using `[hIT.1 Q ι, odd_mem_Iq, hι]`. Apply the tactic sequence `rcases Int.units_eq_one_or s' with hs | hs <;> rw [hs]`. Use `left`. Both sides reduce to the same expression. Use `right`.

Both sides reduce to the same expression. Establish `hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q` using `Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)`. Take `⟨σ', hσ'⟩` from `exists_restrict hqd h (ι * F ^ k)`. Establish `hgm : galMap h.1 a b (ι * F ^ k) = ((galMap h.1 a b F).1 ^ k, s' * (galMap h.1 a b F).2.1 ^ k, 1)`. Rewrite using `[hmulL, hpowL, hι]`.

Apply the tactic sequence `refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF3]`. Establish `hσσ : σ' = σ`. Apply `hbijE.1` to reduce the goal to its premises. Rewrite using `[galE_lift h hσ', hgm, hF1]`. Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations.

Rewrite using `[hs', inv_mul_cancel_right]`. Conclude with `hs2.symm`. Rewrite using `[hk]`. Conclude with `QuotientGroup.mk_pow _ uq k`. Rewrite using `[← hσσ]`.

Conclude with `stab_restrict P Q σ' _ hσ' hτ`. Establish `: Fact d.Prime` using `⟨hd⟩`. Take `⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L))` from `inferInstance`. Establish `: Q.LiesOver (span {(d : ℤ)})` using `Ideal.LiesOver.trans Q P (span {(d : ℤ)})`. Establish `: Finite (𝓞 L ⧸ Q)`.

Establish `hpb : span {(d : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hd.ne_zero` after adjusting the coercions. Conclude with `Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)`. Take `⟨F, hF⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q`.

Take `⟨σF, hσF⟩` from `exists_restrict hqd h F`. Establish `hFE : IsArithFrobAt ℤ σF P` using `frob_restrict d Q P σF F hσF hF`. Establish `hF1 : (galMap h.1 a b F).1 = ud` using `Units.ext ((odd_cyc_frob h.1 d hd2 Q F hF).trans hud.symm)`. Establish `hF2 : (galMap h.1 a b F).2.1 = -1`. Use `odd_frob_sgn d hd2 Q F hF a _ ha (by rw [dvd_neg]; intro h'; exact hdnq (by exact_mod_cast h'))` as an intermediate fact.

Rewrite `this` using `[hrec]`. Conclude with `Units.ext this`. Establish `hgF : galE e ζ a b σF = ((-1, (galMap h.1 a b F).2.2), hcl e ud)`. Rewrite using `[galE_lift h hσF, hF2, hF1]`. Prove the components needed by the constructor for the conclusion.

Introduce `hσ`. Take `⟨k, ρ, hρ, rfl⟩` from `stab_eq_inertia_mul d P σF σ hFE hσ`. Establish `e2 : (galE e ζ a b ρ).2 = 1` using `hPart_inertia hqd h d hd hd2 Q P ρ hρ`. Establish `e1 : (galE e ζ a b ρ).1.1 = 1` using `odd_sgn_inertia d hd hd2 P ρ hρ (aE ζ a b) q (aE_sq_eq_neg_q h) hdnq`. Rewrite using `[hmulE, hpowE, hgF]`.

Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[e1]`. Simplify using `[e2]`. Introduce and unpack `⟨k, hk1, hk2⟩ set t' : ℤˣ := (galE e ζ a b σ).1.2 * ((galMap h.1 a b F).2.2 ^ k)⁻¹ with ht'`. Take `⟨ι, hι⟩` from `hbijL.2 ((1, 1, t') : GalL (e + 2))`.

Establish `hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q`. Rewrite using `[hIT.2 Q ι, odd_mem_Id, hι]`. Apply the tactic sequence `rcases Int.units_eq_one_or t' with ht | ht <;> rw [ht]`. Use `left`. Both sides reduce to the same expression.

Use `right`. Both sides reduce to the same expression. Establish `hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q` using `Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)`. Take `⟨σ', hσ'⟩` from `exists_restrict hqd h (ι * F ^ k)`. Establish `hgm : galMap h.1 a b (ι * F ^ k) = ((galMap h.1 a b F).1 ^ k, (-1) ^ k, t' * (galMap h.1 a b F).2.2 ^ k)`.

Rewrite using `[hmulL, hpowL, hι]`. Apply the tactic sequence `refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF2]`. Establish `hσσ : σ' = σ`. Apply `hbijE.1` to reduce the goal to its premises. Rewrite using `[galE_lift h hσ', hgm, hF1]`.

Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Conclude with `hk1.symm`. Rewrite using `[ht', inv_mul_cancel_right]`. Rewrite using `[hk2]`. Conclude with `QuotientGroup.mk_pow _ ud k`.

Rewrite using `[← hσσ]`. Conclude with `stab_restrict P Q σ' _ hσ' hτ`.
-/
theorem hostDecomp : HostDecomp := by
  intro e q d hH L _ _ ζ a b h uq ud huq hud σ
  have hqd := hH.toHypOdd
  have hQD := hH.toHypQD
  have hrec := hostRecip q d hH
  obtain ⟨hq, hd, -, hd16, hjac⟩ := hH
  have hq2 : q ≠ 2 := hqd.2.2.2.1
  have hd2 : d ≠ 2 := hqd.2.2.2.2
  have hqd' : q ≠ d := hqd.2.2.1
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layer_galois hqd h
  have := hLgal
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  let gE : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) →* GG e := MonoidHom.mk' (galE e ζ a b) hmulE
  let gL : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmulL
  have hpowE : ∀ (x : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ),
      galE e ζ a b (x ^ k) = galE e ζ a b x ^ k := fun x k => map_pow gE x k
  have hpowL : ∀ (x : Gal(L/ℚ)) (k : ℕ), galMap h.1 a b (x ^ k) = galMap h.1 a b x ^ k :=
    fun x k => map_pow gL x k
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hqnd : ¬ q ∣ d := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv)
  have hdnq : ¬ d ∣ q := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm
  have hIT := layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h
  refine ⟨fun P _ _ => ?_, fun P _ _ => ?_, fun P _ _ => ?_⟩
  ·
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(2 : ℤ)}) := Ideal.LiesOver.trans Q P (span {(2 : ℤ)})
    rw [mem_Psi_iff]
    refine ⟨stab_two_sgn hqd hd16 h P σ, fun hs => ?_⟩
    obtain ⟨τ, hστ⟩ := exists_lift hqd h σ
    have hgl := galE_lift h hστ
    apply stab_restrict P Q σ τ hστ
    rw [layerDecompTwo (e + 2) q d (by omega) hQD L ζ a b h Q τ, D2, MonoidHom.mem_ker]
    have h1 := congrArg (fun g : GG e => g.1.2) hgl
    simp only at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_snd]
    rw [← h1]
    exact hs
  ·
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(q : ℤ)}) := Ideal.LiesOver.trans Q P (span {(q : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(q : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict q Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = uq := Units.ext ((odd_cyc_frob h.1 q hq2 Q F hF).trans huq.symm)
    have hF3 : (galMap h.1 a b F).2.2 = 1 := by
      have := odd_frob_sgn q hq2 Q F hF b _ hb
        (by rw [dvd_neg]; intro h'; exact hqnd (by exact_mod_cast h'))
      rw [hjac] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = (((galMap h.1 a b F).2.1, 1), hcl e uq) := by
      rw [galE_lift h hσF, hF3, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul q P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h q hq hq2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.2 = 1 :=
        odd_sgn_inertia q hq hq2 P ρ hρ (bE ζ a b) d (bE_sq' h) hqnd
      rw [hmulE, hpowE, hgF]
      refine ⟨?_, k, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨hs2, k, hk⟩
      set s' : ℤˣ := (galE e ζ a b σ).1.1 * ((galMap h.1 a b F).2.1 ^ k)⁻¹ with hs'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, s', 1) : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.1 Q ι, odd_mem_Iq, hι]
        rcases Int.units_eq_one_or s' with hs | hs <;> rw [hs]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, s' * (galMap h.1 a b F).2.1 ^ k, 1) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF3]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · rw [hs', inv_mul_cancel_right]
        · exact hs2.symm
        · rw [hk]; exact QuotientGroup.mk_pow _ uq k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ
  ·
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(d : ℤ)}) := Ideal.LiesOver.trans Q P (span {(d : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(d : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hd.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict d Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = ud := Units.ext ((odd_cyc_frob h.1 d hd2 Q F hF).trans hud.symm)
    have hF2 : (galMap h.1 a b F).2.1 = -1 := by
      have := odd_frob_sgn d hd2 Q F hF a _ ha
        (by rw [dvd_neg]; intro h'; exact hdnq (by exact_mod_cast h'))
      rw [hrec] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = ((-1, (galMap h.1 a b F).2.2), hcl e ud) := by
      rw [galE_lift h hσF, hF2, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul d P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h d hd hd2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.1 = 1 :=
        odd_sgn_inertia d hd hd2 P ρ hρ (aE ζ a b) q (aE_sq_eq_neg_q h) hdnq
      rw [hmulE, hpowE, hgF]
      refine ⟨k, ?_, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨k, hk1, hk2⟩
      set t' : ℤˣ := (galE e ζ a b σ).1.2 * ((galMap h.1 a b F).2.2 ^ k)⁻¹ with ht'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, 1, t') : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.2 Q ι, odd_mem_Id, hι]
        rcases Int.units_eq_one_or t' with ht | ht <;> rw [ht]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, (-1) ^ k, t' * (galMap h.1 a b F).2.2 ^ k) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF2]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · exact hk1.symm
        · rw [ht', inv_mul_cancel_right]
        · rw [hk2]; exact QuotientGroup.mk_pow _ ud k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ

/- English proof (translation)
Introduce `e q d hyp L _ _ ζ a b h σ hσ p hp P _ _`. Establish `hm1 : (-1 : ℤˣ) ≠ 1`. Introduce `h1`. Establish `h2` using `congrArg Units.val h1`. Simplify using `at h2`.

Establish `hq8 : q % 8 = 3` using `hyp.2.2.1`. Establish `hd16 : d % 16 = 7` using `hyp.2.2.2.1`. Establish `hcq : Nat.Coprime q (2 ^ (e + 2))` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.1 Nat.prime_two).mpr (by omega))`. Establish `hcd : Nat.Coprime d (2 ^ (e + 2))` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.2.1 Nat.prime_two).mpr (by omega))`. Establish `HD` using `hostDecomp e q d hyp L ζ a b h (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd) (ZMod.coe_unitOfCoprime q hcq) (ZMod.coe_unitOfCoprime d hcd) σ`.

Rewrite `HD` using `[hσ]`. Establish `hnotPsi : cc e ∉ Psi e`. Introduce `hmem`. Establish `h3 : chD e (cc e) = -1` using `by first`. Consider the case `rfl`.

Consider the case `simp [chD, cc, c0]`. Conclude with `hm1 (h3.symm.trans (MonoidHom.mem_ker.mp hmem))`. Break down `hp with rfl | rfl | ⟨rfl, he2⟩` into its components or cases. Use `haveI : P.LiesOver (span {(2 : ℤ)}) := by`. Establish `h' : P.LiesOver (span {((2 : ℕ) : ℤ)})` using `inferInstance`.

Simplify using `using h'`. Rewrite using `[HD.1 P]`. Conclude with `hnotPsi`. Rewrite using `[HD.2.1 P]`. Introduce and unpack `⟨h1, -⟩`.

Conclude with `hm1 h1`. Rewrite using `[HD.2.2 P]`. Introduce and unpack `⟨k, hk1, hk2⟩`. Establish `hk1' : (-1 : ℤˣ) = (-1) ^ k` using `hk1`. Choose the witnesses or unpack the hypotheses as in `⟨j, rfl⟩ : Odd k := by`.

Break down `Nat.even_or_odd k with hev | hod` into its components or cases. Rewrite `hk1'` using `[hev.neg_one_pow]`. Conclude with `absurd hk1' hm1`. Conclude with `hod`. Establish `hk3 : ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e) = 1`.

Rewrite using `[QuotientGroup.mk_pow]`. Conclude with `hk2.symm`. Rewrite `hk3` using `[QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]`. Take `⟨i, hi⟩` from `hk3`. Establish `hpm : (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = 1 ∨ (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = -1`.

Rewrite using `[← hi]`. Break down `Int.even_or_odd i with hev | hod` into its components or cases. Use `left`. Conclude with `hev.neg_one_zpow`. Use `right`.

Conclude with `hod.neg_one_zpow`. Establish `h16 : 16 ∣ 2 ^ (e + 2)`. Establish `h4` using `Nat.pow_dvd_pow 2 (show 4 ≤ e + 2 by omega)`. Simplify using `using h4`. Establish `hd7 : ((p : ℕ) : ZMod 16) = 7`.

Rewrite using `[← ZMod.natCast_mod, hd16]`. Apply the tactic sequence `all_goals first | rfl | decide`. Establish `h49 : (7 : ZMod 16) ^ 2 = 1` using `by decide`. Establish `h7 : (7 : ZMod 16) ^ (2 * j + 1) = 7`. Rewrite using `[pow_succ, pow_mul, h49, one_pow, one_mul]`.

Establish `hval : ZMod.castHom h16 (ZMod 16) ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 7`. Rewrite using `[Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, map_pow, map_natCast, hd7, h7]`. Break down `hpm with h1 | h1` into its components or cases. Rewrite `hval` using `[h1, Units.val_one, map_one]`. Conclude with `absurd hval (by decide)`.

Rewrite `hval` using `[h1, Units.val_neg, Units.val_one, map_neg, map_one]`. Conclude with `absurd hval (by decide)`.
-/
theorem hostDecompConj : HostDecompConj := by
  intro e q d hyp L _ _ ζ a b h σ hσ p hp P _ _
  have hm1 : (-1 : ℤˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg Units.val h1
    simp at h2
  have hq8 : q % 8 = 3 := hyp.2.2.1
  have hd16 : d % 16 = 7 := hyp.2.2.2.1
  have hcq : Nat.Coprime q (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.1 Nat.prime_two).mpr (by omega))
  have hcd : Nat.Coprime d (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.2.1 Nat.prime_two).mpr (by omega))
  have HD := hostDecomp e q d hyp L ζ a b h (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd)
    (ZMod.coe_unitOfCoprime q hcq) (ZMod.coe_unitOfCoprime d hcd) σ
  rw [hσ] at HD
  have hnotPsi : cc e ∉ Psi e := by
    intro hmem
    have h3 : chD e (cc e) = -1 := by
      first
        | rfl
        | simp [chD, cc, c0]
    exact hm1 (h3.symm.trans (MonoidHom.mem_ker.mp hmem))
  rcases hp with rfl | rfl | ⟨rfl, he2⟩
  · haveI : P.LiesOver (span {(2 : ℤ)}) := by
      have h' : P.LiesOver (span {((2 : ℕ) : ℤ)}) := inferInstance
      simpa using h'
    rw [HD.1 P]
    exact hnotPsi
  · rw [HD.2.1 P]
    rintro ⟨h1, -⟩
    exact hm1 h1
  · rw [HD.2.2 P]
    rintro ⟨k, hk1, hk2⟩
    have hk1' : (-1 : ℤˣ) = (-1) ^ k := hk1
    obtain ⟨j, rfl⟩ : Odd k := by
      rcases Nat.even_or_odd k with hev | hod
      · rw [hev.neg_one_pow] at hk1'
        exact absurd hk1' hm1
      · exact hod
    have hk3 : ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk2.symm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hk3
    obtain ⟨i, hi⟩ := hk3
    have hpm : (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = 1 ∨
        (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = -1 := by
      rw [← hi]
      rcases Int.even_or_odd i with hev | hod
      · left
        exact hev.neg_one_zpow
      · right
        exact hod.neg_one_zpow
    have h16 : 16 ∣ 2 ^ (e + 2) := by
      have h4 := Nat.pow_dvd_pow 2 (show 4 ≤ e + 2 by omega)
      simpa using h4
    have hd7 : ((p : ℕ) : ZMod 16) = 7 := by
      rw [← ZMod.natCast_mod, hd16]
      all_goals first | rfl | decide
    have h49 : (7 : ZMod 16) ^ 2 = 1 := by decide
    have h7 : (7 : ZMod 16) ^ (2 * j + 1) = 7 := by
      rw [pow_succ, pow_mul, h49, one_pow, one_mul]
    have hval : ZMod.castHom h16 (ZMod 16)
        ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 7 := by
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, map_pow, map_natCast, hd7, h7]
    rcases hpm with h1 | h1
    · rw [h1, Units.val_one, map_one] at hval
      exact absurd hval (by decide)
    · rw [h1, Units.val_neg, Units.val_one, map_neg, map_one] at hval
      exact absurd hval (by decide)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hostDecomp, hostDecompConj⟩`.
-/
theorem hostDecompBoth : HostDecomp ∧ HostDecompConj := ⟨hostDecomp, hostDecompConj⟩

end Formalism.FrobeniusOrbits
