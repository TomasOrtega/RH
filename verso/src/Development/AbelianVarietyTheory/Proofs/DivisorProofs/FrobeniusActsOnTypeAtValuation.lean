import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV

set_option autoImplicit false

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section ResidueField

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {d : ℕ}

/- English proof (translation)
Introduce `h`. Establish `h2k : (2 : k) ≠ 0`. Introduce `h0`. Establish `: p ∣ 2` using `(CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)`.

Establish `hr0 : r = 0`. Establish `: 2 * r = 0` using `by linear_combination h`. Conclude with `(mul_eq_zero.1 this).resolve_left h2k`. Establish `hdk : (d : k) = 0`. Rewrite `hr` using `[hr0]`.

Take the linear combination `hr`. Conclude with `hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))`.
-/
theorem sqrtNeg_ne_neg (h2 : p ≠ 2) (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) : r ≠ -r := by
  intro h
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hr0 : r = 0 := by
    have : 2 * r = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2k
  have hdk : (d : k) = 0 := by
    rw [hr0] at hr
    linear_combination hr
  exact hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))

/- English proof (translation)
Take `⟨m, hm⟩` from `hs`. Establish `h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2`. Rewrite using `[hr, ← map_pow, sq, ← hm, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. Rewrite using `[h, ← map_pow, ZMod.pow_card]`.

Rewrite using `[h, ← map_neg, ← map_pow, ZMod.pow_card]`.
-/
theorem sqrtNeg_pow_of_isSquare (hs : IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) : r ^ p = r := by
  obtain ⟨m, hm⟩ := hs
  have h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2 := by
    rw [hr, ← map_pow, sq, ← hm, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, ← map_pow, ZMod.pow_card]
  · rw [h, ← map_neg, ← map_pow, ZMod.pow_card]

/- English proof (translation)
Establish `hd : (d : ZMod p) ≠ 0` using `fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)`. Establish `hd' : -(d : ZMod p) ≠ 0` using `neg_ne_zero.2 hd`. Establish `h2 : p ≠ 2`. Introduce and unpack `rfl`. Apply `hs` to reduce the goal to its premises.

Generalize the expression as in `(-(d : ZMod 2)) = x`. Conclude with `⟨x, by rw [← sq, ZMod.pow_card]⟩`. Establish `he : (-(d : ZMod p)) ^ (p / 2) = -1` using `(ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)`. Establish `hk : (-(d : k)) ^ (p / 2) = -1`. Use `congrArg (ZMod.castHom (dvd_refl p) k) he` as an intermediate fact.

Rewrite `this` using `[map_pow, map_neg, map_neg, map_natCast, map_one]`. Then use the resulting hypothesis. Establish `hp : p = 2 * (p / 2) + 1`. Use `(Fact.out : p.Prime).eq_two_or_odd.resolve_left h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h3 : r ^ p = -r` using `by conv_lhs => rw [hp]`.

Rewrite using `[pow_succ, pow_mul, hr, hk, neg_one_mul]`. Rewrite using `[h3]`. Conclude with `(sqrtNeg_ne_neg h2 hd hr).symm`.
-/
theorem sqrtNeg_pow_ne_of_not_isSquare (hs : ¬ IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ^ p ≠ r := by
  have hd : (d : ZMod p) ≠ 0 := fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  have h2 : p ≠ 2 := by
    rintro rfl
    apply hs
    generalize (-(d : ZMod 2)) = x
    exact ⟨x, by rw [← sq, ZMod.pow_card]⟩
  have he : (-(d : ZMod p)) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)
  have hk : (-(d : k)) ^ (p / 2) = -1 := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) he
    rwa [map_pow, map_neg, map_neg, map_natCast, map_one] at this
  have hp : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd.resolve_left h2
    omega
  have h3 : r ^ p = -r := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hr, hk, neg_one_mul]
  rw [h3]
  exact (sqrtNeg_ne_neg h2 hd hr).symm

end ResidueField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

/- English proof (translation)
Use `congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq` as an intermediate fact. Rewrite `this` using `[map_pow, map_neg, map_natCast]`. Then use the resulting hypothesis.
-/
theorem label_rt_sq (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rwa [map_pow, map_neg, map_natCast] at this

/- English proof (translation)
Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `h` using `label_rt_sq H σ`. Generalize the expression as in `σ (H.rt : E) = z at h`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1` using `congrArg Complex.re h`.

Establish `h2` using `congrArg Complex.im h`. Simplify using `[sq] at h1 h2`. Establish `h3 : z.re = 0`. Assume the negation of the conclusion as `h0`. Establish `h4 : z.im = 0`.

Establish `: z.re * z.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h0`. Rewrite `h1` using `[h4]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [h3]`.
-/
theorem conj_label_rt (H : Host E) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have h := label_rt_sq H σ
  generalize σ (H.rt : E) = z at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : z.re = 0 := by
    by_contra h0
    have h4 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [h4] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h3]

/- English proof (translation)
Use `⟨(H.d + 1) / 8, ?_⟩` and prove the remaining obligations. Establish `h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E)`. Establish `: H.d + 1 = 8 * ((H.d + 1) / 8)` using `by have := H.d_mod; omega`. Conclude with `this` after adjusting the coercions. Establish `h4 : (4 : 𝓞 E) ≠ 0` using `by norm_num`.

Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Establish `h1` using `H.two_weight_eq_one_add_root`. Establish `h2` using `H.rt_sq`. Take the linear combination `(2 * H.w0 - 1 + H.rt) * h1 + h2 - h8`.
-/
theorem exists_w0_sq_even_constant (H : Host E) : ∃ n : ℕ, H.w0 ^ 2 = H.w0 - 2 * n := by
  refine ⟨(H.d + 1) / 8, ?_⟩
  have h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E) := by
    have : H.d + 1 = 8 * ((H.d + 1) / 8) := by have := H.d_mod; omega
    exact_mod_cast this
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h1 := H.two_weight_eq_one_add_root
  have h2 := H.rt_sq
  linear_combination (2 * H.w0 - 1 + H.rt) * h1 + h2 - h8

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

/- English proof (translation)
Establish `h1 : embK c σ' a = embK c σ b` using `Subtype.ext h`. Establish `h2 : embO io X σ' a = embO io X σ b` using `X.ints.hom_inj (by`. Rewrite using `[algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, h1])`. Rewrite using `[red, red, RingHom.comp_apply, RingHom.comp_apply, h2]`.
-/
theorem red_eq_of_label_eq {σ σ' : E →+* ℂ} {a b : 𝓞 E} (h : σ' (a : E) = σ (b : E)) :
    red io X σ' a = red io X σ b := by
  have h1 : embK c σ' a = embK c σ b := Subtype.ext h
  have h2 : embO io X σ' a = embO io X σ b := X.ints.hom_inj (by
    rw [algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, h1])
  rw [red, red, RingHom.comp_apply, RingHom.comp_apply, h2]

/- English proof (translation)
Introduce `σ σ' hF`. Use `haveI := charP_residueField_of_irreducible X`. Establish `hred : ∀ a, red io X σ' a = red io X σ a ^ p` using `fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)`. Establish `hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O)`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`.

Establish `hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E)` using `sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])`. Use `⟨fun hs => ?_, fun hi => ?_⟩` and prove the remaining obligations. Establish `key : σ' (H.rt : E) = σ (H.rt : E)`. Use `hpm.resolve_right fun h => ?_` and prove the remaining obligations. Distinguish the cases in `h2 : p = 2`.

Substitute `h2` using the available equality. Take `⟨n, hn⟩` from `exists_w0_sq_even_constant H`. Establish `hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E)` using `fun τ => by`. Use `congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Then use the resulting hypothesis.

Establish `h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E)`. Establish `e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E)`. Use `map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Rewrite using `[e]`.

Take the linear combination `(1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h`. Establish `h3` using `red_eq_of_label_eq io X h1`. Rewrite `h3` using `[hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat]`. Establish `h4 : (2 : ResidueField X.O) = 0`. Conclude with `CharP.cast_eq_zero (ResidueField X.O) 2` after adjusting the coercions.

Apply `one_ne_zero (α := ResidueField X.O)` to reduce the goal to its premises. Take the linear combination `-h3 + (red io X σ H.w0 - red io X σ n) * h4`. Establish `h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E)`. Rewrite using `[h]`. Conclude with `(map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm`.

Establish `h3` using `red_eq_of_label_eq io X h1`. Rewrite `h3` using `[hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg]`. Conclude with `sqrtNeg_ne_neg h2 hs.1 hr h3`. Rewrite using `[InPsi, InPsi, key]`. Establish `key : σ' (H.rt : E) = -σ (H.rt : E)`.

Use `hpm.resolve_left fun h => ?_` and prove the remaining obligations. Establish `h3` using `red_eq_of_label_eq io X h`. Rewrite `h3` using `[hred]`. Conclude with `sqrtNeg_pow_ne_of_not_isSquare hi hr h3`. Rewrite using `[InPsi, InPsi, key, conj_label_rt]`.
-/
theorem frobOnType : FrobOnType io X := by
  intro σ σ' hF
  haveI := charP_residueField_of_irreducible X
  have hred : ∀ a, red io X σ' a = red io X σ a ^ p := fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)
  have hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O) := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have key : σ' (H.rt : E) = σ (H.rt : E) := by
      refine hpm.resolve_right fun h => ?_
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨n, hn⟩ := exists_w0_sq_even_constant H
        have hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
          have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        have h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E) := by
          have e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
            have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
            rwa [map_one] at this
          rw [e]
          linear_combination (1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat] at h3
        have h4 : (2 : ResidueField X.O) = 0 := by
          exact_mod_cast CharP.cast_eq_zero (ResidueField X.O) 2
        apply one_ne_zero (α := ResidueField X.O)
        linear_combination -h3 + (red io X σ H.w0 - red io X σ n) * h4
      · have h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E) := by
          rw [h]; exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg] at h3
        exact sqrtNeg_ne_neg h2 hs.1 hr h3
    rw [InPsi, InPsi, key]
  · have key : σ' (H.rt : E) = -σ (H.rt : E) := by
      refine hpm.resolve_left fun h => ?_
      have h3 := red_eq_of_label_eq io X h
      rw [hred] at h3
      exact sqrtNeg_pow_ne_of_not_isSquare hi hr h3
    rw [InPsi, InPsi, key, conj_label_rt]

/- English proof (translation)
The claim follows from `frobOnType io X`.
-/
theorem frobOnType_all (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) : FrobOnType io X :=
  frobOnType io X

end GlobalTheory.PrimePart
