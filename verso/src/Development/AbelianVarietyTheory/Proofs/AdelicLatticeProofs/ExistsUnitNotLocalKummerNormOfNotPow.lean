import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrderStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletionStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Establish `h : pows p (U.map f) = (pows p U).map f`. Unfold `pows`. Rewrite using `[Subgroup.map_map, Subgroup.map_map]`. Use `congr 1`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Unfold `pIdx`. Rewrite using `[h, Subgroup.relIndex_map_map_of_injective _ _ hf]`.
-/
theorem nonnorm_pIdx_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pIdx p (U.map f) = pIdx p U := by
  have h : pows p (U.map f) = (pows p U).map f := by
    unfold pows
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  unfold pIdx
  rw [h, Subgroup.relIndex_map_map_of_injective _ _ hf]

/- English proof (translation)
Unfold `pTor`. Use `symm`. Use `Nat.card_eq_of_bijective (fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2.1, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Conclude with `Subtype.ext (hf (congrArg Subtype.val hxy))`.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, h⟩`. Use `⟨⟨x, hx, hf ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[map_pow, h, map_one]`.
-/
theorem nonnorm_pTor_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pTor p (U.map f) = pTor p U := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2.1, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    refine ⟨⟨x, hx, hf ?_⟩, rfl⟩
    rw [map_pow, h, map_one]

/- English proof (translation)
Introduce `p F _ _ ζ δ v hp hζ hδ`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Use `haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective`. Establish `hζ' : IsPrimitiveRoot (algebraMap F (v.adicCompletion F) ζ) p` using `hζ.map_of_injective (algebraMap F (v.adicCompletion F)).injective`.

Take `⟨L, _, _, θ, σ, hK⟩` from `exists_isKum p (v.adicCompletion F) _ _ hp hζ' hδ`. Take `⟨hfd, hrk, hσp, hfix, -, -, hnorm⟩` from `GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p _ L _ _ θ σ hK`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) := by`. Establish `h0 : v.valuation F (p : F) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`.

Conclude with `hp.ne_zero` after adjusting the coercions. Establish `h1 : v.valuation F (p : F) ≤ 1`. Use `v.valuation_le_one (K := F) (p : 𝓞 F)` as an intermediate fact. Simplify using `using this`. Establish `h2 : WithZero.log (v.valuation F (p : F)) ≤ 0`.

Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Conclude with `h1`. Use `⟨(-WithZero.log (v.valuation F (p : F))).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]`. Take `⟨htL, hiL⟩` from `GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e L hp.pos he`.

Take `⟨htK, hiK⟩` from `GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e (v.adicCompletion F) hp.pos he`. Rewrite `hiL` using `[hrk]`. Rewrite `hiK` using `[Module.finrank_self, pow_one]`. Establish `hQ : Ideal.absNorm v.asIdeal ^ e ≠ 0` using `pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)`. Generalize the expression as in `Ideal.absNorm v.asIdeal ^ e = Q at hiL hiK hQ`.

Set `s : Lˣ →* Lˣ` to `Units.map (σ : L →* L)`. Establish `hs : ∀ (n : ℕ) (a : Lˣ), ((s^[n] a : Lˣ) : L) = σ^[n] (a : L)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro a`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `a`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]`. Both sides reduce to the same expression.

Set `f : (v.adicCompletion F)ˣ →* Lˣ` to `Units.map (algebraMap (v.adicCompletion F) L : v.adicCompletion F →* L)`. Establish `hf : Function.Injective f` using `Units.map_injective (algebraMap (v.adicCompletion F) L).injective`. Establish `hfx : fix s = (⊤ : Subgroup (v.adicCompletion F)ˣ).map f`. Use extensionality with `a`. Rewrite using `[mem_fix]`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨b, hb⟩` from `hfix a (congrArg Units.val ha)`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`.

Conclude with `a.ne_zero (by rw [hb, map_zero])`. Conclude with `⟨Units.mk0 b hb0, trivial, Units.ext hb.symm⟩`. Introduce and unpack `⟨b, -, rfl⟩`. Conclude with `Units.ext (σ.commutes (b : v.adicCompletion F))`. Establish `hiL0 : pIdx p (⊤ : Subgroup Lˣ) ≠ 0`.

Rewrite using `[hiL]`. Conclude with `mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hQ)) htL`. Take `⟨-, h1, -, -, hH⟩` from `GlobalTheory.T.herbrand_prime_order' p Lˣ s hp (fun a => Units.ext (by rw [hs, hσp])) hiL0 htL`. Establish `h0 : (nrm s p).range.relIndex (fix s) = 1`. Rewrite using `[Subgroup.relIndex_eq_one, hfx]`.

Introduce and unpack `_ ⟨c, -, rfl⟩`. Take `⟨y, hy⟩` from `(hnorm c).1 (hall c)`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Establish `: ∏ i ∈ Finset.range p, σ^[i] (0 : L) = 0` using `Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) rfl`.

Rewrite `hy` using `[this]`. Conclude with `c.ne_zero ((map_eq_zero _).1 hy.symm)`. Use `⟨Units.mk0 y hy0, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[nrm_apply, Units.coe_prod]`. Simplify using `only [hs, Units.val_mk0]`.

Conclude with `hy`. Rewrite `hH` using `[h0, hfx, nonnorm_pIdx_map p f hf, nonnorm_pTor_map p f hf, hiL, hiK, one_pow]`. Generalize the expression as in `pTor p (⊤ : Subgroup Lˣ) = tL at hH htL`. Generalize the expression as in `pTor p (⊤ : Subgroup (v.adicCompletion F)ˣ) = tK at hH htK`. Generalize the expression as in `(dif s).range.relIndex (nrm s p).ker = h at hH h1`.

Establish `hc : Q ^ p * tL * tK ^ p ≠ 0` using `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hQ) htL) (pow_ne_zero _ htK)`. Establish `key : p = h ^ (p - 1) * p ^ p`. Apply `mul_right_cancel₀ hc` to reduce the goal to its premises. Rewrite `hH` using `[mul_pow, mul_pow]`. Take the linear combination `hH`.

Establish `hle : p ^ p ≤ p`. Combine the equalities or inequalities in the displayed calculation. Establish `hlt : p ^ 1 < p ^ p` using `Nat.pow_lt_pow_right hp.one_lt hp.one_lt`. Rewrite `hlt` using `[pow_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_local_nonnorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F)
    (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p →
    (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) →
    ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F) δ) := by
  intro p F _ _ ζ δ v hp hζ hδ
  by_contra hall
  push_neg at hall
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hζ' : IsPrimitiveRoot (algebraMap F (v.adicCompletion F) ζ) p :=
    hζ.map_of_injective (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨L, _, _, θ, σ, hK⟩ := exists_isKum p (v.adicCompletion F) _ _ hp hζ' hδ
  obtain ⟨hfd, hrk, hσp, hfix, -, -, hnorm⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p _ L _ _ θ σ hK
  obtain ⟨e, he⟩ : ∃ e : ℕ, v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) := by
    have h0 : v.valuation F (p : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast hp.ne_zero
    have h1 : v.valuation F (p : F) ≤ 1 := by
      have := v.valuation_le_one (K := F) (p : 𝓞 F)
      simpa using this
    have h2 : WithZero.log (v.valuation F (p : F)) ≤ 0 := by
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      exact h1
    refine ⟨(-WithZero.log (v.valuation F (p : F))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨htL, hiL⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e L hp.pos he
  obtain ⟨htK, hiK⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e (v.adicCompletion F) hp.pos he
  rw [hrk] at hiL
  rw [Module.finrank_self, pow_one] at hiK
  have hQ : Ideal.absNorm v.asIdeal ^ e ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal ^ e = Q at hiL hiK hQ
  let s : Lˣ →* Lˣ := Units.map (σ : L →* L)
  have hs : ∀ (n : ℕ) (a : Lˣ), ((s^[n] a : Lˣ) : L) = σ^[n] (a : L) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let f : (v.adicCompletion F)ˣ →* Lˣ :=
    Units.map (algebraMap (v.adicCompletion F) L : v.adicCompletion F →* L)
  have hf : Function.Injective f :=
    Units.map_injective (algebraMap (v.adicCompletion F) L).injective
  have hfx : fix s = (⊤ : Subgroup (v.adicCompletion F)ˣ).map f := by
    ext a
    rw [mem_fix]
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hfix a (congrArg Units.val ha)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact a.ne_zero (by rw [hb, map_zero])
      exact ⟨Units.mk0 b hb0, trivial, Units.ext hb.symm⟩
    · rintro ⟨b, -, rfl⟩
      exact Units.ext (σ.commutes (b : v.adicCompletion F))
  have hiL0 : pIdx p (⊤ : Subgroup Lˣ) ≠ 0 := by
    rw [hiL]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hQ)) htL
  obtain ⟨-, h1, -, -, hH⟩ := GlobalTheory.T.herbrand_prime_order' p Lˣ s hp
    (fun a => Units.ext (by rw [hs, hσp])) hiL0 htL
  have h0 : (nrm s p).range.relIndex (fix s) = 1 := by
    rw [Subgroup.relIndex_eq_one, hfx]
    rintro _ ⟨c, -, rfl⟩
    obtain ⟨y, hy⟩ := (hnorm c).1 (hall c)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ∏ i ∈ Finset.range p, σ^[i] (0 : L) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) rfl
      rw [this] at hy
      exact c.ne_zero ((map_eq_zero _).1 hy.symm)
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [nrm_apply, Units.coe_prod]
    simp only [hs, Units.val_mk0]
    exact hy
  rw [h0, hfx, nonnorm_pIdx_map p f hf, nonnorm_pTor_map p f hf, hiL, hiK, one_pow] at hH
  generalize pTor p (⊤ : Subgroup Lˣ) = tL at hH htL
  generalize pTor p (⊤ : Subgroup (v.adicCompletion F)ˣ) = tK at hH htK
  generalize (dif s).range.relIndex (nrm s p).ker = h at hH h1
  have hc : Q ^ p * tL * tK ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hQ) htL) (pow_ne_zero _ htK)
  have key : p = h ^ (p - 1) * p ^ p := by
    apply mul_right_cancel₀ hc
    rw [mul_pow, mul_pow] at hH
    linear_combination hH
  have hle : p ^ p ≤ p := by
    calc p ^ p ≤ h ^ (p - 1) * p ^ p := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (pow_ne_zero _ h1))
      _ = p := key.symm
  have hlt : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp.one_lt hp.one_lt
  rw [pow_one] at hlt
  omega

end GlobalTheory.CNorm
