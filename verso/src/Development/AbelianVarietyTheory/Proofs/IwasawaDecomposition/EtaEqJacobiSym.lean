import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.FrobeniusOrbits.HostCorollaries

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped Pointwise

namespace GlobalTheory.EtaJacobi

/- English proof (translation)
Establish `hdo : Odd d` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[jacobiSym.neg _ hp]`. Break down `Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h` into its components or cases. Rewrite using `[ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hdo]`. Rewrite using `[ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobi_flip {p d : ℕ} (hp : Odd p) (hd : d % 4 = 3) :
    jacobiSym (p : ℤ) d = jacobiSym (-(d : ℤ)) p := by
  have hdo : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hdo]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hd]
    ring

/- English proof (translation)
Establish `hodd : p % 2 = 1` using `Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)`. Establish `h1 : x ^ p = ((legendreSym p m : ℤ) : k) * x`. Establish `h` using `congrArg (ZMod.castHom (dvd_refl p) k) (legendreSym.eq_pow p m)`. Rewrite `h` using `[map_intCast, map_pow, map_intCast]`. Rewrite using `[h, ← hx, ← pow_mul, ← pow_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ z : ℤ, (z : k) ^ p = z` using `fun z => by`. Use `map_intCast (frobenius k p) z` as an intermediate fact. Rewrite `this` using `[frobenius_def]`. Then use the resulting hypothesis.

Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ f ih`. Rewrite using `[pow_succ, pow_mul, ih, mul_pow, h2, h1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_prime_pow {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : p ≠ 2)
    (m : ℤ) (x : k) (hx : x ^ 2 = (m : k)) (f : ℕ) :
    x ^ (p ^ f) = ((legendreSym p m ^ f : ℤ) : k) * x := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have h1 : x ^ p = ((legendreSym p m : ℤ) : k) * x := by
    have h := congrArg (ZMod.castHom (dvd_refl p) k) (legendreSym.eq_pow p m)
    rw [map_intCast, map_pow, map_intCast] at h
    rw [h, ← hx, ← pow_mul, ← pow_succ]
    congr 1
    omega
  have h2 : ∀ z : ℤ, (z : k) ^ p = z := fun z => by
    have := map_intCast (frobenius k p) z
    rwa [frobenius_def] at this
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, h2, h1]
    push_cast
    ring

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/- English proof (translation)
Establish `h𝔭 : P.under (𝓞 K⁺) ≠ ⊥` using `Ideal.under_ne_bot (𝓞 K⁺) hP0`. Establish `hmax : P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hP0`. Establish `hfin : Finite (𝓞 K ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Take `⟨g, hg⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 K⁺) (K ≃ₐ[K⁺] K) P`. Establish `hN : Ideal.absNorm (P.under (𝓞 K⁺)) = Nat.card (𝓞 K⁺ ⧸ P.under (𝓞 K⁺))`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hg' : ∀ y : 𝓞 K, g • y - y ^ Ideal.absNorm (P.under (𝓞 K⁺)) ∈ P`. Introduce `y`. Rewrite using `[hN]`. Conclude with `hg y`.

Break down `Eta.cases K g with rfl | rfl` into its components or cases. Establish `hne : ¬ (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1`. Introduce `h1`. Break down `Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨-, h⟩` into its components or cases. Use linear arithmetic over natural numbers and integers.

Rewrite `h` using `[Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 K⁺)) P (K ≃ₐ[K⁺] K)]`. Establish `hc` using `Ideal.absNorm_pow_inertiaDeg (P.under (𝓞 K⁺)) P`. Rewrite `hc` using `[h, Ideal.absNorm_apply P, Submodule.cardQuot_apply]`. Use `set N := Ideal.absNorm (P.under (𝓞 K⁺)) with hNdef`. Establish `hN0 : N ≠ 0` using `by rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔭`.

Establish `hN1 : N ≠ 1`. Rewrite using `[hNdef, Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `Ideal.IsPrime.ne_top inferInstance`. Use `letI := Ideal.Quotient.field P`. Use `letI := Fintype.ofFinite (𝓞 K ⧸ P)`.

Establish `hall : ∀ u : (𝓞 K ⧸ P)ˣ, u ^ (N - 1) = 1`. Introduce `u`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ P)`. Establish `h3` using `Ideal.Quotient.eq.mpr (hg' y)`. Rewrite `h3` using `[one_smul, map_pow, hy]`.

Establish `h4 : u ^ (N - 1) * u = 1 * u`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), one_mul]`. Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `h3.symm`.

Conclude with `mul_right_cancel h4`. Establish `hd` using `(FiniteField.forall_pow_eq_one_iff (𝓞 K ⧸ P) (N - 1)).mp hall`. Rewrite `hd` using `[← Nat.card_eq_fintype_card, ← hc]`. Use `Nat.le_of_dvd (by omega) hd` as an intermediate fact. Establish `h5 : N * 2 ≤ N * N` using `Nat.mul_le_mul_left _ (by omega)`.

Rewrite `this` using `[sq]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hne]`. Simplify using `using hg' x`. Establish `hst : IsCMField.complexConj K • P = P` using `hg.mem_stabilizer`.

Establish `h1 : (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1`. Break down `Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨h, -⟩` into its components or cases. Conclude with `absurd hst ((Eta.ncard_eq_two_iff K hunr P hP0).mp h)`. Conclude with `h`. Rewrite using `[if_pos h1]`.

Conclude with `hg' x`.
-/
theorem frob_eq
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) (x : 𝓞 K) :
    (if (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 then IsCMField.complexConj K • x else x)
      - x ^ Ideal.absNorm (P.under (𝓞 K⁺)) ∈ P := by
  have h𝔭 : P.under (𝓞 K⁺) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K⁺) hP0
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨g, hg⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K⁺) (K ≃ₐ[K⁺] K) P
  have hN : Ideal.absNorm (P.under (𝓞 K⁺)) = Nat.card (𝓞 K⁺ ⧸ P.under (𝓞 K⁺)) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hg' : ∀ y : 𝓞 K, g • y - y ^ Ideal.absNorm (P.under (𝓞 K⁺)) ∈ P := by
    intro y; rw [hN]; exact hg y
  rcases Eta.cases K g with rfl | rfl
  · have hne : ¬ (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 := by
      intro h1
      rcases Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨-, h⟩
      · omega
      rw [Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 K⁺)) P (K ≃ₐ[K⁺] K)] at h
      have hc := Ideal.absNorm_pow_inertiaDeg (P.under (𝓞 K⁺)) P
      rw [h, Ideal.absNorm_apply P, Submodule.cardQuot_apply] at hc
      set N := Ideal.absNorm (P.under (𝓞 K⁺)) with hNdef
      have hN0 : N ≠ 0 := by rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔭
      have hN1 : N ≠ 1 := by
        rw [hNdef, Ne, Ideal.absNorm_eq_one_iff]
        exact Ideal.IsPrime.ne_top inferInstance
      letI := Ideal.Quotient.field P
      letI := Fintype.ofFinite (𝓞 K ⧸ P)
      have hall : ∀ u : (𝓞 K ⧸ P)ˣ, u ^ (N - 1) = 1 := by
        intro u
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ P)
        have h3 := Ideal.Quotient.eq.mpr (hg' y)
        rw [one_smul, map_pow, hy] at h3
        have h4 : u ^ (N - 1) * u = 1 * u := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
          ext
          rw [Units.val_pow_eq_pow_val]
          exact h3.symm
        exact mul_right_cancel h4
      have hd := (FiniteField.forall_pow_eq_one_iff (𝓞 K ⧸ P) (N - 1)).mp hall
      rw [← Nat.card_eq_fintype_card, ← hc] at hd
      have := Nat.le_of_dvd (by omega) hd
      have h5 : N * 2 ≤ N * N := Nat.mul_le_mul_left _ (by omega)
      rw [sq] at this
      omega
    rw [if_neg hne]
    simpa using hg' x
  · have hst : IsCMField.complexConj K • P = P := hg.mem_stabilizer
    have h1 : (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 := by
      rcases Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨h, -⟩
      · exact absurd hst ((Eta.ncard_eq_two_iff K hunr P hP0).mp h)
      · exact h
    rw [if_pos h1]
    exact hg' x

end CM

/- English proof (translation)
Rewrite using `[← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]`. Use `congr 1`. Use extensionality with `Q`. Simplify using `only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨P, rfl, rfl⟩`. Conclude with `⟨P.isPrime, ⟨rfl⟩⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext h2.over.symm, rfl⟩`.
-/
theorem card_aboveF {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F]
    [Algebra F L] (v : HeightOneSpectrum (𝓞 F)) :
    (aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

open Classical in

/- English proof (translation)
Introduce `R H v hv`. Establish `hCM : IsCMField H.E` using `H.isCMField_hostE`. Establish `hcc : ∀ x : H.E, IsCMField.complexConj H.E x = H.conj x` using `fun x => by`. Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, H.conjE_apply]`.

Establish `hsm : ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x = H.conj • x` using `fun x => RingOfIntegers.ext (hcc x)`. Establish `hd16 : H.d % 16 = 7` using `H.hyp.2.2.2.1`. Rewrite using `[card_aboveF]`. Establish `hvp` using `v.isPrime`. Take `⟨⟨P, hPp, hPo⟩⟩` from `(inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 H.E)))`.

Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P`. Establish `hunder : P.under (𝓞 H.F) = v.asIdeal` using `hPo.over.symm`. Establish `hmax : P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hP0`. Establish `hfin : Finite (𝓞 H.E ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Use `letI := Ideal.Quotient.field P`.

Take `⟨p, hchar⟩` from `CharP.exists (𝓞 H.E ⧸ P)`. Establish `hp : p.Prime` using `CharP.char_is_prime (𝓞 H.E ⧸ P) p`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hpP : (p : 𝓞 H.E) ∈ P`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `CharP.cast_eq_zero _ p`. Establish `hPZ : P.LiesOver (Ideal.span {(p : ℤ)})`. Establish `hm : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`.

Conclude with `hpP`. Establish `hvZ : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})` using `Ideal.LiesOver.tower_bot P v.asIdeal _`. Establish `hN` using `Ideal.pow_inertiaDeg p v.asIdeal`. Use `set f := v.asIdeal.inertiaDeg ℤ`. Rewrite using `[← hN, Nat.cast_pow, jacobiSym.pow_left]`.

Distinguish the cases in `hp2 : p = 2`. Establish `h2N : p ∣ H.condN`. Rewrite using `[hp2]`. Conclude with `((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans H.tower_dvd).trans (Dvd.dvd.mul_right (dvd_mul_right _ _) _)`. Establish `he` using `H.der.eta.2.2 p h2N P`.

Unfold `Formalism.HC.HostRaw.etaF at he`. Express the relevant statement in the definitionally equal form `(if (Ideal.primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he`. Rewrite `he` using `[hunder]`. Establish `h2 : (Ideal.primesOver v.asIdeal (𝓞 H.E)).ncard = 2`. Assume the negation of the conclusion as `hc`.

Rewrite `he` using `[if_neg hc]`. Conclude with `absurd he (by decide)`. Establish `hj : jacobiSym (p : ℤ) H.d = 1`. Rewrite using `[hp2, Nat.cast_ofNat, jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega)]`. Rewrite using `[h2, hj, if_neg (by decide), one_pow]`.

Establish `hunr : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P` using `fun P hP hP0 hx => H.der.unramEF P hP hP0 (fun x => hsm x ▸ hx x)`. Establish `hsq` using `H.sqd_sq`. Establish `hint : IsIntegral ℤ (H.sqd)`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hsq]`.

Conclude with `(isIntegral_natCast _).neg`. Set `β : 𝓞 H.E` to `⟨_, hint⟩`. Establish `hβsq : β ^ 2 = -(H.d : 𝓞 H.E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 H.E) H.E (β ^ 2) = algebraMap (𝓞 H.E) H.E (-(H.d : 𝓞 H.E))`.

Rewrite using `[map_pow, map_neg, map_natCast]`. Conclude with `hsq`. Establish `hcβ : IsCMField.complexConj H.E • β = -β`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h1` using `H.galE_bE H.conj`.

Rewrite `h1` using `[H.galE_conjE]`. Express the relevant statement in the definitionally equal form `IsCMField.complexConj H.E (H.sqd) = -(H.sqd)`. Rewrite using `[hcc, h1]`. Simplify using `[Formalism.HC.Frame.cc, c0]`. Establish `hfr` using `Ideal.Quotient.eq.mpr (frob_eq H.E hunr P hP0 β)`.

Rewrite `hfr` using `[hunder, ← hN, map_pow, hcβ]`. Establish `hx : (Ideal.Quotient.mk P β) ^ 2 = ((-(H.d : ℤ) : ℤ) : 𝓞 H.E ⧸ P)`. Rewrite using `[← map_pow, hβsq]`. Simplify using the standard rewrite rules. Establish `hdP : ((H.d : ℕ) : 𝓞 H.E ⧸ P) ≠ 0`.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Rewrite using `[← hunder, Ideal.mem_comap, map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h0`. Establish `hx0 : Ideal.Quotient.mk P β ≠ 0`.

Introduce `h0`. Rewrite `hx` using `[h0]`. Apply `hdP` to reduce the goal to its premises. Simplify using `using hx`. Rewrite `hfr` using `[pow_prime_pow p hp2 _ _ hx f]`.

Rewrite using `[jacobi_flip (hp.odd_of_ne_two hp2) (by omega), ← jacobiSym.legendreSym.to_jacobiSym]`. Establish `hs : legendreSym p (-(H.d : ℤ)) ^ f = 1 ∨ legendreSym p (-(H.d : ℤ)) ^ f = -1`. Establish `hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0`. Introduce `h0`. Rewrite `h0` using `[ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg, Int.natCast_dvd_natCast]`.

Conclude with `hdP ((CharP.cast_eq_zero_iff _ p _).mpr h0)`. Break down `legendreSym.eq_one_or_neg_one p hne with h1 | h1` into its components or cases. Use `left`. Rewrite using `[h1, one_pow]`. Rewrite using `[h1]`.

Conclude with `neg_one_pow_eq_or ℤ f`. Establish `h2 : (2 : 𝓞 H.E ⧸ P) ≠ 0`. Introduce `h0`. Establish `: p ∣ 2` using `(CharP.cast_eq_zero_iff (𝓞 H.E ⧸ P) p 2).mp (by simpa using h0)`. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)`.

Establish `hneg : Ideal.Quotient.mk P β ≠ -Ideal.Quotient.mk P β`. Introduce `h0`. Establish `: 2 * Ideal.Quotient.mk P β = 0` using `by linear_combination h0`. Conclude with `(mul_ne_zero h2 hx0) this`. Use `split_ifs at hfr ⊢ with hc`.

Break down `hs with hs | hs` into its components or cases. Rewrite `hfr` using `[hs, map_neg]`. Conclude with `absurd (by simpa using hfr.symm) hneg`. Conclude with `hs.symm`. Break down `hs with hs | hs` into its components or cases.

Conclude with `hs.symm`. Rewrite `hfr` using `[hs]`. Conclude with `absurd (by simpa using hfr) hneg`.
-/
theorem eta_eq_jacobiSym : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (v : HeightOneSpectrum (𝓞 H.F)),
    ((H.d : ℕ) : 𝓞 H.F) ∉ v.asIdeal →
    (if (aboveF (L := H.E) H.F v).card = 1 then (-1 : ℤ) else 1) =
      jacobiSym (Ideal.absNorm v.asIdeal : ℕ) H.d := by
  intro R H v hv
  have hCM : IsCMField H.E := H.isCMField_hostE
  have hcc : ∀ x : H.E, IsCMField.complexConj H.E x = H.conj x := fun x => by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, H.conjE_apply]
  have hsm : ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x = H.conj • x := fun x =>
    RingOfIntegers.ext (hcc x)
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  rw [card_aboveF]
  have hvp := v.isPrime
  obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 H.E)))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hunder : P.under (𝓞 H.F) = v.asIdeal := hPo.over.symm
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hfin : Finite (𝓞 H.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI := Ideal.Quotient.field P
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 H.E ⧸ P)
  have hp : p.Prime := CharP.char_is_prime (𝓞 H.E ⧸ P) p
  haveI : Fact p.Prime := ⟨hp⟩
  have hpP : (p : 𝓞 H.E) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hpP
  have hvZ : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.tower_bot P v.asIdeal _
  have hN := Ideal.pow_inertiaDeg p v.asIdeal
  set f := v.asIdeal.inertiaDeg ℤ
  rw [← hN, Nat.cast_pow, jacobiSym.pow_left]
  by_cases hp2 : p = 2
  · have h2N : p ∣ H.condN := by
      rw [hp2]
      exact ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans H.tower_dvd).trans
        (Dvd.dvd.mul_right (dvd_mul_right _ _) _)
    have he := H.der.eta.2.2 p h2N P
    unfold Formalism.HC.HostRaw.etaF at he
    change (if (Ideal.primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
    rw [hunder] at he
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 H.E)).ncard = 2 := by
      by_contra hc
      rw [if_neg hc] at he
      exact absurd he (by decide)
    have hj : jacobiSym (p : ℤ) H.d = 1 := by
      rw [hp2, Nat.cast_ofNat, jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),
        ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega)]
    rw [h2, hj, if_neg (by decide), one_pow]
  · have hunr : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
        ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P :=
      fun P hP hP0 hx => H.der.unramEF P hP hP0 (fun x => hsm x ▸ hx x)
    have hsq := H.sqd_sq
    have hint : IsIntegral ℤ (H.sqd) := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hsq]
      exact (isIntegral_natCast _).neg
    let β : 𝓞 H.E := ⟨_, hint⟩
    have hβsq : β ^ 2 = -(H.d : 𝓞 H.E) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 H.E) H.E (β ^ 2) = algebraMap (𝓞 H.E) H.E (-(H.d : 𝓞 H.E))
      rw [map_pow, map_neg, map_natCast]
      exact hsq
    have hcβ : IsCMField.complexConj H.E • β = -β := by
      apply RingOfIntegers.ext
      have h1 := H.galE_bE H.conj
      rw [H.galE_conjE] at h1
      change IsCMField.complexConj H.E (H.sqd) = -(H.sqd)
      rw [hcc, h1]
      simp [Formalism.HC.Frame.cc, c0]
    have hfr := Ideal.Quotient.eq.mpr (frob_eq H.E hunr P hP0 β)
    rw [hunder, ← hN, map_pow, hcβ] at hfr
    have hx : (Ideal.Quotient.mk P β) ^ 2 = ((-(H.d : ℤ) : ℤ) : 𝓞 H.E ⧸ P) := by
      rw [← map_pow, hβsq]; simp
    have hdP : ((H.d : ℕ) : 𝓞 H.E ⧸ P) ≠ 0 := by
      intro h0
      apply hv
      rw [← hunder, Ideal.mem_comap, map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h0
    have hx0 : Ideal.Quotient.mk P β ≠ 0 := by
      intro h0
      rw [h0] at hx
      apply hdP
      simpa using hx
    rw [pow_prime_pow p hp2 _ _ hx f] at hfr
    rw [jacobi_flip (hp.odd_of_ne_two hp2) (by omega), ← jacobiSym.legendreSym.to_jacobiSym]
    have hs : legendreSym p (-(H.d : ℤ)) ^ f = 1 ∨ legendreSym p (-(H.d : ℤ)) ^ f = -1 := by
      have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg, Int.natCast_dvd_natCast] at h0
        exact hdP ((CharP.cast_eq_zero_iff _ p _).mpr h0)
      rcases legendreSym.eq_one_or_neg_one p hne with h1 | h1
      · left; rw [h1, one_pow]
      · rw [h1]; exact neg_one_pow_eq_or ℤ f
    have h2 : (2 : 𝓞 H.E ⧸ P) ≠ 0 := by
      intro h0
      have : p ∣ 2 := (CharP.cast_eq_zero_iff (𝓞 H.E ⧸ P) p 2).mp (by simpa using h0)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hneg : Ideal.Quotient.mk P β ≠ -Ideal.Quotient.mk P β := by
      intro h0
      have : 2 * Ideal.Quotient.mk P β = 0 := by linear_combination h0
      exact (mul_ne_zero h2 hx0) this
    split_ifs at hfr ⊢ with hc
    · rcases hs with hs | hs
      · rw [hs, map_neg] at hfr
        exact absurd (by simpa using hfr.symm) hneg
      · exact hs.symm
    · rcases hs with hs | hs
      · exact hs.symm
      · rw [hs] at hfr
        exact absurd (by simpa using hfr) hneg

end GlobalTheory.EtaJacobi
