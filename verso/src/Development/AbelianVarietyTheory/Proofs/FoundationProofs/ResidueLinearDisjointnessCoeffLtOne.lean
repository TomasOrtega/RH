import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.ResDisj

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Use `haveI : CharP (LaurentSeries (ZMod p)) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by`. Rewrite using `[← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p))]`. Use the proof step `simp)`. Assume the negation of the conclusion as `hne`. Establish `hb : a - HahnSeries.C (a.coeff 0) ≠ 0` using `sub_ne_zero.2 hne`.

Establish `hpow : (a - HahnSeries.C (a.coeff 0)) ^ p ^ f = a - HahnSeries.C (a.coeff 0)`. Rewrite using `[sub_pow_char_pow, ha, ← map_pow, ZMod.pow_card_pow]`. Establish `h0 : (a - HahnSeries.C (a.coeff 0)).coeff 0 = 0` using `by simp`. Generalize the expression as in `a - HahnSeries.C (a.coeff 0) = b at hb hpow h0`. Establish `ho` using `HahnSeries.order_pow b (p ^ f)`.

Rewrite `ho` using `[hpow, nsmul_eq_mul]`. Establish `h1 : (1 : ℤ) < ((p ^ f : ℕ) : ℤ)` using `by exact_mod_cast Nat.one_lt_pow hf hp.out.one_lt`. Establish `h2 : b.order = 0`. Establish `: (((p ^ f : ℕ) : ℤ) - 1) * b.order = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Conclude with `hb (HahnSeries.coeff_order_eq_zero.1 (by rw [h2]; exact h0))`.
-/
theorem const_of_pow_eq {f : ℕ} (hf : f ≠ 0) (a : LaurentSeries (ZMod p)) (ha : a ^ p ^ f = a) :
    a = HahnSeries.C (a.coeff 0) := by
  haveI : CharP (LaurentSeries (ZMod p)) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p))]; simp)
  by_contra hne
  have hb : a - HahnSeries.C (a.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have hpow : (a - HahnSeries.C (a.coeff 0)) ^ p ^ f = a - HahnSeries.C (a.coeff 0) := by
    rw [sub_pow_char_pow, ha, ← map_pow, ZMod.pow_card_pow]
  have h0 : (a - HahnSeries.C (a.coeff 0)).coeff 0 = 0 := by simp
  generalize a - HahnSeries.C (a.coeff 0) = b at hb hpow h0
  have ho := HahnSeries.order_pow b (p ^ f)
  rw [hpow, nsmul_eq_mul] at ho
  have h1 : (1 : ℤ) < ((p ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_lt_pow hf hp.out.one_lt
  have h2 : b.order = 0 := by
    have : (((p ^ f : ℕ) : ℤ) - 1) * b.order = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact h
  exact hb (HahnSeries.coeff_order_eq_zero.1 (by rw [h2]; exact h0))

/- English proof (translation)
Use `haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by`. Rewrite using `[← map_natCast (algebraMap (ZMod p) k)]`. Use the proof step `simp)`. Establish `hC : ∀ c : ZMod p, φ (HahnSeries.C c) = algebraMap (ZMod p) k c` using `fun c => DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) c`. Proceed by induction on `s using Finset.strongInduction with`.

Consider the case `H s ih`. Introduce `b hb hrel r`. Distinguish the cases in `hA : ∃ l : ι → ZMod p, (∀ t, t ∉ s → l t = 0) ∧ ∑ t, ε t * algebraMap (ZMod p) k (l t) = 0 ∧ ∃ u, l u = 1`. Take `⟨l, hl, hlr, u, hu⟩` from `hA`. Establish `hus : u ∈ s`.

Assume the negation of the conclusion as `h`. Rewrite `hu` using `[hl u h]`. Conclude with `zero_ne_one hu`. Use `ih (s.erase u) (Finset.erase_ssubset hus) (fun t => b t - HahnSeries.C (l t) * b u) ?_ ?_ r` as an intermediate fact. Simplify using `only [HahnSeries.coeff_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr] at this`.

Simplify using `using this`. Introduce `t ht`. Distinguish the cases in `htu : t = u`. Substitute `htu` using the available equality. Simplify using `[hu]`.

Establish `: t ∉ s` using `fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)`. Simplify using `[hb t this, hl t this]`. Simplify using `only [map_sub, map_mul, hC, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr, hrel]`. Simplify using the standard rewrite rules. Establish `hb0 : ∀ u, b u = 0`.

Introduce `u`. Assume the negation of the conclusion as `hu`. Establish `hus : u ∈ s`. Assume the negation of the conclusion as `h`. Conclude with `hu (hb u h)`.

Establish `hq : p ^ f ≠ 0` using `pow_ne_zero _ hp.out.ne_zero`. Use `set c : ι → LaurentSeries (ZMod p) := fun t => b t * (b u)⁻¹ with hc`. Establish `hcu : c u = 1` using `mul_inv_cancel₀ hu`. Establish `hcs : ∀ t, t ∉ s → c t = 0` using `fun t ht => by simp [hc, hb t ht]`. Establish `hcr : ∑ t, ε t * φ (c t) = 0`.

Simplify using `only [hc, map_mul, ← mul_assoc, ← Finset.sum_mul, hrel, zero_mul]`. Establish `hcr' : ∑ t, ε t * φ (c t ^ p ^ f) = 0`. Use `congrArg (· ^ p ^ f) hcr` as an intermediate fact. Simplify using `only [sum_pow_char_pow, mul_pow, hε, zero_pow hq] at this`. Simplify `this` using `only [map_pow]`.

Establish `hi` using `ih (s.erase u) (Finset.erase_ssubset hus) (fun t => c t ^ p ^ f - c t) ?_ ?_`. Establish `hfix : ∀ t, c t ^ p ^ f = c t`. Introduce `t`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `r'`.

Assume the negation of the conclusion as `hne`. Apply `hA` to reduce the goal to its premises. Use `⟨fun t' => (c t' ^ p ^ f - c t').coeff r' * ((c t ^ p ^ f - c t).coeff r')⁻¹, ?_, ?_, t, mul_inv_cancel₀ hne⟩` and prove the remaining obligations. Introduce `t' ht'`. Simplify using `[hcs t' ht', zero_pow hq]`.

Simplify using `only [map_mul, ← mul_assoc, ← Finset.sum_mul, hi r', zero_mul]`. Apply `hA` to reduce the goal to its premises. Use `⟨fun t => (c t).coeff 0, fun t ht => by simp [hcs t ht], ?_, u, by simp [hcu]⟩` and prove the remaining obligations. Rewrite using `[← hcr]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[← hC, ← const_of_pow_eq hf _ (hfix t)]`. Introduce `t ht`. Distinguish the cases in `htu : t = u`. Substitute `htu` using the available equality. Simplify using `[hcu]`.

Establish `: t ∉ s` using `fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)`. Simplify using `[hcs t this, zero_pow hq]`. Simplify using `only [map_sub, mul_sub, Finset.sum_sub_distrib, hcr, hcr', sub_self]`. Simplify using `[hb0]`.
-/
theorem coeff_rel_of_pow {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι]
    (φ : LaurentSeries (ZMod p) →+* k) {f : ℕ} (hf : f ≠ 0) (ε : ι → k) (hε : ∀ t, ε t ^ p ^ f = ε t)
    (s : Finset ι) : ∀ b : ι → LaurentSeries (ZMod p), (∀ t, t ∉ s → b t = 0) → ∑ t, ε t * φ (b t) = 0 →
      ∀ r, ∑ t, ε t * algebraMap (ZMod p) k ((b t).coeff r) = 0 := by
  classical
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) k)]; simp)
  have hC : ∀ c : ZMod p, φ (HahnSeries.C c) = algebraMap (ZMod p) k c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) c
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hb hrel r
  by_cases hA : ∃ l : ι → ZMod p, (∀ t, t ∉ s → l t = 0) ∧ ∑ t, ε t * algebraMap (ZMod p) k (l t) = 0 ∧ ∃ u, l u = 1
  · obtain ⟨l, hl, hlr, u, hu⟩ := hA
    have hus : u ∈ s := by
      by_contra h
      rw [hl u h] at hu; exact zero_ne_one hu
    have := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => b t - HahnSeries.C (l t) * b u) ?_ ?_ r
    · simp only [HahnSeries.coeff_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
        map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr] at this
      simpa using this
    · intro t ht
      by_cases htu : t = u
      · subst htu; simp [hu]
      · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
        simp [hb t this, hl t this]
    · simp only [map_sub, map_mul, hC, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr, hrel]
      simp
  · have hb0 : ∀ u, b u = 0 := by
      intro u
      by_contra hu
      have hus : u ∈ s := by
        by_contra h
        exact hu (hb u h)
      have hq : p ^ f ≠ 0 := pow_ne_zero _ hp.out.ne_zero
      set c : ι → LaurentSeries (ZMod p) := fun t => b t * (b u)⁻¹ with hc
      have hcu : c u = 1 := mul_inv_cancel₀ hu
      have hcs : ∀ t, t ∉ s → c t = 0 := fun t ht => by simp [hc, hb t ht]
      have hcr : ∑ t, ε t * φ (c t) = 0 := by
        simp only [hc, map_mul, ← mul_assoc, ← Finset.sum_mul, hrel, zero_mul]
      have hcr' : ∑ t, ε t * φ (c t ^ p ^ f) = 0 := by
        have := congrArg (· ^ p ^ f) hcr
        simp only [sum_pow_char_pow, mul_pow, hε, zero_pow hq] at this
        simpa only [map_pow] using this
      have hi := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => c t ^ p ^ f - c t) ?_ ?_
      · have hfix : ∀ t, c t ^ p ^ f = c t := by
          intro t
          rw [← sub_eq_zero]
          ext r'
          by_contra hne
          apply hA
          refine ⟨fun t' => (c t' ^ p ^ f - c t').coeff r' * ((c t ^ p ^ f - c t).coeff r')⁻¹, ?_, ?_, t,
            mul_inv_cancel₀ hne⟩
          · intro t' ht'
            simp [hcs t' ht', zero_pow hq]
          · simp only [map_mul, ← mul_assoc, ← Finset.sum_mul, hi r', zero_mul]
        apply hA
        refine ⟨fun t => (c t).coeff 0, fun t ht => by simp [hcs t ht], ?_, u, by simp [hcu]⟩
        rw [← hcr]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hC, ← const_of_pow_eq hf _ (hfix t)]
      · intro t ht
        by_cases htu : t = u
        · subst htu; simp [hcu]
        · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
          simp [hcs t this, zero_pow hq]
      · simp only [map_sub, mul_sub, Finset.sum_sub_distrib, hcr, hcr', sub_self]
    simp [hb0]

/- English proof (translation)
Set `K` to `IntermediateField.adjoin (ZMod p) (Set.range ε)`. Use `haveI : FiniteDimensional (ZMod p) K := IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨t, rfl⟩; exact (h t).isIntegral)`. Use `haveI : Finite K := Module.finite_of_finite (ZMod p)`. Use `letI : Fintype K := Fintype.ofFinite K`. Use `haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by`.

Rewrite using `[← map_natCast (algebraMap (ZMod p) K)]`. Use the proof step `simp)`. Take `⟨n, -, hn⟩` from `FiniteField.card K p`. Use `⟨n, n.ne_zero, fun t => ?_⟩` and prove the remaining obligations. Use `FiniteField.pow_card (⟨ε t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ : K)` as an intermediate fact.

Rewrite `this` using `[hn]`. Conclude with `congrArg Subtype.val this`.
-/
theorem exists_pow_eq {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι] (ε : ι → k)
    (h : ∀ t, IsAlgebraic (ZMod p) (ε t)) : ∃ f : ℕ, f ≠ 0 ∧ ∀ t, ε t ^ p ^ f = ε t := by
  let K := IntermediateField.adjoin (ZMod p) (Set.range ε)
  haveI : FiniteDimensional (ZMod p) K :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨t, rfl⟩; exact (h t).isIntegral)
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) K)]; simp)
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  refine ⟨n, n.ne_zero, fun t => ?_⟩
  have := FiniteField.pow_card (⟨ε t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ : K)
  rw [hn] at this
  exact congrArg Subtype.val this

open Polynomial in

/- English proof (translation)
Use `letI : NormalizedGCDMonoid ℤ_[p] := Classical.arbitrary _`. Use `⟨P.content, P.primPart, by rwa [Ne, content_eq_zero_iff], P.eq_C_content_mul_primPart, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hd : ∀ n, (p : ℤ_[p]) ∣ P.primPart.coeff n`. Introduce `n`.

Use `congrArg (fun Q => Q.coeff n) h0` as an intermediate fact. Simplify using `only [coeff_map, coeff_zero] at this`. Rewrite `this` using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Conclude with `PadicInt.prime_p.not_unit (isPrimitive_primPart P (p : ℤ_[p]) ((C_dvd_iff_dvd_coeff _ _).2 hd))`.
-/
theorem exists_prim (P : ℤ_[p][X]) (hP : P ≠ 0) :
    ∃ (c : ℤ_[p]) (Q : ℤ_[p][X]), c ≠ 0 ∧ P = C c * Q ∧ Q.map (PadicInt.toZMod (p := p)) ≠ 0 := by
  classical
  letI : NormalizedGCDMonoid ℤ_[p] := Classical.arbitrary _
  refine ⟨P.content, P.primPart, by rwa [Ne, content_eq_zero_iff], P.eq_C_content_mul_primPart, ?_⟩
  intro h0
  have hd : ∀ n, (p : ℤ_[p]) ∣ P.primPart.coeff n := by
    intro n
    have := congrArg (fun Q => Q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    rwa [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at this
  exact PadicInt.prime_p.not_unit (isPrimitive_primPart P (p : ℤ_[p]) ((C_dvd_iff_dvd_coeff _ _).2 hd))

/- English proof (translation)
Introduce `p hp Ω _ _ hC v hv hvp T n ψ hψ d e a he hsum r`. Establish `hq : p ^ n ≠ 0` using `pow_ne_zero _ hp.out.ne_zero`. Establish `hqq : IsIntegral (O0 p) (T.qq n)` using `IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)`. Establish `hint : ∀ x, ψ x ∈ v.valuationSubring`. Introduce `x`.

Establish `hx : ψ x ∈ ψ.range` using `⟨x, rfl⟩`. Rewrite `hx` using `[hψ.rng]`. Conclude with `(hv _).2 (adjoin_le_integralClosure hqq hx)`. Establish `hzp : ∀ z : ℤ_[p], ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z`. Introduce `z`.

Use `hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i = 0`. Simplify using `[hi]`. Establish `: (p : ℤ) ^ n * i ≠ 0` using `mul_ne_zero (by exact_mod_cast hq) hi`. Simplify using `[HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this, HahnSeries.coeff_single_of_ne hi]`.

Establish `: r ≠ 0` using `by rintro rfl; exact hr (dvd_zero _)`. Simplify using `[HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this]`. Set `A` to `v.valuationSubring`. Set `k` to `IsLocalRing.ResidueField A`. Set `ρ : A →+* k` to `IsLocalRing.residue A`.

Establish `hρ : ∀ x : A, ρ x = 0 ↔ v (x : Ω) < 1` using `fun x => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]`. Set `g : Lau p →+* A` to `(ψ.comp (algebraMap (Lau p) (O0 p))).codRestrict A (fun x => hint _)`. Establish `hg : ∀ x, (g x : Ω) = ψ (algebraMap (Lau p) (O0 p) x)` using `fun _ => rfl`. Establish `hp0 : (p : k) = 0`.

Rewrite using `[← map_natCast ρ, hρ]`. Simplify using `using hvp`. Use `haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Establish `hker : RingHom.ker (LauZ.red p) ≤ RingHom.ker (ρ.comp g)`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `(Basic.dvd_iff_map p x).2 hx`. Rewrite using `[RingHom.mem_ker, map_mul, map_natCast, hp0, zero_mul]`. Set `φ : LaurentSeries (ZMod p) →+* k` to `RingHom.liftOfRightInverse (LauZ.red p) (LauZ.lift p) (LauZ.red_lift p) ⟨ρ.comp g, hker⟩`. Establish `hφ : ∀ x, φ (LauZ.red p x) = ρ (g x)` using `fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ.comp g, hker⟩ x`.

Establish `hCz : ∀ z : ℤ_[p], ρ (g (HahnSeries.C z)) = algebraMap (ZMod p) k (PadicInt.toZMod z)`. Introduce `z`. Establish `h1 : LauZ.red p (HahnSeries.C z) = HahnSeries.C (PadicInt.toZMod z)`. Use extensionality with `i`. Rewrite using `[LauZ.red_coeff]`.

Distinguish the cases in `hi : i = 0`. Simplify using `[hi]`. Simplify using `[HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hi]`. Rewrite using `[← hφ, h1]`. Conclude with `DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) _`.

Set `E : Fin d → A` to `fun t => ⟨e t, (hv _).2 (he t).1⟩`. Set `g0 : ℤ_[p] →+* A` to `g.comp HahnSeries.C`. Establish `hg0 : (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) = A.subtype.comp g0`. Use extensionality with `z`. Establish `h2 : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z)`.

Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]`. Use `congr 1`. Use extensionality with `i`. Simplify using `[HahnSeries.algebraMap_apply']`. Use `show algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) = ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z))`.

Rewrite using `[hzp, h2, zp]`. Establish `halg : ∀ t, IsAlgebraic (ZMod p) (ρ (E t))`. Introduce `t`. Take `⟨P, hP, hPe⟩` from `(he t).2`. Take `⟨c, Q, hc, rfl, hQ⟩` from `exists_prim P hP`.

Use `⟨_, hQ, ?_⟩` and prove the remaining obligations. Rewrite `hPe` using `[Polynomial.aeval_def, Polynomial.eval₂_map, hg0, Polynomial.eval₂_mul, Polynomial.eval₂_C]`. Establish `hc' : (A.subtype.comp g0) c ≠ 0` using `by haveI : CharZero Ω := Basic.charZero_of_isClo hC`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p`. Rewrite using `[map_mul, map_pow, map_natCast]`.

Conclude with `mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))`. Establish `h1` using `(mul_eq_zero.1 hPe).resolve_left hc'`. Establish `h2 : Q.eval₂ g0 (E t) = 0`. Apply `A.subtype_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.hom_eval₂, map_zero]`.

Conclude with `h1`. Establish `h3` using `congrArg ρ h2`. Rewrite `h3` using `[Polynomial.hom_eval₂, map_zero]`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map, ← h3]`. Use `congr 1`.

Use extensionality with `z`. Conclude with `(hCz z).symm`. Take `⟨f, hf, hfix⟩` from `exists_pow_eq _ halg`. Establish `hrel : ∑ t, ρ (E t) * φ (LauZ.red p (a t)) = 0`. Simplify using `only [hφ, ← map_mul, ← map_sum]`.

Rewrite using `[hρ]`. Use `hsum using 2` and compare the differences between its conclusion and the goal. Conclude with `map_sum A.subtype _ _`. Establish `hres` using `coeff_rel_of_pow φ hf _ hfix Finset.univ _ (fun t ht => absurd (Finset.mem_univ t) ht) hrel r`. Simplify using `only [LauZ.red_coeff, ← hCz, ← map_mul, ← map_sum] at hres`.

Rewrite `hres` using `[hρ]`. Use `hres using 2` and compare the differences between its conclusion and the goal. Use `Eq.trans ?_ (map_sum A.subtype _ _).symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← hzp]`.

Both sides reduce to the same expression.
-/
theorem coeff_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) → v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) → v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 → ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  intro p hp Ω _ _ hC v hv hvp T n ψ hψ d e a he hsum r
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hint : ∀ x, ψ x ∈ v.valuationSubring := by
    intro x
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [hψ.rng] at hx
    exact (hv _).2 (adjoin_le_integralClosure hqq hx)
  have hzp : ∀ z : ℤ_[p], ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
    intro z
    refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
    · by_cases hi : i = 0
      · simp [hi]
      · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hi
        simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this, HahnSeries.coeff_single_of_ne hi]
    · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
      simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this]
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  have hρ : ∀ x : A, ρ x = 0 ↔ v (x : Ω) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let g : Lau p →+* A := (ψ.comp (algebraMap (Lau p) (O0 p))).codRestrict A (fun x => hint _)
  have hg : ∀ x, (g x : Ω) = ψ (algebraMap (Lau p) (O0 p) x) := fun _ => rfl
  have hp0 : (p : k) = 0 := by
    rw [← map_natCast ρ, hρ]; simpa using hvp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hker : RingHom.ker (LauZ.red p) ≤ RingHom.ker (ρ.comp g) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (Basic.dvd_iff_map p x).2 hx
    rw [RingHom.mem_ker, map_mul, map_natCast, hp0, zero_mul]
  let φ : LaurentSeries (ZMod p) →+* k :=
    RingHom.liftOfRightInverse (LauZ.red p) (LauZ.lift p) (LauZ.red_lift p) ⟨ρ.comp g, hker⟩
  have hφ : ∀ x, φ (LauZ.red p x) = ρ (g x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ.comp g, hker⟩ x
  have hCz : ∀ z : ℤ_[p], ρ (g (HahnSeries.C z)) = algebraMap (ZMod p) k (PadicInt.toZMod z) := by
    intro z
    have h1 : LauZ.red p (HahnSeries.C z) = HahnSeries.C (PadicInt.toZMod z) := by
      ext i
      rw [LauZ.red_coeff]
      by_cases hi : i = 0
      · simp [hi]
      · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hi]
    rw [← hφ, h1]
    exact DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) _
  let E : Fin d → A := fun t => ⟨e t, (hv _).2 (he t).1⟩
  let g0 : ℤ_[p] →+* A := g.comp HahnSeries.C
  have hg0 : (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) = A.subtype.comp g0 := by
    ext z
    have h2 : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z) := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
      congr 1
      ext i
      simp [HahnSeries.algebraMap_apply']
    show algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) = ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z))
    rw [hzp, h2, zp]
  have halg : ∀ t, IsAlgebraic (ZMod p) (ρ (E t)) := by
    intro t
    obtain ⟨P, hP, hPe⟩ := (he t).2
    obtain ⟨c, Q, hc, rfl, hQ⟩ := exists_prim P hP
    refine ⟨_, hQ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hg0, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hPe
    have hc' : (A.subtype.comp g0) c ≠ 0 := by
      haveI : CharZero Ω := Basic.charZero_of_isClo hC
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      rw [map_mul, map_pow, map_natCast]
      exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
    have h1 := (mul_eq_zero.1 hPe).resolve_left hc'
    have h2 : Q.eval₂ g0 (E t) = 0 := by
      apply A.subtype_injective
      rw [Polynomial.hom_eval₂, map_zero]
      exact h1
    have h3 := congrArg ρ h2
    rw [Polynomial.hom_eval₂, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← h3]
    congr 1
    ext z
    exact (hCz z).symm
  obtain ⟨f, hf, hfix⟩ := exists_pow_eq _ halg
  have hrel : ∑ t, ρ (E t) * φ (LauZ.red p (a t)) = 0 := by
    simp only [hφ, ← map_mul, ← map_sum]
    rw [hρ]
    convert hsum using 2
    exact map_sum A.subtype _ _
  have hres := coeff_rel_of_pow φ hf _ hfix Finset.univ _ (fun t ht => absurd (Finset.mem_univ t) ht) hrel r
  simp only [LauZ.red_coeff, ← hCz, ← map_mul, ← map_sum] at hres
  rw [hρ] at hres
  convert hres using 2
  refine Eq.trans ?_ (map_sum A.subtype _ _).symm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hzp]; rfl

end GlobalTheory.K5.ResDisj
