import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rb

open GlobalTheory.CompanionTheory.Ar.GR.FundGen Polynomial

/- English proof (translation)
Use `Ideal.isMaximal_iff.2 ⟨by rw [mem_mIdeal]; simp, fun J x _ hx hxJ => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[mem_mIdeal, not_lt]`. Establish `hu : IsUnit x` using `hv.isUnit_of_one' (le_antisymm (hv.map_le_one _) hx)`. Rewrite using `[← Ideal.eq_top_iff_one]`. Conclude with `J.eq_top_of_isUnit_mem hxJ hu`.
-/
theorem mIdeal_isMaximal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : (mIdeal v R hv).IsMaximal := by
  refine Ideal.isMaximal_iff.2 ⟨by rw [mem_mIdeal]; simp, fun J x _ hx hxJ => ?_⟩
  rw [mem_mIdeal, not_lt] at hx
  have hu : IsUnit x := hv.isUnit_of_one' (le_antisymm (hv.map_le_one _) hx)
  rw [← Ideal.eq_top_iff_one]
  exact J.eq_top_of_isUnit_mem hxJ hu

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Rewrite `hr` using `[(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hP, map_multiset_prod, Multiset.map_map]`. Use `absurd hr (not_lt.2 (Multiset.one_le_prod_of_one_le ?_))` and prove the remaining obligations. Introduce `x hx`.

Take `⟨z, hz, rfl⟩` from `Multiset.mem_map.1 hx`. Conclude with `h z (isRoot_of_mem_roots hz)`.
-/
theorem exists_root_near {C : Type} [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
    (P : C[X]) (hP : P.Monic) (r : C) (hr : v (P.eval r) < 1) :
    ∃ z, P.eval z = 0 ∧ v (r - z) < 1 := by
  by_contra h
  push Not at h
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hP, map_multiset_prod,
    Multiset.map_map] at hr
  refine absurd hr (not_lt.2 (Multiset.one_le_prod_of_one_le ?_))
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
  exact h z (isRoot_of_mem_roots hz)

/- English proof (translation)
Use `haveI := mIdeal_isMaximal v R hv`. Use `letI : Field (R ⧸ mIdeal v R hv) := Ideal.Quotient.field _`. Use `haveI : Nontrivial R := hv.nontrivial_iff.mpr inferInstance`. Use `haveI : IsAlgClosed (R ⧸ mIdeal v R hv) := by`. Use `IsAlgClosed.of_exists_root _ fun P hP hirr => ?_` and prove the remaining obligations.

Establish `hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk (mIdeal v R hv))` using `Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P`. Take `⟨Q, hQ, hdeg, hQm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hP`. Establish `hd : (Q.map (algebraMap R C)).degree ≠ 0`. Rewrite using `[hQm.degree_map, hdeg]`. Conclude with `(Polynomial.degree_pos_of_irreducible hirr).ne'`.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_root _ hd`. Establish `hint : IsIntegral R z` using `⟨Q, hQm, by rw [← Polynomial.eval_map]; exact hz⟩`. Take `⟨r, rfl⟩` from `hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hint)`. Use `⟨Ideal.Quotient.mk _ r, ?_⟩` and prove the remaining obligations. Establish `h0 : Q.eval r = 0`.

Apply `hv.hom_inj` to reduce the goal to its premises. Rewrite using `[map_zero, ← Polynomial.eval_map_apply]`. Conclude with `hz`. Rewrite using `[← hQ, Polynomial.eval_map_apply, h0, map_zero]`. Use `haveI : CharP (R ⧸ mIdeal v R hv) p := by`.

Rewrite using `[CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (Ideal.Quotient.mk (mIdeal v R hv)), Ideal.Quotient.eq_zero_iff_mem, mem_mIdeal]`. Simplify using `using hp`. Use `letI : Algebra (ZMod p) F := ZMod.algebra F p`. Use `letI : Algebra (ZMod p) (R ⧸ mIdeal v R hv) := ZMod.algebra _ p`. Conclude with `⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := R ⧸ mIdeal v R hv)).toRingHom⟩`.
-/
theorem exists_embedding (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hp : v (p : C) < 1) (F : Type) [Field F] [Fintype F] [CharP F p] :
    Nonempty (F →+* R ⧸ mIdeal v R hv) := by
  haveI := mIdeal_isMaximal v R hv
  letI : Field (R ⧸ mIdeal v R hv) := Ideal.Quotient.field _
  haveI : Nontrivial R := hv.nontrivial_iff.mpr inferInstance
  haveI : IsAlgClosed (R ⧸ mIdeal v R hv) := by
    refine IsAlgClosed.of_exists_root _ fun P hP hirr => ?_
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk (mIdeal v R hv)) :=
      Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P
    obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hP
    have hd : (Q.map (algebraMap R C)).degree ≠ 0 := by
      rw [hQm.degree_map, hdeg]
      exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hd
    have hint : IsIntegral R z := ⟨Q, hQm, by rw [← Polynomial.eval_map]; exact hz⟩
    obtain ⟨r, rfl⟩ := hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hint)
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    have h0 : Q.eval r = 0 := by
      apply hv.hom_inj
      rw [map_zero, ← Polynomial.eval_map_apply]
      exact hz
    rw [← hQ, Polynomial.eval_map_apply, h0, map_zero]
  haveI : CharP (R ⧸ mIdeal v R hv) p := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (Ideal.Quotient.mk (mIdeal v R hv)),
      Ideal.Quotient.eq_zero_iff_mem, mem_mIdeal]
    simpa using hp
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (R ⧸ mIdeal v R hv) := ZMod.algebra _ p
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := R ⧸ mIdeal v R hv)).toRingHom⟩

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc`. Take `⟨φ⟩` from `exists_embedding p v R hv hp F`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := Fˣ)`. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (φ (g : F))`. Establish `hN : Fintype.card Fˣ ≠ 0` using `Fintype.card_ne_zero`.

Establish `hgN : (g : F) ^ Fintype.card Fˣ = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]`. Establish `hsm : r ^ Fintype.card Fˣ - 1 ∈ mIdeal v R hv`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hr, ← map_pow, hgN, map_one, map_one, sub_self]`. Take `⟨z, hz, hrz⟩` from `exists_root_near v (X ^ Fintype.card Fˣ - Polynomial.C 1) (monic_X_pow_sub_C 1 hN) (algebraMap R C r) (by`.

Rewrite `hsm` using `[mem_mIdeal]`. Simplify using `using hsm)`. Establish `hz1 : v z ≤ 1`. Establish `: z = algebraMap R C r - (algebraMap R C r - z)` using `by ring`. Rewrite using `[this]`.

Conclude with `v.map_sub_le (hv.map_le_one r) hrz.le`. Take `⟨ζ, rfl⟩` from `hv.exists_of_le_one hz1`. Establish `hζ : ζ ^ Fintype.card Fˣ = 1`. Apply `hv.hom_inj` to reduce the goal to its premises. Use `hz` as an intermediate fact.

Simplify using `only [eval_sub, eval_pow, eval_X, eval_C] at this`. Rewrite using `[map_pow, map_one]`. Conclude with `sub_eq_zero.1 this`. Establish `hζg : Ideal.Quotient.mk (mIdeal v R hv) ζ = φ (g : F)`. Rewrite using `[← hr]`.

Use `symm`. Rewrite using `[Ideal.Quotient.eq, mem_mIdeal, map_sub]`. Conclude with `hrz`. Set `ζu : Rˣ` to `Units.ofPowEqOne ζ _ hζ hN`. Establish `hζu : ζu ∈ rootsOfUnity (Fintype.card Fˣ) R`.

Rewrite using `[mem_rootsOfUnity]`. Conclude with `Units.pow_ofPowEqOne hζ hN`. Set `σ : MulChar F R` to `MulChar.ofRootOfUnity hζu hg`. Establish `hσg : σ (g : F) = ζ` using `MulChar.ofRootOfUnity_spec hζu hg`. Establish `hσφ : ∀ a, Ideal.Quotient.mk (mIdeal v R hv) (σ a) = φ a`.

Introduce `a`. Distinguish the cases in `ha : a = 0`. Rewrite using `[ha, MulChar.map_zero, map_zero, map_zero]`. Take `⟨k, hk⟩` from `(mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 a ha)))`. Establish `hk' : (g : F) ^ k = a`.

Use `congrArg Units.val hk` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hk', map_pow, map_pow, hσg, hζg, map_pow]`. Use `⟨σ, fun a b => ?_⟩` and prove the remaining obligations. Use `set μ := σ (a + b) - σ a - σ b with hμ`.

Establish `hμm : v (algebraMap R C μ) < 1`. Rewrite using `[← mem_mIdeal v R hv, ← Ideal.Quotient.eq_zero_iff_mem, hμ, map_sub, map_sub, hσφ, hσφ, hσφ, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : 0 < v (p : C)`. Rewrite using `[pos_iff_ne_zero, v.ne_zero_iff]`.

Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hp0 hμm`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Use `Fintype.one_lt_card (α := F)` as an intermediate fact.

Simplify using `[hc] at this`. Establish `hkle : k ≤ p ^ (f * k)` using `(Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hf)).trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le`. Establish `hdvd : (p : R) ∣ μ ^ p ^ (f * k)`. Rewrite using `[hv.dvd_iff_le, map_pow, map_pow, map_natCast]`. Conclude with `(pow_le_pow_right_of_le_one' hμm.le hkle).trans hk.le`.

Establish `hfix : ∀ c : F, σ c ^ p ^ (f * k) = σ c`. Introduce `c`. Rewrite using `[← map_pow, pow_mul, ← hc, FiniteField.pow_card_pow]`. Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (by`. Introduce `hu`.

Use `hv.one_of_isUnit hu` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `hp.ne this)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `h0 : Ideal.Quotient.mk (Ideal.span {(p : R)}) μ ^ p ^ (f * k) = 0`.

Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `hdvd`. Establish `hfix' : ∀ c : F, Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ c) ^ p ^ (f * k) = Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ c)` using `fun c => by rw [← map_pow, hfix]`. Rewrite `h0` using `[hμ, map_sub, map_sub, sub_pow_char_pow, sub_pow_char_pow, hfix', hfix', hfix']`. Rewrite using `[hμ, map_sub, map_sub]`.

Conclude with `h0`.
-/
theorem fund_ex : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∃ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc
  obtain ⟨φ⟩ := exists_embedding p v R hv hp F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (φ (g : F))
  have hN : Fintype.card Fˣ ≠ 0 := Fintype.card_ne_zero
  have hgN : (g : F) ^ Fintype.card Fˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]
  have hsm : r ^ Fintype.card Fˣ - 1 ∈ mIdeal v R hv := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hr, ← map_pow, hgN, map_one, map_one,
      sub_self]
  obtain ⟨z, hz, hrz⟩ := exists_root_near v (X ^ Fintype.card Fˣ - Polynomial.C 1)
    (monic_X_pow_sub_C 1 hN) (algebraMap R C r) (by
      rw [mem_mIdeal] at hsm
      simpa using hsm)
  have hz1 : v z ≤ 1 := by
    have : z = algebraMap R C r - (algebraMap R C r - z) := by ring
    rw [this]
    exact v.map_sub_le (hv.map_le_one r) hrz.le
  obtain ⟨ζ, rfl⟩ := hv.exists_of_le_one hz1
  have hζ : ζ ^ Fintype.card Fˣ = 1 := by
    apply hv.hom_inj
    have := hz
    simp only [eval_sub, eval_pow, eval_X, eval_C] at this
    rw [map_pow, map_one]
    exact sub_eq_zero.1 this
  have hζg : Ideal.Quotient.mk (mIdeal v R hv) ζ = φ (g : F) := by
    rw [← hr]
    symm
    rw [Ideal.Quotient.eq, mem_mIdeal, map_sub]
    exact hrz
  let ζu : Rˣ := Units.ofPowEqOne ζ _ hζ hN
  have hζu : ζu ∈ rootsOfUnity (Fintype.card Fˣ) R := by
    rw [mem_rootsOfUnity]
    exact Units.pow_ofPowEqOne hζ hN
  let σ : MulChar F R := MulChar.ofRootOfUnity hζu hg
  have hσg : σ (g : F) = ζ := MulChar.ofRootOfUnity_spec hζu hg
  have hσφ : ∀ a, Ideal.Quotient.mk (mIdeal v R hv) (σ a) = φ a := by
    intro a
    by_cases ha : a = 0
    · rw [ha, MulChar.map_zero, map_zero, map_zero]
    · obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 a ha)))
      have hk' : (g : F) ^ k = a := by
        have := congrArg Units.val hk
        simpa using this
      rw [← hk', map_pow, map_pow, hσg, hζg, map_pow]
  refine ⟨σ, fun a b => ?_⟩
  set μ := σ (a + b) - σ a - σ b with hμ
  have hμm : v (algebraMap R C μ) < 1 := by
    rw [← mem_mIdeal v R hv, ← Ideal.Quotient.eq_zero_iff_mem, hμ, map_sub, map_sub, hσφ, hσφ,
      hσφ, map_add]
    ring
  have hp0 : 0 < v (p : C) := by
    rw [pos_iff_ne_zero, v.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 hμm
  have hf : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    simp [hc] at this
  have hkle : k ≤ p ^ (f * k) :=
    (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hf)).trans
      (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hdvd : (p : R) ∣ μ ^ p ^ (f * k) := by
    rw [hv.dvd_iff_le, map_pow, map_pow, map_natCast]
    exact (pow_le_pow_right_of_le_one' hμm.le hkle).trans hk.le
  have hfix : ∀ c : F, σ c ^ p ^ (f * k) = σ c := by
    intro c
    rw [← map_pow, pow_mul, ← hc, FiniteField.pow_card_pow]
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (by
    intro hu
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hp.ne this)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : Ideal.Quotient.mk (Ideal.span {(p : R)}) μ ^ p ^ (f * k) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hfix' : ∀ c : F, Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ c) ^ p ^ (f * k) =
      Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ c) := fun c => by rw [← map_pow, hfix]
  rw [hμ, map_sub, map_sub, sub_pow_char_pow, sub_pow_char_pow, hfix', hfix', hfix'] at h0
  rw [hμ, map_sub, map_sub]
  exact h0

/- English proof (translation)
Establish `hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F`. Use `Module.card_eq_pow_finrank (K := ZMod p) (V := F)` as an intermediate fact. Rewrite `this` using `[ZMod.card]`. Then use the resulting hypothesis. Conclude with `Nat.pow_right_injective (Fact.out : p.Prime).two_le (hcard.symm.trans hc)`.
-/
theorem finrank_eq (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [Algebra (ZMod p) F]
    (f : ℕ) (hc : Fintype.card F = p ^ f) : Module.finrank (ZMod p) F = f := by
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    have := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rwa [ZMod.card] at this
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (hcard.symm.trans hc)

/- English proof (translation)
Use `letI : Algebra (ZMod p) F := ZMod.algebra F p`. Establish `hf` using `finrank_eq p F f hc`. Substitute `hf` using the available equality. Apply `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).1` to reduce the goal to its premises. Use extensionality with `a`.

Simplify using `only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]`. Conclude with `h a`.
-/
theorem frob_pow_inj (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (f : ℕ) (hc : Fintype.card F = p ^ f) (n m : Fin f)
    (h : ∀ a : F, a ^ p ^ (n : ℕ) = a ^ p ^ (m : ℕ)) : n = m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hf := finrank_eq p F f hc
  subst hf
  apply (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).1
  ext a
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  exact h a

/- English proof (translation)
Establish `hn : ∀ k : ℕ, p ^ k ≠ 0` using `fun k => pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Use `frob_pow_inj p F f hc n m fun a => toHom_injective v R hv hp F σ hσ ?_` and prove the remaining obligations. Use `congrArg (fun χ : MulChar F R => χ a) h` as an intermediate fact. Simplify using `only [MulChar.pow_apply' _ (hn _)] at this`. Rewrite using `[toHom_apply, toHom_apply, map_pow σ, map_pow σ, this]`.
-/
theorem fund_pow_inj (p : ℕ) [Fact p.Prime] {C : Type} [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hp : v (p : C) < 1) (F : Type) [Field F] [Fintype F] [CharP F p]
    (f : ℕ) (hc : Fintype.card F = p ^ f) (σ : MulChar F R)
    (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) (n m : Fin f)
    (h : σ ^ p ^ (n : ℕ) = σ ^ p ^ (m : ℕ)) : n = m := by
  have hn : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine frob_pow_inj p F f hc n m fun a => toHom_injective v R hv hp F σ hσ ?_
  have := congrArg (fun χ : MulChar F R => χ a) h
  simp only [MulChar.pow_apply' _ (hn _)] at this
  rw [toHom_apply, toHom_apply, map_pow σ, map_pow σ, this]

/- English proof (translation)
Rewrite using `[← b.sum_repr a, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_zmod_val (b.repr a i), Nat.cast_smul_eq_nsmul, map_nsmul, h, nsmul_zero]`.
-/
theorem addHom_eq_zero (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra (ZMod p) F]
    {ι : Type} [Fintype ι] (b : Module.Basis ι (ZMod p) F) {A : Type} [AddCommGroup A]
    (ψ : F →+ A) (h : ∀ i, ψ (b i) = 0) (a : F) : ψ a = 0 := by
  rw [← b.sum_repr a, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← ZMod.natCast_zmod_val (b.repr a i), Nat.cast_smul_eq_nsmul, map_nsmul, h, nsmul_zero]

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc σ hσ l hl`. Use `letI : Algebra (ZMod p) F := ZMod.algebra F p`. Set `b : Module.Basis (Fin f) (ZMod p) F` to `Module.finBasisOfFinrankEq (ZMod p) F (finrank_eq p F f hc)`. Establish `hn : ∀ k : ℕ, p ^ k ≠ 0` using `fun k => pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Set `M : Matrix (Fin f) (Fin f) R` to `Matrix.of fun n i => (σ ^ p ^ (n : ℕ)) (b i)`.

Establish `hadd` using `frob_pow_additive p F σ hσ`. Establish `hdet : IsUnit M.det` using `by haveI := mIdeal_isMaximal v R hv haveI : IsDomain (R ⧸ mIdeal v R hv) := Ideal.Quotient.isDomain _`. Assume the negation of the conclusion as `hnu`. Establish `hmem : M.det ∈ mIdeal v R hv`. Rewrite using `[mem_mIdeal]`.

Conclude with `lt_of_le_of_ne (hv.map_le_one _) fun h => hnu (hv.isUnit_of_one' h)`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Take `⟨c, hc0, hcM⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hmem`. Set `φ : Fin f → (F →+* R ⧸ mIdeal v R hv)` to `fun n => toHom v R hv hp F (σ ^ p ^ (n : ℕ)) (hadd n)`. Establish `hinj : Function.Injective fun n => (φ n : F →* R ⧸ mIdeal v R hv)`.

Introduce `n m h`. Use `frob_pow_inj p F f hc n m fun a => toHom_injective v R hv hp F σ hσ ?_` and prove the remaining obligations. Use `DFunLike.congr_fun h a` as an intermediate fact. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ ((σ ^ p ^ (n : ℕ)) a) = Ideal.Quotient.mk _ ((σ ^ p ^ (m : ℕ)) a) at this`. Rewrite `this` using `[MulChar.pow_apply' _ (hn _), MulChar.pow_apply' _ (hn _)]`.

Rewrite using `[toHom_apply, toHom_apply, map_pow σ, map_pow σ, this]`. Establish `hli` using `(linearIndependent_monoidHom F (R ⧸ mIdeal v R hv)).comp _ hinj`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Apply `hc0` to reduce the goal to its premises. Use function extensionality and compare the values at `n`.

Use `hli c ?_ n` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Set `ψ : F →+ R ⧸ mIdeal v R hv` to `{ toFun := fun a => ∑ n, c n * φ n a map_zero' := by simp map_add' := fun a b => by simp [mul_add, Finset.sum_add_distrib] }`. Use `addHom_eq_zero p b ψ (fun i => congrFun hcM i) a` as an intermediate fact. Simplify `this` using `[ψ, Finset.sum_apply]`.

Establish `hβ : ∀ β : Fin f → R, (∀ i, l (b i) - (β ᵥ* M) i ∈ Ideal.span {(p : R)}) → ∀ a, l a - ∑ n, β n * (σ ^ p ^ (n : ℕ)) a ∈ Ideal.span {(p : R)}`. Introduce `β h a`. Set `ψ : F →+ R ⧸ Ideal.span {(p : R)}` to `AddMonoidHom.mk' (fun a => Ideal.Quotient.mk _ (l a - ∑ n, β n * (σ ^ p ^ (n : ℕ)) a)) (fun a b => by`. Rewrite using `[← map_add, Ideal.Quotient.eq]`. Establish `h2 : ∑ n, β n * ((σ ^ p ^ (n : ℕ)) (a + b) - (σ ^ p ^ (n : ℕ)) a - (σ ^ p ^ (n : ℕ)) b) ∈ Ideal.span {(p : R)}` using `Ideal.sum_mem _ fun n _ => Ideal.mul_mem_left _ _ (hadd n a b)`.

Use `Ideal.sub_mem _ (hl a b) h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Use the proof step `ring)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `addHom_eq_zero p b ψ (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (h i)) a`.

Establish `hsol : ((fun i => l (b i)) ᵥ* M⁻¹) ᵥ* M = fun i => l (b i)`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]`. Use `⟨(fun i => l (b i)) ᵥ* M⁻¹, hβ _ fun i => by rw [hsol]; simp, fun β' h' n => ?_⟩` and prove the remaining obligations. Establish `e : (fun i => l (b i)) ᵥ* M⁻¹ - β' = ((fun i => l (b i)) - β' ᵥ* M) ᵥ* M⁻¹`. Rewrite using `[Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]`.

Establish `e'` using `congrFun e n`. Rewrite `e'` using `[Pi.sub_apply]`. Rewrite using `[e', Matrix.vecMul, dotProduct]`. Use `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Conclude with `h' (b i)`.
-/
theorem moore : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ l : F → R, (∀ a b, l (a + b) - l a - l b ∈ Ideal.span {(p : R)}) → ∃ β : Fin f → R, (∀ a, l a - ∑ n, β n * (σ ^ p ^ (n : ℕ)) a ∈ Ideal.span {(p : R)}) ∧ ∀ β' : Fin f → R, (∀ a, l a - ∑ n, β' n * (σ ^ p ^ (n : ℕ)) a ∈ Ideal.span {(p : R)}) → ∀ n, β n - β' n ∈ Ideal.span {(p : R)} := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc σ hσ l hl
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let b : Module.Basis (Fin f) (ZMod p) F :=
    Module.finBasisOfFinrankEq (ZMod p) F (finrank_eq p F f hc)
  have hn : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  let M : Matrix (Fin f) (Fin f) R := Matrix.of fun n i => (σ ^ p ^ (n : ℕ)) (b i)
  have hadd := frob_pow_additive p F σ hσ
  have hdet : IsUnit M.det := by
    haveI := mIdeal_isMaximal v R hv
    haveI : IsDomain (R ⧸ mIdeal v R hv) := Ideal.Quotient.isDomain _
    by_contra hnu
    have hmem : M.det ∈ mIdeal v R hv := by
      rw [mem_mIdeal]
      exact lt_of_le_of_ne (hv.map_le_one _) fun h => hnu (hv.isUnit_of_one' h)
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
    obtain ⟨c, hc0, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hmem
    let φ : Fin f → (F →+* R ⧸ mIdeal v R hv) := fun n =>
      toHom v R hv hp F (σ ^ p ^ (n : ℕ)) (hadd n)
    have hinj : Function.Injective fun n => (φ n : F →* R ⧸ mIdeal v R hv) := by
      intro n m h
      refine frob_pow_inj p F f hc n m fun a => toHom_injective v R hv hp F σ hσ ?_
      have := DFunLike.congr_fun h a
      change Ideal.Quotient.mk _ ((σ ^ p ^ (n : ℕ)) a) =
        Ideal.Quotient.mk _ ((σ ^ p ^ (m : ℕ)) a) at this
      rw [MulChar.pow_apply' _ (hn _), MulChar.pow_apply' _ (hn _)] at this
      rw [toHom_apply, toHom_apply, map_pow σ, map_pow σ, this]
    have hli := (linearIndependent_monoidHom F (R ⧸ mIdeal v R hv)).comp _ hinj
    rw [Fintype.linearIndependent_iff] at hli
    apply hc0
    funext n
    refine hli c ?_ n
    funext a
    let ψ : F →+ R ⧸ mIdeal v R hv :=
      { toFun := fun a => ∑ n, c n * φ n a
        map_zero' := by simp
        map_add' := fun a b => by simp [mul_add, Finset.sum_add_distrib] }
    have := addHom_eq_zero p b ψ (fun i => congrFun hcM i) a
    simpa [ψ, Finset.sum_apply] using this
  have hβ : ∀ β : Fin f → R,
      (∀ i, l (b i) - (β ᵥ* M) i ∈ Ideal.span {(p : R)}) →
      ∀ a, l a - ∑ n, β n * (σ ^ p ^ (n : ℕ)) a ∈ Ideal.span {(p : R)} := by
    intro β h a
    let ψ : F →+ R ⧸ Ideal.span {(p : R)} := AddMonoidHom.mk'
      (fun a => Ideal.Quotient.mk _ (l a - ∑ n, β n * (σ ^ p ^ (n : ℕ)) a)) (fun a b => by
        rw [← map_add, Ideal.Quotient.eq]
        have h2 : ∑ n, β n * ((σ ^ p ^ (n : ℕ)) (a + b) - (σ ^ p ^ (n : ℕ)) a -
            (σ ^ p ^ (n : ℕ)) b) ∈ Ideal.span {(p : R)} :=
          Ideal.sum_mem _ fun n _ => Ideal.mul_mem_left _ _ (hadd n a b)
        convert Ideal.sub_mem _ (hl a b) h2 using 1
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring)
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact addHom_eq_zero p b ψ (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (h i)) a
  have hsol : ((fun i => l (b i)) ᵥ* M⁻¹) ᵥ* M = fun i => l (b i) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  refine ⟨(fun i => l (b i)) ᵥ* M⁻¹, hβ _ fun i => by rw [hsol]; simp, fun β' h' n => ?_⟩
  have e : (fun i => l (b i)) ᵥ* M⁻¹ - β' = ((fun i => l (b i)) - β' ᵥ* M) ᵥ* M⁻¹ := by
    rw [Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  have e' := congrFun e n
  rw [Pi.sub_apply] at e'
  rw [e', Matrix.vecMul, dotProduct]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_
  exact h' (b i)

end PositivityTheory.HtPt.Rb
