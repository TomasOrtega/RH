import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Module

namespace GroundTheory.Global

namespace Quadratic

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

def conj : Gal(K/ℚ) :=
  (exists_ne_one_of_card_eq_two (card_gal K)).choose

/- English proof (translation)
The claim follows from `(exists_ne_one_of_card_eq_two (card_gal K)).choose_spec`.
-/
theorem conj_ne_one : conj K ≠ 1 :=
  (exists_ne_one_of_card_eq_two (card_gal K)).choose_spec

/- English proof (translation)
Distinguish the cases in `h : σ = 1`. Conclude with `Or.inl h`. Conclude with `Or.inr (eq_of_ne_one_of_card_eq_two (card_gal K) h (conj_ne_one K))`.
-/
theorem eq_one_or_eq_conj (σ : Gal(K/ℚ)) : σ = 1 ∨ σ = conj K := by
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (eq_of_ne_one_of_card_eq_two (card_gal K) h (conj_ne_one K))

/- English proof (translation)
Establish `h` using `mul_self_eq_one_of_card_eq_two (card_gal K) (conj K)`. Rewrite using `[← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]`.
-/
theorem conj_conj (x : K) : conj K (conj K x) = x := by
  have h := mul_self_eq_one_of_card_eq_two (card_gal K) (conj K)
  rw [← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]

/- English proof (translation)
The claim follows from `galChar_apply_of_ne_one K (conj_ne_one K)`.
-/
theorem galChar_conj : galChar K (conj K) = -1 :=
  galChar_apply_of_ne_one K (conj_ne_one K)

/- English proof (translation)
Rewrite using `[trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 (conj K) (conj_ne_one K).symm (fun σ hσ ↦ absurd (eq_one_or_eq_conj K σ) (by tauto)), AlgEquiv.one_apply]`.
-/
theorem algebraMap_trace (x : K) : algebraMap ℚ K (Algebra.trace ℚ K x) = x + conj K x := by
  classical
  rw [trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 (conj K) (conj_ne_one K).symm
    (fun σ hσ ↦ absurd (eq_one_or_eq_conj K σ) (by tauto)), AlgEquiv.one_apply]

/- English proof (translation)
Rewrite using `[← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two]`.
-/
theorem card_chooseBasisIndex : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
  rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
    Algebra.IsQuadraticExtension.finrank_eq_two]

def intBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq (card_chooseBasisIndex K))

abbrev conjRing : 𝓞 K →+* 𝓞 K :=
  MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) (conj K)

def sqrtDiscr : 𝓞 K :=
  intBasis K 0 * conjRing K (intBasis K 1) - intBasis K 1 * conjRing K (intBasis K 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjRing (x : 𝓞 K) : ((conjRing K x : 𝓞 K) : K) = conj K (x : K) :=
  rfl

/- English proof (translation)
Establish `h` using `coe_discr K`. Rewrite `h` using `[← Algebra.discr_reindex ℚ (integralBasis K) (Fintype.equivFinOfCardEq (card_chooseBasisIndex K)), Algebra.discr_def, Matrix.det_fin_two]`. Establish `hb : ∀ i, ((integralBasis K) ∘ (Fintype.equivFinOfCardEq (card_chooseBasisIndex K)).symm) i = ((intBasis K i : 𝓞 K) : K)` using `fun i ↦ by`. Rewrite using `[Function.comp_apply, integralBasis_apply, intBasis, Basis.reindex_apply]`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb] at h`.

Establish `h'` using `congrArg (algebraMap ℚ K) h`. Simplify using `only [map_sub, map_mul, algebraMap_trace, map_intCast] at h'`. Rewrite using `[h', sqrtDiscr]`. Move the coercions through the operations in `[coe_conjRing, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrtDiscr_sq : (sqrtDiscr K : K) ^ 2 = (discr K : K) := by
  classical
  have h := coe_discr K
  rw [← Algebra.discr_reindex ℚ (integralBasis K)
    (Fintype.equivFinOfCardEq (card_chooseBasisIndex K)), Algebra.discr_def,
    Matrix.det_fin_two] at h
  have hb : ∀ i, ((integralBasis K) ∘ (Fintype.equivFinOfCardEq (card_chooseBasisIndex K)).symm) i =
      ((intBasis K i : 𝓞 K) : K) := fun i ↦ by
    rw [Function.comp_apply, integralBasis_apply, intBasis, Basis.reindex_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb] at h
  have h' := congrArg (algebraMap ℚ K) h
  simp only [map_sub, map_mul, algebraMap_trace, map_intCast] at h'
  rw [h', sqrtDiscr]
  push_cast [coe_conjRing, map_mul]
  ring

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `hc` using `conj_conj K`. Rewrite using `[sqrtDiscr, map_sub, map_mul, map_mul]`. Move the coercions through the operations in `[coe_conjRing, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_sqrtDiscr : conjRing K (sqrtDiscr K) = -sqrtDiscr K := by
  apply RingOfIntegers.coe_injective
  have hc := conj_conj K
  rw [sqrtDiscr, map_sub, map_mul, map_mul]
  push_cast [coe_conjRing, hc]
  ring

/- English proof (translation)
Introduce `h`. Establish `h2 : (discr K : K) = 0`. Rewrite using `[← sqrtDiscr_sq K, h]`. Simplify using the standard rewrite rules. Conclude with `discr_ne_zero K (by exact_mod_cast h2)`.
-/
theorem sqrtDiscr_ne_zero : sqrtDiscr K ≠ 0 := by
  intro h
  have h2 : (discr K : K) = 0 := by
    rw [← sqrtDiscr_sq K, h]
    simp
  exact discr_ne_zero K (by exact_mod_cast h2)

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Use `set b := intBasis K`. Establish `h1` using `b.sum_repr 1`. Establish `hx` using `b.sum_repr x`. Rewrite `h1`, `hx` using `[Fin.sum_univ_two]`.

Simplify using `only [zsmul_eq_mul] at h1 hx`. Establish `h1c` using `congrArg (conjRing K) h1`. Establish `hxc` using `congrArg (conjRing K) hx`. Simplify using `only [map_add, map_mul, map_intCast, map_one] at h1c hxc`. Use `⟨(b.repr x 1 * b.repr 1 0 - b.repr x 0 * b.repr 1 1 : ℤ), ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = conjRing K x - x`. Simplify using `only [sqrtDiscr]`. Use `push_cast`. Take the linear combination `((b.repr x 0 : 𝓞 K) * conjRing K (b 0) + (b.repr x 1 : 𝓞 K) * conjRing K (b 1)) * h1 - ((b.repr x 0 : 𝓞 K) * b 0 + (b.repr x 1 : 𝓞 K) * b 1) * h1c - hx + hxc`.
-/
theorem conj_smul_sub_mem_span (x : 𝓞 K) :
    conj K • x - x ∈ Ideal.span {sqrtDiscr K} := by
  rw [Ideal.mem_span_singleton']
  set b := intBasis K
  have h1 := b.sum_repr 1
  have hx := b.sum_repr x
  rw [Fin.sum_univ_two] at h1 hx
  simp only [zsmul_eq_mul] at h1 hx
  have h1c := congrArg (conjRing K) h1
  have hxc := congrArg (conjRing K) hx
  simp only [map_add, map_mul, map_intCast, map_one] at h1c hxc
  refine ⟨(b.repr x 1 * b.repr 1 0 - b.repr x 0 * b.repr 1 1 : ℤ), ?_⟩
  change _ = conjRing K x - x
  simp only [sqrtDiscr]
  push_cast
  linear_combination ((b.repr x 0 : 𝓞 K) * conjRing K (b 0) + (b.repr x 1 : 𝓞 K) * conjRing K (b 1)) * h1 -
    ((b.repr x 0 : 𝓞 K) * b 0 + (b.repr x 1 : 𝓞 K) * b 1) * h1c - hx + hxc

section Prime

open RationalSymbol

variable (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]

omit [Algebra.IsQuadraticExtension ℚ K] in

/- English proof (translation)
Establish `hover : v.asIdeal = w.asIdeal.under (𝓞 ℚ)` using `Ideal.LiesOver.over`. Rewrite using `[show (n : 𝓞 K) = algebraMap (𝓞 ℚ) (𝓞 K) (n : 𝓞 ℚ) from (map_intCast _ n).symm, ← Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `(n : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _`. Rewrite using `[← hover, DirichletHecke.asIdeal_eq_span, Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]`. Use `norm_cast`.
-/
theorem intCast_mem_iff (n : ℤ) : (n : 𝓞 K) ∈ w.asIdeal ↔ (prime v : ℤ) ∣ n := by
  have hover : v.asIdeal = w.asIdeal.under (𝓞 ℚ) := Ideal.LiesOver.over
  rw [show (n : 𝓞 K) = algebraMap (𝓞 ℚ) (𝓞 K) (n : 𝓞 ℚ) from (map_intCast _ n).symm,
    ← Ideal.mem_comap]
  change (n : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _
  rw [← hover, DirichletHecke.asIdeal_eq_span, Ideal.mem_span_singleton,
    ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]
  norm_cast

/- English proof (translation)
The claim follows from `RingOfIntegers.coe_injective (by push_cast; exact sqrtDiscr_sq K)`.
-/
theorem sqrtDiscr_sq' : sqrtDiscr K ^ 2 = (discr K : 𝓞 K) :=
  RingOfIntegers.coe_injective (by push_cast; exact sqrtDiscr_sq K)

/- English proof (translation)
The claim follows from `w.isPrime.mem_of_pow_mem 2 (sqrtDiscr_sq' K ▸ (intCast_mem_iff K v w _).2 h)`.
-/
theorem sqrtDiscr_mem_of_dvd (h : (prime v : ℤ) ∣ discr K) : sqrtDiscr K ∈ w.asIdeal :=
  w.isPrime.mem_of_pow_mem 2 (sqrtDiscr_sq' K ▸ (intCast_mem_iff K v w _).2 h)

/- English proof (translation)
The claim follows from `fun hm ↦ h ((intCast_mem_iff K v w _).1 (sqrtDiscr_sq' K ▸ w.asIdeal.pow_mem_of_mem hm 2 two_pos))`.
-/
theorem sqrtDiscr_not_mem_of_not_dvd (h : ¬ (prime v : ℤ) ∣ discr K) : sqrtDiscr K ∉ w.asIdeal :=
  fun hm ↦ h ((intCast_mem_iff K v w _).1 (sqrtDiscr_sq' K ▸ w.asIdeal.pow_mem_of_mem hm 2 two_pos))

/- English proof (translation)
The claim follows from `fun x ↦ (Ideal.span_singleton_le_iff_mem _).2 (sqrtDiscr_mem_of_dvd K v w h) (conj_smul_sub_mem_span K x)`.
-/
theorem conj_mem_inertia_of_dvd (h : (prime v : ℤ) ∣ discr K) :
    conj K ∈ w.asIdeal.inertia Gal(K/ℚ) := fun x ↦
  (Ideal.span_singleton_le_iff_mem _).2 (sqrtDiscr_mem_of_dvd K v w h) (conj_smul_sub_mem_span K x)

/- English proof (translation)
Break down `eq_one_or_eq_conj K σ with hs | hs` into its components or cases. Conclude with `hs`. It suffices to derive a contradiction. Substitute `hs` using the available equality. Establish `hm : conjRing K (sqrtDiscr K) - sqrtDiscr K ∈ w.asIdeal` using `hσ (sqrtDiscr K)`.

Rewrite `hm` using `[conj_sqrtDiscr, show -sqrtDiscr K - sqrtDiscr K = -(((2 : ℤ) : 𝓞 K) * sqrtDiscr K) by push_cast; ring, neg_mem_iff]`. Break down `w.isPrime.mem_or_mem hm with h2 | h2` into its components or cases. Establish `hd` using `(intCast_mem_iff K v w 2).1 h2`. Establish `hpr : (prime v).Prime` using `Fact.out`. Establish `: prime v ∣ 2` using `by exact_mod_cast hd`.

Conclude with `hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)`. Conclude with `sqrtDiscr_not_mem_of_not_dvd K v w h h2`.
-/
theorem eq_one_of_mem_inertia (hp : prime v ≠ 2) (h : ¬ (prime v : ℤ) ∣ discr K) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ w.asIdeal.inertia Gal(K/ℚ)) : σ = 1 := by
  rcases eq_one_or_eq_conj K σ with hs | hs
  · exact hs
  exfalso
  subst hs
  have hm : conjRing K (sqrtDiscr K) - sqrtDiscr K ∈ w.asIdeal := hσ (sqrtDiscr K)
  rw [conj_sqrtDiscr, show -sqrtDiscr K - sqrtDiscr K = -(((2 : ℤ) : 𝓞 K) * sqrtDiscr K) by
    push_cast; ring, neg_mem_iff] at hm
  rcases w.isPrime.mem_or_mem hm with h2 | h2
  · have hd := (intCast_mem_iff K v w 2).1 h2
    have hpr : (prime v).Prime := Fact.out
    have : prime v ∣ 2 := by exact_mod_cast hd
    exact hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)
  · exact sqrtDiscr_not_mem_of_not_dvd K v w h h2

/- English proof (translation)
Introduce `h`. Use `congrArg (fun u : ℂˣ ↦ (u : ℂ)) h` as an intermediate fact. Evaluate the numerical expressions using `at this`.
-/
theorem units_neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ ↦ (u : ℂ)) h
  norm_num at this

/- English proof (translation)
The claim follows from `(heckeCharacter_kronecker K).symm`.
-/
theorem heckeCharacterOfChar_galChar :
    heckeCharacterOfChar (galChar K) = DirichletHecke.heckeCharacter (kronecker K) :=
  (heckeCharacter_kronecker K).symm

/- English proof (translation)
Establish `w` using `placeAbove (L := K) v`. Establish `hnot : ¬ ∀ σ ∈ (placeAbove (L` using `K) v).asIdeal.inertia Gal(K/ℚ), galChar K σ = 1 := fun hall ↦ units_neg_one_ne_one ((galChar_conj K).symm.trans (hall _ (conj_mem_inertia_of_dvd K v _ h)))`. Establish `hdvd : v.asIdeal ∣ (heckeCharacterOfChar (galChar K)).conductor`. Assume the negation of the conclusion as `hn`. Conclude with `hnot ((not_dvd_conductor_heckeCharacterOfChar_iff _ v _).1 hn)`.

Rewrite `hdvd` using `[heckeCharacterOfChar_galChar]`. Conclude with `(DirichletHecke.dvd_conductor_iff _ (isPrimitive_kronecker K) v).1 hdvd`.
-/
theorem dvd_level_of_dvd_discr (h : (prime v : ℤ) ∣ discr K) : prime v ∣ level K := by
  have w := placeAbove (L := K) v
  have hnot : ¬ ∀ σ ∈ (placeAbove (L := K) v).asIdeal.inertia Gal(K/ℚ), galChar K σ = 1 :=
    fun hall ↦ units_neg_one_ne_one
      ((galChar_conj K).symm.trans (hall _ (conj_mem_inertia_of_dvd K v _ h)))
  have hdvd : v.asIdeal ∣ (heckeCharacterOfChar (galChar K)).conductor := by
    by_contra hn
    exact hnot ((not_dvd_conductor_heckeCharacterOfChar_iff _ v _).1 hn)
  rw [heckeCharacterOfChar_galChar] at hdvd
  exact (DirichletHecke.dvd_conductor_iff _ (isPrimitive_kronecker K) v).1 hdvd

/- English proof (translation)
Establish `hall : ∀ σ ∈ (placeAbove (L` using `K) v).asIdeal.inertia Gal(K/ℚ), galChar K σ = 1 := fun σ hσ ↦ by rw [eq_one_of_mem_inertia K v _ hp h hσ, map_one]`. Establish `hn` using `(not_dvd_conductor_heckeCharacterOfChar_iff _ v _).2 hall`. Rewrite `hn` using `[heckeCharacterOfChar_galChar]`. Conclude with `fun hd ↦ hn ((DirichletHecke.dvd_conductor_iff _ (isPrimitive_kronecker K) v).2 hd)`.
-/
theorem not_dvd_level_of_not_dvd_discr (hp : prime v ≠ 2) (h : ¬ (prime v : ℤ) ∣ discr K) :
    ¬ prime v ∣ level K := by
  have hall : ∀ σ ∈ (placeAbove (L := K) v).asIdeal.inertia Gal(K/ℚ), galChar K σ = 1 :=
    fun σ hσ ↦ by rw [eq_one_of_mem_inertia K v _ hp h hσ, map_one]
  have hn := (not_dvd_conductor_heckeCharacterOfChar_iff _ v _).2 hall
  rw [heckeCharacterOfChar_galChar] at hn
  exact fun hd ↦ hn ((DirichletHecke.dvd_conductor_iff _ (isPrimitive_kronecker K) v).2 hd)

omit [Algebra.IsQuadraticExtension ℚ K] in

/- English proof (translation)
Rewrite using `[← Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal), ← DirichletHecke.absNorm_asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem card_quotient_under : Nat.card (𝓞 ℚ ⧸ w.asIdeal.under (𝓞 ℚ)) = prime v := by
  rw [← Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal), ← DirichletHecke.absNorm_asIdeal,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `hpr : (prime v).Prime` using `Fact.out`. Use `set p := prime v with hpdef`. Establish `hodd : p = 2 * (p / 2) + 1`. Use `hpr.eq_one_or_self_of_dvd 2` as an intermediate fact. Establish `h2` using `Nat.div_add_mod p 2`.

Break down `Nat.mod_two_eq_zero_or_one p with h0 | h1` into its components or cases. Conclude with `absurd ((hpr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h0)).resolve_left (by norm_num)).symm hp`. Use linear arithmetic over natural numbers and integers. Establish `hF : φ • sqrtDiscr K - sqrtDiscr K ^ p ∈ w.asIdeal`. Use `hφ (sqrtDiscr K)` as an intermediate fact.

Rewrite `this` using `[card_quotient_under K v w]`. Then use the resulting hypothesis. Establish `hpow : sqrtDiscr K ^ p = sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K)`. Rewrite using `[hodd, pow_succ, pow_mul, sqrtDiscr_sq', ← hodd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hδ` using `sqrtDiscr_not_mem_of_not_dvd K v w h`. Establish `hd0 : ((discr K : ℤ) : ZMod p) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis. Break down `eq_one_or_eq_conj K φ with hs | hs` into its components or cases. Substitute `hs` using the available equality.

Rewrite `hF` using `[one_smul, hpow, show sqrtDiscr K - sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K) = sqrtDiscr K * (((1 - discr K ^ (p / 2) : ℤ)) : 𝓞 K) by push_cast; ring]`. Establish `hm` using `(w.isPrime.mem_or_mem hF).resolve_left hδ`. Rewrite `hm` using `[intCast_mem_iff K v w, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hm`. Establish `hsq : IsSquare ((discr K : ℤ) : ZMod p)` using `(ZMod.euler_criterion p hd0).2 (sub_eq_zero.1 hm).symm`.

Rewrite using `[(legendreSym.eq_one_iff p hd0).2 hsq, map_one]`. Evaluate the numerical expressions. Substitute `hs` using the available equality. Rewrite `hF` using `[show conj K • sqrtDiscr K = conjRing K (sqrtDiscr K) from rfl, conj_sqrtDiscr, hpow, show -sqrtDiscr K - sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K) = -(sqrtDiscr K * (((1 + discr K ^ (p / 2) : ℤ)) : 𝓞 K)) by push_cast; ring, neg_mem_iff]`. Establish `hm` using `(w.isPrime.mem_or_mem hF).resolve_left hδ`.

Rewrite `hm` using `[intCast_mem_iff K v w, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hm`. Establish `hns : ¬ IsSquare ((discr K : ℤ) : ZMod p)`. Introduce `hsq`. Establish `h1` using `(ZMod.euler_criterion p hd0).1 hsq`.

Establish `h2 : ((discr K : ℤ) : ZMod p) ^ (p / 2) = -1` using `by linear_combination hm`. Establish `: Fact (2 < p)` using `⟨lt_of_le_of_ne hpr.two_le (Ne.symm hp)⟩`. Conclude with `ZMod.neg_one_ne_one (h2.symm.trans h1)`. Rewrite using `[(legendreSym.eq_neg_one_iff p).2 hns, galChar_conj]`. Evaluate the numerical expressions.
-/
theorem galChar_frob_eq_legendreSym (hp : prime v ≠ 2) (h : ¬ (prime v : ℤ) ∣ discr K)
    {φ : Gal(K/ℚ)} (hφ : IsArithFrobAt (𝓞 ℚ) φ w.asIdeal) :
    ((galChar K φ : ℂˣ) : ℂ) = ((legendreSym (prime v) (discr K) : ℤ) : ℂ) := by
  have hpr : (prime v).Prime := Fact.out
  set p := prime v with hpdef
  have hodd : p = 2 * (p / 2) + 1 := by
    have := hpr.eq_one_or_self_of_dvd 2
    have h2 := Nat.div_add_mod p 2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · exact absurd ((hpr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h0)).resolve_left
        (by norm_num)).symm hp
    · omega
  have hF : φ • sqrtDiscr K - sqrtDiscr K ^ p ∈ w.asIdeal := by
    have := hφ (sqrtDiscr K)
    rwa [card_quotient_under K v w] at this
  have hpow : sqrtDiscr K ^ p = sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K) := by
    rw [hodd, pow_succ, pow_mul, sqrtDiscr_sq', ← hodd]
    push_cast
    ring
  have hδ := sqrtDiscr_not_mem_of_not_dvd K v w h
  have hd0 : ((discr K : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases eq_one_or_eq_conj K φ with hs | hs
  · subst hs
    rw [one_smul, hpow, show sqrtDiscr K - sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K) =
      sqrtDiscr K * (((1 - discr K ^ (p / 2) : ℤ)) : 𝓞 K) by push_cast; ring] at hF
    have hm := (w.isPrime.mem_or_mem hF).resolve_left hδ
    rw [intCast_mem_iff K v w, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
    push_cast at hm
    have hsq : IsSquare ((discr K : ℤ) : ZMod p) :=
      (ZMod.euler_criterion p hd0).2 (sub_eq_zero.1 hm).symm
    rw [(legendreSym.eq_one_iff p hd0).2 hsq, map_one]
    norm_num
  · subst hs
    rw [show conj K • sqrtDiscr K = conjRing K (sqrtDiscr K) from rfl, conj_sqrtDiscr, hpow,
      show -sqrtDiscr K - sqrtDiscr K * ((discr K ^ (p / 2) : ℤ) : 𝓞 K) =
      -(sqrtDiscr K * (((1 + discr K ^ (p / 2) : ℤ)) : 𝓞 K)) by push_cast; ring,
      neg_mem_iff] at hF
    have hm := (w.isPrime.mem_or_mem hF).resolve_left hδ
    rw [intCast_mem_iff K v w, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
    push_cast at hm
    have hns : ¬ IsSquare ((discr K : ℤ) : ZMod p) := by
      intro hsq
      have h1 := (ZMod.euler_criterion p hd0).1 hsq
      have h2 : ((discr K : ℤ) : ZMod p) ^ (p / 2) = -1 := by linear_combination hm
      have : Fact (2 < p) := ⟨lt_of_le_of_ne hpr.two_le (Ne.symm hp)⟩
      exact ZMod.neg_one_ne_one (h2.symm.trans h1)
    rw [(legendreSym.eq_neg_one_iff p).2 hns, galChar_conj]
    norm_num

/- English proof (translation)
Establish `hN` using `not_dvd_level_of_not_dvd_discr K v hp h`. Use `set w := placeAbove (L := K) v`. Establish `hall : ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), galChar K σ = 1` using `fun σ hσ ↦ by rw [eq_one_of_mem_inertia K v w hp h hσ, map_one]`. Establish `hφ` using `IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(K/ℚ) w.asIdeal`. Rewrite using `[← DirichletHecke.coe_heckeCharacter_uniformizer (kronecker K) hN, ← heckeCharacterOfChar_galChar, ← galChar_frob_eq_legendreSym K v w hp h hφ, ← localComponent_uniformizer (galChar K) v w hall (DirichletHecke.valued_uniformizer v) hφ, HeckeCharacter.localComponent_apply, HeckeCh …`.
-/
theorem kronecker_apply_of_not_dvd (hp : prime v ≠ 2) (h : ¬ (prime v : ℤ) ∣ discr K) :
    kronecker K (prime v) = ((legendreSym (prime v) (discr K) : ℤ) : ℂ) := by
  have hN := not_dvd_level_of_not_dvd_discr K v hp h
  set w := placeAbove (L := K) v
  have hall : ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), galChar K σ = 1 :=
    fun σ hσ ↦ by rw [eq_one_of_mem_inertia K v w hp h hσ, map_one]
  have hφ := IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(K/ℚ) w.asIdeal
  rw [← DirichletHecke.coe_heckeCharacter_uniformizer (kronecker K) hN,
    ← heckeCharacterOfChar_galChar, ← galChar_frob_eq_legendreSym K v w hp h hφ,
    ← localComponent_uniformizer (galChar K) v w hall (DirichletHecke.valued_uniformizer v) hφ,
    HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]

end Prime

/- English proof (translation)
Use `set v := RationalSymbol.placeOf ⟨p, hp.out⟩`. Establish `hv : RationalSymbol.prime v = p` using `RationalSymbol.prime_placeOf _`. Distinguish the cases in `h : (p : ℤ) ∣ discr K`. Establish `hN : p ∣ level K` using `hv ▸ dvd_level_of_dvd_discr K v (hv ▸ h)`. Establish `hnu : ¬ IsUnit (p : ZMod (level K))`.

Rewrite using `[ZMod.isUnit_iff_coprime]`. Conclude with `fun hc ↦ hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hN)`. Rewrite using `[MulChar.map_nonunit _ hnu, (legendreSym.eq_zero_iff p _).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h), Int.cast_zero]`. Establish `h1` using `kronecker_apply_of_not_dvd K v (hv ▸ hp2) (hv ▸ h)`. Simplify using `only [hv] at h1`.

Conclude with `h1`.
-/
theorem kronecker_apply_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    kronecker K p = (legendreSym p (discr K) : ℂ) := by
  set v := RationalSymbol.placeOf ⟨p, hp.out⟩
  have hv : RationalSymbol.prime v = p := RationalSymbol.prime_placeOf _
  by_cases h : (p : ℤ) ∣ discr K
  · have hN : p ∣ level K := hv ▸ dvd_level_of_dvd_discr K v (hv ▸ h)
    have hnu : ¬ IsUnit (p : ZMod (level K)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact fun hc ↦ hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hN)
    rw [MulChar.map_nonunit _ hnu, (legendreSym.eq_zero_iff p _).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h), Int.cast_zero]
  · have h1 := kronecker_apply_of_not_dvd K v (hv ▸ hp2) (hv ▸ h)
    simp only [hv] at h1
    exact h1

end Quadratic

end GroundTheory.Global
