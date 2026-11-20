import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjInvolutiveAndExistsHalfIdempotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRealSpanEqConjFixedPrimeMulRelNormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeNatCastMem

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.InertTrivial

section Abstract

variable {A : Type} [CommRing A]

def proj (e : A) (he : e * e = e) : Aˣ →* Aˣ where
  toFun x := ⟨e * x + (1 - e), e * ((x⁻¹ : Aˣ) : A) + (1 - e),
    by linear_combination (1 - (x : A)) * (1 - ((x⁻¹ : Aˣ) : A)) * he + e * x.mul_inv,
    by linear_combination (1 - (x : A)) * (1 - ((x⁻¹ : Aˣ) : A)) * he + e * x.mul_inv⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul]
    linear_combination (-(1 - (x : A)) * (1 - (y : A))) * he

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem proj_val (e : A) (he : e * e = e) (x : Aˣ) : (proj e he x : A) = e * x + (1 - e) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem proj_inv (e : A) (he : e * e = e) (x : Aˣ) :
    (((proj e he x)⁻¹ : Aˣ) : A) = e * ((x⁻¹ : Aˣ) : A) + (1 - e) := rfl

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.PrimeNatCastMembership.exists_prime_natCast_mem P hP n hn h`.
-/
theorem exists_prime_mem (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0) (h : (n : A) ∈ P) :
    ∃ q : ℕ, q.Prime ∧ (q : A) ∈ P :=
  _root_.GlobalTheory.PrimeNatCastMembership.exists_prime_natCast_mem P hP n hn h

variable (S : Subring A)

/- English proof (translation)
Set `I : Ideal ℤ` to `{ carrier := {m | ∃ w ∈ S, (m : A) * y = (N : A) * w} add_mem' := by`. Introduce and unpack `a b ⟨v, hv, ha⟩ ⟨w, hw, hb⟩`. Conclude with `⟨v + w, add_mem hv hw, by push_cast; linear_combination ha + hb⟩`. Use the proof step `zero_mem' := ⟨0, zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c a ⟨v, hv, ha⟩`. Conclude with `⟨c * v, mul_mem (intCast_mem _ _) hv, by`. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Take the linear combination `(c : A) * ha⟩ }`.

Take `⟨g, hg⟩` from `(IsPrincipalIdealRing.principal I).principal`. Establish `hg' : I = Ideal.span {g}` using `hg`. Establish `h1 : g.natAbs = 1`. Assume the negation of the conclusion as `hne`. Take `⟨q, hq, hqg⟩` from `Nat.exists_prime_and_dvd hne`.

Take `⟨k, n', hn', e⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one`. Take `⟨m, -, hm, s, hs, e'⟩` from `h q hq k`. Establish `hmem : ((m * n' : ℕ) : ℤ) ∈ I` using `⟨s, hs, by`. Rewrite using `[e]`. Use `push_cast`.

Take the linear combination `(n' : A) * e'⟩`. Rewrite `hmem` using `[hg', Ideal.mem_span_singleton, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]`. Break down `(Nat.Prime.dvd_mul hq).1 (hqg.trans hmem) with h2 | h2` into its components or cases. Conclude with `(Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm h2`. Conclude with `hn' h2`.

Establish `h2 : (1 : ℤ) ∈ I`. Rewrite using `[hg', Ideal.mem_span_singleton, ← Int.natAbs_dvd_natAbs, h1]`. Simplify using the standard rewrite rules. Take `⟨w, hw, e⟩` from `h2`. Conclude with `⟨w, hw, by simpa using e⟩`.
-/
theorem dvd_of_forall_prime (y : A)
    (h : ∀ q : ℕ, q.Prime → ∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s ∈ S, (m : A) * y = (q : A) ^ k * s)
    (N : ℕ) (hN : 0 < N) : ∃ w ∈ S, y = (N : A) * w := by
  let I : Ideal ℤ :=
    { carrier := {m | ∃ w ∈ S, (m : A) * y = (N : A) * w}
      add_mem' := by
        rintro a b ⟨v, hv, ha⟩ ⟨w, hw, hb⟩
        exact ⟨v + w, add_mem hv hw, by push_cast; linear_combination ha + hb⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨v, hv, ha⟩
        exact ⟨c * v, mul_mem (intCast_mem _ _) hv, by
          simp only [smul_eq_mul]; push_cast; linear_combination (c : A) * ha⟩ }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  have hg' : I = Ideal.span {g} := hg
  have h1 : g.natAbs = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨k, n', hn', e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one
    obtain ⟨m, -, hm, s, hs, e'⟩ := h q hq k
    have hmem : ((m * n' : ℕ) : ℤ) ∈ I := ⟨s, hs, by
      rw [e]; push_cast; linear_combination (n' : A) * e'⟩
    rw [hg', Ideal.mem_span_singleton, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at hmem
    rcases (Nat.Prime.dvd_mul hq).1 (hqg.trans hmem) with h2 | h2
    · exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm h2
    · exact hn' h2
  have h2 : (1 : ℤ) ∈ I := by
    rw [hg', Ideal.mem_span_singleton, ← Int.natAbs_dvd_natAbs, h1]; simp
  obtain ⟨w, hw, e⟩ := h2
  exact ⟨w, hw, by simpa using e⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self (⟨x, hx⟩ : S))`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self (⟨y, hy⟩ : S))`. Establish `ha1 : (a : A) * y = x` using `congrArg Subtype.val ha`. Establish `hb1 : (b : A) * x = y` using `congrArg Subtype.val hb`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Units.val_mul, ← ha1, Units.mul_inv_cancel_right]`. Conclude with `a.2`. Rewrite using `[mul_inv_rev, inv_inv, Units.val_mul, ← hb1, Units.mul_inv_cancel_right]`. Conclude with `b.2`.
-/
theorem assoc_of_span_eq (x y : Aˣ) (hx : (x : A) ∈ S) (hy : (y : A) ∈ S)
    (h : Ideal.span {(⟨x, hx⟩ : S)} = Ideal.span {(⟨y, hy⟩ : S)}) :
    ((x * y⁻¹ : Aˣ) : A) ∈ S ∧ (((x * y⁻¹)⁻¹ : Aˣ) : A) ∈ S := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self (⟨x, hx⟩ : S))
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self (⟨y, hy⟩ : S))
  have ha1 : (a : A) * y = x := congrArg Subtype.val ha
  have hb1 : (b : A) * x = y := congrArg Subtype.val hb
  constructor
  · rw [Units.val_mul, ← ha1, Units.mul_inv_cancel_right]; exact a.2
  · rw [mul_inv_rev, inv_inv, Units.val_mul, ← hb1, Units.mul_inv_cancel_right]; exact b.2

end Abstract

variable (D : D7)

noncomputable def intInc : 𝓞 D.host.E →+* OhE D :=
  ((inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict (OhE D) (VacMove.inc_int D)

def Gen (B : Ideal (𝓞 D.host.E)) (y : (AE D)ˣ) : Prop :=
  ∃ hy : (y : AE D) ∈ OhE D, B.map (intInc D) = Ideal.span {(⟨y, hy⟩ : OhE D)}

/- English proof (translation)
Take `⟨y, h1, k, b, w, hb, hw, e⟩` from `GlobalTheory.IdealIdele.exists_idele_generator D B hB`. Establish `hy : (y : AE D) ∈ OhE D`. Rewrite using `[e]`. Conclude with `sum_mem fun i _ => mul_mem (VacMove.inc_int D _) (hw i)`. Use `⟨y, hy, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `c hc`. Use `Ideal.mem_span_singleton'.2 ⟨⟨_, h1 c hc⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((y⁻¹ : (AE D)ˣ) : AE D) * inc D (c : D.host.E) * y = inc D (c : D.host.E)`. Rewrite using `[mul_right_comm, Units.inv_mul, one_mul]`.

Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `: (⟨y, hy⟩ : OhE D) = ∑ i, intInc D (b i) * ⟨w i, hw i⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `e`.

Rewrite using `[this]`. Conclude with `sum_mem fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hb i))`.
-/
theorem exists_gen (B : Ideal (𝓞 D.host.E)) (hB : B ≠ ⊥) : ∃ y, Gen D B y := by
  obtain ⟨y, h1, k, b, w, hb, hw, e⟩ := GlobalTheory.IdealIdele.exists_idele_generator D B hB
  have hy : (y : AE D) ∈ OhE D := by
    rw [e]; exact sum_mem fun i _ => mul_mem (VacMove.inc_int D _) (hw i)
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h1 c hc⟩, Subtype.ext ?_⟩
    change ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (c : D.host.E) * y = inc D (c : D.host.E)
    rw [mul_right_comm, Units.inv_mul, one_mul]
  · rw [Ideal.span_singleton_le_iff_mem]
    have : (⟨y, hy⟩ : OhE D) = ∑ i, intInc D (b i) * ⟨w i, hw i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact e
    rw [this]
    exact sum_mem fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hb i))

variable {D}

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Take `⟨h3, h4⟩` from `hz`. Use `⟨mul_mem h1 h3, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.map_mul, h2, h4, Ideal.span_singleton_mul_span_singleton]`. Both sides reduce to the same expression.
-/
theorem Gen.mul {B C : Ideal (𝓞 D.host.E)} {y z : (AE D)ˣ} (hy : Gen D B y) (hz : Gen D C z) :
    Gen D (B * C) (y * z) := by
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := hz
  refine ⟨mul_mem h1 h3, ?_⟩
  rw [Ideal.map_mul, h2, h4, Ideal.span_singleton_mul_span_singleton]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Use `⟨VacMove.sgA_mem D h1, ?_⟩` and prove the remaining obligations. Set `s : OhE D →+* OhE D` to `((sgA D).comp (OhE D).subtype).codRestrict (OhE D) (fun x => VacMove.sgA_mem D x.2)`. Establish `hs : (intInc D).comp (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) = s.comp (intInc D)`. Use extensionality with `b : 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = sgA D (inc D (b : D.host.E))`. Rewrite using `[GlobalTheory.NormSum.PtsMem.sgA_inc]`. Both sides reduce to the same expression. Rewrite using `[Ideal.pointwise_smul_def, Ideal.map_map, hs, ← Ideal.map_map, h2, Ideal.map_span, Set.image_singleton]`.

Both sides reduce to the same expression.
-/
theorem Gen.conj {B : Ideal (𝓞 D.host.E)} {y : (AE D)ˣ} (hy : Gen D B y) :
    Gen D (D.host.conj • B) (sgU D y) := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨VacMove.sgA_mem D h1, ?_⟩
  let s : OhE D →+* OhE D := ((sgA D).comp (OhE D).subtype).codRestrict (OhE D)
    (fun x => VacMove.sgA_mem D x.2)
  have hs : (intInc D).comp (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) = s.comp (intInc D) := by
    ext b : 1
    apply Subtype.ext
    change _ = sgA D (inc D (b : D.host.E))
    rw [GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  rw [Ideal.pointwise_smul_def, Ideal.map_map, hs, ← Ideal.map_map, h2, Ideal.map_span, Set.image_singleton]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Take `⟨h3, h4⟩` from `hz`. Conclude with `assoc_of_span_eq (OhE D) y z h1 h3 (h2.symm.trans h4)`.
-/
theorem Gen.intU {B : Ideal (𝓞 D.host.E)} {y z : (AE D)ˣ} (hy : Gen D B y) (hz : Gen D B z) :
    IntU D (y * z⁻¹) := by
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := hz
  exact assoc_of_span_eq (OhE D) y z h1 h3 (h2.symm.trans h4)

/- English proof (translation)
Establish `h1 : ((Units.map (inc D).toMonoidHom a : (AE D)ˣ) : AE D) = inc D (t : D.host.E)`. Rewrite using `[← h]`. Both sides reduce to the same expression. Use `⟨h1 ▸ VacMove.inc_int D t, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Use `congr 2`. Conclude with `Subtype.ext h1.symm`.
-/
theorem gen_span (t : 𝓞 D.host.E) (a : D.host.Eˣ) (h : (a : D.host.E) = t) :
    Gen D (Ideal.span {t}) (Units.map (inc D).toMonoidHom a) := by
  have h1 : ((Units.map (inc D).toMonoidHom a : (AE D)ˣ) : AE D) = inc D (t : D.host.E) := by
    rw [← h]; rfl
  refine ⟨h1 ▸ VacMove.inc_int D t, ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact Subtype.ext h1.symm

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Establish `h3` using `Ideal.mem_map_of_mem (intInc D) hq`. Rewrite `h3` using `[h2, map_natCast]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h3`. Establish `ha1 : (a : AE D) * y = q` using `by simpa using congrArg Subtype.val ha`.

Rewrite using `[← ha1, Units.mul_inv_cancel_right]`. Conclude with `a.2`.
-/
theorem Gen.inv_mul {B : Ideal (𝓞 D.host.E)} {y : (AE D)ˣ} (hy : Gen D B y) {q : ℕ}
    (hq : (q : 𝓞 D.host.E) ∈ B) : (q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D := by
  obtain ⟨h1, h2⟩ := hy
  have h3 := Ideal.mem_map_of_mem (intInc D) hq
  rw [h2, map_natCast] at h3
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h3
  have ha1 : (a : AE D) * y = q := by simpa using congrArg Subtype.val ha
  rw [← ha1, Units.mul_inv_cancel_right]; exact a.2

/- English proof (translation)
Take `⟨m, hm, hmx⟩` from `GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)`. Set `z : OhE D` to `⟨_, hx⟩`. Set `I : Ideal (𝓞 D.host.E)` to `(Ideal.span {z}).comap (intInc D)`. Establish `hMz : (m : OhE D) ∈ Ideal.span {z}`. Use `Ideal.mem_span_singleton'.2 ⟨⟨_, hmx⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show (m : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) * x = ((m : OhE D) : AE D)`. Rewrite using `[Units.inv_mul_cancel_right]`. Simplify using the standard rewrite rules. Establish `hMI : (m : 𝓞 D.host.E) ∈ I` using `by show intInc D _ ∈ Ideal.span {z}`. Rewrite using `[map_natCast]` and apply the resulting hypothesis.

Use `⟨I, fun h0 => ?_, hx, le_antisymm Ideal.map_comap_le ?_⟩` and prove the remaining obligations. Rewrite `hMI` using `[h0, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 hm.ne') hMI`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Take `⟨r, hr, w, hw, e⟩` from `GlobalTheory.HeckeVal.exists_approx D m hm _ hx`.

Establish `e' : z = intInc D ⟨r, hr⟩ + (m : OhE D) * ⟨w, hw⟩` using `Subtype.ext (by show (x : AE D) = inc D r + ((m : OhE D) : AE D) * w`. Rewrite using `[e]`. Use the proof step `simp)`. Establish `hrI : (⟨r, hr⟩ : 𝓞 D.host.E) ∈ I` using `by show intInc D _ ∈ Ideal.span {z}`. Rewrite using `[show intInc D ⟨r, hr⟩ = z - (m : OhE D) * ⟨w, hw⟩ by rw [e']; ring]`.

Conclude with `sub_mem (Ideal.mem_span_singleton_self z) (Ideal.mul_mem_right _ _ hMz)`. Express the relevant statement in the definitionally equal form `z ∈ _`. Rewrite using `[e']`. Use `add_mem (Ideal.mem_map_of_mem _ hrI) (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations. Use `Ideal.mem_map_of_mem (intInc D) hMI` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_ideal_gen (x : (AE D)ˣ) (hx : (x : AE D) ∈ OhE D) : ∃ B, B ≠ ⊥ ∧ Gen D B x := by
  obtain ⟨m, hm, hmx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  let z : OhE D := ⟨_, hx⟩
  let I : Ideal (𝓞 D.host.E) := (Ideal.span {z}).comap (intInc D)
  have hMz : (m : OhE D) ∈ Ideal.span {z} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hmx⟩, Subtype.ext ?_⟩
    show (m : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) * x = ((m : OhE D) : AE D)
    rw [Units.inv_mul_cancel_right]; simp
  have hMI : (m : 𝓞 D.host.E) ∈ I := by
    show intInc D _ ∈ Ideal.span {z}
    rwa [map_natCast]
  refine ⟨I, fun h0 => ?_, hx, le_antisymm Ideal.map_comap_le ?_⟩
  · rw [h0, Ideal.mem_bot] at hMI
    exact (Nat.cast_ne_zero.2 hm.ne') hMI
  rw [Ideal.span_singleton_le_iff_mem]
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D m hm _ hx
  have e' : z = intInc D ⟨r, hr⟩ + (m : OhE D) * ⟨w, hw⟩ := Subtype.ext (by
    show (x : AE D) = inc D r + ((m : OhE D) : AE D) * w
    rw [e]; simp)
  have hrI : (⟨r, hr⟩ : 𝓞 D.host.E) ∈ I := by
    show intInc D _ ∈ Ideal.span {z}
    rw [show intInc D ⟨r, hr⟩ = z - (m : OhE D) * ⟨w, hw⟩ by rw [e']; ring]
    exact sub_mem (Ideal.mem_span_singleton_self z) (Ideal.mul_mem_right _ _ hMz)
  change z ∈ _
  rw [e']
  refine add_mem (Ideal.mem_map_of_mem _ hrI) (Ideal.mul_mem_right _ _ ?_)
  have := Ideal.mem_map_of_mem (intInc D) hMI
  rwa [map_natCast] at this

/- English proof (translation)
Establish `h` using `χ.aut a`. Rewrite `h` using `[Finset.prod_eq_one, mul_one]`. Conclude with `Units.ext h`. Introduce `τ _`. Establish `h1 : Even (χ.n τ)`.

Use `(χ.par τ).add (Int.even_coe_nat N |>.2 hN)` as an intermediate fact. Simplify using `using this`. Take `⟨c, hc⟩` from `h1`. Establish `h2 : embT D τ (D.host.conj a) = starRingEnd ℂ (embT D τ a)` using `D.host.conjE_apply (embT D τ) a`. Rewrite `h2` using `[ha]`.

Establish `h0 : embT D τ (a : D.host.E) ≠ 0` using `(map_ne_zero _).2 a.ne_zero`. Rewrite using `[hc, ← two_mul, zpow_mul, zpow_two, ← pow_two, div_pow, ← Complex.mul_conj', ← h2, pow_two, div_self (mul_ne_zero h0 h0), one_zpow]`.
-/
theorem eq_one_of_real {N : ℕ} (hN : Even N) (χ : HeckeU D N) (a : D.host.Eˣ)
    (ha : D.host.conj (a : D.host.E) = a) : χ.f (Units.map (inc D).toMonoidHom a) = 1 := by
  have h := χ.aut a
  rw [Finset.prod_eq_one, mul_one] at h
  · exact Units.ext h
  intro τ _
  have h1 : Even (χ.n τ) := by
    have := (χ.par τ).add (Int.even_coe_nat N |>.2 hN)
    simpa using this
  obtain ⟨c, hc⟩ := h1
  have h2 : embT D τ (D.host.conj a) = starRingEnd ℂ (embT D τ a) :=
    D.host.conjE_apply (embT D τ) a
  rw [ha] at h2
  have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  rw [hc, ← two_mul, zpow_mul, zpow_two, ← pow_two, div_pow, ← Complex.mul_conj', ← h2, pow_two,
    div_self (mul_ne_zero h0 h0), one_zpow]

/- English proof (translation)
Establish `huniq : ∀ {B y z}, Gen D B y → Gen D B z → ψ y = ψ z` using `fun hy hz => by`. Use `h1 _ (hy.intU hz)` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis. Establish `hprime : ∀ P : Ideal (𝓞 D.host.E), Prime P → ∀ y, Gen D P y → ψ y = 1`. Introduce `P hP y hy`.

Establish `hP0 : P ≠ ⊥` using `hP.ne_zero`. Establish `hPp : P.IsPrime` using `Ideal.isPrime_of_prime hP`. Take `⟨q, hq, hqP⟩ : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P` from `exists_prime_mem P hPp _ (by simpa [Ideal.absNorm_eq_zero_iff] using hP0) (Ideal.absNorm_mem P)`. Distinguish the cases in `hi : InertQ D q`. Take `⟨t, B, ht0, htc, e⟩` from `GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P hPp hP0 (hi P hPp hP0 hqP)`.

Establish `hB : B ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `ht0 (by simpa using e)`. Take `⟨z, hz⟩` from `exists_gen D B hB`. Establish `htE : (t : D.host.E) ≠ 0` using `by simpa using ht0`.

Establish `g1` using `gen_span t (Units.mk0 _ htE) rfl`. Establish `g2` using `(hy.mul hz).mul hz.conj`. Rewrite `g2` using `[← e]`. Use `huniq g1 g2` as an intermediate fact. Rewrite `this` using `[h3 _ htc, mul_assoc, map_mul, h2, mul_one]`.

Conclude with `this.symm`. Conclude with `h4 q y hq hi hy.1 (hy.inv_mul hqP)`. Establish `hall : ∀ B : Ideal (𝓞 D.host.E), B ≠ ⊥ → ∀ y, Gen D B y → ψ y = 1`. Introduce `B`. Proceed by induction on `B using UniqueFactorizationMonoid.induction_on_prime with`.

Consider the case `h₁ => intro h`. Conclude with `absurd rfl h`. Consider the case `h₂ B hB`. Introduce `_ y hy`. Rewrite `hy` using `[Ideal.isUnit_iff.1 hB]`.

Use `h1 y ⟨hy.1, ?_⟩` and prove the remaining obligations. Simplify using `using hy.inv_mul (q := 1) Submodule.mem_top`. Consider the case `h₃ C P hC hP ih`. Introduce `_ y hy`. Take `⟨a, ha⟩` from `exists_gen D P hP.ne_zero`.

Take `⟨c, hc⟩` from `exists_gen D C hC`. Rewrite using `[huniq hy (ha.mul hc), map_mul, hprime P hP a ha, ih hC c hc, one_mul]`. Take `⟨n, hn, hnx⟩` from `GlobalTheory.HeckeVal.exists_denom D (x : AE D)`. Set `a : D.host.Eˣ` to `Units.mk0 (n : D.host.E) (Nat.cast_ne_zero.2 hn.ne')`. Establish `hmem : ((Units.map (inc D).toMonoidHom a * x : (AE D)ˣ) : AE D) ∈ OhE D`.

Express the relevant statement in the definitionally equal form `inc D (n : D.host.E) * (x : AE D) ∈ OhE D`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Take `⟨B, hB, hg⟩` from `exists_ideal_gen _ hmem`. Use `hall B hB _ hg` as an intermediate fact. Rewrite `this` using `[map_mul, h3 a (map_natCast D.host.conj n), one_mul]`. Then use the resulting hypothesis.
-/
theorem hom_eq_one {G : Type} [CommGroup G] (ψ : (AE D)ˣ →* G) (h1 : ∀ u, IntU D u → ψ u = 1)
    (h2 : ∀ y, ψ (y * sgU D y) = 1)
    (h3 : ∀ a : D.host.Eˣ, D.host.conj (a : D.host.E) = a → ψ (Units.map (inc D).toMonoidHom a) = 1)
    (h4 : ∀ (q : ℕ) (y : (AE D)ˣ), q.Prime → ¬ InertQ D q → (y : AE D) ∈ OhE D →
      (q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → ψ y = 1) (x : (AE D)ˣ) : ψ x = 1 := by
  have huniq : ∀ {B y z}, Gen D B y → Gen D B z → ψ y = ψ z := fun hy hz => by
    have := h1 _ (hy.intU hz)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have hprime : ∀ P : Ideal (𝓞 D.host.E), Prime P → ∀ y, Gen D P y → ψ y = 1 := by
    intro P hP y hy
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
    obtain ⟨q, hq, hqP⟩ : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P :=
      exists_prime_mem P hPp _ (by simpa [Ideal.absNorm_eq_zero_iff] using hP0) (Ideal.absNorm_mem P)
    by_cases hi : InertQ D q
    · obtain ⟨t, B, ht0, htc, e⟩ := GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P hPp hP0 (hi P hPp hP0 hqP)
      have hB : B ≠ ⊥ := by
        rintro rfl
        exact ht0 (by simpa using e)
      obtain ⟨z, hz⟩ := exists_gen D B hB
      have htE : (t : D.host.E) ≠ 0 := by simpa using ht0
      have g1 := gen_span t (Units.mk0 _ htE) rfl
      have g2 := (hy.mul hz).mul hz.conj
      rw [← e] at g2
      have := huniq g1 g2
      rw [h3 _ htc, mul_assoc, map_mul, h2, mul_one] at this
      exact this.symm
    · exact h4 q y hq hi hy.1 (hy.inv_mul hqP)
  have hall : ∀ B : Ideal (𝓞 D.host.E), B ≠ ⊥ → ∀ y, Gen D B y → ψ y = 1 := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB =>
      intro _ y hy
      rw [Ideal.isUnit_iff.1 hB] at hy
      refine h1 y ⟨hy.1, ?_⟩
      simpa using hy.inv_mul (q := 1) Submodule.mem_top
    | h₃ C P hC hP ih =>
      intro _ y hy
      obtain ⟨a, ha⟩ := exists_gen D P hP.ne_zero
      obtain ⟨c, hc⟩ := exists_gen D C hC
      rw [huniq hy (ha.mul hc), map_mul, hprime P hP a ha, ih hC c hc, one_mul]
  obtain ⟨n, hn, hnx⟩ := GlobalTheory.HeckeVal.exists_denom D (x : AE D)
  let a : D.host.Eˣ := Units.mk0 (n : D.host.E) (Nat.cast_ne_zero.2 hn.ne')
  have hmem : ((Units.map (inc D).toMonoidHom a * x : (AE D)ˣ) : AE D) ∈ OhE D := by
    change inc D (n : D.host.E) * (x : AE D) ∈ OhE D
    rwa [map_natCast]
  obtain ⟨B, hB, hg⟩ := exists_ideal_gen _ hmem
  have := hall B hB _ hg
  rwa [map_mul, h3 a (map_natCast D.host.conj n), one_mul] at this

/- English proof (translation)
Introduce `D N hN χ x hx`. Take `⟨hinv, ε, hε, h1, h2, h3⟩` from `GlobalTheory.NormSum.HalfIdempotent.conj_involutive_and_exists_half_idempotent D`. Establish `h1' : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, h1]`. Establish `he : (1 - (ε + sgA D ε)) * (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε)`. Take the linear combination `h1 + h1' + 2 * h2`.

Establish `heO : 1 - (ε + sgA D ε) ∈ OhE D` using `sub_mem (one_mem _) (add_mem hε (VacMove.sgA_mem D hε))`. Establish `hse : sgA D (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε)`. Rewrite using `[map_sub, map_add, map_one, hinv, add_comm]`. Establish `hunr : ∀ y : (AE D)ˣ, (y : AE D) ∈ OhE D → (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → χ.f (proj _ he y) = 1`. Introduce `y hy hy'`.

Use `χ.unr _ ⟨?_, ?_⟩ fun q hq hi => ?_` and prove the remaining obligations. Rewrite using `[proj_val]`. Conclude with `add_mem (mul_mem heO hy) (sub_mem (one_mem _) heO)`. Rewrite using `[proj_inv]`. Conclude with `add_mem hy' (sub_mem (one_mem _) heO)`.

Use `VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((y : AE D) - 1) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[proj_val]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `hom_eq_one (χ.f.comp (proj _ he)) (fun u hu => hunr u hu.1 (mul_mem heO hu.2)) (fun y => ?_) (fun a ha => ?_) (fun q y hq hi hy hy' => hunr y hy ?_) x`. Establish `h0 : (ε + sgA D ε) * ((x : AE D) - 1) = 0`.

Use `(GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _ (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : InertQ D q`. Conclude with `VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _`. Rewrite using `[mul_comm]`. Conclude with `VacMove.zeroAt_mul D hq (hx q hq hi) _`.

Establish `: proj _ he x = x` using `by ext; rw [proj_val]; linear_combination -h0`. Rewrite `key` using `[MonoidHom.comp_apply, this]`. Then use the resulting hypothesis. Establish `: proj _ he (sgU D y) = sgU D (proj _ he y)`. Use `ext`. Express the relevant statement in the definitionally equal form `_ * sgA D y + _ = sgA D (_ * y + _)`.

Rewrite using `[map_add, map_mul, hse, map_sub, map_one, hse]`. Rewrite using `[MonoidHom.comp_apply, map_mul, this, χ.norm]`. Establish `h4` using `eq_one_of_real hN χ a ha set t := Units.map (inc D).toMonoidHom a with ht`. Establish `hst : sgA D (t : AE D) = t`. Express the relevant statement in the definitionally equal form `sgA D (inc D a) = inc D a`.

Rewrite using `[GlobalTheory.NormSum.PtsMem.sgA_inc, ha]`. Establish `: t = proj _ he t * (proj ε h1 t * sgU D (proj ε h1 t))`. Use `ext`. Express the relevant statement in the definitionally equal form `(t : AE D) = (_ * t + _) * ((ε * t + _) * sgA D (ε * t + _))`. Rewrite using `[map_add, map_mul, map_sub, map_one, hst]`.

Take the linear combination `((t : AE D) - 1) ^ 2 * he - ((t : AE D) - 1) ^ 2 * (1 + (1 - (ε + sgA D ε)) * (t - 1)) * h2`. Rewrite `h4` using `[this, map_mul, χ.norm, mul_one]`. Conclude with `h4`. Take `⟨m, -, hm, s, hs, e⟩` from `(h3 q hq).2 hi 1`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hm`.

Establish `hab'` using `congrArg (Int.cast : ℤ → AE D) hab`. Move the coercions through the operations in `at hab'`. Rewrite using `[show (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) = (a * s + b * (1 - (ε + sgA D ε))) * ((q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D)) by`. Take the linear combination `(-(1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D)) * hab' + a * ((y⁻¹ : (AE D)ˣ) : AE D) * e]`. Conclude with `mul_mem (add_mem (mul_mem (intCast_mem _ _) hs) (mul_mem (intCast_mem _ _) heO)) hy'`.
-/
theorem character_trivial_at_inert : ∀ (D : D7) (N : ℕ), Even N → ∀ (χ : HeckeU D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((x : AE D) - 1)) → χ.f x = 1 := by
  intro D N hN χ x hx
  obtain ⟨hinv, ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.HalfIdempotent.conj_involutive_and_exists_half_idempotent D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have he : (1 - (ε + sgA D ε)) * (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    linear_combination h1 + h1' + 2 * h2
  have heO : 1 - (ε + sgA D ε) ∈ OhE D := sub_mem (one_mem _) (add_mem hε (VacMove.sgA_mem D hε))
  have hse : sgA D (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    rw [map_sub, map_add, map_one, hinv, add_comm]
  have hunr : ∀ y : (AE D)ˣ, (y : AE D) ∈ OhE D →
      (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → χ.f (proj _ he y) = 1 := by
    intro y hy hy'
    refine χ.unr _ ⟨?_, ?_⟩ fun q hq hi => ?_
    · rw [proj_val]; exact add_mem (mul_mem heO hy) (sub_mem (one_mem _) heO)
    · rw [proj_inv]; exact add_mem hy' (sub_mem (one_mem _) heO)
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((y : AE D) - 1) using 1
      rw [proj_val]; ring
  have key := hom_eq_one (χ.f.comp (proj _ he)) (fun u hu => hunr u hu.1 (mul_mem heO hu.2))
    (fun y => ?_) (fun a ha => ?_) (fun q y hq hi hy hy' => hunr y hy ?_) x
  · have h0 : (ε + sgA D ε) * ((x : AE D) - 1) = 0 := by
      refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _
        (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)
      by_cases hi : InertQ D q
      · exact VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
      · rw [mul_comm]; exact VacMove.zeroAt_mul D hq (hx q hq hi) _
    have : proj _ he x = x := by
      ext; rw [proj_val]; linear_combination -h0
    rwa [MonoidHom.comp_apply, this] at key
  · have : proj _ he (sgU D y) = sgU D (proj _ he y) := by
      ext
      change _ * sgA D y + _ = sgA D (_ * y + _)
      rw [map_add, map_mul, hse, map_sub, map_one, hse]
    rw [MonoidHom.comp_apply, map_mul, this, χ.norm]
  · have h4 := eq_one_of_real hN χ a ha
    set t := Units.map (inc D).toMonoidHom a with ht
    have hst : sgA D (t : AE D) = t := by
      change sgA D (inc D a) = inc D a
      rw [GlobalTheory.NormSum.PtsMem.sgA_inc, ha]
    have : t = proj _ he t * (proj ε h1 t * sgU D (proj ε h1 t)) := by
      ext
      change (t : AE D) = (_ * t + _) * ((ε * t + _) * sgA D (ε * t + _))
      rw [map_add, map_mul, map_sub, map_one, hst]
      linear_combination ((t : AE D) - 1) ^ 2 * he -
        ((t : AE D) - 1) ^ 2 * (1 + (1 - (ε + sgA D ε)) * (t - 1)) * h2
    rw [this, map_mul, χ.norm, mul_one] at h4
    exact h4
  · obtain ⟨m, -, hm, s, hs, e⟩ := (h3 q hq).2 hi 1
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
    have hab' := congrArg (Int.cast : ℤ → AE D) hab
    push_cast at hab'
    rw [show (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) =
      (a * s + b * (1 - (ε + sgA D ε))) * ((q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D)) by
        linear_combination (-(1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D)) * hab' +
          a * ((y⁻¹ : (AE D)ˣ) : AE D) * e]
    exact mul_mem (add_mem (mul_mem (intCast_mem _ _) hs) (mul_mem (intCast_mem _ _) heO)) hy'

end GlobalTheory.InertTrivial
