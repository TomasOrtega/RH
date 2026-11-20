import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

noncomputable section
open NumberField Matrix

namespace PI.SqPairW

open Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

def lam (L' L'' : Submodule (𝓞 E) (Fin N → E)) : Subring (Matrix (Fin N) (Fin N) E) where
  carrier := {e | (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'')}
  mul_mem' {a b} ha hb := ⟨fun y hy => by rw [← mulVec_mulVec]; exact ha.1 _ (hb.1 y hy),
    fun y hy => by rw [← mulVec_mulVec]; exact ha.2 _ (hb.2 y hy)⟩
  one_mem' := ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  add_mem' {a b} ha hb := ⟨fun y hy => by rw [add_mulVec]; exact L'.add_mem (ha.1 y hy) (hb.1 y hy),
    fun y hy => by rw [add_mulVec]; exact L''.add_mem (ha.2 y hy) (hb.2 y hy)⟩
  zero_mem' := ⟨fun y _ => by simp, fun y _ => by simp⟩
  neg_mem' {a} ha := ⟨fun y hy => by rw [neg_mulVec]; exact L'.neg_mem (ha.1 y hy),
    fun y hy => by rw [neg_mulVec]; exact L''.neg_mem (ha.2 y hy)⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lam {L' L'' : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E} :
    e ∈ lam L' L'' ↔ (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdHG_eq_dot (x y : Fin N → E) : stdHG E N x y = star x ⬝ᵥ y := rfl

/- English proof (translation)
Introduce `y hy`. Use `(hL.2.2 _).2 (fun x hx => ?_)` and prove the remaining obligations. Establish `hy'` using `(hL.2.2 y).1 hy (e *ᵥ x) (he x hx)`. Rewrite `hy'`, the goal using `[stdHG_eq_dot]`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`.

Conclude with `hy'`.
-/
theorem conjTranspose_pres {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDG E N L)
    {e : Matrix (Fin N) (Fin N) E} (he : ∀ y ∈ L, e *ᵥ y ∈ L) : ∀ y ∈ L, eᴴ *ᵥ y ∈ L := by
  intro y hy
  refine (hL.2.2 _).2 (fun x hx => ?_)
  have hy' := (hL.2.2 y).1 hy (e *ᵥ x) (he x hx)
  rw [stdHG_eq_dot] at hy' ⊢
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  exact hy'

/- English proof (translation)
Assemble the required witnesses or components as `⟨conjTranspose_pres hL' he.1, conjTranspose_pres hL'' he.2⟩`.
-/
theorem conjTranspose_mem_lam {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L')
    (hL'' : IsSDG E N L'') {e : Matrix (Fin N) (Fin N) E} (he : e ∈ lam L' L'') :
    eᴴ ∈ lam L' L'' := ⟨conjTranspose_pres hL' he.1, conjTranspose_pres hL'' he.2⟩

def mset (e : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)}

/- English proof (translation)
Establish `h1e : 1 - e ∈ R` using `R.sub_mem R.one_mem he`. Introduce and unpack `M (rfl | rfl | rfl)`. Conclude with `R.sub_mem (R.mul_mem he he) he`. Conclude with `R.mul_mem (hstar e he) he`. Conclude with `R.mul_mem (hstar _ h1e) h1e`.
-/
theorem mset_sub {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {e : Matrix (Fin N) (Fin N) E} (he : e ∈ R) : ∀ M ∈ mset e, M ∈ R := by
  have h1e : 1 - e ∈ R := R.sub_mem R.one_mem he
  rintro M (rfl | rfl | rfl)
  · exact R.sub_mem (R.mul_mem he he) he
  · exact R.mul_mem (hstar e he) he
  · exact R.mul_mem (hstar _ h1e) h1e

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_zsmul]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem star_cong (b d : Matrix (Fin N) (Fin N) E) (P : ℤ) :
    (b + P • d)ᴴ * (b + P • d) = bᴴ * b + P • (bᴴ * d + dᴴ * b + P • (dᴴ * d)) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_zsmul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel

/- English proof (translation)
Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem sq_cong (b d : Matrix (Fin N) (Fin N) E) (P : ℤ) :
    (b + P • d) * (b + P • d) - (b + P • d) = (b * b - b) + P • (b * d + d * b + P • (d * d) - d) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub,
    smul_smul]
  abel

/- English proof (translation)
Introduce and unpack `M (rfl | rfl | rfl)`. Use `⟨a * a - a, Or.inl rfl, a * d + d * a + P • (d * d) - d, ?_, sq_cong a d P⟩` and prove the remaining obligations. Conclude with `R.sub_mem (R.add_mem (R.add_mem (R.mul_mem ha hd) (R.mul_mem hd ha)) (zsmul_mem (R.mul_mem hd hd) P)) hd`. Use `⟨aᴴ * a, Or.inr (Or.inl rfl), aᴴ * d + dᴴ * a + P • (dᴴ * d), ?_, star_cong a d P⟩` and prove the remaining obligations. Conclude with `R.add_mem (R.add_mem (R.mul_mem (hstar a ha) hd) (R.mul_mem (hstar d hd) ha)) (zsmul_mem (R.mul_mem (hstar d hd) hd) P)`.

Establish `e1 : 1 - (a + P • d) = (1 - a) + P • (-d)`. Rewrite using `[smul_neg]`. Normalize the expressions using the abelian group laws. Establish `h1a : 1 - a ∈ R` using `R.sub_mem R.one_mem ha`. Establish `hnd : -d ∈ R` using `R.neg_mem hd`.

Use `⟨(1 - a)ᴴ * (1 - a), Or.inr (Or.inr rfl), (1 - a)ᴴ * (-d) + (-d)ᴴ * (1 - a) + P • ((-d)ᴴ * (-d)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `R.add_mem (R.add_mem (R.mul_mem (hstar _ h1a) hnd) (R.mul_mem (hstar _ hnd) h1a)) (zsmul_mem (R.mul_mem (hstar _ hnd) hnd) P)`. Rewrite using `[e1]`. Conclude with `star_cong (1 - a) (-d) P`.
-/
theorem mset_cong {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {a d : Matrix (Fin N) (Fin N) E} (ha : a ∈ R) (hd : d ∈ R) (P : ℤ) :
    ∀ M ∈ mset (a + P • d), ∃ M' ∈ mset a, ∃ r ∈ R, M = M' + P • r := by
  rintro M (rfl | rfl | rfl)
  · refine ⟨a * a - a, Or.inl rfl, a * d + d * a + P • (d * d) - d, ?_, sq_cong a d P⟩
    exact R.sub_mem (R.add_mem (R.add_mem (R.mul_mem ha hd) (R.mul_mem hd ha))
      (zsmul_mem (R.mul_mem hd hd) P)) hd
  · refine ⟨aᴴ * a, Or.inr (Or.inl rfl), aᴴ * d + dᴴ * a + P • (dᴴ * d), ?_, star_cong a d P⟩
    exact R.add_mem (R.add_mem (R.mul_mem (hstar a ha) hd) (R.mul_mem (hstar d hd) ha))
      (zsmul_mem (R.mul_mem (hstar d hd) hd) P)
  · have e1 : 1 - (a + P • d) = (1 - a) + P • (-d) := by
      rw [smul_neg]
      abel
    have h1a : 1 - a ∈ R := R.sub_mem R.one_mem ha
    have hnd : -d ∈ R := R.neg_mem hd
    refine ⟨(1 - a)ᴴ * (1 - a), Or.inr (Or.inr rfl),
      (1 - a)ᴴ * (-d) + (-d)ᴴ * (1 - a) + P • ((-d)ᴴ * (-d)), ?_, ?_⟩
    · exact R.add_mem (R.add_mem (R.mul_mem (hstar _ h1a) hnd) (R.mul_mem (hstar _ hnd) h1a))
        (zsmul_mem (R.mul_mem (hstar _ hnd) hnd) P)
    · rw [e1]
      exact star_cong (1 - a) (-d) P

def yg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) : AddSubgroup (Fin N → E) where
  carrier := {x | ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m}
  add_mem' := by
    rintro _ _ ⟨m1, h1, h1', rfl⟩ ⟨m2, h2, h2', rfl⟩
    exact ⟨m1 + m2, L'.add_mem h1 h2, L''.add_mem h1' h2', (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, L'.zero_mem, L''.zero_mem, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨m, h, h', rfl⟩
    exact ⟨-m, L'.neg_mem h, L''.neg_mem h', (smul_neg _ _).symm⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_yg {L' L'' : Submodule (𝓞 E) (Fin N → E)} {n : 𝓞 E} {x : Fin N → E} :
    x ∈ yg L' L'' n ↔ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m := Iff.rfl

/- English proof (translation)
Set `I : Ideal ℤ` to `{ carrier := {t | t • x ∈ Y} add_mem' := fun {a b} ha hb => by show (a + b) • x ∈ Y`. Rewrite using `[add_smul]`. Conclude with `Y.add_mem ha hb`. Use the proof step `zero_mem' := by show (0 : ℤ) • x ∈ Y`. Rewrite using `[zero_smul]`.

Conclude with `Y.zero_mem`. Use the proof step `smul_mem' := fun c {t} ht => by show (c • t) • x ∈ Y`. Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Y.zsmul_mem ht c }`. Take `⟨n, hn⟩` from `(IsPrincipalIdealRing.principal I).principal`.

Establish `hmem : ∀ t : ℤ, t • x ∈ Y ↔ n ∣ t`. Introduce `t`. Establish `e : t ∈ I ↔ t ∈ Submodule.span ℤ {n}` using `by rw [hn]`. Conclude with `e.trans Ideal.mem_span_singleton`. Establish `h1 : n ∣ 1`.

Assume the negation of the conclusion as `hn1`. Establish `hna : n.natAbs ≠ 1`. Introduce `e`. Apply `hn1` to reduce the goal to its premises. Rewrite using `[← Int.natAbs_dvd, e]`.

Conclude with `one_dvd _`. Establish `hp` using `Nat.minFac_prime hna`. Take `⟨t, ht, htY⟩` from `h _ hp`. Apply `ht` to reduce the goal to its premises. Establish `hpn : ((n.natAbs.minFac : ℕ) : ℤ) ∣ n` using `Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)`.

Conclude with `hpn.trans ((hmem t).1 htY)`. Use `(hmem 1).2 h1` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_of_local {V : Type*} [AddCommGroup V] (Y : AddSubgroup V) (x : V)
    (h : ∀ p : ℕ, p.Prime → ∃ t : ℤ, ¬ (p : ℤ) ∣ t ∧ t • x ∈ Y) : x ∈ Y := by
  classical
  let I : Ideal ℤ :=
    { carrier := {t | t • x ∈ Y}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • x ∈ Y
        rw [add_smul]
        exact Y.add_mem ha hb
      zero_mem' := by
        show (0 : ℤ) • x ∈ Y
        rw [zero_smul]
        exact Y.zero_mem
      smul_mem' := fun c {t} ht => by
        show (c • t) • x ∈ Y
        rw [smul_eq_mul, mul_smul]
        exact Y.zsmul_mem ht c }
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ t : ℤ, t • x ∈ Y ↔ n ∣ t := by
    intro t
    have e : t ∈ I ↔ t ∈ Submodule.span ℤ {n} := by rw [hn]
    exact e.trans Ideal.mem_span_singleton
  have h1 : n ∣ 1 := by
    by_contra hn1
    have hna : n.natAbs ≠ 1 := by
      intro e
      apply hn1
      rw [← Int.natAbs_dvd, e]
      exact one_dvd _
    have hp := Nat.minFac_prime hna
    obtain ⟨t, ht, htY⟩ := h _ hp
    apply ht
    have hpn : ((n.natAbs.minFac : ℕ) : ℤ) ∣ n := Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
    exact hpn.trans ((hmem t).1 htY)
  have := (hmem 1).2 h1
  rwa [one_smul] at this

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ c`. Rewrite using `[IsFractionRing.isAlgebraic_iff ℤ ℚ E]`. Conclude with `Algebra.IsAlgebraic.isAlgebraic c`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Take `⟨β, hβ⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint`.

Establish `e1 : algebraMap (𝓞 E) E β = (y : E) * c` using `by rw [hβ, zsmul_eq_mul]`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq y with h | h` into its components or cases. Use `⟨β, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E β = _`.

Establish `hk : (y : E) = ((y.natAbs : ℤ) : E)` using `by exact_mod_cast h`. Rewrite using `[e1, hk, Int.cast_natCast]`. Use `⟨-β, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (-β) = _`. Establish `hk : (y : E) = -((y.natAbs : ℤ) : E)` using `by exact_mod_cast h`.

Rewrite using `[map_neg, e1, hk, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_mul_int (c : E) : ∃ k : ℕ, 0 < k ∧ ∃ β : 𝓞 E, (β : E) = (k : E) * c := by
  have halg : IsAlgebraic ℤ c := by
    rw [IsFractionRing.isAlgebraic_iff ℤ ℚ E]
    exact Algebra.IsAlgebraic.isAlgebraic c
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨β, hβ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  have e1 : algebraMap (𝓞 E) E β = (y : E) * c := by rw [hβ, zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · refine ⟨β, ?_⟩
    change algebraMap (𝓞 E) E β = _
    have hk : (y : E) = ((y.natAbs : ℤ) : E) := by exact_mod_cast h
    rw [e1, hk, Int.cast_natCast]
  · refine ⟨-β, ?_⟩
    change algebraMap (𝓞 E) E (-β) = _
    have hk : (y : E) = -((y.natAbs : ℤ) : E) := by exact_mod_cast h
    rw [map_neg, e1, hk, Int.cast_natCast]
    ring

end PI.SqPairW
