import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

/- English proof (translation)
Establish `h` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) (k : 𝓞 E)`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Simplify using `using h`.
-/
theorem natCast_adicCompletion_v_le_one {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) : Valued.v ((k : Q.adicCompletion E)) ≤ 1 := by
  have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) (k : 𝓞 E)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  simpa using h

/- English proof (translation)
Take `⟨b, hb, hbx⟩` from `HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x`. Rewrite `hbx` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `set N := Ideal.absNorm (Ideal.span {b}) with hNdef`. Establish `hN0 : N ≠ 0`.

Rewrite using `[hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`. Establish `hmem : (N : 𝓞 E) ∈ Ideal.span {b}` using `Ideal.absNorm_mem _`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `⟨N / p ^ N.factorization p, (Nat.coprime_ordCompl hp hN0).symm, ?_⟩` and prove the remaining obligations.

Establish `hsplit` using `Nat.ordProj_mul_ordCompl_eq_self N p`. Establish `hvp : Valued.v ((p : Q.adicCompletion E)) = 1`. Establish `h1` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (p : 𝓞 E)`. Establish `h2 : Q.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hpQ`. Simplify using `only [map_natCast] at h1 h2`.

Rewrite using `[h1, h2]`. Establish `hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1`. Establish `e : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) * (algebraMap (𝓞 E) (Q.adicCompletion E) b)`. Rewrite using `[← map_mul, hc, map_natCast]`. Rewrite using `[e, mul_assoc, Valuation.map_mul, mul_comm _ x]`.

Use `mul_le_one' ?_ hbx` and prove the remaining obligations. Establish `h` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis. Rewrite `hNx` using `[← hsplit]`. Move the coercions through the operations in `at hNx`.

Rewrite `hNx` using `[mul_assoc, Valuation.map_mul, map_pow, hvp, one_pow, one_mul]`. Conclude with `hNx` after adjusting the coercions.
-/
theorem exists_coprime_natCast_mul_v_le_one {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∉ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨N / p ^ N.factorization p, (Nat.coprime_ordCompl hp hN0).symm, ?_⟩
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self N p
  have hvp : Valued.v ((p : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (p : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hpQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e, mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  rw [← hsplit] at hNx
  push_cast at hNx
  rw [mul_assoc, Valuation.map_mul, map_pow, hvp, one_pow, one_mul] at hNx
  exact_mod_cast hNx

end GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

/- English proof (translation)
Set `f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ` to `fun t => if h : t.1 ∈ S then Classical.choose (hin t.1 h t.2.1 t.2.2) else 1`. Establish `hf : ∀ t, (f t).Coprime p`. Introduce `t`. Distinguish the cases in `h : t.1 ∈ S`. Simplify using `only [f, dif_pos h]`.

Conclude with `(Classical.choose_spec (hin t.1 h t.2.1 t.2.2)).1`. Simplify using `only [f, dif_neg h]`. Conclude with `Nat.coprime_one_left p`. Set `T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n)` to `hS.toFinset ×ˢ Finset.univ`. Use `⟨∏ t ∈ T, f t, Nat.Coprime.prod_left fun t _ => hf t, fun i j Q => ?_⟩` and prove the remaining obligations.

Set `ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E` to `RestrictedProduct.evalRingHom _ Q`. Establish `hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x` using `fun _ => rfl`. Rewrite using `[hev, map_mul, map_natCast, ← hev]`. Distinguish the cases in `hQ : Q ∈ S`. Establish `hmem : (Q, i, j) ∈ T` using `by simp [T, hQ]`.

Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem f hmem`. Rewrite using `[hk, Nat.cast_mul, mul_comm ((f (Q, i, j) : ℕ) : Q.adicCompletion E), mul_assoc, Valuation.map_mul]`. Use `mul_le_one' (natCast_adicCompletion_v_le_one Q k) ?_` and prove the remaining obligations. Use `(Classical.choose_spec (hin Q hQ i j)).2` as an intermediate fact. Simplify `this` using `only [f, dif_pos hQ]`.

Rewrite using `[Valuation.map_mul]`. Conclude with `mul_le_one' (natCast_adicCompletion_v_le_one Q _) (hout Q hQ i j)`.
-/
theorem bnd_of_local {E : Type} [Field E] [NumberField E] (p : ℕ) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : S.Finite)
    (hin : ∀ Q ∈ S, ∀ i j, ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * (A i j) Q) ≤ 1)
    (hout : ∀ Q ∉ S, ∀ i j, Valued.v ((A i j) Q) ≤ 1) : Bnd p A := by
  classical
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : t.1 ∈ S then Classical.choose (hin t.1 h t.2.1 t.2.2) else 1
  have hf : ∀ t, (f t).Coprime p := by
    intro t
    by_cases h : t.1 ∈ S
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (hin t.1 h t.2.1 t.2.2)).1
    · simp only [f, dif_neg h]; exact Nat.coprime_one_left p
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hS.toFinset ×ˢ Finset.univ
  refine ⟨∏ t ∈ T, f t, Nat.Coprime.prod_left fun t _ => hf t, fun i j Q => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  by_cases hQ : Q ∈ S
  · have hmem : (Q, i, j) ∈ T := by simp [T, hQ]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hmem
    rw [hk, Nat.cast_mul, mul_comm ((f (Q, i, j) : ℕ) : Q.adicCompletion E), mul_assoc,
      Valuation.map_mul]
    refine mul_le_one' (natCast_adicCompletion_v_le_one Q k) ?_
    have := (Classical.choose_spec (hin Q hQ i j)).2
    simpa only [f, dif_pos hQ] using this
  · rw [Valuation.map_mul]
    exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) (hout Q hQ i j)

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `natCast_adicCompletion_v_le_one Q 1` as an intermediate fact. Simplify using `using this`. Use `natCast_adicCompletion_v_le_one Q 0` as an intermediate fact.

Simplify using `using this`.
-/
theorem one_entry_v_le_one {E : Type} [Field E] [NumberField E] (n : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · have := natCast_adicCompletion_v_le_one Q 1
    simpa using this
  · have := natCast_adicCompletion_v_le_one Q 0
    simpa using this

/- English proof (translation)
Set `ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E` to `RestrictedProduct.evalRingHom _ Q`. Establish `hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x` using `fun _ => rfl`. Establish `hone : ∀ i j, ev ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j`. Apply the tactic sequence `intro i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Establish `h1 : ev.mapMatrix G.1 = 1`.

Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, ← hev, hQ, hev, hone]`. Establish `h2 : ev.mapMatrix G.1 * ev.mapMatrix (G⁻¹).1 = 1`. Rewrite using `[← map_mul]`. Establish `: G.1 * (G⁻¹).1 = 1`.

Use `congrArg Units.val (mul_inv_cancel G)` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, map_one]`. Rewrite `h2` using `[h1, one_mul]`. Introduce `i j`.

Rewrite using `[hev, hev, hone]`. Use `congrFun (congrFun h2 i) j` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply]`. Then use the resulting hypothesis.
-/
theorem inv_eq_one_off {E : Type} [Field E] [NumberField E] (n : ℕ)
    (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) :
    ∀ i j, ((G⁻¹).1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have hone : ∀ i j, ev ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by
    intro i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have h1 : ev.mapMatrix G.1 = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hev, hQ, hev, hone]
  have h2 : ev.mapMatrix G.1 * ev.mapMatrix (G⁻¹).1 = 1 := by
    rw [← map_mul]
    have : G.1 * (G⁻¹).1 = 1 := by
      have := congrArg Units.val (mul_inv_cancel G)
      simpa using this
    rw [this, map_one]
  rw [h1, one_mul] at h2
  intro i j
  rw [hev, hev, hone]
  have := congrFun (congrFun h2 i) j
  rwa [RingHom.mapMatrix_apply, Matrix.map_apply] at this

/- English proof (translation)
Introduce `E _ _ p hp n G S hS hpS hG`. Establish `hGi` using `fun Q hQ => inv_eq_one_off n G Q (hG Q hQ)`. Establish `key : ∀ A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E), (∀ Q ∉ S, ∀ i j, (A i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p A`. Introduce `A hA`. Use `bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)` and prove the remaining obligations.

Conclude with `exists_coprime_natCast_mul_v_le_one p hp Q (hpS Q hQ) _`. Rewrite using `[hA Q hQ i j]`. Conclude with `one_entry_v_le_one n Q i j`. Conclude with `⟨key G.1 hG, key (G⁻¹).1 hGi⟩`.
-/
theorem bnd_and_bnd_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  intro E _ _ p hp n G S hS hpS hG
  have hGi := fun Q hQ => inv_eq_one_off n G Q (hG Q hQ)
  have key : ∀ A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
      (∀ Q ∉ S, ∀ i j, (A i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) →
      Bnd p A := by
    intro A hA
    refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
    · exact exists_coprime_natCast_mul_v_le_one p hp Q (hpS Q hQ) _
    · rw [hA Q hQ i j]; exact one_entry_v_le_one n Q i j
  exact ⟨key G.1 hG, key (G⁻¹).1 hGi⟩

end GlobalTheory.StdAtPrime
