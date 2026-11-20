import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.LocalToGlobal.Columns.QthExistsBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAtStatement

noncomputable section

namespace GlobalTheory.FrameAway

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col GlobalTheory.TwU GlobalTheory.TwU.Model
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.integralAt_of_component_zero_under_prime P z h`.
-/
theorem intAtA_of_prV (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) : IntAtA (F := F) P z :=
  GlobalTheory.T.integralAt_of_component_zero_under_prime P z h

/- English proof (translation)
The claim follows from `GlobalTheory.T.integralAt_of_adelic_integralAt P x h`.
-/
theorem intAt_of_intAtA (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAtA (F := F) P (iA F E x)) : IntAt P x :=
  GlobalTheory.T.integralAt_of_adelic_integralAt P x h

/- English proof (translation)
Take `⟨r, s, hs, e⟩` from `h`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, e]`. Conclude with `(Formalism.L2.DIV.toRInt F E r).2`.
-/
theorem intAtA_of_intAt (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAt P x) : IntAtA (F := F) P (iA F E x) := by
  obtain ⟨r, s, hs, e⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [← map_mul, e]
  exact (Formalism.L2.DIV.toRInt F E r).2

/- English proof (translation)
Use `intAtA_mul (intAtA_int (F := F) (P := P) (-1)) h` as an intermediate fact. Simplify using `using this`.
-/
theorem intAtA_neg (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using intAtA_int (F := F) (P := P) 1`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `intAtA_mul ih h`.
-/
theorem intAtA_pow (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact intAtA_mul ih h

/- English proof (translation)
Establish `hq : ((qOf Q : ℕ) : E) ≠ 0`. Establish `: qOf Q ≠ 0` using `fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `this` after adjusting the coercions. Use `set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi`. Use `set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd`.

Establish `hdq : d * qi = 1`. Rewrite using `[hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]`. Establish `hd : IntAtA (F` using `F) Q d := by`. Use `intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)` as an intermediate fact. Simplify `this` using `[hdd]`.

Use `set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm`. Use `set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y₁⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm`. Use `set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hCm`. Use `set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm`. Use `set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh`.

Establish `hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1`. Rewrite using `[hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression. Establish `key : (1 + Am) * (1 + Mh) = (1 + Cm) * (1 + Bm)`. Rewrite using `[hMh', hAm, hBm, hCm, add_sub_cancel, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul, ← Units.val_mul]`.

Use `congr 1`. Rewrite using `[map_mul, map_inv]`. Use `group`. Establish `e1 : Mh = Cm * (1 + Bm) + Bm - Am - Am * Mh`. Establish `e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh` using `by noncomm_ring`.

Rewrite `e0` using `[key]`. Conclude with `e0.trans (by noncomm_ring)`. Establish `hC : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → ∀ i j, prV (E` using `E) v (Cm i j) = 0 := by`. Introduce `v hvv i j`. Establish `h1 : bc (prV (E` using `E) v) (y⁻¹ * y₁) = 1 := by`.

Rewrite using `[map_mul, map_inv, hv v hvv, inv_mul_cancel]`. Establish `h2` using `congrArg (fun g : GL (Fin N) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) i j) h1`. Simplify using `only [Units.val_one] at h2`. Express the relevant statement in the definitionally equal form `prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j) = (1 : Matrix (Fin N) (Fin N) _) i j at h2`. Rewrite using `[hCm, Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hA : ∀ i j, IntAtA (F` using `F) Q (qi * Am i j) := fun i j => h i j`. Establish `hB : ∀ i j, IntAtA (F` using `F) Q (qi * Bm i j) := fun i j => h₁ i j`. Establish `step : ∀ m : ℕ, (∀ i j, IntAtA (F` using `F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by`. Introduce `m hm i j`.

Establish `e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * (Cm * (1 + Bm)) i j) + d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) + -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)))`. Establish `es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Take the linear combination `(d ^ m * qi * Am i l * Mh l j) * hdq`.

Rewrite using `[es]`. Use `conv_lhs => rw [e1]`. Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply (M := Am)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Use `intAtA_add (intAtA_add (intAtA_add ?_ (intAtA_mul (intAtA_pow Q hd m) (hB i j))) (intAtA_neg Q (intAtA_mul (intAtA_pow Q hd m) (hA i j)))) (intAtA_neg Q (intAtA_sum _ _ fun l _ => intAtA_mul (hA i l) (hm l j)))` and prove the remaining obligations. Use `intAtA_of_prV Q _ fun v hvv => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Matrix.mul_apply, map_sum]`. Simplify using `[hC v hvv]`. Establish `desc : ∀ m : ℕ, (∀ i j, IntAtA (F` using `F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro hm i j`. Simplify using `using hm i j`. Consider the case `succ m ih => intro hm`.

Conclude with `ih (step m hm)`. Take `⟨J, hJ⟩` from `qth_bound Q Mm`. Establish `hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ)`. Establish `h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1` using `by rw [pow_one]; exact Ideal.absNorm_mem _`. Use `(Q.intValuation_le_pow_iff_mem _ 1).2 h0` as an intermediate fact.

Rewrite `this` using `[← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Simplify using `using this`. Establish `hbig : ∀ i j, IntAtA (F` using `F) Q (d ^ (J + 1) * (qi * Mh i j)) := by`. Introduce `i j`. Establish `e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j)`.

Rewrite using `[hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]`. Rewrite using `[e]`. Use `intAtA_of_intAt Q _ ((qth_intAt_iff Q _).2 ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Establish `: (J : ℤ) ≤ (n : ℤ) * J` using `by exact_mod_cast Nat.le_mul_of_pos_left J hn`. Rewrite using `[nsmul_eq_mul]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin` using `desc (J + 1) hbig a b`. Use `show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)`. Use `intAt_of_intAtA (F := F) Q _ ?_` and prove the remaining obligations.

Establish `e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b` using `by rw [map_mul, hMh, Matrix.map_apply]`. Rewrite using `[e3]`. Conclude with `hfin`.
-/
theorem frame_core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y₁⁻¹ * ratA F G₁))
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → bc (prV (E := E) v) y₁ = bc (prV (E := E) v) y) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y₁⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hCm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = (1 + Cm) * (1 + Bm) := by
    rw [hMh', hAm, hBm, hCm, add_sub_cancel, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Cm * (1 + Bm) + Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → ∀ i j, prV (E := E) v (Cm i j) = 0 := by
    intro v hvv i j
    have h1 : bc (prV (E := E) v) (y⁻¹ * y₁) = 1 := by
      rw [map_mul, map_inv, hv v hvv, inv_mul_cancel]
    have h2 := congrArg (fun g : GL (Fin N) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) i j) h1
    simp only [Units.val_one] at h2
    change prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j) = (1 : Matrix (Fin N) (Fin N) _) i j at h2
    rw [hCm, Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * (Cm * (1 + Bm)) i j) + d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    refine intAtA_add (intAtA_add (intAtA_add ?_ (intAtA_mul (intAtA_pow Q hd m) (hB i j))) (intAtA_neg Q (intAtA_mul (intAtA_pow Q hd m) (hA i j)))) (intAtA_neg Q (intAtA_sum _ _ fun l _ => intAtA_mul (hA i l) (hm l j)))
    refine intAtA_of_prV Q _ fun v hvv => ?_
    rw [map_mul, map_mul, Matrix.mul_apply, map_sum]
    simp [hC v hvv]
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine intAtA_of_intAt Q _ ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open _root_.Formalism.L2.Ker _root_.Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

/- English proof (translation)
Establish `hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE)`. Use extensionality with `y`. Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨(RingOfIntegers.mapRingEquiv s.iE).symm y, (mem_seamP s P _).1 (by simpa using hy), by simp⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_seamP s P x).2 hx`. Unfold `qOf`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`.

Conclude with `Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hI).symm.toEquiv`.
-/
theorem qOf_seamP (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm y, (mem_seamP s P _).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (mem_seamP s P x).2 hx
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hI).symm.toEquiv

/- English proof (translation)
Take `⟨r, c, hc, e⟩` from `h`. Use `set f := RingOfIntegers.mapRingEquiv s.iE`. Use `⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩` and prove the remaining obligations. Use `(mem_seamP s P (f.symm c)).2 hm` as an intermediate fact. Rewrite `this` using `[show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c]`. Then use the resulting hypothesis.

Apply `s.iE.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Establish `h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w`. Introduce `w`. Establish `h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x)` using `fun x => rfl`.

Rewrite using `[h2, f.apply_symm_apply]`. Rewrite using `[h1, h1, e]`.
-/
theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV GlobalTheory.TwV in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ p p₁ hp hp₁ P hv`. Use `letI := D.host.cmStar`. Establish `hD` using `(t.idx_ok μ).cst_ok.D_pos P`. Use `set k := (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P with hk`. Use `⟨k, (mul_inv_cancel_left _ _).symm, fun s l => ?_⟩` and prove the remaining obligations.

Establish `hf : CongAt (seamP t.seam P.1) ((t.cst μ).D P) ((ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))` using `hp.frame P`. Establish `hf₁ : CongAt (seamP t.seam P.1) ((t.cst μ).D P) ((ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P)))` using `hp₁.frame P`. Establish `hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E` using `D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) = bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by`. Introduce `v hvv`. Establish `e` using `hv v hvv`.

Simplify using `only [map_mul]`. Rewrite using `[e]`. Establish `hc` using `frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ _ hf hf₁ hw l s`. Rewrite `hc` using `[← map_inv, ← map_mul, qOf_seamP, ← hk]`. Use `intAt_of_seamP t.seam P.1 _ ?_` and prove the remaining obligations.

Use `hc using 1` and compare the differences between its conclusion and the goal. Establish `hm` using `congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l`. Establish `hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) j)) = Pi.single s (1 : D.host.E)`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.single_apply, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hm` using `[hs1, Matrix.mulVec_single_one]`. Rewrite using `[map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]`. Distinguish the cases in `h : l = s`. Substitute `h` using the available equality.

Simplify using `[Matrix.col_apply]`. Simplify using `[h, Matrix.col_apply]`.
-/
theorem frame_away : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ p p₁ hp hp₁ P hv
  letI := D.host.cmStar
  have hD := (t.idx_ok μ).cst_ok.D_pos P
  set k := (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P with hk
  refine ⟨k, (mul_inv_cancel_left _ _).symm, fun s l => ?_⟩
  have hf : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P))) :=
    hp.frame P
  have hf₁ : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) :=
    hp₁.frame P
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) →
      bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    intro v hvv
    have e := hv v hvv
    simp only [map_mul]
    rw [e]
  have hc := frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ _ hf hf₁ hw l s
  rw [← map_inv, ← map_mul, qOf_seamP, ← hk] at hc
  refine intAt_of_seamP t.seam P.1 _ ?_
  convert hc using 1
  have hm := congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l
  have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) j)) = Pi.single s (1 : D.host.E) := by
    funext j
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hs1, Matrix.mulVec_single_one] at hm
  rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
  by_cases h : l = s
  · subst h; simp [Matrix.col_apply]
  · simp [h, Matrix.col_apply]

end GlobalTheory.FrameAway
