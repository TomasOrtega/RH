import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.Good

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
open GlobalTheory.HalfCompare (badInt exists_prime_under mem_of_dvd not_mem_of_coprime)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA (Dinv xi_mem_Dinv int_of_xi normCc_mem_AA int_of_mem_b)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
  GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

variable {D : D7}

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h c`. Take `⟨m, hm⟩` from `h (c : D.host.E) ((FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mpr ⟨c, rfl⟩)`. Conclude with `⟨m, by rw [← Algebra.traceForm_apply, ← hm]; rfl⟩`.

Introduce and unpack `h a ha`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mp ha`. Take `⟨m, hm⟩` from `h c`. Conclude with `⟨m, by rw [Algebra.traceForm_apply]; exact hm.symm⟩`.
-/
theorem mem_Dinv {z : D.host.E} : z ∈ Dinv D ↔ ∀ c : 𝓞 D.host.E, ∃ m : ℤ, Algebra.trace ℚ D.host.E (z * c) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0)]
  constructor
  · intro h c
    obtain ⟨m, hm⟩ := h (c : D.host.E) ((FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mpr ⟨c, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm]; rfl⟩
  · rintro h a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mp ha
    obtain ⟨m, hm⟩ := h c
    exact ⟨m, by rw [Algebra.traceForm_apply]; exact hm.symm⟩

/- English proof (translation)
Establish `h2 : incA D c = (1 : AF D.host.F) ⊗ₜ[D.host.F] c` using `rfl`. Rewrite using `[h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul]`. Conclude with `Prod.ext (zero_mul _) rfl`.
-/
theorem trace_inc_pair (c x : D.host.E) (α : Af D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (incA D c * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) =
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E (c * x))) := by
  have h2 : incA D c = (1 : AF D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul]
  exact Prod.ext (zero_mul _) rfl

/- English proof (translation)
Establish `key : ∀ y ∈ intAE D, ∃ z' : AE D, infPart D z' = 0 ∧ finPart D z' = y ∧ ψ (Algebra.trace (AF D.host.F) (AE D) (incA D c * z')) = 1`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, x, rfl⟩` from `hy`.

Use `⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] (x : D.host.E), GlobalTheory.LatVac.infPart_pair _ _, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[trace_inc_pair]`. Use `GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]`. Use `mem_Dinv.1 hc (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a * x)` as an intermediate fact.

Rewrite using `[Algebra.smul_def, mul_left_comm]`. Conclude with `this`. Consider the case `zero => exact ⟨0, RingHom.map_zero _, RingHom.map_zero _, by rw [mul_zero, map_zero, ψ.map_zero_eq_one]⟩`. Consider the case `add y y' _ _ h h'`. Take `⟨z, h1, h2, h3⟩` from `h`.

Take `⟨z', h1', h2', h3'⟩` from `h'`. Conclude with `⟨z + z', by rw [RingHom.map_add, h1, h1', add_zero], by rw [RingHom.map_add, h2, h2'], by rw [mul_add, map_add, ψ.map_add_eq_mul, h3, h3', one_mul]⟩`. Consider the case `neg y _ h`. Take `⟨z, h1, h2, h3⟩` from `h`. Conclude with `⟨-z, by rw [RingHom.map_neg, h1, neg_zero], by rw [RingHom.map_neg, h2], by rw [mul_neg, map_neg, ψ.map_neg_eq_inv, h3, inv_one]⟩`.

Take `⟨z', h1, h2, h3⟩` from `key _ hz`. Establish `: z = z'` using `sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [RingHom.map_sub, h0, h1, sub_self]) (by rw [RingHom.map_sub, h2, sub_self]))`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {c : D.host.E} (hc : c ∈ Dinv D)
    {z : AE D} (h0 : infPart D z = 0) (hz : finPart D z ∈ intAE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D c * z)) = 1 := by
  have key : ∀ y ∈ intAE D, ∃ z' : AE D, infPart D z' = 0 ∧ finPart D z' = y ∧
      ψ (Algebra.trace (AF D.host.F) (AE D) (incA D c * z')) = 1 := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, x, rfl⟩ := hy
      refine ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] (x : D.host.E), GlobalTheory.LatVac.infPart_pair _ _, rfl, ?_⟩
      rw [trace_inc_pair]
      refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα
      rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
      have := mem_Dinv.1 hc (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a * x)
      rw [Algebra.smul_def, mul_left_comm]
      exact this
    | zero => exact ⟨0, RingHom.map_zero _, RingHom.map_zero _, by rw [mul_zero, map_zero, ψ.map_zero_eq_one]⟩
    | add y y' _ _ h h' =>
      obtain ⟨z, h1, h2, h3⟩ := h
      obtain ⟨z', h1', h2', h3'⟩ := h'
      exact ⟨z + z', by rw [RingHom.map_add, h1, h1', add_zero], by rw [RingHom.map_add, h2, h2'],
        by rw [mul_add, map_add, ψ.map_add_eq_mul, h3, h3', one_mul]⟩
    | neg y _ h =>
      obtain ⟨z, h1, h2, h3⟩ := h
      exact ⟨-z, by rw [RingHom.map_neg, h1, neg_zero], by rw [RingHom.map_neg, h2],
        by rw [mul_neg, map_neg, ψ.map_neg_eq_inv, h3, inv_one]⟩
  obtain ⟨z', h1, h2, h3⟩ := key _ hz
  have : z = z' := sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [RingHom.map_sub, h0, h1, sub_self])
    (by rw [RingHom.map_sub, h2, sub_self]))
  rwa [this]

/- English proof (translation)
The claim follows from `congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) ((comp_toAd D).inc c)`.
-/
theorem cpt_incA (Q : Pl D.host.E) (c : D.host.E) :
    cpt (D := D) Q (toEAf D (incA D c)) = algebraMap D.host.E (Kw Q) c :=
  congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) ((comp_toAd D).inc c)

/- English proof (translation)
Use `ae_ext (by rw [RingHom.map_mul, (atPl_spec w _).1, (atPl_spec w _).1, mul_zero]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, RingHom.map_mul, (atPl_spec w _).2, (atPl_spec w _).2, cpt_incA]`. Distinguish the cases in `h : Q = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem atPl_mul (w : Pl D.host.E) (c : D.host.E) (x : Kw w) :
    atPl w (algebraMap D.host.E (Kw w) c * x) = incA D c * atPl w x := by
  classical
  refine ae_ext (by rw [RingHom.map_mul, (atPl_spec w _).1, (atPl_spec w _).1, mul_zero]) fun Q => ?_
  rw [RingHom.map_mul, RingHom.map_mul, (atPl_spec w _).2, (atPl_spec w _).2, cpt_incA]
  by_cases h : Q = w
  · subst h; simp
  · simp [h]

/- English proof (translation)
The claim follows from `((comp_toAd D).int z).2 h`.
-/
theorem mem_intAE {z : AE D} (h : ∀ Q : Pl D.host.E, Valued.v (cpt (D := D) Q (toEAf D z)) ≤ 1) :
    finPart D z ∈ intAE D := ((comp_toAd D).int z).2 h

/- English proof (translation)
Take `⟨u, hu, hu'⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) w.ne_bot w.isPrime.ne_top`. Establish `h1 : ∀ p ∈ w.asIdeal, ∀ Q : Pl D.host.E, Q.valuation D.host.E u * Q.intValuation p ≤ 1` using `fun p hp Q => by`. Use `(FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)).1 hu _ (FractionalIdeal.mem_coeIdeal_of_mem _ hp)` as an intermediate fact. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 this`. Rewrite using `[← Q.valuation_of_algebraMap (K := D.host.E), ← map_mul, ← hc]`.

Conclude with `Q.valuation_le_one c`. Use `⟨u, fun h => hu' ((FractionalIdeal.mem_one_iff _).2 ⟨⟨u, h⟩, rfl⟩), ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `w.intValuation_exists_uniformizer`. Establish `h2` using `h1 p ((w.intValuation_lt_one_iff_mem p).1 (by`. Rewrite using `[hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use the proof step `omega)) w`. Rewrite `h2` using `[hp, WithZero.exp_neg, mul_inv_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), one_mul]`. Conclude with `h2`. Take `⟨p, hp, hp'⟩` from `Set.not_subset.1 fun h : (w.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal => hQ (GlobalTheory.IdemSupport.eq_of_le h).symm`. Establish `h2` using `h1 p hp Q`.

Rewrite `h2` using `[(Q.intValuation_eq_one_iff).2 hp', mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_pole (w : Pl D.host.E) : ∃ u : D.host.E, ¬ IsIntegral ℤ u ∧ w.valuation D.host.E u ≤ WithZero.exp (1 : ℤ) ∧
    ∀ Q : Pl D.host.E, Q ≠ w → Q.valuation D.host.E u ≤ 1 := by
  obtain ⟨u, hu, hu'⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) w.ne_bot w.isPrime.ne_top
  have h1 : ∀ p ∈ w.asIdeal, ∀ Q : Pl D.host.E, Q.valuation D.host.E u * Q.intValuation p ≤ 1 := fun p hp Q => by
    have := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)).1 hu _
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 this
    rw [← Q.valuation_of_algebraMap (K := D.host.E), ← map_mul, ← hc]
    exact Q.valuation_le_one c
  refine ⟨u, fun h => hu' ((FractionalIdeal.mem_one_iff _).2 ⟨⟨u, h⟩, rfl⟩), ?_, fun Q hQ => ?_⟩
  · obtain ⟨p, hp⟩ := w.intValuation_exists_uniformizer
    have h2 := h1 p ((w.intValuation_lt_one_iff_mem p).1 (by
      rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)) w
    rw [hp, WithZero.exp_neg, mul_inv_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), one_mul] at h2
    exact h2
  · obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 fun h : (w.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal =>
      hQ (GlobalTheory.IdemSupport.eq_of_le h).symm
    have h2 := h1 p hp Q
    rwa [(Q.intValuation_eq_one_iff).2 hp', mul_one] at h2

/- English proof (translation)
The claim follows from `haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _ ValuativeRel.isEquiv _ _`.
-/
theorem isEquiv_Kw (w : Pl D.host.E) :
    (valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c`.
-/
theorem valued_alg (w : Pl D.host.E) (c : D.host.E) :
    Valued.v (algebraMap D.host.E (Kw w) c) = w.valuation D.host.E c :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.E) D.host.E), w.valuation_of_algebraMap, w.intValuation_eq_one_iff]`. Conclude with `h`.
-/
theorem valuation_nat {w : Pl D.host.E} {n : ℕ} (h : (n : 𝓞 D.host.E) ∉ w.asIdeal) :
    w.valuation D.host.E (n : D.host.E) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E), w.valuation_of_algebraMap, w.intValuation_eq_one_iff]
  exact h

/- English proof (translation)
Establish `hn : ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal` using `fun hm => by`. Take `⟨p, hp, hP⟩` from `exists_prime_under w`. Conclude with `h ((hP _).2 ((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 hm)))`. Establish `key : ∃ c : 𝓞 D.host.E, algebraMap _ _ c = a * (Ideal.absNorm D.host.𝔟 : ℕ)`. Break down `ha with ha | ha` into its components or cases.

Conclude with `int_of_mem_b D (Ideal.absNorm_mem _) ha`. Take `⟨c, hc⟩` from `int_of_mem_b D (Ideal.absNorm_mem _) (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 a).1 ha)`. Use `⟨GlobalTheory.IdemSupport.cO D c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (algebraMap _ D.host.E c) = _`. Rewrite using `[hc, star_mul', star_star, star_natCast]`.

Take `⟨c, hc⟩` from `key`. Establish `: w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E c) ≤ 1` using `w.valuation_le_one c`. Rewrite `this` using `[hc, map_mul, valuation_nat hn, mul_one]`. Then use the resulting hypothesis.
-/
theorem valuation_le_one_of_mem {w : Pl D.host.E} (h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {a : D.host.E}
    (ha : a ∈ D.host.AA ∨ a ∈ D.host.AAbar) : w.valuation D.host.E a ≤ 1 := by
  have hn : ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun hm => by
    obtain ⟨p, hp, hP⟩ := exists_prime_under w
    exact h ((hP _).2 ((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 hm)))
  have key : ∃ c : 𝓞 D.host.E, algebraMap _ _ c = a * (Ideal.absNorm D.host.𝔟 : ℕ) := by
    rcases ha with ha | ha
    · exact int_of_mem_b D (Ideal.absNorm_mem _) ha
    · obtain ⟨c, hc⟩ := int_of_mem_b D (Ideal.absNorm_mem _) (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 a).1 ha)
      refine ⟨GlobalTheory.IdemSupport.cO D c, ?_⟩
      change star (algebraMap _ D.host.E c) = _
      rw [hc, star_mul', star_star, star_natCast]
  obtain ⟨c, hc⟩ := key
  have : w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E c) ≤ 1 := w.valuation_le_one c
  rwa [hc, map_mul, valuation_nat hn, mul_one] at this

/- English proof (translation)
The claim follows from `congrArg (Formalism.IndefR.Lev.swapAE D) ((GlobalTheory.LatVac.finPart_pair 1 u).trans (GlobalTheory.LatVac.finPart_incA u).symm)`.
-/
theorem toEAf_pair (u : D.host.E) : toEAf D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u) = toEAf D (incA D u) :=
  congrArg (Formalism.IndefR.Lev.swapAE D) ((GlobalTheory.LatVac.finPart_pair 1 u).trans (GlobalTheory.LatVac.finPart_incA u).symm)

/- English proof (translation)
The claim follows from `(congrArg (cpt (D := D) Q) (toEAf_pair u)).trans (cpt_incA Q u)`.
-/
theorem cpt_pair (Q : Pl D.host.E) (u : D.host.E) :
    cpt (D := D) Q (toEAf D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u)) = algebraMap D.host.E (Kw Q) u :=
  (congrArg (cpt (D := D) Q) (toEAf_pair u)).trans (cpt_incA Q u)

/- English proof (translation)
Rewrite using `[← mul_assoc, ← RingHom.map_mul]`.
-/
theorem inc_mul_inc (a b : D.host.E) (z : AE D) : incA D a * (incA D b * z) = incA D (a * b) * z := by
  rw [← mul_assoc, ← RingHom.map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
The claim follows from `Circle.ext_iff`.
-/
theorem psiAt_eq_one {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) (x : Kw w) : psiAt W w x = 1 ↔
    W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w x)) = 1 :=
  Circle.ext_iff

/- English proof (translation)
Establish `hP` using `Formalism.IndefR.Fin.factPrincipalDatum`. Establish `e` using `isEquiv_Kw w`. Establish `h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal` using `fun h => hw (mem_of_dvd h (Dvd.intro _ rfl))`. Establish `hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal` using `fun h => hw (mem_of_dvd h (Dvd.intro_left _ rfl))`. Establish `hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D` using `fun y hy => mem_intAE fun Q => by`.

Rewrite using `[(atPl_spec w y).2]`. Distinguish the cases in `h : Q = w`. Substitute `h` using the available equality. Simplify using `using hy`. Simplify using `[h]`.

Introduce `x`. Rewrite using `[Units.val_one, map_one, e.le_one_iff_le_one]`. Use `⟨fun h => ?_, fun hx y hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Take `⟨u, hu, hu1, hu2⟩` from `exists_pole w`.

Use `hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)` and prove the remaining obligations. Establish `hx1 : WithZero.exp (1 : ℤ) ≤ Valued.v x`. Establish `h0 : Valued.v x ≠ 0` using `fun h0 => hx (h0 ▸ zero_le_one)`. Rewrite `hx` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite using `[← WithZero.exp_log h0, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hn : D.host.xi0 * (a * j) * c ∈ Dinv D`. Rewrite using `[mul_comm]`. Conclude with `(Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)`. Establish `h1` using `(psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by`.

Rewrite using `[e, map_mul, valued_alg, valued_alg, map_mul, map_mul]`. Use `le_trans ?_ hx1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[atPl_mul, inc_mul_inc]`. Establish `hc : ∀ Q : Pl D.host.E, cpt (D` using `D) Q (toEAf D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u)) = algebraMap D.host.E (Kw Q) u := fun Q => cpt_pair Q u`.

Establish `h2` using `char_int W.ψ_std hn (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u)) (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by`. Rewrite using `[RingHom.map_sub, RingHom.map_sub, hc, (atPl_spec w _).2]`. Distinguish the cases in `hQ : Q = w`. Substitute `hQ` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.single_eq_of_ne hQ, sub_zero, valued_alg]`. Conclude with `hu2 Q hQ)`. Rewrite `h1` using `[← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0]`. Rewrite `h2` using `[← mul_assoc D.host.xi0]`. Establish `h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1`.

Rewrite using `[← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add, map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]`. Rewrite `h3` using `[trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std]`. Rewrite using `[show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]` and apply the resulting hypothesis. Establish `hy1 : Valued.v y ≤ 1` using `((e y x).1 hy).trans hx set N : D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) with hNdef`. Establish `hN1 : w.valuation D.host.E N = 1` using `valuation_nat hN`.

Establish `hv : Valued.v (algebraMap D.host.E (Kw w) (N * N)) = 1` using `by rw [valued_alg, map_mul, hN1, one_mul]`. Establish `h0 : algebraMap D.host.E (Kw w) (N * N) ≠ 0` using `fun h => by simp [h] at hv`. Rewrite using `[psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]`. Use `char_int W.ψ_std (xi_mem_Dinv hP D (normCc_mem_AA D) (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 N).2 ?_)) (atPl_spec w _).1 (hint _ (by rwa [map_mul, map_inv₀, hv, inv_one, one_mul]))` and prove the remaining obligations. Rewrite using `[hNdef, star_natCast]`.

Conclude with `normCc_mem_AA D`.
-/
theorem hasConductor_psiAt {G : GridData L sc} (W : G.Weil) {w : Pl D.host.E}
    (hw : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) : HasConductor (psiAt W w) 1 := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have e := isEquiv_Kw w
  have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (mem_of_dvd h (Dvd.intro _ rfl))
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (mem_of_dvd h (Dvd.intro_left _ rfl))
  have hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D := fun y hy => mem_intAE fun Q => by
    rw [(atPl_spec w y).2]
    by_cases h : Q = w
    · subst h; simpa using hy
    · simp [h]
  intro x
  rw [Units.val_one, map_one, e.le_one_iff_le_one]
  refine ⟨fun h => ?_, fun hx y hy => ?_⟩
  · by_contra hx
    obtain ⟨u, hu, hu1, hu2⟩ := exists_pole w
    refine hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)
    have hx1 : WithZero.exp (1 : ℤ) ≤ Valued.v x := by
      have h0 : Valued.v x ≠ 0 := fun h0 => hx (h0 ▸ zero_le_one)
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    have hn : D.host.xi0 * (a * j) * c ∈ Dinv D := by
      rw [mul_comm]
      exact (Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)
    have h1 := (psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by
      rw [e, map_mul, valued_alg, valued_alg, map_mul, map_mul]
      refine le_trans ?_ hx1
      calc _ ≤ 1 * 1 * 1 * WithZero.exp (1 : ℤ) :=
            mul_le_mul' (mul_le_mul' (mul_le_mul' (valuation_le_one_of_mem h2q (.inl ha))
              (valuation_le_one_of_mem h2q (.inr hj))) (w.valuation_le_one c)) hu1
        _ = _ := by simp))
    rw [atPl_mul, inc_mul_inc] at h1
    have hc : ∀ Q : Pl D.host.E, cpt (D := D) Q (toEAf D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u)) =
        algebraMap D.host.E (Kw Q) u := fun Q => cpt_pair Q u
    have h2 := char_int W.ψ_std hn (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u))
      (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by
        rw [RingHom.map_sub, RingHom.map_sub, hc, (atPl_spec w _).2]
        by_cases hQ : Q = w
        · subst hQ; simp
        · rw [Pi.single_eq_of_ne hQ, sub_zero, valued_alg]
          exact hu2 Q hQ)
    rw [← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0] at h1
    rw [← mul_assoc D.host.xi0] at h2
    have h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1 := by
      rw [← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add,
        map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]
    rw [trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std] at h3
    rwa [show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]
  · have hy1 : Valued.v y ≤ 1 := ((e y x).1 hy).trans hx
    set N : D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) with hNdef
    have hN1 : w.valuation D.host.E N = 1 := valuation_nat hN
    have hv : Valued.v (algebraMap D.host.E (Kw w) (N * N)) = 1 := by rw [valued_alg, map_mul, hN1, one_mul]
    have h0 : algebraMap D.host.E (Kw w) (N * N) ≠ 0 := fun h => by simp [h] at hv
    rw [psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]
    refine char_int W.ψ_std (xi_mem_Dinv hP D (normCc_mem_AA D) (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 N).2 ?_)) (atPl_spec w _).1
      (hint _ (by rwa [map_mul, map_inv₀, hv, inv_one, one_mul]))
    rw [hNdef, star_natCast]
    exact normCc_mem_AA D

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))]`. Both sides reduce to the same expression.
-/
theorem natCast_mem_under (w : Pl D.host.E) (n : ℕ) :
    (n : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal ↔ (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  rw [← map_natCast (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))]
  rfl

/- English proof (translation)
Establish `h0 : w ∈ G.pl.W0 → w.under (𝓞 D.host.F) ∈ G.pl.S0 ∧ w = G.pl.w (w.under (𝓞 D.host.F))` using `fun h => by`. Take `⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w` from `by simpa [Places.W0] using h`. Rewrite using `[G.pl.under_w hv]`. Conclude with `⟨hv, rfl⟩`. Distinguish the cases in `h : w ∈ G.pl.W0`.

Conclude with `.inl (h0 h)`. Establish `hQ : w ∈ L.Q t` using `by simpa [locPl, h] using hw`. Distinguish the cases in `hS : w.under (𝓞 D.host.F) ∈ G.pl.S0`. Conclude with `.inl ⟨hS, G.pl.w_Q t w hQ ((G.pl.mem_S0_of_sum_eq.1 hS).resolve_left (G.pl.levelPlace_ne_basePlace t w hQ))⟩`. Conclude with `.inr ⟨hS, h, hQ⟩`.
-/
theorem locPl_cases {G : GridData L sc} {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (w.under (𝓞 D.host.F) ∈ G.pl.S0 ∧ w = G.pl.w (w.under (𝓞 D.host.F))) ∨
      (w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧ w ∉ G.pl.W0 ∧ w ∈ L.Q t) := by
  classical
  have h0 : w ∈ G.pl.W0 → w.under (𝓞 D.host.F) ∈ G.pl.S0 ∧ w = G.pl.w (w.under (𝓞 D.host.F)) := fun h => by
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by simpa [Places.W0] using h
    rw [G.pl.under_w hv]
    exact ⟨hv, rfl⟩
  by_cases h : w ∈ G.pl.W0
  · exact .inl (h0 h)
  have hQ : w ∈ L.Q t := by simpa [locPl, h] using hw
  by_cases hS : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · exact .inl ⟨hS, G.pl.w_Q t w hQ ((G.pl.mem_S0_of_sum_eq.1 hS).resolve_left (G.pl.levelPlace_ne_basePlace t w hQ))⟩
  · exact .inr ⟨hS, h, hQ⟩

/- English proof (translation)
Introduce `w hw w' hw' (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))`. Apply the tactic sequence `rcases locPl_cases hw with ⟨a, b⟩ | ⟨a, -, b⟩ <;> rcases locPl_cases hw' with ⟨a', b'⟩ | ⟨a', -, b'⟩`. Conclude with `b.trans ((congrArg G.pl.w h).trans b'.symm)`. Conclude with `absurd (h ▸ a) a'`. Conclude with `absurd (h ▸ a') a`.

Conclude with `(GlobalTheory.IdemSupport.eq_or_eq_cP h).resolve_right fun e => (hL.Q_pl t w' b').2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 e)`.
-/
theorem under_injOn {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) :
    Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (locPl G t) := by
  intro w hw w' hw' (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))
  rcases locPl_cases hw with ⟨a, b⟩ | ⟨a, -, b⟩ <;> rcases locPl_cases hw' with ⟨a', b'⟩ | ⟨a', -, b'⟩
  · exact b.trans ((congrArg G.pl.w h).trans b'.symm)
  · exact absurd (h ▸ a) a'
  · exact absurd (h ▸ a') a
  · exact (GlobalTheory.IdemSupport.eq_or_eq_cP h).resolve_right fun e =>
      (hL.Q_pl t w' b').2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 e)

/- English proof (translation)
Establish `hq : D.host.q.Prime` using `D.host.hyp.1`. Establish `hp : ∀ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) → p ∈ D.host.levelPrimes → Nat.Coprime (badInt D) p` using `fun p h2 h3 => Nat.Coprime.mul_left h2.symm (D.host.ccK_coprime p (by simp [h3]))`. Break down `locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩` into its components or cases. Break down `G.pl.mem_S0_of_sum_eq.1 a with a | a` into its components or cases. Use `not_mem_of_coprime w (b := q0 D) ?_ ((natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))` and prove the remaining obligations.

Take `⟨h1, h2, h3⟩` from `leastSplitAuxiliaryPrimeThetaChain_spec D`. Establish `h4 : Nat.Coprime (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D)`. Rewrite using `[Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h2, Nat.gcd_one_left]`. Conclude with `(Nat.Coprime.mul_right (h4.coprime_dvd_right ⟨Formalism.MainNotions.rPrAv D * D.host.d, by unfold LevelStarExponents.condE; ring⟩) ((h1.coprime_iff_not_dvd).2 h3)).symm`. Simplify using `only [S1_mem_OmF, natCast_mem_under] at a`.

Break down `a with a | a | a | a` into its components or cases. Conclude with `not_mem_of_coprime w (GlobalTheory.CoverHalf.g_coprime D 0).symm a`. Conclude with `not_mem_of_coprime w (GlobalTheory.CoverHalf.g_coprime D 1).symm a`. Conclude with `not_mem_of_coprime w (hp _ hde.1 D.host.pde_level.1) a`. Conclude with `not_mem_of_coprime w (hp _ hde.2 D.host.pde_level.2) a`.

Rewrite using `[Nat.cast_mul]`. Conclude with `fun h => (w.isPrime.mem_or_mem h).elim (fun h => (hL.Q_off t w b).1 (mem_of_dvd h ⟨D.host.d * D.sp.T, by ring⟩)) (hc w b)`.
-/
theorem badInt_notMem {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc} {t : T}
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    ((badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hp : ∀ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) → p ∈ D.host.levelPrimes → Nat.Coprime (badInt D) p :=
    fun p h2 h3 => Nat.Coprime.mul_left h2.symm (D.host.ccK_coprime p (by simp [h3]))
  rcases locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine not_mem_of_coprime w (b := q0 D) ?_ ((natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      obtain ⟨h1, h2, h3⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
      have h4 : Nat.Coprime (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h2, Nat.gcd_one_left]
      exact (Nat.Coprime.mul_right (h4.coprime_dvd_right
        ⟨Formalism.MainNotions.rPrAv D * D.host.d, by unfold LevelStarExponents.condE; ring⟩) ((h1.coprime_iff_not_dvd).2 h3)).symm
    · simp only [S1_mem_OmF, natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact not_mem_of_coprime w (GlobalTheory.CoverHalf.g_coprime D 0).symm a
      · exact not_mem_of_coprime w (GlobalTheory.CoverHalf.g_coprime D 1).symm a
      · exact not_mem_of_coprime w (hp _ hde.1 D.host.pde_level.1) a
      · exact not_mem_of_coprime w (hp _ hde.2 D.host.pde_level.2) a
  · rw [Nat.cast_mul]
    exact fun h => (w.isPrime.mem_or_mem h).elim
      (fun h => (hL.Q_off t w b).1 (mem_of_dvd h ⟨D.host.d * D.sp.T, by ring⟩)) (hc w b)

/- English proof (translation)
Introduce and unpack `x ⟨h1, h2⟩`. Establish `hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ)` using `unif_spec w`. Use `h x ((isEquiv_Kw w).eq_one_iff_eq_one.1 h1) (((isEquiv_Kw w _ _).1 h2).trans ?_)` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hu, ← WithZero.exp_nsmul, WithZero.exp_le_exp]`. Simplify using `[hn]`.
-/
theorem condLE_loc {χ : HChar D.host.E} {w : Pl D.host.E} {n e : ℕ} (h : χ.LevelLe w n) (hn : n ≤ e) :
    CondLE (unifAt w) e (χ.loc w) := by
  rintro x ⟨h1, h2⟩
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  refine h x ((isEquiv_Kw w).eq_one_iff_eq_one.1 h1) (((isEquiv_Kw w _ _).1 h2).trans ?_)
  rw [Units.val_pow_eq_pow_val, map_pow, hu, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simp [hn]

/- English proof (translation)
The claim follows from `forall_congr' fun _ => imp_congr_left (isEquiv_Kw w).eq_one_iff_eq_one`.
-/
theorem isUnram_loc {χ : HChar D.host.E} {w : Pl D.host.E} : IsUnram (χ.loc w) ↔ χ.UnrAt w :=
  forall_congr' fun _ => imp_congr_left (isEquiv_Kw w).eq_one_iff_eq_one

/- English proof (translation)
Introduce `x hx` and use `by rw [MonoidHom.pow_apply, h x hx.1, one_pow]`.
-/
theorem condLE_pow {w : Pl D.host.E} {e : ℕ} {α : (Kw w)ˣ →* ℂˣ} (h : IsUnram α) (n : ℕ) : CondLE (unifAt w) e (α ^ n) :=
  fun x hx => by rw [MonoidHom.pow_apply, h x hx.1, one_pow]

/- English proof (translation)
Establish `hη : IsUnram (locGrid G t w).eta` using `isUnram_loc.2 (L.C.isEta.unr w)`. Use `⟨D.R.t_odd, odd_sLen D, hη, fun i hi j hj => ?_⟩` and prove the remaining obligations. Use `replace hi : i < D.R.m := hi`. Use `replace hj : j < D.R.m := hj`. Establish `i1 : 1 ≤ D.R.m - i` using `by omega`.

Establish `i2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `hμ` using `L.C.isMu0 ⟨j, hj⟩`. Establish `emu : (locGrid G t w).mu (j + 1) = (L.C.mu0 ⟨j, hj⟩).loc w * (L.xiH t).loc w`. Express the relevant statement in the definitionally equal form `(muBase L (j + 1) * L.xiH t).loc w = _`. Rewrite using `[muBase, dif_pos hj]`.

Both sides reduce to the same expression. Establish `echi : (locGrid G t w).chi ((locGrid G t w).m - i) = (G.ch.chiH (D.R.m - i)).loc w` using `rfl`. Establish `enu : ∀ x, ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) x = (L.C.mu0 ⟨j, hj⟩).loc w x * (L.xiH t).loc w x / (G.ch.chiH (D.R.m - i)).loc w x` using `fun x => by`. Rewrite using `[Grid.alpha_div_beta, Grid.nu, emu, echi]`. Both sides reduce to the same expression.

Establish `h1 : 1 ≤ depthAt G w` using `le_max_right _ _`. Establish `hμ1 : w.under (𝓞 D.host.F) ∉ S1 D → (L.C.mu0 ⟨j, hj⟩).UnrAt w` using `fun h => hμ.unr w fun k hk => h (by`. Rewrite using `[S1_mem_OmF, natCast_mem_under, natCast_mem_under]`. Use `fin_cases k`. Conclude with `.inl hk`.

Conclude with `.inr (.inl hk))`. Establish `key : ¬ IsUnram ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) ∧ CondLE (unifAt w) (depthAt G w) ((G.ch.chiH (D.R.m - i)).loc w)`. Establish `hun : IsUnram ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) → ∀ x, IsUnitAt w x → (L.C.mu0 ⟨j, hj⟩).loc w x * (L.xiH t).loc w x = (G.ch.chiH (D.R.m - i)).loc w x` using `fun h x hx => div_eq_one.1 ((enu x).symm.trans (h x ((isEquiv_Kw w).eq_one_iff_eq_one.2 hx)))`. Break down `locPl_cases hw with ⟨a, b⟩ | ⟨a, b, c⟩` into its components or cases. Break down `G.pl.mem_S0_of_sum_eq.1 a with a0 | a1` into its components or cases.

Take `⟨l1, l2⟩` from `G.ch.lev0 _ i1 i2 w a0`. Establish `hξ : (L.xiH t).UnrAt w`. Assume the negation of the conclusion as `h`. Break down `(hL.Q_ram t w).1 h with h | ⟨P, hP, h⟩` into its components or cases. Conclude with `G.pl.levelPlace_ne_basePlace t w h a0`.

Conclude with `G.pl.levelPlace_ne_basePlace t P hP (by`. Rewrite using `[← a0, (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP])`. Conclude with `⟨fun h => l2 fun x hx => by`. Rewrite using `[← hun h x hx, hμ1 (a0 ▸ G.ch.basePlace_not_mem_chiGridBadPlaces) x hx, hξ x hx, one_mul], condLE_loc l1 h1⟩`. Take `⟨l1, l2⟩` from `G.ch.lev1 _ i1 i2 w a1`.

Use `⟨fun h => l2 fun x hx hx' => by` and prove the remaining obligations. Rewrite using `[← hun h x hx, hμ.tame w x hx hx', hL.xi_tame t w x hx hx', one_mul], condLE_loc l1 ?_⟩`. Use `(depthAt_w G a).2` as an intermediate fact. Rewrite `this` using `[← b, Places.depth, if_neg fun e : _ = G.pl.v0 => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ a1)]`. Conclude with `this.ge`.

Establish `hχ` using `G.ch.unr _ i1 i2 w a`. Use `⟨fun h => (hL.Q_ram t w).2 (.inl c) fun x hx => ?_, condLE_of_isUnram _ _ (isUnram_loc.2 hχ)⟩` and prove the remaining obligations. Use `hun h x hx` as an intermediate fact. Rewrite `this` using `[hμ1 (fun h => a (G.pl.mem_S0_of_sum_eq.2 (.inr h))) x hx, hχ x hx, one_mul]`. Then use the resulting hypothesis. Use `⟨isUnif_unifAt w, hasConductor_psiAt W hb, key.1, fun x => ?_, h1, ?_, ?_⟩` and prove the remaining obligations.

Establish `u1 : ‖((L.C.mu0 ⟨j, hj⟩).loc w x : ℂ)‖ = 1` using `hμ.unitary _`. Establish `u2 : ‖((L.xiH t).loc w x : ℂ)‖ = 1` using `GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (hL.xi t) _`. Establish `u3 : ‖((G.ch.chiH (D.R.m - i)).loc w x : ℂ)‖ = 1` using `GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ i1 i2) _`. Rewrite using `[enu, Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, u1, u2, u3, one_mul, div_one]`. Rewrite using `[Grid.alpha, emu]`.

Conclude with `((condLE_loc (hμ.tame w) h1).mul (condLE_loc (hL.xi_tame t w) h1)).mul (condLE_pow hη _)`. Conclude with `key.2.mul (condLE_pow hη _)`.
-/
theorem isGood_of_notMem {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc} (W : G.Weil) {t : T} {w : Pl D.host.E}
    (hw : w ∈ locPl G t) (hb : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    (locGrid G t w).IsGood (unifAt w) (psiAt W w) (depthAt G w) := by
  have hη : IsUnram (locGrid G t w).eta := isUnram_loc.2 (L.C.isEta.unr w)
  refine ⟨D.R.t_odd, odd_sLen D, hη, fun i hi j hj => ?_⟩
  replace hi : i < D.R.m := hi
  replace hj : j < D.R.m := hj
  have i1 : 1 ≤ D.R.m - i := by omega
  have i2 : D.R.m - i ≤ D.R.m := by omega
  have hμ := L.C.isMu0 ⟨j, hj⟩
  have emu : (locGrid G t w).mu (j + 1) = (L.C.mu0 ⟨j, hj⟩).loc w * (L.xiH t).loc w := by
    change (muBase L (j + 1) * L.xiH t).loc w = _
    rw [muBase, dif_pos hj]
    rfl
  have echi : (locGrid G t w).chi ((locGrid G t w).m - i) = (G.ch.chiH (D.R.m - i)).loc w := rfl
  have enu : ∀ x, ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) x =
      (L.C.mu0 ⟨j, hj⟩).loc w x * (L.xiH t).loc w x / (G.ch.chiH (D.R.m - i)).loc w x := fun x => by
    rw [Grid.alpha_div_beta, Grid.nu, emu, echi]
    rfl
  have h1 : 1 ≤ depthAt G w := le_max_right _ _
  have hμ1 : w.under (𝓞 D.host.F) ∉ S1 D → (L.C.mu0 ⟨j, hj⟩).UnrAt w := fun h => hμ.unr w fun k hk => h (by
    rw [S1_mem_OmF, natCast_mem_under, natCast_mem_under]
    fin_cases k
    · exact .inl hk
    · exact .inr (.inl hk))
  have key : ¬ IsUnram ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) ∧
      CondLE (unifAt w) (depthAt G w) ((G.ch.chiH (D.R.m - i)).loc w) := by
    have hun : IsUnram ((locGrid G t w).alpha i j / (locGrid G t w).beta i j) → ∀ x, IsUnitAt w x →
        (L.C.mu0 ⟨j, hj⟩).loc w x * (L.xiH t).loc w x = (G.ch.chiH (D.R.m - i)).loc w x := fun h x hx =>
      div_eq_one.1 ((enu x).symm.trans (h x ((isEquiv_Kw w).eq_one_iff_eq_one.2 hx)))
    rcases locPl_cases hw with ⟨a, b⟩ | ⟨a, b, c⟩
    · rcases G.pl.mem_S0_of_sum_eq.1 a with a0 | a1
      · obtain ⟨l1, l2⟩ := G.ch.lev0 _ i1 i2 w a0
        have hξ : (L.xiH t).UnrAt w := by
          by_contra h
          rcases (hL.Q_ram t w).1 h with h | ⟨P, hP, h⟩
          · exact G.pl.levelPlace_ne_basePlace t w h a0
          · exact G.pl.levelPlace_ne_basePlace t P hP (by
              rw [← a0, (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP])
        exact ⟨fun h => l2 fun x hx => by
          rw [← hun h x hx, hμ1 (a0 ▸ G.ch.basePlace_not_mem_chiGridBadPlaces) x hx, hξ x hx, one_mul], condLE_loc l1 h1⟩
      · obtain ⟨l1, l2⟩ := G.ch.lev1 _ i1 i2 w a1
        refine ⟨fun h => l2 fun x hx hx' => by
          rw [← hun h x hx, hμ.tame w x hx hx', hL.xi_tame t w x hx hx', one_mul], condLE_loc l1 ?_⟩
        have := (depthAt_w G a).2
        rw [← b, Places.depth, if_neg fun e : _ = G.pl.v0 => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ a1)] at this
        exact this.ge
    · have hχ := G.ch.unr _ i1 i2 w a
      refine ⟨fun h => (hL.Q_ram t w).2 (.inl c) fun x hx => ?_, condLE_of_isUnram _ _ (isUnram_loc.2 hχ)⟩
      have := hun h x hx
      rwa [hμ1 (fun h => a (G.pl.mem_S0_of_sum_eq.2 (.inr h))) x hx, hχ x hx, one_mul] at this
  refine ⟨isUnif_unifAt w, hasConductor_psiAt W hb, key.1, fun x => ?_, h1, ?_, ?_⟩
  · have u1 : ‖((L.C.mu0 ⟨j, hj⟩).loc w x : ℂ)‖ = 1 := hμ.unitary _
    have u2 : ‖((L.xiH t).loc w x : ℂ)‖ = 1 := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (hL.xi t) _
    have u3 : ‖((G.ch.chiH (D.R.m - i)).loc w x : ℂ)‖ = 1 :=
      GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ i1 i2) _
    rw [enu, Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, u1, u2, u3, one_mul, div_one]
  · rw [Grid.alpha, emu]
    exact ((condLE_loc (hμ.tame w) h1).mul (condLE_loc (hL.xi_tame t w) h1)).mul (condLE_pow hη _)
  · exact key.2.mul (condLE_pow hη _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hw => isGood_of_notMem hL W hw (badInt_notMem hL hde hc hw), under_injOn hL G t⟩`.
-/
theorem locGrid_isGood {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (W : G.Weil) (t : T) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    (∀ w ∈ locPl G t, (locGrid G t w).IsGood (unifAt w) (psiAt W w) (depthAt G w)) ∧
      Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (locPl G t) :=
  ⟨fun _ hw => isGood_of_notMem hL W hw (badInt_notMem hL hde hc hw), under_injOn hL G t⟩

end GlobalTheory.FunObj.Good

end
