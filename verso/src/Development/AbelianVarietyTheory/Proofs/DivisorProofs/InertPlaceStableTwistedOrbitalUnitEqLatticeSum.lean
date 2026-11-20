import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspliStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

/- English proof (translation)
Distinguish the cases in `h : (Function.support f).Finite`. Conclude with `map_finsum (Rat.castHom ℂ) h`. Establish `h1 : (Function.support f).Infinite` using `h`. Establish `h2 : (Function.support fun i => (f i : ℂ)).Infinite`. Establish `e : (Function.support fun i => (f i : ℂ)) = Function.support f`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `h1`. Rewrite using `[finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]`.
-/
theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

/- English proof (translation)
Introduce `E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ`. Unfold `stTw IsCsr at *`. Unfold `clSum`. Establish `hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse` using `hQ.resolve_left hw`. Establish `hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom`.

Use extensionality with `y`. Establish `h` using `congrArg e.symm (hc (e.symm y))`. Simplify using `only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h`. Simplify using `[h]`. Establish `hrev : ∀ p : (w.adicCompletion E)[X], (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse`.

Introduce `p`. Unfold `Polynomial.reverse`. Rewrite using `[Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]`. Establish `hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom = ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse`. Establish `h1` using `congrArg (Polynomial.map e.symm.toRingHom) hQ'`.

Establish `h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0)`. Rewrite using `[Polynomial.coeff_map]`. Conclude with `RingHom.congr_fun hcomm (Q.coeff 0)`. Rewrite `h1` using `[Polynomial.map_mul, Polynomial.map_C, h0]`. Rewrite using `[h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]`.

Take `⟨B, hg, hP⟩` from `GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr`. Establish `hsep : B.P.Separable`. Rewrite using `[hP]`. Conclude with `hs.map`. Use `⟨B, hg, hP, ?_⟩` and prove the remaining obligations.

Establish `hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1` using `neg_one_pow_eq_or B.A (a - 1)`. Take `⟨β₀, hβ₀, hX⟩` from `GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε`. Take `⟨F, hF⟩` from `GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀`. Establish `hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w a) (F k).1.rep ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ)`. Introduce `k`.

Take `⟨b, hb⟩` from `hF k`. Establish `hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ)` using `(Quot.out k).2`. Establish `hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) = (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g)`. Rewrite using `[Units.val_mul, map_mul, hβ₀, hu]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h` using `GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep (fun i j => by rw [Units.val_mul]; exact hb i j)`. Rewrite using `[h, Units.val_mul, hX _ hu]`. Both sides reduce to the same expression. Simplify using `only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]`. Simplify using `only [← finsum_eq_if]`.

Rewrite using `[← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]`. Simplify using `only [hterm]`. Conclude with `(cast_finsum_rat _).symm`.
-/
theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε
  obtain ⟨F, hF⟩ := GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w a) (F k).1.rep
      ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
