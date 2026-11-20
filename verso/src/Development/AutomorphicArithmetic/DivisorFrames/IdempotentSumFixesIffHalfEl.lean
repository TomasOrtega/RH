import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

open GlobalTheory.StdFrames (cpt comp_toAd)
open GlobalTheory.LFun (complMap)
open GlobalTheory.AdelicU (splitPrime_under)

variable {D : D7}

/- English proof (translation)
The claim follows from `(comp_toAd D).ext' h1 h2`.
-/
private theorem ext_cpt {a b : AE D} (h1 : infPart D a = infPart D b)
    (h2 : ∀ Q, cpt (D := D) Q (toEAf D a) = cpt (D := D) Q (toEAf D b)) : a = b :=
  (comp_toAd D).ext' h1 h2

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `(comp_toAd D).base u Q`.
-/
private theorem cpt_base {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) (u : AF D.host.F) :
    cpt (D := D) Q (toEAf D (algebraMap _ (AE D) u)) = complMap h (evFin D.host.F v u) := by
  subst h
  exact (comp_toAd D).base u Q

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [RingHom.map_add, hx, hy]`. Consider the case `tmul a x`. Establish `e1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap _ (AE D) a * incA D x`.

Express the relevant statement in the definitionally equal form `_ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `e2 : piW τ (a ⊗ₜ[D.host.F] x : AE D) = evFin D.host.F v a * τ x` using `rfl`. Establish `e3 : cpt (D` using `D) (splitPrime τ) (toEAf D (incA D x)) = algebraMap _ _ x := congrArg (fun s => s (splitPrime τ)) ((comp_toAd D).inc x)`. Rewrite using `[e2, e1, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cpt_base (splitPrime_under τ), e3, GlobalTheory.LFun.SplitTie.complMap_apply_emb]`.
-/
private theorem cpt_split {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    cpt (D := D) (splitPrime τ) (toEAf D z) = complMap (splitPrime_under τ) (piW τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x =>
    have e1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap _ (AE D) a * incA D x := by
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : piW τ (a ⊗ₜ[D.host.F] x : AE D) = evFin D.host.F v a * τ x := rfl
    have e3 : cpt (D := D) (splitPrime τ) (toEAf D (incA D x)) = algebraMap _ _ x :=
      congrArg (fun s => s (splitPrime τ)) ((comp_toAd D).inc x)
    rw [e2, e1, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cpt_base (splitPrime_under τ), e3,
      GlobalTheory.LFun.SplitTie.complMap_apply_emb]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [RingHom.map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
private theorem piW_comp {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piW (τ.comp D.sp.cm.sig) z = piW τ (cA D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Take `⟨e0, e1, e2⟩` from `GlobalTheory.FunObj.Comparison₂.cpt_idemSum he`. Establish `one : ∀ {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ S → piW τ e₀ = 1` using `fun τ h => (complMap (splitPrime_under τ)).injective (by rw [← cpt_split, e1 _ h, RingHom.map_one])`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `⟨fun u hu => ?_, fun v => ?_⟩` and prove the remaining obligations.

Establish `h0 : algebraMap _ (AE D) u * e₀ = 0`. Use `ext_cpt (by rw [RingHom.map_mul, e0, mul_zero, RingHom.map_zero]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]`. Distinguish the cases in `hQ : Q ∈ S`. Rewrite using `[cpt_base rfl, hu _ ((hP _).2 ⟨Q, hQ, rfl⟩), RingHom.map_zero, zero_mul]`.

Rewrite using `[e2 Q hQ, mul_zero]`. Rewrite using `[Algebra.smul_def, ← hz, ← mul_assoc]`. Conclude with `(congrArg (· * z) h0).trans (zero_mul z)`. Establish `h0` using `congrArg (piW (t v)) he.2`. Rewrite `h0` using `[RingHom.map_mul, one _ (ht v), one_mul, RingHom.map_zero, ← piW_comp]`.

Express the relevant statement in the definitionally equal form `piW ((t v).comp D.sp.cm.sig) z = 0`. Rewrite using `[← hz, RingHom.map_mul, h0, zero_mul]`. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : ∀ u : AF D.host.F, (∀ v ∈ P, evFin D.host.F v u = 0) → algebraMap _ (AE D) u * z = 0` using `fun u hu => (Algebra.smul_def u z).symm.trans (h1 u hu)`. Use `ext_cpt ?_ fun Q => ?_` and prove the remaining obligations.

Establish `h3` using `congrArg (infPart D) (h1' ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) fun v _ => rfl)`. Establish `h4 : infPart D (algebraMap (AF D.host.F) (AE D) ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) = 1` using `rfl`. Rewrite `h3` using `[RingHom.map_mul, h4, one_mul, RingHom.map_zero]`. Rewrite using `[RingHom.map_mul, h3, mul_zero]`. Rewrite using `[RingHom.map_mul, RingHom.map_mul]`.

Distinguish the cases in `hQ : Q ∈ S`. Rewrite using `[e1 Q hQ, one_mul]`. Rewrite using `[e2 Q hQ, zero_mul, eq_comm]`. Distinguish the cases in `hv : Q.under (𝓞 D.host.F) ∈ P`. Establish `hm : Q.asIdeal ∈ (Q.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E)` using `⟨Q.isPrime, ⟨rfl⟩⟩`.

Rewrite `hm` using `[GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) (t ⟨_, hv⟩)]`. Break down `hm with e | e` into its components or cases. Conclude with `absurd ((HeightOneSpectrum.ext e : Q = _) ▸ ht ⟨_, hv⟩) hQ`. Establish `h5` using `cpt_split ((t ⟨_, hv⟩).comp D.sp.cm.sig) z`. Rewrite `h5` using `[h2 ⟨_, hv⟩, RingHom.map_zero]`.

Establish `e' : Q = splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig)` using `HeightOneSpectrum.ext e`. Generalize the expression as in `splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) = Q' at h5 e'`. Substitute `e'` using the available equality. Conclude with `h5`. Set `u : AF D.host.F` to `((0, singleV D.host.F (Q.under (𝓞 D.host.F)) 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)`.

Establish `h3` using `congrArg (fun y => cpt (D := D) Q (toEAf D y)) (h1' u fun v hv' => Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (fun e : v = Q.under (𝓞 D.host.F) => hv (e ▸ hv')) 1)`. Establish `h4 : evFin D.host.F (Q.under (𝓞 D.host.F)) u = 1` using `Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Q.under (𝓞 D.host.F)) 1`. Simplify using `only [RingHom.map_mul, RingHom.map_zero] at h3`. Rewrite `h3` using `[cpt_base rfl, h4, RingHom.map_one, one_mul]`. Then use the resulting hypothesis.
-/
private theorem first_half {e₀ : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e₀ S)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hP : ∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) (ht : ∀ v : P, splitPrime (t v) ∈ S) (z : AE D) :
    e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z := by
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  have one : ∀ {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ S →
      piW τ e₀ = 1 := fun τ h =>
    (complMap (splitPrime_under τ)).injective (by rw [← cpt_split, e1 _ h, RingHom.map_one])
  constructor
  · intro hz
    refine ⟨fun u hu => ?_, fun v => ?_⟩
    · have h0 : algebraMap _ (AE D) u * e₀ = 0 := by
        refine ext_cpt (by rw [RingHom.map_mul, e0, mul_zero, RingHom.map_zero]) fun Q => ?_
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]
        by_cases hQ : Q ∈ S
        · rw [cpt_base rfl, hu _ ((hP _).2 ⟨Q, hQ, rfl⟩), RingHom.map_zero, zero_mul]
        · rw [e2 Q hQ, mul_zero]
      rw [Algebra.smul_def, ← hz, ← mul_assoc]
      exact (congrArg (· * z) h0).trans (zero_mul z)
    · have h0 := congrArg (piW (t v)) he.2
      rw [RingHom.map_mul, one _ (ht v), one_mul, RingHom.map_zero, ← piW_comp] at h0
      change piW ((t v).comp D.sp.cm.sig) z = 0
      rw [← hz, RingHom.map_mul, h0, zero_mul]
  · rintro ⟨h1, h2⟩
    have h1' : ∀ u : AF D.host.F, (∀ v ∈ P, evFin D.host.F v u = 0) → algebraMap _ (AE D) u * z = 0 :=
      fun u hu => (Algebra.smul_def u z).symm.trans (h1 u hu)
    refine ext_cpt ?_ fun Q => ?_
    · have h3 := congrArg (infPart D) (h1' ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) fun v _ => rfl)
      have h4 : infPart D (algebraMap (AF D.host.F) (AE D) ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) = 1 := rfl
      rw [RingHom.map_mul, h4, one_mul, RingHom.map_zero] at h3
      rw [RingHom.map_mul, h3, mul_zero]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hQ : Q ∈ S
      · rw [e1 Q hQ, one_mul]
      rw [e2 Q hQ, zero_mul, eq_comm]
      by_cases hv : Q.under (𝓞 D.host.F) ∈ P
      · have hm : Q.asIdeal ∈ (Q.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨rfl⟩⟩
        rw [GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) (t ⟨_, hv⟩)] at hm
        rcases hm with e | e
        · exact absurd ((HeightOneSpectrum.ext e : Q = _) ▸ ht ⟨_, hv⟩) hQ
        · have h5 := cpt_split ((t ⟨_, hv⟩).comp D.sp.cm.sig) z
          rw [h2 ⟨_, hv⟩, RingHom.map_zero] at h5
          have e' : Q = splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) := HeightOneSpectrum.ext e
          generalize splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) = Q' at h5 e'
          subst e'
          exact h5
      · let u : AF D.host.F := ((0, singleV D.host.F (Q.under (𝓞 D.host.F)) 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
        have h3 := congrArg (fun y => cpt (D := D) Q (toEAf D y)) (h1' u fun v hv' =>
          Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F)
            (fun e : v = Q.under (𝓞 D.host.F) => hv (e ▸ hv')) 1)
        have h4 : evFin D.host.F (Q.under (𝓞 D.host.F)) u = 1 :=
          Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Q.under (𝓞 D.host.F)) 1
        simp only [RingHom.map_mul, RingHom.map_zero] at h3
        rwa [cpt_base rfl, h4, RingHom.map_one, one_mul] at h3

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, GlobalTheory.IdemSupport.cA_algebraMap]`.
-/
private theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, GlobalTheory.IdemSupport.cA_algebraMap]

end

/- English proof (translation)
Introduce `D e₀ S he P t hP ht`. Use `⟨first_half he P t hP ht, fun z => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ y : AE D, cA D (cA D y) = y` using `fun y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `add x y hx hy => simp only [RingHom.map_add, hx, hy]`. Consider the case `tmul a x => exact congrArg (fun s => a ⊗ₜ[D.host.F] s) (star_star x)`. Establish `hi : Function.Injective (cA D)` using `Function.LeftInverse.injective hc`. Establish `h` using `first_half he P t hP ht (cA D z)`. Rewrite `h` using `[← hi.eq_iff, RingHom.map_mul, hc]`.

Use `h.trans (and_congr (forall_congr' fun u => imp_congr_right fun _ => ?_) (forall_congr' fun v => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u • cA D z = 0 ↔ u • z = 0`. Rewrite using `[← cA_smul, ← hi.eq_iff, hc, RingHom.map_zero]`. Express the relevant statement in the definitionally equal form `piW ((t v).comp D.sp.cm.sig) (cA D z) = 0 ↔ _`. Rewrite using `[piW_comp, hc]`.
-/
theorem UpperTheory.idempotentSum_fixes_iff_halfEl :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        (∀ z : AE D, e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z) ∧ ∀ z : AE D, cA D e₀ * z = z ↔ HalfEl P t z := by
  intro D e₀ S he P t hP ht
  refine ⟨first_half he P t hP ht, fun z => ?_⟩
  have hc : ∀ y : AE D, cA D (cA D y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [RingHom.map_add, hx, hy]
    | tmul a x => exact congrArg (fun s => a ⊗ₜ[D.host.F] s) (star_star x)
  have hi : Function.Injective (cA D) := Function.LeftInverse.injective hc
  have h := first_half he P t hP ht (cA D z)
  rw [← hi.eq_iff, RingHom.map_mul, hc] at h
  refine h.trans (and_congr (forall_congr' fun u => imp_congr_right fun _ => ?_) (forall_congr' fun v => ?_))
  · change u • cA D z = 0 ↔ u • z = 0
    rw [← cA_smul, ← hi.eq_iff, hc, RingHom.map_zero]
  · change piW ((t v).comp D.sp.cm.sig) (cA D z) = 0 ↔ _
    rw [piW_comp, hc]
