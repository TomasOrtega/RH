import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceIdempotentFiniteAdeleZeroElsewhereStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePartIntegralUnitOfUnitResidueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.SpecGood

variable {D : D7}

/- English proof (translation)
Introduce `D P e h`. Take `⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩` from `h`. Establish `k1` using `congrArg (infPart D) h1`. Establish `k2` using `congrArg (infPart D) h2`. Establish `k3` using `congrArg (infPart D) h3`.

Simplify using `only [RingHom.map_mul, RingHom.map_add, RingHom.map_zero] at k1 k2 k3`. Establish `k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0`. Simplify using `[infPart, Algebra.TensorProduct.algebraMap_apply]`. Use `show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Conclude with `TensorProduct.zero_tmul _ _`.

Rewrite `k3` using `[k4]`. Take the linear combination `-k1 + infPart D e * k3 - k2`.
-/
theorem infPart_eq_zero_of_isIdemAt : ∀ (D : D7) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 := by
  intro D P e h
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add, RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

/- English proof (translation)
Take `⟨ι, i1, i2, -⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Use `⟨?_, GlobalTheory.T.finite_part_integral_unit_of_unit_residue D ι i1 i2 P (idemAt P) (GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere D ι i1 i2 P _ hP) x h1 hx v hv⟩` and prove the remaining obligations. Use `congrArg (infPart D) h1` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_eq_zero_of_isIdemAt D P _ hP, sub_zero, one_mul]`. Then use the resulting hypothesis.
-/
theorem finUnit_of_res (P : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt (idemAt P) P) (x : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (x : AE D) = 1 - idemAt P)
    (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ)
    (hv : resS D.host.F P ⟨_, hx⟩ = v) :
    infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, i1, i2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  refine ⟨?_, GlobalTheory.T.finite_part_integral_unit_of_unit_residue D ι i1 i2 P (idemAt P) (GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere D ι i1 i2 P _ hP) x h1 hx v hv⟩
  have := congrArg (infPart D) h1
  rwa [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_eq_zero_of_isIdemAt D P _ hP, sub_zero, one_mul] at this

variable {C A : Type} [AddCommGroup C] [CommGroup A]

/- English proof (translation)
The claim follows from `GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP`.
-/
theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

/- English proof (translation)
Rewrite using `[idem, map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun j hj => h.mul_conj hP hj`.
-/
theorem idemAt_mul_conj_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * cA D (idem Q) = 0 := by
  rw [idem, map_sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => h.mul_conj hP hj

/- English proof (translation)
Use extensionality with `PP`. Conclude with `congrArg Multiplicative.toAdd (hx PP.1 PP.2)`.
-/
theorem delQ_eq_one {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} {x : (AE D)ˣ} (hx : ∀ P ∈ Q, u.del P x = 1) :
    u.delQ Q x = 1 := by
  ext PP
  exact congrArg Multiplicative.toAdd (hx PP.1 PP.2)

open Classical in

/- English proof (translation)
Establish `cc` using `GlobalTheory.DualPairCheck.cA_cA (D := D)`. Use `⟨?_, ?_, ?_, h.1, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)`. Set `H : Subgroup (AE D)ˣ` to `⨅ P : ↥Q, (u.del P.1).ker`. Establish `hH : IsOpen (H : Set (AE D)ˣ)`.

Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite fun P => (h.2 P.1 P.2).isOpen`. Use `Subgroup.isOpen_mono (fun x hx => ?_) hH` and prove the remaining obligations. Rewrite `hx` using `[Subgroup.mem_iInf]`. Use `show χ (u.delQ Q x) = 1`.

Rewrite using `[delQ_eq_one fun P hP => hx ⟨P, hP⟩, map_one]`. Introduce `x show χ (u.delQ Q _) = 1`. Rewrite using `[delQ_eq_one fun P hP => (h.2 P hP).rat x, map_one]`. Introduce `a show χ (u.delQ Q _) = 1`. Rewrite using `[h.delQ_real a, map_one]`.

Introduce `x h1 h2 h3 h4 show χ (u.delQ Q x) = 1 replace h4 : (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) := h4`. Use `(congrArg χ (delQ_eq_one fun P hP => ?_)).trans (map_one χ)` and prove the remaining obligations. Use `(h.2 P hP).unram x h1 h2 h3 ?_` and prove the remaining obligations. Use `show (idem {P} + cA D (idem {P})) * (x : AE D) = idem {P} + cA D (idem {P})`. Establish `e1 : idem ({P} : Finset (Pl D.host.E)) = idemAt P` using `Finset.sum_singleton _ _`.

Rewrite using `[e1]`. Establish `k1` using `idemAt_mul_idem h.1 hP`. Establish `k2` using `idemAt_mul_conj_idem h.1 hP`. Establish `k3 : cA D (idemAt P) * idem Q = 0`. Use `congrArg (cA D) k2` as an intermediate fact.

Rewrite `this` using `[RingHom.map_mul, cc, RingHom.map_zero]`. Then use the resulting hypothesis. Establish `k4 : cA D (idemAt P) * cA D (idem Q) = cA D (idemAt P)`. Rewrite using `[← RingHom.map_mul, k1]`. Take the linear combination `(idemAt P + cA D (idemAt P)) * h4 + (1 - (x : AE D)) * (k1 + k2 + k3 + k4)`. Introduce `PP hPP x h1 hx v hv show χ (u.delQ Q x) = (u.spec Q χ).res PP v`.

Rewrite using `[show (u.spec Q χ).res PP = χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, hPP⟩)).comp (u.kap PP)) from dif_pos hPP, MonoidHom.comp_apply]`. Establish `hfu` using `finUnit_of_res PP (h.1.isIdemAt hPP) x h1 hx v hv`. Use `congrArg χ ?_` and prove the remaining obligations. Use extensionality with `⟨P', hP'⟩`. Distinguish the cases in `hne : P' = PP`.

Substitute `hne` using the available equality. Use `(h.2 P' hP').res P' (Finset.mem_singleton_self _) x h1 hx v hv` as an intermediate fact. Simplify using `[UnivTwist.delQ, this]`. Establish `hd : u.del P' x = 1`. Use `(h.2 P' hP').unram x hfu.1 hfu.2.1 hfu.2.2 ?_` and prove the remaining obligations.

Use `show (idem {P'} + cA D (idem {P'})) * (x : AE D) = idem {P'} + cA D (idem {P'})`. Establish `e1 : idem ({P'} : Finset (Pl D.host.E)) = idemAt P'` using `Finset.sum_singleton _ _`. Rewrite using `[e1]`. Establish `z1 : idemAt P' * idemAt PP = 0` using `h.1.mul_eq_zero hP' hPP (Ne.symm hne)`. Establish `z2 : idemAt PP * cA D (idemAt P') = 0` using `h.1.mul_conj hPP hP'`.

Take the linear combination `(idemAt P' + cA D (idemAt P')) * h1 + ((x : AE D) - 1) * (z1 + z2)`. Simplify using `[UnivTwist.delQ, hd, Pi.single_apply, hne]`. Introduce `e`. Conclude with `absurd (congrArg Subtype.val e) hne`.
-/
theorem spec_good (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E))
    (χ : Multiplicative (↥Q → C) →* A) (h : u.Good Q) : (u.spec Q χ).Good := by
  have cc := GlobalTheory.DualPairCheck.cA_cA (D := D)
  refine ⟨?_, ?_, ?_, h.1, ?_, ?_⟩
  · haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    let H : Subgroup (AE D)ˣ := ⨅ P : ↥Q, (u.del P.1).ker
    have hH : IsOpen (H : Set (AE D)ˣ) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun P => (h.2 P.1 P.2).isOpen
    refine Subgroup.isOpen_mono (fun x hx => ?_) hH
    rw [Subgroup.mem_iInf] at hx
    show χ (u.delQ Q x) = 1
    rw [delQ_eq_one fun P hP => hx ⟨P, hP⟩, map_one]
  · intro x
    show χ (u.delQ Q _) = 1
    rw [delQ_eq_one fun P hP => (h.2 P hP).rat x, map_one]
  · intro a
    show χ (u.delQ Q _) = 1
    rw [h.delQ_real a, map_one]
  · intro x h1 h2 h3 h4
    show χ (u.delQ Q x) = 1
    replace h4 : (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) := h4
    refine (congrArg χ (delQ_eq_one fun P hP => ?_)).trans (map_one χ)
    refine (h.2 P hP).unram x h1 h2 h3 ?_
    show (idem {P} + cA D (idem {P})) * (x : AE D) = idem {P} + cA D (idem {P})
    have e1 : idem ({P} : Finset (Pl D.host.E)) = idemAt P := Finset.sum_singleton _ _
    rw [e1]
    have k1 := idemAt_mul_idem h.1 hP
    have k2 := idemAt_mul_conj_idem h.1 hP
    have k3 : cA D (idemAt P) * idem Q = 0 := by
      have := congrArg (cA D) k2
      rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
    have k4 : cA D (idemAt P) * cA D (idem Q) = cA D (idemAt P) := by
      rw [← RingHom.map_mul, k1]
    linear_combination (idemAt P + cA D (idemAt P)) * h4 + (1 - (x : AE D)) * (k1 + k2 + k3 + k4)
  · intro PP hPP x h1 hx v hv
    show χ (u.delQ Q x) = (u.spec Q χ).res PP v
    rw [show (u.spec Q χ).res PP = χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, hPP⟩)).comp
      (u.kap PP)) from dif_pos hPP, MonoidHom.comp_apply]
    have hfu := finUnit_of_res PP (h.1.isIdemAt hPP) x h1 hx v hv
    refine congrArg χ ?_
    ext ⟨P', hP'⟩
    by_cases hne : P' = PP
    · subst hne
      have := (h.2 P' hP').res P' (Finset.mem_singleton_self _) x h1 hx v hv
      simp [UnivTwist.delQ, this]
    · have hd : u.del P' x = 1 := by
        refine (h.2 P' hP').unram x hfu.1 hfu.2.1 hfu.2.2 ?_
        show (idem {P'} + cA D (idem {P'})) * (x : AE D) = idem {P'} + cA D (idem {P'})
        have e1 : idem ({P'} : Finset (Pl D.host.E)) = idemAt P' := Finset.sum_singleton _ _
        rw [e1]
        have z1 : idemAt P' * idemAt PP = 0 := h.1.mul_eq_zero hP' hPP (Ne.symm hne)
        have z2 : idemAt PP * cA D (idemAt P') = 0 := h.1.mul_conj hPP hP'
        linear_combination (idemAt P' + cA D (idemAt P')) * h1 + ((x : AE D) - 1) * (z1 + z2)
      simp [UnivTwist.delQ, hd, Pi.single_apply, hne]
      intro e
      exact absurd (congrArg Subtype.val e) hne

end GlobalTheory.ExportSeries.SpecGood
