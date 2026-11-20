import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

/- English proof (translation)
Take `⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩` from `h`. Establish `k1` using `congrArg (infPart D) h1`. Establish `k2` using `congrArg (infPart D) h2`. Establish `k3` using `congrArg (infPart D) h3`. Simplify using `only [RingHom.map_mul, RingHom.map_add, RingHom.map_zero] at k1 k2 k3`.

Establish `k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0`. Simplify using `[infPart, Algebra.TensorProduct.algebraMap_apply]`. Use `show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Conclude with `TensorProduct.zero_tmul _ _`. Rewrite `k3` using `[k4]`.

Take the linear combination `-k1 + infPart D e * k3 - k2`.
-/
theorem infPart_idemAt (P : Pl D.host.E) (e : AE D) (h : Formalism.L2.NTheta.IsIdemAt e P) : infPart D e = 0 := by
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
The claim follows from `GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP`.
-/
theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

/- English proof (translation)
Use `show (∑ P ∈ Q, idemAt P) * idem Q = idem Q`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP`.
-/
theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

/- English proof (translation)
Rewrite using `[idem, idem, Finset.sum_mul_sum]`. Conclude with `Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)`.
-/
theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

/- English proof (translation)
Rewrite using `[idem, idem, map_sum, Finset.sum_mul_sum]`. Conclude with `Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)`.
-/
theorem idem_mul_conj {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q) :
    idem s * cA D (idem s') = 0 := by
  rw [idem, idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)

/- English proof (translation)
Take the linear combination `(d * d - 2 * d + 1) * h`.
-/
theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

/- English proof (translation)
Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`.

Introduce `hs`. Rewrite using `[Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]`. Establish `e1 : idem (insert a s) = idemAt a + idem s` using `Finset.sum_insert ha`. Rewrite using `[e1]`. Use `val_mul d _ _ ?_` and prove the remaining obligations.

Use `idem_mul_idem_of_disjoint h (s := {a}) (s' := s) (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs) (Finset.disjoint_singleton_left.2 ha)` as an intermediate fact. Rewrite `this` using `[show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _]`. Then use the resulting hypothesis.
-/
theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

/- English proof (translation)
Introduce `D V A _ t ht β Q' hQ' hsub κ _ hst hsupp`. Establish `he : idem Q' * idem Q' = idem Q'` using `idem_mul_self hQ'`. Establish `hce : idem Q' * cA D (idem Q') = 0` using `hQ'.isIdemSum.2`. Establish `hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ)`. Establish `hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ)` using `GlobalTheory.VecInv.isDetAt_detAt _ he V κ`.

Unfold `IsDetAt at hx`. Unfold `IsDetRoot`. Rewrite using `[hx]`. Conclude with `idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)`. Rewrite using `[detChar_eq ht.real hroot]`.

Establish `hR : Q' \ t.Q ⊆ Q'` using `Finset.sdiff_subset`. Establish `heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q)` using `idem_mul_self (hQ'.mono hR)`. Establish `hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P` using `fun P hP => (hQ'.isIdemAt (hsub hP)).1.1`. Establish `hsum : idem (Q' \ t.Q) + idem t.Q = idem Q'` using `Finset.sum_sdiff hsub`. Establish `hRQ : idem (Q' \ t.Q) * idem t.Q = 0` using `idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint`.

Establish `hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ * ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ`. Use `ext`. Rewrite using `[Units.val_mul, Units.coe_prod]`. Use `show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) * ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))`. Rewrite using `[Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)), prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]`.

Establish `hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1`. Use `ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR)) (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_` and prove the remaining obligations. Establish `hinf : infPart D (idem (Q' \ t.Q)) = 0`. Rewrite using `[idem, map_sum]`. Conclude with `Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))`.

Use `show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1`. Rewrite using `[map_add, map_mul, map_sub, map_one, hinf]`. Expand and normalize the polynomial expressions, which then agree. Establish `a1 : idem t.Q * idem (Q' \ t.Q) = 0` using `idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff`. Establish `a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0` using `idem_mul_conj hQ' hR hsub`.

Use `show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = idem t.Q + cA D (idem t.Q)`. Take the linear combination `((mt V κ).det - 1) * (a1 + a2)`. Rewrite using `[hsplit, map_mul, hw, one_mul, map_prod, ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]`. Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations. Use `ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _ (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm` and prove the remaining obligations.

Use `show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1`. Take the linear combination `(1 - (mt V κ).det) * hPi P.1 P.2`.
-/
theorem detChar_eq_prod_res : ∀ {D : D7} {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A), t.Good →
    ∀ (β : GL (Fin V.rank) (Lev.EAf D)) {Q' : Finset (Pl D.host.E)}, SplitSet Q' → t.Q ⊆ Q' → ∀ {κ : GA D V},
    κ ∈ GfC V → Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ →
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  intro D V A _ t ht β Q' hQ' hsub κ _ hst hsupp
  have he : idem Q' * idem Q' = idem Q' := idem_mul_self hQ'
  have hce : idem Q' * cA D (idem Q') = 0 := hQ'.isIdemSum.2
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := by
    have hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := GlobalTheory.VecInv.isDetAt_detAt _ he V κ
    unfold IsDetAt at hx
    unfold IsDetRoot
    rw [hx]
    exact idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)
  rw [detChar_eq ht.real hroot]
  have hR : Q' \ t.Q ⊆ Q' := Finset.sdiff_subset
  have heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q) := idem_mul_self (hQ'.mono hR)
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (hQ'.isIdemAt (hsub hP)).1.1
  have hsum : idem (Q' \ t.Q) + idem t.Q = idem Q' := Finset.sum_sdiff hsub
  have hRQ : idem (Q' \ t.Q) * idem t.Q = 0 := idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint
  have hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ *
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.val_mul, Units.coe_prod]
    show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) *
      ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]
  have hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1 := by
    refine ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR))
      (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_
    · have hinf : infPart D (idem (Q' \ t.Q)) = 0 := by
        rw [idem, map_sum]
        exact Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))
      show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1
      rw [map_add, map_mul, map_sub, map_one, hinf]
      ring
    · have a1 : idem t.Q * idem (Q' \ t.Q) = 0 := idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff
      have a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0 := idem_mul_conj hQ' hR hsub
      show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) =
        idem t.Q + cA D (idem t.Q)
      linear_combination ((mt V κ).det - 1) * (a1 + a2)
  rw [hsplit, map_mul, hw, one_mul, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

end GlobalTheory.TwistDetStab

end
