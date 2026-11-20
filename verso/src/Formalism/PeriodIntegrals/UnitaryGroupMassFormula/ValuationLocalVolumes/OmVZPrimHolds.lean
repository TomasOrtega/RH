import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FrameVectorMemBaseLattice

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[← X.flagZVector u']`. Conclude with `(X.Fu u').z_orth a`.

Consider the case `zero => simp`. Consider the case `add x y _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c x _ h => simp [h]`.
-/
theorem zu_orth_X (y : (VS D).V) (hy : y ∈ (X.Fu u').X) : (VS D).hT y (X.zu u') = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← X.flagZVector u']
    exact (X.Fu u').z_orth a
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul c x _ h => simp [h]

/- English proof (translation)
Establish `hL0 : X.ιE g • X.zu u' ∈ (VS D).L0`. Establish `h` using `(X.L_eq _).1 hg`. Establish `e : (∑ i, X.ιE ((g • crdOf X.B.I X.ιE X.bas (X.zu u')) i) • X.bas i) = X.ιE g • X.zu u'`. Simplify using `only [Pi.smul_apply, smul_eq_mul, crdOf, map_mul, RingEquiv.apply_symm_apply, mul_smul]`. Rewrite using `[← Finset.smul_sum, X.bas.sum_repr]`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `horth : X.ιE g • X.zu u' ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u').X`. Simplify using `only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker, map_smul, smul_eq_mul]`. Introduce `x hx`. Rewrite using `[zu_orth_X X u' x hx, mul_zero]`.

Take `⟨o, ho⟩` from `(X.Fu_fixed u').2.2.2.2 (X.ιE g) (by`. Express the relevant statement in the definitionally equal form `X.ιE g • (X.Fu u').z ∈ _`. Rewrite using `[X.flagZVector u']`. Unfold `Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep`. Conclude with `Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩)`.

Establish `e : g = X.ιE.symm (o : D.host.E)` using `by rw [ho, RingEquiv.symm_apply_apply]`. Rewrite using `[e]`. Conclude with `(RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom`.
-/
theorem glob_prim (g : X.B.I.E) (hg : g • crdOf X.B.I X.ιE X.bas (X.zu u') ∈ X.B.I.L) : IsIntegral ℤ g := by
  have hL0 : X.ιE g • X.zu u' ∈ (VS D).L0 := by
    have h := (X.L_eq _).1 hg
    have e : (∑ i, X.ιE ((g • crdOf X.B.I X.ιE X.bas (X.zu u')) i) • X.bas i) = X.ιE g • X.zu u' := by
      simp only [Pi.smul_apply, smul_eq_mul, crdOf, map_mul, RingEquiv.apply_symm_apply, mul_smul]
      rw [← Finset.smul_sum, X.bas.sum_repr]
    rwa [e] at h
  have horth : X.ιE g • X.zu u' ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u').X := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker, map_smul, smul_eq_mul]
    intro x hx
    rw [zu_orth_X X u' x hx, mul_zero]
  obtain ⟨o, ho⟩ := (X.Fu_fixed u').2.2.2.2 (X.ιE g) (by
    change X.ιE g • (X.Fu u').z ∈ _
    rw [X.flagZVector u']
    unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩)
  have e : g = X.ιE.symm (o : D.host.E) := by rw [ho, RingEquiv.symm_apply_apply]
  rw [e]
  exact (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom

/- English proof (translation)
Establish `hs : scl X v (zi (D` using `D)) = 1 := by`. Simplify using `only [scl, zi, Fin.append_left]`. Conclude with `alp_last v D.R.rS`. Establish `h1 : yTup X u' v (zi (D` using `D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _`. Rewrite using `[hs]`. Simplify using `only [sc, ← Algebra.TensorProduct.one_def, one_mul]`. Both sides reduce to the same expression. Establish `h2 : hv X u' (zi (D` using `D)) = X.zu u' := by simp only [hv, zi, Fin.append_left, Fin.snoc_last]`.

Rewrite using `[h1, tupH_eq, h2]`.
-/
theorem yTup_zi (v : PlX X) :
    yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (X.zu u')) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  have h2 : hv X u' (zi (D := D)) = X.zu u' := by simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  rw [h1, tupH_eq, h2]

/- English proof (translation)
Introduce `v _ c hc`. Use `set z := crdOf X.B.I X.ιE X.bas (X.zu u') with hz_def`. Establish `hz : z ∈ abelian₂ X` using `crdOf_mem X (frame_vector_mem_base_lattice X u')`. Rewrite `hc` using `[yTup_zi]`. Take `⟨c', w, hw, hcw⟩` from `approx v 1 one_ne_zero c`.

Establish `hw' : c - inclR (F` using `X.B.I.F) (Fv X.B.I.F v) c' = w := by rw [hcw]; simp`. Establish `h1 : ratV (F` using `X.B.I.F) (Fv X.B.I.F v) (c' • z) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by`. Establish `e : ratV (F` using `X.B.I.F) (Fv X.B.I.F v) (c' • z) = c • ratV (F := X.B.I.F) (Fv X.B.I.F v) z - w • ratV (F := X.B.I.F) (Fv X.B.I.F v) z := by`. Use function extensionality and compare the values at `i`. Simplify using `only [ratV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul]`.

Rewrite using `[← hw']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ hc (lat_oev_smul X v hw (Submodule.subset_span ⟨z, hz, rfl⟩))`. Establish `hpair : ∀ l ∈ X.B.I.L, inclR (F` using `X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) ∈ OEv (E := X.B.I.E) v := by`.

Introduce `l hl`. Establish `h2 : inclR (F` using `X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) = hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l) (ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z)) := (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, c' • z] 0 1). …`. Rewrite using `[h2]`. Conclude with `omVSD_fwd X v (Submodule.subset_span ⟨l, hl, rfl⟩) h1`. Take `⟨t, ht, htL⟩` from `locGlob X v _ hpair`.

Establish `hg : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c')` using `glob_prim X u' _ (by rw [mul_smul]; exact htL)`. Take `⟨hinv, hne⟩` from `unit_of_notMem v t ht`. Establish `hc' : inclR (F` using `X.B.I.F) (Fv X.B.I.F v) c' ∈ OEv (E := X.B.I.E) v := by`. Establish `e : inclR (F` using `X.B.I.F) (Fv X.B.I.F v) c' = (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') := by show inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = (algebraMap X.B. …`. Rewrite using `[map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (incl_mem v (⟨_, (mem_integralClosure_iff ℤ _).2 hg⟩ : 𝓞 X.B.I.E))`. Establish `e2 : c = w + inclR (F` using `X.B.I.F) (Fv X.B.I.F v) c' := by rw [← hw']; ring`. Rewrite using `[e2]`. Conclude with `Submodule.add_mem _ hw hc'`.
-/
theorem omVZPrim_holds : OmVZPrim X u' := by
  intro v _ c hc
  set z := crdOf X.B.I X.ιE X.bas (X.zu u') with hz_def
  have hz : z ∈ abelian₂ X := crdOf_mem X (frame_vector_mem_base_lattice X u')
  rw [yTup_zi] at hc
  obtain ⟨c', w, hw, hcw⟩ := approx v 1 one_ne_zero c
  have hw' : c - inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = w := by rw [hcw]; simp
  have h1 : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have e : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) =
        c • ratV (F := X.B.I.F) (Fv X.B.I.F v) z - w • ratV (F := X.B.I.F) (Fv X.B.I.F v) z := by
      funext i
      simp only [ratV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul]
      rw [← hw']; ring
    rw [e]
    exact Submodule.sub_mem _ hc (lat_oev_smul X v hw (Submodule.subset_span ⟨z, hz, rfl⟩))
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z)) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, c' • z] 0 1).symm
    rw [h2]
    exact omVSD_fwd X v (Submodule.subset_span ⟨l, hl, rfl⟩) h1
  obtain ⟨t, ht, htL⟩ := locGlob X v _ hpair
  have hg : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') :=
    glob_prim X u' _ (by rw [mul_smul]; exact htL)
  obtain ⟨hinv, hne⟩ := unit_of_notMem v t ht
  have hc' : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' ∈ OEv (E := X.B.I.E) v := by
    have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') := by
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = (algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c')
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (incl_mem v (⟨_, (mem_integralClosure_iff ℤ _).2 hg⟩ : 𝓞 X.B.I.E))
  have e2 : c = w + inclR (F := X.B.I.F) (Fv X.B.I.F v) c' := by rw [← hw']; ring
  rw [e2]
  exact Submodule.add_mem _ hw hc'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
