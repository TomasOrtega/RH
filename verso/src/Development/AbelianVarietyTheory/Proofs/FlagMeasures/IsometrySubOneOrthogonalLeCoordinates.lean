import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Simplify using `[GlobalTheory.SgAlg.eOf, Pc]`.
-/
theorem eOf_Pc_apply (u : D.what₂.Word) (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    GlobalTheory.SgAlg.eOf (Pc X u) i a = crdH X (X.eX a) i := by
  simp [GlobalTheory.SgAlg.eOf, Pc]

/- English proof (translation)
Use `show Submodule.span D.host.E (Set.range (X.Fu u).e) = _`. Rewrite using `[X.Fu_e]`.
-/
theorem Xsp_Fu_eq_span (u : D.what₂.Word) :
    Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

/- English proof (translation)
Establish `hcol : GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c = ∑ a, c a • crdH X (X.eX a)`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, eOf_Pc_apply, Finset.sum_apply, mul_comm]`. Rewrite using `[hcol, map_sum]`. Simplify using `only [map_smul, vecOf_crdH]`.
-/
theorem vecOf_eOf_mulVec (u : D.what₂.Word) (c : Fin D.R.rS → D.host.E) :
    vecOf X (GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) = ∑ a, c a • X.eX a := by
  have hcol : GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c = ∑ a, c a • crdH X (X.eX a) := by
    ext i
    simp [Matrix.mulVec, dotProduct, eOf_Pc_apply, Finset.sum_apply, mul_comm]
  rw [hcol, map_sum]
  simp only [map_smul, vecOf_crdH]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Use `conv_rhs => rw [← vecOf_crdH X (X.eX a), hT_vecOf]`. Simplify using `only [GlobalTheory.SgAlg.form, GlobalTheory.SgAlg.cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, eOf_Pc_apply]`.
-/
theorem cT_eOf_mulVec_apply (u : D.what₂.Word) (v : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) (a : Fin D.R.rS) :
    ((GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v) a
      = (VS D).hT (X.eX a) (vecOf X v) := by
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← vecOf_crdH X (X.eX a), hT_vecOf]
  simp only [GlobalTheory.SgAlg.form, GlobalTheory.SgAlg.cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, eOf_Pc_apply]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`. Conclude with `h _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `h x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `h a`. Consider the case `zero => simp`.

Consider the case `add x z _ _ hx hz => simp [hx, hz]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem mem_orth_span_iff (y : (VS D).V) :
    y ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) ↔
      ∀ a, (VS D).hT (X.eX a) y = 0 := by
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => simp
    | add x z _ _ hx hz => simp [hx, hz]
    | smul c x _ hx => simp [hx]

/- English proof (translation)
Introduce `D X u n γ hγ`. Establish `inj : Function.Injective (vecOf X)` using `fun a b h => by`. Simplify `congrArg (crdH X) h` using `[crdH_vecOf]`. Establish `hperp : ∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 ↔ ∀ a, (VS D).hT (X.eX a) (vecOf X v) = 0`. Introduce `v`.

Prove the components needed by the constructor for the conclusion. Introduce `h a`. Establish `h'` using `congrFun h a`. Rewrite `h'` using `[cT_eOf_mulVec_apply]`. Then use the resulting hypothesis. Introduce `h`.

Use function extensionality and compare the values at `a`. Rewrite using `[cT_eOf_mulVec_apply]`. Conclude with `h a`. Establish `himg : ∀ v c, (γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c ↔ n (vecOf X v) - vecOf X v = ∑ a, c a • X.eX a)`. Introduce `v c`.

Rewrite using `[← vecOf_eOf_mulVec X u c, n_vecOf hγ, ← map_sub]`. Conclude with `inj.eq_iff.symm`. Rewrite using `[Xsp_Fu_eq_span X u]`. Prove the components needed by the constructor for the conclusion. Introduce `H x hx`.

Rewrite `hx` using `[mem_orth_span_iff X x]`. Take `⟨c, hc⟩` from `H (crdH X x) ((hperp _).2 (by simpa [vecOf_crdH] using hx))`. Rewrite `hc` using `[himg, vecOf_crdH]`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Conclude with `⟨c, hc.symm⟩`.

Introduce `H v hv`. Establish `hx : vecOf X v ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX))` using `(mem_orth_span_iff X (vecOf X v)).2 ((hperp v).1 hv)`. Establish `hm` using `H _ hx`. Rewrite `hm` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hm`.

Conclude with `⟨c, (himg v c).2 hc.symm⟩`.
-/
theorem orth_cond_iff_coord : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  intro D X u n γ hγ
  have inj : Function.Injective (vecOf X) := fun a b h => by
    simpa [crdH_vecOf] using congrArg (crdH X) h
  have hperp : ∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 ↔
      ∀ a, (VS D).hT (X.eX a) (vecOf X v) = 0 := by
    intro v
    constructor
    · intro h a
      have h' := congrFun h a
      rwa [cT_eOf_mulVec_apply] at h'
    · intro h
      funext a
      rw [cT_eOf_mulVec_apply]
      exact h a
  have himg : ∀ v c, (γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c ↔
      n (vecOf X v) - vecOf X v = ∑ a, c a • X.eX a) := by
    intro v c
    rw [← vecOf_eOf_mulVec X u c, n_vecOf hγ, ← map_sub]
    exact inj.eq_iff.symm
  rw [Xsp_Fu_eq_span X u]
  constructor
  · intro H x hx
    rw [mem_orth_span_iff X x] at hx
    obtain ⟨c, hc⟩ := H (crdH X x) ((hperp _).2 (by simpa [vecOf_crdH] using hx))
    rw [himg, vecOf_crdH] at hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, hc.symm⟩
  · intro H v hv
    have hx : vecOf X v ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) :=
      (mem_orth_span_iff X (vecOf X v)).2 ((hperp v).1 hv)
    have hm := H _ hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, (himg v c).2 hc.symm⟩

end GlobalTheory.CovDomGrp
