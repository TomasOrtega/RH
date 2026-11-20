import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKeyPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceEqSumPlaces
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.PoincareInHH.Cut
open Matrix

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Rewrite using `[← toV_crd X y, ← toV_crd X y', h]`.
-/
theorem crd_injective' {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  rw [← toV_crd X y, ← toV_crd X y', h]

/- English proof (translation)
Use extensionality with `y`. Conclude with `crd_injective' X (by rw [h3, matE_crdC])`.
-/
theorem eq_matEC {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {M : GL (Fin X.B.I.n) X.B.I.E}
    (h3 : ∀ y, X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) : n = matEC X M := by
  ext y
  exact crd_injective' X (by rw [h3, matE_crdC])

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hn`. Establish `hgtop : Formalism.HermitianLatticesTheory.gmap n (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[Submodule.map_top]`.

Conclude with `LinearMap.range_eq_top.2 n.surjective`. Conclude with `nLamNinf_holds D X u ⊤ x n hx ⟨⟨hn.1, hgtop⟩, hn.2.1, hn.2.2⟩`. Introduce `hν1`. Take `⟨M, hM, hinf, -, h3⟩` from `hx`. Establish `hn` using `eq_matEC X h3`.

Substitute `hn` using the available equality. Take `⟨v⟩ : Nonempty (InfinitePlace X.B.I.F)` from `inferInstance`. Establish `hGv : ∀ y, uMat (x.1 v) *ᵥ Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v y = Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y)`. Introduce `y`. Rewrite using `[Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, hinf v]`.

Conclude with `rv_mulVec X v _ y`. Establish `hsub : ∀ y, (uMat (x.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y)` using `fun y => tr_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _ hGv y`. Establish `hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y`. Introduce `y`. Rewrite using `[crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]`.

Establish `hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)), ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) → matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T)`. Introduce `y T hy`. Rewrite `hy` using `[← hcrdn]`. Use `toV_span X hy` as an intermediate fact. Rewrite `this` using `[toV_crd]`. Then use the resulting hypothesis.

Establish `hInN` using `hν1 v`. Use `⟨matE_isomC X M hM, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Express the relevant statement in the definitionally equal form `x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})`.

Rewrite `hx`, the goal using `[X.Fu_e]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Establish `h1` using `hInN.1.1 a`.

Rewrite `h1` using `[hsub]`. Establish `h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈ Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1}))`. Rewrite using `[Set.image_image]`. Conclude with `h1`. Establish `h3` using `rv_desc X v _ _ h2`.

Establish `h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < j})`. Use `Submodule.span_mono (Set.image_mono fun b hb => ?_) h3` and prove the remaining obligations. Establish `: a.1 < j + 1` using `ha`. Use `show b.1 < j`. Establish `: b.1 < a.1` using `hb`.

Use linear arithmetic over natural numbers and integers. Conclude with `hback _ _ h4`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add, add_sub_add_comm]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ ha`. Introduce `x hx`.

Express the relevant statement in the definitionally equal form `x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)`. Rewrite `hx`, the goal using `[X.Fu_e]`. Establish `hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0`. Introduce `a`.

Rewrite using `[hJ_rv]`. Establish `h0 : hE X (X.eR a) (X.crd x) = 0`. Apply `X.ιE.injective` to reduce the goal to its premises. Rewrite using `[iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]`. Conclude with `(mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)`.

Rewrite using `[h0, map_zero]`. Establish `h1` using `hInN.2 _ hzero`. Rewrite `h1` using `[hsub]`. Establish `huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ` using `Set.eq_univ_of_forall fun b => b.2`. Establish `h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈ Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS}))`.

Rewrite using `[Set.image_image]`. Conclude with `h1`. Establish `h3` using `hback x _ (rv_desc X v _ _ h2)`. Rewrite `h3` using `[huniv, Set.image_univ]`. Then use the resulting hypothesis.
-/
theorem nrat_iff (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) :
    n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u := by
  constructor
  · intro hn
    have hgtop : Formalism.HermitianLatticesTheory.gmap n (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
      unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 n.surjective
    exact nLamNinf_holds D X u ⊤ x n hx ⟨⟨hn.1, hgtop⟩, hn.2.1, hn.2.2⟩
  · intro hν1
    obtain ⟨M, hM, hinf, -, h3⟩ := hx
    have hn := eq_matEC X h3
    subst hn
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (x.1 v) *ᵥ Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v y = Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (x.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hν1 v
    refine ⟨matE_isomC X M hM, ?_, ?_⟩
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add, add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.NonRelPf

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Unfold `Formalism.L2.SG.PairVal.sgUp`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by omega)]`.

Both sides reduce to the same expression.
-/
theorem sgUp_eq {E : Type} [Field E] [NumberField E] {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.L2.SG.PairVal.sgUp A = ∑ a : Fin r, A a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by omega)]
  rfl

/- English proof (translation)
Establish `e : nxt X.eX (X.zu u) a = frame (lf D (X.Fu u)) a.succ` using `by show _ = (X.Fu u).fvec a.succ`. Rewrite using `[fvec_succ, X.Fu_e, X.flagZVector]`. Rewrite using `[e, hA, map_sum, Fin.sum_univ_castSucc]`. Establish `h1 : ∀ b : Fin D.R.rS, frame (lf D (X.Fu u)) b.castSucc = X.eX b`. Introduce `b`.

Use `show (X.Fu u).fvec b.castSucc = _`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]`. Establish `h2 : frame (lf D (X.Fu u)) (Fin.last D.R.rS) = X.zu u` using `by show (X.Fu u).fvec (Fin.last _) = _`. Simplify using `only [FlagG.fvec, Fin.snoc_last, X.flagZVector]`. Simplify using `only [map_smul, smul_eq_mul, h1, h2, hTfe, (X.zu_orth u a).2, mul_zero, add_zero, mul_ite, mul_one]`.

Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem root_entry (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) (a : Fin D.R.rS) :
    (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = A a.castSucc a.succ := by
  have e : nxt X.eX (X.zu u) a = frame (lf D (X.Fu u)) a.succ := by
    show _ = (X.Fu u).fvec a.succ
    rw [fvec_succ, X.Fu_e, X.flagZVector]
  rw [e, hA, map_sum, Fin.sum_univ_castSucc]
  have h1 : ∀ b : Fin D.R.rS, frame (lf D (X.Fu u)) b.castSucc = X.eX b := by
    intro b
    show (X.Fu u).fvec b.castSucc = _
    simp only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
  have h2 : frame (lf D (X.Fu u)) (Fin.last D.R.rS) = X.zu u := by
    show (X.Fu u).fvec (Fin.last _) = _
    simp only [FlagG.fvec, Fin.snoc_last, X.flagZVector]
  simp only [map_smul, smul_eq_mul, h1, h2, hTfe, (X.zu_orth u a).2, mul_zero, add_zero, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp

/- English proof (translation)
Rewrite using `[psi_rat X u hx]`. Apply the tactic sequence `simp only [root_entry X u n A hA]`. Establish `hs : ∀ v, (∑ a : Fin D.R.rS, (Φ X v (A a.castSucc a.succ) + star (Φ X v (A a.castSucc a.succ)))) = X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)) + star (X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)))`. Introduce `v`. Rewrite using `[Finset.sum_add_distrib, ← star_sum, ← Φ_sum, ← sgUp_eq]`.

Both sides reduce to the same expression. Simplify using `only [hs]`. Rewrite using `[Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm _), RingEquiv.apply_symm_apply, X.g_eq]`. Both sides reduce to the same expression.
-/
theorem psi_eq (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A) := by
  rw [psi_rat X u hx]
  simp only [root_entry X u n A hA]
  have hs : ∀ v, (∑ a : Fin D.R.rS, (Φ X v (A a.castSucc a.succ) + star (Φ X v (A a.castSucc a.succ)))) =
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)) +
        star (X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A))) := by
    intro v
    rw [Finset.sum_add_distrib, ← star_sum, ← Φ_sum, ← sgUp_eq]
    rfl
  simp only [hs]
  rw [Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm _), RingEquiv.apply_symm_apply, X.g_eq]
  rfl

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

/- English proof (translation)
Introduce `D X`. Use `⟨fun γ hγ => ?_, fun x y γ δ hx hy => ?_, fun u x n hx => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `Formalism.L2.SG.Pf.ratPt_holds D X γ hγ`. Conclude with `⟨x, hx, fun y hy => Formalism.L2.SG.TermOp.Vanish.ratLink_unique X hy hx⟩`. Conclude with `⟨Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx, Formalism.L2.SG.Pf.IdMeet.lin_eq_of_fst X hx hy⟩`.

Conclude with `⟨nrat_iff X u hx, fun _ A hA => psi_eq X u hx A hA⟩`.
-/
theorem ratLink_points : ∀ (D : D7) (X : HidaSetting D), (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃! x : X.B.I.GA, RatLink X x γ) ∧ (∀ x y γ δ, RatLink X x γ → RatLink X y δ → RatLink X (x * y) (γ * δ) ∧ RatLink X x⁻¹ γ⁻¹ ∧ (x.1 = y.1 → γ = δ)) ∧ ∀ (u : D.what₂.Word) x n, RatLink X x n → (n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u) ∧ (n ∈ NRat (lf D (X.Fu u)) → ∀ A : Formalism.L2.SG.PairVal.MatR D, (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) → X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A)) := by
  intro D X
  refine ⟨fun γ hγ => ?_, fun x y γ δ hx hy => ?_, fun u x n hx => ?_⟩
  · obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X γ hγ
    exact ⟨x, hx, fun y hy => Formalism.L2.SG.TermOp.Vanish.ratLink_unique X hy hx⟩
  · exact ⟨Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx,
      Formalism.L2.SG.Pf.IdMeet.lin_eq_of_fst X hx hy⟩
  · exact ⟨nrat_iff X u hx, fun _ A hA => psi_eq X u hx A hA⟩

end GlobalTheory.RatIsomPoint
