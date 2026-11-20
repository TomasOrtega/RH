import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLagrangianTransverseInOpenOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjDoublingIsotropicUnipotentMemSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryNormalisesIsotropicUnipotentRadiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryKeepsIsotropicFrameOfSiegelStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

/- English proof (translation)
Introduce `D V γ hγ hopen`. Take `⟨g, hg, -, hγi⟩` from `exists_rat (dblSp V) hγ`. Establish `hgi : g⁻¹ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (dblSp V).gram` using `inv_mem hg`. Use `set γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E := (g⁻¹).1 with hγidef`. Establish `hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi = dblGram finSumFinEquiv V.gram`.

Establish `h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * (dblSp V).gram * γi = (dblSp V).gram` using `hgi`. Rewrite `h` using `[gram_hdbl]`. Then use the resulting hypothesis. Use `set Qd := diagSnd γi with hQd`. Use `set P := leviMat finSumFinEquiv γi with hP`. Establish `hinj : ∀ x, P *ᵥ x = 0 → Qd *ᵥ x = 0 → x = 0`.

Introduce `x h1 h2`. Establish `h3 : γi *ᵥ pairVec finSumFinEquiv x x = 0`. Rewrite using `[mulVec_pairVec_diag, ← hP, ← hQd, h1, h2]`. Use function extensionality and compare the values at `j`. Simplify using `[pairVec, Sum.elim_zero_zero]`.

Establish `h4 : (g.1 * γi) *ᵥ pairVec finSumFinEquiv x x = 0` using `by rw [← mulVec_mulVec, h3, mulVec_zero]`. Rewrite `h4` using `[hγidef, Units.mul_inv, one_mulVec]`. Use function extensionality and compare the values at `i`. Use `congrFun h4 (finSumFinEquiv (.inl i))` as an intermediate fact. Rewrite `this` using `[pairVec_inl]`. Then use the resulting hypothesis.

Distinguish the cases in `hk : ∀ x, Qd *ᵥ x = 0 → x = 0`. Conclude with `absurd (GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit D V γ hγ γi hγi hk) hopen`. Use `push Not at hk`. Take `⟨x0, hx0, hx0ne⟩` from `hk`. Set `W` to `LinearMap.ker Qd.mulVecLin`.

Set `b` to `Module.finBasis D.host.E W`. Set `K : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E W)) D.host.E` to `Matrix.of fun i j => (b j : Fin V.rank → D.host.E) i`. Establish `hKv : ∀ y, K *ᵥ y = ((∑ j, y j • b j : W) : Fin V.rank → D.host.E)`. Introduce `y`. Use function extensionality and compare the values at `i`.

Simplify using `[K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]`. Establish `hbQ : ∀ j, Qd *ᵥ (b j : Fin V.rank → D.host.E) = 0` using `fun j => (b j).2`. Establish `hQK : Qd * K = 0`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (hbQ j) i` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mul_apply, K, Matrix.of_apply, Matrix.zero_apply]`. Conclude with `this`. Establish `hspan : ∀ x, Qd *ᵥ x = 0 → ∃ y, x = K *ᵥ y`. Introduce `x hx`.

Use `⟨b.repr ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hKv, b.sum_repr]`. Establish `hiso : IsIsoFrame V (P * K)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x0, hx0⟩, fun h => hx0ne (congrArg Subtype.val h)⟩`.

Use `(Matrix.mulVec_injective_iff (M := P * K)).1 ?_` and prove the remaining obligations. Introduce `c c' hc`. Rewrite `hc`, the goal using `[← sub_eq_zero]`. Rewrite `hc` using `[← mulVec_sub, ← mulVec_mulVec]`. Establish `h1 : K *ᵥ (c - c') = 0` using `hinj _ hc (by rw [mulVec_mulVec, hQK, zero_mulVec])`.

Rewrite `h1` using `[hKv]`. Establish `h2 : (∑ j, (c - c') j • b j : W) = 0` using `Subtype.ext h1`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 j`. Establish `hI` using `isotropic_diag hU`.

Rewrite `hI` using `[← hP, ← hQd]`. Rewrite using `[Formalism.UG.cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Qd * K) * V.gram * (Qd * K) := by`.

Rewrite using `[hI, Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hQK]; simp [Formalism.UG.cT]`. Use `⟨_, P * K, hiso, GlobalTheory.T.conj_doubling_isotropic_unipotent_mem_siegel D V γ hγ γi hγi _ K hQK hiso, ?_⟩` and prove the remaining obligations. Introduce `δ hδ hs n hn`.

Take `⟨d, -, hδm, -⟩` from `exists_rat V hδ`. Take `⟨G, hG, hGe⟩` from `GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel D V γ hγ γi hγi _ K hQK hspan hiso δ hδ d.1 hδm hs`. Conclude with `GlobalTheory.T.rational_isometry_normalises_isotropic_unipotent_radical D V _ (P * K) δ hδ d.1 hδm G hG hGe n hn`.
-/
theorem offOpen : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V γ hγ hopen
  obtain ⟨g, hg, -, hγi⟩ := exists_rat (dblSp V) hγ
  have hgi : g⁻¹ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (dblSp V).gram := inv_mem hg
  set γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E := (g⁻¹).1 with hγidef
  have hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * (dblSp V).gram * γi = (dblSp V).gram := hgi
    rwa [gram_hdbl] at h
  set Qd := diagSnd γi with hQd
  set P := leviMat finSumFinEquiv γi with hP
  have hinj : ∀ x, P *ᵥ x = 0 → Qd *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    have h3 : γi *ᵥ pairVec finSumFinEquiv x x = 0 := by
      rw [mulVec_pairVec_diag, ← hP, ← hQd, h1, h2]
      funext j; simp [pairVec, Sum.elim_zero_zero]
    have h4 : (g.1 * γi) *ᵥ pairVec finSumFinEquiv x x = 0 := by rw [← mulVec_mulVec, h3, mulVec_zero]
    rw [hγidef, Units.mul_inv, one_mulVec] at h4
    funext i
    have := congrFun h4 (finSumFinEquiv (.inl i))
    rwa [pairVec_inl] at this
  by_cases hk : ∀ x, Qd *ᵥ x = 0 → x = 0
  · exact absurd (GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit D V γ hγ γi hγi hk) hopen
  push Not at hk
  obtain ⟨x0, hx0, hx0ne⟩ := hk
  let W := LinearMap.ker Qd.mulVecLin
  let b := Module.finBasis D.host.E W
  let K : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E W)) D.host.E :=
    Matrix.of fun i j => (b j : Fin V.rank → D.host.E) i
  have hKv : ∀ y, K *ᵥ y = ((∑ j, y j • b j : W) : Fin V.rank → D.host.E) := by
    intro y; funext i
    simp [K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
  have hbQ : ∀ j, Qd *ᵥ (b j : Fin V.rank → D.host.E) = 0 := fun j => (b j).2
  have hQK : Qd * K = 0 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hbQ j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, K, Matrix.of_apply, Matrix.zero_apply]
    exact this
  have hspan : ∀ x, Qd *ᵥ x = 0 → ∃ y, x = K *ᵥ y := by
    intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    rw [hKv, b.sum_repr]
  have hiso : IsIsoFrame V (P * K) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x0, hx0⟩, fun h => hx0ne (congrArg Subtype.val h)⟩
    · refine (Matrix.mulVec_injective_iff (M := P * K)).1 ?_
      intro c c' hc
      rw [← sub_eq_zero] at hc ⊢
      rw [← mulVec_sub, ← mulVec_mulVec] at hc
      have h1 : K *ᵥ (c - c') = 0 := hinj _ hc (by rw [mulVec_mulVec, hQK, zero_mulVec])
      rw [hKv] at h1
      have h2 : (∑ j, (c - c') j • b j : W) = 0 := Subtype.ext h1
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 j
    · have hI := isotropic_diag hU
      rw [← hP, ← hQd] at hI
      rw [Formalism.UG.cT_mul]
      calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P *
            V.gram * (P * K)
          = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K *
            (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P) * K := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Qd * K) * V.gram * (Qd * K) := by
            rw [hI, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQK]; simp [Formalism.UG.cT]
  refine ⟨_, P * K, hiso, GlobalTheory.T.conj_doubling_isotropic_unipotent_mem_siegel D V γ hγ γi hγi _ K hQK hiso, ?_⟩
  intro δ hδ hs n hn
  obtain ⟨d, -, hδm, -⟩ := exists_rat V hδ
  obtain ⟨G, hG, hGe⟩ := GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel D V γ hγ γi hγi _ K hQK hspan hiso δ hδ d.1 hδm hs
  exact GlobalTheory.T.rational_isometry_normalises_isotropic_unipotent_radical D V _ (P * K) δ hδ d.1 hδm G hG hGe n hn

end GlobalTheory.Core.Rk.Dich

end
