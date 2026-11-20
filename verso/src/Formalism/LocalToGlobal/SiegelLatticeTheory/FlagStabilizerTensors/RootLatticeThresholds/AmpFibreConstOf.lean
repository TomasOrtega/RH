import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish
open Matrix

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

/- English proof (translation)
Use extensionality with `ξ`. Rewrite using `[_root_.smul_apply, ContinuousLinearMap.comp_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, LinearIsometryEquiv.inner_map_eq_flip, smul_smul]`. Both sides reduce to the same expression.
-/
theorem rk1_smul_right (v : V) (b : ℂ) (B : V' ≃ₗᵢ[ℂ] V') (w : V') :
    rk1 v (b • B w) = conj b • (rk1 v w).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V') := by
  ext ξ
  rw [_root_.smul_apply, ContinuousLinearMap.comp_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply,
    Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, LinearIsometryEquiv.inner_map_eq_flip, smul_smul]
  rfl

variable {G : Type*} [Group G] [MeasurableSpace G]

/- English proof (translation)
Establish `hx : ∀ x, rk1 (Ph x) (Ph' ((γ * t)⁻¹ * x)) = conj b • (ContinuousLinearEquiv.arrowCongr B.toContinuousLinearEquiv (ContinuousLinearEquiv.refl ℂ V)) (rk1 (Ph x) (Ph' (γ⁻¹ * x)))`. Introduce `x`. Rewrite using `[_root_.mul_inv_rev, mul_assoc, hB, rk1_smul_right]`. Both sides reduce to the same expression. Unfold `Formalism.L2.SG.TermOp.OO`.

Repeatedly rewrite using `[hx]`. Rewrite using `[integral_smul, ContinuousLinearEquiv.integral_comp_comm]`. Both sides reduce to the same expression.
-/
theorem OO_right [CompleteSpace V] (μ : Measure G) (Ω : Set G) (Ph : G → V) (Ph' : G → V') (γ t : G) (b : ℂ)
    (B : V' ≃ₗᵢ[ℂ] V') (hB : ∀ x, Ph' (t⁻¹ * x) = b • B (Ph' x)) :
    OO μ Ω Ph Ph' (γ * t) = conj b • (OO μ Ω Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V') := by
  have hx : ∀ x, rk1 (Ph x) (Ph' ((γ * t)⁻¹ * x)) =
      conj b • (ContinuousLinearEquiv.arrowCongr B.toContinuousLinearEquiv
        (ContinuousLinearEquiv.refl ℂ V)) (rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    rw [_root_.mul_inv_rev, mul_assoc, hB, rk1_smul_right]
    rfl
  unfold Formalism.L2.SG.TermOp.OO
  simp_rw [hx]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm]
  rfl

/- English proof (translation)
Unfold `Formalism.L2.SG.TermOp.OO`. Simplify using the standard rewrite rules.
-/
theorem OO_empty [CompleteSpace V] (μ : Measure G) (Ph : G → V) (Ph' : G → V') (γ : G) :
    OO μ ∅ Ph Ph' γ = 0 := by
  unfold Formalism.L2.SG.TermOp.OO
  simp

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']

/- English proof (translation)
Rewrite using `[PiLp.norm_sq_eq_of_L2]`. Both sides reduce to the same expression.
-/
theorem norm_hsEmb_sq' (A : V' →L[ℂ] V) : ‖Formalism.L2.SG.PackageTie.hsEmb A‖ ^ 2 = Formalism.L2.SG.RealObj.hs2 A := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/- English proof (translation)
Rewrite using `[← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_hsEmb_sq', norm_hsEmb_sq', Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, hb, one_pow, one_mul]`. Conclude with `Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right A B.symm`.
-/
theorem norm_hsEmb_right (A : V' →L[ℂ] V) (b : ℂ) (hb : ‖b‖ = 1) (B : V' ≃ₗᵢ[ℂ] V') :
    ‖Formalism.L2.SG.PackageTie.hsEmb (b • A.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))‖ =
      ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_hsEmb_sq', norm_hsEmb_sq',
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, hb, one_pow, one_mul]
  exact Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right A B.symm

/- English proof (translation)
Rewrite using `[map_smul, norm_smul, hb, one_mul]`.
-/
theorem norm_hsEmb_smul (A : V' →L[ℂ] V) (b : ℂ) (hb : ‖b‖ = 1) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (b • A)‖ = ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  rw [map_smul, norm_smul, hb, one_mul]

end Gen

section Amp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem ratLink_congr {x : X.B.I.GA} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x a) (e : a = b) :
    RatLink X x b := by
  subst e
  exact h

/- English proof (translation)
Substitute `h1 h2 h3` using the available equality. Both sides reduce to the same expression.
-/
theorem roset_congr {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ₁ Λ₂ Λ₁' Λ₂' : Submodule (𝓞 D.host.E) (VS D).V}
    {γ₁ γ₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h1 : Λ₁ = Λ₂) (h2 : Λ₁' = Λ₂') (h3 : γ₁ = γ₂) :
    ROset X F0 F0' Λ₁ Λ₁' γ₁ = ROset X F0 F0' Λ₂ Λ₂' γ₂ := by
  subst h1 h2 h3
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hS`.
-/
theorem isSFund_congr {S S' Ω : Set X.B.I.Ginf} (h : S = S') (hS : IsSFund X.B.I S Ω) : IsSFund X.B.I S' Ω := by
  subst h
  exact hS

/- English proof (translation)
Establish `hF : ∀ a, frame (lf D F0') a = c (frame (lf D F0') a)` using `fun a => by`. Rewrite using `[frame_lf, hfix a]`. Establish `hF' : ∀ a, frame (lf D F0') a = c⁻¹ (frame (lf D F0') a)` using `fun a => by`. Rewrite using `[frame_lf, inv_fix F0' hfix a]`. Establish `hA' : IsAutLam (VS D) Λ' c⁻¹` using `⟨inv_mem hA.1, gmap_inv_of hA.2⟩`.

Use extensionality with `y`. Simplify using `only [Formalism.L2.SG.TermOp.ROset, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, n, hx, rfl, hn, hn'⟩`. Use `⟨x, n, hx, rfl, hn, ?_⟩` and prove the remaining obligations.

Use `Formalism.L2.SG.Pf.nlam_conj hA hF hn'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Introduce and unpack `⟨x, n, hx, rfl, hn, hn'⟩`. Use `⟨x, n, hx, rfl, hn, ?_⟩` and prove the remaining obligations.

Use `Formalism.L2.SG.Pf.nlam_conj hA' hF' hn'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem roset_c {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hA : IsAutLam (VS D) Λ' c)
    (hfix : ∀ a, c (F0'.fvec a) = F0'.fvec a) :
    ROset X F0 F0' Λ Λ' (γ * c) = ROset X F0 F0' Λ Λ' γ := by
  have hF : ∀ a, frame (lf D F0') a = c (frame (lf D F0') a) := fun a => by
    rw [frame_lf, hfix a]
  have hF' : ∀ a, frame (lf D F0') a = c⁻¹ (frame (lf D F0') a) := fun a => by
    rw [frame_lf, inv_fix F0' hfix a]
  have hA' : IsAutLam (VS D) Λ' c⁻¹ := ⟨inv_mem hA.1, gmap_inv_of hA.2⟩
  ext y
  simp only [Formalism.L2.SG.TermOp.ROset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, n, hx, rfl, hn, hn'⟩
    refine ⟨x, n, hx, rfl, hn, ?_⟩
    have := Formalism.L2.SG.Pf.nlam_conj hA hF hn'
    convert this using 1
    group
  · rintro ⟨x, n, hx, rfl, hn, hn'⟩
    refine ⟨x, n, hx, rfl, hn, ?_⟩
    have := Formalism.L2.SG.Pf.nlam_conj hA' hF' hn'
    convert this using 1
    group

/- English proof (translation)
Take `⟨M, -, hM1, -, hM3⟩` from `hx`. Establish `hce : ∀ a, c (X.eX a) = X.eX a` using `fun a => by`. Use `hfix (Fin.castSucc a)` as an intermediate fact. Rewrite `this` using `[Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]`. Then use the resulting hypothesis. Establish `hcz : c (X.zu u') = X.zu u'`.

Use `hfix (Fin.last _)` as an intermediate fact. Rewrite `this` using `[Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, X.flagZVector]`. Then use the resulting hypothesis. Establish `hfixM : ∀ y, c y = y → (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y = X.crd y` using `fun y hy => by`. Rewrite using `[← hM3, hy]`. Introduce `v`.

Establish `key : ∀ w, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ w = w → (uMat (x.1 v) - 1) *ᵥ rv X.B.I v w = 0`. Introduce `w hw`. Establish `hP : IsUnit (X.B.I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)`. Establish `hφ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ (fun i => X.B.I.φ v (w i)) = fun i => X.B.I.φ v (w i)`. Use function extensionality and compare the values at `i`.

Establish `hi` using `RingHom.map_mulVec (X.B.I.φ v) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) w i`. Rewrite `hi` using `[hw]`. Conclude with `hi.symm`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, hM1 v, Formalism.L2.SG.HidaSetting.rv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, ← Matrix.mulVec_mulVec, hφ, sub_self]`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[key (X.eR a) (hfixM _ (hce a))]`. Conclude with `zero_mem _`. Rewrite using `[key (X.zR u') (hfixM _ hcz)]`. Conclude with `zero_mem _`.
-/
theorem sinf_of_fix {x : X.B.I.GA} {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x c)
    (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) : x.1 ∈ X.SinfU u' := by
  obtain ⟨M, -, hM1, -, hM3⟩ := hx
  have hce : ∀ a, c (X.eX a) = X.eX a := fun a => by
    have := hfix (Fin.castSucc a)
    rwa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, X.Fu_e] at this
  have hcz : c (X.zu u') = X.zu u' := by
    have := hfix (Fin.last _)
    rwa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, X.flagZVector] at this
  have hfixM : ∀ y, c y = y →
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y = X.crd y := fun y hy => by
    rw [← hM3, hy]
  intro v
  have key : ∀ w, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ w = w →
      (uMat (x.1 v) - 1) *ᵥ rv X.B.I v w = 0 := by
    intro w hw
    have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hφ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ
        (fun i => X.B.I.φ v (w i)) = fun i => X.B.I.φ v (w i) := by
      funext i
      have hi := RingHom.map_mulVec (X.B.I.φ v) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) w i
      rw [hw] at hi
      exact hi.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hM1 v, Formalism.L2.SG.HidaSetting.rv, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, ← Matrix.mulVec_mulVec, hφ, sub_self]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key (X.eR a) (hfixM _ (hce a))]
    exact zero_mem _
  · rw [key (X.zR u') (hfixM _ hcz)]
    exact zero_mem _

/- English proof (translation)
Conclude with `Formalism.L2.SG.TermOp.KExpCut.psiUnit X _`.
-/
theorem norm_chiN (κ : X.B.I.Gf) : ‖chiN X κ‖ = 1 := by
  exact Formalism.L2.SG.TermOp.KExpCut.psiUnit X _

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Take `⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩` from `fib_c h`. Take `⟨hl, -⟩` from `fib_dec h`. Establish `hl'` using `lam'_eq h`. Take `⟨xn, hxn⟩` from `hR D X n (nlam_isom hn)`. Take `⟨Ω, hΩ⟩` from `hs`.

Establish `e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν)`. Establish `hr` using `roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix`. Rewrite `hr` using `[← hlin]`. Conclude with `(roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr`. Establish `hS : ∀ σ, σ ∈ ROinf s' ↔ xn.1⁻¹ * σ * xn.1 ∈ ROinf s`.

Introduce `σ`. Rewrite using `[e1]`. Establish `hc` using `Formalism.L2.SG.TermOp.Vanish.roset_conj (X := X) (γ := s.lin) hn hν hxn (xn.1⁻¹ * σ * xn.1)`. Establish `hsimp : xn.1 * (xn.1⁻¹ * σ * xn.1) * xn.1⁻¹ = σ` using `by group`. Rewrite `hc` using `[hsimp]`.

Conclude with `hc.symm`. Conclude with `⟨_, Formalism.L2.SG.TermOp.Vanish.isSF_image_mul xn.1 hS hΩ⟩`.
-/
private theorem exists_isSFund_ROinf_of_toTerm_eq (hR : RatPt) {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm)
    (hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω) : ∃ Ω, IsSFund X.B.I (ROinf s') Ω := by
  obtain ⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩ := fib_c h
  obtain ⟨hl, -⟩ := fib_dec h
  have hl' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨Ω, hΩ⟩ := hs
  have e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) := by
    have hr := roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix
    rw [← hlin] at hr
    exact (roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr
  have hS : ∀ σ, σ ∈ ROinf s' ↔ xn.1⁻¹ * σ * xn.1 ∈ ROinf s := by
    intro σ
    rw [e1]
    have hc := Formalism.L2.SG.TermOp.Vanish.roset_conj (X := X) (γ := s.lin) hn hν hxn (xn.1⁻¹ * σ * xn.1)
    have hsimp : xn.1 * (xn.1⁻¹ * σ * xn.1) * xn.1⁻¹ = σ := by group
    rw [hsimp] at hc
    exact hc.symm
  exact ⟨_, Formalism.L2.SG.TermOp.Vanish.isSF_image_mul xn.1 hS hΩ⟩

/- English proof (translation)
Take `⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩` from `fib_c h`. Take `⟨hl, -⟩` from `fib_dec h`. Establish `hl'` using `lam'_eq h`. Take `⟨xn, hxn⟩` from `hR D X n (nlam_isom hn)`. Take `⟨xν, hxν⟩` from `hR D X ν (nlam_isom hν)`.

Take `⟨xc, hxc⟩` from `hR D X c hcI`. Establish `hl2 : RatLink X (xn * s.rep.1.1 * xν * xc) s'.lin`. Rewrite using `[hlin]`. Conclude with `Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X) (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X) (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X) hxn s.rep.2.1) hxν) hxc`. Establish `hpt : s'.pt = xn * s.rep.1.1 * xν * xc` using `Formalism.L2.SG.TermOp.Vanish.ratLink_unique (X := X) s'.rep.2.1 hl2`.

Establish `hsinv : xc.1⁻¹ ∈ X.SinfU u'` using `Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hcfix)`. Establish `hΩp : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.rep.1.2) (FundOf s)`. Unfold `Formalism.L2.SG.TermOp.FundOf`. Rewrite using `[dif_pos hs]`. Conclude with `hs.choose_spec`.

Establish `e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν)`. Establish `hr` using `roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix`. Rewrite `hr` using `[← hlin]`. Conclude with `(roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr`. Establish `hΩq : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.rep.1.2 * ν)) (FundOf s')`.

Establish `h2 : IsSFund X.B.I (ROinf s') (FundOf s')`. Unfold `Formalism.L2.SG.TermOp.FundOf`. Rewrite using `[dif_pos hs']`. Conclude with `hs'.choose_spec`. Conclude with `isSFund_congr e1 h2`.

Establish `key` using `Formalism.L2.SG.TermOp.Vanish.oo_rel Formalism.L2.SG.Pf.nLamNinf_holds hC Y s.mem s.mem' s.rep hn hν hxn hxν hΩp hΩq`. Establish `hOO : OOt s' = conj (X.psiInfU u' xc.1⁻¹) • ((X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s).comp ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u')`. Use `FiniteDimensional.complete ℂ (X.Vpi u)` as an intermediate fact. Use `show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') s'.pt.1 = _`. Rewrite using `[hpt, Prod.fst_mul, OO_right _ _ _ _ _ xc.1 _ _ (fun x => by`.

Rewrite using `[Formalism.L2.SG.RealObj.InfCut.piIso_apply]`. Conclude with `(X.Wu_spec u').1 _ hsinv x), key]`. Both sides reduce to the same expression. Establish `hb : ‖conj (X.psiInfU u' xc.1⁻¹)‖ = 1` using `(Complex.norm_conj _).trans (Formalism.L2.SG.TermOp.Vanish.psiInfU_norm X u' _)`. Establish `hk : ‖X.psiInfU u xn.1 * X.psiInfU u' xν.1‖ = 1`.

Rewrite using `[norm_mul, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, one_mul]`. Rewrite using `[hOO, norm_hsEmb_right _ _ hb, norm_hsEmb_smul _ _ hk]`.
-/
private theorem norm_hsEmb_OOt_eq_of_toTerm_eq (hR : RatPt) (hC : ChiTrivialC) {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm)
    (hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω) (hs' : ∃ Ω, IsSFund X.B.I (ROinf s') Ω) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s')‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s)‖ := by
  obtain ⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩ := fib_c h
  obtain ⟨hl, -⟩ := fib_dec h
  have hl' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨xν, hxν⟩ := hR D X ν (nlam_isom hν)
  obtain ⟨xc, hxc⟩ := hR D X c hcI
  have hl2 : RatLink X (xn * s.rep.1.1 * xν * xc) s'.lin := by
    rw [hlin]
    exact Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X)
      (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X)
        (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X) hxn s.rep.2.1) hxν) hxc
  have hpt : s'.pt = xn * s.rep.1.1 * xν * xc :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_unique (X := X) s'.rep.2.1 hl2
  have hsinv : xc.1⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hcfix)
  have hΩp : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.rep.1.2) (FundOf s) := by
    unfold Formalism.L2.SG.TermOp.FundOf
    rw [dif_pos hs]
    exact hs.choose_spec
  have e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) := by
    have hr := roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix
    rw [← hlin] at hr
    exact (roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr
  have hΩq : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.rep.1.2 * ν)) (FundOf s') := by
    have h2 : IsSFund X.B.I (ROinf s') (FundOf s') := by
      unfold Formalism.L2.SG.TermOp.FundOf
      rw [dif_pos hs']
      exact hs'.choose_spec
    exact isSFund_congr e1 h2
  have key := Formalism.L2.SG.TermOp.Vanish.oo_rel Formalism.L2.SG.Pf.nLamNinf_holds hC Y s.mem s.mem' s.rep
    hn hν hxn hxν hΩp hΩq
  have hOO : OOt s' = conj (X.psiInfU u' xc.1⁻¹) •
      ((X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s).comp
        ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
          X.Vpi u' →L[ℂ] X.Vpi u') := by
    have := FiniteDimensional.complete ℂ (X.Vpi u)
    show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') s'.pt.1 = _
    rw [hpt, Prod.fst_mul, OO_right _ _ _ _ _ xc.1 _ _ (fun x => by
      rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
      exact (X.Wu_spec u').1 _ hsinv x), key]
    rfl
  have hb : ‖conj (X.psiInfU u' xc.1⁻¹)‖ = 1 :=
    (Complex.norm_conj _).trans (Formalism.L2.SG.TermOp.Vanish.psiInfU_norm X u' _)
  have hk : ‖X.psiInfU u xn.1 * X.psiInfU u' xν.1‖ = 1 := by
    rw [norm_mul, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, one_mul]
  rw [hOO, norm_hsEmb_right _ _ hb, norm_hsEmb_smul _ _ hk]

/- English proof (translation)
Distinguish the cases in `hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω`. Conclude with `norm_hsEmb_OOt_eq_of_toTerm_eq hR hC h hs (exists_isSFund_ROinf_of_toTerm_eq hR h hs)`. Distinguish the cases in `hs' : ∃ Ω, IsSFund X.B.I (ROinf s') Ω`. Conclude with `absurd (exists_isSFund_ROinf_of_toTerm_eq hR h.symm hs') hs`. Establish `e : ∀ t : TT Y u u', ¬ (∃ Ω, IsSFund X.B.I (ROinf t) Ω) → OOt t = 0` using `fun t ht => by`.

Use `FiniteDimensional.complete ℂ (X.Vpi u)` as an intermediate fact. Use `show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1 = 0`. Unfold `Formalism.L2.SG.TermOp.FundOf`. Rewrite using `[dif_neg ht]`. Conclude with `OO_empty _ _ _ _`.

Rewrite using `[e s hs, e s' hs']`.
-/
theorem oot_norm (hR : RatPt) (hC : ChiTrivialC) {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s')‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s)‖ := by
  by_cases hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω
  · exact norm_hsEmb_OOt_eq_of_toTerm_eq hR hC h hs (exists_isSFund_ROinf_of_toTerm_eq hR h hs)
  · by_cases hs' : ∃ Ω, IsSFund X.B.I (ROinf s') Ω
    · exact absurd (exists_isSFund_ROinf_of_toTerm_eq hR h.symm hs') hs
    · have e : ∀ t : TT Y u u', ¬ (∃ Ω, IsSFund X.B.I (ROinf t) Ω) → OOt t = 0 := fun t ht => by
        have := FiniteDimensional.complete ℂ (X.Vpi u)
        show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1 = 0
        unfold Formalism.L2.SG.TermOp.FundOf
        rw [dif_neg ht]
        exact OO_empty _ _ _ _
      rw [e s hs, e s' hs']

/- English proof (translation)
Unfold `Formalism.L2.SG.LoopTieOf.AmpFibreConst`. Introduce `u u' t s s'`. Simplify using `only [Formalism.L2.SG.LoopTieOf.ampL, Formalism.L2.SG.TermOp.ampN, map_smul, norm_smul, norm_chiN, one_mul]`. Rewrite using `[oot_norm hR hC (s'.2.trans s.2.symm)]`.
-/
theorem ampFibreConst_of (hR : RatPt) (hC : ChiTrivialC) (Y : Full X) : Formalism.L2.SG.LoopTieOf.AmpFibreConst Y := by
  unfold Formalism.L2.SG.LoopTieOf.AmpFibreConst
  intro u u' t s s'
  simp only [Formalism.L2.SG.LoopTieOf.ampL, Formalism.L2.SG.TermOp.ampN, map_smul, norm_smul, norm_chiN, one_mul]
  rw [oot_norm hR hC (s'.2.trans s.2.symm)]

end Amp

end Formalism.L2.SG.Pf.FibreCounting
