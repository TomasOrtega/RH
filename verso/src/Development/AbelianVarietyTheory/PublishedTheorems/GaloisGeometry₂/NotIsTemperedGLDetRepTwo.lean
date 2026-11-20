import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

namespace GlobalTheory.LocGL.TemperedTests

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GenericUnitary Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨n, c⟩` from `x`. Take `rfl : n = 1` from `hx`. Take `⟨θ, hθ, ⟨e⟩⟩` from `RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr`. Conclude with `⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩`.
-/
theorem exists_eq_ofChar (x : IrrGL k) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

/- English proof (translation)
Introduce `h` and use `by have hd : Δ.len * Δ.d = 2 := h.deg_eq have h1 := Δ.len_pos have h2 := Δ.d_pos have hl : Δ.len ≤ 2 := by nlinarith have key : ∀ (ρ : IrrGL k) (hρ : ρ.IsCusp), ρ.1 = 2 → ¬ IsLSeg (.single ρ hρ) (detRep (Fin 2) η) := by rintro ⟨n, c⟩ hρ hn h obtain rfl : n = 2 := hn obtain ⟨e⟩ := …`.
-/
theorem not_isLSeg_detRep_two (η : kˣ →* ℂˣ) (Δ : Segment k) : ¬ IsLSeg Δ (detRep (Fin 2) η) := fun h => by
  have hd : Δ.len * Δ.d = 2 := h.deg_eq
  have h1 := Δ.len_pos
  have h2 := Δ.d_pos
  have hl : Δ.len ≤ 2 := by nlinarith
  have key : ∀ (ρ : IrrGL k) (hρ : ρ.IsCusp), ρ.1 = 2 → ¬ IsLSeg (.single ρ hρ) (detRep (Fin 2) η) := by
    rintro ⟨n, c⟩ hρ hn h
    obtain rfl : n = 2 := hn
    obtain ⟨e⟩ := (single_spec hρ).2.1.unique h
    exact not_isCuspidal_detRep_two η (isCuspidal_of_equiv e.symm hρ.2)
  rcases (by omega : Δ.len = 1 ∨ Δ.len = 2) with e | e
  · have e2 : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl e
    exact key _ Δ.isCusp_first (by change Δ.d = 2; rw [e] at hd; omega) (e2 ▸ h)
  · obtain ⟨θ, hθ, e3⟩ := exists_eq_ofChar Δ.first (by change Δ.d = 1; rw [e] at hd; omega)
    have e2 : Δ = Segment.ofChar θ hθ 2 two_pos := Segment.ext_first e3 e
    obtain ⟨V, _, _, π, h3, h4⟩ := exists_isLSeg_two hθ
    obtain ⟨φ⟩ := (e2 ▸ h : IsLSeg (Segment.ofChar θ hθ 2 two_pos) (detRep (Fin 2) η)).unique h3
    exact (h4 _).false φ

/- English proof (translation)
Introduce and unpack `⟨h, δ, hd, h1, ⟨φ⟩⟩`. Establish `hp : ∀ i, 1 ≤ (δ i).1` using `fun i => (h1 i).deg_pos`. Establish `h2 : h ≤ 2` using `by simpa [hd] using Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i`. Establish `h3 : h ≠ 0` using `by rintro rfl; simp at hd`. Break down `(by omega : h = 1 ∨ h = 2) with rfl | rfl` into its components or cases.

Take `⟨x, rfl⟩ : ∃ x, δ = fun _ => x` from `⟨δ 0, funext fun i => congrArg δ (Subsingleton.elim _ _)⟩`. Take `⟨n, c⟩` from `x`. Take `rfl : n = 2` from `by simpa using hd`. Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_one (⟨2, c⟩ : IrrGL k) hd`. Take `⟨Δ, hΔ⟩` from `(h1 0).1`.

Conclude with `not_isLSeg_detRep_two η Δ (hΔ.of_equiv (ψ.trans φ.symm))`. Establish `h4 : ∀ i, (δ i).1 = 1`. Establish `a` using `hp 0`. Establish `b` using `hp 1`. Rewrite `hd` using `[Fin.sum_univ_two]`.

Conclude with `Fin.forall_fin_two.2 ⟨by omega, by omega⟩`. Use `choose θ hθ e using fun i => exists_eq_ofChar (δ i) (h4 i)`. Establish `hu : ∀ i z, ‖(θ i z : ℂ)‖ = 1` using `fun i z => by`. Establish `h5` using `(h1 i).2`. Rewrite `h5` using `[e i]`.

Establish `h6` using `(isUnitarisable_ofChar_iff _).1 (isUnitarisable_of_equiv (equivRep (IrrRep.det (Fin 1) (θ i) (hθ i))).symm h5) (GeneralLinearGroup.scalar (Fin 1) z)`. Establish `h7 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z` using `by ext; simp [GeneralLinearGroup.scalar]`. Rewrite `h6` using `[detChar_apply, h7]`. Then use the resulting hypothesis. Set `Θ : Levi k (fun _ : Fin 2 => Fin 1) →* ℂˣ` to `∏ a, (detChar (Fin 1) (θ a)).comp (Pi.evalMonoidHom (fun _ : Fin 2 => GL (Fin 1) k) a)`. Establish `hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))` using `fun g => by`.

Simplify using `[Θ]`. Take `⟨hd', ⟨ψ⟩⟩` from `ProjLine.exists_equiv_prodIrr hθ e hΘ`. Set `T` to `φ.trans ψ.symm`. Set `f` to `T.toLinearEquiv 1`. Establish `hf : ∀ g, f.1.1 g = (detChar (Fin 2) η g : ℂ) * f.1.1 1` using `fun g => by`.

Establish `h5 : T.toLinearEquiv (detRep (Fin 2) η g 1) = parInd _ _ g f` using `T.toIntertwiningMap.isIntertwining _ _ g 1`. Establish `h6 : detRep (Fin 2) η g 1 = (detChar (Fin 2) η g : ℂ) • (1 : ℂ)` using `ofChar_apply _ _ _`. Rewrite `h5` using `[h6, map_smul]`. Establish `h7` using `congrArg (fun F => F.1.1 1) h5`. Simplify using `only [parInd_apply, one_mul] at h7`.

Conclude with `h7.symm`. Establish `h0 : f.1.1 1 ≠ 0` using `fun h5 => one_ne_zero (T.toLinearEquiv.map_eq_zero_iff.1 (Subtype.ext (Subtype.ext (funext fun g => by rw [hf, h5, mul_zero]; rfl))))`. Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`. Establish `hn : nabs k ϖ ≠ 1` using `fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)`. Set `m : Levi k (fun _ : Fin 2 => Fin 1)` to `![GeneralLinearGroup.scalar (Fin 1) ϖ, GeneralLinearGroup.scalar (Fin 1) ϖ⁻¹]`.

Establish `h7 : ∀ z : kˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z` using `fun z => by ext; simp [GeneralLinearGroup.scalar]`. Establish `h8` using `parInd_law _ _ f ⟨_, leviEmb_mem_parab k ProjLine.pts m⟩ 1`. Rewrite `h8` using `[mul_one, hf, leviProj_leviEmb, detChar_apply, det_leviEmb, ofChar_apply, hΘ, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]`. Simplify using `only [m, Matrix.cons_val_zero, Matrix.cons_val_one, h7, mul_inv_cancel, map_one, Units.val_one, smul_eq_mul, ← mul_assoc] at h8`. Establish `h9` using `congrArg norm (mul_right_cancel₀ h0 h8)`.

Simplify using `only [norm_mul, Units.val_mul, hu, mul_one, norm_one] at h9`. Evaluate the numerical expressions using `at h9`. Rewrite `h9` using `[← norm_inv, ← Units.val_inv_eq_inv_val, absPow_neg, MonoidHom.inv_apply, inv_inv, ← norm_mul, ← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add, add_halves, val_absPow, Complex.cpow_one, Complex.norm_real, Real.norm_of_nonneg (nabs_pos' k ϖ).le]`. Conclude with `hn h9.symm`.
-/
theorem not_isTemperedGL_detRep_two (η : kˣ →* ℂˣ) : ¬ IsTemperedGL (detRep (Fin 2) η) := by
  rintro ⟨h, δ, hd, h1, ⟨φ⟩⟩
  have hp : ∀ i, 1 ≤ (δ i).1 := fun i => (h1 i).deg_pos
  have h2 : h ≤ 2 := by simpa [hd] using Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
  have h3 : h ≠ 0 := by rintro rfl; simp at hd
  rcases (by omega : h = 1 ∨ h = 2) with rfl | rfl
  · obtain ⟨x, rfl⟩ : ∃ x, δ = fun _ => x := ⟨δ 0, funext fun i => congrArg δ (Subsingleton.elim _ _)⟩
    obtain ⟨n, c⟩ := x
    obtain rfl : n = 2 := by simpa using hd
    obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨2, c⟩ : IrrGL k) hd
    obtain ⟨Δ, hΔ⟩ := (h1 0).1
    exact not_isLSeg_detRep_two η Δ (hΔ.of_equiv (ψ.trans φ.symm))
  · have h4 : ∀ i, (δ i).1 = 1 := by
      have a := hp 0
      have b := hp 1
      rw [Fin.sum_univ_two] at hd
      exact Fin.forall_fin_two.2 ⟨by omega, by omega⟩
    choose θ hθ e using fun i => exists_eq_ofChar (δ i) (h4 i)
    have hu : ∀ i z, ‖(θ i z : ℂ)‖ = 1 := fun i z => by
      have h5 := (h1 i).2
      rw [e i] at h5
      have h6 := (isUnitarisable_ofChar_iff _).1
        (isUnitarisable_of_equiv (equivRep (IrrRep.det (Fin 1) (θ i) (hθ i))).symm h5)
        (GeneralLinearGroup.scalar (Fin 1) z)
      have h7 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
        ext; simp [GeneralLinearGroup.scalar]
      rwa [detChar_apply, h7] at h6
    let Θ : Levi k (fun _ : Fin 2 => Fin 1) →* ℂˣ :=
      ∏ a, (detChar (Fin 1) (θ a)).comp (Pi.evalMonoidHom (fun _ : Fin 2 => GL (Fin 1) k) a)
    have hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a)) := fun g => by
      simp [Θ]
    obtain ⟨hd', ⟨ψ⟩⟩ := ProjLine.exists_equiv_prodIrr hθ e hΘ
    let T := φ.trans ψ.symm
    let f := T.toLinearEquiv 1
    have hf : ∀ g, f.1.1 g = (detChar (Fin 2) η g : ℂ) * f.1.1 1 := fun g => by
      have h5 : T.toLinearEquiv (detRep (Fin 2) η g 1) = parInd _ _ g f :=
        T.toIntertwiningMap.isIntertwining _ _ g 1
      have h6 : detRep (Fin 2) η g 1 = (detChar (Fin 2) η g : ℂ) • (1 : ℂ) := ofChar_apply _ _ _
      rw [h6, map_smul] at h5
      have h7 := congrArg (fun F => F.1.1 1) h5
      simp only [parInd_apply, one_mul] at h7
      exact h7.symm
    have h0 : f.1.1 1 ≠ 0 := fun h5 => one_ne_zero (T.toLinearEquiv.map_eq_zero_iff.1
      (Subtype.ext (Subtype.ext (funext fun g => by rw [hf, h5, mul_zero]; rfl))))
    obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
    have hn : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
    let m : Levi k (fun _ : Fin 2 => Fin 1) :=
      ![GeneralLinearGroup.scalar (Fin 1) ϖ, GeneralLinearGroup.scalar (Fin 1) ϖ⁻¹]
    have h7 : ∀ z : kˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := fun z => by
      ext; simp [GeneralLinearGroup.scalar]
    have h8 := parInd_law _ _ f ⟨_, leviEmb_mem_parab k ProjLine.pts m⟩ 1
    rw [mul_one, hf, leviProj_leviEmb, detChar_apply, det_leviEmb, ofChar_apply, hΘ, deltaHalf_apply,
      Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)] at h8
    simp only [m, Matrix.cons_val_zero, Matrix.cons_val_one, h7, mul_inv_cancel, map_one, Units.val_one, smul_eq_mul,
      ← mul_assoc] at h8
    have h9 := congrArg norm (mul_right_cancel₀ h0 h8)
    simp only [norm_mul, Units.val_mul, hu, mul_one, norm_one] at h9
    norm_num at h9
    rw [← norm_inv, ← Units.val_inv_eq_inv_val, absPow_neg, MonoidHom.inv_apply, inv_inv, ← norm_mul, ← Units.val_mul,
      ← MonoidHom.mul_apply, ← absPow_add, add_halves, val_absPow, Complex.cpow_one, Complex.norm_real,
      Real.norm_of_nonneg (nabs_pos' k ϖ).le] at h9
    exact hn h9.symm

end GlobalTheory.LocGL.TemperedTests

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GKCoh.Tests

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

/- English proof (translation)
Take `⟨ω, hω, hc⟩` from `CsdUnitary.isUnitary_of_isCsd L 1 (CG.mk π) hπ`. Take `⟨f, h0, hf⟩` from `h`. Take `⟨ψ, hψ, ⟨e⟩⟩` from `RankLeOne.exists_equiv_detRep _ (Fin 1) _ σ.ρ σ.smooth σ.irred`. Use `((LocGL.isTemperedGL_detRep_one hψ).2 ((isUnitarisable_ofChar_iff _).2 fun g => ?_)).of_equiv e.symm` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, f v ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h0 (LinearMap.ext hc)`. Establish `h1 : σ.ρ g v = (detChar (Fin 1) ψ g : ℂ) • v` using `e.toLinearEquiv.injective (by`. Rewrite using `[map_smul]`.

Conclude with `(e.toIntertwiningMap.isIntertwining _ _ g v).trans (ofChar_apply _ _ _))`. Establish `h2` using `hf g v`. Establish `h3` using `hc (GeneralLinearGroup.det (locGL L 1 y g)) (f v)`. Rewrite `h3` using `[RankLeOne.scalar_det_of_subsingleton]`. Rewrite `h2` using `[h1, map_smul]`.

Rewrite using `[smul_left_injective ℂ hv (h2.trans h3)]`. Conclude with `hω _`.
-/
theorem tempered_rank_one (L : Type) [Field L] [NumberField L] [IsCMField L] (π : CuspSub L 1) (hπ : π.IsCsd)
    (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin 1) (y.adicCompletion L))) (h : π.IsLocComp y σ) :
    LocGL.IsTemperedGL σ.ρ := by
  obtain ⟨ω, hω, hc⟩ := CsdUnitary.isUnitary_of_isCsd L 1 (CG.mk π) hπ
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨ψ, hψ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep _ (Fin 1) _ σ.ρ σ.smooth σ.irred
  refine ((LocGL.isTemperedGL_detRep_one hψ).2 ((isUnitarisable_ofChar_iff _).2 fun g => ?_)).of_equiv e.symm
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (LinearMap.ext hc)
  have h1 : σ.ρ g v = (detChar (Fin 1) ψ g : ℂ) • v := e.toLinearEquiv.injective (by
    rw [map_smul]
    exact (e.toIntertwiningMap.isIntertwining _ _ g v).trans (ofChar_apply _ _ _))
  have h2 := hf g v
  have h3 := hc (GeneralLinearGroup.det (locGL L 1 y g)) (f v)
  rw [RankLeOne.scalar_det_of_subsingleton] at h3
  rw [h1, map_smul] at h2
  rw [smul_left_injective ℂ hv (h2.trans h3)]
  exact hω _

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Set `A : Cinf E →L[ℝ] ℂ` to `s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))`. Establish `h : dchi (Model.absC E s) = A` using `fderiv_extZero (continuous_chiInf _) fun z => by`. Express the relevant statement in the definitionally equal form `Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _`. Rewrite using `[Model.logNorm_infId]`. Use `congr 1`.

Simplify using `[A, expU, Complex.norm_exp]`. Rewrite using `[h]`. Simplify using `[A, mul_comm]`.
-/
theorem dchi_absC_one (s : ℂ) : dchi (Model.absC E s) 1 = s * (2 * Fintype.card (InfinitePlace E)) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A, mul_comm]

/- English proof (translation)
Use `not_hasCohomology_of_central (c := s * (2 * Fintype.card (InfinitePlace E))) (by simp [hs]) fun m => ?_` and prove the remaining obligations. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `tmul φ v`.

Rewrite using `[tensorLie_tmul, CuspSub.op_triv_twist, AlgRep.dmat_triv, ← dchi_absC_one]`. Simplify using `[opTriv, opAdd, TensorProduct.smul_tmul']`.
-/
theorem not_isCohFor_absC {s : ℂ} (hs : s ≠ 0) :
    ¬ IsCohFor ((CuspSub.triv E le_rfl).twist (Model.absC E s)) (AlgRep.triv E 1) := by
  refine not_hasCohomology_of_central (c := s * (2 * Fintype.card (InfinitePlace E))) (by simp [hs]) fun m => ?_
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul φ v =>
    rw [tensorLie_tmul, CuspSub.op_triv_twist, AlgRep.dmat_triv, ← dchi_absC_one]
    simp [opTriv, opAdd, TensorProduct.smul_tmul']

/- English proof (translation)
Establish `h1 : (CuspSub.triv L (le_refl 1)).IsCsd` using `⟨.refl _ _, fun o φ => Subtype.ext (by`. Take `⟨c, e⟩` from `Submodule.mem_span_singleton.1 φ.2`. Express the relevant statement in the definitionally equal form `act (thetaOp o) φ.1 = act o φ.1`. Rewrite using `[← e, map_smul, map_smul, act_oneFn, act_oneFn]`. Apply the tactic sequence `cases o <;> rfl)⟩`.

Establish `h2 : (CuspSub.triv L (le_refl 1)).IsLocComp y (SmIrr.triv _)` using `⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn L 1, Submodule.mem_span_singleton_self _⟩, fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))), fun _ _ => rfl⟩`. Conclude with `⟨_, _, h1, ⟨_, isCohFor_triv le_rfl⟩, h2, tempered_rank_one L _ h1 y _ h2⟩`.
-/
theorem triv_spec (L : Type) [Field L] [NumberField L] [IsCMField L] (y : HeightOneSpectrum (𝓞 L)) :
    ∃ (π : CuspSub L 1) (σ : SmIrr (GL (Fin 1) (y.adicCompletion L))),
      π.IsCsd ∧ IsCohomological π ∧ π.IsLocComp y σ ∧ LocGL.IsTemperedGL σ.ρ := by
  have h1 : (CuspSub.triv L (le_refl 1)).IsCsd := ⟨.refl _ _, fun o φ => Subtype.ext (by
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
    change act (thetaOp o) φ.1 = act o φ.1
    rw [← e, map_smul, map_smul, act_oneFn, act_oneFn]
    cases o <;> rfl)⟩
  have h2 : (CuspSub.triv L (le_refl 1)).IsLocComp y (SmIrr.triv _) :=
    ⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn L 1, Submodule.mem_span_singleton_self _⟩,
      fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))),
      fun _ _ => rfl⟩
  exact ⟨_, _, h1, ⟨_, isCohFor_triv le_rfl⟩, h2, tempered_rank_one L _ h1 y _ h2⟩

/- English proof (translation)
Rewrite using `[← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding` using `fun h => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))`. Establish `e : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding}`. Use extensionality with `τ`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h | h` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr (by rw [← h]; ext x; simp)`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp`. Rewrite using `[e, Finset.prod_pair hne]`. Simplify using `[coord, hne]`.
-/
theorem prod_coord {M : Type} [CommMonoid M] (F : ℂ → M) (z : Cinf E) :
    ∏ τ : E →+* ℂ, F (coord τ z) = ∏ w, F (z w) * F (starRingEnd ℂ (z w)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have e : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← h]; ext x; simp)
    · rintro (rfl | rfl) <;> simp
  rw [e, Finset.prod_pair hne]
  simp [coord, hne]

variable (E) in

def normRep : AlgRep E 1 where
  d := 1
  mat :=
    { toFun := fun y => Matrix.of fun _ _ => ∏ τ : E →+* ℂ, coord τ (y.val 0 0)
      map_one' := by ext i j; rw [Subsingleton.elim i j]; simp
      map_mul' := fun x y => by ext i j; simp [Matrix.mul_apply, Finset.prod_mul_distrib] }
  reg i j := by
    have h : (∏ τ : E →+* ℂ, fun y : GL (Fin 1) (Cinf E) => coord τ (y.val 0 0)) ∈ regFun E 1 :=
      Subalgebra.prod_mem _ fun τ _ => Algebra.subset_adjoin (Or.inl ⟨τ, 0, 0, rfl⟩)
    convert h using 1
    ext y; simp
  pos := one_pos
  irred W _ := by
    have : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
    exact eq_bot_or_eq_top W

/- English proof (translation)
Establish `h` using `extGL_eventuallyEq (f := fun y => (normRep E).mat y i j) (F := fun x => ∏ τ : E →+* ℂ, coordL τ (x 0 0)) (fun _ => rfl) (x := oneL E 1) isUnit_one`. Express the relevant statement in the definitionally equal form `fderiv ℝ _ _ X = _`. Rewrite using `[h.fderiv_eq]`. Set `P : (E →+* ℂ) → Lie E 1 →L[ℝ] ℂ` to `fun τ => (coordL τ).comp ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 1 → Cinf E) 0))`. Establish `h2` using `HasFDerivAt.finsetProd (u := Finset.univ) (x := oneL E 1) fun τ _ => (P τ).hasFDerivAt`.

Establish `h3` using `congrArg (fun D : Lie E 1 →L[ℝ] ℂ => D X) h2.fderiv`. Use `h3.trans ?_` and prove the remaining obligations. Establish `h4` using `prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd (X 0 0)`. Simplify using `only [← ofAdd_add, ← ofAdd_sum, Complex.add_conj] at h4`. Simplify `Multiplicative.ofAdd.injective h4` using `[P]`.
-/
theorem dmat_normRep (X : Lie E 1) (i j : Fin 1) :
    (normRep E).dmat X i j = ∑ w, (2 * ((X 0 0 w).re : ℝ) : ℂ) := by
  classical
  have h := extGL_eventuallyEq (f := fun y => (normRep E).mat y i j) (F := fun x => ∏ τ : E →+* ℂ, coordL τ (x 0 0))
    (fun _ => rfl) (x := oneL E 1) isUnit_one
  change fderiv ℝ _ _ X = _
  rw [h.fderiv_eq]
  let P : (E →+* ℂ) → Lie E 1 →L[ℝ] ℂ := fun τ => (coordL τ).comp ((ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 1 → Cinf E) 0))
  have h2 := HasFDerivAt.finsetProd (u := Finset.univ) (x := oneL E 1) fun τ _ => (P τ).hasFDerivAt
  have h3 := congrArg (fun D : Lie E 1 →L[ℝ] ℂ => D X) h2.fderiv
  refine h3.trans ?_
  have h4 := prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd (X 0 0)
  simp only [← ofAdd_add, ← ofAdd_sum, Complex.add_conj] at h4
  simpa [P] using Multiplicative.ofAdd.injective h4

/- English proof (translation)
Set `A : Cinf E →L[ℝ] ℂ` to `s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))`. Establish `h : dchi (Model.absC E s) = A` using `fderiv_extZero (continuous_chiInf _) fun z => by`. Express the relevant statement in the definitionally equal form `Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _`. Rewrite using `[Model.logNorm_infId]`. Use `congr 1`.

Simplify using `[A, expU, Complex.norm_exp]`. Rewrite using `[h]`. Simplify using `[A]`.
-/
theorem dchi_absC (s : ℂ) (z : Cinf E) : dchi (Model.absC E s) z = s * ∑ w, (2 * ((z w).re : ℝ) : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A]

/- English proof (translation)
Use `Submodule.nontrivial_iff_ne_bot.2 ((CuspSub.triv E le_rfl).twist (Model.absC E (-1))).ne_bot` as an intermediate fact. Take `⟨φ, hφ⟩` from `exists_ne (0 : ((CuspSub.triv E le_rfl).twist (Model.absC E (-1))).V)`. Use `hasCohomology_of_invariant (m := φ ⊗ₜ fun _ => 1) (fun h => hφ ?_) (fun k => ?_) fun X => ?_` and prove the remaining obligations. Establish `key : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (v : V), v ⊗ₜ[ℂ] (fun _ : Fin 1 => (1 : ℂ)) = 0 → v = 0` using `fun v h => by`. Establish `h1` using `congrArg (fun x => TensorProduct.rid ℂ _ (LinearMap.lTensor _ (LinearMap.proj (0 : Fin 1)) x)) h`.

Simplify using `only [LinearMap.lTensor_tmul, LinearMap.proj_apply, TensorProduct.rid_tmul, one_smul, map_zero] at h1`. Conclude with `h1`. Conclude with `key φ h`. Establish `hk : ∀ w, k.1 0 0 w * starRingEnd ℂ (k.1 0 0 w) = 1` using `fun w => by`. Use `congrFun (congrFun (congrFun k.2.2 0) 0) w` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply]`. Establish `hn : ∀ w, ‖k.1 0 0 w‖ = 1` using `fun w => by`. Use `congrArg norm (hk w)` as an intermediate fact. Rewrite `this` using `[norm_mul, Complex.norm_conj, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (k.1 0 0 w)]`.

Rewrite using `[tensorK, TensorProduct.map_tmul, CuspSub.op_triv_twist]`. Establish `e1 : ((opMul (Model.absC E (-1)) (.cpt k : Op E 1) : ℂˣ) : ℂ) = 1`. Simplify using `only [opMul, chiDet, MonoidHom.comp_apply, det_infGL]`. Express the relevant statement in the definitionally equal form `Complex.exp (-1 * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = _`. Rewrite using `[Model.logNorm_infId]`.

Simplify using `[hn]`. Establish `e2 : (normRep E).mat (Unitary.toUnits k) = 1`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `∏ τ : E →+* ℂ, id (coord τ (k.1 0 0)) = (1 : Matrix (Fin 1) (Fin 1) ℂ) i j`. Rewrite using `[prod_coord]`.

Rewrite using `[Subsingleton.elim (α := Fin 1) i j]`. Simplify using `only [id, hk, Finset.prod_const_one]`. Conclude with `(Matrix.one_apply_eq (α := ℂ) (n := Fin 1) j).symm`. Rewrite using `[e1, e2]`. Simplify using `[opTriv, opAdd]`.

Rewrite using `[tensorLie_tmul, CuspSub.op_triv_twist]`. Establish `e : (normRep E).dmat X *ᵥ (fun _ => 1) = (∑ w, (2 * ((X 0 0 w).re : ℝ) : ℂ)) • fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `∑ j : Fin 1, (normRep E).dmat X i j * 1 = _`. Rewrite using `[Fin.sum_univ_one, dmat_normRep X i 0]`.

Simplify using the standard rewrite rules. Rewrite using `[e, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul]`. Simplify using `[opTriv, opAdd, dchi_absC, Matrix.trace_fin_one]`.
-/
theorem isCohFor_absC_neg_one :
    IsCohFor ((CuspSub.triv E le_rfl).twist (Model.absC E (-1))) (normRep E) := by
  have := Submodule.nontrivial_iff_ne_bot.2 ((CuspSub.triv E le_rfl).twist (Model.absC E (-1))).ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ((CuspSub.triv E le_rfl).twist (Model.absC E (-1))).V)
  refine hasCohomology_of_invariant (m := φ ⊗ₜ fun _ => 1) (fun h => hφ ?_) (fun k => ?_) fun X => ?_
  · have key : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (v : V), v ⊗ₜ[ℂ] (fun _ : Fin 1 => (1 : ℂ)) = 0 → v = 0 :=
      fun v h => by
        have h1 := congrArg (fun x => TensorProduct.rid ℂ _ (LinearMap.lTensor _ (LinearMap.proj (0 : Fin 1)) x)) h
        simp only [LinearMap.lTensor_tmul, LinearMap.proj_apply, TensorProduct.rid_tmul, one_smul, map_zero] at h1
        exact h1
    exact key φ h
  · have hk : ∀ w, k.1 0 0 w * starRingEnd ℂ (k.1 0 0 w) = 1 := fun w => by
      have := congrFun (congrFun (congrFun k.2.2 0) 0) w
      simpa [Matrix.mul_apply] using this
    have hn : ∀ w, ‖k.1 0 0 w‖ = 1 := fun w => by
      have := congrArg norm (hk w)
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      nlinarith [norm_nonneg (k.1 0 0 w)]
    rw [tensorK, TensorProduct.map_tmul, CuspSub.op_triv_twist]
    have e1 : ((opMul (Model.absC E (-1)) (.cpt k : Op E 1) : ℂˣ) : ℂ) = 1 := by
      simp only [opMul, chiDet, MonoidHom.comp_apply, det_infGL]
      change Complex.exp (-1 * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = _
      rw [Model.logNorm_infId]
      simp [hn]
    have e2 : (normRep E).mat (Unitary.toUnits k) = 1 := by
      ext i j
      change ∏ τ : E →+* ℂ, id (coord τ (k.1 0 0)) = (1 : Matrix (Fin 1) (Fin 1) ℂ) i j
      rw [prod_coord]
      rw [Subsingleton.elim (α := Fin 1) i j]
      simp only [id, hk, Finset.prod_const_one]
      exact (Matrix.one_apply_eq (α := ℂ) (n := Fin 1) j).symm
    rw [e1, e2]
    simp [opTriv, opAdd]
  · rw [tensorLie_tmul, CuspSub.op_triv_twist]
    have e : (normRep E).dmat X *ᵥ (fun _ => 1) = (∑ w, (2 * ((X 0 0 w).re : ℝ) : ℂ)) • fun _ => (1 : ℂ) := by
      funext i
      change ∑ j : Fin 1, (normRep E).dmat X i j * 1 = _
      rw [Fin.sum_univ_one, dmat_normRep X i 0]
      simp
    rw [e, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul]
    simp [opTriv, opAdd, dchi_absC, Matrix.trace_fin_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, ⟨_, isCohFor_absC_neg_one⟩, fun h => by simpa using (Model.isCsd_absC (L := L) (-1)).1 h⟩`.
-/
theorem coh_not_csd (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ π : CuspSub L 1, IsCohomological π ∧ ¬ π.IsCsd :=
  ⟨_, ⟨_, isCohFor_absC_neg_one⟩, fun h => by simpa using (Model.isCsd_absC (L := L) (-1)).1 h⟩

end GlobalTheory.GKCoh.Tests
