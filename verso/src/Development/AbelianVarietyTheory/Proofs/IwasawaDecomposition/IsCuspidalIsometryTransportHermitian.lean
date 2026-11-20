import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom.IsoMat

open Formalism.UG (cT cT_mul cT_one)

section Gen

variable {A : Type} [CommRing A] {k n m : ℕ}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_right_zero {r : ℕ} {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {c : Matrix (Fin n) (Fin r) A} (h : x * c = 0) : aP * x * aQ * (aP * c) = 0 := by
  calc _ = aP * (x * ((aQ * aP) * c)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.mul_zero]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_left_zero {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {y : Matrix (Fin k) (Fin n) A} (h : y * x = 0) : y * aQ * (aP * x * aQ) = 0 := by
  calc _ = (y * ((aQ * aP) * x)) * aQ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.zero_mul]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]`.
-/
theorem conj_mulVec {r : ℕ} (aP : Matrix (Fin m) (Fin n) A) (aQ : Matrix (Fin n) (Fin m) A)
    (x : Matrix (Fin n) (Fin n) A) (c : Matrix (Fin n) (Fin r) A) (v : Fin m → A) (a : Fin r → A)
    (h : x.mulVec (aQ.mulVec v) = c.mulVec a) : (aP * x * aQ).mulVec v = (aP * c).mulVec a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]`.
-/
theorem conj_sub_one {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hPQ : aP * aQ = 1)
    (x : Matrix (Fin n) (Fin n) A) : aP * x * aQ - 1 = aP * (x - 1) * aQ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]

end Gen

variable {D : D7} {V V' : HSp D} (I : IsoMat V V')

/- English proof (translation)
Rewrite using `[← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]`.
-/
theorem cT_P_gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q := by
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

/- English proof (translation)
The claim follows from `conj_sub_one I.aP_aQ _`.
-/
theorem mat_kap_sub (g : GA D V) :
    (matHom V' (I.kap g)).1 - 1 = HMul.hMul (HMul.hMul I.aP ((matHom V g).1 - 1)) I.aQ :=
  conj_sub_one I.aP_aQ _

/- English proof (translation)
Establish `key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce `g hg`. Use `show I.kap g ∈ NI V' (I.P * C)`. Take `⟨h1, h2, h3⟩` from `hg`.

Use `Subgroup.subset_closure ?_` and prove the remaining obligations. Establish `hm` using `I.mat_kap_sub g`. Establish `hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D)` using `Matrix.map_mul`. Establish `hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q`. Rewrite using `[cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]`.

Establish `hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ`. Rewrite using `[hG, Matrix.map_mul]`. Both sides reduce to the same expression. Use `⟨?_, ?_, fun x' hx' => ?_⟩` and prove the remaining obligations. Use `show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0`.

Rewrite using `[hm, hPC]`. Conclude with `conj_right_zero I.aQ_aP h1`. Use `show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D)) ((matHom V' (I.kap g)).1 - 1) = 0`. Rewrite using `[hGm, hm]`. Conclude with `conj_left_zero I.aQ_aP h2`.

Establish `hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0`. Rewrite using `[Matrix.mulVec_mulVec, ← hG]`. Conclude with `hx'`. Take `⟨a, ha⟩` from `h3 _ hx`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i)`. Use function extensionality and compare the values at `fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm`. Use `show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a`. Rewrite using `[hm, hPC]`. Use `conj_mulVec _ _ _ _ _ _ ?_` and prove the remaining obligations.

Rewrite using `[hQx]`. Conclude with `ha`. Conclude with `key hx`.
-/
theorem kap_mem_NI {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : GA D V} (hx : x ∈ NI V C) :
    I.kap x ∈ NI V' (I.P * C) := by
  have key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    show I.kap g ∈ NI V' (I.P * C)
    obtain ⟨h1, h2, h3⟩ := hg
    refine Subgroup.subset_closure ?_
    have hm := I.mat_kap_sub g
    have hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D) := Matrix.map_mul
    have hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram =
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q := by
      rw [cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]
    have hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ := by
      rw [hG, Matrix.map_mul]; rfl
    refine ⟨?_, ?_, fun x' hx' => ?_⟩
    · show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0
      rw [hm, hPC]
      exact conj_right_zero I.aQ_aP h1
    · show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D))
        ((matHom V' (I.kap g)).1 - 1) = 0
      rw [hGm, hm]
      exact conj_left_zero I.aQ_aP h2
    · have hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0 := by
        rw [Matrix.mulVec_mulVec, ← hG]
        exact hx'
      obtain ⟨a, ha⟩ := h3 _ hx
      refine ⟨a, ?_⟩
      have hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i) :=
        funext fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm
      show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a
      rw [hm, hPC]
      refine conj_mulVec _ _ _ _ _ _ ?_
      rw [hQx]
      exact ha
  exact key hx

/- English proof (translation)
Take `⟨hr, hli, hiso⟩` from `h`. Use `⟨hr, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose`. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression.

Rewrite using `[e]`. Use `hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)` and prove the remaining obligations. Use `congrArg I.P.mulVec hab` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, I.PQ]`. Establish `hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram` using `I.symm.gram`.

Rewrite using `[cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hg]; exact hiso`.
-/
theorem isIsoFrame_Q {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} (h : IsIsoFrame V' C') :
    IsIsoFrame V (I.Q * C') := by
  obtain ⟨hr, hli, hiso⟩ := h
  refine ⟨hr, ?_, ?_⟩
  · have e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose := by
      funext i j
      rfl
    rw [e]
    refine hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)
    have := congrArg I.P.mulVec hab
    simpa [Matrix.mulVec_mulVec, I.PQ] using this
  · have hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram := I.symm.gram
    rw [cT_mul]
    calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' *
          (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q) * C' := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg]; exact hiso

/- English proof (translation)
Use `I.kap_mem_NI (I.Q * C') hx` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, I.PQ, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem kap_mem_NI' {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {x : GA D V} (hx : x ∈ NI V (I.Q * C')) :
    I.kap x ∈ NI V' C' := by
  have := I.kap_mem_NI (I.Q * C') hx
  rwa [← Matrix.mul_assoc, I.PQ, Matrix.one_mul] at this

/- English proof (translation)
The claim follows from `I.symm.kap_mem_NI C' hy`.
-/
theorem kap_symm_mem_NI {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {y : GA D V'} (hy : y ∈ NI V' C') :
    I.kap.symm y ∈ NI V (I.Q * C') :=
  I.symm.kap_mem_NI C' hy

end GlobalTheory.Mem.Isom.IsoMat

open GlobalTheory.Mem.Isom GlobalTheory.Mem.Isom.IsoMat in

/- English proof (translation)
Introduce `D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g`. Use `haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')`. Use `haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'`. Use `haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V`. Use `haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'`.

Set `T : NI V (I.Q * C') ≃ₜ* NI V' C'` to `{ toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩ invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩ left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V)) right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V')) map_mul …`. Set `e : NI V (I.Q * C') ≃ᵐ NI V' C'` to `T.toHomeomorph.toMeasurableEquiv`. Establish `hp : MeasurePreserving e (μ.map e.symm) μ` using `(MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)`. Establish `hH : (μ.map e.symm).IsHaarMeasure` using `T.symm.isHaarMeasure_map μ`. Establish `hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm)`.

Use `h𝓕.preimage_of_equiv hp.quasiMeasurePreserving (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_` and prove the remaining obligations. Conclude with `Subtype.ext (T.symm.injective (congrArg Subtype.val hab))`. Conclude with `⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩`. Express the relevant statement in the definitionally equal form `T (T.symm γ * x) = γ * T x`. Rewrite using `[map_mul, T.apply_symm_apply]`.

Establish `key` using `hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)`. Rewrite using `[← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x`.

Use `show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)`. Rewrite using `[map_mul, MulEquiv.symm_apply_apply]`.
-/
theorem GlobalTheory.Mem.Isom.isCuspFun_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ),
    IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  intro D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'
  let T : NI V (I.Q * C') ≃ₜ* NI V' C' :=
    { toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩
      invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩
      left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V))
      right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V'))
      map_mul' := fun x y => Subtype.ext (map_mul I.kap (x : GA D V) (y : GA D V))
      continuous_toFun := (I.continuous_kap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (I.continuous_kap_symm.comp continuous_subtype_val).subtype_mk _ }
  let e : NI V (I.Q * C') ≃ᵐ NI V' C' := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (μ.map e.symm) μ :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hH : (μ.map e.symm).IsHaarMeasure := T.symm.isHaarMeasure_map μ
  have hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_
    · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
    · change T (T.symm γ * x) = γ * T x
      rw [map_mul, T.apply_symm_apply]
  have key := hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)
  rw [← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]
  refine Eq.trans ?_ key
  congr 1
  funext x
  show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)
  rw [map_mul, MulEquiv.symm_apply_apply]
