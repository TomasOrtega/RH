import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Unfold `U.embG U.muP`. Rewrite using `[Ux3.block3_mul, Ux3.block3_mul]`. Apply the tactic sequence `congr 1 <;> simp`.
-/
theorem emb_mu_uni {k p ρ : ℕ} (ν : B.Mat k ρ) (V : Matrix (Fin p) (Fin p) ℂ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ ν * U.muP k p ρ V * U.blk3 1 a b 0 1 c 0 0 1 =
      U.blk3 V (V * a) (V * b) 0 ν (ν * c) 0 0 (G.wMat p * Vᴴ⁻¹ * G.wMat p) := by
  unfold U.embG U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `h1` using `congrFun (congrFun h p.1.1) p.1.2`. Simplify using `only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2), zero_add, dif_pos p.2] at h1`. Conclude with `h1`.
-/
theorem upper_inj {p : ℕ} {u u' : G.UT p → ℂ} (h : G.upper u = G.upper u') : u = u' := by
  funext p
  have h1 := congrFun (congrFun h p.1.1) p.1.2
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2),
    zero_add, dif_pos p.2] at h1
  exact h1

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ` as an intermediate fact. Use `set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef`. Establish `hSc : IsClosed S` using `IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst)) ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))`.

Establish `hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ)`. Establish `: BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ))` using `Prod.borelSpace`. Establish `: BorelSpace (U.RC k p ρ)` using `Prod.borelSpace`. Establish `: BorelSpace (U.RC k p ρ × (G.UT p → ℂ))` using `Prod.borelSpace`. Establish `: BorelSpace (Mt k ρ × Mt k ρ)` using `Prod.borelSpace`.

Conclude with `Prod.borelSpace`. Establish `hSm : MeasurableSet S` using `hSc.measurableSet`. Establish `hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k` using `k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by`. Establish `h` using `LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'`. Unfold `LeftFubiniLemmas.muR`.

Rewrite using `[hN0, hNj]`. Conclude with `h`. Establish `hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k` using `k) (p := p) (ρ := ρ)) S := by`. Introduce `s hs s' hs' he`. Establish `he1` using `congrArg Prod.fst he`.

Establish `he2` using `congrArg Prod.snd he`. Establish `h11 : s.1.1 = s'.1.1`. Use `congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1` as an intermediate fact. Simplify `this` using `only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt]`. Establish `hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s'` using `Matrix.of.symm.injective he2`.

Take `⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1` from `⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩`. Take `⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1` from `⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩`. Unfold `LeftFubiniLemmas.NR at hN`. Rewrite `hN` using `[hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff]`. Take `⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩` from `hN`.

Establish `hUu : IsUnit (G.upper s.2.2).det` using `by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one`. Establish `hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1`. Establish `hu : s.2.2 = s'.2.2` using `upper_inj hU`. Rewrite `hUa`, `hUb` using `[← hU]`. Rewrite `hνc` using `[← hν]`.

Establish `ha : a = a'`. Use `congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul]`. Establish `hb : b = b'`. Use `congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb` as an intermediate fact.

Simplify `this` using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul]`. Establish `hc : c = c'`. Use `congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul]`. Establish `hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1` using `(Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])`.

Rewrite `hR` using `[← h11]`. Establish `hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1`. Establish `h21 : s.2.1 = s'.2.1`. Establish `e1` using `congrArg Prod.fst hR`. Establish `e2` using `congrArg Prod.snd hR`.

Simplify using `only [LeftFubiniLemmas.rcAct] at e1 e2`. Establish `e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1`. Use extensionality with `v w`. Conclude with `congrFun (congrFun e1 v) w`. Establish `e3` using `congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'`.

Simplify using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3`. Conclude with `Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2`. Establish `h12 : s.1.2 = s'.1.2`. Use extensionality with `v w`. Conclude with `congrFun (congrFun hν v) w`.

Conclude with `Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)`. Establish `hres : (LeftFubiniLemmas.muR (p` using `p) Bj).restrict S = LeftFubiniLemmas.muR Bj := Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)`. Establish `hcont : Continuous (LeftFubiniLemmas.PsiR (k` using `k) (p := p) (ρ := ρ)) := by`. Unfold `LeftFubiniLemmas.PsiR`. Conclude with `((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont`.

Establish `hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ)` using `{}`. Establish `hSB : StandardBorelSpace (LeftFubiniLemmas.XR k p ρ)` using `inferInstance`. Establish `: StandardBorelSpace S` using `hSm.standardBorel`. Establish `hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))` using `(hcont.measurable.comp measurable_subtype_coe).measurableEmbedding (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))`. Rewrite using `[LeftFubiniLemmas.kr_eq_int]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl, ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]`. Use `_ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) := hemb.integral_map _`. Use `_ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) := ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftF …`. Use `_ = _ := by rw [map_comap_subtype_coe hSm, hres]`.
-/
theorem kr_eq_integral_krI_psiR {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂(LeftFubiniLemmas.muR (p := p) Bj) := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ

  set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef
  have hSc : IsClosed S :=
    IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst))
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))
  have hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  have hSm : MeasurableSet S := hSc.measurableSet

  have hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by
    have h := LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
    unfold LeftFubiniLemmas.muR
    rw [hN0, hNj]
    exact h

  have hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) S := by
    intro s hs s' hs' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have h11 : s.1.1 = s'.1.1 := by
      have := congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1
      simpa only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt] using this
    have hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s' := Matrix.of.symm.injective he2
    obtain ⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    obtain ⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    unfold LeftFubiniLemmas.NR at hN
    rw [hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff] at hN
    obtain ⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩ := hN
    have hUu : IsUnit (G.upper s.2.2).det := by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one
    have hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1
    have hu : s.2.2 = s'.2.2 := upper_inj hU
    rw [← hU] at hUa hUb
    rw [← hν] at hνc
    have ha : a = a' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hb : b = b' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hc : c = c' := by
      have := congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul] using this
    have hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1 :=
      (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])
    rw [← h11] at hR
    have hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1
    have h21 : s.2.1 = s'.2.1 := by
      have e1 := congrArg Prod.fst hR
      have e2 := congrArg Prod.snd hR
      simp only [LeftFubiniLemmas.rcAct] at e1 e2
      have e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1 := by
        ext v w; exact congrFun (congrFun e1 v) w
      have e3 := congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3
      exact Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2
    have h12 : s.1.2 = s'.1.2 := by
      ext v w; exact congrFun (congrFun hν v) w
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)
  have hres : (LeftFubiniLemmas.muR (p := p) Bj).restrict S = LeftFubiniLemmas.muR Bj :=
    Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)
  have hcont : Continuous (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) := by
    unfold LeftFubiniLemmas.PsiR
    exact ((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont
  have hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ) := {}
  have hSB : StandardBorelSpace (LeftFubiniLemmas.XR k p ρ) := inferInstance
  have : StandardBorelSpace S := hSm.standardBorel
  have hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) :=
    (hcont.measurable.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  rw [LeftFubiniLemmas.kr_eq_int]
  calc ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN)
      = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((LeftFubiniLemmas.muR (p := p) Bj).map LeftFubiniLemmas.PsiR) := by rw [hmp.map_eq]
    _ = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))) := by
        rw [show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl,
          ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]
    _ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) :=
        hemb.integral_map _
    _ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) :=
        ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s))).symm
    _ = _ := by rw [map_comap_subtype_coe hSm, hres]

end Formalism.FourierDecayAlt.P.PBQ
