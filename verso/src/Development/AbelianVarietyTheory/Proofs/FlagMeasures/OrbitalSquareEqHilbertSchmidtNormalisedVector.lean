import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrbQuotWithDensity
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix

namespace GlobalTheory.ThA.OrbSq

/- English proof (translation)
Establish `hν : ∀ᵐ x ∂ν, x ∈ S`. Establish `h` using `hW (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)`. Establish `h0 : ∫⁻ x, Sᶜ.indicator (1 : X → ENNReal) x ∂P = 0`. Rewrite using `[lintegral_indicator_one hS.compl]`. Conclude with `hP`.

Establish `h1 : ∀ x, ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ = Sᶜ.indicator (fun _ => μ Set.univ) x`. Introduce `x`. Establish `: ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ = ∫⁻ _, Sᶜ.indicator (1 : X → ENNReal) x ∂μ`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hact] with a ha`.

Distinguish the cases in `hx : x ∈ S`. Simplify using `[hx, (ha x).2 hx]`. Establish `: act a x ∉ S` using `fun h => hx ((ha x).1 h)`. Simplify using `[hx, this]`. Rewrite using `[this, lintegral_const]`.

Apply the tactic sequence `by_cases hx : x ∈ S <;> simp [hx]`. Simplify using `only [h1] at h`. Rewrite `h` using `[h0, lintegral_indicator_const hS.compl]`. Break down `mul_eq_zero.1 h.symm with h2 | h2` into its components or cases. Conclude with `absurd (Measure.measure_univ_eq_zero.1 h2) hμ`.

Conclude with `h2`. Establish `hθ' : Measurable fun x => (θ x).toNNReal` using `hθm.real_toNNReal`. Establish `key : (P.withDensity fun x => ((θ x).toNNReal : ENNReal)).map J = c • ν.map J`. Use extensionality with `T hT`. Establish `hT' : MeasurableSet (J ⁻¹' T)` using `hJ hT`.

Rewrite using `[Measure.map_apply hJ hT, Measure.smul_apply, Measure.map_apply hJ hT, withDensity_apply _ hT', ← lintegral_indicator hT', hW _ (hθ'.coe_nnreal_ennreal.indicator hT'), smul_eq_mul, ← lintegral_indicator_const hT']`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hν] with x hx`. Distinguish the cases in `hxT : x ∈ J ⁻¹' T`. Rewrite using `[Set.indicator_of_mem hxT, ← hc x hx]`.

Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hact, hinv] with a ha hb`. Establish `: act a x ∈ J ⁻¹' T`. Rewrite using `[Set.mem_preimage, hIJ _ ((ha x).2 hx), hb x hx, ← hIJ x hx]`. Conclude with `hxT`.

Rewrite using `[Set.indicator_of_mem this]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hxT, ← lintegral_zero (μ := μ)]`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hact, hinv] with a ha hb`.

Establish `: act a x ∉ J ⁻¹' T`. Rewrite using `[Set.mem_preimage, hIJ _ ((ha x).2 hx), hb x hx, ← hIJ x hx]`. Conclude with `hxT`. Rewrite using `[Set.indicator_of_notMem this]`. Establish `e1 : ∫ x, θ x • I x ∂P = ∫ x, (θ x).toNNReal • J x ∂P`.

Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hP] with x hx`. Rewrite using `[hIJ x hx, NNReal.smul_def, Real.coe_toNNReal _ (hθ0 x)]`. Establish `e2 : ∫ x, I x ∂ν = ∫ x, J x ∂ν`. Apply `integral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [hν] with x hx`. Rewrite using `[hIJ x hx]`. Establish `e3 : ∀ m : Measure X, ∫ x, J x ∂m = ∫ y, y ∂(m.map J)` using `fun m => (integral_map (f := fun y => y) hJ.aemeasurable aestronglyMeasurable_id).symm`. Rewrite using `[e1, e2, ← integral_withDensity_eq_integral_smul hθ', e3, e3, key, integral_smul_measure]`.
-/
theorem weil_integral {X A E : Type} [MeasurableSpace X] [MeasurableSpace A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (P ν : Measure X) (μ : Measure A) (act : A → X → X) (S : Set X) (hS : MeasurableSet S)
    (hP : ∀ᵐ x ∂P, x ∈ S) (hμ : μ ≠ 0)
    (hW : ∀ f : X → ENNReal, Measurable f → ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (act a x) ∂μ) ∂ν)
    (hact : ∀ᵐ a ∂μ, ∀ x, (act a x ∈ S ↔ x ∈ S))
    (I J : X → E) (hJ : Measurable J) (hIJ : ∀ x ∈ S, J x = I x)
    (hinv : ∀ᵐ a ∂μ, ∀ x ∈ S, I (act a x) = I x)
    (θ : X → ℝ) (hθm : Measurable θ) (hθ0 : ∀ x, 0 ≤ θ x) (c : ENNReal)
    (hc : ∀ x ∈ S, ∫⁻ a, ENNReal.ofReal (θ (act a x)) ∂μ = c) :
    ∫ x, θ x • I x ∂P = c.toReal • ∫ x, I x ∂ν := by
  classical
  have hν : ∀ᵐ x ∂ν, x ∈ S := by
    have h := hW (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)
    have h0 : ∫⁻ x, Sᶜ.indicator (1 : X → ENNReal) x ∂P = 0 := by
      rw [lintegral_indicator_one hS.compl]; exact hP
    have h1 : ∀ x, ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ =
        Sᶜ.indicator (fun _ => μ Set.univ) x := by
      intro x
      have : ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ = ∫⁻ _, Sᶜ.indicator (1 : X → ENNReal) x ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hact] with a ha
        by_cases hx : x ∈ S
        · simp [hx, (ha x).2 hx]
        · have : act a x ∉ S := fun h => hx ((ha x).1 h)
          simp [hx, this]
      rw [this, lintegral_const]
      by_cases hx : x ∈ S <;> simp [hx]
    simp only [h1] at h
    rw [h0, lintegral_indicator_const hS.compl] at h
    rcases mul_eq_zero.1 h.symm with h2 | h2
    · exact absurd (Measure.measure_univ_eq_zero.1 h2) hμ
    · exact h2
  have hθ' : Measurable fun x => (θ x).toNNReal := hθm.real_toNNReal
  have key : (P.withDensity fun x => ((θ x).toNNReal : ENNReal)).map J = c • ν.map J := by
    ext T hT
    have hT' : MeasurableSet (J ⁻¹' T) := hJ hT
    rw [Measure.map_apply hJ hT, Measure.smul_apply, Measure.map_apply hJ hT, withDensity_apply _ hT',
      ← lintegral_indicator hT', hW _ (hθ'.coe_nnreal_ennreal.indicator hT'), smul_eq_mul,
      ← lintegral_indicator_const hT']
    apply lintegral_congr_ae
    filter_upwards [hν] with x hx
    by_cases hxT : x ∈ J ⁻¹' T
    · rw [Set.indicator_of_mem hxT, ← hc x hx]
      apply lintegral_congr_ae
      filter_upwards [hact, hinv] with a ha hb
      have : act a x ∈ J ⁻¹' T := by
        rw [Set.mem_preimage, hIJ _ ((ha x).2 hx), hb x hx, ← hIJ x hx]; exact hxT
      rw [Set.indicator_of_mem this]; rfl
    · rw [Set.indicator_of_notMem hxT, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards [hact, hinv] with a ha hb
      have : act a x ∉ J ⁻¹' T := by
        rw [Set.mem_preimage, hIJ _ ((ha x).2 hx), hb x hx, ← hIJ x hx]; exact hxT
      rw [Set.indicator_of_notMem this]
  have e1 : ∫ x, θ x • I x ∂P = ∫ x, (θ x).toNNReal • J x ∂P := by
    apply integral_congr_ae
    filter_upwards [hP] with x hx
    rw [hIJ x hx, NNReal.smul_def, Real.coe_toNNReal _ (hθ0 x)]
  have e2 : ∫ x, I x ∂ν = ∫ x, J x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [hIJ x hx]
  have e3 : ∀ m : Measure X, ∫ x, J x ∂m = ∫ y, y ∂(m.map J) := fun m =>
    (integral_map (f := fun y => y) hJ.aemeasurable aestronglyMeasurable_id).symm
  rw [e1, e2, ← integral_withDensity_eq_integral_smul hθ', e3, e3, key, integral_smul_measure]

abbrev sw (bs : List (ℂ × ℕ)) : C.LPt := bs.map fun b => (b.2, b.1)

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | (t, s) :: bs, i, j => by simp only [sw, List.map_cons, D.ptEntry, Formalism.MainNotions.S.ptEntry] rw [← entry_sw bs]`.
-/
theorem entry_sw : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), D.ptEntry (sw bs) i j = Formalism.MainNotions.S.ptEntry bs i j
  | [], _, _ => rfl
  | (t, s) :: bs, i, j => by
    simp only [sw, List.map_cons, D.ptEntry, Formalism.MainNotions.S.ptEntry]
    rw [← entry_sw bs]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Take `⟨a, ha, rfl⟩` from `List.mem_map.1 hb`. Conclude with `⟨(γ.2.1 a ha).2, (γ.2.1 a ha).1⟩`. Use `γ.2.2` as an intermediate fact.

Simplify `this` using `[D.ptSize, sw, List.map_map, Function.comp_def]`.
-/
theorem isLocPt_sw {n : ℕ} (γ : Point ℂ n) : D.IsLocPt (sw γ.1) n := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact ⟨(γ.2.1 a ha).2, (γ.2.1 a ha).1⟩
  · have := γ.2.2
    simpa [D.ptSize, sw, List.map_map, Function.comp_def] using this

/- English proof (translation)
Use extensionality with `a b`. Conclude with `entry_sw _ _ _`.
-/
theorem ptMat_sw {n : ℕ} (γ : Point ℂ n) : D.ptMatN (sw γ.1) n = Formalism.MainNotions.S.ptMat γ := by
  ext a b; exact entry_sw _ _ _

/- English proof (translation)
Unfold `D.ptG ThB.Gpt leadMinor`. Rewrite using `[← ptMat_sw]`. Both sides reduce to the same expression.
-/
theorem ptG_sw {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) : D.ptG (T * T') r (sw γ.1) = ThB.Gpt T T' γ := by
  unfold D.ptG ThB.Gpt leadMinor
  rw [← ptMat_sw]
  rfl

/- English proof (translation)
The claim follows from `| [], _, _ => by intro _ h; simp [D.ptSize] at h | (t, s) :: bs, a, b => by intro hab hb have e : sw ((t, s) :: bs) = (s, t) :: sw bs := rfl rw [e] at hb ⊢ rw [Formalism.FourierDecayAlt.P.Dx1.ptSize_cons] at hb simp only [blockIdx, D.ptPartner] by_cases h1 : a < s · by_cases h2 : …`.
-/
theorem block_iff : ∀ (bs : List (ℂ × ℕ)) (a b : ℕ), a < b → b < D.ptSize (sw bs) →
    (blockIdx bs a = blockIdx bs b ↔ D.ptPartner (sw bs) b < D.ptPartner (sw bs) a)
  | [], _, _ => by intro _ h; simp [D.ptSize] at h
  | (t, s) :: bs, a, b => by
    intro hab hb
    have e : sw ((t, s) :: bs) = (s, t) :: sw bs := rfl
    rw [e] at hb ⊢
    rw [Formalism.FourierDecayAlt.P.Dx1.ptSize_cons] at hb
    simp only [blockIdx, D.ptPartner]
    by_cases h1 : a < s
    · by_cases h2 : b < s
      · simp only [h1, h2, if_true, true_iff]; omega
      · simp only [h1, h2, if_true, if_false]; omega
    · have h2 : ¬ b < s := by omega
      simp only [h1, h2, if_false]
      have := block_iff bs (a - s) (b - s) (by omega) (by omega)
      omega

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[← Formalism.FourierDecayAlt.P.Dx1.ptPerm_val]`. Use `congr 1`. Rewrite using `[Equiv.symm_apply_eq, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol]`.
-/
theorem perm_symm_val (p : C.LPt) (n : ℕ) (h : D.ptSize p = n) (a : Fin n) :
    (((h ▸ D.ptPerm p : Equiv.Perm (Fin n)).symm a : Fin n) : ℕ) = D.ptPartner p a := by
  subst h
  rw [← Formalism.FourierDecayAlt.P.Dx1.ptPerm_val]
  congr 1
  rw [Equiv.symm_apply_eq, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol]

noncomputable abbrev permOf {r : ℕ} (γ : Point ℂ (r + 1)) : Equiv.Perm (Fin (r + 1)) := (isLocPt_sw γ).2 ▸ D.ptPerm (sw γ.1)

/- English proof (translation)
Simplify using `only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `and_congr_right fun hab => ?_` and prove the remaining obligations. Rewrite using `[block_iff γ.1 a b hab (by rw [(isLocPt_sw γ).2]; exact b.isLt), Fin.lt_def, perm_symm_val, perm_symm_val]`.
-/
theorem mem_rootPat {r : ℕ} (γ : Point ℂ (r + 1)) (a b : Fin (r + 1)) :
    (a, b) ∈ rootPat γ ↔ a < b ∧ (permOf γ).symm b < (permOf γ).symm a := by
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun hab => ?_
  rw [block_iff γ.1 a b hab (by rw [(isLocPt_sw γ).2]; exact b.isLt), Fin.lt_def, perm_symm_val, perm_symm_val]

noncomputable def rootEquiv {r : ℕ} (γ : Point ℂ (r + 1)) : rootPat γ ≃ C2.Lstidx (permOf γ) where
  toFun q := ⟨(q.1.2, q.1.1), (mem_rootPat γ _ _).1 q.2⟩
  invFun q := ⟨(q.1.2, q.1.1), (mem_rootPat γ _ _).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def cjE {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) : (ι → ℂ) ≃ᵐ (κ → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) e).trans
    (MeasurableEquiv.piCongrRight fun _ => Complex.conjLIE.toHomeomorph.toMeasurableEquiv)

/- English proof (translation)
Take `⟨i, rfl⟩` from `e.surjective q`. Simplify using `[cjE, MeasurableEquiv.piCongrRight, MeasurableEquiv.piCongrLeft_apply_apply]`.
-/
theorem cjE_apply {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (y : ι → ℂ) (q : κ) :
    cjE e y q = star (y (e.symm q)) := by
  obtain ⟨i, rfl⟩ := e.surjective q
  simp [cjE, MeasurableEquiv.piCongrRight, MeasurableEquiv.piCongrLeft_apply_apply]

/- English proof (translation)
Establish `h1` using `volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e`. Establish `h2 : MeasurePreserving (fun (y : κ → ℂ) (q : κ) => Complex.conjLIE (y q)) volume volume` using `volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving`. Conclude with `h2.comp h1`.
-/
theorem cjE_mp {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) : MeasurePreserving (cjE e) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e
  have h2 : MeasurePreserving (fun (y : κ → ℂ) (q : κ) => Complex.conjLIE (y q)) volume volume :=
    volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  exact h2.comp h1

section root

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2

variable {k r : ℕ} (L : LocBessel k r) (Bs : B.RealPlaceData k r L.Wp L.Wq)

/- English proof (translation)
Use function extensionality and compare the values at `q`. Rewrite using `[cjE_apply]`. Establish `hq : q.1.2.val < r` using `by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega`. Use `show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r L.z (Matrix.of x) q.1.2 q.1.1)`. Unfold `C2.uMap flagMat`.

Rewrite using `[dif_pos hq, dif_pos hq, hz]`. Conclude with `congrArg star (DF.herm_es _ _)`.
-/
theorem besselPhi_eq_reindexConj_rootCoords (hz : Bs.z = L.z) (γ : Point ℂ (r + 1)) (x : Mt k r) :
    Rad.phi0 Bs (permOf γ) x = cjE (rootEquiv γ) (rootCoords k r L.z γ x) := by
  funext q
  rw [cjE_apply]
  have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
  show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r L.z (Matrix.of x) q.1.2 q.1.1)
  unfold C2.uMap flagMat
  rw [dif_pos hq, dif_pos hq, hz]
  exact congrArg star (DF.herm_es _ _)

/- English proof (translation)
Take `⟨hw, hd⟩` from `VV.ptMatN_monoP' (sw γ.1) (r + 1) (isLocPt_sw γ).2 (isLocPt_sw γ).1`. Establish `hZw` using `hZ.trans hw`. Establish `hG : Rad.Good Bs g (permOf γ) _` using `⟨Rad.exists_rho Bs hg hpos hd hZw, Rad.u_inj Bs hg hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hg hpos hd hZw hρ⟩`. Establish `hm` using `Rad.rhoF_meas Bs hg hd hG`. Establish `hmu : D.muR Bs g (permOf γ) = (volume : Measure (C2.Lstidx (permOf γ) → ℂ)).map (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r))` using `rfl`.

Establish `hcst : ‖L.c‖ / (2 * Real.pi) = Real.pi⁻¹`. Rewrite using `[hc, cStd]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Establish `hrc : rootCoords k r L.z γ = (cjE (rootEquiv γ)).symm ∘ Rad.phi0 Bs (permOf γ)`.

Use function extensionality and compare the values at `x`. Simplify using `[besselPhi_eq_reindexConj_rootCoords L Bs hz γ x]`. Establish `hrm : Measurable (rootCoords k r L.z γ)`. Rewrite using `[hrc]`. Conclude with `(cjE (rootEquiv γ)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable`.

Unfold `IsRootMeas`. Rewrite using `[hcst]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `e1 : μ.map ((fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) ∘ (cjE (rootEquiv γ)) ∘ rootCoords k r L.z γ) = μ` using `by conv_rhs => rw [← Measure.map_id (μ := μ)]`.

Apply `Measure.map_congr` to reduce the goal to its premises. Establish `: ∀ᵐ x ∂μ, Matrix.of x ∈ C6.Rset g` using `h1`. Use `filter_upwards [this] with x hx`. Simplify using `only [Function.comp, id]`. Rewrite using `[← besselPhi_eq_reindexConj_rootCoords L Bs hz, ← Rad.rhoF_unique Bs hg hd hG _ hx]`.

Both sides reduce to the same expression. Use `Rad.u_eq_low Bs hg hd hG hx` as an intermediate fact. Rewrite using `[← Matrix.conjTranspose_conjTranspose (C2.uMap k r Bs.z (Matrix.of x)), this]`. Both sides reduce to the same expression. Rewrite using `[← e1, ← Measure.map_map hm ((cjE _).measurable.comp hrm), ← Measure.map_map (cjE _).measurable hrm, h2, Measure.map_smul, Measure.map_smul, (cjE_mp _).map_eq, hmu]`.

Introduce and unpack `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.smul_apply]`. Establish `: D.muR Bs g (permOf γ) {x | Matrix.of x ∉ RStab k r g} = 0` using `(Rad.haar_good Bs hg hd hG).conc`. Rewrite using `[this, smul_zero]`.

Rewrite using `[Measure.map_smul, hmu, Measure.map_map hrm hm]`. Use `congr 1`. Establish `: rootCoords k r L.z γ ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) = (cjE (rootEquiv γ)).symm`. Use function extensionality and compare the values at `x`. Rewrite using `[hrc]`.

Simplify using `only [Function.comp]`. Rewrite using `[Rad.coordMap_hermRep_leftInverse Bs hg hd hG]`. Rewrite using `[this, (cjE_mp _).symm.map_eq]`.
-/
theorem rootMeas_iff (hz : Bs.z = L.z) (hc : L.c = cStd) (γ : Point ℂ (r + 1)) {g : B.Mat k r}
    (hg : g ∈ B.GV k r) (hZ : Zhat k r Bs.z Bs.z' g = D.ptMatN (sw γ.1) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' g)
    (μ : Measure (Mt k r)) :
    IsRootMeas L γ g μ ↔ μ = ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • D.muR Bs g (permOf γ) := by
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw γ.1) (r + 1) (isLocPt_sw γ).2 (isLocPt_sw γ).1
  have hZw := hZ.trans hw
  have hG : Rad.Good Bs g (permOf γ) _ :=
    ⟨Rad.exists_rho Bs hg hpos hd hZw, Rad.u_inj Bs hg hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hg hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hg hd hG
  have hmu : D.muR Bs g (permOf γ) = (volume : Measure (C2.Lstidx (permOf γ) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) := rfl
  have hcst : ‖L.c‖ / (2 * Real.pi) = Real.pi⁻¹ := by
    rw [hc, cStd]; simp; field_simp
  have hrc : rootCoords k r L.z γ = (cjE (rootEquiv γ)).symm ∘ Rad.phi0 Bs (permOf γ) := by
    funext x; simp [besselPhi_eq_reindexConj_rootCoords L Bs hz γ x]
  have hrm : Measurable (rootCoords k r L.z γ) := by
    rw [hrc]; exact (cjE (rootEquiv γ)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  unfold IsRootMeas
  rw [hcst]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : μ.map ((fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) ∘ (cjE (rootEquiv γ)) ∘
        rootCoords k r L.z γ) = μ := by
      conv_rhs => rw [← Measure.map_id (μ := μ)]
      apply Measure.map_congr
      have : ∀ᵐ x ∂μ, Matrix.of x ∈ C6.Rset g := h1
      filter_upwards [this] with x hx
      simp only [Function.comp, id]
      rw [← besselPhi_eq_reindexConj_rootCoords L Bs hz, ← Rad.rhoF_unique Bs hg hd hG _ hx]
      · rfl
      · have := Rad.u_eq_low Bs hg hd hG hx
        rw [← Matrix.conjTranspose_conjTranspose (C2.uMap k r Bs.z (Matrix.of x)), this]; rfl
    rw [← e1, ← Measure.map_map hm ((cjE _).measurable.comp hrm), ← Measure.map_map (cjE _).measurable hrm, h2,
      Measure.map_smul, Measure.map_smul, (cjE_mp _).map_eq, hmu]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Measure.smul_apply]
      have : D.muR Bs g (permOf γ) {x | Matrix.of x ∉ RStab k r g} = 0 := (Rad.haar_good Bs hg hd hG).conc
      rw [this, smul_zero]
    · rw [Measure.map_smul, hmu, Measure.map_map hrm hm]
      congr 1
      have : rootCoords k r L.z γ ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) =
          (cjE (rootEquiv γ)).symm := by
        funext x
        rw [hrc]
        simp only [Function.comp]
        rw [Rad.coordMap_hermRep_leftInverse Bs hg hd hG]
      rw [this, (cjE_mp _).symm.map_eq]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, -⟩` from `hS`. Use function extensionality and compare the values at `p`. Unfold `besselIntg D.orbIntegrand B.rho B.sgs B.xiTau B.lam psi`. Rewrite using `[h1, h2, h3, h4, hc]`. Use `congr 1`.

Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intg_eq {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hS : IsStdOf L μsec Bs) (hc : L.c = cStd)
    (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)) (g : B.Mat k r) : besselIntg L F g = D.orbIntegrand Bs g F := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hS
  funext p
  unfold besselIntg D.orbIntegrand B.rho B.sgs B.xiTau B.lam psi
  rw [h1, h2, h3, h4, hc]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/- English proof (translation)
Take `⟨-, -, -, -, h5, h6, h7, -⟩` from `hS`. Use `OrbJ.sigmaF Bs.haarW` as an intermediate fact. Use `OrbJ.sigmaF Bs.haarN` as an intermediate fact. Use `OrbJ.sigmaF Bs.haarW'` as an intermediate fact. Establish `e : L.μN = (L.κN * ENNReal.ofReal cN) • Bs.μN`.

Rewrite using `[h7, ← smul_smul, ← hN.2]`. Unfold `LocBessel.μN haarLie`. Rewrite using `[one_smul]`. Unfold `pairMeas B.RealPlaceData.μSS`. Rewrite using `[e, ← h5, ← h6, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]`.
-/
theorem pairMeas_eq {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hS : IsStdOf L μsec Bs) {cN : ℝ}
    (hN : IsRatioN k r cN) :
    pairMeas L = ((L.κN * ENNReal.ofReal cN) * (L.κN * ENNReal.ofReal cN)) • Bs.μSS := by
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := hS
  have := OrbJ.sigmaF Bs.haarW; have := OrbJ.sigmaF Bs.haarN; have := OrbJ.sigmaF Bs.haarW'
  have e : L.μN = (L.κN * ENNReal.ofReal cN) • Bs.μN := by
    rw [h7, ← smul_smul, ← hN.2]
    unfold LocBessel.μN haarLie
    rw [one_smul]
  unfold pairMeas B.RealPlaceData.μSS
  rw [e, ← h5, ← h6, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul]

end root

section cont

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2 Formalism.FourierDecayAlt.P.Dx2.OrbJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Establish `hWc` using `(P.weyl_subgroup_closed k r D.z).closed`. Establish `hWc'` using `(P.weyl_subgroup_closed k r D.z').closed`. Establish `hNc` using `(P.unipotent_radical_closed k r).closed`. Establish `e : {p | D.inSS p} = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r D.z) ∩ ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩ ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r D.z') ∩ (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r)))`. Use extensionality with `p`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))`.
-/
theorem closed_SS (D : B.RealPlaceData k r Wp Wq) : IsClosed {p | D.inSS p} := by
  have hWc := (P.weyl_subgroup_closed k r D.z).closed
  have hWc' := (P.weyl_subgroup_closed k r D.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have e : {p | D.inSS p} = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r D.z) ∩
      ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
        ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r D.z') ∩
          (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
    ext p; rfl
  rw [e]
  exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
    ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))

/- English proof (translation)
Use `set S : Set (B.SS k r) := {p | D.inSS p} with hS`. Establish `hxi : Continuous fun p : B.SS k r => B.xiTau D (1, 1) p` using `(P.B7.continuous_xi D).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))`. Establish `hπ : ContinuousOn (fun p : B.SS k r => D.π (Matrix.of p.1.1)) S` using `D.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)`. Establish `hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S` using `(P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)`. Establish `hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S` using `(P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)`.

Establish `hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S` using `(P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)`. Establish `hπ' : ContinuousOn (fun p : B.SS k r => D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S` using `D.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)`. Establish `hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S` using `(continuous_snd.snd).continuousOn`. Establish `hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S` using `(continuous_snd.fst).continuousOn`. Establish `hsgs : ContinuousOn (fun p : B.SS k r => B.sgs p γ) S` using `((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)`.

Establish `hFs : ContinuousOn (fun p : B.SS k r => F (B.sgs p γ)) S` using `hF.comp hsgs (fun p hp => P.B7.sgs_mem D hp hγ)`. Unfold `Formalism.FourierDecayAlt.D.orbIntegrand B.rho`. Conclude with `hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))`.
-/
theorem integrand_contOn (D : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (B.GV k r)) :
    ContinuousOn (Formalism.FourierDecayAlt.D.orbIntegrand D γ F) {p | D.inSS p} := by
  set S : Set (B.SS k r) := {p | D.inSS p} with hS
  have hxi : Continuous fun p : B.SS k r => B.xiTau D (1, 1) p :=
    (P.B7.continuous_xi D).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => D.π (Matrix.of p.1.1)) S :=
    D.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    D.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have hsgs : ContinuousOn (fun p : B.SS k r => B.sgs p γ) S :=
    ((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)
  have hFs : ContinuousOn (fun p : B.SS k r => F (B.sgs p γ)) S :=
    hF.comp hsgs (fun p hp => P.B7.sgs_mem D hp hγ)
  unfold Formalism.FourierDecayAlt.D.orbIntegrand B.rho
  exact hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))

/- English proof (translation)
Establish `hN` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Conclude with `⟨hp.1, hN.mul_mem _ hρ.1 _ hp.2.1, hp.2.2.1, hN.mul_mem _ hρ.2 _ hp.2.2.2⟩`.
-/
theorem act_inSS (D : B.RealPlaceData k r Wp Wq) {γ ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) (p : B.SS k r)
    (hp : D.inSS p) : D.inSS (C6.actR γ ρ p) := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  exact ⟨hp.1, hN.mul_mem _ hρ.1 _ hp.2.1, hp.2.2.1, hN.mul_mem _ hρ.2 _ hp.2.2.2⟩

/- English proof (translation)
Use `⟨fun h => ?_, act_inSS D hρ p⟩` and prove the remaining obligations. Use `act_inSS D ((closedR (isUnit_of_G hγ)).inv_mem ρ hρ) _ h` as an intermediate fact. Rewrite `this` using `[act_act γ (isUnit_of_G hγ) (isUnit_of_N hρ.1)]`. Then use the resulting hypothesis.
-/
theorem act_inSS_iff (D : B.RealPlaceData k r Wp Wq) {γ ρ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hρ : ρ ∈ C6.Rset γ)
    (p : B.SS k r) : D.inSS (C6.actR γ ρ p) ↔ D.inSS p := by
  refine ⟨fun h => ?_, act_inSS D hρ p⟩
  have := act_inSS D ((closedR (isUnit_of_G hγ)).inv_mem ρ hρ) _ h
  rwa [act_act γ (isUnit_of_G hγ) (isUnit_of_N hρ.1)] at this

/- English proof (translation)
Establish `h : B.hsInner (VV.CinL D hA hB X) (VV.CinL D hA hB X) = B.hsInner X X`. Rewrite using `[VV.CinL_apply, VV.Cin, PBI.hsInner_comp_left _ (D.π_unitary _ hhA), PBI.hsInner_comp_right _ (D.π'_unitary _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB))]`. Unfold `B.hsInner at h`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Conclude with `h` after adjusting the coercions.
-/
theorem hs_Cin [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {hA hB : B.Mat k r}
    (hhA : hA ∈ UWset k r D.z) (hhB : hB ∈ UWset k r D.z') (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (VV.CinL D hA hB X)‖ ^ 2 = ‖B.hsVec X‖ ^ 2 := by
  have h : B.hsInner (VV.CinL D hA hB X) (VV.CinL D hA hB X) = B.hsInner X X := by
    rw [VV.CinL_apply, VV.Cin, PBI.hsInner_comp_left _ (D.π_unitary _ hhA),
      PBI.hsInner_comp_right _ (D.π'_unitary _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB))]
  unfold B.hsInner at h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `hsNormSq Formalism.MainNotions.S.hsInner`. Rewrite using `[Complex.re_sum, PiLp.norm_sq_eq_of_L2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`.
-/
theorem hsNormSq_hsVec [FiniteDimensional ℂ Wq] (X : Wq →L[ℂ] Wp) : hsNormSq X = ‖B.hsVec X‖ ^ 2 := by
  unfold hsNormSq Formalism.MainNotions.S.hsInner
  rw [Complex.re_sum, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/- English proof (translation)
Use `⟨?_, fun a ha => ?_, fun a ha => ?_, fun K hK => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, h.conc, smul_zero]`. Rewrite using `[Measure.map_smul, h.left a ha]`. Rewrite using `[Measure.map_smul, h.right a ha]`. Rewrite using `[Measure.smul_apply, smul_eq_mul]`.

Conclude with `ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)`. Introduce `e`. Establish `e2 : c * μ Set.univ = 0` using `congrArg (fun m : Measure (Mt k r) => m Set.univ) e`. Conclude with `(mul_eq_zero.1 e2).elim h0 fun e3 => h.ne_zero (Measure.measure_univ_eq_zero.1 e3)`.
-/
theorem haar_smul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ENNReal} (h0 : c ≠ 0)
    (h1 : c ≠ ⊤) : B.IsHaarOn U (c • μ) := by
  refine ⟨?_, fun a ha => ?_, fun a ha => ?_, fun K hK => ?_, ?_⟩
  · rw [Measure.smul_apply, h.conc, smul_zero]
  · rw [Measure.map_smul, h.left a ha]
  · rw [Measure.map_smul, h.right a ha]
  · rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)
  · intro e
    have e2 : c * μ Set.univ = 0 := congrArg (fun m : Measure (Mt k r) => m Set.univ) e
    exact (mul_eq_zero.1 e2).elim h0 fun e3 => h.ne_zero (Measure.measure_univ_eq_zero.1 e3)

end cont

section main

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2 Formalism.FourierDecayAlt.P.Dx2.OrbJ

variable {k r : ℕ} (L : LocBessel k r) (Bs : B.RealPlaceData k r L.Wp L.Wq)

/- English proof (translation)
Establish `hcl` using `closed_SS Bs`. Establish `hco` using `integrand_contOn Bs hrel.1 hF`. Use `borelize (L.Wq →L[ℂ] L.Wp)`. Establish `ha0 : ENNReal.ofReal a⁻¹ ≠ 0` using `by simpa using ha`. Establish `hμ'` using `haar_smul hμ ha0 ENNReal.ofReal_ne_top`.

Establish `hJ : Measurable (({p | Bs.inSS p} : Set (B.SS k r)).piecewise (D.orbIntegrand Bs g F) 0)` using `hco.measurable_piecewise continuousOn_const hcl.measurableSet`. Establish `hP : ∀ᵐ x ∂(pairMeas L), x ∈ ({p | Bs.inSS p} : Set (B.SS k r))`. Rewrite using `[pairMeas_eq L Bs hS hN]`. Conclude with `Measure.ae_smul_measure (ae_inSS Bs) _`. Establish `key` using `weil_integral (pairMeas L) ν (ENNReal.ofReal a⁻¹ • μ) (fun x p => stabAct g (Matrix.of x) p) {p | Bs.inSS p} hcl.measurableSet hP hμ'.ne_zero hν (by filter_upwards [ae_mem hμ'] with x hx p; exact act_inSS_iff Bs hrel.1 hx p) (D.orbIntegrand Bs g F) _ hJ (fun x hx => Set.piecewise …`.

Introduce `p hp`. Establish `h1` using `hθ.2.2 p hp`. Establish `hi : Integrable (fun x : Mt k r => θ (C6.actR g (Matrix.of x) p)) μ`. Assume the negation of the conclusion as `h`. Rewrite `h1` using `[integral_undef h]`.

Conclude with `zero_ne_one h1`. Establish `h2` using `ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => hθ.2.1 _)`. Rewrite `h2` using `[h1, ENNReal.ofReal_one]`. Rewrite using `[lintegral_smul_measure]`. Establish `h3 : ∫⁻ x, ENNReal.ofReal (θ (stabAct g (Matrix.of x) p)) ∂μ = 1` using `h2.symm`.

Rewrite using `[h3, smul_eq_mul, mul_one])`. Rewrite `key` using `[pairMeas_eq L Bs hS hN, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]`. Unfold `OrbInt`. Rewrite using `[intg_eq L Bs hS hc, mul_comm _ a, mul_smul]`. Establish `e : (L.κN * ENNReal.ofReal cN * (L.κN * ENNReal.ofReal cN)).toReal = (L.κN.toReal * cN) ^ 2`.

Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hN.1.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[e]`. Rewrite using `[key, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]`.
-/
theorem orbInt_eq {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hS : IsStdOf L μsec Bs) (hc : L.c = cStd)
    {cN : ℝ} (hN : IsRatioN k r cN) {F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)} (hF : ContinuousOn F (B.GV k r))
    {g : B.Mat k r} (hrel : C6.IsRelevant Bs g) {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (C6.Rset g) μ)
    {a : ℝ} (ha : 0 < a) {ν : Measure (PairSp k r)} (hν : IsOrbQuot L g (ENNReal.ofReal a⁻¹ • μ) ν)
    {θ : B.SS k r → ℝ} (hθ : D.IsNormCut Bs g μ θ) :
    OrbInt L F g ν = ((L.κN.toReal * cN) ^ 2 * a) • ∫ p, θ p • D.orbIntegrand Bs g F p ∂Bs.μSS := by
  classical
  have hcl := closed_SS Bs
  have hco := integrand_contOn Bs hrel.1 hF
  borelize (L.Wq →L[ℂ] L.Wp)
  have ha0 : ENNReal.ofReal a⁻¹ ≠ 0 := by simpa using ha
  have hμ' := haar_smul hμ ha0 ENNReal.ofReal_ne_top
  have hJ : Measurable (({p | Bs.inSS p} : Set (B.SS k r)).piecewise (D.orbIntegrand Bs g F) 0) :=
    hco.measurable_piecewise continuousOn_const hcl.measurableSet
  have hP : ∀ᵐ x ∂(pairMeas L), x ∈ ({p | Bs.inSS p} : Set (B.SS k r)) := by
    rw [pairMeas_eq L Bs hS hN]
    exact Measure.ae_smul_measure (ae_inSS Bs) _
  have key := weil_integral (pairMeas L) ν (ENNReal.ofReal a⁻¹ • μ) (fun x p => stabAct g (Matrix.of x) p)
    {p | Bs.inSS p} hcl.measurableSet hP hμ'.ne_zero hν
    (by filter_upwards [ae_mem hμ'] with x hx p; exact act_inSS_iff Bs hrel.1 hx p)
    (D.orbIntegrand Bs g F) _ hJ (fun x hx => Set.piecewise_eq_of_mem _ _ _ hx)
    (by filter_upwards [ae_mem hμ'] with x hx p hp; exact integrand_act Bs g F hrel hx p hp.2.1 hp.2.2.2)
    θ hθ.1 hθ.2.1 (ENNReal.ofReal a⁻¹) (by
      intro p hp
      have h1 := hθ.2.2 p hp
      have hi : Integrable (fun x : Mt k r => θ (C6.actR g (Matrix.of x) p)) μ := by
        by_contra h
        rw [integral_undef h] at h1
        exact zero_ne_one h1
      have h2 := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => hθ.2.1 _)
      rw [h1, ENNReal.ofReal_one] at h2
      rw [lintegral_smul_measure]
      have h3 : ∫⁻ x, ENNReal.ofReal (θ (stabAct g (Matrix.of x) p)) ∂μ = 1 := h2.symm
      rw [h3, smul_eq_mul, mul_one])
  rw [pairMeas_eq L Bs hS hN, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at key
  unfold OrbInt
  rw [intg_eq L Bs hS hc, mul_comm _ a, mul_smul]
  have e : (L.κN * ENNReal.ofReal cN * (L.κN * ENNReal.ofReal cN)).toReal = (L.κN.toReal * cN) ^ 2 := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hN.1.le]; ring
  rw [e] at key
  rw [key, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/- English proof (translation)
Take `⟨g₀, hg₀, hZ₀, hD₀⟩` from `exists_isotropic_frame k r _ _ Bs ν' m₀ p hb hp hG`. Rewrite using `[isotropic_vectors_linear_indep k r _ _ Bs ν' m₀ F p hp g₀ hb hG hg₀ hZ₀ hD₀]`. Establish `hpos : 0 < Gf k r Bs.z Bs.z' g₀`. Rewrite using `[← ptG_spec k r Bs.z Bs.z' p _ hp hZ₀]`. Conclude with `hG`.

Take `⟨s, hs, s', hs', hγs⟩` from `fibre_orbit_description k r Bs.z Bs.z' ⟨Bs.k_pos, VV.std_vector_z Bs, VV.std_vector_z_prime Bs⟩ _ hg₀ g hg hpos (hZ₀.trans hZ.symm)`. Take `⟨hA, hhA, nA, hnA, hfA, rfl⟩` from `VV.stabilizer_decomp_unitary_mul_unipotent (VV.std_vector_z Bs) hs`. Take `⟨hB, hhB, nB, hnB, hfB, rfl⟩` from `VV.stabilizer_decomp_unitary_mul_unipotent (VV.std_vector_z_prime Bs) hs'`. Substitute `hγs` using the available equality. Rewrite using `[← VV.orbJ_pt Bs p hp hg₀ hZ₀ hpos hhA hnA hfA hhB hnB hfB F, hs_Cin Bs hhA hhB]`.
-/
theorem hs_orbJ {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r} (hb : D.IsBaseFrame Bs ν' m₀)
    (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)) (p : C.LPt) (hp : D.IsLocPt p (r + 1))
    (hG : 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r p) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' g = D.ptMatN p (r + 1)) :
    ‖B.hsVec (D.orbJ Bs g (D.muR Bs g (hp.2 ▸ D.ptPerm p)) F)‖ ^ 2 = ‖B.hsVec (D.vecV Bs ν' m₀ F p)‖ ^ 2 := by
  obtain ⟨g₀, hg₀, hZ₀, hD₀⟩ := exists_isotropic_frame k r _ _ Bs ν' m₀ p hb hp hG
  rw [isotropic_vectors_linear_indep k r _ _ Bs ν' m₀ F p hp g₀ hb hG hg₀ hZ₀ hD₀]
  have hpos : 0 < Gf k r Bs.z Bs.z' g₀ := by
    rw [← ptG_spec k r Bs.z Bs.z' p _ hp hZ₀]; exact hG
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, VV.std_vector_z Bs, VV.std_vector_z_prime Bs⟩ _ hg₀ g hg hpos (hZ₀.trans hZ.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := VV.stabilizer_decomp_unitary_mul_unipotent (VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := VV.stabilizer_decomp_unitary_mul_unipotent (VV.std_vector_z_prime Bs) hs'
  subst hγs
  rw [← VV.orbJ_pt Bs p hp hg₀ hZ₀ hpos hhA hnA hfA hhB hnB hfB F, hs_Cin Bs hhA hhB]

end main

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2 in

/- English proof (translation)
Take `⟨c₃, hconv⟩` from `Dx3.d_orbJConv`. Use `⟨c₃, ?_⟩` and prove the remaining obligations. Introduce `k r L μsec Bs cN A ν' m₀ F hS hN hc _ hκ hb hA hF γ hγ`. Establish `hz : Bs.z = L.z` using `hS.1`. Establish `hz' : Bs.z' = L.z'` using `hS.2.1`.

Establish `hp` using `isLocPt_sw γ`. Establish `hG : 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r (sw γ.1)` using `by rw [hz, hz', ptG_sw]; exact hγ`. Establish `hFc : ContinuousOn F (B.GV k r)`. Take `⟨c, hc⟩` from `hF`. Conclude with `B5.ckOn_continuousOn hc.1`.

Take `⟨hw, hd⟩` from `VV.ptMatN_monoP' (sw γ.1) (r + 1) hp.2 hp.1`. Establish `hπ : 0 < Real.pi ^ (rootPat γ).card` using `by positivity`. Establish `facts : ∀ g ∈ B.GV k r, Zhat k r Bs.z Bs.z' g = D.ptMatN (sw γ.1) (r + 1) → 0 < Gf k r Bs.z Bs.z' g ∧ C6.IsRelevant Bs g ∧ B.IsHaarOn (C6.Rset g) (D.muR Bs g (permOf γ)) ∧ ∃ θ, D.IsNormCut Bs g (D.muR Bs g (permOf γ)) θ ∧ Integrable (fun p => θ p • D.orbIntegrand Bs g F p) Bs.μSS`. Introduce `g hg hZ`. Establish `hpos : 0 < Gf k r Bs.z Bs.z' g`.

Rewrite using `[← ptG_spec k r Bs.z Bs.z' _ _ hp hZ]`. Conclude with `hG`. Establish `hrel` using `relevant_points_holds k r _ _ Bs _ g hp hg hZ`. Conclude with `⟨hpos, hrel, radial_measure_is_haar k r _ _ Bs g _ _ hg hd (hZ.trans hw), hconv k r _ _ Bs g _ _ A F hg hrel hd (hZ.trans hw) hpos hA hF⟩`. Establish `val : ∀ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν → hsNormSq (OrbInt L F g ν) = (L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 * ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2`.

Introduce and unpack `g μR ν ⟨⟨hg, hZ⟩, -, hR, hQ⟩`. Rewrite `hZ` using `[← hz, ← hz', ← ptMat_sw]`. Take `⟨hpos, hrel, hH, hex⟩` from `facts g hg hZ`. Rewrite `hQ` using `[(rootMeas_iff L Bs hz hc γ hg hZ hpos μR).1 hR, inv_pow]`. Rewrite using `[orbInt_eq L Bs hS hc hN hFc hrel hH hπ hQ hex.choose_spec.1, ← hs_orbJ L Bs hb F _ hp hG hg hZ]`.

Unfold `D.orbJ`. Rewrite using `[dif_pos hex, hsNormSq_hsVec]`. Generalize the expression as in `(∫ p, hex.choose p • D.orbIntegrand Bs g F p ∂Bs.μSS) = X`. Establish `e : ∀ t : ℝ, B.hsVec (t • X) = t • B.hsVec X` using `fun _ => rfl`. Rewrite using `[e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]`.

Expand and normalize the polynomial expressions, which then agree. Apply `le_antisymm` to reduce the goal to its premises. Unfold `ThB.orbSq`. Use `iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_` and prove the remaining obligations. Rewrite using `[val g μR ν h]`.

Take `⟨g, hg, hZ, -⟩` from `exists_isotropic_frame k r _ _ Bs ν' m₀ _ hb hp hG`. Take `⟨hpos, hrel, hH, θ, hθ, -⟩` from `facts g hg hZ`. Establish `ha0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0`. Establish `: 0 < Real.pi⁻¹ ^ (rootPat γ).card` using `by positivity`. Simplify using `using this`.

Establish `hQ` using `GlobalTheory.ThA.QuotCut.isOrbQuot_withDensity k r L g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • D.muR Bs g (permOf γ)) (fun p => Real.pi ^ (rootPat γ).card * θ p) cN hN hκ hg (haar_smul hH ha0 ENNReal.ofReal_ne_top) (hθ.1.const_mul _) (fun p => mul_nonneg hπ.le (hθ.2.1 p) …`. Introduce `p h1 h2 h3 h4`. Establish `h5 : ∫ a, θ (stabAct g (Matrix.of a) p) ∂(D.muR Bs g (permOf γ)) = 1` using `hθ.2.2 p ⟨by rw [hz]; exact h3, h1, by rw [hz']; exact h4, h2⟩`. Rewrite using `[integral_smul_measure, integral_const_mul, h5, ENNReal.toReal_ofReal (by positivity), inv_pow, smul_eq_mul, mul_one, inv_mul_cancel₀ hπ.ne'])`. Establish `hadm : IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g _ ∧ IsOrbQuot L g _ _` using `⟨⟨hg, by rw [← hz, ← hz', ← ptMat_sw]; exact hZ⟩, fun a ha => by rw [hc, ← hz, ← hz']; exact hrel.2 a ha, (rootMeas_iff L Bs hz hc γ hg hZ hpos _).2 rfl, hQ⟩`.

Rewrite using `[← val _ _ _ hadm]`. Unfold `ThB.orbSq`. Conclude with `le_iSup_of_le g (le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le hadm le_rfl)))`.
-/
theorem orbSq_eq_vecV : ∃ c₃ : ℝ, ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN A : ℝ) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.IsBaseFrame Bs ν' m₀ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 F → ∀ γ : Point ℂ (r + 1), 0 < ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ → ThB.orbSq L F γ = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 * ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2) := by
  obtain ⟨c₃, hconv⟩ := Dx3.d_orbJConv
  refine ⟨c₃, ?_⟩
  intro k r L μsec Bs cN A ν' m₀ F hS hN hc _ hκ hb hA hF γ hγ
  have hz : Bs.z = L.z := hS.1
  have hz' : Bs.z' = L.z' := hS.2.1
  have hp := isLocPt_sw γ
  have hG : 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r (sw γ.1) := by rw [hz, hz', ptG_sw]; exact hγ
  have hFc : ContinuousOn F (B.GV k r) := by
    obtain ⟨c, hc⟩ := hF
    exact B5.ckOn_continuousOn hc.1
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw γ.1) (r + 1) hp.2 hp.1
  have hπ : 0 < Real.pi ^ (rootPat γ).card := by positivity
  have facts : ∀ g ∈ B.GV k r, Zhat k r Bs.z Bs.z' g = D.ptMatN (sw γ.1) (r + 1) →
      0 < Gf k r Bs.z Bs.z' g ∧ C6.IsRelevant Bs g ∧ B.IsHaarOn (C6.Rset g) (D.muR Bs g (permOf γ)) ∧
      ∃ θ, D.IsNormCut Bs g (D.muR Bs g (permOf γ)) θ ∧
        Integrable (fun p => θ p • D.orbIntegrand Bs g F p) Bs.μSS := by
    intro g hg hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' g := by
      rw [← ptG_spec k r Bs.z Bs.z' _ _ hp hZ]; exact hG
    have hrel := relevant_points_holds k r _ _ Bs _ g hp hg hZ
    exact ⟨hpos, hrel, radial_measure_is_haar k r _ _ Bs g _ _ hg hd (hZ.trans hw),
      hconv k r _ _ Bs g _ _ A F hg hrel hd (hZ.trans hw) hpos hA hF⟩
  have val : ∀ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν →
      hsNormSq (OrbInt L F g ν) = (L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 *
        ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2 := by
    rintro g μR ν ⟨⟨hg, hZ⟩, -, hR, hQ⟩
    rw [← hz, ← hz', ← ptMat_sw] at hZ
    obtain ⟨hpos, hrel, hH, hex⟩ := facts g hg hZ
    rw [(rootMeas_iff L Bs hz hc γ hg hZ hpos μR).1 hR, inv_pow] at hQ
    rw [orbInt_eq L Bs hS hc hN hFc hrel hH hπ hQ hex.choose_spec.1, ← hs_orbJ L Bs hb F _ hp hG hg hZ]
    unfold D.orbJ
    rw [dif_pos hex, hsNormSq_hsVec]
    generalize (∫ p, hex.choose p • D.orbIntegrand Bs g F p ∂Bs.μSS) = X
    have e : ∀ t : ℝ, B.hsVec (t • X) = t • B.hsVec X := fun _ => rfl
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  apply le_antisymm
  · unfold ThB.orbSq
    refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    rw [val g μR ν h]
  · obtain ⟨g, hg, hZ, -⟩ := exists_isotropic_frame k r _ _ Bs ν' m₀ _ hb hp hG
    obtain ⟨hpos, hrel, hH, θ, hθ, -⟩ := facts g hg hZ
    have ha0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
      have : 0 < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
      simpa using this
    have hQ := GlobalTheory.ThA.QuotCut.isOrbQuot_withDensity k r L g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • D.muR Bs g (permOf γ))
      (fun p => Real.pi ^ (rootPat γ).card * θ p) cN hN hκ hg (haar_smul hH ha0 ENNReal.ofReal_ne_top)
      (hθ.1.const_mul _) (fun p => mul_nonneg hπ.le (hθ.2.1 p)) (by
        intro p h1 h2 h3 h4
        have h5 : ∫ a, θ (stabAct g (Matrix.of a) p) ∂(D.muR Bs g (permOf γ)) = 1 :=
          hθ.2.2 p ⟨by rw [hz]; exact h3, h1, by rw [hz']; exact h4, h2⟩
        rw [integral_smul_measure, integral_const_mul, h5, ENNReal.toReal_ofReal (by positivity), inv_pow,
          smul_eq_mul, mul_one, inv_mul_cancel₀ hπ.ne'])
    have hadm : IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g _ ∧ IsOrbQuot L g _ _ :=
      ⟨⟨hg, by rw [← hz, ← hz', ← ptMat_sw]; exact hZ⟩,
        fun a ha => by rw [hc, ← hz, ← hz']; exact hrel.2 a ha,
        (rootMeas_iff L Bs hz hc γ hg hZ hpos _).2 rfl, hQ⟩
    rw [← val _ _ _ hadm]
    unfold ThB.orbSq
    exact le_iSup_of_le g (le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le hadm le_rfl)))

end GlobalTheory.ThA.OrbSq
