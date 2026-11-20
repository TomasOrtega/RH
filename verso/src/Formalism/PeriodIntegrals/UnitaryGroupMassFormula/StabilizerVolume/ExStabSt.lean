import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeilQuotMeas

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k`. Rewrite using `[hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]`.
-/
theorem orb_mk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Establish `: g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) = ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0)` using `rfl`. Rewrite using `[this, orb_mk, mul_smul]`.
-/
theorem orb_smul (x0 : X) (g : G) (q : G ⧸ MulAction.stabilizer G x0) :
    (g • q).out • x0 = g • (q.out • x0) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  have : g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) =
      ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0) := rfl
  rw [this, orb_mk, mul_smul]

/- English proof (translation)
Use `hνH` as an intermediate fact. Use `set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef`. Take `⟨ρ, hρ0, hρfin, hρinv, hρF, hρU⟩` from `PI.weil_quotient_measure G (MulAction.stabilizer G x0) hcl μ ν inferInstance hμr inferInstance hνr`. Establish `hrange : ∀ y, y ∈ Set.range ι ↔ ∃ g : G, g • x0 = y`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨q.out, rfl⟩`. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨(g : G ⧸ MulAction.stabilizer G x0), orb_mk x0 g⟩`.

Use `set ρ' : Measure (G ⧸ MulAction.stabilizer G x0) := νX.comap ι with hρ'def`. Establish `hmap : ρ'.map ι = νX`. Rewrite using `[hρ'def, hemb.map_comap]`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises. Rewrite using `[ae_iff]`.

Use `hnull using 2` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, hrange]`. Establish `hρ'inv : ∀ (g : G) (s : Set (G ⧸ MulAction.stabilizer G x0)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s`. Introduce `g s hs`.

Rewrite using `[hρ'def, hemb.comap_apply, hemb.comap_apply]`. Establish `himg : ι '' ((fun y => g • y) ⁻¹' s) = (fun y => g • y) ⁻¹' (ι '' s)`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨q, hq, rfl⟩`. Conclude with `⟨g • q, hq, orb_smul x0 g q⟩`. Introduce and unpack `⟨q', hq', hy⟩`. Use `⟨g⁻¹ • q', by simpa [smul_smul] using hq', ?_⟩` and prove the remaining obligations. Use `show (g⁻¹ • q').out • x0 = y`.

Rewrite using `[orb_smul x0 g⁻¹ q']`. Use `show g⁻¹ • ι q' = y`. Rewrite using `[hy, inv_smul_smul]`. Rewrite using `[himg]`. Conclude with `hinv g _ (hemb.measurableSet_image.2 hs)`.

Establish `hρ'fin : ∀ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K → ρ' K < ⊤`. Introduce `K hK`. Rewrite using `[hρ'def, hemb.comap_apply]`. Conclude with `hfin _ (hK.image hcont)`. Establish `hρ'ne : ρ' ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hmap, h0, Measure.map_zero]`. Take `⟨c, hc⟩` from `hρU ρ' hρ'fin hρ'inv`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hρ'ne (by rw [hc, zero_smul])`. Establish `hK : ∃ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K ∧ ρ K ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hρ0` to reduce the goal to its premises. Apply `Measure.measure_univ_eq_zero.1` to reduce the goal to its premises. Apply `measure_mono_null (t := ⋃ n, (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) '' compactCovering G n)` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[Set.mem_iUnion]`.

Take `⟨n, hn⟩` from `Set.mem_iUnion.1 ((iUnion_compactCovering G).symm ▸ Set.mem_univ q.out)`. Conclude with `⟨n, q.out, hn, QuotientGroup.out_eq' q⟩`. Conclude with `measure_iUnion_null fun n => hcon _ ((isCompact_compactCovering G n).image QuotientGroup.continuous_mk)`. Establish `hctop : c ≠ ⊤`. Introduce and unpack `rfl`.

Take `⟨K, hKc, hKpos⟩` from `hK`. Use `hρ'fin K hKc` as an intermediate fact. Rewrite `this` using `[hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hKpos]`. Conclude with `lt_irrefl _ this`. Use `⟨c⁻¹ • ν, Measure.IsHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0), ?_⟩` and prove the remaining obligations.

Introduce `f hf s hs`. Rewrite using `[hρF f hf]`. Establish `hin : ∀ q : G ⧸ MulAction.stabilizer G x0, ∫⁻ h', f (s (ι q) * (h' : G)) ∂(c⁻¹ • ν) = c⁻¹ * ∫⁻ h, f (q.out * (h : G)) ∂ν`. Introduce `q`. Rewrite using `[lintegral_smul_measure]`.

Use `congr 1`. Establish `hsq : s (ι q) • x0 = q.out • x0` using `hs (ι q) ⟨q.out, rfl⟩`. Establish `hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0`. Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]`. Establish `hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q))` using `by group`.

Rewrite using `[hsk]`. Use `lintegral_mul_left_eq_self (μ := ν) (fun h : MulAction.stabilizer G x0 => f (q.out * (h : G))) ⟨q.out⁻¹ * s (ι q), hk⟩` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[← hmap, hemb.lintegral_map, hc, lintegral_smul_measure]`. Repeatedly rewrite using `[hin]`.

Rewrite using `[lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]`.
-/
theorem weil_orbit (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (hμr : μ.IsMulRightInvariant)
    (ν : Measure (MulAction.stabilizer G x0)) (hνH : ν.IsHaarMeasure) (hνr : ν.IsMulRightInvariant)
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX := by
  classical
  have := hνH
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  obtain ⟨ρ, hρ0, hρfin, hρinv, hρF, hρU⟩ :=
    PI.weil_quotient_measure G (MulAction.stabilizer G x0) hcl μ ν inferInstance hμr inferInstance hνr

  have hrange : ∀ y, y ∈ Set.range ι ↔ ∃ g : G, g • x0 = y := by
    intro y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.out, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ MulAction.stabilizer G x0), orb_mk x0 g⟩
  set ρ' : Measure (G ⧸ MulAction.stabilizer G x0) := νX.comap ι with hρ'def
  have hmap : ρ'.map ι = νX := by
    rw [hρ'def, hemb.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    convert hnull using 2
    ext y
    simp only [Set.mem_ofPred_eq, hrange]
  have hρ'inv : ∀ (g : G) (s : Set (G ⧸ MulAction.stabilizer G x0)), MeasurableSet s →
      ρ' ((fun y => g • y) ⁻¹' s) = ρ' s := by
    intro g s hs
    rw [hρ'def, hemb.comap_apply, hemb.comap_apply]
    have himg : ι '' ((fun y => g • y) ⁻¹' s) = (fun y => g • y) ⁻¹' (ι '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, orb_smul x0 g q⟩
      · rintro ⟨q', hq', hy⟩
        refine ⟨g⁻¹ • q', by simpa [smul_smul] using hq', ?_⟩
        show (g⁻¹ • q').out • x0 = y
        rw [orb_smul x0 g⁻¹ q']
        show g⁻¹ • ι q' = y
        rw [hy, inv_smul_smul]
    rw [himg]
    exact hinv g _ (hemb.measurableSet_image.2 hs)
  have hρ'fin : ∀ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K → ρ' K < ⊤ := by
    intro K hK
    rw [hρ'def, hemb.comap_apply]
    exact hfin _ (hK.image hcont)
  have hρ'ne : ρ' ≠ 0 := by
    intro h0
    apply hne
    rw [← hmap, h0, Measure.map_zero]
  obtain ⟨c, hc⟩ := hρU ρ' hρ'fin hρ'inv
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hρ'ne (by rw [hc, zero_smul])

  have hK : ∃ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K ∧ ρ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hρ0
    apply Measure.measure_univ_eq_zero.1
    apply measure_mono_null (t := ⋃ n, (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) '' compactCovering G n)
    · intro q _
      rw [Set.mem_iUnion]
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering G).symm ▸ Set.mem_univ q.out)
      exact ⟨n, q.out, hn, QuotientGroup.out_eq' q⟩
    · exact measure_iUnion_null fun n =>
        hcon _ ((isCompact_compactCovering G n).image QuotientGroup.continuous_mk)
  have hctop : c ≠ ⊤ := by
    rintro rfl
    obtain ⟨K, hKc, hKpos⟩ := hK
    have := hρ'fin K hKc
    rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hKpos] at this
    exact lt_irrefl _ this
  refine ⟨c⁻¹ • ν, Measure.IsHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0), ?_⟩
  intro f hf s hs
  rw [hρF f hf]
  have hin : ∀ q : G ⧸ MulAction.stabilizer G x0, ∫⁻ h', f (s (ι q) * (h' : G)) ∂(c⁻¹ • ν) =
      c⁻¹ * ∫⁻ h, f (q.out * (h : G)) ∂ν := by
    intro q
    rw [lintegral_smul_measure]
    congr 1
    have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
    have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
    have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
    rw [hsk]
    have := lintegral_mul_left_eq_self (μ := ν) (fun h : MulAction.stabilizer G x0 => f (q.out * (h : G)))
      ⟨q.out⁻¹ * s (ι q), hk⟩
    simpa [mul_assoc] using this
  rw [← hmap, hemb.lintegral_map, hc, lintegral_smul_measure]
  simp_rw [hin]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hctop, one_mul]

end Abstract

def SecCtblG : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def OrbTup : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ y : Fin a → Fin M → AF F ⊗[F] E, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) →
    ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y

def StabClosed : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))

def StabUni : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  ∃ ν : Measure (stabT (AF F) σ J X0), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant

def NuInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ (g : HA (AF F) σ J) (s : Set (Fin a → Fin M → AF F ⊗[F] E)), MeasurableSet s →
      νX ((fun y => g • y) ⁻¹' s) = νX s

def NuFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → νX K < ⊤

def NuNeZero : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX → νX ≠ 0

def OrbEmb : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  MeasurableEmbedding (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ∧
    Continuous (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Use `hS F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet` as an intermediate fact. Establish `: T2Space (HA (AF F) σ J)` using `inferInstanceAs (T2Space (HR (AF F) σ J))`. Establish `: μ.IsHaarMeasure` using `hμ`.

Take `⟨ν, hνH, hνr⟩` from `hH F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet`. Establish `hnull : νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0`. Apply `measure_mono_null _ hν.1` to reduce the goal to its premises. Introduce `y hy`. Simplify using `only [Set.mem_ofPred_eq] at hy ⊢`.

Introduce `hg`. Conclude with `hy (hO F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet y hg)`. Take `⟨hemb, hcont⟩` from `hE F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet`. Take `⟨μ', h1, h2⟩` from `weil_orbit (G := HA (AF F) σ J) (ratTup (AF F) X0) (hCl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet) μ (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ) ν hνH hνr νX hnull (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν) (hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT h …`. Conclude with `⟨μ', h1, hnull, fun f hf s hs => h2 f hf s hs⟩`.
-/
theorem exStab_of (hS : SecCtblG) (hO : OrbTup) (hCl : StabClosed) (hH : StabUni) (hI : NuInv)
    (hF : NuFin) (hN : NuNeZero) (hE : OrbEmb) (hU : Unimod) : ExStab := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hS F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : μ.IsHaarMeasure := hμ
  obtain ⟨ν, hνH, hνr⟩ := hH F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have hnull : νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 := by
    apply measure_mono_null _ hν.1
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    intro hg
    exact hy (hO F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet y hg)
  obtain ⟨hemb, hcont⟩ := hE F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨μ', h1, h2⟩ := weil_orbit (G := HA (AF F) σ J) (ratTup (AF F) X0)
    (hCl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet) μ (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ)
    ν hνH hνr νX hnull (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hN F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν) hemb hcont
  exact ⟨μ', h1, hnull, fun f hf s hs => h2 f hf s hs⟩

end PI.VolStabS
