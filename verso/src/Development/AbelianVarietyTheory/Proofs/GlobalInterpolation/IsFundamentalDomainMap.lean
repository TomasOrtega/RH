import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureLatticeIndependence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightInvariantOfFiniteCovolume
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti

noncomputable section

namespace GlobalTheory.VolumeIndep

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.VolTransport GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
open scoped TensorProduct Matrix ENNReal

/- English proof (translation)
Set `ψ : G ≃ᵐ H` to `⟨φ.toEquiv, hc, hc'⟩`. Establish `hψ : MeasurePreserving ψ μ (μ.map φ)` using `⟨ψ.measurable, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕` using `φ.toEquiv.image_eq_preimage_symm 𝓕`.

Rewrite using `[e]`. Conclude with `h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩) ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)), fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩ fun γ y => by show φ. …`. Rewrite using `[map_mul, φ.symm_apply_apply]`. Introduce `h`. Establish `e : 𝓕 = φ ⁻¹' (φ '' 𝓕)` using `(φ.injective.preimage_image 𝓕).symm`.

Rewrite using `[e]`. Conclude with `h.preimage_of_equiv (f := φ) hψ.quasiMeasurePreserving (e := fun γ => ⟨φ.symm γ, (hQ _).2 (by simp)⟩) ⟨fun a b hab => Subtype.ext (φ.symm.injective (congrArg Subtype.val hab)), fun b => ⟨⟨φ b, (hQ b).1 b.2⟩, Subtype.ext (by simp)⟩⟩ fun γ y => by show φ (φ.symm γ * y) = γ * φ y`. Rewrite using `[map_mul, φ.apply_symm_apply]`.
-/
theorem isFundamentalDomain_map {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) :
    IsFundamentalDomain Γ 𝓕 μ ↔ IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  constructor
  · intro h
    have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
    rw [e]
    exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  · intro h
    have e : 𝓕 = φ ⁻¹' (φ '' 𝓕) := (φ.injective.preimage_image 𝓕).symm
    rw [e]
    exact h.preimage_of_equiv (f := φ) hψ.quasiMeasurePreserving
      (e := fun γ => ⟨φ.symm γ, (hQ _).2 (by simp)⟩)
      ⟨fun a b hab => Subtype.ext (φ.symm.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ b, (hQ b).1 b.2⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ (φ.symm γ * y) = γ * φ y
        rw [map_mul, φ.apply_symm_apply]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix_comp]`. Simplify using the standard rewrite rules. Rewrite using `[← LinearMap.toMatrix_comp]`. Simplify using the standard rewrite rules.

Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V V' e.toLinearMap he`. Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V' V e.symm.toLinearMap (fun x y => by`. Use `he (e.symm x) (e.symm y)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `this.symm)`.
-/
theorem isoPair_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V)
    (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram
      (LinearMap.toMatrix V.frame V'.frame e.toLinearMap)
      (LinearMap.toMatrix V'.frame V.frame e.symm.toLinearMap) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]; simp
  · rw [← LinearMap.toMatrix_comp]; simp
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V V' e.toLinearMap he
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V' V e.symm.toLinearMap (fun x y => by
      have := he (e.symm x) (e.symm y)
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact this.symm)

/- English proof (translation)
Establish `c1` using `conjA_continuous h`. Establish `c2 : Continuous (conjA h).symm` using `conjA_continuous h.symm`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V'.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram` as an intermediate fact.

Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram` as an intermediate fact. Use `hμ.1` as an intermediate fact. Establish `hτ : ∀ (ρ : D.what₂.Tau) a, embOf D ρ ((D.sp.cm.sig : D.host.E →+* D.host.E) a) = starRingEnd ℂ (embOf D ρ a)` using `fun ρ a => D.sp.cm.cmUnram.2.1 _ a`. Use `⟨MulEquiv.isHaarMeasure_map μ (conjA h) c1 c2, hμ.2.1, fun θ hθ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `(hμ.2.2 θ hθ).1`.

Conclude with `⟨_, fun ρ => frame_transport h.symm (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)⟩`. Introduce `A hA B hB`. Establish `key` using `(hμ.2.2 θ hθ).2 _ (fun ρ => frame_transport h (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)) B hB`. Set `H : GA D V ≃ₜ GA D V'` to `⟨(conjA h).toEquiv, c1, c2⟩`. Use `Eq.trans (H.toMeasurableEquiv.map_apply _) ?_` and prove the remaining obligations.

Use `Eq.trans (congrArg μ ?_) key` and prove the remaining obligations. Use extensionality with `g`. Use `and_congr (stab_transport h hL hL' g) ?_` and prove the remaining obligations. Use `forall_congr' fun ρ => exists_congr fun b => and_congr Iff.rfl ?_` and prove the remaining obligations. Use `Iff.trans ?_ (frame_iff h (embOf D ρ) _ (A ρ) _)` and prove the remaining obligations.

Rewrite using `[← conjA_infMat h g (hθ ρ)]`. Both sides reduce to the same expression.
-/
theorem isVolMeas_map (V V' : HSp D) {T : Matrix (Fin V'.rank) (Fin V.rank) D.host.E}
    {T' : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (h : IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram T T')
    (hL : ∀ x ∈ L0c D V, T *ᵥ x ∈ L0c D V') (hL' : ∀ x ∈ L0c D V', T' *ᵥ x ∈ L0c D V)
    (P Q : ℕ) (μ : Measure (GA D V)) (hμ : IsVolMeas D V P Q μ) : IsVolMeas D V' P Q (μ.map (conjA h)) := by
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have := hμ.1
  have hτ : ∀ (ρ : D.what₂.Tau) a, embOf D ρ ((D.sp.cm.sig : D.host.E →+* D.host.E) a) =
      starRingEnd ℂ (embOf D ρ a) := fun ρ a => D.sp.cm.cmUnram.2.1 _ a
  refine ⟨MulEquiv.isHaarMeasure_map μ (conjA h) c1 c2, hμ.2.1, fun θ hθ => ⟨?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
    exact ⟨_, fun ρ => frame_transport h.symm (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)⟩
  · intro A hA B hB
    have key := (hμ.2.2 θ hθ).2 _
      (fun ρ => frame_transport h (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)) B hB
    let H : GA D V ≃ₜ GA D V' := ⟨(conjA h).toEquiv, c1, c2⟩
    refine Eq.trans (H.toMeasurableEquiv.map_apply _) ?_
    refine Eq.trans (congrArg μ ?_) key
    ext g
    refine and_congr (stab_transport h hL hL' g) ?_
    refine forall_congr' fun ρ => exists_congr fun b => and_congr Iff.rfl ?_
    refine Iff.trans ?_ (frame_iff h (embOf D ρ) _ (A ρ) _)
    rw [← conjA_infMat h g (hθ ρ)]
    rfl

/- English proof (translation)
Introduce `W P Q _ L L' hL hU hL' hU' μ`. Conclude with `⟨fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L hL hU) L' hL' hU' h (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1), fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L' hL' hU') L hL hU h (GlobalTh …`.
-/
theorem latticeIndependence (D : D7) : LatticeIndependence D := by
  intro W P Q _ L L' hL hU hL' hU' μ
  exact ⟨fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L hL hU) L' hL' hU' h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1),
    fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L' hL' hU') L hL hU h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1)⟩

/- English proof (translation)
Introduce `V V' P Q _ _ e he hL`. Apply the tactic sequence `have h := isoPair_of_isometry V V' e he`. Establish `c1` using `conjA_continuous h`. Establish `c2 : Continuous (conjA h).symm` using `conjA_continuous h.symm`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram` as an intermediate fact.

Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram` as an intermediate fact. Establish `l1` using `mem_std_lattice_iff_integral_coords D V V' e.toLinearMap fun x => (hL x).1`. Establish `l2` using `mem_std_lattice_iff_integral_coords D V' V e.symm.toLinearMap fun x hx => (hL _).2 (by simpa using hx)`. Establish `hQ : ∀ g, g ∈ GQ V ↔ conjA h g ∈ GQ V'` using `fun g => ⟨conjA_rat h g, fun hg => by`. Use `conjA_rat h.symm _ hg` as an intermediate fact.

Rewrite using `[← conjA_symm h, MulEquiv.symm_apply_apply] at this⟩` and apply the resulting hypothesis. Use `⟨⟨conjA h, c1, c2⟩, fun g => ?_, hQ, fun μ => ⟨isVolMeas_map V V' h l1 l2 P Q μ, fun hμ => ?_⟩, fun μ _ 𝓕 => isFundamentalDomain_map (conjA h) c1.measurable c2.measurable (GQ V) (GQ V') hQ μ 𝓕⟩` and prove the remaining obligations. Establish `e1` using `conjA_mat h g`. Establish `e2` using `h.adelic.2.1`. Unfold `Intertwines pointMatrix baseChange frameMatrix`.

Use `(congrArg (· * _) e1).trans ?_` and prove the remaining obligations. Use `show _ * _ * _ * _ = _`. Rewrite using `[Matrix.mul_assoc, e2, Matrix.mul_one]`. Establish `k` using `isVolMeas_map V' V h.symm l2 l1 P Q _ hμ`. Establish `e3 : Measure.map (conjA h.symm) (Measure.map (conjA h) μ) = μ`.

Use `(Measure.map_map c2.measurable c1.measurable).trans ?_` and prove the remaining obligations. Rewrite using `[show ((conjA h).symm : _ → _) ∘ (conjA h) = id from funext (conjA h).symm_apply_apply, Measure.map_id]`. Conclude with `e3 ▸ k`.
-/
theorem isometryTransport (D : D7) : IsometryTransport D := by
  intro V V' P Q _ _ e he hL
  have h := isoPair_of_isometry V V' e he
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have l1 := mem_std_lattice_iff_integral_coords D V V' e.toLinearMap fun x => (hL x).1
  have l2 := mem_std_lattice_iff_integral_coords D V' V e.symm.toLinearMap fun x hx => (hL _).2 (by simpa using hx)
  have hQ : ∀ g, g ∈ GQ V ↔ conjA h g ∈ GQ V' := fun g => ⟨conjA_rat h g, fun hg => by
    have := conjA_rat h.symm _ hg
    rwa [← conjA_symm h, MulEquiv.symm_apply_apply] at this⟩
  refine ⟨⟨conjA h, c1, c2⟩, fun g => ?_, hQ, fun μ => ⟨isVolMeas_map V V' h l1 l2 P Q μ, fun hμ => ?_⟩,
    fun μ _ 𝓕 => isFundamentalDomain_map (conjA h) c1.measurable c2.measurable (GQ V) (GQ V') hQ μ 𝓕⟩
  · have e1 := conjA_mat h g
    have e2 := h.adelic.2.1
    unfold Intertwines pointMatrix baseChange frameMatrix
    refine (congrArg (· * _) e1).trans ?_
    show _ * _ * _ * _ = _
    rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  · have k := isVolMeas_map V' V h.symm l2 l1 P Q _ hμ
    have e3 : Measure.map (conjA h.symm) (Measure.map (conjA h) μ) = μ := by
      refine (Measure.map_map c2.measurable c1.measurable).trans ?_
      rw [show ((conjA h).symm : _ → _) ∘ (conjA h) = id from funext (conjA h).symm_apply_apply, Measure.map_id]
    exact e3 ▸ k

/- English proof (translation)
Introduce `hT V V' P Q hV hV' ⟨e, he⟩`. Establish `pos : ∀ W : HSp D, HasSignatureEverywhere W P Q → 0 < D.vol W` using `fun W hW => by`. Take `⟨⟨μ, hμ⟩, hall⟩` from `hT W P Q hW.1 hW.2`. Take `⟨⟨𝓕, h𝓕⟩, hv⟩` from `hall μ hμ`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig W.gram` as an intermediate fact.

Use `hμ.1` as an intermediate fact. Establish `: Countable (GQ W)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ W)` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ W) μ` as an intermediate fact. Establish `h𝓕' : IsFundamentalDomain (GQ W) 𝓕 μ` using `h𝓕`.

Use `h𝓕'.measure_ne_zero (NeZero.ne μ)` as an intermediate fact. Rewrite `this` using `[hv 𝓕 h𝓕]`. Conclude with `ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)`. Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular.IsVol D V P Q (D.vol V)` using `⟨pos V hV, hT V P Q hV.1 hV.2⟩`. Apply the tactic sequence `have h2 := GlobalTheory.VolumeRatioTypings.isVol_of_isometry V V' e he h1`.

Take `⟨⟨μ, hμ⟩, hall⟩` from `hT V' P Q hV'.1 hV'.2`. Take `⟨⟨𝓕, h𝓕⟩, hv⟩` from `hall μ hμ`. Conclude with `(ENNReal.ofReal_eq_ofReal_iff (pos V hV).le (pos V' hV').le).1 (((h2.2.2 μ hμ).2 𝓕 h𝓕).symm.trans (hv 𝓕 h𝓕))`.
-/
theorem volumeInvariance (D : D7) : VolumeInvariance D := by
  intro hT V V' P Q hV hV' ⟨e, he⟩
  have pos : ∀ W : HSp D, HasSignatureEverywhere W P Q → 0 < D.vol W := fun W hW => by
    obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W P Q hW.1 hW.2
    obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig W.gram
    have := hμ.1
    have : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ W)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ W) μ
    have h𝓕' : IsFundamentalDomain (GQ W) 𝓕 μ := h𝓕
    have := h𝓕'.measure_ne_zero (NeZero.ne μ)
    rw [hv 𝓕 h𝓕] at this
    exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular.IsVol D V P Q (D.vol V) := ⟨pos V hV, hT V P Q hV.1 hV.2⟩
  have h2 := GlobalTheory.VolumeRatioTypings.isVol_of_isometry V V' e he h1
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT V' P Q hV'.1 hV'.2
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  exact (ENNReal.ofReal_eq_ofReal_iff (pos V hV).le (pos V' hV').le).1
    (((h2.2.2 μ hμ).2 𝓕 h𝓕).symm.trans (hv 𝓕 h𝓕))

/- English proof (translation)
Assemble the required witnesses or components as `⟨latticeIndependence D, isometryTransport D, volumeInvariance D⟩`.
-/
theorem volumeIndependence (D : D7) : VolumeIndependence D :=
  ⟨latticeIndependence D, isometryTransport D, volumeInvariance D⟩

end GlobalTheory.VolumeIndep
