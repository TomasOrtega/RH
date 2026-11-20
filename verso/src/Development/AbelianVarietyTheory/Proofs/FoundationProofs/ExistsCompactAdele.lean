import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory NumberField Matrix Topology GlobalTheory.Mem.Vol
open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.VolPairExists
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `haveI := h.1 GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 a x`.
-/
theorem infEmb_tmul (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (a : Ainf F) (x : E) : θ (a ⊗ₜ x) = GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) a * τ x :=
  haveI := h.1
  GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 a x

/- English proof (translation)
Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [infEmb_tmul h hθ, infEmb_tmul h hθ']`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem infEmb_unique (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ θ' : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (hθ' : IsInfEmb τ θ') : θ = θ' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [infEmb_tmul h hθ, infEmb_tmul h hθ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
The claim follows from `haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩ IsModuleTopology.continuous_of_ringHom (R := Ainf F) θ hθ.2`.
-/
theorem infEmb_continuous {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) : Continuous θ :=
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.continuous_of_ringHom (R := Ainf F) θ hθ.2

/- English proof (translation)
Use `haveI := h.1`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Establish `e : sigR (Ainf F) σ (a ⊗ₜ x) = a ⊗ₜ σ x` using `rfl`.

Rewrite using `[e, infEmb_tmul h hθ, infEmb_tmul h hθ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, h.2.2.2]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem infEmb_sigR (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (z : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ z) = starRingEnd ℂ (θ z) := by
  haveI := h.1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : sigR (Ainf F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
    rw [e, infEmb_tmul h hθ, infEmb_tmul h hθ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, h.2.2.2]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Use `haveI := h.1`. Use `haveI := h.2.1`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Set `c : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)`. Establish `hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x)` using `h.2.2.2`.

Establish `hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ` using `fun φ hφ => IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)`. Establish `hc1 : c ≠ 1` using `fun e => by`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `hnr φ (RingHom.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hc, e, AlgEquiv.one_apply]`.

Use `choose θ₀ h1 h2 using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ`. Establish `hΨ : ∀ φ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ` using `fun φ => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩ ⟨j, hj⟩`. Establish `: j = i` using `hτ.1 (by simp only [hj, InfinitePlace.mk_conjugate_eq])`.

Substitute `this` using the available equality. Conclude with `hnr _ hj.symm`. Introduce `hn`. Take `⟨i, hi⟩` from `hτ.2 (InfinitePlace.mk φ)`. Break down `InfinitePlace.mk_eq_iff.1 hi with e | e` into its components or cases.

Conclude with `⟨i, e⟩`. Conclude with `absurd ⟨i, by rw [← e]; ext x; simp⟩ hn`. Establish `hb` using `GlobalTheory.InfAdeleCM.bijective c h.2.2.1 hc1 hc θ₀ (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ₀ φ) (h1 φ) (h2 φ)) _ hΨ`. Establish `hinj : Function.Injective τ` using `fun i j e => hτ.1 (by simp only [e])`. Establish `e0 : ∀ ρ, θ ρ = θ₀ (τ ρ)` using `fun ρ => infEmb_unique h (hθ ρ) ⟨h1 _, h2 _⟩`.

Use `((Equiv.ofInjective τ hinj).symm.arrowCongr (Equiv.refl ℂ)).bijective.comp hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z ρ`. Rewrite using `[e0]`. Both sides reduce to the same expression.
-/
theorem infEmb_bijective (h : IsCMExt F E σ) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    Function.Bijective fun (z : Ainf F ⊗[F] E) (ρ : I) => θ ρ z := by
  haveI := h.1
  haveI := h.2.1
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x) := h.2.2.2
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc1 : c ≠ 1 := fun e => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, e, AlgEquiv.one_apply]
  choose θ₀ h1 h2 using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := fun φ => by
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by simp only [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · exact absurd ⟨i, by rw [← e]; ext x; simp⟩ hn
  have hb := GlobalTheory.InfAdeleCM.bijective c h.2.2.1 hc1 hc θ₀
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ₀ φ) (h1 φ) (h2 φ)) _ hΨ
  have hinj : Function.Injective τ := fun i j e => hτ.1 (by simp only [e])
  have e0 : ∀ ρ, θ ρ = θ₀ (τ ρ) := fun ρ => infEmb_unique h (hθ ρ) ⟨h1 _, h2 _⟩
  have := ((Equiv.ofInjective τ hinj).symm.arrowCongr (Equiv.refl ℂ)).bijective.comp hb
  convert this using 1
  funext z ρ
  rw [e0]
  rfl

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F`. Take `⟨e₀⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)`.

Use `haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology`. Establish `hb` using `infEmb_bijective h hτ hθ`. Set `Θ : Ainf F ⊗[F] E →+ (I → ℂ)` to `(Pi.ringHom θ).toAddMonoidHom`. Establish `hΘ : Continuous Θ` using `continuous_pi fun ρ => infEmb_continuous (hθ ρ)`.

Establish `ho : IsOpenMap Θ` using `AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ`. Set `Φ` to `(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho`. Establish `hB : IsCompact (Φ ⁻¹' Set.pi Set.univ fun _ : I => Metric.closedBall (0 : ℂ) R)` using `Φ.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)`. Take `⟨e, he, -, hc⟩` from `GlobalTheory.AdSplit.exists_adele_equiv F E`. Use `⟨_, (hB.prod hC).image hc, fun z hz hR => ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩⟩` and prove the remaining obligations.

Rewrite using `[(he z).1]`. Conclude with `fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ)`. Rewrite using `[(he z).2]`. Conclude with `hz`.
-/
theorem exists_compact_adele (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (R : ℝ) (C : Set (Af F ⊗[F] E))
    (hC : IsCompact C) : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z ∈ C →
      (∀ ρ, ‖θ ρ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)‖ ≤ R) → z ∈ K := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  let Φ := (Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho
  have hB : IsCompact (Φ ⁻¹' Set.pi Set.univ fun _ : I => Metric.closedBall (0 : ℂ) R) :=
    Φ.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨_, (hB.prod hC).image hc, fun z hz hR => ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩⟩
  · rw [(he z).1]
    exact fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ)
  · rw [(he z).2]
    exact hz

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Establish `h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1` using `Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))`. Conclude with `(h1.matrix_map (GlobalTheory.Member.Arch.continuous_inf F E)).matrix_map (infEmb_continuous hθ)`.
-/
theorem continuous_infMat {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    Continuous fun h => infMat σ J θ h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact (h1.matrix_map (GlobalTheory.Member.Arch.continuous_inf F E)).matrix_map (infEmb_continuous hθ)

/- English proof (translation)
Establish `h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1` using `Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))`. Conclude with `h1.matrix_map (GlobalTheory.LevelOpen.continuous_fin F E)`.
-/
theorem continuous_finMat : Continuous fun h => finMat σ J h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact h1.matrix_map (GlobalTheory.LevelOpen.continuous_fin F E)

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => hθ.1 _`.
-/
theorem JR_map {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    (JR (F := F) (Ainf F) J).map θ = J.map τ :=
  Matrix.ext fun _ _ => hθ.1 _

/- English proof (translation)
Establish `hm` using `GlobalTheory.Member.Arch.inf_mem σ J (HA.mat (AF F) σ J g) g.2`. Establish `h2` using `GlobalTheory.Member.Arch.form_map _ θ (infEmb_sigR h hθ) ((HA.mat (AF F) σ J g).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) (JR (Ainf F) J)`. Rewrite using `[← JR_map J hθ]`. Conclude with `h2.symm.trans (congrArg (fun X => X.map θ) hm)`.
-/
theorem infMat_unitary (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (g : HA (AF F) σ J) : (infMat σ J θ g)ᴴ * J.map τ * infMat σ J θ g = J.map τ := by
  have hm := GlobalTheory.Member.Arch.inf_mem σ J (HA.mat (AF F) σ J g) g.2
  have h2 := GlobalTheory.Member.Arch.form_map _ θ (infEmb_sigR h hθ)
    ((HA.mat (AF F) σ J g).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) (JR (Ainf F) J)
  rw [← JR_map J hθ]
  exact h2.symm.trans (congrArg (fun X => X.map θ) hm)

/- English proof (translation)
Take `⟨a, ha, hau⟩` from `GlobalTheory.Member.Arch.exists_lift (sigR (Ainf F) σ) θ (infEmb_bijective h hτ hθ) (fun ρ => infEmb_sigR h (hθ ρ)) (JR (Ainf F) J) (fun ρ => by`. Rewrite using `[JR_map J (hθ ρ)]`. Establish `: (J.map (τ ρ)).det = τ ρ J.det` using `((τ ρ).map_det J).symm`. Rewrite using `[this]`. Conclude with `(map_ne_zero (τ ρ)).2 hJ) u (fun ρ => by rw [JR_map J (hθ ρ)]; exact hu ρ)`.

Set `p` to `(Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom`. Set `q` to `(Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom`. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv F E`. Establish `hi : ∀ x y, p x = p y → q x = q y → x = y` using `fun x y h1 h2 => e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))`. Establish `hs : ∀ a b, ∃ x, p x = a ∧ q x = b` using `fun a b => by`.

Apply the tactic sequence `refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp`. Take `⟨g, g1, g2⟩` from `GlobalTheory.UnitarySplit.gl_glue p q hi hs a 1`. Establish `hg : g ∈ HR (AF F) σ J`. Use `(GlobalTheory.UnitarySplit.mem_iff p q hi (sigR _ σ) (sigR _ σ) (sigR _ σ) (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g).2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[g1, GlobalTheory.UnitarySplit.map_JR]`.

Conclude with `ha`. Rewrite using `[g2]`. Conclude with `one_mem _`. Use `⟨⟨g, hg⟩, congrArg Units.val g2, fun ρ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hau, ← g1]`.

Both sides reduce to the same expression.
-/
theorem exists_real_point (h : IsCMExt F E σ) (hJ : J.det ≠ 0) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (u : I → Matrix (Fin M) (Fin M) ℂ)
    (hu : ∀ ρ, (u ρ)ᴴ * J.map (τ ρ) * u ρ = J.map (τ ρ)) :
    ∃ g : HA (AF F) σ J, finMat σ J g = 1 ∧ ∀ ρ, infMat σ J (θ ρ) g = u ρ := by
  obtain ⟨a, ha, hau⟩ := GlobalTheory.Member.Arch.exists_lift (sigR (Ainf F) σ) θ (infEmb_bijective h hτ hθ)
    (fun ρ => infEmb_sigR h (hθ ρ)) (JR (Ainf F) J) (fun ρ => by
      rw [JR_map J (hθ ρ)]
      have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
      rw [this]
      exact (map_ne_zero (τ ρ)).2 hJ) u (fun ρ => by rw [JR_map J (hθ ρ)]; exact hu ρ)
  let p := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let q := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y, p x = p y → q x = q y → x = y := fun x y h1 h2 =>
    e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))
  have hs : ∀ a b, ∃ x, p x = a ∧ q x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue p q hi hs a 1
  have hg : g ∈ HR (AF F) σ J := by
    refine (GlobalTheory.UnitarySplit.mem_iff p q hi (sigR _ σ) (sigR _ σ) (sigR _ σ) (GlobalTheory.UnitarySplit.map_sig _ _)
      (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g).2 ⟨?_, ?_⟩
    · rw [g1, GlobalTheory.UnitarySplit.map_JR]
      exact ha
    · rw [g2]
      exact one_mem _
  refine ⟨⟨g, hg⟩, congrArg Units.val g2, fun ρ => ?_⟩
  rw [← hau, ← g1]
  rfl

variable (σ) in

def stab (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | StabHat F L (finMat σ J h)}
  one_mem' := fun y => by rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]

/- English proof (translation)
Use `Unfold.topGroupHA σ J` as an intermediate fact. Establish `hn` using `GlobalTheory.LevelOpen.congr_mem_nhds F E M L hfg hsp 1 one_pos`. Establish `hc` using `continuous_finMat (σ := σ) J`. Establish `h1` using `hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [finMat_one]; exact hn)`. Establish `h2` using `(hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds (by rw [Function.comp_apply, inv_one, finMat_one]; exact hn)`.

Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_)` and prove the remaining obligations. Introduce and unpack `k ⟨hk1, hk2⟩ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨w, hw, h⟩` from `hk1 y hy`.

Rewrite using `[eq_add_of_sub_eq h]`. Conclude with `add_mem (nsmul_mem hw 1) hy`. Introduce `hy`. Take `⟨w, hw, h⟩` from `hk2 _ hy`. Rewrite `h` using `[Function.comp_apply, Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec]`.

Rewrite using `[eq_add_of_sub_eq h]`. Conclude with `add_mem (nsmul_mem hw 1) hy`.
-/
theorem isOpen_stab (L : Submodule (𝓞 E) (Fin M → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) : IsOpen (stab σ J L : Set (HA (AF F) σ J)) := by
  have := Unfold.topGroupHA σ J
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds F E M L hfg hsp 1 one_pos
  have hc := continuous_finMat (σ := σ) J
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [finMat_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, finMat_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_)
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one,
      Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end Chart

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨cm.totReal, cm.cmUnram.1, cm.deg2, cm.cmUnram.2.1⟩`.
-/
theorem isCMExt (cm : CMData F E) : IsCMExt F E cm.sig :=
  ⟨cm.totReal, cm.cmUnram.1, cm.deg2, cm.cmUnram.2.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => W.herm.eq (W.frame j) (W.frame i), GlobalTheory.StabCompact.det_gram_ne_zero W⟩`.
-/
theorem isHermND (cm : CMData F E) (W : HSpace E) : IsHermND cm.sig W.gram :=
  ⟨fun i j => W.herm.eq (W.frame j) (W.frame i), GlobalTheory.StabCompact.det_gram_ne_zero W⟩

/- English proof (translation)
Set `f` to `W.frame.equivFun.toLinearMap`. Use `⟨W.L0.map (f.restrictScalars (𝓞 E)), W.standardTuple_isLattice.fg.map _, ?_, ?_⟩` and prove the remaining obligations. Establish `: (W.L0.map (f.restrictScalars (𝓞 E)) : Set (Fin W.rank → E)) = f '' W.L0` using `rfl`. Rewrite using `[this, ← Submodule.map_span, W.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `∑ i, W.frame.equivFun x i • W.frame i ∈ W.L0`. Rewrite using `[W.frame.sum_equivFun]` and apply the resulting hypothesis. Introduce `hv`.

Use `⟨W.frame.equivFun.symm v, ?_, W.frame.equivFun.apply_symm_apply v⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Conclude with `hv`.
-/
theorem exists_lattice (W : HSpace E) : ∃ L : Submodule (𝓞 E) (Fin W.rank → E), L.FG ∧
    Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ ∧ (L : Set (Fin W.rank → E)) = latC W := by
  let f := W.frame.equivFun.toLinearMap
  refine ⟨W.L0.map (f.restrictScalars (𝓞 E)), W.standardTuple_isLattice.fg.map _, ?_, ?_⟩
  · have : (W.L0.map (f.restrictScalars (𝓞 E)) : Set (Fin W.rank → E)) = f '' W.L0 := rfl
    rw [this, ← Submodule.map_span, W.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, W.frame.equivFun x i • W.frame i ∈ W.L0
      rwa [W.frame.sum_equivFun]
    · intro hv
      refine ⟨W.frame.equivFun.symm v, ?_, W.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv

end Main

end GlobalTheory.Mem.VolExists
