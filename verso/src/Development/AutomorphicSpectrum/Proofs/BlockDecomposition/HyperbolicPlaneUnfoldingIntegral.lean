import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitExtensionFundamentalDomainStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliserStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStableStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

section Tup

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Use function extensionality and compare the values at `j i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`. Simplify using `[ratTup, consA]`.
-/
theorem ratTup_consA {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) :
    ratTup (F := F) R (consA a Y) = consA (ratTup (F := F) R a) (ratTup (F := F) R Y) := by
  funext j i
  refine Fin.cases ?_ (fun j => ?_) j <;> refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    simp [ratTup, consA]

/- English proof (translation)
Use function extensionality and compare the values at `j i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp [ratTup, e0]`.
-/
theorem ratTup_e0 {M : ℕ} : ratTup (F := F) R (e0 E M) = e0 (R ⊗[F] E) M := by
  funext j i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [ratTup, e0]

/- English proof (translation)
Use `continuous_pi fun j => continuous_pi fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Conclude with `continuous_const`. Use `Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i` and prove the remaining obligations. Conclude with `(continuous_apply j).comp ((continuous_apply (0 : Fin 1)).comp continuous_fst)`.

Conclude with `continuous_const`. Conclude with `(continuous_apply i).comp ((continuous_apply j).comp continuous_snd)`.
-/
theorem continuous_consA {K : Type} [Zero K] [One K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : (Fin 1 → Fin n → K) × (Fin n → Fin M → K) => consA p.1 p.2) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · exact continuous_const
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact (continuous_apply j).comp ((continuous_apply (0 : Fin 1)).comp continuous_fst)
    · exact continuous_const
    · exact (continuous_apply i).comp ((continuous_apply j).comp continuous_snd)

end Tup

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def phiA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ)
    (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (g : HA (AF F) σ (hypOne J)) : ℝ≥0∞ :=
  ∑' X : framesOne σ J n, Φ (actW (AF F) σ (hypOne J) g⁻¹ (ratTup (AF F) X.1))

end Glob

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp`. Take `⟨⟨i1, i2, i3⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`.

Take `⟨hJb, -, -⟩` from `GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ`. Take `⟨tg, lc, sc, t2, bs, act⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)`. Take `⟨tg₁, lc₁, sc₁, t2₁, bs₁, act₁⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)`. Use `haveI := tg`. Use `haveI := lc`.

Use `haveI := sc`. Use `haveI := t2`. Use `haveI := bs`. Use `haveI := tg₁`. Use `haveI := lc₁`.

Use `haveI := sc₁`. Use `haveI := t2₁`. Use `haveI := bs₁`. Take `⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩` from `TopK.topTens_props F E σ hσ (AF F)`. Use `haveI := c1`.

Use `haveI := c2`. Use `haveI := c3`. Use `haveI := c4`. Use `haveI := hB (n + 1) (M + 2)`. Use `haveI := hB 1 (M + 2)`.

Use `haveI := hB n M`. Use `haveI := hB 1 n`. Use `haveI : μ₁.IsHaarMeasure := hμ₁`. Use `haveI : dA.IsAddHaarMeasure := hdA.1`. Take `⟨D, hD, hD1⟩` from `hdA.2`.

Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable`. Establish `hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J)))` using `isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const`. Use `haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _`.

Take `⟨ι, π, hιc, hπc, hπι, hι1, hπ1, hK, hιact, hl⟩` from `GlobalTheory.T.stabiliser_splitting_adelic F E σ hσ M J hJ`. Take `⟨hc0, U, hU, hU1⟩` from `rational_countable_discrete F E σ hσ (M + 2) _ hJb`. Use `haveI hc₁ : Countable (HFinIn (AF F) σ J) := (rational_countable_discrete F E σ hσ M J hJ).1`. Set `Γ₁ : Subgroup (HA (AF F) σ J)` to `HFinIn (AF F) σ J`. Use `haveI hc₁' : Countable Γ₁ := hc₁`.

Use `haveI hcP : Countable (ratP (AF F) σ J) := by haveI := hc0`. Establish `hinj : Function.Injective fun γ : ratP (AF F) σ J => (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J))`. Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))`. Conclude with `hinj.countable`.

Establish `hfin : μ₁ 𝓕₁ < ⊤` using `((finVol_unitaryGroup F E σ hσ M J hJ).2 μ₁ hμ₁).2 𝓕₁ h𝓕₁`. Establish `hUP : ∃ U' ∈ 𝓝 (1 : stabilizer₂ (AF F) σ J), ∀ γ ∈ ratP (AF F) σ J, γ ∈ U' → γ = 1`. Use `⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩` and prove the remaining obligations. Introduce `γ hγ hγU`. Use `Subtype.ext (hU1 _ hγU ?_)` and prove the remaining obligations.

Conclude with `(mem_HFinIn_iff _ σ _ _).1 hγ`. Take `⟨ν, 𝓕N, μP, 𝓕P, hν, h𝓕N, hν0, hνf, hμP, h𝓕P, hPf, hform⟩` from `GlobalTheory.T.split_extension_fundamental_domain (stabilizer₂ (AF F) σ J) (HA (AF F) σ J) ι π hιc hπc hπι (ratP (AF F) σ J) Γ₁ hUP hι1 hπ1 μ₁ 𝓕₁ h𝓕₁ hfin hK`. Use `⟨μP, 𝓕P, hμP, h𝓕P, hPf, fun g => ?_⟩` and prove the remaining obligations. Use `haveI := hν`. Establish `hNc : IsClosed ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J))`.

Establish `: ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J)) = π ⁻¹' {1}`. Use extensionality with `x`. Simplify using `[MonoidHom.mem_ker]`. Rewrite using `[this]`. Conclude with `isClosed_singleton.preimage hπc`.

Use `haveI : LocallyCompactSpace π.ker := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : BorelSpace π.ker := Subtype.borelSpace _`. Use `haveI hcN : Countable ((ratP (AF F) σ J).subgroupOf π.ker) := by`. Establish `hinj : Function.Injective fun γ : (ratP (AF F) σ J).subgroupOf π.ker => (⟨(γ : π.ker), Subgroup.mem_subgroupOf.1 γ.2⟩ : ratP (AF F) σ J)`.

Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun x : ratP (AF F) σ J => (x : stabilizer₂ (AF F) σ J)) h))`. Conclude with `hinj.countable`. Use `haveI hcΛ : Countable (ratA (F := F) (E := E) n) := by`. Establish `hs : Function.Surjective fun a : Fin 1 → Fin n → E => (⟨ratTup (AF F) a, ⟨a, rfl⟩⟩ : ratA (F` using `F) (E := E) n) := by`.

Introduce and unpack `⟨_, a, rfl⟩`. Conclude with `⟨a, rfl⟩`. Conclude with `hs.countable`. Establish `hl' : ∀ Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∃ l : π.ker → Fin 1 → Fin n → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F` using `F) (E := E) n) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin n → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y.1)) = consA (a + l m) (ratTup (AF F) Y.1) := fun Y => hl n Y.1 Y.2.1`. Use `choose ll hlc hladd hlsurj hlrat hlact using hl'`.

Set `eA : (Fin 1 → Fin n → E) ≃ ratA (F` to `F) (E := E) n := Equiv.ofBijective (fun a => ⟨ratTup (AF F) a, ⟨a, rfl⟩⟩) ⟨fun a b h => ratTup_adele_injective (F := F) (congrArg Subtype.val h), by`. Introduce and unpack `⟨_, a, rfl⟩`. Conclude with `⟨a, rfl⟩⟩`. Establish `hact : ∀ k : ℕ, Continuous fun X : Fin k → Fin (M + 2) → AF F ⊗[F] E => actW (AF F) σ (hypOne J) g⁻¹ X` using `fun k => (act k).1.comp (continuous_const.prodMk continuous_id)`. Set `K : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞` to `fun Y' => ∫⁻ x, Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y')) ∂dA`.

Establish `hjoint : Measurable fun p : (Fin n → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin n → AF F ⊗[F] E) => Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA p.2 p.1))` using `hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp continuous_swap)).measurable`. Establish `hKm : Measurable K` using `hjoint.lintegral_prod_right'`. Establish `hslice : ∀ Y' : Fin n → Fin M → AF F ⊗[F] E, Measurable fun x : Fin 1 → Fin n → AF F ⊗[F] E => Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y'))` using `fun Y' => hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp (continuous_id.prodMk continuous_const))).measurable`. Establish `hterm : ∀ (u : HA (AF F) σ J) (m : π.ker), phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : ratA (F` using `F) (E := E) n, Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA ((a : Fin 1 → Fin n → AF F ⊗[F] E) + ll Y m⁻¹) (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)))) := by`. Introduce `u m`.

Rewrite using `[phiA, GlobalTheory.T.frames_sum_by_first_vector F E σ M J n (fun X => Φ (actW (AF F) σ (hypOne J) ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X)))]`. Use `tsum_congr fun Y => ?_` and prove the remaining obligations. Rewrite using `[← eA.tsum_eq]`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `e1 : ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ = g⁻¹ * (((ι u⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * (((m⁻¹ : π.ker) : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)))`. Rewrite using `[map_inv]`. Simplify using `[mul_assoc]`. Rewrite using `[e1, actW_mul_apply, actW_mul_apply, ratTup_consA, hlact, hιact]`. Both sides reduce to the same expression.

Establish `hinner : ∀ u : HA (AF F) σ J, ∫⁻ m in 𝓕N, phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) ∂ν = ν 𝓕N * ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), K (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1))`. Introduce `u`. Rewrite using `[lintegral_congr (hterm u), lintegral_tsum, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun Y => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.fundamental_domain_fibration_volume π.ker ν ((ratP (AF F) σ J).subgroupOf π.ker) 𝓕N h𝓕N hνf (Fin 1 → Fin n → AF F ⊗[F] E) dA (ratA (F := F) (E := E) n) D hD hD1 (ll Y) (hlc Y) (hladd Y) (hlsurj Y) (fun γ hγ => hlrat Y γ (Subgroup.mem_subgroupOf.1 hγ)) _ (hslice _)`.

Introduce `Y`. Use `Measurable.aemeasurable (Measurable.ennreal_tsum fun a => ?_)` and prove the remaining obligations. Use `(hslice _).comp ?_` and prove the remaining obligations. Conclude with `(measurable_const.add ((hlc Y).measurable.comp measurable_inv))`. Establish `hfm : Measurable fun p : stabilizer₂ (AF F) σ J => phiA σ J n Φ ((p : HA (AF F) σ (hypOne J)) * g)`.

Use `Measurable.ennreal_tsum fun X => hΦ.comp ?_` and prove the remaining obligations. Establish `: Continuous fun p : stabilizer₂ (AF F) σ J => actW (AF F) σ (hypOne J) ((p : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X.1)` using `(act (n + 1)).1.comp (((continuous_subtype_val.mul continuous_const).inv).prodMk continuous_const)`. Conclude with `this.measurable`. Establish `hvol : μP 𝓕P = ν 𝓕N * μ₁ 𝓕₁`. Use `hform (fun _ => 1) measurable_const` as an intermediate fact.

Simplify `this` using `[mul_comm]`. Rewrite using `[hform _ hfm, lintegral_congr hinner, lintegral_const_mul' _ _ hνf.ne, hvol, hyp g⁻¹, GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ₁ 𝓕₁ hμ₁ h𝓕₁ n _ K hKm, ENNReal.mul_inv (Or.inl hν0) (Or.inl hνf.ne)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem meanP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∃ (μP : Measure (stabilizer₂ (AF F) σ J)) (𝓕P : Set (stabilizer₂ (AF F) σ J)), μP.IsHaarMeasure ∧ IsFundamentalDomain (ratP (AF F) σ J) 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ g : HA (AF F) σ (hypOne J), (μP 𝓕P)⁻¹ * ∫⁻ u in 𝓕P, phiA σ J n Φ ((u : HA (AF F) σ (hypOne J)) * g) ∂μP = Ψ (actW (AF F) σ (hypOne J) g⁻¹ (e0 _ M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨hJb, -, -⟩ := GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, act₁⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := c1
  haveI := c2
  haveI := c3
  haveI := c4
  haveI := hB (n + 1) (M + 2)
  haveI := hB 1 (M + 2)
  haveI := hB n M
  haveI := hB 1 n
  haveI : μ₁.IsHaarMeasure := hμ₁
  haveI : dA.IsAddHaarMeasure := hdA.1
  obtain ⟨D, hD, hD1⟩ := hdA.2
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  have hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J))) :=
    isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const
  haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _
  obtain ⟨ι, π, hιc, hπc, hπι, hι1, hπ1, hK, hιact, hl⟩ := GlobalTheory.T.stabiliser_splitting_adelic F E σ hσ M J hJ
  obtain ⟨hc0, U, hU, hU1⟩ := rational_countable_discrete F E σ hσ (M + 2) _ hJb
  haveI hc₁ : Countable (HFinIn (AF F) σ J) := (rational_countable_discrete F E σ hσ M J hJ).1
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI hc₁' : Countable Γ₁ := hc₁
  haveI hcP : Countable (ratP (AF F) σ J) := by
    haveI := hc0
    have hinj : Function.Injective fun γ : ratP (AF F) σ J =>
        (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J)) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))
    exact hinj.countable
  have hfin : μ₁ 𝓕₁ < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ₁ hμ₁).2 𝓕₁ h𝓕₁
  have hUP : ∃ U' ∈ 𝓝 (1 : stabilizer₂ (AF F) σ J), ∀ γ ∈ ratP (AF F) σ J, γ ∈ U' → γ = 1 := by
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro γ hγ hγU
    refine Subtype.ext (hU1 _ hγU ?_)
    exact (mem_HFinIn_iff _ σ _ _).1 hγ
  obtain ⟨ν, 𝓕N, μP, 𝓕P, hν, h𝓕N, hν0, hνf, hμP, h𝓕P, hPf, hform⟩ :=
    GlobalTheory.T.split_extension_fundamental_domain (stabilizer₂ (AF F) σ J) (HA (AF F) σ J) ι π hιc hπc hπι (ratP (AF F) σ J) Γ₁
      hUP hι1 hπ1 μ₁ 𝓕₁ h𝓕₁ hfin hK
  refine ⟨μP, 𝓕P, hμP, h𝓕P, hPf, fun g => ?_⟩
  haveI := hν
  have hNc : IsClosed ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J)) := by
    have : ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J)) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπc
  haveI : LocallyCompactSpace π.ker := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI hcN : Countable ((ratP (AF F) σ J).subgroupOf π.ker) := by
    have hinj : Function.Injective fun γ : (ratP (AF F) σ J).subgroupOf π.ker =>
        (⟨(γ : π.ker), Subgroup.mem_subgroupOf.1 γ.2⟩ : ratP (AF F) σ J) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : ratP (AF F) σ J => (x : stabilizer₂ (AF F) σ J)) h))
    exact hinj.countable
  haveI hcΛ : Countable (ratA (F := F) (E := E) n) := by
    have hs : Function.Surjective fun a : Fin 1 → Fin n → E =>
        (⟨ratTup (AF F) a, ⟨a, rfl⟩⟩ : ratA (F := F) (E := E) n) := by
      rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩
    exact hs.countable
  have hl' : ∀ Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∃ l : π.ker → Fin 1 → Fin n → AF F ⊗[F] E,
      Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧
      (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) n) ∧
      ∀ (m : π.ker) (a : Fin 1 → Fin n → AF F ⊗[F] E),
        actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y.1)) =
          consA (a + l m) (ratTup (AF F) Y.1) := fun Y => hl n Y.1 Y.2.1
  choose ll hlc hladd hlsurj hlrat hlact using hl'

  let eA : (Fin 1 → Fin n → E) ≃ ratA (F := F) (E := E) n := Equiv.ofBijective
    (fun a => ⟨ratTup (AF F) a, ⟨a, rfl⟩⟩)
    ⟨fun a b h => ratTup_adele_injective (F := F) (congrArg Subtype.val h), by
      rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩⟩
  have hact : ∀ k : ℕ, Continuous fun X : Fin k → Fin (M + 2) → AF F ⊗[F] E =>
      actW (AF F) σ (hypOne J) g⁻¹ X := fun k =>
    (act k).1.comp (continuous_const.prodMk continuous_id)
  let K : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := fun Y' =>
    ∫⁻ x, Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y')) ∂dA
  have hjoint : Measurable fun p : (Fin n → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin n → AF F ⊗[F] E) =>
      Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA p.2 p.1)) :=
    hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp continuous_swap)).measurable
  have hKm : Measurable K := hjoint.lintegral_prod_right'
  have hslice : ∀ Y' : Fin n → Fin M → AF F ⊗[F] E, Measurable fun x : Fin 1 → Fin n → AF F ⊗[F] E =>
      Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y')) := fun Y' =>
    hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp (continuous_id.prodMk continuous_const))).measurable

  have hterm : ∀ (u : HA (AF F) σ J) (m : π.ker),
      phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) =
      ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : ratA (F := F) (E := E) n,
        Φ (actW (AF F) σ (hypOne J) g⁻¹
          (consA ((a : Fin 1 → Fin n → AF F ⊗[F] E) + ll Y m⁻¹)
            (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)))) := by
    intro u m
    rw [phiA, GlobalTheory.T.frames_sum_by_first_vector F E σ M J n (fun X => Φ (actW (AF F) σ (hypOne J)
      ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X)))]
    refine tsum_congr fun Y => ?_
    rw [← eA.tsum_eq]
    refine tsum_congr fun a => ?_
    congr 1
    have e1 : ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ =
        g⁻¹ * (((ι u⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) *
          (((m⁻¹ : π.ker) : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J))) := by
      rw [map_inv]
      simp [mul_assoc]
    rw [e1, actW_mul_apply, actW_mul_apply, ratTup_consA, hlact, hιact]
    rfl
  have hinner : ∀ u : HA (AF F) σ J,
      ∫⁻ m in 𝓕N, phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) ∂ν =
      ν 𝓕N * ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E),
        K (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)) := by
    intro u
    rw [lintegral_congr (hterm u), lintegral_tsum, ← ENNReal.tsum_mul_left]
    · refine tsum_congr fun Y => ?_
      exact GlobalTheory.T.fundamental_domain_fibration_volume π.ker ν ((ratP (AF F) σ J).subgroupOf π.ker) 𝓕N h𝓕N hνf
        (Fin 1 → Fin n → AF F ⊗[F] E) dA (ratA (F := F) (E := E) n) D hD hD1 (ll Y) (hlc Y) (hladd Y)
        (hlsurj Y) (fun γ hγ => hlrat Y γ (Subgroup.mem_subgroupOf.1 hγ)) _ (hslice _)
    · intro Y
      refine Measurable.aemeasurable (Measurable.ennreal_tsum fun a => ?_)
      refine (hslice _).comp ?_
      exact (measurable_const.add ((hlc Y).measurable.comp measurable_inv))
  have hfm : Measurable fun p : stabilizer₂ (AF F) σ J =>
      phiA σ J n Φ ((p : HA (AF F) σ (hypOne J)) * g) := by
    refine Measurable.ennreal_tsum fun X => hΦ.comp ?_
    have : Continuous fun p : stabilizer₂ (AF F) σ J =>
        actW (AF F) σ (hypOne J) ((p : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X.1) :=
      (act (n + 1)).1.comp (((continuous_subtype_val.mul continuous_const).inv).prodMk continuous_const)
    exact this.measurable
  have hvol : μP 𝓕P = ν 𝓕N * μ₁ 𝓕₁ := by
    have := hform (fun _ => 1) measurable_const
    simpa [mul_comm] using this
  rw [hform _ hfm, lintegral_congr hinner, lintegral_const_mul' _ _ hνf.ne, hvol, hyp g⁻¹,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ₁ 𝓕₁ hμ₁ h𝓕₁ n _ K hKm, ENNReal.mul_inv (Or.inl hν0) (Or.inl hνf.ne)]
  calc _ = (ν 𝓕N)⁻¹ * ν 𝓕N * ((μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), K (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)) ∂μ₁) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hν0 hνf.ne, one_mul]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ n hn hM μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hΨ hyp`. Take `⟨⟨i1, i2, i3⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`.

Take `⟨hJb, he0, hgq⟩` from `GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ`. Take `⟨tg, lc, sc, t2, bs, act⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)`. Use `haveI := tg`. Use `haveI := lc`. Use `haveI := sc`.

Use `haveI := t2`. Use `haveI := bs`. Take `⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩` from `TopK.topTens_props F E σ hσ (AF F)`. Use `haveI := c1`. Use `haveI := c2`.

Use `haveI := c3`. Use `haveI := c4`. Use `haveI := hB (n + 1) (M + 2)`. Use `haveI := hB 1 (M + 2)`. Use `haveI : μ.IsHaarMeasure := hμ`.

Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable`. Take `⟨μP, 𝓕P, hμP, h𝓕P, hPf, hmean⟩` from `meanP F E σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp`. Use `haveI := hμP`. Establish `hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J)))` using `isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const`. Use `haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _`. Use `haveI hc : Countable (HFinIn (AF F) σ (hypOne J)) := (rational_countable_discrete F E σ hσ (M + 2) _ hJb).1`. Set `Γ : Subgroup (HA (AF F) σ (hypOne J))` to `HFinIn (AF F) σ (hypOne J)`. Use `haveI hc' : Countable Γ := hc`.

Use `haveI hcP : Countable (ratP (AF F) σ J) := by`. Establish `hinj : Function.Injective fun γ : ratP (AF F) σ J => (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J))`. Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))`. Conclude with `hinj.countable`.

Establish `hW : ∀ q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q.1 = e0 E M` using `fun q => GlobalTheory.T.global_unitary_moves_isotropic_frame F E σ hσ M J hJ q.1 q.2`. Use `choose rr hrr using hW`. Set `r` to `fun q => ratH (AF F) σ (hypOne J) (rr q)`. Establish `hφ : Measurable (phiA σ J n Φ)`. Use `Measurable.ennreal_tsum fun X => hΦ.comp ?_` and prove the remaining obligations.

Establish `: Continuous fun g : HA (AF F) σ (hypOne J) => actW (AF F) σ (hypOne J) g⁻¹ (ratTup (AF F) X.1)` using `(act (n + 1)).1.comp (continuous_inv.prodMk continuous_const)`. Conclude with `this.measurable`. Establish `hmul : ∀ (g h : HA (AF F) σ (hypOne J)) {k : ℕ} (X : Fin k → Fin (M + 2) → AF F ⊗[F] E), actW (AF F) σ _ (g * h) X = actW (AF F) σ _ g (actW (AF F) σ _ h X)` using `fun g h {k} X => actW_mul_apply _ σ _ g h X`. Establish `hfix : ∀ g : UJ (σ : E →+* E) (hypOne J), actW (AF F) σ _ (ratH (AF F) σ _ g) (e0 _ M) = ratTup (AF F) (gact σ g (e0 E M))`. Introduce `g`.

Rewrite using `[← ratTup_e0, actW_ratH']`. Establish `hinv : ∀ u ∈ ratP (AF F) σ J, ∀ g, phiA σ J n Φ ((stabilizer₂ (AF F) σ J).subtype u * g) = phiA σ J n Φ g`. Introduce `u hu g`. Take `⟨w, hw⟩` from `exists_ratH (AF F) σ _ (u : HA (AF F) σ (hypOne J)) hu`. Establish `hw0 : gact σ w (e0 E M) = e0 E M`.

Establish `h1 : actW (AF F) σ (hypOne J) (u : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M` using `u.2`. Rewrite `h1` using `[hw, hfix, ← ratTup_e0]`. Conclude with `ratTup_adele_injective (F := F) h1`. Establish `hw1 : gact σ w⁻¹ (e0 E M) = e0 E M` using `by conv_lhs => rw [← hw0]`. Conclude with `gact_inv_gact σ w _`.

Establish `e : ∀ X : Fin (n + 1) → Fin (M + 2) → E, actW (AF F) σ _ ((stabilizer₂ (AF F) σ J).subtype u * g)⁻¹ (ratTup (AF F) X) = actW (AF F) σ _ g⁻¹ (ratTup (AF F) (gact σ w⁻¹ X))`. Introduce `X`. Rewrite using `[mul_inv_rev, hmul]`. Express the relevant statement in the definitionally equal form `actW (AF F) σ _ g⁻¹ (actW (AF F) σ _ (u : HA (AF F) σ (hypOne J))⁻¹ (ratTup (AF F) X)) = _`. Rewrite using `[hw, ratH_inv, actW_ratH']`.

Simplify using `only [phiA, e]`. Conclude with `GlobalTheory.T.frames_sum_invariant_under_stabiliser F E σ M J n w⁻¹ hw1 (fun X => Φ (actW (AF F) σ _ g⁻¹ (ratTup (AF F) X)))`. Establish `hΓ : ∀ u ∈ ratP (AF F) σ J, (stabilizer₂ (AF F) σ J).subtype u ∈ Γ` using `fun u hu => hu`. Establish `hrinv : ∀ q, gact σ (rr q)⁻¹ (e0 E M) = q.1`. Introduce `q`.

Rewrite using `[← hrr q, gact_inv_gact]`. Establish `huniq : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ ratP (AF F) σ J, γ = (stabilizer₂ (AF F) σ J).subtype u * r q`. Introduce `γ hγ`. Take `⟨g, rfl⟩` from `exists_ratH (AF F) σ _ γ hγ`. Establish `hy` using `hgq g⁻¹ _ he0`.

Set `q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E)` to `⟨_, hy⟩`. Establish `hst : ratH (AF F) σ _ g * (r q)⁻¹ ∈ stabilizer₂ (AF F) σ J`. Express the relevant statement in the definitionally equal form `actW (AF F) σ _ (ratH (AF F) σ _ g * (r q)⁻¹) (e0 _ M) = e0 _ M`. Establish `e1 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹` using `ratH_inv _ σ _ _`. Rewrite using `[hmul, e1, hfix, hrinv, actW_ratH']`.

Express the relevant statement in the definitionally equal form `ratTup (AF F) (gact σ g (gact σ g⁻¹ _)) = _`. Rewrite using `[gact_gact_inv, ratTup_e0]`. Establish `hmemu : (⟨_, hst⟩ : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J` using `Subgroup.mul_mem Γ (ratH_mem _ σ _ g) (Subgroup.inv_mem Γ (ratH_mem _ σ _ (rr q)))`. Use `⟨q, ⟨⟨_, hst⟩, hmemu, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ratH (AF F) σ _ g = ratH (AF F) σ _ g * (r q)⁻¹ * r q`.

Rewrite using `[inv_mul_cancel_right]`. Introduce and unpack `q' ⟨u', -, he⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `ratTup_adele_injective (F := F)` to reduce the goal to its premises. Establish `e1 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q.1`.

Rewrite using `[ratH_inv, hfix]`. Establish `e2 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q'.1`. Establish `e3 : (r q')⁻¹ = ratH (AF F) σ _ (rr q')⁻¹` using `ratH_inv _ σ _ _`. Establish `h6 : (ratH (AF F) σ _ g)⁻¹ = (r q')⁻¹ * ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J))`. Rewrite using `[he, mul_inv_rev]`.

Both sides reduce to the same expression. Establish `h7 : actW (AF F) σ (hypOne J) ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M` using `(u'⁻¹).2`. Rewrite using `[h6, hmul, h7, e3, hfix, hrinv]`. Rewrite using `[← e1, ← e2]`. Establish `key` using `GlobalTheory.T.quotient_measure_tower _ _ (stabilizer₂ (AF F) σ J).subtype hPc.isClosedEmbedding_subtypeVal μ μP Γ (ratP (AF F) σ J) 𝓕 𝓕P h𝓕 h𝓕P hPf hΓ _ r (fun q => ratH_mem _ σ _ _) huniq (phiA σ J n Φ) hφ hinv`.

Establish `hA : ∀ h : HA (AF F) σ (hypOne J), ∑' Y : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) = ∑' q, phiA σ J n Φ (r q * h)`. Introduce `h`. Rewrite using `[GlobalTheory.T.isotropic_frames_sum_by_orbit F E σ M J n rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]`. Use `tsum_congr fun q => tsum_congr fun X => ?_` and prove the remaining obligations. Establish `e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹` using `ratH_inv _ σ _ _`.

Rewrite using `[mul_inv_rev, hmul, e3, actW_ratH']`. Rewrite using `[GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 (n + 1) _ Φ hΦ, GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 1 _ Ψ hΨ]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun h => tsum_congr fun q => ?_` and prove the remaining obligations.

Establish `e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹` using `ratH_inv _ σ _ _`. Use `(hmean (r q * h)).trans ?_` and prove the remaining obligations. Rewrite using `[mul_inv_rev, hmul, e3, hfix, hrinv]`.
-/
theorem unfold_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (μ : Measure (HA (AF F) σ (hypOne J))) 𝓕, IsHaarH F E σ (M + 2) (hypOne J) μ → IsFDH F E σ (M + 2) (hypOne J) μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∫⁻ X, Φ X ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E))) = ∫⁻ y, Ψ y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n hn hM μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hΨ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨hJb, he0, hgq⟩ := GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  obtain ⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := c1
  haveI := c2
  haveI := c3
  haveI := c4
  haveI := hB (n + 1) (M + 2)
  haveI := hB 1 (M + 2)
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  obtain ⟨μP, 𝓕P, hμP, h𝓕P, hPf, hmean⟩ := meanP F E σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp
  haveI := hμP
  have hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J))) :=
    isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const
  haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _
  haveI hc : Countable (HFinIn (AF F) σ (hypOne J)) := (rational_countable_discrete F E σ hσ (M + 2) _ hJb).1
  let Γ : Subgroup (HA (AF F) σ (hypOne J)) := HFinIn (AF F) σ (hypOne J)
  haveI hc' : Countable Γ := hc
  haveI hcP : Countable (ratP (AF F) σ J) := by
    have hinj : Function.Injective fun γ : ratP (AF F) σ J =>
        (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J)) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))
    exact hinj.countable
  have hW : ∀ q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E),
      ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q.1 = e0 E M :=
    fun q => GlobalTheory.T.global_unitary_moves_isotropic_frame F E σ hσ M J hJ q.1 q.2
  choose rr hrr using hW
  let r := fun q => ratH (AF F) σ (hypOne J) (rr q)
  have hφ : Measurable (phiA σ J n Φ) := by
    refine Measurable.ennreal_tsum fun X => hΦ.comp ?_
    have : Continuous fun g : HA (AF F) σ (hypOne J) =>
        actW (AF F) σ (hypOne J) g⁻¹ (ratTup (AF F) X.1) :=
      (act (n + 1)).1.comp (continuous_inv.prodMk continuous_const)
    exact this.measurable
  have hmul : ∀ (g h : HA (AF F) σ (hypOne J)) {k : ℕ} (X : Fin k → Fin (M + 2) → AF F ⊗[F] E),
      actW (AF F) σ _ (g * h) X = actW (AF F) σ _ g (actW (AF F) σ _ h X) :=
    fun g h {k} X => actW_mul_apply _ σ _ g h X
  have hfix : ∀ g : UJ (σ : E →+* E) (hypOne J),
      actW (AF F) σ _ (ratH (AF F) σ _ g) (e0 _ M) = ratTup (AF F) (gact σ g (e0 E M)) := by
    intro g
    rw [← ratTup_e0, actW_ratH']
  have hinv : ∀ u ∈ ratP (AF F) σ J, ∀ g, phiA σ J n Φ ((stabilizer₂ (AF F) σ J).subtype u * g) = phiA σ J n Φ g := by
    intro u hu g
    obtain ⟨w, hw⟩ := exists_ratH (AF F) σ _ (u : HA (AF F) σ (hypOne J)) hu
    have hw0 : gact σ w (e0 E M) = e0 E M := by
      have h1 : actW (AF F) σ (hypOne J) (u : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M := u.2
      rw [hw, hfix, ← ratTup_e0] at h1
      exact ratTup_adele_injective (F := F) h1
    have hw1 : gact σ w⁻¹ (e0 E M) = e0 E M := by
      conv_lhs => rw [← hw0]
      exact gact_inv_gact σ w _
    have e : ∀ X : Fin (n + 1) → Fin (M + 2) → E,
        actW (AF F) σ _ ((stabilizer₂ (AF F) σ J).subtype u * g)⁻¹ (ratTup (AF F) X) =
          actW (AF F) σ _ g⁻¹ (ratTup (AF F) (gact σ w⁻¹ X)) := by
      intro X
      rw [mul_inv_rev, hmul]
      change actW (AF F) σ _ g⁻¹ (actW (AF F) σ _ (u : HA (AF F) σ (hypOne J))⁻¹ (ratTup (AF F) X)) = _
      rw [hw, ratH_inv, actW_ratH']
    simp only [phiA, e]
    exact GlobalTheory.T.frames_sum_invariant_under_stabiliser F E σ M J n w⁻¹ hw1 (fun X => Φ (actW (AF F) σ _ g⁻¹ (ratTup (AF F) X)))
  have hΓ : ∀ u ∈ ratP (AF F) σ J, (stabilizer₂ (AF F) σ J).subtype u ∈ Γ := fun u hu => hu
  have hrinv : ∀ q, gact σ (rr q)⁻¹ (e0 E M) = q.1 := by
    intro q
    rw [← hrr q, gact_inv_gact]
  have huniq : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ ratP (AF F) σ J, γ = (stabilizer₂ (AF F) σ J).subtype u * r q := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := exists_ratH (AF F) σ _ γ hγ
    have hy := hgq g⁻¹ _ he0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hy⟩
    have hst : ratH (AF F) σ _ g * (r q)⁻¹ ∈ stabilizer₂ (AF F) σ J := by
      change actW (AF F) σ _ (ratH (AF F) σ _ g * (r q)⁻¹) (e0 _ M) = e0 _ M
      have e1 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hmul, e1, hfix, hrinv, actW_ratH']
      change ratTup (AF F) (gact σ g (gact σ g⁻¹ _)) = _
      rw [gact_gact_inv, ratTup_e0]
    have hmemu : (⟨_, hst⟩ : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J :=
      Subgroup.mul_mem Γ (ratH_mem _ σ _ g) (Subgroup.inv_mem Γ (ratH_mem _ σ _ (rr q)))
    refine ⟨q, ⟨⟨_, hst⟩, hmemu, ?_⟩, ?_⟩
    · change ratH (AF F) σ _ g = ratH (AF F) σ _ g * (r q)⁻¹ * r q
      rw [inv_mul_cancel_right]
    rintro q' ⟨u', -, he⟩
    apply Subtype.ext
    apply ratTup_adele_injective (F := F)
    have e1 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q.1 := by
      rw [ratH_inv, hfix]
    have e2 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q'.1 := by
      have e3 : (r q')⁻¹ = ratH (AF F) σ _ (rr q')⁻¹ := ratH_inv _ σ _ _
      have h6 : (ratH (AF F) σ _ g)⁻¹ = (r q')⁻¹ * ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) := by
        rw [he, mul_inv_rev]
        rfl
      have h7 : actW (AF F) σ (hypOne J) ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M :=
        (u'⁻¹).2
      rw [h6, hmul, h7, e3, hfix, hrinv]
    rw [← e1, ← e2]
  have key := GlobalTheory.T.quotient_measure_tower _ _ (stabilizer₂ (AF F) σ J).subtype hPc.isClosedEmbedding_subtypeVal μ μP Γ
    (ratP (AF F) σ J) 𝓕 𝓕P h𝓕 h𝓕P hPf hΓ _ r (fun q => ratH_mem _ σ _ _) huniq (phiA σ J n Φ) hφ hinv
  have hA : ∀ h : HA (AF F) σ (hypOne J),
      ∑' Y : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E),
        Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) = ∑' q, phiA σ J n Φ (r q * h) := by
    intro h
    rw [GlobalTheory.T.isotropic_frames_sum_by_orbit F E σ M J n rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]
    refine tsum_congr fun q => tsum_congr fun X => ?_
    have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
    rw [mul_inv_rev, hmul, e3, actW_ratH']
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 (n + 1) _ Φ hΦ,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 1 _ Ψ hΨ]
  congr 1
  calc _ = ∫⁻ h in 𝓕, ∑' q, phiA σ J n Φ (r q * h) ∂μ := lintegral_congr hA
    _ = _ := key
    _ = _ := by
      refine lintegral_congr fun h => tsum_congr fun q => ?_
      have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      refine (hmean (r q * h)).trans ?_
      rw [mul_inv_rev, hmul, e3, hfix, hrinv]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
