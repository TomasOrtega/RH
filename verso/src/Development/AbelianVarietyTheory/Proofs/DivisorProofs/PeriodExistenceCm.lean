import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEquiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleClassIdentityComponentIffArtinKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedIdeleEqLocalIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriodStatement

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal

open Neutral.B1

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod h2 ι Λ₀ Ω₀ hΛ hΩ`.
-/
theorem exists_uniformisation_torsTransport {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ≠ 0) :
    letI : Algebra K ℂ := ι.toAlgebra
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ :=
  GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod h2 ι Λ₀ Ω₀ hΛ hΩ

/- English proof (translation)
Take `⟨φ, hφc, hφb, hφ⟩` from `GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv e`. Set `ψ : Ideles K →* Field.absoluteGaloisGroupAbelianization K` to `φ.comp art⁻¹`. Establish `hψ : ∀ s, ψ s = φ (art s)⁻¹` using `fun s => rfl`. Establish `hle : (diagUnits K).range ≤ ψ.ker`. Introduce and unpack `_ ⟨k, rfl⟩`.

Establish `hk : diagUnits K k ∈ art.ker`. Rewrite using `[ha.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)`. Rewrite using `[MonoidHom.mem_ker, hψ, MonoidHom.mem_ker.mp hk, inv_one, map_one]`. Set `Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K` to `QuotientGroup.lift _ ψ hle`.

Establish `hArt : ∀ s, Art (QuotientGroup.mk s) = φ ((art s)⁻¹)` using `fun s => rfl`. Establish `hArtσ : ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ → Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e)` using `fun s σ h => by`. Rewrite using `[hArt, h, hφ]`. Use `⟨Art, ⟨?_, ?_, ?_, ?_, ?_⟩, hArtσ⟩` and prove the remaining obligations. Use `(QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_` and prove the remaining obligations.

Conclude with `hφc.comp (ha.quot.continuous.inv)`. Introduce `c`. Take `⟨y, rfl⟩` from `hφb.2 c`. Take `⟨x, rfl⟩` from `ha.quot.surjective y`. Conclude with `⟨QuotientGroup.mk x⁻¹, by rw [hArt, map_inv art, inv_inv]⟩`.

Use extensionality with `c`. Take `⟨s, rfl⟩` from `QuotientGroup.mk_surjective c`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, hArt, GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel ha, ← map_one φ, hφb.1.eq_iff, inv_eq_one]`. Introduce `L h v hv a hsupp`. Take `⟨x, hx, rfl⟩` from `GlobalTheory.T.supportedIdele_eq_localIdele hsupp`.

Take `⟨A, hA⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver Ω v`. Prove the components needed by the constructor for the conclusion. Introduce `hu Q hQ hQv`. Rewrite `hu` using `[← hx]`. Take `⟨σ, hσ, hσe⟩` from `(ha.frob v A hA (art (localIdele K v x))).1 ⟨x, (GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt v x).1 hu, rfl⟩`.

Rewrite using `[hArtσ _ σ (by rw [← hσe, map_inv, inv_inv]), abRestrict_mk]`. Conclude with `GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension e L h v A hA σ hσ Q hQ hQv`. Introduce `hu`. Rewrite `hu` using `[← hx]`. Take `⟨σ, hσ, hσe⟩` from `(ha.ine v A hA (art (localIdele K v x))).1 ⟨x, hu, rfl⟩`.

Rewrite using `[hArtσ _ σ⁻¹ (by rw [← hσe, map_inv]), abRestrict_mk]`. Conclude with `GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one e L h v hv A hA σ⁻¹ ((ReciprocityTheory.Gal.Ine A).inv_mem hσ)`. Introduce `L h w hw`. Conclude with `absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))`.
-/
theorem exists_globalArtinMap {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (e : Ω ≃ₐ[K] AlgebraicClosure K) :
    ∃ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art ∧
      ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
        Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  obtain ⟨φ, hφc, hφb, hφ⟩ := GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv e
  let ψ : Ideles K →* Field.absoluteGaloisGroupAbelianization K := φ.comp art⁻¹
  have hψ : ∀ s, ψ s = φ (art s)⁻¹ := fun s => rfl
  have hle : (diagUnits K).range ≤ ψ.ker := by
    rintro _ ⟨k, rfl⟩
    have hk : diagUnits K k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    rw [MonoidHom.mem_ker, hψ, MonoidHom.mem_ker.mp hk, inv_one, map_one]
  let Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K := QuotientGroup.lift _ ψ hle
  have hArt : ∀ s, Art (QuotientGroup.mk s) = φ ((art s)⁻¹) := fun s => rfl
  have hArtσ : ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
      Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := fun s σ h => by
    rw [hArt, h, hφ]
  refine ⟨Art, ⟨?_, ?_, ?_, ?_, ?_⟩, hArtσ⟩
  · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    exact hφc.comp (ha.quot.continuous.inv)
  · intro c
    obtain ⟨y, rfl⟩ := hφb.2 c
    obtain ⟨x, rfl⟩ := ha.quot.surjective y
    exact ⟨QuotientGroup.mk x⁻¹, by rw [hArt, map_inv art, inv_inv]⟩
  · ext c
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hArt, GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel ha,
      ← map_one φ, hφb.1.eq_iff, inv_eq_one]
  · intro L h v hv a hsupp
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.supportedIdele_eq_localIdele hsupp
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
    constructor
    · intro hu Q hQ hQv
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.frob v A hA (art (localIdele K v x))).1
        ⟨x, (GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt v x).1 hu, rfl⟩
      rw [hArtσ _ σ (by rw [← hσe, map_inv, inv_inv]), abRestrict_mk]
      exact GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension e L h v A hA σ hσ Q hQ hQv
    · intro hu
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.ine v A hA (art (localIdele K v x))).1 ⟨x, hu, rfl⟩
      rw [hArtσ _ σ⁻¹ (by rw [← hσe, map_inv]), abRestrict_mk]
      exact GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one e L h v hv A hA σ⁻¹ ((ReciprocityTheory.Gal.Ine A).inv_mem hσ)
  · intro L h w hw
    exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))

/- English proof (translation)
Introduce `hMT K _ _ _ ι h2 Λ₀ Ω₀ hΛ hΩ Ω _ _ _ j art hj ha g σ t hσg hsym`. Use `letI : Algebra K ℂ := ι.toAlgebra`. Establish `hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x` using `fun x => by`. Express the relevant statement in the definitionally equal form `g (ι x) = ι x`. Rewrite using `[← hj, RingHom.comp_apply, ← hσg, AlgEquiv.commutes]`.

Set `gK : ℂ ≃ₐ[K] ℂ` to `AlgEquiv.ofRingEquiv (f := g) hg`. Take `⟨X, hX, ξ, hξ, hT⟩` from `exists_uniformisation_torsTransport h2 ι Λ₀ Ω₀ hΛ hΩ`. Set `e` to `IsAlgClosure.equiv K Ω (AlgebraicClosure K)`. Take `⟨Art, hArt, hArtσ⟩` from `exists_globalArtinMap ha e`. Establish `hjK : ∀ x : K, j (algebraMap K Ω x) = algebraMap K ℂ x` using `fun x => by`.

Rewrite using `[← RingHom.comp_apply, hj]`. Both sides reduce to the same expression. Set `jK : Ω →ₐ[K] ℂ` to `{ j with commutes' := hjK }`. Establish `hR : GlobalTheory.EllipticCM.RestrictsTo gK (Art (QuotientGroup.mk (finIdele K t)))`. Rewrite using `[hArtσ _ σ hsym]`.

Use `⟨jK.comp e.symm.toAlgHom, (e.symm.trans σ).trans e, fun x => ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (j (e.symm x)) = j (e.symm (e (σ (e.symm x))))`. Rewrite using `[AlgEquiv.symm_apply_apply, hσg]`. Establish `hTr` using `hMT K h2 Art hArt gK (finIdele K t) hR X 1 one_ne_zero ξ hξ`. Rewrite `hTr` using `[show GlobalTheory.EllipticCM.finitePart (finIdele K t) = t from GlobalTheory.EllipticCM.finitePart_inr t]`.

Conclude with `hT gK t hTr`.
-/
theorem periodEx_of_mainTheorem : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  intro hMT K _ _ _ ι h2 Λ₀ Ω₀ hΛ hΩ Ω _ _ _ j art hj ha g σ t hσg hsym
  letI : Algebra K ℂ := ι.toAlgebra
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← hj, RingHom.comp_apply, ← hσg, AlgEquiv.commutes]
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨X, hX, ξ, hξ, hT⟩ := exists_uniformisation_torsTransport h2 ι Λ₀ Ω₀ hΛ hΩ
  let e := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  obtain ⟨Art, hArt, hArtσ⟩ := exists_globalArtinMap ha e
  have hjK : ∀ x : K, j (algebraMap K Ω x) = algebraMap K ℂ x := fun x => by
    rw [← RingHom.comp_apply, hj]
    rfl
  let jK : Ω →ₐ[K] ℂ := { j with commutes' := hjK }
  have hR : GlobalTheory.EllipticCM.RestrictsTo gK (Art (QuotientGroup.mk (finIdele K t))) := by
    rw [hArtσ _ σ hsym]
    refine ⟨jK.comp e.symm.toAlgHom, (e.symm.trans σ).trans e, fun x => ?_, rfl⟩
    change g (j (e.symm x)) = j (e.symm (e (σ (e.symm x))))
    rw [AlgEquiv.symm_apply_apply, hσg]
  have hTr := hMT K h2 Art hArt gK (finIdele K t) hR X 1 one_ne_zero ξ hξ
  rw [show GlobalTheory.EllipticCM.finitePart (finIdele K t) = t from GlobalTheory.EllipticCM.finitePart_inr t] at hTr
  exact hT gK t hTr

end GlobalTheory.LatVal
