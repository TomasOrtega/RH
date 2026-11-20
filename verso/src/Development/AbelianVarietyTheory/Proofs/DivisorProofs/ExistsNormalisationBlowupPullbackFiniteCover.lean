import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationNormalisedBlowupSiegelModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

/- English proof (translation)
Introduce `o _ Z Z' M z _ b _ J hB _ _ U g' _ hne`. Use `haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ o`. Use `haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z`. Use `haveI : LocallyOfFiniteType (g' ≫ U.ι ≫ z) := inferInstance`. Use `haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian (g' ≫ U.ι ≫ z)`.

Set `Vi : Z.Opens` to `J.support.compl`. Use `haveI hbV : IsIso (b ∣_ Vi) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB Vi (fun x hx => hx)`. Establish `monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ Z'), u ≫ b = v ≫ b → Set.range (u ≫ b) ⊆ (Vi : Set Z) → u = v`. Introduce `T u v huv hr`. Establish `hu : Set.range u ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z')`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hr ⟨w, rfl⟩`. Establish `hv : Set.range v ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z')`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `hr ⟨w, rfl⟩` as an intermediate fact.

Rewrite `this` using `[huv]`. Conclude with `this`. Establish `hm : Mono ((b ⁻¹ᵁ Vi).ι ≫ b)`. Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`.

Rewrite `hu`, `hv` using `[← Scheme.Opens.range_ι]`. Rewrite using `[← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]`. Use `congr 1`. Rewrite using `[← cancel_mono ((b ⁻¹ᵁ Vi).ι ≫ b)]`. Simplify using `only [← Category.assoc, IsOpenImmersion.lift_fac]`.

Conclude with `huv`. Set `bU` to `b ∣_ U`. Establish `hbU : bU ≫ U.ι = (b ⁻¹ᵁ U).ι ≫ b` using `morphismRestrict_ι _ _`. Establish `monoU : ∀ {T : Scheme.{0}} (u v : T ⟶ (b ⁻¹ᵁ U).toScheme), u ≫ bU = v ≫ bU → Set.range (u ≫ bU ≫ U.ι) ⊆ (Vi : Set Z) → u = v`. Introduce `T u v huv hr`.

Rewrite using `[← cancel_mono (b ⁻¹ᵁ U).ι]`. Apply `monoV` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, ← hbU, ← Category.assoc, huv, Category.assoc]`. Rewrite using `[Category.assoc, ← hbU]`. Conclude with `hr`.

Set `V : M.Opens` to `(g' ≫ U.ι) ⁻¹ᵁ Vi`. Take `⟨m₀, hm₀⟩` from `hne`. Use `haveI : Nonempty V := ⟨⟨m₀, hm₀⟩⟩`. Set `c₀ : (V : Scheme.{0}) ⟶ Z'` to `(g' ≫ U.ι) ∣_ Vi ≫ inv (b ∣_ Vi) ≫ (b ⁻¹ᵁ Vi).ι`. Establish `hc₀ : c₀ ≫ b = V.ι ≫ g' ≫ U.ι`.

Simplify using `only [c₀, Category.assoc]`. Rewrite using `[← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]`. Establish `hr₀ : Set.range c₀ ⊆ Set.range (b ⁻¹ᵁ U).ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `show b (c₀ x) ∈ U`. Rewrite using `[← Scheme.Hom.comp_apply, hc₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `(g' (V.ι x)).2`. Set `c : (V : Scheme.{0}) ⟶ (b ⁻¹ᵁ U).toScheme` to `IsOpenImmersion.lift (b ⁻¹ᵁ U).ι c₀ hr₀`. Establish `hcι : c ≫ (b ⁻¹ᵁ U).ι = c₀` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hc : c ≫ bU = V.ι ≫ g'`. Rewrite using `[← cancel_mono U.ι, Category.assoc, hbU, ← Category.assoc, hcι, hc₀, Category.assoc]`. Set `j : (V : Scheme.{0}) ⟶ pullback bU g'` to `pullback.lift c V.ι hc`. Establish `hjs : j ≫ pullback.snd bU g' = V.ι` using `pullback.lift_snd _ _ _`. Establish `hjf : j ≫ pullback.fst bU g' = c` using `pullback.lift_fst _ _ _`.

Use `haveI : IsProper bU := by dsimp only [bU]; infer_instance`. Use `haveI : QuasiCompact (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance`. Use `haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd bU g')`. Use `haveI : QuasiSeparated (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance`. Use `haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd bU g')`.

Use `haveI : LocallyOfFiniteType (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance`. Use `haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd bU g')`. Use `haveI : GlobalTheory.IsNormalScheme (V : Scheme.{0}) := .of_isOpenImmersion V.ι`. Use `haveI : IsReduced (V : Scheme.{0}) := inferInstance`. Use `haveI : IsLocallyNoetherian (V : Scheme.{0}) := inferInstance`.

Use `haveI hfin : IsFinite j.fromNormalization := GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := o) j (pullback.fst bU g' ≫ bU ≫ U.ι ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap`. Set `p₁ : j.normalization ⟶ M` to `j.fromNormalization ≫ pullback.snd bU g'`. Set `ν₁ : j.normalization ⟶ (b ⁻¹ᵁ U).toScheme` to `j.fromNormalization ≫ pullback.fst bU g'`. Establish `hp₁ : j.toNormalization ≫ p₁ = V.ι` using `by show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd bU g' = V.ι`. Rewrite using `[Scheme.Hom.toNormalization_fromNormalization_assoc, hjs]`.

Establish `hcomm : ν₁ ≫ bU = p₁ ≫ g'` using `by simp [ν₁, p₁, pullback.condition]`. Use `⟨j.normalization, inferInstance, p₁, ν₁, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, hcomm, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show IsProper (j.fromNormalization ≫ pullback.snd bU g') infer_instance`. Use `show IsFinite (j.fromNormalization ≫ pullback.fst bU g') infer_instance`. Take `⟨D, hD⟩` from `GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1`.

Establish `hpe : p₁ ≫ g' ≫ U.ι = (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b`. Rewrite using `[← Category.assoc, ← hcomm, Category.assoc, hbU]`. Simplify using `only [Category.assoc]`. Establish `hK : D.KeepsRegular (ν₁ ≫ (b ⁻¹ᵁ U).ι)`. Use `D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Use `show (ν₁ ≫ (b ⁻¹ᵁ U).ι) (j.toNormalization x) ∉ D.idealSheaf.support`. Rewrite using `[hD, GlobalTheory.ProjBlowup.mem_support_comap]`. Introduce `h`. Apply `x.2` to reduce the goal to its premises.

Establish `: j.toNormalization ≫ (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b = V.ι ≫ g' ≫ U.ι`. Rewrite using `[← hpe, ← Category.assoc, hp₁]`. Rewrite `h` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]`. Conclude with `h`. Establish `e : J.comap (p₁ ≫ g' ≫ U.ι) = (D.pull (ν₁ ≫ (b ⁻¹ᵁ U).ι) hK).idealSheaf`.

Rewrite using `[GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]`. Rewrite using `[e]`. Conclude with `GlobalTheory.EffCartierData.effCartier_idealSheaf _`. Introduce `m hm`. Use `⟨j.toNormalization ⟨m, hm⟩, ?_⟩` and prove the remaining obligations.

Use `show (j.toNormalization ≫ p₁) ⟨m, hm⟩ = m`. Rewrite using `[hp₁]`. Both sides reduce to the same expression. Introduce `R _ _ _ a β hab hgen`. Set `d : Sp R ⟶ pullback bU g'` to `pullback.lift a β hab`.

Establish `hr : Set.range (jK R ≫ β) ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `show (g' ≫ U.ι) ((jK R ≫ β) w) ∉ J.support`. Rewrite using `[← Scheme.Hom.comp_apply]`.

Simplify `hgen w` using `only [Category.assoc]`. Set `y` to `IsOpenImmersion.lift V.ι (jK R ≫ β) hr`. Establish `hy : y ≫ V.ι = jK R ≫ β` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hyj : y ≫ j = jK R ≫ d`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hjf, Category.assoc, pullback.lift_fst]`. Apply `monoU` to reduce the goal to its premises. Rewrite using `[Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]`. Establish `key : y ≫ c ≫ bU ≫ U.ι = jK R ≫ β ≫ g' ≫ U.ι`. Rewrite using `[reassoc_of% hc, ← Category.assoc y, hy, Category.assoc]`.

Rewrite using `[Category.assoc, key]`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hgen w`. Rewrite using `[Category.assoc, hjs, Category.assoc, pullback.lift_snd, hy]`. Take `⟨ξ, ⟨-, hξ⟩, -⟩` from `GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R) (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])`.

Use `⟨ξ, ?_, ?_⟩` and prove the remaining obligations. Use `show ξ ≫ j.fromNormalization ≫ pullback.fst bU g' = a`. Rewrite using `[← Category.assoc, hξ, pullback.lift_fst]`. Use `show ξ ≫ j.fromNormalization ≫ pullback.snd bU g' = β`. Rewrite using `[← Category.assoc, hξ, pullback.lift_snd]`.
-/
theorem exists_normalisation_pullback_cover : ∀ {o : CommRingCat.{0}} [Algebra.FiniteType ℤ o] {Z Z' M : Scheme.{0}} (z : Z ⟶ Spec o) [LocallyOfFiniteType z] (b : Z' ⟶ Z) [IsProper b] (J : Z.IdealSheafData), FinalTheorems.Blowup b J → ∀ [IsIntegral M] [GlobalTheory.IsNormalScheme M] (U : Z.Opens) (g' : M ⟶ U.toScheme) [IsFinite g'], (∃ m, (g' ≫ U.ι) m ∉ J.support) → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (ν₁ : S₁ ⟶ (b ⁻¹ᵁ U).toScheme), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsFinite ν₁ ∧ ν₁ ≫ (b ∣_ U) = p₁ ≫ g' ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g' ≫ U.ι)) ∧ (∀ m, (g' ≫ U.ι) m ∉ J.support → m ∈ Set.range p₁) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (a : Sp R ⟶ (b ⁻¹ᵁ U).toScheme) (β : Sp R ⟶ M), a ≫ (b ∣_ U) = β ≫ g' → (∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support) → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν₁ = a ∧ ξ₁ ≫ p₁ = β := by
  intro o _ Z Z' M z _ b _ J hB _ _ U g' _ hne
  haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ o
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI : LocallyOfFiniteType (g' ≫ U.ι ≫ z) := inferInstance
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian (g' ≫ U.ι ≫ z)
  let Vi : Z.Opens := J.support.compl
  haveI hbV : IsIso (b ∣_ Vi) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB Vi (fun x hx => hx)
  have monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ Z'), u ≫ b = v ≫ b → Set.range (u ≫ b) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    have hu : Set.range u ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z') := by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨w, rfl⟩
    have hv : Set.range v ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z') := by
      rintro _ ⟨w, rfl⟩
      have := hr ⟨w, rfl⟩
      rw [huv] at this
      exact this
    have hm : Mono ((b ⁻¹ᵁ Vi).ι ≫ b) := by
      rw [← morphismRestrict_ι]; infer_instance
    rw [← Scheme.Opens.range_ι] at hu hv
    rw [← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]
    congr 1
    rw [← cancel_mono ((b ⁻¹ᵁ Vi).ι ≫ b)]
    simp only [← Category.assoc, IsOpenImmersion.lift_fac]
    exact huv
  let bU := b ∣_ U
  have hbU : bU ≫ U.ι = (b ⁻¹ᵁ U).ι ≫ b := morphismRestrict_ι _ _
  have monoU : ∀ {T : Scheme.{0}} (u v : T ⟶ (b ⁻¹ᵁ U).toScheme), u ≫ bU = v ≫ bU →
      Set.range (u ≫ bU ≫ U.ι) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    rw [← cancel_mono (b ⁻¹ᵁ U).ι]
    apply monoV
    · rw [Category.assoc, Category.assoc, ← hbU, ← Category.assoc, huv, Category.assoc]
    · rw [Category.assoc, ← hbU]; exact hr
  let V : M.Opens := (g' ≫ U.ι) ⁻¹ᵁ Vi
  obtain ⟨m₀, hm₀⟩ := hne
  haveI : Nonempty V := ⟨⟨m₀, hm₀⟩⟩
  let c₀ : (V : Scheme.{0}) ⟶ Z' := (g' ≫ U.ι) ∣_ Vi ≫ inv (b ∣_ Vi) ≫ (b ⁻¹ᵁ Vi).ι
  have hc₀ : c₀ ≫ b = V.ι ≫ g' ≫ U.ι := by
    simp only [c₀, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hr₀ : Set.range c₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show b (c₀ x) ∈ U
    rw [← Scheme.Hom.comp_apply, hc₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (g' (V.ι x)).2
  let c : (V : Scheme.{0}) ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι c₀ hr₀
  have hcι : c ≫ (b ⁻¹ᵁ U).ι = c₀ := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ bU = V.ι ≫ g' := by
    rw [← cancel_mono U.ι, Category.assoc, hbU, ← Category.assoc, hcι, hc₀, Category.assoc]
  let j : (V : Scheme.{0}) ⟶ pullback bU g' := pullback.lift c V.ι hc
  have hjs : j ≫ pullback.snd bU g' = V.ι := pullback.lift_snd _ _ _
  have hjf : j ≫ pullback.fst bU g' = c := pullback.lift_fst _ _ _
  haveI : IsProper bU := by dsimp only [bU]; infer_instance
  haveI : QuasiCompact (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd bU g')
  haveI : QuasiSeparated (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd bU g')
  haveI : LocallyOfFiniteType (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd bU g')
  haveI : GlobalTheory.IsNormalScheme (V : Scheme.{0}) := .of_isOpenImmersion V.ι
  haveI : IsReduced (V : Scheme.{0}) := inferInstance
  haveI : IsLocallyNoetherian (V : Scheme.{0}) := inferInstance
  haveI hfin : IsFinite j.fromNormalization :=
    GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := o) j
      (pullback.fst bU g' ≫ bU ≫ U.ι ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap
  let p₁ : j.normalization ⟶ M := j.fromNormalization ≫ pullback.snd bU g'
  let ν₁ : j.normalization ⟶ (b ⁻¹ᵁ U).toScheme := j.fromNormalization ≫ pullback.fst bU g'
  have hp₁ : j.toNormalization ≫ p₁ = V.ι := by
    show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd bU g' = V.ι
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, hjs]
  have hcomm : ν₁ ≫ bU = p₁ ≫ g' := by simp [ν₁, p₁, pullback.condition]
  refine ⟨j.normalization, inferInstance, p₁, ν₁, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · show IsProper (j.fromNormalization ≫ pullback.snd bU g')
    infer_instance
  · show IsFinite (j.fromNormalization ≫ pullback.fst bU g')
    infer_instance
  · obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1
    have hpe : p₁ ≫ g' ≫ U.ι = (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b := by
      rw [← Category.assoc, ← hcomm, Category.assoc, hbU]; simp only [Category.assoc]
    have hK : D.KeepsRegular (ν₁ ≫ (b ⁻¹ᵁ U).ι) := by
      refine D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)
      rintro _ ⟨x, rfl⟩
      show (ν₁ ≫ (b ⁻¹ᵁ U).ι) (j.toNormalization x) ∉ D.idealSheaf.support
      rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
      intro h
      apply x.2
      have : j.toNormalization ≫ (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b = V.ι ≫ g' ≫ U.ι := by
        rw [← hpe, ← Category.assoc, hp₁]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this] at h
      exact h
    have e : J.comap (p₁ ≫ g' ≫ U.ι) = (D.pull (ν₁ ≫ (b ⁻¹ᵁ U).ι) hK).idealSheaf := by
      rw [GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]
    rw [e]
    exact GlobalTheory.EffCartierData.effCartier_idealSheaf _
  · intro m hm
    refine ⟨j.toNormalization ⟨m, hm⟩, ?_⟩
    show (j.toNormalization ≫ p₁) ⟨m, hm⟩ = m
    rw [hp₁]
    rfl
  · intro R _ _ _ a β hab hgen
    let d : Sp R ⟶ pullback bU g' := pullback.lift a β hab
    have hr : Set.range (jK R ≫ β) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show (g' ≫ U.ι) ((jK R ≫ β) w) ∉ J.support
      rw [← Scheme.Hom.comp_apply]
      simpa only [Category.assoc] using hgen w
    let y := IsOpenImmersion.lift V.ι (jK R ≫ β) hr
    have hy : y ≫ V.ι = jK R ≫ β := IsOpenImmersion.lift_fac _ _ _
    have hyj : y ≫ j = jK R ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, hjf, Category.assoc, pullback.lift_fst]
        apply monoU
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]
        · have key : y ≫ c ≫ bU ≫ U.ι = jK R ≫ β ≫ g' ≫ U.ι := by
            rw [reassoc_of% hc, ← Category.assoc y, hy, Category.assoc]
          rw [Category.assoc, key]
          rintro _ ⟨w, rfl⟩
          exact hgen w
      · rw [Category.assoc, hjs, Category.assoc, pullback.lift_snd, hy]
    obtain ⟨ξ, ⟨-, hξ⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R)
      (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d
      (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])
    refine ⟨ξ, ?_, ?_⟩
    · show ξ ≫ j.fromNormalization ≫ pullback.fst bU g' = a
      rw [← Category.assoc, hξ, pullback.lift_fst]
    · show ξ ≫ j.fromNormalization ≫ pullback.snd bU g' = β
      rw [← Category.assoc, hξ, pullback.lift_snd]

end GlobalTheory.USep
