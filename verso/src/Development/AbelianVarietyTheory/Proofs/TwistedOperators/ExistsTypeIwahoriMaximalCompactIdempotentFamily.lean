import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FixedOfForallLocalSubgroupFixedFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegratedOperatorNormalizedIndicatorProdFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentOperatorFixSpanImagesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRestrictedFiniteTensorFamilyTypeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GroupConvolutionNormalizedIndicatorSelfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothRepIntegratedOperatorNormalizedIndicatorFiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTypeLevelFamilyIsOpenLeLatticeStabilizerStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

/- English proof (translation)
Introduce `v l`. Establish `hi` using `hρ.smoothOp_integrand hf.1 hf.2 v`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `integrable_map (μ := μ) hi.1 hi.2 l l.map_zero` using `[smul_eq_mul]`. Rewrite using `[hρ.map_smoothOp (μ := μ) hf.1 hf.2 l v]`.

Simplify using `[smul_eq_mul]`.
-/
theorem isIntegralOp_smoothOp {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G W} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f ∧ HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf.1 hf.2 v
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
  · rw [hρ.map_smoothOp (μ := μ) hf.1 hf.2 l v]
    simp [smul_eq_mul]

/- English proof (translation)
Introduce `x` and use `(hσ x).preimage ((continuous_emb D.sp.cm.sig V.gram v).subtype_mk _)`.
-/
theorem isSmooth_comp_locFin {D : D7} {V : HSp D} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.PRep.IsSmooth (σ.comp (locFin V v)) := fun x =>
  (hσ x).preimage ((continuous_emb D.sp.cm.sig V.gram v).subtype_mk _)

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D V T U hu μf hH h1 ν hν`. Use `⟨fam T U μf T.S, GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu T.S, fun v => fam_of_mem T U μf T.S v.2 v.2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Distinguish the cases in `hv : v ∈ T.S`. Rewrite using `[fam_of_mem T U μf T.S hv hv]`.

Set `s` to `T.frame ⟨v, hv⟩`. Establish `hk : IsOpen (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v))`. Rewrite using `[show (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) = (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram s.emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from Set.ext s.red_eq_one_iff]`. Conclude with `(isOpen_stabLocOne V.gram s.emb (frameLat V) s.cm).preimage continuous_subtype_val`. Conclude with `conv_typeIdem (μf v) (isOpen_stabLoc _ _ _ v) (isCompact_stabLoc _ _ _ v) s.red_surjective hk _ (T.irred _)`.

Rewrite using `[fam_of_not T U μf T.S (fun h => hv h.1)]`. Take `⟨ho, hle⟩` from `GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu v`. Conclude with `GlobalTheory.T.groupConvolution_normalizedIndicator_self _ (μf v) _ ho ((isCompact_stabLoc _ _ _ v).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle)`. Introduce `k hk g`. Rewrite using `[fam_of_not T U μf T.S (fun h => hu h.1), levelFam_u]`.

Simplify using `only [normInd, Pi.smul_apply]`. Use `congr 1`. Distinguish the cases in `hg : g ∈ U.frame.iwahori`. Rewrite using `[indicator_of_mem (show k * g ∈ (U.frame.iwahori : Set _) from mul_mem hk hg), indicator_of_mem (show g ∈ (U.frame.iwahori : Set _) from hg)]`. Both sides reduce to the same expression.

Rewrite using `[indicator_of_notMem (show k * g ∉ (U.frame.iwahori : Set _) from fun h => hg ((Subgroup.mul_mem_cancel_left _ hk).1 h)), indicator_of_notMem (show g ∉ (U.frame.iwahori : Set _) from hg)]`. Introduce `v hv hvu k hk k' hk' g`. Rewrite using `[fam_of_not T U μf T.S (fun h => hv h.1), levelFam_of_notMem T U hv hvu]`. Simplify using `only [normInd, Pi.smul_apply]`. Use `congr 1`.

Establish `: k * g * k' ∈ Kv V v ↔ g ∈ Kv V v`. Rewrite using `[Subgroup.mul_mem_cancel_right _ hk', Subgroup.mul_mem_cancel_left _ hk]`. Distinguish the cases in `hg : g ∈ Kv V v`. Rewrite using `[indicator_of_mem (show k * g * k' ∈ (Kv V v : Set _) from this.2 hg), indicator_of_mem (show g ∈ (Kv V v : Set _) from hg)]`. Both sides reduce to the same expression.

Rewrite using `[indicator_of_notMem (show k * g * k' ∉ (Kv V v : Set _) from fun h => hg (this.1 h)), indicator_of_notMem (show g ∉ (Kv V v : Set _) from hg)]`. Introduce `W _ _ σ hσ hT P hP`. Rewrite `hT` using `[HasTypeVec]`. Take `⟨x, hx0, hxK, hxS⟩` from `hT`. Establish `hxker : ∀ v : T.S, ∀ k ∈ kerSub T v, σ (locFin V v k) x = x`.

Introduce `v`. Establish `hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤ GlobalTheory.PRep.fixed (σ.comp (locFin V v)) (kerSub T v)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, z, rfl⟩ ⟨_, ⟨k, hk1, rfl⟩⟩`. Use `hφ k z` as an intermediate fact.

Rewrite `this` using `[MonoidHom.mem_ker.1 hk1, map_one]`. Simplify using `using this.symm`. Introduce `k hk`. Simplify using `using hle (hxS v) ⟨k, hk⟩`. Establish `hxlev : ∀ v, ∀ k ∈ levelFam T U v, σ (locFin V v k) x = x`.

Introduce `v k hk`. Distinguish the cases in `hvu : v = U.u`. Substitute `hvu` using the available equality. Rewrite `hk` using `[levelFam_u]`. Conclude with `hxK _ hu k (U.frame.iwahori_le hk)`.

Distinguish the cases in `hv : v ∈ T.S`. Rewrite `hk` using `[levelFam_of_mem T U hu ⟨v, hv⟩]`. Conclude with `hxker ⟨v, hv⟩ k hk`. Rewrite `hk` using `[levelFam_of_notMem T U hv hvu]`. Conclude with `hxK v hv k hk`.

Establish `hlev` using `GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu`. Establish `key : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), A ⊆ T.S → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A)) P → P x = x`. Introduce `A`. Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty`.

Introduce `_ P hP`. Establish `e : fam T U μf ∅ = fun v => normInd (μf v) (levelFam T U v : Set _)`. Use function extensionality and compare the values at `fun v => fam_of_not T U μf ∅ (fun h => Finset.notMem_empty v h.2)`. Rewrite `hP` using `[e]`. Use `GlobalTheory.T.integratedOperator_normalizedIndicatorProd_fixed D V μf hH h1 ν hν (levelFam T U) (fun v => (hlev v).1) (fun v => (hlev v).2) ?_ W σ x (GlobalTheory.T.fixed_of_forall_localSubgroup_fixed_finiteAdelic D V W σ hσ (levelFam T U) (fun v => (hlev v).2) x hxlev) P hP` and prove the remaining obligations.

Use `filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u] with v hv hvu`. Conclude with `levelFam_of_notMem T U hv hvu`. Consider the case `insert a A ha ih`. Introduce `hsub P hP`. Establish `haS : a ∈ T.S` using `hsub (Finset.mem_insert_self a A)`.

Take `⟨H, K, -, -, -, hHB⟩` from `GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V a μf hH h1 ν hν W σ hσ (fam T U μf A) (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A)`. Establish `hloc` using `isSmooth_comp_locFin hσ a`. Establish `hfin` using `(GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A).1`. Establish `hfin'` using `(GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu (insert a A)).1`. Establish `hg : fam T U μf (insert a A) a = T.idem μf ⟨a, haS⟩` using `fam_of_mem T U μf _ haS (Finset.mem_insert_self _ _)`.

Establish `e1 : Function.update (fam T U μf A) a (fam T U μf (insert a A) a) = fam T U μf (insert a A)`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hva : v = a`. Substitute `hva` using the available equality. Rewrite using `[Function.update_self]`.

Rewrite using `[Function.update_of_ne hva]`. Distinguish the cases in `hv : v ∈ T.S ∧ v ∈ A`. Rewrite using `[fam_of_mem T U μf _ hv.1 hv.2, fam_of_mem T U μf _ hv.1 (Finset.mem_insert_of_mem hv.2)]`. Rewrite using `[fam_of_not T U μf _ hv, fam_of_not T U μf _ (fun h => hv ⟨h.1, (Finset.mem_insert.1 h.2).resolve_left hva⟩)]`. Establish `h2 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf (insert a A))) (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a))`.

Use `hHB _ (hfin' a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin' a).1, (hfin' a).2⟩)` as an intermediate fact. Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Establish `hPB` using `hP.unique h2`. Establish `h3 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A)) (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a))`. Use `hHB _ (hfin a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin a).1, (hfin a).2⟩)` as an intermediate fact.

Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis. Establish `hB'` using `ih (fun v hv => hsub (Finset.mem_insert_of_mem hv)) _ h3`. Establish `hBx : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a) x = x` using `hg ▸ GlobalTheory.T.typeIdempotentOperator_fix_span_images D V T μf hH W σ hσ ⟨a, haS⟩ x (hxS ⟨a, haS⟩)`. Establish `hB'x : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a) x = x`. Rewrite using `[fam_of_not T U μf A (fun h => ha h.2)]`.

Take `⟨ho, hle⟩` from `hlev a`. Conclude with `GlobalTheory.T.smoothRepIntegratedOperator_normalizedIndicator_fixed _ (μf a) _ ho ((isCompact_stabLoc _ _ _ a).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle) W _ hloc x (hxlev a)`. Rewrite using `[hPB, LinearMap.comp_apply, hBx]`. Rewrite `hB'` using `[LinearMap.comp_apply, hB'x]`. Conclude with `hB'`.

Introduce `h0`. Establish `hx` using `key T.S (Finset.Subset.refl _) P hP`. Substitute `h0` using the available equality. Conclude with `hx0 hx.symm`.
-/
theorem exists_idemFam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ v : T.S, e v = T.idem μf v) ∧ (∀ v, conv (μf v) (e v) (e v) = e v) ∧ (∀ k ∈ U.frame.iwahori, ∀ g, e U.u (k * g) = e U.u g) ∧ SphRest T U e ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → HasTypeVec T σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ≠ 0 := by
  intro D V T U hu μf hH h1 ν hν
  refine ⟨fam T U μf T.S, GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu T.S, fun v => fam_of_mem T U μf T.S v.2 v.2, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ T.S
    · rw [fam_of_mem T U μf T.S hv hv]
      let s := T.frame ⟨v, hv⟩
      have hk : IsOpen (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) := by
        rw [show (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) = (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram s.emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
          Set.ext s.red_eq_one_iff]
        exact (isOpen_stabLocOne V.gram s.emb (frameLat V) s.cm).preimage continuous_subtype_val
      exact conv_typeIdem (μf v) (isOpen_stabLoc _ _ _ v) (isCompact_stabLoc _ _ _ v) s.red_surjective hk _ (T.irred _)
    · rw [fam_of_not T U μf T.S (fun h => hv h.1)]
      obtain ⟨ho, hle⟩ := GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu v
      exact GlobalTheory.T.groupConvolution_normalizedIndicator_self _ (μf v) _ ho ((isCompact_stabLoc _ _ _ v).of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ ho) hle)
  · intro k hk g
    rw [fam_of_not T U μf T.S (fun h => hu h.1), levelFam_u]
    simp only [normInd, Pi.smul_apply]
    congr 1
    by_cases hg : g ∈ U.frame.iwahori
    · rw [indicator_of_mem (show k * g ∈ (U.frame.iwahori : Set _) from mul_mem hk hg), indicator_of_mem (show g ∈ (U.frame.iwahori : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g ∉ (U.frame.iwahori : Set _) from fun h => hg ((Subgroup.mul_mem_cancel_left _ hk).1 h)),
        indicator_of_notMem (show g ∉ (U.frame.iwahori : Set _) from hg)]
  · intro v hv hvu k hk k' hk' g
    rw [fam_of_not T U μf T.S (fun h => hv h.1), levelFam_of_notMem T U hv hvu]
    simp only [normInd, Pi.smul_apply]
    congr 1
    have : k * g * k' ∈ Kv V v ↔ g ∈ Kv V v := by
      rw [Subgroup.mul_mem_cancel_right _ hk', Subgroup.mul_mem_cancel_left _ hk]
    by_cases hg : g ∈ Kv V v
    · rw [indicator_of_mem (show k * g * k' ∈ (Kv V v : Set _) from this.2 hg), indicator_of_mem (show g ∈ (Kv V v : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g * k' ∉ (Kv V v : Set _) from fun h => hg (this.1 h)),
        indicator_of_notMem (show g ∉ (Kv V v : Set _) from hg)]
  · intro W _ _ σ hσ hT P hP
    rw [HasTypeVec] at hT
    obtain ⟨x, hx0, hxK, hxS⟩ := hT

    have hxker : ∀ v : T.S, ∀ k ∈ kerSub T v, σ (locFin V v k) x = x := by
      intro v
      have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
          GlobalTheory.PRep.fixed (σ.comp (locFin V v)) (kerSub T v) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨φ, hφ, z, rfl⟩ ⟨_, ⟨k, hk1, rfl⟩⟩
        have := hφ k z
        rw [MonoidHom.mem_ker.1 hk1, map_one] at this
        simpa using this.symm
      intro k hk
      simpa using hle (hxS v) ⟨k, hk⟩
    have hxlev : ∀ v, ∀ k ∈ levelFam T U v, σ (locFin V v k) x = x := by
      intro v k hk
      by_cases hvu : v = U.u
      · subst hvu
        rw [levelFam_u] at hk
        exact hxK _ hu k (U.frame.iwahori_le hk)
      · by_cases hv : v ∈ T.S
        · rw [levelFam_of_mem T U hu ⟨v, hv⟩] at hk
          exact hxker ⟨v, hv⟩ k hk
        · rw [levelFam_of_notMem T U hv hvu] at hk
          exact hxK v hv k hk
    have hlev := GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu
    have key : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), A ⊆ T.S → ∀ P,
        GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A)) P → P x = x := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro _ P hP
        have e : fam T U μf ∅ = fun v => normInd (μf v) (levelFam T U v : Set _) :=
          funext fun v => fam_of_not T U μf ∅ (fun h => Finset.notMem_empty v h.2)
        rw [e] at hP
        refine GlobalTheory.T.integratedOperator_normalizedIndicatorProd_fixed D V μf hH h1 ν hν (levelFam T U) (fun v => (hlev v).1) (fun v => (hlev v).2) ?_ W σ x
          (GlobalTheory.T.fixed_of_forall_localSubgroup_fixed_finiteAdelic D V W σ hσ (levelFam T U) (fun v => (hlev v).2) x hxlev) P hP
        filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u] with v hv hvu
        exact levelFam_of_notMem T U hv hvu
      | insert a A ha ih =>
        intro hsub P hP
        have haS : a ∈ T.S := hsub (Finset.mem_insert_self a A)
        obtain ⟨H, K, -, -, -, hHB⟩ := GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V a μf hH h1 ν hν W σ hσ (fam T U μf A)
          (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A)
        have hloc := isSmooth_comp_locFin hσ a
        have hfin := (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A).1
        have hfin' := (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu (insert a A)).1
        have hg : fam T U μf (insert a A) a = T.idem μf ⟨a, haS⟩ := fam_of_mem T U μf _ haS (Finset.mem_insert_self _ _)
        have e1 : Function.update (fam T U μf A) a (fam T U μf (insert a A) a) = fam T U μf (insert a A) := by
          funext v
          by_cases hva : v = a
          · subst hva
            rw [Function.update_self]
          · rw [Function.update_of_ne hva]
            by_cases hv : v ∈ T.S ∧ v ∈ A
            · rw [fam_of_mem T U μf _ hv.1 hv.2, fam_of_mem T U μf _ hv.1 (Finset.mem_insert_of_mem hv.2)]
            · rw [fam_of_not T U μf _ hv, fam_of_not T U μf _ (fun h => hv ⟨h.1, (Finset.mem_insert.1 h.2).resolve_left hva⟩)]
        have h2 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf (insert a A)))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a)) := by
          have := hHB _ (hfin' a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin' a).1, (hfin' a).2⟩)
          rwa [e1] at this
        have hPB := hP.unique h2
        have h3 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a)) := by
          have := hHB _ (hfin a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin a).1, (hfin a).2⟩)
          rwa [Function.update_eq_self] at this
        have hB' := ih (fun v hv => hsub (Finset.mem_insert_of_mem hv)) _ h3
        have hBx : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a) x = x :=
          hg ▸ GlobalTheory.T.typeIdempotentOperator_fix_span_images D V T μf hH W σ hσ ⟨a, haS⟩ x (hxS ⟨a, haS⟩)
        have hB'x : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a) x = x := by
          rw [fam_of_not T U μf A (fun h => ha h.2)]
          obtain ⟨ho, hle⟩ := hlev a
          exact GlobalTheory.T.smoothRepIntegratedOperator_normalizedIndicator_fixed _ (μf a) _ ho ((isCompact_stabLoc _ _ _ a).of_isClosed_subset
            (Subgroup.isClosed_of_isOpen _ ho) hle) W _ hloc x (hxlev a)
        rw [hPB, LinearMap.comp_apply, hBx]
        rw [LinearMap.comp_apply, hB'x] at hB'
        exact hB'
    intro h0
    have hx := key T.S (Finset.Subset.refl _) P hP
    subst h0
    exact hx0 hx.symm

end GlobalTheory.TrIdem
