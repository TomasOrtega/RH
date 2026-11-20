import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElementsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitClassRealizedByLatticeIsometryStatement

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

open scoped Pointwise

noncomputable section

namespace GlobalTheory.TrEll

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]`. Conclude with `mul_comm _ _`.
-/
theorem torPt_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : HR k (star' P) (one₁ P)) : a * b = b * a := by
  apply Subtype.ext; apply Units.ext; ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact mul_comm _ _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE r P J hJ L _`. Establish `hsep : P.1.Separable` using `P.2.2.1.separable`. Apply the tactic sequence `filter_upwards [GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry F E σ hE r P J hJ L, eventually_conj_of_charpoly_eq hE hJ L hsep] with v hu hc`. Take `⟨φ₁, h₁, hγ₁, hT₁⟩` from `hu`. Establish `hcp : ∀ (x : plusUnits P (Fv F v)) φ (h : IsIsom P (Fv F v) J x.1.1 φ), (matHom _ σ J (gam h)).1.charpoly = P.1.map (inclR (Fv F v))` using `fun x φ h => (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hE r r P J hJ (Fv F v) x φ h).1`.

Establish `hcpc : ∀ g y : GLoc σ J v, (matHom _ σ J (y⁻¹ * g * y)).1.charpoly = (matHom _ σ J g).1.charpoly` using `fun g y => by`. Rewrite using `[map_mul, map_mul, map_inv, charpoly_conj_GL]`. Establish `hcls : ∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1`. Introduce and unpack `γ q ⟨x, φ, h, rfl, rfl⟩ ⟨g, hg⟩`. Take `⟨k, hk, hkg⟩` from `hc _ hg _ hγ₁ (by rw [hcpc]; exact hcp x φ h) (hcp 1 φ₁ h₁)`.

Conclude with `(GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.1 (isConj_iff.2 ⟨(g * k)⁻¹, by rw [← hkg]; group⟩)`. Use `⟨⟨1, φ₁, rfl, h₁⟩, hcls, ?_, ?_⟩` and prove the remaining obligations. Introduce `x φ h hγ t`. Take `⟨k, hk, hkg⟩` from `hc _ hγ _ hγ₁ (hcp x φ h) (hcp 1 φ₁ h₁)`. Establish `ht` using `(GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.2.1 k⁻¹ (by rw [inv_inv, hkg]) t`.

Rewrite using `[← hT₁ t, ht, inv_inv, Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]`. Introduce `μ dt hμ hdt hμK hdtK q`. Establish `hK` using `isOpen_stabLoc σ J L v`. Establish `hKc` using `isCompact_stabLoc σ J L v`. Use `⟨fun hq => ?_, fun hq => ?_⟩` and prove the remaining obligations.

Establish `hcont : Continuous (unitLoc σ J L v)` using `(IsClopen.continuous_indicator ⟨Subgroup.isClosed_of_isOpen _ hK, hK⟩ continuous_const)`. Establish `hcs : HasCompactSupport (unitLoc σ J L v)` using `HasCompactSupport.intro hKc fun y hy => indicator_of_notMem hy _`. Establish `h1` using `((GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hE r r P J hJ).1 v μ dt (unitLoc σ J L v) hμ hdt hcont hcs).2 1 φ₁ h₁`. Establish `hqe : (⟨QuotientGroup.mk 1, 1, φ₁, rfl, h₁⟩ : XSet P (Fv F v) J) = q` using `Subtype.ext (by rw [hq]; rfl)`. Rewrite `h1` using `[hqe]`.

Take `⟨e, he1, he2⟩` from `GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hE r r P J hJ (Fv F v) 1 φ₁ h₁`. Rewrite `h1` using `[he2]`. Use `haveI := hμ`. Use `haveI := hdt`. Use `haveI : (dt.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map dt e`.

Establish `hcomm : ∀ a b : cent (gam h₁), a * b = b * a` using `fun a b => by`. Apply `e.symm.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`. Conclude with `torPt_mul_comm P (Fv F v) (e.symm a) (e.symm b)`. Use `haveI : (dt.map e).IsMulRightInvariant := ⟨fun g => by`.

Establish `: (fun x : cent (gam h₁) => x * g) = (fun x => g * x)` using `funext fun x => hcomm x g`. Rewrite using `[this]`. Conclude with `map_mul_left_eq_self _ g⟩`. Establish `hset : conjFn (gam h₁) (unitLoc σ J L v) = ((cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))).indicator 1`. Use function extensionality and compare the values at `y`.

Establish `hmem : y⁻¹ * gam h₁ * y ∈ stabLoc σ J L v ↔ y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))`. Use `⟨fun hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, hk, hkg⟩` from `hc _ hy _ hγ₁ (by rw [hcpc]; exact hcp 1 φ₁ h₁) (hcp 1 φ₁ h₁)`. Use `⟨y * k, mem_cent.2 ?_, k⁻¹, inv_mem hk, by group⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨t, ht, k, hk, rfl⟩`. Establish `: (t * k)⁻¹ * gam h₁ * (t * k) = k⁻¹ * (t⁻¹ * (gam h₁ * t)) * k` using `by group`. Rewrite using `[this, ← mem_cent.1 ht, inv_mul_cancel_left]`. Conclude with `mul_mem (mul_mem (inv_mem hk) hγ₁) hk`. Distinguish the cases in `hy : y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))`.

Rewrite using `[Set.indicator_of_mem hy]`. Conclude with `Set.indicator_of_mem (hmem.2 hy) _`. Rewrite using `[Set.indicator_of_notMem hy]`. Conclude with `Set.indicator_of_notMem (mt hmem.1 hy) _`. Establish `h2` using `hasQuotInt_indicator_mul (dt := dt.map e) (dh := μ) (isClosed_cent (gam h₁)) hK hKc`.

Rewrite `h1` using `[HasOrbInt, hset]`. Rewrite using `[← h1.2, h2.2]`. Establish `hpre : e ⁻¹' ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) = (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v : Set (Tor P (Fv F v)))`. Use extensionality with `t`. Simplify using `[Subgroup.mem_subgroupOf, he1, hT₁]`.

Establish `hm : (dt.map e) ((stabLoc σ J L v).subgroupOf (cent (gam h₁))) = 1`. Rewrite using `[Measure.map_apply (show Measurable e from e.continuous.measurable) (show MeasurableSet ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) from (hK.preimage continuous_subtype_val).measurableSet), hpre, hdtK]`. Simplify using `[Measure.real, hμK, hm]`. Establish `hrep` using `q.2.choose_spec.choose_spec`. Establish `h0 : conjFn (gam hrep.2) (unitLoc σ J L v) = 0`.

Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y⁻¹ * gam hrep.2 * y ∈ stabLoc σ J L v`. Conclude with `absurd (hcls _ _ ⟨_, _, hrep.2, hrep.1, rfl⟩ ⟨y, hy⟩) hq`. Conclude with `Set.indicator_of_notMem hy _`. Rewrite using `[orbCls, orbInt, h0]`.

Simplify using `[quotInt, descend]`.
-/
theorem eventually_unitLoc_orbCls : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Cls P (Fv F v)) ∈ XSet P (Fv F v) J ∧ (∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1) ∧ (∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h ∈ stabLoc σ J L v → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) ∧ ∀ (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))), μ.IsHaarMeasure → dt.IsHaarMeasure → μ (stabLoc σ J L v) = 1 → dt (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) = 1 → ∀ q : XSet P (Fv F v) J, (q.1 = 1 → orbCls μ dt (unitLoc σ J L v) q = 1) ∧ (q.1 ≠ 1 → orbCls μ dt (unitLoc σ J L v) q = 0) := by
  intro F E _ _ _ _ _ σ hE r P J hJ L _
  have hsep : P.1.Separable := P.2.2.1.separable
  filter_upwards [GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry F E σ hE r P J hJ L, eventually_conj_of_charpoly_eq hE hJ L hsep] with v hu hc
  obtain ⟨φ₁, h₁, hγ₁, hT₁⟩ := hu
  have hcp : ∀ (x : plusUnits P (Fv F v)) φ (h : IsIsom P (Fv F v) J x.1.1 φ),
      (matHom _ σ J (gam h)).1.charpoly = P.1.map (inclR (Fv F v)) :=
    fun x φ h => (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hE r r P J hJ (Fv F v) x φ h).1
  have hcpc : ∀ g y : GLoc σ J v,
      (matHom _ σ J (y⁻¹ * g * y)).1.charpoly = (matHom _ σ J g).1.charpoly := fun g y => by
    rw [map_mul, map_mul, map_inv, charpoly_conj_GL]
  have hcls : ∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1 := by
    rintro γ q ⟨x, φ, h, rfl, rfl⟩ ⟨g, hg⟩
    obtain ⟨k, hk, hkg⟩ := hc _ hg _ hγ₁ (by rw [hcpc]; exact hcp x φ h) (hcp 1 φ₁ h₁)
    exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.1
      (isConj_iff.2 ⟨(g * k)⁻¹, by rw [← hkg]; group⟩)
  refine ⟨⟨1, φ₁, rfl, h₁⟩, hcls, ?_, ?_⟩
  · intro x φ h hγ t
    obtain ⟨k, hk, hkg⟩ := hc _ hγ _ hγ₁ (hcp x φ h) (hcp 1 φ₁ h₁)
    have ht := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.2.1 k⁻¹ (by rw [inv_inv, hkg]) t
    rw [← hT₁ t, ht, inv_inv, Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  · intro μ dt hμ hdt hμK hdtK q
    have hK := isOpen_stabLoc σ J L v
    have hKc := isCompact_stabLoc σ J L v
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · have hcont : Continuous (unitLoc σ J L v) :=
        (IsClopen.continuous_indicator ⟨Subgroup.isClosed_of_isOpen _ hK, hK⟩ continuous_const)
      have hcs : HasCompactSupport (unitLoc σ J L v) :=
        HasCompactSupport.intro hKc fun y hy => indicator_of_notMem hy _
      have h1 := ((GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hE r r P J hJ).1 v μ dt (unitLoc σ J L v) hμ hdt hcont hcs).2 1 φ₁ h₁
      have hqe : (⟨QuotientGroup.mk 1, 1, φ₁, rfl, h₁⟩ : XSet P (Fv F v) J) = q := Subtype.ext (by rw [hq]; rfl)
      rw [hqe] at h1
      obtain ⟨e, he1, he2⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hE r r P J hJ (Fv F v) 1 φ₁ h₁
      rw [he2] at h1
      haveI := hμ
      haveI := hdt
      haveI : (dt.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map dt e
      have hcomm : ∀ a b : cent (gam h₁), a * b = b * a := fun a b => by
        apply e.symm.injective
        rw [map_mul, map_mul]
        exact torPt_mul_comm P (Fv F v) (e.symm a) (e.symm b)
      haveI : (dt.map e).IsMulRightInvariant := ⟨fun g => by
        have : (fun x : cent (gam h₁) => x * g) = (fun x => g * x) := funext fun x => hcomm x g
        rw [this]; exact map_mul_left_eq_self _ g⟩
      have hset : conjFn (gam h₁) (unitLoc σ J L v) =
          ((cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))).indicator 1 := by
        funext y
        have hmem : y⁻¹ * gam h₁ * y ∈ stabLoc σ J L v ↔
            y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)) := by
          refine ⟨fun hy => ?_, ?_⟩
          · obtain ⟨k, hk, hkg⟩ := hc _ hy _ hγ₁ (by rw [hcpc]; exact hcp 1 φ₁ h₁) (hcp 1 φ₁ h₁)
            refine ⟨y * k, mem_cent.2 ?_, k⁻¹, inv_mem hk, by group⟩
            calc y * k * gam h₁ = y * k * (k⁻¹ * (y⁻¹ * gam h₁ * y) * k) := by rw [hkg]
              _ = gam h₁ * (y * k) := by group
          · rintro ⟨t, ht, k, hk, rfl⟩
            have : (t * k)⁻¹ * gam h₁ * (t * k) = k⁻¹ * (t⁻¹ * (gam h₁ * t)) * k := by group
            rw [this, ← mem_cent.1 ht, inv_mul_cancel_left]
            exact mul_mem (mul_mem (inv_mem hk) hγ₁) hk
        by_cases hy : y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))
        · rw [Set.indicator_of_mem hy]
          exact Set.indicator_of_mem (hmem.2 hy) _
        · rw [Set.indicator_of_notMem hy]
          exact Set.indicator_of_notMem (mt hmem.1 hy) _
      have h2 := hasQuotInt_indicator_mul (dt := dt.map e) (dh := μ) (isClosed_cent (gam h₁)) hK hKc
      rw [HasOrbInt, hset] at h1
      rw [← h1.2, h2.2]
      have hpre : e ⁻¹' ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) =
          (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v : Set (Tor P (Fv F v))) := by
        ext t
        simp [Subgroup.mem_subgroupOf, he1, hT₁]
      have hm : (dt.map e) ((stabLoc σ J L v).subgroupOf (cent (gam h₁))) = 1 := by
        rw [Measure.map_apply (show Measurable e from e.continuous.measurable) (show MeasurableSet ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) from
          (hK.preimage continuous_subtype_val).measurableSet), hpre, hdtK]
      simp [Measure.real, hμK, hm]
    · have hrep := q.2.choose_spec.choose_spec
      have h0 : conjFn (gam hrep.2) (unitLoc σ J L v) = 0 := by
        funext y
        by_cases hy : y⁻¹ * gam hrep.2 * y ∈ stabLoc σ J L v
        · exact absurd (hcls _ _ ⟨_, _, hrep.2, hrep.1, rfl⟩ ⟨y, hy⟩) hq
        · exact Set.indicator_of_notMem hy _
      rw [orbCls, orbInt, h0]
      simp [quotInt, descend]
