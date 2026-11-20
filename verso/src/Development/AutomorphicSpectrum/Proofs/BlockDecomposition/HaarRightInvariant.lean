import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.MapMulRightEqOfMemCompactSubgroup
import GroundTheory.AutomorphicForms.AdelicGLn

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
open scoped RestrictedProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicUnimod

open GroundTheory.Automorphic

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `h1` using `Measure.map_right_mul_eq_modularCharacterFun_smul μ z`. Rewrite `h1` using `[h]`. Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `h2` using `congrArg (fun m : Measure G => m C) h1`. Establish `hne : μ C ≠ 0` using `(Measure.measure_pos_of_mem_nhds μ hC1).ne'`.

Establish `hnt : μ C ≠ ⊤` using `hC.measure_lt_top.ne`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h2`. Establish `h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)`. Conclude with `h3` after adjusting the coercions.
-/
theorem modularCharacter_eq_one_of_map (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (h : μ.map (fun x => x * z) = μ) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
  rw [h] at h1
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m C) h1
  have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
  simp only [Measure.coe_nnreal_smul_apply] at h2
  have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

/- English proof (translation)
Use `modularCharacter_eq_one_of_map μ ?_` and prove the remaining obligations. Rewrite using `[show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm, Measure.IsMulLeftInvariant.map_mul_left_eq_self]`.
-/
theorem modularCharacter_eq_one_of_central (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (hz : ∀ h, z * h = h * z) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  refine modularCharacter_eq_one_of_map μ ?_
  rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
    Measure.IsMulLeftInvariant.map_mul_left_eq_self]

/- English proof (translation)
The claim follows from `modularCharacter_eq_one_of_map μ (GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup G μ inferInstance inferInstance K hK k hk)`.
-/
theorem modularCharacter_eq_one_of_compact (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : (Measure.modularCharacter k : ℝ≥0) = 1 :=
  modularCharacter_eq_one_of_map μ
    (GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup G μ inferInstance inferInstance K hK k hk)

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h g, one_smul]`.
-/
theorem isMulRightInvariant_of_modularCharacter (μ : Measure G) [μ.IsHaarMeasure]
    (h : ∀ g : G, (Measure.modularCharacter g : ℝ≥0) = 1) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h g, one_smul]

end General

section Products

/- English proof (translation)
Establish `key : ∀ (S : Finset ι) (x : ∀ i, H i), (∀ i, i ∉ S → x i = 1) → Δ x = 1`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `x hx`.

Rewrite using `[show x = 1 from funext fun i => hx i (by simp), map_one]`. Consider the case `insert a S _ ih`. Introduce `x hx`. Establish `e : x = (x * (Pi.mulSingle a (x a))⁻¹) * Pi.mulSingle a (x a)` using `by simp`. Rewrite using `[e, map_mul, h, mul_one]`.

Use `ih _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia, inv_one, mul_one]`.

Conclude with `hx i (by simp [hia, hi])`. Conclude with `key Finset.univ x (by simp)`.
-/
theorem pi_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (Δ : (∀ i, H i) →* ℝ≥0) (h : ∀ i (x : H i), Δ (Pi.mulSingle i x) = 1) (x : ∀ i, H i) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : ∀ i, H i), (∀ i, i ∉ S → x i = 1) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      rw [show x = 1 from funext fun i => hx i (by simp), map_one]
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (Pi.mulSingle a (x a))⁻¹) * Pi.mulSingle a (x a) := by simp
      rw [e, map_mul, h, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp
      · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  exact key Finset.univ x (by simp)

/- English proof (translation)
Establish `key : ∀ (S : Finset ι) (x : Πʳ i, [H i, A i]), (∀ i, i ∉ S → x i ∈ A i) → Δ x = 1`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact fun x hx => h2 x fun i => hx i (by simp)`. Consider the case `insert a S _ ih`.

Introduce `x hx`. Establish `e : x = (x * (RestrictedProduct.mulSingle A a (x a))⁻¹) * RestrictedProduct.mulSingle A a (x a)` using `by simp`. Rewrite using `[e, map_mul, h1, mul_one]`. Use `ih _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hia : i = a`.

Substitute `hia` using the available equality. Simplify using `[RestrictedProduct.mulSingle_eq_same, one_mem]`. Simplify using `only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mulSingle_eq_of_ne A _ hia, inv_one, mul_one]`. Conclude with `hx i (by simp [hia, hi])`. Establish `hfin : {i | x i ∉ A i}.Finite` using `x.2`.

Conclude with `key hfin.toFinset x fun i hi => by simpa using hi`.
-/
theorem restricted_eq_one {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    {A : ∀ i, Subgroup (H i)} (Δ : (Πʳ i, [H i, A i]) →* ℝ≥0)
    (h1 : ∀ i (x : H i), Δ (RestrictedProduct.mulSingle A i x) = 1)
    (h2 : ∀ x : Πʳ i, [H i, A i], (∀ i, x i ∈ A i) → Δ x = 1) (x : Πʳ i, [H i, A i]) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : Πʳ i, [H i, A i]), (∀ i, i ∉ S → x i ∈ A i) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun x hx => h2 x fun i => hx i (by simp)
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (RestrictedProduct.mulSingle A a (x a))⁻¹) *
          RestrictedProduct.mulSingle A a (x a) := by simp
      rw [e, map_mul, h1, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp [RestrictedProduct.mulSingle_eq_same, one_mem]
      · simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
          RestrictedProduct.mulSingle_eq_of_ne A _ hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  have hfin : {i | x i ∉ A i}.Finite := x.2
  exact key hfin.toFinset x fun i hi => by simpa using hi

def singleHom {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (A : ∀ i, Subgroup (H i)) (i : ι) : H i →* Πʳ i, [H i, A i] where
  toFun := RestrictedProduct.mulSingle A i
  map_one' := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]
  map_mul' x y := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]

end Products

section Adelic

variable (E : Type) [Field E] [NumberField E] (N : ℕ)

abbrev PInf : Type := ∀ w : InfinitePlace E, GL (Fin N) w.Completion

abbrev AInt (v : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin N) (v.adicCompletion E)) :=
  GLnLocal.integralGL (v.adicCompletion E) N

abbrev PFin : Type := Πʳ v : HeightOneSpectrum (𝓞 E), [GL (Fin N) (v.adicCompletion E), AInt E N v]

open GroundTheory.Automorphic.AdelicGLn in

def finInc : FiniteAdelicGL E N →* GA E N :=
  ((prodEquiv E N).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)

open GroundTheory.Automorphic.AdelicGLn in
/- English proof (translation)
The claim follows from `(prodEquiv E N).symm.continuous.comp (continuous_const.prodMk continuous_id)`.
-/
theorem continuous_finInc : Continuous (finInc E N) :=
  (prodEquiv E N).symm.continuous.comp (continuous_const.prodMk continuous_id)

open GroundTheory.Automorphic.AdelicGLn in

/- English proof (translation)
Use `isMulRightInvariant_of_modularCharacter μ fun g => ?_` and prove the remaining obligations. Set `e` to `restrictedProductEquiv E N`. Set `Δ : PInf E N × PFin E N →* ℝ≥0` to `(Measure.modularCharacter : GA E N →* ℝ≥0).comp e.symm.toMulEquiv.toMonoidHom`. Establish `hΔ : ∀ z, Δ z = Measure.modularCharacter (e.symm z)` using `fun _ => rfl`. Establish `hcen : ∀ z, (∀ h, z * h = h * z) → Δ z = 1` using `fun z hz => by`.

Rewrite using `[hΔ]`. Use `modularCharacter_eq_one_of_central μ fun h => ?_` and prove the remaining obligations. Use `hz (e h)` as an intermediate fact. Apply `e.injective` to reduce the goal to its premises. Simplify `this` using `[map_mul]`.

Establish `hinf : ∀ (w : InfinitePlace E) (x : GL (Fin N) w.Completion), Δ (Pi.mulSingle w x, 1) = 1` using `fun w x => by`. Set `ι : GL (Fin N) w.Completion →* PInf E N × PFin E N` to `(MonoidHom.inl (PInf E N) (PFin E N)).comp (MonoidHom.mulSingle (fun w : InfinitePlace E => GL (Fin N) w.Completion) w)`. Use `GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x` and prove the remaining obligations. Use `Prod.ext (funext fun u => ?_) (by simp [ι])` and prove the remaining obligations. Distinguish the cases in `hu : u = w`.

Substitute `hu` using the available equality. Simplify `hc (h.1 u)` using `[ι]`. Simplify using `[ι, Pi.mulSingle_eq_of_ne hu]`. Establish `hfin : ∀ (v : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (v.adicCompletion E)), Δ (1, RestrictedProduct.mulSingle (AInt E N) v x) = 1` using `fun v x => by`. Set `ι : GL (Fin N) (v.adicCompletion E) →* PInf E N × PFin E N` to `(MonoidHom.inr (PInf E N) (PFin E N)).comp (singleHom (AInt E N) v)`.

Use `GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x` and prove the remaining obligations. Use `Prod.ext (by simp [ι]) ?_` and prove the remaining obligations. Use extensionality with `u : 1`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Simplify `hc (h.2 u)` using `[ι, singleHom, RestrictedProduct.mulSingle_eq_same]`. Simplify using `[ι, singleHom, RestrictedProduct.mulSingle_eq_of_ne _ _ hu]`. Establish `hint : ∀ b : PFin E N, (∀ v, b v ∈ AInt E N v) → Δ (1, b) = 1` using `fun b hb => by`. Establish `hk : (finiteRestrictedEquiv E N).symm b ∈ integralFiniteGL E N` using `(mem_integralFiniteGL_iff_forall E N).2 (by simpa using hb)`. Establish `hcomp : IsCompact (((integralFiniteGL E N).map (finInc E N) : Subgroup (GA E N)) : Set (GA E N))`.

Rewrite using `[Subgroup.coe_map]`. Conclude with `(isCompact_integralFiniteGL E N).image (continuous_finInc E N)`. Establish `he : e.symm (1, b) = finInc E N ((finiteRestrictedEquiv E N).symm b)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show 1 = infiniteEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).1`. Simplify using the standard rewrite rules. Use `show b = finiteRestrictedEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).2`. Simplify using the standard rewrite rules.

Rewrite using `[hΔ, he]`. Conclude with `modularCharacter_eq_one_of_compact μ _ hcomp (Subgroup.mem_map_of_mem _ hk)`. Establish `hall : ∀ z, Δ z = 1` using `fun z => by`. Establish `hz : z = (z.1, 1) * (1, z.2)` using `by simp`. Rewrite using `[hz, map_mul]`.

Establish `a1 : Δ (z.1, 1) = 1` using `pi_eq_one (Δ.comp (MonoidHom.inl (PInf E N) (PFin E N))) (fun w x => hinf w x) z.1`. Establish `a2 : Δ (1, z.2) = 1` using `restricted_eq_one (Δ.comp (MonoidHom.inr (PInf E N) (PFin E N))) (fun v x => hfin v x) (fun b hb => hint b hb) z.2`. Rewrite using `[a1, a2, one_mul]`. Use `hall (e g)` as an intermediate fact. Rewrite `this` using `[hΔ, ContinuousMulEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem isMulRightInvariant_GA (μ : Measure (GA E N)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_modularCharacter μ fun g => ?_
  let e := restrictedProductEquiv E N
  let Δ : PInf E N × PFin E N →* ℝ≥0 := (Measure.modularCharacter : GA E N →* ℝ≥0).comp e.symm.toMulEquiv.toMonoidHom
  have hΔ : ∀ z, Δ z = Measure.modularCharacter (e.symm z) := fun _ => rfl
  have hcen : ∀ z, (∀ h, z * h = h * z) → Δ z = 1 := fun z hz => by
    rw [hΔ]
    refine modularCharacter_eq_one_of_central μ fun h => ?_
    have := hz (e h)
    apply e.injective
    simpa [map_mul] using this
  have hinf : ∀ (w : InfinitePlace E) (x : GL (Fin N) w.Completion),
      Δ (Pi.mulSingle w x, 1) = 1 := fun w x => by
    let ι : GL (Fin N) w.Completion →* PInf E N × PFin E N :=
      (MonoidHom.inl (PInf E N) (PFin E N)).comp (MonoidHom.mulSingle (fun w : InfinitePlace E => GL (Fin N) w.Completion) w)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (funext fun u => ?_) (by simp [ι])
    by_cases hu : u = w
    · subst hu
      simpa [ι] using hc (h.1 u)
    · simp [ι, Pi.mulSingle_eq_of_ne hu]
  have hfin : ∀ (v : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (v.adicCompletion E)),
      Δ (1, RestrictedProduct.mulSingle (AInt E N) v x) = 1 := fun v x => by
    let ι : GL (Fin N) (v.adicCompletion E) →* PInf E N × PFin E N :=
      (MonoidHom.inr (PInf E N) (PFin E N)).comp (singleHom (AInt E N) v)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (by simp [ι]) ?_
    ext u : 1
    by_cases hu : u = v
    · subst hu
      simpa [ι, singleHom, RestrictedProduct.mulSingle_eq_same] using hc (h.2 u)
    · simp [ι, singleHom, RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
  have hint : ∀ b : PFin E N, (∀ v, b v ∈ AInt E N v) → Δ (1, b) = 1 := fun b hb => by
    have hk : (finiteRestrictedEquiv E N).symm b ∈ integralFiniteGL E N :=
      (mem_integralFiniteGL_iff_forall E N).2 (by simpa using hb)
    have hcomp : IsCompact (((integralFiniteGL E N).map (finInc E N) : Subgroup (GA E N)) : Set (GA E N)) := by
      rw [Subgroup.coe_map]
      exact (isCompact_integralFiniteGL E N).image (continuous_finInc E N)
    have he : e.symm (1, b) = finInc E N ((finiteRestrictedEquiv E N).symm b) := by
      apply e.injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · show 1 = infiniteEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).1
        simp
      · show b = finiteRestrictedEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).2
        simp
    rw [hΔ, he]
    exact modularCharacter_eq_one_of_compact μ _ hcomp (Subgroup.mem_map_of_mem _ hk)
  have hall : ∀ z, Δ z = 1 := fun z => by
    have hz : z = (z.1, 1) * (1, z.2) := by simp
    rw [hz, map_mul]
    have a1 : Δ (z.1, 1) = 1 :=
      pi_eq_one (Δ.comp (MonoidHom.inl (PInf E N) (PFin E N))) (fun w x => hinf w x) z.1
    have a2 : Δ (1, z.2) = 1 :=
      restricted_eq_one (Δ.comp (MonoidHom.inr (PInf E N) (PFin E N))) (fun v x => hfin v x) (fun b hb => hint b hb) z.2
    rw [a1, a2, one_mul]
  have := hall (e g)
  rwa [hΔ, ContinuousMulEquiv.symm_apply_apply] at this

end Adelic

/- English proof (translation)
Introduce `E _ _ _ N μ _` and use `isMulRightInvariant_GA E N μ`.
-/
theorem isMulRightInvariant_GA_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N μ _ => isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.AdelicUnimod
