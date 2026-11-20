import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section
namespace GlobalTheory.ThKCtFin

/- English proof (translation)
Take `⟨C, hC⟩` from `PIW.ClassFinD.idele_class_finite E`. Establish `hO : IsCompact ((PIW.ClassFinD.Ohat E).toSubmonoid : Set (FiniteAdeleRing (𝓞 E) E))` using `(GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1`. Use `haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))`. Establish `hK` using `Submonoid.units_isCompact hO`. Take `⟨D, -, hD⟩` from `hK.elim_nhds_subcover (fun d => {y | d⁻¹ * y ∈ U}) (fun d _ => (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by show d⁻¹ * d ∈ U`.

Rewrite using `[inv_mul_cancel]`. Conclude with `U.one_mem))`. Use `⟨Finset.image₂ (· * ·) C D, fun a => ?_⟩` and prove the remaining obligations. Take `⟨f, c, hc, e, he, he', rfl⟩` from `hC a`. Establish `heK : e ∈ ((PIW.ClassFinD.Ohat E).toSubmonoid.units : Set (FiniteAdeleRing (𝓞 E) E)ˣ)` using `⟨he, he'⟩`.

Take `⟨d, hd, hde⟩` from `Set.mem_iUnion₂.1 (hD heK)`. Use `⟨f, c * d, Finset.mem_image₂_of_mem hc hd, d⁻¹ * e, hde, ?_⟩` and prove the remaining obligations. Use `group`.
-/
theorem finiteIdele_classes (E : Type) [Field E] [NumberField E] (U : Subgroup (FiniteAdeleRing (𝓞 E) E)ˣ)
    (hU : IsOpen (U : Set (FiniteAdeleRing (𝓞 E) E)ˣ)) :
    ∃ C : Finset (FiniteAdeleRing (𝓞 E) E)ˣ, ∀ a : (FiniteAdeleRing (𝓞 E) E)ˣ, ∃ f : Eˣ, ∃ c ∈ C, ∃ u ∈ U,
      a = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E) : E →* FiniteAdeleRing (𝓞 E) E) f * c * u := by
  classical
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite E
  have hO : IsCompact ((PIW.ClassFinD.Ohat E).toSubmonoid : Set (FiniteAdeleRing (𝓞 E) E)) :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  have hK := Submonoid.units_isCompact hO
  obtain ⟨D, -, hD⟩ := hK.elim_nhds_subcover (fun d => {y | d⁻¹ * y ∈ U})
    (fun d _ => (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by
      show d⁻¹ * d ∈ U
      rw [inv_mul_cancel]; exact U.one_mem))
  refine ⟨Finset.image₂ (· * ·) C D, fun a => ?_⟩
  obtain ⟨f, c, hc, e, he, he', rfl⟩ := hC a
  have heK : e ∈ ((PIW.ClassFinD.Ohat E).toSubmonoid.units : Set (FiniteAdeleRing (𝓞 E) E)ˣ) := ⟨he, he'⟩
  obtain ⟨d, hd, hde⟩ := Set.mem_iUnion₂.1 (hD heK)
  refine ⟨f, c * d, Finset.mem_image₂_of_mem hc hd, d⁻¹ * e, hde, ?_⟩
  group

/- English proof (translation)
Introduce `F E _ _ _ _ _ U hU`. Use `letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)`. Use `letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)`. Take `⟨e, he, -, hec⟩` from `GlobalTheory.AdSplit.exists_adele_equiv F E`. Take `⟨ι, hι1, hι2, -⟩` from `GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E`.

Establish `hιc` using `GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2`. Establish `he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x` using `fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)`. Establish `he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x` using `fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)`. Set `Φ : AE F E ≃+* ((InfiniteAdeleRing F ⊗[F] E) × FiniteAdeleRing (𝓞 E) E)` to `e.trans (RingEquiv.prodCongr (RingEquiv.refl _) ι)`. Establish `hΦ : ∀ z, Φ z = ((e z).1, ι (e z).2)` using `fun z => rfl`.

Set `mf : FiniteAdeleRing (𝓞 E) E →* AE F E` to `Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inr _ _)`. Set `mi : (InfiniteAdeleRing F ⊗[F] E) →* AE F E` to `Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inl _ _)`. Establish `hmf : ∀ y, Φ (mf y) = (1, y)` using `fun y => Φ.apply_symm_apply _`. Establish `hmi : ∀ y, Φ (mi y) = (y, 1)` using `fun y => Φ.apply_symm_apply _`. Establish `hmfc : Continuous mf`.

Establish `: (mf : _ → _) = fun w => e.symm (1, ι.symm w)` using `rfl`. Rewrite using `[this]`. Conclude with `hec.comp (continuous_const.prodMk hιc)`. Establish `hsm : ∀ (a : AF F) (z : AE F E), Φ (a • z) = (a.1 ⊗ₜ[F] (1 : E), ι (a.2 ⊗ₜ[F] (1 : E))) * Φ z`. Introduce `a z`.

Rewrite using `[Algebra.smul_def, map_mul]`. Use `congr 1`. Rewrite using `[hΦ, ← he1, ← he2]`. Both sides reduce to the same expression. Take `⟨C, hC⟩` from `finiteIdele_classes E (U.comap (Units.map mf)) (hU.preimage (Continuous.units_map _ hmfc))`.

Use `⟨C.image (Units.map mf), fun t => ?_⟩` and prove the remaining obligations. Set `p1 : AE F E →* (InfiniteAdeleRing F ⊗[F] E)` to `(MonoidHom.fst _ _).comp Φ.toRingHom.toMonoidHom`. Set `p2 : AE F E →* FiniteAdeleRing (𝓞 E) E` to `(MonoidHom.snd _ _).comp Φ.toRingHom.toMonoidHom`. Take `⟨f, c, hc, u, hu, ht⟩` from `hC (Units.map p2 t)`. Use `set g : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom f with hg`.

Use `⟨f, Units.map mf c, Finset.mem_image_of_mem _ hc, Units.map mi (Units.map p1 (g⁻¹ * t)), ?_, Units.map mf u, hu, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `ha1 : a.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[hsm, map_sub, map_one, map_zero, Units.coe_map, hmi, ha1]`.

Apply the tactic sequence `ext <;> simp`. Introduce `a ha`. Establish `ha2 : a.2 = 0` using `ha`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[hsm, map_sub, map_one, map_zero, Units.coe_map, hmf, ha2]`.

Apply the tactic sequence `ext <;> simp`. Rewrite using `[← hg, mul_assoc, mul_assoc, ← inv_mul_eq_iff_eq_mul]`. Establish `hg2 : Units.map p2 g = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E) : E →* FiniteAdeleRing (𝓞 E) E) f`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ι (e ((1 : AF F) ⊗ₜ[F] (f : E))).2 = _`.

Rewrite using `[he2]`. Conclude with `hι1 f`. Establish `h2 : Units.map p2 (g⁻¹ * t) = c * u`. Rewrite using `[map_mul, map_inv, hg2, ht]`. Use `group`.

Establish `h2' : (Φ ((g⁻¹ * t : (AE F E)ˣ) : AE F E)).2 = (c : FiniteAdeleRing (𝓞 E) E) * u` using `congrArg Units.val h2`. Apply `Units.ext` to reduce the goal to its premises. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[Units.val_mul (Units.map mf c), Units.val_mul (Units.map mi _), map_mul, map_mul, Units.coe_map, Units.coe_map, Units.coe_map (f := mf), hmf, hmf, hmi]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Simplify using `only [Prod.fst_mul, one_mul, mul_one]`. Both sides reduce to the same expression. Simplify using `only [Prod.snd_mul, one_mul]`. Conclude with `h2'`.
-/
theorem idele_classes_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (U : Subgroup (AE F E)ˣ), IsOpen (U : Set (AE F E)ˣ) → ∃ C : Finset (AE F E)ˣ, ∀ t : (AE F E)ˣ, ∃ γ : Eˣ, ∃ c ∈ C, ∃ a ∈ idelesInf F E, ∃ u ∈ U, u ∈ idelesFin F E ∧ t = Units.map (inclR (F := F) (AF F)).toMonoidHom γ * c * a * u := by
  intro F E _ _ _ _ _ U hU
  classical
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AE F E ≃+* ((InfiniteAdeleRing F ⊗[F] E) × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr (RingEquiv.refl _) ι)
  have hΦ : ∀ z, Φ z = ((e z).1, ι (e z).2) := fun z => rfl
  let mf : FiniteAdeleRing (𝓞 E) E →* AE F E := Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inr _ _)
  let mi : (InfiniteAdeleRing F ⊗[F] E) →* AE F E := Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inl _ _)
  have hmf : ∀ y, Φ (mf y) = (1, y) := fun y => Φ.apply_symm_apply _
  have hmi : ∀ y, Φ (mi y) = (y, 1) := fun y => Φ.apply_symm_apply _
  have hmfc : Continuous mf := by
    have : (mf : _ → _) = fun w => e.symm (1, ι.symm w) := rfl
    rw [this]
    exact hec.comp (continuous_const.prodMk hιc)
  have hsm : ∀ (a : AF F) (z : AE F E), Φ (a • z) = (a.1 ⊗ₜ[F] (1 : E), ι (a.2 ⊗ₜ[F] (1 : E))) * Φ z := by
    intro a z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hΦ, ← he1, ← he2]
    rfl
  obtain ⟨C, hC⟩ := finiteIdele_classes E (U.comap (Units.map mf)) (hU.preimage (Continuous.units_map _ hmfc))
  refine ⟨C.image (Units.map mf), fun t => ?_⟩
  let p1 : AE F E →* (InfiniteAdeleRing F ⊗[F] E) := (MonoidHom.fst _ _).comp Φ.toRingHom.toMonoidHom
  let p2 : AE F E →* FiniteAdeleRing (𝓞 E) E := (MonoidHom.snd _ _).comp Φ.toRingHom.toMonoidHom
  obtain ⟨f, c, hc, u, hu, ht⟩ := hC (Units.map p2 t)
  set g : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom f with hg
  refine ⟨f, Units.map mf c, Finset.mem_image_of_mem _ hc, Units.map mi (Units.map p1 (g⁻¹ * t)), ?_,
    Units.map mf u, hu, ?_, ?_⟩
  · intro a ha
    have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
    apply Φ.injective
    rw [hsm, map_sub, map_one, map_zero, Units.coe_map, hmi, ha1]
    ext <;> simp
  · intro a ha
    have ha2 : a.2 = 0 := ha
    apply Φ.injective
    rw [hsm, map_sub, map_one, map_zero, Units.coe_map, hmf, ha2]
    ext <;> simp
  · rw [← hg, mul_assoc, mul_assoc, ← inv_mul_eq_iff_eq_mul]
    have hg2 : Units.map p2 g = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E) : E →* FiniteAdeleRing (𝓞 E) E) f := by
      apply Units.ext
      change ι (e ((1 : AF F) ⊗ₜ[F] (f : E))).2 = _
      rw [he2]
      exact hι1 f
    have h2 : Units.map p2 (g⁻¹ * t) = c * u := by
      rw [map_mul, map_inv, hg2, ht]; group
    have h2' : (Φ ((g⁻¹ * t : (AE F E)ˣ) : AE F E)).2 = (c : FiniteAdeleRing (𝓞 E) E) * u := congrArg Units.val h2
    apply Units.ext
    apply Φ.injective
    rw [Units.val_mul (Units.map mf c), Units.val_mul (Units.map mi _), map_mul, map_mul, Units.coe_map, Units.coe_map,
      Units.coe_map (f := mf), hmf, hmf, hmi]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, one_mul, mul_one]
      rfl
    · simp only [Prod.snd_mul, one_mul]
      exact h2'

end GlobalTheory.ThKCtFin
