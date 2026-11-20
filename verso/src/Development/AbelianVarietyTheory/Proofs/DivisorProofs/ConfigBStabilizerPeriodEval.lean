import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerNormalizedHaarRestricted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtUnitArchOfMemIdelesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitAtUnitArch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentActionFiniteSetSchwartzInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionRestrictedProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorFixesIntegralIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationInfinitePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVacuumFixedByStabilizerStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.ConeEulerGen

open GlobalTheory.TruncFix (truncU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Take `⟨hTG, hLC, hSC, hT2⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc`. Use `haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)`. Use `haveI : ∀ v : Pl F, CompactSpace (KAt K (evFin F v)) := fun v => isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)`.

Use `haveI : ∀ v : Pl F, BorelSpace (KAt K (evFin F v)) := fun v => inferInstance`. Use `haveI : ∀ v : Pl F, SecondCountableTopology (KAt K (evFin F v)) := fun v => inferInstance`. Use `haveI : ∀ v : Pl F, IsTopologicalGroup (KAt K (evFin F v)) := fun v => inferInstance`. Use `haveI : ∀ v : Pl F, T2Space (KAt K (evFin F v)) := fun v => inferInstance`. Use `haveI : ∀ v : Pl F, LocallyCompactSpace (KAt K (evFin F v)) := fun v => (isCompact_KAt hKc _).isClosed.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace (KAt K (evI F)) := (isCompact_KAt hKc _).isClosed.locallyCompactSpace`. Use `haveI : LocallyCompactSpace K := hKc.isClosed.locallyCompactSpace`. Take `⟨h1, h2⟩` from `continuous_components F E σ n X.J`. Establish `hs` using `SuppOne.comp_of_supp F E σ n X`. Take `⟨c, hc⟩` from `integral_of_components (ι := S) (B := fun v => KAt K (evFin F v.1)) μK μKi (fun v => μKv v.1) (CompIntegral.archK hK) ((h2.comp continuous_subtype_val).subtype_mk _) (fun v => CompIntegral.atK hK v.1) (fun v => ((h1 v.1).comp continuous_subtype_val).subtype_mk _) (fun a => ⟨a.1, …`.

Use `⟨c, fun a b => ?_⟩` and prove the remaining obligations. Use `hc (fun k => a k.1) (fun v k => b v.1 k.1)` as an intermediate fact. Rewrite `this` using `[Finset.prod_coe_sort S fun v => ∫ k, b v k.1 ∂μKv v]`. Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[mul_one, ← Finset.prod_coe_sort S]`. Both sides reduce to the same expression.
-/
theorem integral_stab {B : Base F E} {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K)
    (hKc : IsCompact (K : Set (UA σ X.J))) (μK : Measure K) [μK.IsHaarMeasure]
    (μKi : Measure (KAt K (evI F))) [μKi.IsHaarMeasure] (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v)))
    [∀ v, (μKv v).IsHaarMeasure] (S : Finset (Pl F)) :
    ∃ c : ℂ, ∀ (a : UA σ X.J → ℂ) (b : Pl F → UA σ X.J → ℂ),
      ∫ k, a (compArch σ X.J k.1) * ∏ v ∈ S, b v (compAt σ X.J v k.1) ∂μK =
        c * ((∫ k, a k.1 ∂μKi) * ∏ v ∈ S, ∫ k, b v k.1 ∂μKv v) := by
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : ∀ v : Pl F, CompactSpace (KAt K (evFin F v)) := fun v => isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : ∀ v : Pl F, BorelSpace (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, SecondCountableTopology (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, IsTopologicalGroup (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, T2Space (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, LocallyCompactSpace (KAt K (evFin F v)) := fun v =>
    (isCompact_KAt hKc _).isClosed.locallyCompactSpace
  haveI : LocallyCompactSpace (KAt K (evI F)) := (isCompact_KAt hKc _).isClosed.locallyCompactSpace
  haveI : LocallyCompactSpace K := hKc.isClosed.locallyCompactSpace
  obtain ⟨h1, h2⟩ := continuous_components F E σ n X.J
  have hs := SuppOne.comp_of_supp F E σ n X
  obtain ⟨c, hc⟩ := integral_of_components (ι := S) (B := fun v => KAt K (evFin F v.1)) μK μKi (fun v => μKv v.1)
    (CompIntegral.archK hK) ((h2.comp continuous_subtype_val).subtype_mk _)
    (fun v => CompIntegral.atK hK v.1) (fun v => ((h1 v.1).comp continuous_subtype_val).subtype_mk _)
    (fun a => ⟨a.1, a.2.1⟩) (continuous_subtype_val.subtype_mk _)
    (fun v b => ⟨b.1, b.2.1⟩) (fun v => continuous_subtype_val.subtype_mk _)
    (fun a => Subtype.ext ((hs a.1).2 a.2.2).1) (fun v b => Subtype.ext ((hs b.1).1 v.1 b.2.2).2.1)
    (fun v a => Subtype.ext (((hs a.1).2 a.2.2).2 v.1)) (fun v b => Subtype.ext ((hs b.1).1 v.1 b.2.2).1)
    (fun v w b hw => Subtype.ext (((hs b.1).1 w.1 b.2.2).2.2 v.1 fun e => hw (Subtype.ext e.symm)))
    (fun _ => 1) (fun _ _ => rfl) (fun _ _ _ => rfl)
  refine ⟨c, fun a b => ?_⟩
  have := hc (fun k => a k.1) (fun v k => b v.1 k.1)
  rw [Finset.prod_coe_sort S fun v => ∫ k, b v k.1 ∂μKv v] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [mul_one, ← Finset.prod_coe_sort S]
  rfl

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Use `haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`. Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`. Use `haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`.

Use `haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩`. Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evI F)`. Use `haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).1`.

Use `haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.1`. Use `haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.1`. Use `haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.2.1`. Use `haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.2.2`. Take `⟨h1, h2⟩` from `continuous_unitAt_unitArch F E`.

Establish `hs` using `unitAt_unitArch_of_mem_idelesAt F E`. Take `⟨c, hc⟩` from `integral_of_components (ι := S) (B := fun v => idelesAt E (evFin F v.1)) μ μi (fun v => μv v.1) ((unitArch F E).codRestrict _ unitArch_mem) (h2.subtype_mk _) (fun v => (unitAt E v.1).codRestrict _ (unitAt_mem v.1)) (fun v => (h1 v.1).subtype_mk _) (fun a => a.1) continuous_subtyp …`. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[if_pos hv, if_pos hv]`. Rewrite using `[map_mul, ((hs b.1).1 w.1 b.2).2.2 v (fun e => hv (e ▸ w.2)), one_mul])`.

Use `⟨c, fun a b => ?_⟩` and prove the remaining obligations. Use `hc (fun k => a k.1) (fun v k => b v.1 k.1)` as an intermediate fact. Rewrite `this` using `[Finset.prod_coe_sort S fun v => ∫ k, b v k.1 ∂μv v]`. Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[← Finset.prod_coe_sort S]`. Both sides reduce to the same expression.
-/
theorem integral_ideles (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure]
    (μi : Measure (idelesAt E (evI F))) [μi.IsHaarMeasure] (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v)))
    [∀ v, (μv v).IsHaarMeasure] (S : Finset (Pl F)) (r : Pl F → (AE F E)ˣ → ℂ) :
    ∃ c : ℂ, ∀ (a : (AE F E)ˣ → ℂ) (b : Pl F → (AE F E)ˣ → ℂ),
      ∫ l, a (unitArch F E l) * (∏ v ∈ S, b v (unitAt E v l)) * ∏ᶠ v, (if v ∈ S then 1 else r v (unitAt E v l)) ∂μ =
        c * ((∫ l, a l.1 ∂μi) * ∏ v ∈ S, ∫ l, b v l.1 ∂μv v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).1
  haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.1
  haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.1
  haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.2.1
  haveI := fun v : Pl F => (idelesAt_facts E (evFin F v)).2.2.2.2
  obtain ⟨h1, h2⟩ := continuous_unitAt_unitArch F E
  have hs := unitAt_unitArch_of_mem_idelesAt F E
  obtain ⟨c, hc⟩ := integral_of_components (ι := S) (B := fun v => idelesAt E (evFin F v.1)) μ μi (fun v => μv v.1)
    ((unitArch F E).codRestrict _ unitArch_mem) (h2.subtype_mk _)
    (fun v => (unitAt E v.1).codRestrict _ (unitAt_mem v.1)) (fun v => (h1 v.1).subtype_mk _)
    (fun a => a.1) continuous_subtype_val (fun v b => b.1) (fun v => continuous_subtype_val)
    (fun a => Subtype.ext ((hs a.1).2 a.2).1) (fun v b => Subtype.ext ((hs b.1).1 v.1 b.2).2.1)
    (fun v a => Subtype.ext (((hs a.1).2 a.2).2 v.1)) (fun v b => Subtype.ext ((hs b.1).1 v.1 b.2).1)
    (fun v w b hw => Subtype.ext (((hs b.1).1 w.1 b.2).2.2 v.1 fun e => hw (Subtype.ext e.symm)))
    (fun l => ∏ᶠ v, (if v ∈ S then 1 else r v (unitAt E v l)))
    (fun a x => finprod_congr fun v => by rw [map_mul, ((hs a.1).2 a.2).2 v, one_mul])
    (fun w b x => finprod_congr fun v => by
      by_cases hv : v ∈ S
      · rw [if_pos hv, if_pos hv]
      · rw [map_mul, ((hs b.1).1 w.1 b.2).2.2 v (fun e => hv (e ▸ w.2)), one_mul])
  refine ⟨c, fun a b => ?_⟩
  have := hc (fun k => a k.1) (fun v k => b v.1 k.1)
  rw [Finset.prod_coe_sort S fun v => ∫ k, b v k.1 ∂μv v] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [← Finset.prod_coe_sort S]
  rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.StabHaar.mat_mul, ← map_inv, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]`.
-/
theorem mat_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    mat ((compArch σ J k)⁻¹ * k) = eInf F • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - eInf F) • mat k := by
  rw [GlobalTheory.StabHaar.mat_mul, ← map_inv, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]

/- English proof (translation)
Introduce `u hu`. Establish `h : u * eInf F = u`. Establish `h` using `partInf_of_at (M := AF F) hu`. Rewrite `h` using `[partInf, smul_eq_mul]`. Rewrite using `[mul_comm]`.

Conclude with `h`. Rewrite using `[mat_archRest, smul_sub, smul_add, smul_smul, smul_smul, h, mul_sub, mul_one, h, sub_self, zero_smul, add_zero, sub_self]`.
-/
theorem archRest_triv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    ∀ u : AF F, At (evI F) u → u • (mat ((compArch σ J k)⁻¹ * k) - 1) = 0 := by
  intro u hu
  have h : u * eInf F = u := by
    have h := partInf_of_at (M := AF F) hu
    rw [partInf, smul_eq_mul] at h
    rw [mul_comm]; exact h
  rw [mat_archRest, smul_sub, smul_add, smul_smul, smul_smul, h, mul_sub, mul_one, h, sub_self, zero_smul, add_zero,
    sub_self]

/- English proof (translation)
Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Use `show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem {v}) (mat ((compArch σ J k)⁻¹ * k)) = mat (compAt σ J v k)`. Rewrite using `[GlobalTheory.TruncFix.idem_singleton, GlobalTheory.TruncFix.truncMat, mat_archRest, mat_compAt]`. Establish `h1 : GlobalTheory.LatVac.liftV v 1 * eInf F = 0`. Establish `h` using `at_partFin (M := AF F) v (1 : AF F) (eInf F) (map_zero (evalV F v))`.

Rewrite `h` using `[partFin, smul_eq_mul, smul_eq_mul, mul_one]`. Rewrite using `[mul_comm]`. Conclude with `h`. Establish `h2 : GlobalTheory.LatVac.liftV v 1 * (1 - eInf F) = GlobalTheory.LatVac.liftV v 1` using `by rw [mul_sub, mul_one, h1, sub_zero]`. Rewrite using `[smul_sub, smul_add, smul_smul, smul_smul, h1, h2, zero_smul, zero_add, show eFin v = GlobalTheory.LatVac.liftV v 1 from rfl, sub_smul, one_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem truncU_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) (v : Pl F) :
    truncU {v} ((compArch σ J k)⁻¹ * k) = compAt σ J v k := by
  refine Subtype.ext (Units.ext ?_)
  show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem {v}) (mat ((compArch σ J k)⁻¹ * k)) = mat (compAt σ J v k)
  rw [GlobalTheory.TruncFix.idem_singleton, GlobalTheory.TruncFix.truncMat, mat_archRest, mat_compAt]
  have h1 : GlobalTheory.LatVac.liftV v 1 * eInf F = 0 := by
    have h := at_partFin (M := AF F) v (1 : AF F) (eInf F) (map_zero (evalV F v))
    rw [partFin, smul_eq_mul, smul_eq_mul, mul_one] at h
    rw [mul_comm]; exact h
  have h2 : GlobalTheory.LatVac.liftV v 1 * (1 - eInf F) = GlobalTheory.LatVac.liftV v 1 := by rw [mul_sub, mul_one, h1, sub_zero]
  rw [smul_sub, smul_add, smul_smul, smul_smul, h1, h2, zero_smul, zero_add, show eFin v = GlobalTheory.LatVac.liftV v 1 from rfl,
    sub_smul, one_smul]
  abel

/- English proof (translation)
Establish `hM` using `hP.good`. Establish `hvac : (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) = fun v => if v ∈ S then locOp v (om (compAt σ X.J v k, 1)) (φ v) else M.vac v`. Use function extensionality and compare the values at `v`. Use `split_ifs with hv`. Both sides reduce to the same expression.

Rewrite using `[hS v hv]`. Conclude with `locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)`. Use `set k' := (compArch σ X.J k)⁻¹ * k with hk'`. Establish `hsplit : (k, (1 : UA σ W.J)) = (compArch σ X.J k, 1) * (k', 1)`. Rewrite using `[Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]`.

Establish `h1 : om (k', 1) (pure f φ) = pure f (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v))`. Use `GlobalTheory.TruncFixOm.om_archtriv B M _ _ om _ _ _ _ hA hP k' (archRest_triv X.J k) S f φ hSB hS (fun v hv => by rw [hk', truncU_archRest]; exact hfix v hv)` as an intermediate fact. Simplify `this` using `only [hk', truncU_archRest]`. Establish `h1mem : (1 : UA σ W.J) ∈ UAt σ W (evI F)` using `fun u _ => by show u • (mat (1 : UA σ W.J) - 1) = 0`. Rewrite using `[GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]`.

Take `⟨Aop, hAop⟩` from `GlobalTheory.ArchLocalAct.exists_op_of_UAt hP.base.std hP.weil (compArch σ X.J k, 1) (compArch_mem k) h1mem`. Establish `hcof : ∀ᶠ v in Filter.cofinite, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v` using `Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by`. Assume the negation of the conclusion as `h`. Conclude with `hv ((congrFun hvac v).trans (if_neg h)))`. Rewrite using `[hsplit, map_mul, Module.End.mul_apply, h1, GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ n d X W M om hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof, locOpInf_eq (hAop f), hvac]`.
-/
theorem om_pure (hA : ActsEx) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (k : UA σ X.J)
    (S : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB _) (hS : ∀ v ∉ S, φ v = M.vac v)
    (hfix : ∀ v ∉ S, Acts (evFin F v) (om (compAt σ X.J v k, 1)) (M.vac v) (M.vac v)) :
    om (k, 1) (pure f φ) = pure (locOpInf (om (compArch σ X.J k, 1)) f)
      (fun v => if v ∈ S then locOp v (om (compAt σ X.J v k, 1)) (φ v) else M.vac v) := by
  have hM := hP.good
  have hvac : (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) =
      fun v => if v ∈ S then locOp v (om (compAt σ X.J v k, 1)) (φ v) else M.vac v := by
    funext v
    split_ifs with hv
    · rfl
    · rw [hS v hv]
      exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)
  set k' := (compArch σ X.J k)⁻¹ * k with hk'
  have hsplit : (k, (1 : UA σ W.J)) = (compArch σ X.J k, 1) * (k', 1) := by
    rw [Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]
  have h1 : om (k', 1) (pure f φ) = pure f (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) := by
    have := GlobalTheory.TruncFixOm.om_archtriv B M _ _ om _ _ _ _ hA hP k' (archRest_triv X.J k) S f φ hSB hS
      (fun v hv => by rw [hk', truncU_archRest]; exact hfix v hv)
    simpa only [hk', truncU_archRest] using this
  have h1mem : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  obtain ⟨Aop, hAop⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hP.base.std hP.weil (compArch σ X.J k, 1)
    (compArch_mem k) h1mem
  have hcof : ∀ᶠ v in Filter.cofinite, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v :=
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv ((congrFun hvac v).trans (if_neg h)))
  rw [hsplit, map_mul, Module.End.mul_apply, h1,
    GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ n d X W M om hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof,
    locOpInf_eq (hAop f), hvac]

/- English proof (translation)
Unfold `partInf`. Rewrite using `[smul_shiftB, smul_shiftB]`. Use `congr 2`. Use `show eInf F • (eInf F • (l : AE F E) + (1 - eInf F) • 1) = eInf F • (l : AE F E)`. Rewrite using `[smul_add, smul_smul, smul_smul, eInf_idem, idem_mul_one_sub eInf_idem, zero_smul, add_zero]`.
-/
theorem partInf_shiftB_unitArch {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ) :
    partInf F (shiftB σ H H' (unitArch F E l)) = partInf F (shiftB σ H H' l) := by
  unfold partInf
  rw [smul_shiftB, smul_shiftB]
  congr 2
  show eInf F • (eInf F • (l : AE F E) + (1 - eInf F) • 1) = eInf F • (l : AE F E)
  rw [smul_add, smul_smul, smul_smul, eInf_idem, idem_mul_one_sub eInf_idem, zero_smul, add_zero]

/- English proof (translation)
Unfold `partFin`. Rewrite using `[smul_shiftB, smul_shiftB]`. Use `congr 2`. Use `show eFin v • (eFin v • (l : AE F E) + (1 - eFin v) • 1) = eFin v • (l : AE F E)`. Rewrite using `[smul_add, smul_smul, smul_smul, eFin_idem, idem_mul_one_sub (eFin_idem v), zero_smul, add_zero]`.
-/
theorem partFin_shiftB_unitAt {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (l : (AE F E)ˣ) :
    partFin v (shiftB σ H H' (unitAt E v l)) = partFin v (shiftB σ H H' l) := by
  unfold partFin
  rw [smul_shiftB, smul_shiftB]
  congr 2
  show eFin v • (eFin v • (l : AE F E) + (1 - eFin v) • 1) = eFin v • (l : AE F E)
  rw [smul_add, smul_smul, smul_smul, eFin_idem, idem_mul_one_sub (eFin_idem v), zero_smul, add_zero]

/- English proof (translation)
Apply the tactic sequence `have e : ∀ v, (if v ∈ S then p v else q v) = (if v ∈ S then p v else 1) * (if v ∈ S then 1 else q v) := fun v => by split_ifs <;> simp`. Establish `h1 : (Function.mulSupport fun v => if v ∈ S then p v else 1) ⊆ S` using `fun v hv => by`. Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`. Establish `h2 : (Function.mulSupport fun v => if v ∈ S then 1 else q v).Finite` using `(eventually_cofinite.1 hq).subset fun v hv h => hv (by simp [h])`.

Rewrite using `[finprod_congr e, finprod_mul_distrib (S.finite_toSet.subset h1) h2, finprod_eq_prod_of_mulSupport_subset _ h1]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun v hv => if_pos hv`.
-/
theorem finprod_ite_eq {ι : Type} (S : Finset ι) (p q : ι → ℂ) (hq : ∀ᶠ v in cofinite, q v = 1) :
    ∏ᶠ v, (if v ∈ S then p v else q v) = (∏ v ∈ S, p v) * ∏ᶠ v, (if v ∈ S then 1 else q v) := by
  have e : ∀ v, (if v ∈ S then p v else q v) = (if v ∈ S then p v else 1) * (if v ∈ S then 1 else q v) := fun v => by
    split_ifs <;> simp
  have h1 : (Function.mulSupport fun v => if v ∈ S then p v else 1) ⊆ S := fun v hv => by
    by_contra h
    exact hv (if_neg h)
  have h2 : (Function.mulSupport fun v => if v ∈ S then 1 else q v).Finite :=
    (eventually_cofinite.1 hq).subset fun v hv h => hv (by simp [h])
  rw [finprod_congr e, finprod_mul_distrib (S.finite_toSet.subset h1) h2, finprod_eq_prod_of_mulSupport_subset _ h1]
  congr 1
  exact Finset.prod_congr rfl fun v hv => if_pos hv

/- English proof (translation)
Establish `hM` using `hT.geo.hM'`. Establish `hfix : ∀ v ∉ S, Acts (evFin F v) (om' (compAt σ G.V'.J v k, 1)) (G.M'.vac v) (G.M'.vac v)` using `fun v hv => (GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer B G X om om' hT v fun h => hv (hXS h)).2 K hK _ (mem_KAt.2 ⟨(StabComp.comp_mem_of_isStab F E σ B _ _ K hK k hk).1 v, compAt_mem v k⟩)`. Establish `hA` using `om_pure (GlobalTheory.ThK.LocalOps.actsEx hP) (Inhab.pairV' hT) k S f φ hSB hS hfix`. Use `set φ₁ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ := fun v => if v ∈ S then locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v) else G.M'.vac v with hφ₁`. Use `set f₁ := locOpInf (om' (compArch σ G.V'.J k, 1)) f with hf₁`.

Establish `hSB₁ : ∀ v, φ₁ v ∈ SB _` using `fun v => by`. Simplify using `only [hφ₁]`. Use `split_ifs`. Use `exacts [locOp_mem _ _ _, (hM.vac v).1]`. Establish `hnS : ∀ᶠ v in cofinite, v ∉ S` using `S.eventually_cofinite_notMem`.

Establish `hcof₁ : ∀ᶠ v in cofinite, φ₁ v = G.M'.vac v` using `hnS.mono fun v hv => if_neg hv`. Establish `hstd₁` using `(hcof₁.and hM.std).mono fun v hv => hv.1.trans hv.2`. Establish `hB` using `GlobalTheory.T.weil_action_restricted_product G.M' B.ψ hT.base.std (shiftB σ H H' l) f₁ φ₁ hSB₁ hstd₁`. Use `set φ₂ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ := fun v => locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (φ₁ v) with hφ₂`. Use `set f₂ := locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' l))) f₁ with hf₂`.

Establish `hcof₂ : ∀ᶠ v in cofinite, φ₂ v = G.M'.vac v` using `by filter_upwards [GlobalTheory.T.local_operator_fixes_integral_indicator G.M' B.ψ hT.base.std (shiftB σ H H' l), hstd₁, hM.std] with v h1 h2 h3`. Simplify using `only [hφ₂]`. Rewrite using `[h2, h1, h3]`. Establish `hν : Continuous X.ν` using `hT.chars.heckeα.1.div' hT.chars.heckeβ.1`. Take `⟨hfinC, hCh⟩` from `ConeEulerChr.chr_abs_eq_finprod X.ν hν l z`.

Use `set C : Pl F → ℂ := fun v => (X.ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z with hCdef`. Use `set J : Pl F → ℂ := fun v => if compFin F E v (unitAt E v l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then (1 : ℂ) else 0 with hJdef`. Use `set V : Pl F → ℂ := fun v => G₁.M'.vac v (fun i => evFin F v (y i)) with hVdef`. Establish `hoff : ∀ v ∉ S, ev v (φ₂ v) = if compFin F E v (unitAt E v l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then G₁.M'.vac v else 0` using `fun v hv => by`. Simplify using `only [hφ₂, hφ₁, if_neg hv]`.

Rewrite using `[← partFin_shiftB_unitAt]`. Conclude with `UnrSuppB.evShift_vac B G G₁ H H' hT.base hT.geo hG₁ hC e' he' ei ev hei hev hpure v _ (unitAt_mem v l)`. Establish `hJ1 : ∀ᶠ v in cofinite, J v = 1` using `by filter_upwards [hnS, hcof₂, hG₁.hM'.std] with v h1 h2 h3`. Use `if_pos (by_contra fun h => ?_)` and prove the remaining obligations. Establish `h4` using `hoff v h1`.

Rewrite `h4` using `[if_neg h, h2, (hev v).1, h3]`. Establish `h5` using `congrFun h4 0`. Rewrite `h5` using `[Set.indicator_of_mem (by intro i; exact zero_mem _)]`. Conclude with `one_ne_zero h5`. Establish `hC1 : ∀ᶠ v in cofinite, C v = 1` using `eventually_cofinite.2 hfinC`.

Establish `hV1 : ∀ᶠ v in cofinite, V v = 1` using `eventually_cofinite.2 (GlobalTheory.PureFactor.mulSupport_finite _ hG₁.hM'.std y)`. Establish `hstdE : ∀ᶠ v in cofinite, ev v (φ₂ v) = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1` using `(hcof₂.and hG₁.hM'.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]`. Establish `hfinA` using `GlobalTheory.PureFactor.mulSupport_finite (fun v => ev v (φ₂ v)) hstdE y`. Establish `hR : ∀ v, ev v (φ₂ v) (fun i => evFin F v (y i)) * C v = if v ∈ S then coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) (compAt σ G.V'.J v k) (unitAt E v l) (fun i => evFin F v (y i)) else J v * C v * V v`. Introduce `v`.

Use `split_ifs with hv`. Rewrite using `[coneFinInt, partFin_shiftB_unitAt]`. Simplify using `only [hφ₂, hφ₁, if_pos hv, hCdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hoff v hv]`.

Simplify using `only [hJdef, hVdef]`. Use `split_ifs`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hI : coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f (compArch σ G.V'.J k) (unitArch F E l) (fun i => evI F (y i)) = ei f₂ (fun i => evI F (y i)) * ((X.ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z)`.

Rewrite using `[coneInfInt_apply, partInf_shiftB_unitArch]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsp : ∏ᶠ v, (if v ∈ S then 1 else J v * C v * V v) = (∏ᶠ v, (if v ∈ S then 1 else J v * C v)) * ∏ᶠ v, (if v ∈ S then 1 else V v)`. Rewrite using `[← finprod_mul_distrib]`. Apply the tactic sequence `exact finprod_congr fun v => by split_ifs <;> simp`.

Conclude with `(eventually_cofinite.1 (hJ1.and hC1)).subset fun v hv h => hv (by simp [h.1, h.2])`. Conclude with `(eventually_cofinite.1 hV1).subset fun v hv h => hv (by simp [h])`. Establish `hprod` using `(finprod_mul_distrib hfinA hfinC).symm.trans ((finprod_congr hR).trans (finprod_ite_eq S _ _ (((hJ1.and hC1).and hV1).mono fun v h => by rw [h.1.1, h.1.2, h.2]; simp)))`. Rewrite `hprod` using `[hsp]`. Rewrite using `[coneInt, hA, hB, hpure f₂ φ₂ (fun v => locOp_mem _ _ _) hcof₂, hI, mul_assoc _ (X.ν l : ℂ), hCh]`.

Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]`. Take the linear combination `(ei f₂ (fun i => evI F (y i)) * ((X.ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z)) * hprod`.
-/
theorem integrand_eq (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {K : Subgroup (UA σ G.V'.J)} (hK : IsStab B K) {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') (hG₁ : G₁.IsGood B)
    {ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b))}
    {ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ}
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ)
    (S : Finset (Pl F)) (hSB : ∀ v, φ v ∈ SB _) (hS : ∀ v ∉ S, φ v = G.M'.vac v) (hXS : X.T ⊆ S) (z : ℕ)
    {k : UA σ G.V'.J} (hk : k ∈ K) (l : (AE F E)ˣ) (y : Fin b × Fin (a + b) → AF F) :
    coneInt B G.M' om' e' (shiftB σ H H') X.ν z (pure f φ) k l y =
      (coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f (compArch σ G.V'.J k) (unitArch F E l) (fun i => evI F (y i)) *
        (∏ v ∈ S, coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) (compAt σ G.V'.J v k) (unitAt E v l)
          (fun i => evFin F v (y i))) *
        ∏ᶠ v, (if v ∈ S then 1 else
          (if compFin F E v (unitAt E v l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then (1 : ℂ) else 0) *
            ((X.ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z))) *
      ∏ᶠ v, (if v ∈ S then 1 else G₁.M'.vac v (fun i => evFin F v (y i))) := by
  have hM := hT.geo.hM'
  have hfix : ∀ v ∉ S, Acts (evFin F v) (om' (compAt σ G.V'.J v k, 1)) (G.M'.vac v) (G.M'.vac v) := fun v hv =>
    (GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer B G X om om' hT v fun h => hv (hXS h)).2 K hK _
      (mem_KAt.2 ⟨(StabComp.comp_mem_of_isStab F E σ B _ _ K hK k hk).1 v, compAt_mem v k⟩)
  have hA := om_pure (GlobalTheory.ThK.LocalOps.actsEx hP) (Inhab.pairV' hT) k S f φ hSB hS hfix
  set φ₁ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ :=
    fun v => if v ∈ S then locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v) else G.M'.vac v with hφ₁
  set f₁ := locOpInf (om' (compArch σ G.V'.J k, 1)) f with hf₁
  have hSB₁ : ∀ v, φ₁ v ∈ SB _ := fun v => by
    simp only [hφ₁]
    split_ifs
    exacts [locOp_mem _ _ _, (hM.vac v).1]
  have hnS : ∀ᶠ v in cofinite, v ∉ S := S.eventually_cofinite_notMem
  have hcof₁ : ∀ᶠ v in cofinite, φ₁ v = G.M'.vac v := hnS.mono fun v hv => if_neg hv
  have hstd₁ := (hcof₁.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hB := GlobalTheory.T.weil_action_restricted_product G.M' B.ψ hT.base.std (shiftB σ H H' l) f₁ φ₁ hSB₁ hstd₁
  set φ₂ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ :=
    fun v => locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (φ₁ v) with hφ₂
  set f₂ := locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' l))) f₁ with hf₂
  have hcof₂ : ∀ᶠ v in cofinite, φ₂ v = G.M'.vac v := by
    filter_upwards [GlobalTheory.T.local_operator_fixes_integral_indicator G.M' B.ψ hT.base.std (shiftB σ H H' l), hstd₁, hM.std] with v h1 h2 h3
    simp only [hφ₂]
    rw [h2, h1, h3]
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  obtain ⟨hfinC, hCh⟩ := ConeEulerChr.chr_abs_eq_finprod X.ν hν l z
  set C : Pl F → ℂ := fun v => (X.ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z with hCdef
  set J : Pl F → ℂ := fun v =>
    if compFin F E v (unitAt E v l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then (1 : ℂ) else 0 with hJdef
  set V : Pl F → ℂ := fun v => G₁.M'.vac v (fun i => evFin F v (y i)) with hVdef
  have hoff : ∀ v ∉ S, ev v (φ₂ v) =
      if compFin F E v (unitAt E v l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then G₁.M'.vac v else 0 := fun v hv => by
    simp only [hφ₂, hφ₁, if_neg hv]
    rw [← partFin_shiftB_unitAt]
    exact UnrSuppB.evShift_vac B G G₁ H H' hT.base hT.geo hG₁ hC e' he' ei ev hei hev hpure v _ (unitAt_mem v l)
  have hJ1 : ∀ᶠ v in cofinite, J v = 1 := by
    filter_upwards [hnS, hcof₂, hG₁.hM'.std] with v h1 h2 h3
    refine if_pos (by_contra fun h => ?_)
    have h4 := hoff v h1
    rw [if_neg h, h2, (hev v).1, h3] at h4
    have h5 := congrFun h4 0
    rw [Set.indicator_of_mem (by intro i; exact zero_mem _)] at h5
    exact one_ne_zero h5
  have hC1 : ∀ᶠ v in cofinite, C v = 1 := eventually_cofinite.2 hfinC
  have hV1 : ∀ᶠ v in cofinite, V v = 1 :=
    eventually_cofinite.2 (GlobalTheory.PureFactor.mulSupport_finite _ hG₁.hM'.std y)
  have hstdE : ∀ᶠ v in cofinite, ev v (φ₂ v) =
      Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hcof₂.and hG₁.hM'.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hfinA := GlobalTheory.PureFactor.mulSupport_finite (fun v => ev v (φ₂ v)) hstdE y
  have hR : ∀ v, ev v (φ₂ v) (fun i => evFin F v (y i)) * C v =
      if v ∈ S then coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) (compAt σ G.V'.J v k) (unitAt E v l)
        (fun i => evFin F v (y i)) else J v * C v * V v := by
    intro v
    split_ifs with hv
    · rw [coneFinInt, partFin_shiftB_unitAt]
      simp only [hφ₂, hφ₁, if_pos hv, hCdef]
      ring
    · rw [hoff v hv]
      simp only [hJdef, hVdef]
      split_ifs
      · ring
      · simp
  have hI : coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f (compArch σ G.V'.J k) (unitArch F E l)
      (fun i => evI F (y i)) =
      ei f₂ (fun i => evI F (y i)) * ((X.ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z) := by
    rw [coneInfInt_apply, partInf_shiftB_unitArch]
    ring
  have hsp : ∏ᶠ v, (if v ∈ S then 1 else J v * C v * V v) =
      (∏ᶠ v, (if v ∈ S then 1 else J v * C v)) * ∏ᶠ v, (if v ∈ S then 1 else V v) := by
    rw [← finprod_mul_distrib]
    · exact finprod_congr fun v => by split_ifs <;> simp
    · exact (eventually_cofinite.1 (hJ1.and hC1)).subset fun v hv h => hv (by simp [h.1, h.2])
    · exact (eventually_cofinite.1 hV1).subset fun v hv h => hv (by simp [h])
  have hprod := (finprod_mul_distrib hfinA hfinC).symm.trans ((finprod_congr hR).trans
    (finprod_ite_eq S _ _ (((hJ1.and hC1).and hV1).mono fun v h => by rw [h.1.1, h.1.2, h.2]; simp)))
  rw [hsp] at hprod
  rw [coneInt, hA, hB, hpure f₂ φ₂ (fun v => locOp_mem _ _ _) hcof₂, hI, mul_assoc _ (X.ν l : ℂ), hCh]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  linear_combination (ei f₂ (fun i => evI F (y i)) *
    ((X.ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z)) * hprod

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpure μK μ hμK hμ μKi μi hKi hμi μKv μv hKv hμv f φ S hSB hS hXS _`. Establish `hKc : IsCompact (K : Set (UA σ G.V'.J))`. Take `⟨K', -, -, hK', hc, -⟩` from `GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hT.base hT.geo.hV'`. Rewrite using `[show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]` and apply the resulting hypothesis. Use `haveI := hKi.1`.

Use `haveI := fun v => (hKv v).1`. Use `haveI := fun v => (hμv v).1`. Use `set z : ℕ := (a - (b + 2)) / 2 + 1`. Take `⟨cK, hcK⟩` from `integral_stab hK hKc μK μKi μKv S`. Take `⟨cI, hcI⟩` from `integral_ideles μ μi μv S fun v m => (if compFin F E v (m : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then (1 : ℂ) else 0) * ((X.ν m : ℂ) * ((absE F E m : ℝ) : ℂ) ^ z)`.

Use `⟨cK * cI, fun y => ?_⟩` and prove the remaining obligations. Use `set V : ℂ := ∏ᶠ v, (if v ∈ S then 1 else G₁.M'.vac v (fun i => evFin F v (y i))) with hV`. Use `set gI : UA σ G.V'.J → ℂ := fun k => ∫ l, coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f k l.1 (fun i => evI F (y i)) ∂μi with hgI`. Use `set g : Pl F → UA σ G.V'.J → ℂ := fun v k => ∫ l, coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) k l.1 (fun i => evFin F v (y i)) ∂μv v with hg`. Establish `hin : ∀ k : K, ∫ l, coneInt B G.M' om' e' (shiftB σ H H') X.ν z (pure f φ) k.1 l y ∂μ = (cI * V) * (gI (compArch σ G.V'.J k.1) * ∏ v ∈ S, g v (compAt σ G.V'.J v k.1))` using `fun k => by`.

Rewrite using `[integral_congr_ae (Eventually.of_forall fun l => integrand_eq hP hC he' hK hT hT₁.geo hei hev hpure f φ S hSB hS hXS z k.2 l y), integral_mul_const, hcI (fun l => coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f (compArch σ G.V'.J k.1) l (fun i => evI F (y i))) (fun v l => coneF …`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : ∏ᶠ v, (if v ∈ S then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν z (φ v) else G₁.M'.vac v) (fun i => evFin F v (y i)) = (∏ v ∈ S, ∫ k, g v k.1 ∂μKv v) * V`. Rewrite using `[hV, ← finprod_ite_eq S _ _ (eventually_cofinite.2 (GlobalTheory.PureFactor.mulSupport_finite _ hT₁.geo.hM'.std y))]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[cone_apply, integral_congr_ae (Eventually.of_forall hin), integral_const_mul, hcK, hfin]`. Express the relevant statement in the definitionally equal form `_ = cK * cI * ((∫ k, gI k.1 ∂μKi) * _)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cone_pure_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))),
    (∀ v, IsNormK K (evFin F v) (μKv v)) → (∀ v, IsNormE E v (μv v)) →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ)
      (S : Finset (Pl F)), (∀ v, φ v ∈ SB _) → (∀ v ∉ S, φ v = G.M'.vac v) → X.T ⊆ S → B.v₁ ∈ S →
    ∃ c : ℂ, ∀ y : Fin b × Fin (a + b) → AF F,
      cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) y =
        c * (coneInfFun B G.M' om' ei K μKi μi (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f (fun i => evI F (y i)) *
          ∏ᶠ v, (if v ∈ S then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ v)
            else G₁.M'.vac v) (fun i => evFin F v (y i))) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpure μK μ hμK hμ
    μKi μi hKi hμi μKv μv hKv hμv f φ S hSB hS hXS _
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', -, -, hK', hc, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hT.base hT.geo.hV'
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  haveI := hKi.1
  haveI := fun v => (hKv v).1
  haveI := fun v => (hμv v).1
  set z : ℕ := (a - (b + 2)) / 2 + 1
  obtain ⟨cK, hcK⟩ := integral_stab hK hKc μK μKi μKv S
  obtain ⟨cI, hcI⟩ := integral_ideles μ μi μv S fun v m =>
    (if compFin F E v (m : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then (1 : ℂ) else 0) *
      ((X.ν m : ℂ) * ((absE F E m : ℝ) : ℂ) ^ z)
  refine ⟨cK * cI, fun y => ?_⟩
  set V : ℂ := ∏ᶠ v, (if v ∈ S then 1 else G₁.M'.vac v (fun i => evFin F v (y i))) with hV
  set gI : UA σ G.V'.J → ℂ := fun k =>
    ∫ l, coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f k l.1 (fun i => evI F (y i)) ∂μi with hgI
  set g : Pl F → UA σ G.V'.J → ℂ := fun v k =>
    ∫ l, coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) k l.1 (fun i => evFin F v (y i)) ∂μv v with hg
  have hin : ∀ k : K, ∫ l, coneInt B G.M' om' e' (shiftB σ H H') X.ν z (pure f φ) k.1 l y ∂μ =
      (cI * V) * (gI (compArch σ G.V'.J k.1) * ∏ v ∈ S, g v (compAt σ G.V'.J v k.1)) := fun k => by
    rw [integral_congr_ae (Eventually.of_forall fun l =>
      integrand_eq hP hC he' hK hT hT₁.geo hei hev hpure f φ S hSB hS hXS z k.2 l y), integral_mul_const,
      hcI (fun l => coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f (compArch σ G.V'.J k.1) l (fun i => evI F (y i)))
        (fun v l => coneFinInt B G.M' om' v (ev v) (shiftB σ H H') X.ν z (φ v) (compAt σ G.V'.J v k.1) l
          (fun i => evFin F v (y i)))]
    ring
  have hfin : ∏ᶠ v, (if v ∈ S then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν z (φ v)
      else G₁.M'.vac v) (fun i => evFin F v (y i)) = (∏ v ∈ S, ∫ k, g v k.1 ∂μKv v) * V := by
    rw [hV, ← finprod_ite_eq S _ _ (eventually_cofinite.2 (GlobalTheory.PureFactor.mulSupport_finite _ hT₁.geo.hM'.std y))]
    refine finprod_congr fun v => ?_
    split_ifs <;> rfl
  rw [cone_apply, integral_congr_ae (Eventually.of_forall hin), integral_const_mul, hcK, hfin]
  change _ = cK * cI * ((∫ k, gI k.1 ∂μKi) * _)
  ring

end GlobalTheory.ConeEulerGen

end
