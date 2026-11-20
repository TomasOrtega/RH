import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Valued RestrictedProduct Topology

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn resS oToS frGL intGL)

section LocalCompact

variable {F : Type} [Field F] [NumberField F]

def rlt_toInt (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* 𝒪[v.adicCompletion F] :=
  (algebraMap (𝓞 F) (v.adicCompletion F)).codRestrict 𝒪[v.adicCompletion F]
    (fun r => (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (Formalism.UG.P.levelaf_int_mem_v v r))

/- English proof (translation)
Establish `: Finite (𝓞 F ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Set `ψ : 𝓞 F →+* 𝓀[v.adicCompletion F]` to `(IsLocalRing.residue 𝒪[v.adicCompletion F]).comp (rlt_toInt v)`. Establish `hlt : ∀ r : 𝓞 F, r ∈ v.asIdeal → Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1`. Introduce `r hr`. Rewrite using `[Formalism.UG.P.csGlobApprox_vD]`.

Conclude with `(HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr`. Establish `hker : ∀ r ∈ v.asIdeal, ψ r = 0`. Introduce `r hr`. Use `show IsLocalRing.residue _ (rlt_toInt v r) = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`.

Conclude with `hlt r hr`. Establish `hsurj : Function.Surjective ψ`. Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨D, hD, hD0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`.

Take `⟨r, hr⟩` from `Formalism.UG.P.csGlobApprox_local v D hD0 x.1 x.2`. Use `⟨r, ?_⟩` and prove the remaining obligations. Use `show IsLocalRing.residue _ (rlt_toInt v r) = IsLocalRing.residue _ x`. Rewrite using `[eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Conclude with `lt_of_le_of_lt hr (hlt D hD)`.

Conclude with `Finite.of_surjective (Ideal.Quotient.lift v.asIdeal ψ hker) (Ideal.Quotient.lift_surjective_of_surjective _ hker hsurj)`.
-/
theorem rlt_finite_res (v : HeightOneSpectrum (𝓞 F)) : Finite 𝓀[v.adicCompletion F] := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let ψ : 𝓞 F →+* 𝓀[v.adicCompletion F] := (IsLocalRing.residue 𝒪[v.adicCompletion F]).comp (rlt_toInt v)
  have hlt : ∀ r : 𝓞 F, r ∈ v.asIdeal → Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
    intro r hr
    rw [Formalism.UG.P.csGlobApprox_vD]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
  have hker : ∀ r ∈ v.asIdeal, ψ r = 0 := by
    intro r hr
    show IsLocalRing.residue _ (rlt_toInt v r) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hlt r hr
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    obtain ⟨r, hr⟩ := Formalism.UG.P.csGlobApprox_local v D hD0 x.1 x.2
    refine ⟨r, ?_⟩
    show IsLocalRing.residue _ (rlt_toInt v r) = IsLocalRing.residue _ x
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact lt_of_le_of_lt hr (hlt D hD)
  exact Finite.of_surjective (Ideal.Quotient.lift v.asIdeal ψ hker) (Ideal.Quotient.lift_surjective_of_surjective _ hker hsurj)

/- English proof (translation)
Rewrite using `[Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]`. Use `⟨?_, ?_, rlt_finite_res v⟩` and prove the remaining obligations. Conclude with `(Valued.isClosed_integer (v.adicCompletion F)).isComplete.completeSpace_coe`. Conclude with `inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))`.
-/
theorem rlt_compact_int (v : HeightOneSpectrum (𝓞 F)) : CompactSpace 𝒪[v.adicCompletion F] := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, rlt_finite_res v⟩
  · exact (Valued.isClosed_integer (v.adicCompletion F)).isComplete.completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.2 (rlt_compact_int v)`.
-/
theorem rlt_isCompact_int (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.2 (rlt_compact_int v)

/- English proof (translation)
Use `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun v => Valued.isOpen_valuationSubring _)` as an intermediate fact. Conclude with `this`.
-/
theorem rlt_isOpen_intAd : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact this

/- English proof (translation)
Establish `: ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F)` using `fun v => rlt_compact_int v`. Establish `hemb` using `RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)`. Establish `h` using `isCompact_range hemb.continuous`. Establish `hset : (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨fun v => ⟨a v, ha v⟩, rfl⟩`. Introduce and unpack `⟨b, rfl⟩ v`. Conclude with `(b v).2`.

Rewrite using `[hset]`. Conclude with `h`.
-/
theorem rlt_isCompact_intAd : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := fun v => rlt_compact_int v
  have hemb := RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)
  have h := isCompact_range hemb.continuous
  have hset : (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) =
      Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨b, rfl⟩ v
      exact (b v).2
  rw [hset]
  exact h

end LocalCompact

section Tens

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

attribute [local instance] Algebra.TensorProduct.rightAlgebra

@[reducible] def rlt_top : TopologicalSpace 𝒜 := Formalism.BasicNotions.tensTopL (F := F) (E := E) 𝔸

attribute [local instance] rlt_top

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem rlt_isModTop : IsModuleTopology 𝔸 𝒜 := ⟨rfl⟩

attribute [local instance] rlt_isModTop

variable {F E}

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Use `show ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] b) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem rlt_smul_tmul (a : 𝔸) (e : E) (b : 𝔸) : a • (e ⊗ₜ[F] b : 𝒜) = e ⊗ₜ[F] (a * b) := by
  rw [Algebra.smul_def]
  show ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def rlt_comb {m : ℕ} (b : Fin m → 𝓞 E) : (Fin m → 𝔸) →ₗ[𝔸] 𝒜 :=
  Fintype.linearCombination 𝔸 (fun j => (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] (1 : 𝔸) : 𝒜))

/- English proof (translation)
Unfold `rlt_comb`. Rewrite using `[Fintype.linearCombination_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[rlt_smul_tmul, mul_one]`.
-/
theorem rlt_comb_apply {m : ℕ} (b : Fin m → 𝓞 E) (r : Fin m → 𝔸) :
    rlt_comb b r = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j := by
  unfold rlt_comb
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rlt_smul_tmul, mul_one]

/- English proof (translation)
Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Rewrite using `[rlt_comb_apply]`. Conclude with `sum_mem fun j _ => Formalism.UG.P.levelaf_tmul_mem _ (hr j (Set.mem_univ _))`.

Introduce `hs`. Take `⟨r, hr, rfl⟩` from `Formalism.UG.P.levelaf_decomp b hb hs`. Conclude with `⟨r, fun j _ => hr j, rlt_comb_apply b r⟩`.
-/
theorem rlt_image_comb {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤) :
    rlt_comb b '' (Set.pi Set.univ fun _ => (Formalism.UG.intAd F : Set 𝔸)) = (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [rlt_comb_apply]
    exact sum_mem fun j _ => Formalism.UG.P.levelaf_tmul_mem _ (hr j (Set.mem_univ _))
  · intro hs
    obtain ⟨r, hr, rfl⟩ := Formalism.UG.P.levelaf_decomp b hb hs
    exact ⟨r, fun j _ => hr j, rlt_comb_apply b r⟩

/- English proof (translation)
Introduce `x`. Take `⟨d, hd, hx⟩` from `Formalism.UG.P.levelaf_denom x`. Take `⟨r, -, hr⟩` from `(Set.ext_iff.1 (rlt_image_comb b hb) _).2 hx`. Establish `hd' : (algebraMap (𝓞 F) F d) ≠ 0`. Simplify using `using hd`.

Use `⟨(algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹) • r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hr, Algebra.smul_def]`. Use `show ((1 : E) ⊗ₜ[F] _) * (((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) 𝔸 d) * x) = x`. Rewrite using `[← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸, ← map_mul, inv_mul_cancel₀ hd', map_one]`. Conclude with `one_mul x`.
-/
theorem rlt_comb_surj {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤) :
    Function.Surjective (rlt_comb (F := F) b) := by
  intro x
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨r, -, hr⟩ := (Set.ext_iff.1 (rlt_image_comb b hb) _).2 hx
  have hd' : (algebraMap (𝓞 F) F d) ≠ 0 := by
    simpa using hd
  refine ⟨(algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹) • r, ?_⟩
  rw [map_smul, hr, Algebra.smul_def]
  show ((1 : E) ⊗ₜ[F] _) * (((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) 𝔸 d) * x) = x
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸, ← map_mul,
    inv_mul_cancel₀ hd', map_one]
  exact one_mul x

/- English proof (translation)
Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Conclude with `Module.Finite.of_surjective _ (rlt_comb_surj b hb)`.
-/
theorem rlt_finite : Module.Finite 𝔸 𝒜 := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  exact Module.Finite.of_surjective _ (rlt_comb_surj b hb)

/- English proof (translation)
The claim follows from `haveI := rlt_finite (F := F) (E := E) IsModuleTopology.isTopologicalRing 𝔸 𝒜`.
-/
theorem rlt_topRing : IsTopologicalRing 𝒜 :=
  haveI := rlt_finite (F := F) (E := E)
  IsModuleTopology.isTopologicalRing 𝔸 𝒜

/- English proof (translation)
Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Rewrite using `[← rlt_image_comb b hb]`. Use `IsModuleTopology.toContinuousAdd 𝔸 𝒜` as an intermediate fact. Conclude with `(isCompact_univ_pi fun _ => rlt_isCompact_intAd).image (IsModuleTopology.continuous_of_linearMap _)`.
-/
theorem rlt_isCompact_intAf : IsCompact (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  rw [← rlt_image_comb b hb]
  have := IsModuleTopology.toContinuousAdd 𝔸 𝒜
  exact (isCompact_univ_pi fun _ => rlt_isCompact_intAd).image (IsModuleTopology.continuous_of_linearMap _)

/- English proof (translation)
Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Rewrite using `[← rlt_image_comb b hb]`. Conclude with `IsModuleTopology.isOpenMap_of_surjective (rlt_comb_surj b hb) _ (isOpen_set_pi Set.finite_univ fun _ _ => rlt_isOpen_intAd)`.
-/
theorem rlt_isOpen_intAf : IsOpen (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  rw [← rlt_image_comb b hb]
  exact IsModuleTopology.isOpenMap_of_surjective (rlt_comb_surj b hb) _ (isOpen_set_pi Set.finite_univ fun _ _ => rlt_isOpen_intAd)

def rlt_comm : 𝒜 →ₗ[𝔸] 𝔸 ⊗[F] E where
  toFun := TensorProduct.comm F E 𝔸
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e b =>
      rw [rlt_smul_tmul]
      simp only [TensorProduct.comm_tmul, RingHom.id_apply, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
Set `bas` to `Algebra.TensorProduct.basis 𝔸 (Module.finBasis F E)`. Set `φ : 𝒜 →ₗ[𝔸] (Fin (Module.finrank F E) → 𝔸)` to `(bas.equivFun : _ →ₗ[𝔸] _).comp rlt_comm`. Establish `hinj : Function.Injective φ` using `bas.equivFun.injective.comp (TensorProduct.comm F E 𝔸).injective`. Establish `: T2Space 𝔸` using `inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))`. Conclude with `T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)`.
-/
theorem adeles_t2Space : T2Space 𝒜 := by
  let bas := Algebra.TensorProduct.basis 𝔸 (Module.finBasis F E)
  let φ : 𝒜 →ₗ[𝔸] (Fin (Module.finrank F E) → 𝔸) := (bas.equivFun : _ →ₗ[𝔸] _).comp rlt_comm
  have hinj : Function.Injective φ := bas.equivFun.injective.comp (TensorProduct.comm F E 𝔸).injective
  have : T2Space 𝔸 := inferInstanceAs
    (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

/- English proof (translation)
Use `IsModuleTopology.toContinuousAdd 𝔸 𝒜` as an intermediate fact. Set `φ : 𝒜 →ₗ[𝔸] 𝒜` to `{ toFun := Formalism.UG.sigR σ 𝔸 map_add' := map_add _ map_smul' := by`. Introduce `a x`. Rewrite using `[Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def]`. Use `congr 1`.

Use `show Formalism.UG.sigR σ 𝔸 ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a`. Simplify using `[Formalism.UG.sigR] }`. Conclude with `IsModuleTopology.continuous_of_linearMap φ`.
-/
theorem rlt_continuous_sig (σ : E →ₐ[F] E) : Continuous (Formalism.UG.sigR σ 𝔸) := by
  have := IsModuleTopology.toContinuousAdd 𝔸 𝒜
  let φ : 𝒜 →ₗ[𝔸] 𝒜 :=
    { toFun := Formalism.UG.sigR σ 𝔸
      map_add' := map_add _
      map_smul' := by
        intro a x
        rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def]
        congr 1
        show Formalism.UG.sigR σ 𝔸 ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
        simp [Formalism.UG.sigR] }
  exact IsModuleTopology.continuous_of_linearMap φ

end Tens

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

local notation "𝒜" => E ⊗[F] Formalism.L2.Herm.Af F

/- English proof (translation)
Establish `h : Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (u : Matrix (Fin n) (Fin n) 𝒜) * ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F))) * (u : Matrix (Fin n) (Fin n) 𝒜) = (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) := hu`. Rewrite `h` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rlt_inv_eq {u : GL (Fin n) 𝒜} (hu : u ∈ UAd hc n) :
    ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) =
      Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (u : Matrix (Fin n) (Fin n) 𝒜) := by
  have h : Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (u : Matrix (Fin n) (Fin n) 𝒜) *
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) * (u : Matrix (Fin n) (Fin n) 𝒜) =
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) := hu
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  calc ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜)
      = (Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (u : Matrix (Fin n) (Fin n) 𝒜) * (u : Matrix (Fin n) (Fin n) 𝒜)) *
          ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) := by rw [h, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/- English proof (translation)
Establish `h1 : (u : Matrix (Fin n) (Fin n) 𝒜) ∈ (RingHom.mapMatrix (m` using `Fin n) (Formalism.L2.Herm.intAf F E).subtype).range := ⟨Matrix.of fun i j => ⟨_, hi i j⟩, by ext i j; rfl⟩`. Establish `h2 : ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) ∈ (RingHom.mapMatrix (m` using `Fin n) (Formalism.L2.Herm.intAf F E).subtype).range := by`. Rewrite using `[rlt_inv_eq hc n hu]`. Conclude with `⟨Matrix.of fun i j => ⟨_, Formalism.UG.P.csScale_sigR_mem hc.sig (hi j i)⟩, by ext i j; rfl⟩`. Take `⟨y, hy⟩` from `Formalism.UG.P.levelaf_mem_range_of_integral _ u h1 h2`.

Conclude with `⟨y, by simp [frGL, intGL, hy]⟩`.
-/
theorem rlt_mem_St {u : GL (Fin n) 𝒜} (hu : u ∈ UAd hc n)
    (hi : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E) : u ∈ St (1 : GL (Fin n) 𝒜) := by
  have h1 : (u : Matrix (Fin n) (Fin n) 𝒜) ∈ (RingHom.mapMatrix (m := Fin n) (Formalism.L2.Herm.intAf F E).subtype).range :=
    ⟨Matrix.of fun i j => ⟨_, hi i j⟩, by ext i j; rfl⟩
  have h2 : ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) ∈
      (RingHom.mapMatrix (m := Fin n) (Formalism.L2.Herm.intAf F E).subtype).range := by
    rw [rlt_inv_eq hc n hu]
    exact ⟨Matrix.of fun i j => ⟨_, Formalism.UG.P.csScale_sigR_mem hc.sig (hi j i)⟩, by ext i j; rfl⟩
  obtain ⟨y, hy⟩ := Formalism.UG.P.levelaf_mem_range_of_integral _ u h1 h2
  exact ⟨y, by simp [frGL, intGL, hy]⟩

/- English proof (translation)
Establish `hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `hi : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E`. Introduce `i j`. Rewrite using `[hs]`. Conclude with `add_mem (hone i j) (mul_mem (iA_mem a) (s i j).2)`.

Establish `hSt` using `rlt_mem_St hc n hu hi`. Take `⟨y, hy, hred⟩` from `St_one_int hSt`. Establish `hr : ∀ P : Pl E, a ∈ P.asIdeal → redAt (1 : GL (Fin n) 𝒜) P ⟨u, hSt⟩ = 1`. Introduce `P hP`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Rewrite using `[hred P i j]`. Establish `e : y i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j + oToS F E a * s i j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hy, hs]`.

Simplify using `only [Subring.coe_add, Subring.coe_mul]`. Use `congr 1`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[e, map_add, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul, add_zero]`.

Use `show _ = (1 : Matrix (Fin n) (Fin n) (kP P)) i j`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hJ : u ∈ J0 hc n ST`. Use `⟨⟨hu, hSt⟩, ?_⟩` and prove the remaining obligations.

Use `Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_` and prove the remaining obligations. Use `⟨⟨u, hSt⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show redAt (1 : GL (Fin n) 𝒜) P ⟨u, hSt⟩ ∈ mirab (kP P) n`. Rewrite using `[hr P (haT P hP)]`. Conclude with `Subgroup.one_mem _`.

Use `⟨⟨u, hJ⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show redG hc n ST SG ⟨u, hJ⟩ = 1`. Use function extensionality and compare the values at `w`. Conclude with `hr w.1 (haG w.1 w.2)`.
-/
theorem mem_kOne_of_congruent_one (a : 𝓞 E) (haT : ∀ P ∈ ST, a ∈ P.asIdeal) (haG : ∀ P ∈ SG, a ∈ P.asIdeal) {u : GL (Fin n) 𝒜} (hu : u ∈ UAd hc n)
    (s : Fin n → Fin n → Formalism.L2.Herm.intAf F E)
    (hs : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j = (1 : Matrix (Fin n) (Fin n) 𝒜) i j + iA F E (algebraMap (𝓞 E) E a) * s i j) :
    u ∈ K1 hc n ST SG := by
  classical
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hi : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [hs]
    exact add_mem (hone i j) (mul_mem (iA_mem a) (s i j).2)
  have hSt := rlt_mem_St hc n hu hi
  obtain ⟨y, hy, hred⟩ := St_one_int hSt
  have hr : ∀ P : Pl E, a ∈ P.asIdeal → redAt (1 : GL (Fin n) 𝒜) P ⟨u, hSt⟩ = 1 := by
    intro P hP
    apply Units.ext
    ext i j
    rw [hred P i j]
    have e : y i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j + oToS F E a * s i j := by
      apply Subtype.ext
      rw [← hy, hs]
      simp only [Subring.coe_add, Subring.coe_mul]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [e, map_add, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul, add_zero]
    show _ = (1 : Matrix (Fin n) (Fin n) (kP P)) i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hJ : u ∈ J0 hc n ST := by
    refine ⟨⟨hu, hSt⟩, ?_⟩
    refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_
    refine ⟨⟨u, hSt⟩, ?_, rfl⟩
    show redAt (1 : GL (Fin n) 𝒜) P ⟨u, hSt⟩ ∈ mirab (kP P) n
    rw [hr P (haT P hP)]
    exact Subgroup.one_mem _
  refine ⟨⟨u, hJ⟩, ?_, rfl⟩
  show redG hc n ST SG ⟨u, hJ⟩ = 1
  funext w
  exact hr w.1 (haG w.1 w.2)

/- English proof (translation)
Use `choose f hf hf0 using fun P : Pl E => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Use `⟨∏ P ∈ S, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP => ?_⟩` and prove the remaining obligations. Conclude with `Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)`.
-/
theorem rlt_exists_a (S : Finset (Pl E)) : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ P ∈ S, a ∈ P.asIdeal := by
  classical
  choose f hf hf0 using fun P : Pl E => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  refine ⟨∏ P ∈ S, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP => ?_⟩
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)

end Alg

section GLTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

/- English proof (translation)
Establish `h : {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (Formalism.L2.Herm.intAf F E : Set 𝒜)`. Use extensionality with `A`. Conclude with `⟨fun hA i _ j _ => hA i j, fun hA i j => hA i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[h]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => rlt_isCompact_intAf`.
-/
theorem rlt_isCompact_MS : IsCompact {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} := by
  have h : {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} =
      Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
    ext A
    exact ⟨fun hA i _ j _ => hA i j, fun hA i j => hA i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => rlt_isCompact_intAf

/- English proof (translation)
Establish `hK : IsCompact ({A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E}))` using `(rlt_isCompact_MS n).prod ((Homeomorph.isCompact_preimage _).2 (rlt_isCompact_MS n))`. Conclude with `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) 𝒜)).isCompact_preimage hK`.
-/
theorem rlt_isCompact_GLS : IsCompact {u : GL (Fin n) 𝒜 | (∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E) ∧
    ∀ i j, ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) i j ∈ Formalism.L2.Herm.intAf F E} := by
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} ×ˢ
      (MulOpposite.opHomeomorph.symm ⁻¹' {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E})) :=
    (rlt_isCompact_MS n).prod ((Homeomorph.isCompact_preimage _).2 (rlt_isCompact_MS n))
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) 𝒜)).isCompact_preimage hK

/- English proof (translation)
Establish `hσ` using `rlt_continuous_sig (F := F) (E := E) hc.sig`. Establish `h1 : Continuous fun u : GL (Fin n) 𝒜 => Formalism.UG.cT (Formalism.UG.sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) 𝒜) * ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F))) * (u : Matrix (Fin n) (Fin n) 𝒜) := by`. Unfold `Formalism.UG.cT`. Conclude with `(((Units.continuous_val.matrix_map hσ).matrix_transpose).matrix_mul continuous_const).matrix_mul Units.continuous_val`. Conclude with `isClosed_eq h1 continuous_const`.
-/
theorem rlt_isClosed_UAd : IsClosed (UAd hc n : Set (GL (Fin n) 𝒜)) := by
  have hσ := rlt_continuous_sig (F := F) (E := E) hc.sig
  have h1 : Continuous fun u : GL (Fin n) 𝒜 =>
      Formalism.UG.cT (Formalism.UG.sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) 𝒜) *
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * (u : Matrix (Fin n) (Fin n) 𝒜) := by
    unfold Formalism.UG.cT
    exact (((Units.continuous_val.matrix_map hσ).matrix_transpose).matrix_mul continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq h1 continuous_const

/- English proof (translation)
Take `⟨a, ha0, ha⟩` from `rlt_exists_a (ST ∪ SG)`. Use `set c : 𝒜 := iA F E (algebraMap (𝓞 E) E a)⁻¹ with hc'`. Establish `hca : iA F E (algebraMap (𝓞 E) E a) * c = 1`. Rewrite using `[hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]`. Set `W : Set (GL (Fin n) 𝒜)` to `{u | ∀ i j, c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j) ∈ Formalism.L2.Herm.intAf F E}`.

Establish `hWo : IsOpen W`. Establish `: W = ⋂ i, ⋂ j, (fun u : GL (Fin n) 𝒜 => c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j)) ⁻¹' (Formalism.L2.Herm.intAf F E : Set 𝒜)`. Use extensionality with `u`. Simplify using `[W]`. Rewrite using `[this]`.

Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => rlt_isOpen_intAf.preimage ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((Units.continuous_val.matrix_elem i j).sub continuous_const)`. Establish `hW1 : (1 : GL (Fin n) 𝒜) ∈ W`. Introduce `i j`. Simplify using the standard rewrite rules.

Establish `hsub : ∀ u ∈ UAd hc n, u ∈ W → u ∈ U`. Introduce `u hu hW`. Use `hU (mem_kOne_of_congruent_one hc n ST SG a (fun P hP => ha P (Finset.mem_union_left _ hP)) (fun P hP => ha P (Finset.mem_union_right _ hP)) hu (fun i j => ⟨_, hW i j⟩) ?_)` and prove the remaining obligations. Introduce `i j`. Use `show _ = _ + iA F E (algebraMap (𝓞 E) E a) * (c * _)`.

Rewrite using `[← mul_assoc, hca, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnh : ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) ∈ 𝓝 (1 : UAd hc n)`. Use `Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `hsub x.1 x.2 hx`. Conclude with `Subgroup.isOpen_of_mem_nhds _ hnh`.
-/
theorem rlt_open_of_le (U : Subgroup (GL (Fin n) 𝒜)) (hU : K1 hc n ST SG ≤ U) :
    IsOpen {x : UAd hc n | (x : GL (Fin n) 𝒜) ∈ U} := by
  classical
  obtain ⟨a, ha0, ha⟩ := rlt_exists_a (ST ∪ SG)
  set c : 𝒜 := iA F E (algebraMap (𝓞 E) E a)⁻¹ with hc'
  have hca : iA F E (algebraMap (𝓞 E) E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  let W : Set (GL (Fin n) 𝒜) := {u | ∀ i j, c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j) ∈
    Formalism.L2.Herm.intAf F E}
  have hWo : IsOpen W := by
    have : W = ⋂ i, ⋂ j, (fun u : GL (Fin n) 𝒜 => c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j)) ⁻¹'
        (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
      ext u; simp [W]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => rlt_isOpen_intAf.preimage ?_
    exact continuous_const.mul ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  have hW1 : (1 : GL (Fin n) 𝒜) ∈ W := by
    intro i j
    simp
  have hsub : ∀ u ∈ UAd hc n, u ∈ W → u ∈ U := by
    intro u hu hW
    refine hU (mem_kOne_of_congruent_one hc n ST SG a (fun P hP => ha P (Finset.mem_union_left _ hP))
      (fun P hP => ha P (Finset.mem_union_right _ hP)) hu (fun i j => ⟨_, hW i j⟩) ?_)
    intro i j
    show _ = _ + iA F E (algebraMap (𝓞 E) E a) * (c * _)
    rw [← mul_assoc, hca, one_mul]
    ring
  have hnh : ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) ∈ 𝓝 (1 : UAd hc n) := by
    refine Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) ?_
    intro x hx
    exact hsub x.1 x.2 hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

/- English proof (translation)
Establish `hcl : IsClosed ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n))` using `Subgroup.isClosed_of_isOpen _ (rlt_open_of_le hc n ST SG U hU)`. Establish `himg : (U : Set (GL (Fin n) 𝒜)) = Subtype.val '' ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n))`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce `hu`.

Conclude with `⟨⟨u, hUA hu⟩, hu, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx`. Establish `hclosed : IsClosed (U : Set (GL (Fin n) 𝒜))`. Rewrite using `[himg]`.

Conclude with `(rlt_isClosed_UAd hc n).isClosedEmbedding_subtypeVal.isClosedMap _ hcl`. Use `(rlt_isCompact_GLS n).of_isClosed_subset hclosed ?_` and prove the remaining obligations. Introduce `u hu`. Establish `hS : u ∈ St (1 : GL (Fin n) 𝒜)` using `hUS hu`. Take `⟨y, hy, -⟩` from `St_one_int hS`.

Take `⟨y', hy', -⟩` from `St_one_int (Subgroup.inv_mem _ hS)`. Conclude with `⟨fun i j => by rw [hy]; exact (y i j).2, fun i j => by rw [hy']; exact (y' i j).2⟩`.
-/
theorem rlt_compact_of_le (U : Subgroup (GL (Fin n) 𝒜)) (hU : K1 hc n ST SG ≤ U) (hUA : U ≤ UAd hc n)
    (hUS : U ≤ St (1 : GL (Fin n) 𝒜)) : IsCompact (U : Set (GL (Fin n) 𝒜)) := by
  have hcl : IsClosed ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) :=
    Subgroup.isClosed_of_isOpen _ (rlt_open_of_le hc n ST SG U hU)
  have himg : (U : Set (GL (Fin n) 𝒜)) =
      Subtype.val '' ((U.subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u, hUA hu⟩, hu, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hclosed : IsClosed (U : Set (GL (Fin n) 𝒜)) := by
    rw [himg]
    exact (rlt_isClosed_UAd hc n).isClosedEmbedding_subtypeVal.isClosedMap _ hcl
  refine (rlt_isCompact_GLS n).of_isClosed_subset hclosed ?_
  intro u hu
  have hS : u ∈ St (1 : GL (Fin n) 𝒜) := hUS hu
  obtain ⟨y, hy, -⟩ := St_one_int hS
  obtain ⟨y', hy', -⟩ := St_one_int (Subgroup.inv_mem _ hS)
  exact ⟨fun i j => by rw [hy]; exact (y i j).2, fun i j => by rw [hy']; exact (y' i j).2⟩

end GLTop

section Final

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
The claim follows from `rlt_compact_of_le hc n ST SG _ (kOne_le_unipotentLevel hc n ST SG H) (levU_le_UAd hc n ST SG H) ((unipotentLevel_le_mirabolicLevel hc n ST SG H).trans (congruence_subgroup_le_stabilizer hc n ST))`.
-/
theorem levU_compact : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (levU hc n ST SG H : Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
  rlt_compact_of_le hc n ST SG _ (kOne_le_unipotentLevel hc n ST SG H) (levU_le_UAd hc n ST SG H)
    ((unipotentLevel_le_mirabolicLevel hc n ST SG H).trans (congruence_subgroup_le_stabilizer hc n ST))

/- English proof (translation)
The claim follows from `rlt_open_of_le hc n ST SG _ (kOne_le_unipotentLevel hc n ST SG H)`.
-/
theorem levU_open : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : Formalism.UG.UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) |
      (x : GL _ _) ∈ levU hc n ST SG H} :=
  rlt_open_of_le hc n ST SG _ (kOne_le_unipotentLevel hc n ST SG H)

end Final

end Formalism.L2.Col
