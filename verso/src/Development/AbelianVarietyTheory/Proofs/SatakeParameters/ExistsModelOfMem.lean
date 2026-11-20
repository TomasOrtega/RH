import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst

noncomputable section

namespace GlobalTheory.AboveLRes

/- English proof (translation)
Set `f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l)` to `Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom`. Establish `hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _)` using `Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective`. Establish `hf : Function.Injective f` using `Units.map_injective hmi`. Set `lift : Γ → Matrix (Fin a) (Fin a) ↥T.1` to `fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩`. Establish `hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _)` using `fun g => by ext i k; rfl`.

Establish `hm : ∀ g, ρ g ∈ f.range`. Introduce `g`. Use `⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩` and prove the remaining obligations. Rewrite using `[map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Rewrite using `[map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`.

Use `⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩` and prove the remaining obligations. Conclude with `MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩`.
-/
theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ} (T : FinExt l)
    (ρ : Γ →* GL (Fin a) (Om l))
    (hρ : ∀ g i k, ((ρ g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1) :
    ∃ ρ' : Γ →* GL (Fin a) ↥T.1, mapRep (algebraMap ↥T.1 (Om l)) ρ' = ρ := by
  let f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l) := Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom
  have hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _) :=
    Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective
  have hf : Function.Injective f := Units.map_injective hmi
  let lift : Γ → Matrix (Fin a) (Fin a) ↥T.1 := fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩
  have hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _) :=
    fun g => by ext i k; rfl
  have hm : ∀ g, ρ g ∈ f.range := by
    intro g
    refine ⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩
  exact MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

/- English proof (translation)
Set `τ : G L Ω` to `{ (σ : G K Ω).toRingEquiv with commutes' := hσ }`. Establish `hτ : τ ∈ Dec (F` using `L) A := by`. Establish `hg` using `mem_Dec.mp σ.2`. Rewrite using `[mem_Dec]`. Use extensionality with `x`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Use `conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Both sides reduce to the same expression. Conclude with `⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩`.
-/
theorem exists_decRes_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L]
    [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} (σ : ↥(Dec (F := K) A))
    (hσ : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) :
    ∃ σ' : ↥(Dec (F := L) A), decRes A σ' = σ := by
  let τ : G L Ω := { (σ : G K Ω).toRingEquiv with commutes' := hσ }
  have hτ : τ ∈ Dec (F := L) A := by
    have hg := mem_Dec.mp σ.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

open GlobalTheory.AboveL in

/- English proof (translation)
Set `M : IntermediateField K Ω` to `(IsScalarTower.toAlgHom K L Ω).fieldRange`. Use `haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L`. Use `haveI : FiniteDimensional K M := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional`. Use `haveI : Finite (G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen`. Use `haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Use `set H : Subgroup ↥(Dec (F := K) A) := M.fixingSubgroup.subgroupOf (Dec (F := K) A) with hH`. Use `haveI : Finite (↥(Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex`. Use `set S : Set (Om l) := Set.range fun x : (↥(Dec (F := K) A) ⧸ H) × Fin a × Fin a => ((r (x.1.out : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS`. Establish `hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S)` using `IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Take `⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1` from `⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩`.

Establish `hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1` using `hT ▸ le_sup_left.trans le_sup_left`. Establish `hLT : LL'.1 ≤ T.1` using `hT ▸ le_sup_right.trans le_sup_left`. Establish `hBT : B.1 ≤ T.1` using `hT ▸ le_sup_right`. Establish `hfix : ∀ σ : ↥(Dec (F` using `K) A), σ ∈ H → ∀ i k, ((r (σ : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by`. Introduce `σ hσ i k`.

Establish `hσ' : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x` using `fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩`. Take `⟨τ, hτ⟩` from `exists_decRes_eq σ hσ'`. Establish `e1 : (r (σ : G K Ω)) = ((resTo L r).comp (Dec (F` using `L) A).subtype) τ := by`. Rewrite using `[← hτ]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← hm']`. Conclude with `((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2`. Establish `hent : ∀ (g : ↥(Dec (F` using `K) A)) i k, (((r.comp (Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by`. Introduce `g i k`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H g`.

Establish `hg : g = (QuotientGroup.mk g : ↥(Dec (F` using `K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(Dec (F := K) A)) := by`. Rewrite using `[hh, Subgroup.coe_inv, mul_inv_cancel_right]`. Rewrite using `[MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]`. Use `sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_` and prove the remaining obligations. Conclude with `hLT (hfix _ (h⁻¹).2 m k)`.

Take `⟨r₁, hr₁⟩` from `exists_model_of_mem T _ hent`. Conclude with `⟨T, r₁, hBT, hr₁⟩`.
-/
theorem exists_model_dec {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) {l : ℕ}
    [Fact l.Prime] {a : ℕ} (r : G K Ω →* GL (Fin a) (Om l)) (LL' B : FinExt l)
    (r' : ↥(Dec (F := L) A) →* GL (Fin a) ↥LL'.1)
    (hm' : mapRep (algebraMap ↥LL'.1 (Om l)) r' = (resTo L r).comp (Dec (F := L) A).subtype) :
    ∃ (T : FinExt l) (r₁ : ↥(Dec (F := K) A) →* GL (Fin a) ↥T.1), B.1 ≤ T.1 ∧
      mapRep (algebraMap ↥T.1 (Om l)) r₁ = r.comp (Dec (F := K) A).subtype := by
  let M : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K M :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  haveI : Finite (G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen
  haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set H : Subgroup ↥(Dec (F := K) A) := M.fixingSubgroup.subgroupOf (Dec (F := K) A) with hH
  haveI : Finite (↥(Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set S : Set (Om l) := Set.range fun x : (↥(Dec (F := K) A) ⧸ H) × Fin a × Fin a =>
    ((r (x.1.out : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS
  have hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1 :=
    ⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩
  have hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1 := hT ▸ le_sup_left.trans le_sup_left
  have hLT : LL'.1 ≤ T.1 := hT ▸ le_sup_right.trans le_sup_left
  have hBT : B.1 ≤ T.1 := hT ▸ le_sup_right
  have hfix : ∀ σ : ↥(Dec (F := K) A), σ ∈ H → ∀ i k,
      ((r (σ : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by
    intro σ hσ i k
    have hσ' : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_decRes_eq σ hσ'
    have e1 : (r (σ : G K Ω)) = ((resTo L r).comp (Dec (F := L) A).subtype) τ := by
      rw [← hτ]; rfl
    rw [e1, ← hm']
    exact ((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2
  have hent : ∀ (g : ↥(Dec (F := K) A)) i k,
      (((r.comp (Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by
    intro g i k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    have hg : g = (QuotientGroup.mk g : ↥(Dec (F := K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(Dec (F := K) A)) := by
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_
    exact hLT (hfix _ (h⁻¹).2 m k)
  obtain ⟨r₁, hr₁⟩ := exists_model_of_mem T _ hent
  exact ⟨T, r₁, hBT, hr₁⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

open GlobalTheory.AboveL in

/- English proof (translation)
Introduce `K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL`. Establish `hcL : Continuous fun g : ↥(Dec (F` using `L) A) => ((((resTo L r).comp (Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)`. Take `⟨LL', r', hm', hV'⟩` from `hL`. Take `⟨T, r₁, hBT, hr₁⟩` from `exists_model_dec A r LL' Bw.LL r' hm'.2`. Take `⟨S'', Bw'', hjj, hTS, hle⟩` from `exists_bridge (L := L) Bw hj T`.

Establish `hj'' : GlobalTheory.Pst.Induces Bw''` using `fun x => by rw [hjj]; exact hj x`. Take `⟨LL₃, r₃, hm₃, hV₃⟩` from `GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _ hcL ⟨LL', r', hm', hV'⟩`. Establish `h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1` using `le_sup_left`. Establish `h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1` using `le_sup_right`. Establish `hTT : T.1 ≤ (supExt Bw''.LL LL₃).1` using `hTS.trans h1`.

Establish `hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l)) (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (Dec (F` using `K) A).subtype := by`. Use extensionality with `g i k`. Conclude with `congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁`. Establish `hmL : IsModel Bw'' ((resTo L r).comp (Dec (F` using `L) A).subtype) (supExt Bw''.LL LL₃) ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Use extensionality with `g i k`. Conclude with `congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) => ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'`. Establish `hm₃' : IsModel Bw'' ((resTo L r).comp (Dec (F` using `L) A).subtype) (supExt Bw''.LL LL₃) (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by`. Use `⟨hm₃.1.trans h3, ?_⟩` and prove the remaining obligations. Use extensionality with `g i k`.

Conclude with `congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2`. Establish `heq` using `IsModel.unique Bw'' _ hm₃' hmL`. Establish `hp` using `GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃`. Rewrite `hp` using `[heq, repE_decRes Bw Bw'' hjj hle]`. Conclude with `⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩`.
-/
theorem isPstAt_of_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Om l)), Continuous r → ∀ (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL
  have hcL : Continuous fun g : ↥(Dec (F := L) A) =>
      ((((resTo L r).comp (Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)
  obtain ⟨LL', r', hm', hV'⟩ := hL
  obtain ⟨T, r₁, hBT, hr₁⟩ := exists_model_dec A r LL' Bw.LL r' hm'.2

  obtain ⟨S'', Bw'', hjj, hTS, hle⟩ := exists_bridge (L := L) Bw hj T
  have hj'' : GlobalTheory.Pst.Induces Bw'' := fun x => by rw [hjj]; exact hj x
  obtain ⟨LL₃, r₃, hm₃, hV₃⟩ := GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _
    hcL ⟨LL', r', hm', hV'⟩
  have h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_left
  have h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_right
  have hTT : T.1 ≤ (supExt Bw''.LL LL₃).1 := hTS.trans h1
  have hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l))
      (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (Dec (F := K) A).subtype := by
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmL : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by
    refine ⟨h1, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'
  have hm₃' : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h3, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw'' _ hm₃' hmL
  have hp := GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃
  rw [heq, repE_decRes Bw Bw'' hjj hle] at hp
  exact ⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩

end GlobalTheory.AboveLRes
