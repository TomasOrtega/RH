import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioWOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Formalism.LocalToGlobal.UnitaryNorms.CharProd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

/- English proof (translation)
Establish `: Infinite (HeightOneSpectrum (𝓞 ℚ))` using `Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective`. Use `Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 ℚ)) fun v => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal`. Conclude with `⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩`.
-/
private theorem inf_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨⟨s, hs, e1⟩, t, ht, e2⟩` from `hc`. Establish `a` using `(H s hs).resolve_left e1`. Establish `b` using `(H t ht).resolve_right e2`.

Apply the tactic sequence `rcases H _ (I.mul_mem hs ht) with e | e <;> simp only [map_mul] at e`. Conclude with `e1 (mul_right_cancel (b ▸ e))`. Conclude with `e2 (mul_left_cancel (a ▸ e))`.
-/
private theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) : (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨s, hs, e1⟩, t, ht, e2⟩ := hc
  have a := (H s hs).resolve_left e1
  have b := (H t ht).resolve_right e2
  rcases H _ (I.mul_mem hs ht) with e | e <;> simp only [map_mul] at e
  · exact e1 (mul_right_cancel (b ▸ e))
  · exact e2 (mul_left_cancel (a ▸ e))

/- English proof (translation)
Simplify using `only [IsIrr, IsIrrSub, not_and, not_forall] at h`. Take `⟨W, -, hW, hne⟩` from `h top_ne_bot (fun _ _ _ => Submodule.mem_top)`. Rewrite `hne` using `[not_or]`. Establish `h2 : Module.finrank k W < 2` using `by simpa using Submodule.finrank_lt hne.2`. Establish `h0 : Module.finrank k W ≠ 0` using `fun h => hne.1 (Submodule.finrank_eq_zero.mp h)`.

Take `⟨v, hv, hall⟩` from `finrank_eq_one_iff'.mp (show Module.finrank k W = 1 by omega)`. Establish `hv0 : (v : Fin 2 → k) ≠ 0` using `fun h => hv (Subtype.ext h)`. Use `choose c₀ hc₀ using fun g => hall ⟨_, hW g v v.2⟩`. Establish `hc1 : ∀ g, (r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k) = c₀ g • (v : Fin 2 → k)` using `fun g => (congrArg Subtype.val (hc₀ g)).symm`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hv0`.

Set `c₁ : Γ →* k` to `{ toFun := c₀ map_one' := smul_left_injective k hv0 (by simpa using (hc1 1).symm) map_mul' := fun s t => smul_left_injective k hv0 (by`. Simplify using `only`. Rewrite using `[← hc1, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc1, Matrix.mulVec_smul, hc1, smul_smul, mul_comm]) }`. Establish `hcc : Continuous c₁.toHomUnits`. Use `Units.isEmbedding_val₀.continuous_iff.2 ?_` and prove the remaining obligations.

Establish `: Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k)) i / (v : Fin 2 → k) i` using `((continuous_apply i).comp ((Units.continuous_val.comp hc).matrix_mulVec continuous_const)).div_const _`. Use `this.congr fun g => ?_` and prove the remaining obligations. Rewrite using `[hc1, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hi]`. Both sides reduce to the same expression. Establish `hdet : Continuous (Matrix.GeneralLinearGroup.det.comp r : Γ →* kˣ)` using `Units.isEmbedding_val₀.continuous_iff.2 (Units.continuous_val.comp hc).matrix_det`.

Use `⟨c₁.toHomUnits, Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits, hcc, hdet.div' hcc, fun s => ?_⟩` and prove the remaining obligations. Establish `n0 : c₀ s ≠ 0` using `(c₁.toHomUnits s).ne_zero`. Establish `e1 : ((c₁.toHomUnits s : kˣ) : k) = c₀ s` using `rfl`. Establish `e2 : (((Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits) s : kˣ) : k) = (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s`. Rewrite using `[MonoidHom.div_apply, Units.val_div_eq_div_val, e1]`.

Both sides reduce to the same expression. Establish `a0` using `congrFun (hc1 s) 0`. Establish `a1` using `congrFun (hc1 s) 1`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at a0 a1`. Establish `q : c₀ s ^ 2 - (r s : Matrix (Fin 2) (Fin 2) k).trace * c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det = 0`.

Rewrite using `[Matrix.trace_fin_two, Matrix.det_fin_two]`. Use `mul_right_cancel₀ hi ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using `only [Fin.zero_eta, Pi.zero_apply, mul_zero]`. Take the linear combination `(r s 1 1 - c₀ s) * a0 - r s 0 1 * a1`.

Simplify using `only [Fin.mk_one, Pi.zero_apply, mul_zero]`. Take the linear combination `(r s 0 0 - c₀ s) * a1 - r s 1 0 * a0`. Establish `t : (r s : Matrix (Fin 2) (Fin 2) k).trace = c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-q`.

Establish `u : (r s : Matrix (Fin 2) (Fin 2) k).det = c₀ s * ((r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e2, Matrix.charpoly_fin_two, t]`. Use `conv_lhs => rw [u]`. Rewrite using `[← u, map_add]`.

Use `conv_lhs => enter [2]`. Rewrite using `[u, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem chars_of_red {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [NormedField k] (r : Γ →* GL (Fin 2) k)
    (hc : Continuous r) (h : ¬ IsIrr r) : ∃ c d : Γ →* kˣ, Continuous c ∧ Continuous d ∧
      ∀ s, (r s : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (c s : k)) * (X - C (d s : k)) := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp (show Module.finrank k W = 1 by omega)
  have hv0 : (v : Fin 2 → k) ≠ 0 := fun h => hv (Subtype.ext h)
  choose c₀ hc₀ using fun g => hall ⟨_, hW g v v.2⟩
  have hc1 : ∀ g, (r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k) = c₀ g • (v : Fin 2 → k) := fun g =>
    (congrArg Subtype.val (hc₀ g)).symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  let c₁ : Γ →* k :=
    { toFun := c₀
      map_one' := smul_left_injective k hv0 (by simpa using (hc1 1).symm)
      map_mul' := fun s t => smul_left_injective k hv0 (by
        simp only
        rw [← hc1, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc1, Matrix.mulVec_smul, hc1, smul_smul, mul_comm]) }
  have hcc : Continuous c₁.toHomUnits := by
    refine Units.isEmbedding_val₀.continuous_iff.2 ?_
    have : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k)) i / (v : Fin 2 → k) i :=
      ((continuous_apply i).comp ((Units.continuous_val.comp hc).matrix_mulVec continuous_const)).div_const _
    refine this.congr fun g => ?_
    rw [hc1, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hi]
    rfl
  have hdet : Continuous (Matrix.GeneralLinearGroup.det.comp r : Γ →* kˣ) :=
    Units.isEmbedding_val₀.continuous_iff.2 (Units.continuous_val.comp hc).matrix_det
  refine ⟨c₁.toHomUnits, Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits, hcc, hdet.div' hcc, fun s => ?_⟩
  have n0 : c₀ s ≠ 0 := (c₁.toHomUnits s).ne_zero
  have e1 : ((c₁.toHomUnits s : kˣ) : k) = c₀ s := rfl
  have e2 : (((Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits) s : kˣ) : k) =
      (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    rw [MonoidHom.div_apply, Units.val_div_eq_div_val, e1]; rfl
  have a0 := congrFun (hc1 s) 0
  have a1 := congrFun (hc1 s) 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at a0 a1
  have q : c₀ s ^ 2 - (r s : Matrix (Fin 2) (Fin 2) k).trace * c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    refine mul_right_cancel₀ hi ?_
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply, mul_zero]
      linear_combination (r s 1 1 - c₀ s) * a0 - r s 0 1 * a1
    · simp only [Fin.mk_one, Pi.zero_apply, mul_zero]
      linear_combination (r s 0 0 - c₀ s) * a1 - r s 1 0 * a0
  have t : (r s : Matrix (Fin 2) (Fin 2) k).trace = c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    field_simp
    linear_combination -q
  have u : (r s : Matrix (Fin 2) (Fin 2) k).det = c₀ s * ((r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s) := by
    field_simp
  rw [e1, e2, Matrix.charpoly_fin_two, t]
  conv_lhs => rw [u]
  rw [← u, map_add]
  conv_lhs => enter [2]; rw [u, map_mul]
  ring

/- English proof (translation)
Establish `e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly = (r : Matrix (Fin 2) (Fin 2) K).charpoly`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv]`. Conclude with `Matrix.charpoly_units_conj g _`. Rewrite using `[← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]`.
-/
private theorem charpoly_tri {K : Type} [Field K] (g r : GL (Fin 2) K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly =
      (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 0 0)) * (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 1 1)) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `Algebra.IsAlgebraic.trans ℚ F Ω`. Establish `: IsAlgClosure ℚ Ω` using `⟨inferInstance, inferInstance⟩`. Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`.

Establish `hv : A.valuation (l : Ω) < 1`. Simplify using `using (hA _).2 hl`. Take `⟨u, hu⟩` from `GlobalTheory.CycDec.exists_unit_infinite_order l`. Take `⟨σ, hσ, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u`. Set `K : IntermediateField ℚ Ω` to `(IsScalarTower.toAlgHom ℚ F Ω).fieldRange`.

Establish `: FiniteDimensional ℚ K` using `(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional`. Establish `: Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup)` using `Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen`. Establish `: K.fixingSubgroup.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Take `⟨N, hN, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ`. Set `g : G F Ω` to `{ (σ ^ N).toRingEquiv with commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }`.

Establish `hD : σ ^ N ∈ Ine (F` using `ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N`. Establish `hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N)` using `rfl`. Establish `hinj : Function.Injective (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom)` using `Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)`. Use `⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩` and prove the remaining obligations. Rewrite using `[map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]`.
-/
private theorem cyc_ine {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine ⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]

end UpperTheory.V.Sd
