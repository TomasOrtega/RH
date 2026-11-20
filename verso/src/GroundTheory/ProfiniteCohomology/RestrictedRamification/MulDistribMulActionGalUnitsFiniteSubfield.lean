import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Unramified
import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflation
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolUnramified
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.CupProducts
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield
  GroundTheory.Global.SemiLocal groupCohomology

open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section CoboundaryUnits

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra Kv Ωv] [IsGalois Kv Ωv]

/- English proof (translation)
Establish `hw_loc : IsLocallyConstant (fun g : Fin 1 → Gal(Ωv/Kv) => Additive.ofMul (b (g 0)))` using `(hb.comp_continuous (continuous_apply 0)).comp Additive.ofMul`. Establish `hzw : z = (cochainsComplex (galUnits.{0} Kv Ωv)).toCycles 1 2 (mkCochain _ _ hw_loc)`. Apply `cocycleι_injective` to reduce the goal to its premises. Apply `cochainOf_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `u`.

Establish `h1` using `congrFun (cochainOf_cocycleι_toCycles (A := galUnits.{0} Kv Ωv) (i := 1) (mkCochain _ _ hw_loc)) u`. Use `(hz u).trans (Eq.trans ?_ h1.symm)` and prove the remaining obligations. Rewrite using `[cochainOf_mkCochain, inhomogeneousCochains_d_one_apply, galUnits_ρ_apply]`. Both sides reduce to the same expression. Rewrite using `[hzw]`.

Conclude with `cohomologyπ_toCycles _ 1 2 _`.
-/
theorem cohomologyπ_galUnits_eq_zero_of_coboundary (z : cocycles (galUnits.{0} Kv Ωv) 2)
    (b : Gal(Ωv/Kv) → Ωvˣ) (hb : IsLocallyConstant b)
    (hz : ∀ u : Fin 2 → Gal(Ωv/Kv), cochainOf _ (cocycleι _ 2 z) u =
      Additive.ofMul (galUnitsHom Kv Ωv (u 0) (b (u 1)) / b (u 0 * u 1) * b (u 0))) :
    cohomologyπ _ 2 z = 0 := by
  have hw_loc : IsLocallyConstant (fun g : Fin 1 → Gal(Ωv/Kv) => Additive.ofMul (b (g 0))) :=
    (hb.comp_continuous (continuous_apply 0)).comp Additive.ofMul
  have hzw : z = (cochainsComplex (galUnits.{0} Kv Ωv)).toCycles 1 2 (mkCochain _ _ hw_loc) := by
    apply cocycleι_injective
    apply cochainOf_injective
    funext u
    have h1 := congrFun (cochainOf_cocycleι_toCycles (A := galUnits.{0} Kv Ωv) (i := 1)
      (mkCochain _ _ hw_loc)) u
    refine (hz u).trans (Eq.trans ?_ h1.symm)
    rw [cochainOf_mkCochain, inhomogeneousCochains_d_one_apply, galUnits_ρ_apply]
    rfl
  rw [hzw]
  exact cohomologyπ_toCycles _ 1 2 _

omit [IsGalois Kv Ωv] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toMul_galUnitsZ_coboundary (σ : Gal(Ωv/Kv)) (a b c : Additive Ωvˣ) :
    Additive.toMul ((galUnitsZ Kv Ωv).ρ σ a - b + c) =
      σ • Additive.toMul a / Additive.toMul b * Additive.toMul c :=
  rfl

end CoboundaryUnits

section ClassZero

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨w, hw⟩` from `(homologyπ_eq_zero_iff (cochainsComplex A) z).1 hz`. Establish `e : (ComplexShape.up ℕ).prev 2 = 1` using `CochainComplex.prev_nat_succ 1`. Set `w₁` to `((cochainsComplex A).XIsoOfEq e).hom.hom w`.

Establish `hw₁ : ((cochainsComplex A).d 1 2).hom w₁ = ((cochainsComplex A).iCycles 2).hom z`. Rewrite using `[← hw]`. Conclude with `congrArg (fun φ => φ.hom w) ((cochainsComplex A).XIsoOfEq_hom_comp_d e 2)`. Use `⟨cochainOf A w₁, isLocallyConstant_cochainOf w₁, fun u => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (cochainOf A) hw₁`.

Rewrite `h1` using `[cochainOf_d]`. Establish `h2` using `congrFun h1 u`. Rewrite `h2` using `[inhomogeneousCochains_d_one_apply]`. Conclude with `h2.symm`. Introduce and unpack `⟨w, hw, hwz⟩`.

Establish `hzw : z = (cochainsComplex A).toCycles 1 2 (mkCochain A w hw)`. Apply `cocycleι_injective` to reduce the goal to its premises. Apply `cochainOf_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Rewrite using `[hwz u, cochainOf_cocycleι_toCycles, cochainOf_mkCochain, inhomogeneousCochains_d_one_apply]`.

Rewrite using `[hzw]`. Conclude with `cohomologyπ_toCycles A 1 2 _`.
-/
theorem cohomologyπ_two_eq_zero_iff_locallyConstant (z : cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ w : (Fin 1 → G) → A, IsLocallyConstant w ∧
      ∀ u : Fin 2 → G, cochainOf A (cocycleι A 2 z) u =
        A.ρ (u 0) (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0) := by
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff (cochainsComplex A) z).1 hz
    have e : (ComplexShape.up ℕ).prev 2 = 1 := CochainComplex.prev_nat_succ 1
    let w₁ := ((cochainsComplex A).XIsoOfEq e).hom.hom w
    have hw₁ : ((cochainsComplex A).d 1 2).hom w₁ = ((cochainsComplex A).iCycles 2).hom z := by
      rw [← hw]
      exact congrArg (fun φ => φ.hom w) ((cochainsComplex A).XIsoOfEq_hom_comp_d e 2)
    refine ⟨cochainOf A w₁, isLocallyConstant_cochainOf w₁, fun u => ?_⟩
    have h1 := congrArg (cochainOf A) hw₁
    rw [cochainOf_d] at h1
    have h2 := congrFun h1 u
    rw [inhomogeneousCochains_d_one_apply] at h2
    exact h2.symm
  · rintro ⟨w, hw, hwz⟩
    have hzw : z = (cochainsComplex A).toCycles 1 2 (mkCochain A w hw) := by
      apply cocycleι_injective
      apply cochainOf_injective
      funext u
      rw [hwz u, cochainOf_cocycleι_toCycles, cochainOf_mkCochain, inhomogeneousCochains_d_one_apply]
    rw [hzw]
    exact cohomologyπ_toCycles A 1 2 _

end ClassZero

section DTwo

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/- English proof (translation)
Rewrite using `[inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]`. Establish `h0 : Fin.contractNth (0 : Fin 3) (· * ·) u = ![u 0 * u 1, u 2]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl`.

Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]; rfl`. Establish `h1 : Fin.contractNth (1 : Fin 3) (· * ·) u = ![u 0, u 1 * u 2]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl`.

Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl`. Establish `h2 : Fin.contractNth (2 : Fin 3) (· * ·) u = ![u 0, u 1]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl`.

Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl`. Establish `h3 : (fun i : Fin 2 => u i.succ) = ![u 1, u 2]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[h0, h1, h2, h3]`.

Simplify using `only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, neg_smul, one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow]`. Establish `: ((-1 : k) ^ 3) = -1` using `by norm_num`. Rewrite using `[this, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem inhomogeneousCochains_d_two_apply' (f : (Fin 2 → G) → A) (u : Fin 3 → G) :
    (inhomogeneousCochains.d A 2).hom f u =
      A.ρ (u 0) (f ![u 1, u 2]) - f ![u 0 * u 1, u 2] + f ![u 0, u 1 * u 2] - f ![u 0, u 1] := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]
  have h0 : Fin.contractNth (0 : Fin 3) (· * ·) u = ![u 0 * u 1, u 2] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]; rfl
  have h1 : Fin.contractNth (1 : Fin 3) (· * ·) u = ![u 0, u 1 * u 2] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
  have h2 : Fin.contractNth (2 : Fin 3) (· * ·) u = ![u 0, u 1] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  have h3 : (fun i : Fin 2 => u i.succ) = ![u 1, u 2] := by
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, neg_smul, one_smul,
    Nat.reduceAdd, even_two, Even.neg_pow, one_pow]
  have : ((-1 : k) ^ 3) = -1 := by norm_num
  rw [this, neg_smul, one_smul]
  abel

end DTwo

section Level

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [Normal K.1 F.1]

/- English proof (translation)
Use `set τ := decompHom (v.adicCompletion K.1) (embedLevel ι F) σ`. Use `set w₀ := placeOfEmbedding ι F`. Establish `hu : w₀.1 = τ • (τ⁻¹ • w₀).1` using `eq_smul_inv_smul v τ w₀`. Set `j` to `σ.symm.toAlgHom.comp ((completionEmbedding ι F).comp (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu).toAlgHom)`. Establish `hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x`.

Introduce `x`. Express the relevant statement in the definitionally equal form `σ.symm (completionEmbedding ι F (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu (algebraMap F.1 _ x))) = ι x`. Rewrite using `[galEquiv_algebraMap, completionEmbedding_algebraMap]`. Establish `h` using `decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x`. Rewrite `h` using `[embedLevel_apply, embedLevel_apply]`.

Rewrite using `[h, AlgEquiv.symm_apply_apply]`. Establish `h` using `eq_placeOfEmbedding ι F j hj`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decompHom_smul_placeOfEmbedding'
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHom (v.adicCompletion K.1) (embedLevel ι F) σ • placeOfEmbedding ι F =
      placeOfEmbedding ι F := by
  set τ := decompHom (v.adicCompletion K.1) (embedLevel ι F) σ
  set w₀ := placeOfEmbedding ι F
  have hu : w₀.1 = τ • (τ⁻¹ • w₀).1 := eq_smul_inv_smul v τ w₀
  let j := σ.symm.toAlgHom.comp
    ((completionEmbedding ι F).comp (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu).toAlgHom)
  have hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x := by
    intro x
    change σ.symm (completionEmbedding ι F (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu
      (algebraMap F.1 _ x))) = ι x
    rw [galEquiv_algebraMap, completionEmbedding_algebraMap]
    have h := decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x
    rw [embedLevel_apply, embedLevel_apply] at h
    rw [h, AlgEquiv.symm_apply_apply]
  have h := eq_placeOfEmbedding ι F j hj
  calc τ • w₀ = τ • (τ⁻¹ • w₀) := by rw [h]
    _ = w₀ := smul_inv_smul τ w₀

def placeDecompHom :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →*
      MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal :=
  (decompHom (v.adicCompletion K.1) (embedLevel ι F)).codRestrict _ fun σ ↦
    MulAction.mem_stabilizer_iff.2
      (congrArg (fun u : PlacesOver F.1 v ↦ u.1.asIdeal) (decompHom_smul_placeOfEmbedding' ι F σ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_placeDecompHom (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    (placeDecompHom ι F σ : Gal(F.1/K.1)) = decompHom (v.adicCompletion K.1) (embedLevel ι F) σ :=
  rfl

/- English proof (translation)
The claim follows from `decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x`.
-/
theorem ι_placeDecompHom_apply
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) (x : F.1) :
    ι ((placeDecompHom ι F σ : Gal(F.1/K.1)) x : F.1) = σ (ι x) :=
  decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x

/- English proof (translation)
The claim follows from `(continuous_decompHom (embedLevel ι F)).subtype_mk _`.
-/
theorem continuous_placeDecompHom : Continuous (placeDecompHom ι F) :=
  (continuous_decompHom (embedLevel ι F)).subtype_mk _

/- English proof (translation)
Establish `: (completionEmbedding ι F).comp (decompositionAlgEquiv v (placeOfEmbedding ι F).1 (placeDecompHom ι F σ)).toAlgHom = σ.toAlgHom.comp (completionEmbedding ι F)`. Apply `algHom_ext_adicCompletion` to reduce the goal to its premises. Introduce `x`. Express the relevant statement in the definitionally equal form `completionEmbedding ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1 (placeDecompHom ι F σ) (algebraMap F.1 _ x)) = σ (completionEmbedding ι F (algebraMap F.1 _ x))`. Rewrite using `[decompositionAlgEquiv_algebraMap, completionEmbedding_algebraMap, completionEmbedding_algebraMap, ι_placeDecompHom_apply]`.

Conclude with `DFunLike.congr_fun this y`.
-/
theorem completionEmbedding_placeDecompHom_smul
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    completionEmbedding ι F (placeDecompHom ι F σ • y) = σ (completionEmbedding ι F y) := by
  have : (completionEmbedding ι F).comp
      (decompositionAlgEquiv v (placeOfEmbedding ι F).1 (placeDecompHom ι F σ)).toAlgHom =
      σ.toAlgHom.comp (completionEmbedding ι F) := by
    apply algHom_ext_adicCompletion
    intro x
    change completionEmbedding ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1
      (placeDecompHom ι F σ) (algebraMap F.1 _ x)) = σ (completionEmbedding ι F (algebraMap F.1 _ x))
    rw [decompositionAlgEquiv_algebraMap, completionEmbedding_algebraMap,
      completionEmbedding_algebraMap, ι_placeDecompHom_apply]
  exact DFunLike.congr_fun this y

section CompField

@[irreducible]
def compField : IntermediateField (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
  (completionEmbedding ι F).fieldRange

omit [Normal K.1 F.1] in
/- English proof (translation)
Use `with_unfolding_all rfl`.
-/
theorem compField_def : compField ι F = (completionEmbedding ι F).fieldRange := by
  with_unfolding_all rfl

def compEquiv : (placeOfEmbedding ι F).1.adicCompletion F.1 ≃ₐ[v.adicCompletion K.1] compField ι F :=
  (AlgEquiv.ofInjectiveField (completionEmbedding ι F)).trans
    (IntermediateField.equivOfEq (compField_def ι F).symm)

omit [Normal K.1 F.1] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_compEquiv_apply (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    ((compEquiv ι F y : compField ι F) : AlgebraicClosure (v.adicCompletion K.1)) =
      completionEmbedding ι F y :=
  rfl

instance finiteDimensional_compField : FiniteDimensional (v.adicCompletion K.1) (compField ι F) :=
  have : Module.Finite (v.adicCompletion K.1) ((placeOfEmbedding ι F).1.adicCompletion F.1) :=
    finite_adicCompletion v (placeOfEmbedding ι F).1
  LinearEquiv.finiteDimensional (compEquiv ι F).toLinearEquiv

instance isGalois_finiteSubfield_of_normal : IsGalois K.1 F.1 := ⟨⟩

instance normal_compField : Normal (v.adicCompletion K.1) (compField ι F) :=
  have : IsGalois (v.adicCompletion K.1) ((placeOfEmbedding ι F).1.adicCompletion F.1) :=
    isGalois_adicCompletion v (placeOfEmbedding ι F).1
  Normal.of_algEquiv (compEquiv ι F)

omit [Normal K.1 F.1] in
/- English proof (translation)
Rewrite using `[compField_def]`. Conclude with `⟨algebraMap F.1 _ x, completionEmbedding_algebraMap ι F x⟩`.
-/
theorem ι_mem_compField (x : F.1) : ι x ∈ compField ι F := by
  rw [compField_def]
  exact ⟨algebraMap F.1 _ x, completionEmbedding_algebraMap ι F x⟩

def embedComp : F.1 →ₐ[K.1] compField ι F where
  toFun x := ⟨ι x, ι_mem_compField ι F x⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' x y := Subtype.ext (map_mul ι (x : ℚ̄) y)
  map_zero' := Subtype.ext (map_zero ι)
  map_add' x y := Subtype.ext (map_add ι (x : ℚ̄) y)
  commutes' a := Subtype.ext (ι.commutes a)

omit [Normal K.1 F.1] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_embedComp_apply (x : F.1) :
    ((embedComp ι F x : compField ι F) : AlgebraicClosure (v.adicCompletion K.1)) = ι x :=
  rfl

end CompField

end Level

section Inflation

variable {G Γ : Type} [Group G] [TopologicalSpace G] [CompactSpace G] [Group Γ]

/- English proof (translation)
Establish `h1 : ∀ σ, β (r σ, 1) = h 1`. Introduce `σ`. Use `hβ σ 1` as an intermediate fact. Rewrite `this` using `[map_one, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmul : ∀ σ n, r n = 1 → h (σ * n) = h σ + h n - h 1`. Introduce `σ n hn`. Use `hβ σ n` as an intermediate fact. Rewrite `this` using `[hn, h1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfin : (Set.range h).Finite` using `hh.range_finite`. Establish `hk : ∀ n, r n = 1 → h n = h 1`. Introduce `n hn`. Establish `hpow : ∀ m : ℕ, h (n ^ m) - h 1 = m * (h n - h 1)`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, hmul _ _ hn]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hne`. Establish `hne' : h n - h 1 ≠ 0` using `sub_ne_zero.2 hne`. Establish `hinj : Function.Injective fun m : ℕ => h (n ^ m)`. Introduce `m m' hmm`.

Establish `e1` using `hpow m`. Establish `e2` using `hpow m'`. Simplify using `only at hmm`. Rewrite `e1` using `[hmm]`. Establish `: (m : ℤ) * (h n - h 1) = m' * (h n - h 1)` using `by rw [← e1, ← e2]`.

Conclude with `mul_right_cancel₀ hne' this` after adjusting the coercions. Conclude with `Set.infinite_range_of_injective hinj (hfin.subset (Set.range_comp_subset_range _ _))`. Establish `hconst : ∀ σ n, r n = 1 → h (σ * n) = h σ`. Introduce `σ n hn`. Rewrite using `[hmul σ n hn, hk n hn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfac : ∀ σ σ', r σ = r σ' → h σ = h σ'`. Introduce `σ σ' he`. Establish `hn : r (σ⁻¹ * σ') = 1` using `by rw [map_mul, map_inv, he, inv_mul_cancel]`. Rewrite using `[← hconst σ (σ⁻¹ * σ') hn, mul_inv_cancel_left]`.

Use `choose s hs using hr`. Use `⟨fun a => h (s a), fun a b => ?_⟩` and prove the remaining obligations. Use `hβ (s a) (s b)` as an intermediate fact. Rewrite `this` using `[hs a, hs b]`. Rewrite using `[← this]`.

Use `show h (s b) - h (s (a * b)) + h (s a) = _`. Rewrite using `[hfac (s (a * b)) (s a * s b) (by rw [map_mul, hs, hs, hs])]`.
-/
theorem exists_int_coboundary_of_surjective (r : G →* Γ) (hr : Function.Surjective r)
    (β : Γ × Γ → ℤ) (h : G → ℤ) (hh : IsLocallyConstant h)
    (hβ : ∀ σ τ, h τ - h (σ * τ) + h σ = β (r σ, r τ)) :
    ∃ g : Γ → ℤ, ∀ a b, g b - g (a * b) + g a = β (a, b) := by

  have h1 : ∀ σ, β (r σ, 1) = h 1 := by
    intro σ
    have := hβ σ 1
    rw [map_one, mul_one] at this
    linarith
  have hmul : ∀ σ n, r n = 1 → h (σ * n) = h σ + h n - h 1 := by
    intro σ n hn
    have := hβ σ n
    rw [hn, h1] at this
    linarith

  have hfin : (Set.range h).Finite := hh.range_finite
  have hk : ∀ n, r n = 1 → h n = h 1 := by
    intro n hn
    have hpow : ∀ m : ℕ, h (n ^ m) - h 1 = m * (h n - h 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, hmul _ _ hn]
        push_cast
        linarith
    by_contra hne
    have hne' : h n - h 1 ≠ 0 := sub_ne_zero.2 hne
    have hinj : Function.Injective fun m : ℕ => h (n ^ m) := by
      intro m m' hmm
      have e1 := hpow m
      have e2 := hpow m'
      simp only at hmm
      rw [hmm] at e1
      have : (m : ℤ) * (h n - h 1) = m' * (h n - h 1) := by rw [← e1, ← e2]
      exact_mod_cast mul_right_cancel₀ hne' this
    exact Set.infinite_range_of_injective hinj (hfin.subset (Set.range_comp_subset_range _ _))
  have hconst : ∀ σ n, r n = 1 → h (σ * n) = h σ := by
    intro σ n hn
    rw [hmul σ n hn, hk n hn]
    ring
  have hfac : ∀ σ σ', r σ = r σ' → h σ = h σ' := by
    intro σ σ' he
    have hn : r (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [← hconst σ (σ⁻¹ * σ') hn, mul_inv_cancel_left]
  choose s hs using hr
  refine ⟨fun a => h (s a), fun a b => ?_⟩
  have := hβ (s a) (s b)
  rw [hs a, hs b] at this
  rw [← this]
  show h (s b) - h (s (a * b)) + h (s a) = _
  rw [hfac (s (a * b)) (s a * s b) (by rw [map_mul, hs, hs, hs])]

end Inflation

section UnitsVanish

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

open AdicLiesOver

include v in

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `v.valuation_exists_uniformizer K`. Use `set π0 : w.adicCompletion L := algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) with hπ0def`. Establish `hπv : Valued.v π0 = WithZero.exp (-1)`. Rewrite using `[hπ0def, show algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) = ((algebraMap K L ϖ : L) : w.adicCompletion L) from rfl, w.valuedAdicCompletion_eq_valuation', ← HeightOneSpectrum.valuation_liesOver L v w ϖ, Ideal.ramificationIdx'_eq_ramificationIdx' v.asIdeal w.asIdeal (Ideal …`. Establish `hπ0 : π0 ≠ 0`.

Introduce `h`. Rewrite `hπv` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hπv.symm`. Use `set π : (w.adicCompletion L)ˣ := Units.mk0 π0 hπ0`. Establish `hπinv : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) (n : ℤ), a • π ^ n = π ^ n`.

Introduce `a n`. Rewrite using `[smul_zpow']`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Use `show decompositionAlgEquiv v w a π0 = π0`.

Rewrite using `[hπ0def, decompositionAlgEquiv_algebraMap, AlgEquiv.commutes]`. Establish `hπpow : ∀ n : ℤ, Valued.v (((π ^ n : (w.adicCompletion L)ˣ)) : w.adicCompletion L) = WithZero.exp (-n)`. Introduce `n`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀]`. Express the relevant statement in the definitionally equal form `Valued.v π0 ^ n = _`.

Rewrite using `[hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]`. Take `⟨e, he_def⟩ : ∃ e : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal → ℤ, e = fun p => g p.2 - g (p.1 * p.2) + g p.1` from `⟨_, rfl⟩`. Establish `he_ab : ∀ a b, e (a, b) = g b - g (a * b) + g a` using `by intro a b; rw [he_def]`. Establish `he_cocycle : ∀ a b c, e (a * b, c) + e (a, b) = e (b, c) + e (a, b * c)`. Introduce `a b c`.

Rewrite using `[he_ab, he_ab, he_ab, he_ab, mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨α₁, hα₁_def⟩ : ∃ α₁ : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal → (w.adicCompletion L)ˣ, α₁ = fun p => α p * π ^ (-e p)` from `⟨_, rfl⟩`. Establish `hα₁_ab : ∀ p, α₁ p = α p * π ^ (-e p)` using `by intro p; rw [hα₁_def]`. Establish `hv₁ : ∀ p, Valued.v (α₁ p : w.adicCompletion L) = 1`.

Introduce and unpack `⟨a, b⟩`. Rewrite using `[hα₁_ab, Units.val_mul, map_mul, hg a b, hπpow, neg_neg, he_ab, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]`. Establish `hα₁ : IsMulCocycle₂ α₁`. Introduce `a b c`. Rewrite using `[hα₁_ab, hα₁_ab, hα₁_ab, hα₁_ab, smul_mul', hπinv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[neg_add, zpow_add, mul_mul_mul_comm]`. Use `_ = (a • α (b, c) * α (a, b * c)) * π ^ (-(e (b, c) + e (a, b * c))) := by`. Rewrite using `[hα a b c, he_cocycle]`. Use `_ = a • α (b, c) * π ^ (-e (b, c)) * (α (a, b * c) * π ^ (-e (a, b * c))) := by`.

Rewrite using `[neg_add, zpow_add, mul_mul_mul_comm]`. Establish `hmem : ∀ p, (α₁ p : w.adicCompletion L) ∈ w.adicCompletionIntegers L` using `fun p => (HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (hv₁ p).le`. Establish `hmem' : ∀ p, (((α₁ p)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ w.adicCompletionIntegers L`. Introduce `p`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hv₁ p, inv_one]`. Set `u : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal → (w.adicCompletionIntegers L)ˣ` to `fun p => ⟨⟨α₁ p, hmem p⟩, ⟨((α₁ p)⁻¹ : (w.adicCompletion L)ˣ), hmem' p⟩, Subtype.ext (Units.mul_inv (α₁ p)), Subtype.ext (Units.inv_mul (α₁ p))⟩`. Set `toFw : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ` to `Units.map (w.adicCompletionIntegers L).subtype.toMonoidHom`. Establish `htoFw_inj : Function.Injective toFw` using `fun x y h => Units.ext (Subtype.ext (congrArg Units.val h))`. Establish `htoFw_smul : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) y, toFw (a • y) = a • toFw y` using `fun _ _ => rfl`.

Establish `hu_coe : ∀ p, toFw (u p) = α₁ p` using `fun p => Units.ext rfl`. Establish `hu : IsMulCocycle₂ u`. Introduce `a b c`. Apply `htoFw_inj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, htoFw_smul, hu_coe, hu_coe, hu_coe, hu_coe]`.

Conclude with `hα₁ a b c`. Establish `hz` using `isZero_groupCohomology_decomposition_integerUnits v w he (n := 2) (by norm_num)`. Establish `h0 : (ConcreteCategory.hom (groupCohomology.H2π (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ))) (groupCohomology.cocyclesOfIsMulCocycle₂ hu) = 0` using `(ModuleCat.isZero_iff_subsingleton.1 hz).elim _ _`. Rewrite `h0` using `[groupCohomology.H2π_eq_zero_iff]`. Take `⟨x, hx⟩` from `groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ _ h0`.

Use `⟨fun a => toFw (x a) * π ^ g a, fun a b => ?_⟩` and prove the remaining obligations. Establish `hxab : a • x b / x (a * b) * x a = u (a, b)` using `hx a b`. Establish `hxab'` using `congrArg toFw hxab`. Rewrite `hxab'` using `[map_mul, map_div, htoFw_smul, hu_coe, hα₁_ab]`. Simplify using `only [smul_mul', hπinv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[he_ab]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_zpow, add_zsmul, sub_zsmul]`. Normalize the expressions using the abelian group laws.

Use `_ = α (a, b) := by`. Rewrite using `[hxab', mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]`.
-/
theorem isMulCoboundary₂_of_valuation (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (α : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal →
      (w.adicCompletion L)ˣ) (hα : IsMulCocycle₂ α)
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal → ℤ)
    (hg : ∀ a b, Valued.v (α (a, b) : w.adicCompletion L) = WithZero.exp (-(g b - g (a * b) + g a))) :
    IsMulCoboundary₂ α := by
  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
  set π0 : w.adicCompletion L := algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) with hπ0def
  have hπv : Valued.v π0 = WithZero.exp (-1) := by
    rw [hπ0def, show algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) =
      ((algebraMap K L ϖ : L) : w.adicCompletion L) from rfl, w.valuedAdicCompletion_eq_valuation',
      ← HeightOneSpectrum.valuation_liesOver L v w ϖ, Ideal.ramificationIdx'_eq_ramificationIdx' v.asIdeal w.asIdeal
        (Ideal.map_ne_bot_of_ne_bot v.ne_bot), he, pow_one, hϖ]
  have hπ0 : π0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  set π : (w.adicCompletion L)ˣ := Units.mk0 π0 hπ0
  have hπinv : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) (n : ℤ), a • π ^ n = π ^ n := by
    intro a n
    rw [smul_zpow']
    congr 1
    apply Units.ext
    show decompositionAlgEquiv v w a π0 = π0
    rw [hπ0def, decompositionAlgEquiv_algebraMap, AlgEquiv.commutes]
  have hπpow : ∀ n : ℤ, Valued.v (((π ^ n : (w.adicCompletion L)ˣ)) : w.adicCompletion L) =
      WithZero.exp (-n) := by
    intro n
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    change Valued.v π0 ^ n = _
    rw [hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

  obtain ⟨e, he_def⟩ : ∃ e : MulAction.stabilizer Gal(L/K) w.asIdeal ×
      MulAction.stabilizer Gal(L/K) w.asIdeal → ℤ, e = fun p => g p.2 - g (p.1 * p.2) + g p.1 :=
    ⟨_, rfl⟩
  have he_ab : ∀ a b, e (a, b) = g b - g (a * b) + g a := by intro a b; rw [he_def]
  have he_cocycle : ∀ a b c, e (a * b, c) + e (a, b) = e (b, c) + e (a, b * c) := by
    intro a b c
    rw [he_ab, he_ab, he_ab, he_ab, mul_assoc]
    ring

  obtain ⟨α₁, hα₁_def⟩ : ∃ α₁ : MulAction.stabilizer Gal(L/K) w.asIdeal ×
      MulAction.stabilizer Gal(L/K) w.asIdeal → (w.adicCompletion L)ˣ,
      α₁ = fun p => α p * π ^ (-e p) := ⟨_, rfl⟩
  have hα₁_ab : ∀ p, α₁ p = α p * π ^ (-e p) := by intro p; rw [hα₁_def]
  have hv₁ : ∀ p, Valued.v (α₁ p : w.adicCompletion L) = 1 := by
    rintro ⟨a, b⟩
    rw [hα₁_ab, Units.val_mul, map_mul, hg a b, hπpow, neg_neg, he_ab, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  have hα₁ : IsMulCocycle₂ α₁ := by
    intro a b c
    rw [hα₁_ab, hα₁_ab, hα₁_ab, hα₁_ab, smul_mul', hπinv]
    calc α (a * b, c) * π ^ (-e (a * b, c)) * (α (a, b) * π ^ (-e (a, b)))
        = (α (a * b, c) * α (a, b)) * π ^ (-(e (a * b, c) + e (a, b))) := by
          rw [neg_add, zpow_add, mul_mul_mul_comm]
      _ = (a • α (b, c) * α (a, b * c)) * π ^ (-(e (b, c) + e (a, b * c))) := by
          rw [hα a b c, he_cocycle]
      _ = a • α (b, c) * π ^ (-e (b, c)) * (α (a, b * c) * π ^ (-e (a, b * c))) := by
          rw [neg_add, zpow_add, mul_mul_mul_comm]
  have hmem : ∀ p, (α₁ p : w.adicCompletion L) ∈ w.adicCompletionIntegers L := fun p =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (hv₁ p).le
  have hmem' : ∀ p, (((α₁ p)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈
      w.adicCompletionIntegers L := by
    intro p
    refine (HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (le_of_eq ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv₁ p, inv_one]
  let u : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal →
      (w.adicCompletionIntegers L)ˣ := fun p =>
    ⟨⟨α₁ p, hmem p⟩, ⟨((α₁ p)⁻¹ : (w.adicCompletion L)ˣ), hmem' p⟩,
      Subtype.ext (Units.mul_inv (α₁ p)), Subtype.ext (Units.inv_mul (α₁ p))⟩
  let toFw : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map (w.adicCompletionIntegers L).subtype.toMonoidHom
  have htoFw_inj : Function.Injective toFw := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  have htoFw_smul : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) y, toFw (a • y) = a • toFw y :=
    fun _ _ => rfl
  have hu_coe : ∀ p, toFw (u p) = α₁ p := fun p => Units.ext rfl
  have hu : IsMulCocycle₂ u := by
    intro a b c
    apply htoFw_inj
    rw [map_mul, map_mul, htoFw_smul, hu_coe, hu_coe, hu_coe, hu_coe]
    exact hα₁ a b c

  have hz := isZero_groupCohomology_decomposition_integerUnits v w he (n := 2) (by norm_num)
  have h0 : (ConcreteCategory.hom (groupCohomology.H2π
      (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.adicCompletionIntegers L)ˣ))) (groupCohomology.cocyclesOfIsMulCocycle₂ hu) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 hz).elim _ _
  rw [groupCohomology.H2π_eq_zero_iff] at h0
  obtain ⟨x, hx⟩ := groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ _ h0
  refine ⟨fun a => toFw (x a) * π ^ g a, fun a b => ?_⟩
  have hxab : a • x b / x (a * b) * x a = u (a, b) := hx a b
  have hxab' := congrArg toFw hxab
  rw [map_mul, map_div, htoFw_smul, hu_coe, hα₁_ab] at hxab'
  simp only [smul_mul', hπinv]
  calc a • toFw (x b) * π ^ g b / (toFw (x (a * b)) * π ^ g (a * b)) * (toFw (x a) * π ^ g a)
      = (a • toFw (x b) / toFw (x (a * b)) * toFw (x a)) * π ^ e (a, b) := by
        rw [he_ab]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_zpow, add_zsmul, sub_zsmul]
        abel
    _ = α (a, b) := by
        rw [hxab', mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

end UnitsVanish

section Main

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [Normal K.1 F.1]

set_option synthInstance.maxHeartbeats 400000 in
instance mulDistribMulAction_gal_units_finiteSubfield :
    MulDistribMulAction Gal(F.1/K.1) F.1ˣ :=
  AlgEquiv.instMulDistribMulActionUnits

def ordPlace (f : F.1ˣ) : ℤ :=
  -WithZero.log ((placeOfEmbedding ι F).1.valuation F.1 (f : F.1))

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `d`. Take `⟨τ, hτ⟩ : ∃ τ : compField ι F ≃ₐ[v.adicCompletion K.1] compField ι F, ∀ y, τ y = compEquiv ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm y))` from `⟨(compEquiv ι F).symm.trans ((decompositionAlgEquiv v (placeOfEmbedding ι F).1 d).trans (compEquiv ι F)), fun _ => rfl⟩`. Use `⟨τ.liftNormal (AlgebraicClosure (v.adicCompletion K.1)), Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_placeDecompHom, decompHom_eq_iff]`. Introduce `x`.

Establish `e : ∀ y : F.1, embedLevel ι F y = algebraMap (compField ι F) (AlgebraicClosure (v.adicCompletion K.1)) (compEquiv ι F (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) y))`. Introduce `y`. Rewrite using `[IntermediateField.algebraMap_apply, coe_compEquiv_apply, completionEmbedding_algebraMap, embedLevel_apply]`. Rewrite using `[e, e, AlgEquiv.liftNormal_commutes, hτ, AlgEquiv.symm_apply_apply, decompositionAlgEquiv_algebraMap]`.
-/
theorem placeDecompHom_surjective : Function.Surjective (placeDecompHom ι F) := by
  intro d
  obtain ⟨τ, hτ⟩ : ∃ τ : compField ι F ≃ₐ[v.adicCompletion K.1] compField ι F, ∀ y,
      τ y = compEquiv ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm y)) :=
    ⟨(compEquiv ι F).symm.trans ((decompositionAlgEquiv v (placeOfEmbedding ι F).1 d).trans
      (compEquiv ι F)), fun _ => rfl⟩
  refine ⟨τ.liftNormal (AlgebraicClosure (v.adicCompletion K.1)), Subtype.ext ?_⟩
  rw [coe_placeDecompHom, decompHom_eq_iff]
  intro x
  have e : ∀ y : F.1, embedLevel ι F y = algebraMap (compField ι F) (AlgebraicClosure (v.adicCompletion K.1))
      (compEquiv ι F (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) y)) := by
    intro y
    rw [IntermediateField.algebraMap_apply, coe_compEquiv_apply, completionEmbedding_algebraMap,
      embedLevel_apply]
  rw [e, e, AlgEquiv.liftNormal_commutes, hτ, AlgEquiv.symm_apply_apply,
    decompositionAlgEquiv_algebraMap]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `: CompactSpace Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)` using `galois_compactSpace _ _`. Take `⟨g, hg⟩` from `exists_int_coboundary_of_surjective (placeDecompHom ι F) (placeDecompHom_surjective ι F) (fun p => ordPlace ι F (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))) h hh (fun σ τ => hhc σ τ)`. Set `alg : F.1ˣ →* ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ` to `Units.map (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1)).toMonoidHom`. Establish `halg_smul : ∀ (a : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal) y, alg ((a : Gal(F.1/K.1)) • y) = a • alg y`. Introduce `a y`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap F.1 _ ((a : Gal(F.1/K.1)) (y : F.1)) = decompositionAlgEquiv v (placeOfEmbedding ι F).1 a (algebraMap F.1 _ (y : F.1))`. Rewrite using `[decompositionAlgEquiv_algebraMap]`. Set `α : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal × MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal → ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ` to `fun p => alg (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))`. Establish `hα : IsMulCocycle₂ α`.

Introduce `a b d`. Use `congrArg alg (hc a b d)` as an intermediate fact. Simplify using `only [map_mul, halg_smul] at this`. Conclude with `this`. Establish `hval : ∀ y : F.1ˣ, Valued.v ((alg y : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) : (placeOfEmbedding ι F).1.adicCompletion F.1) = WithZero.exp (-ordPlace ι F y)`.

Introduce `y`. Express the relevant statement in the definitionally equal form `Valued.v ((y : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1) = _`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ordPlace, neg_neg, WithZero.exp_log]`. Conclude with `(map_ne_zero _).2 y.ne_zero`. Establish `hg' : ∀ a b, Valued.v (α (a, b) : (placeOfEmbedding ι F).1.adicCompletion F.1) = WithZero.exp (-(g b - g (a * b) + g a))`.

Introduce `a b`. Rewrite using `[hval, hg a b]`. Take `⟨β, hβ⟩` from `isMulCoboundary₂_of_valuation v (placeOfEmbedding ι F).1 he α hα g hg'`. Set `j : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ →* (AlgebraicClosure (v.adicCompletion K.1))ˣ` to `Units.map (completionEmbedding ι F).toRingHom.toMonoidHom`. Establish `hj_smul : ∀ σ y, σ • j y = j (placeDecompHom ι F σ • y)`.

Introduce `σ y`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(completionEmbedding_placeDecompHom_smul ι F σ (y : (placeOfEmbedding ι F).1.adicCompletion F.1)).symm`. Use `⟨fun σ => j (β (placeDecompHom ι F σ)), (IsLocallyConstant.of_discrete (fun d => j (β d))).comp_continuous (continuous_placeDecompHom ι F), fun σ τ => ?_⟩` and prove the remaining obligations. Rewrite using `[hj_smul, ← map_div, ← map_mul, map_mul (placeDecompHom ι F), hβ]`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `completionEmbedding ι F (algebraMap F.1 _ _) = _`. Rewrite using `[completionEmbedding_algebraMap]`. Both sides reduce to the same expression.
-/
theorem exists_mulCoboundary_of_ord (he : (placeOfEmbedding ι F).1.asIdeal.ramificationIdx (𝓞 K.1) = 1)
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (h : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) → ℤ) (hh : IsLocallyConstant h)
    (hhc : ∀ σ τ, h τ - h (σ * τ) + h σ = ordPlace ι F
      (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
        (AlgebraicClosure (v.adicCompletion K.1))ˣ,
      IsLocallyConstant b ∧ ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
        Units.map (embedLevel ι F).toRingHom.toMonoidHom
          (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
            decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  have : CompactSpace Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) :=
    galois_compactSpace _ _

  obtain ⟨g, hg⟩ := exists_int_coboundary_of_surjective (placeDecompHom ι F)
    (placeDecompHom_surjective ι F)
    (fun p => ordPlace ι F (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))) h hh (fun σ τ => hhc σ τ)

  let alg : F.1ˣ →* ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ :=
    Units.map (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1)).toMonoidHom
  have halg_smul : ∀ (a : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal) y,
      alg ((a : Gal(F.1/K.1)) • y) = a • alg y := by
    intro a y
    apply Units.ext
    change algebraMap F.1 _ ((a : Gal(F.1/K.1)) (y : F.1)) =
      decompositionAlgEquiv v (placeOfEmbedding ι F).1 a (algebraMap F.1 _ (y : F.1))
    rw [decompositionAlgEquiv_algebraMap]
  let α : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal ×
      MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal →
      ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ :=
    fun p => alg (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))
  have hα : IsMulCocycle₂ α := by
    intro a b d
    have := congrArg alg (hc a b d)
    simp only [map_mul, halg_smul] at this
    exact this
  have hval : ∀ y : F.1ˣ, Valued.v ((alg y : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) :
      (placeOfEmbedding ι F).1.adicCompletion F.1) = WithZero.exp (-ordPlace ι F y) := by
    intro y
    change Valued.v ((y : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ordPlace, neg_neg, WithZero.exp_log]
    exact (map_ne_zero _).2 y.ne_zero
  have hg' : ∀ a b, Valued.v (α (a, b) : (placeOfEmbedding ι F).1.adicCompletion F.1) =
      WithZero.exp (-(g b - g (a * b) + g a)) := by
    intro a b
    rw [hval, hg a b]
  obtain ⟨β, hβ⟩ := isMulCoboundary₂_of_valuation v (placeOfEmbedding ι F).1 he α hα g hg'

  let j : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ →* (AlgebraicClosure (v.adicCompletion K.1))ˣ :=
    Units.map (completionEmbedding ι F).toRingHom.toMonoidHom
  have hj_smul : ∀ σ y, σ • j y = j (placeDecompHom ι F σ • y) := by
    intro σ y
    apply Units.ext
    exact (completionEmbedding_placeDecompHom_smul ι F σ (y : (placeOfEmbedding ι F).1.adicCompletion F.1)).symm
  refine ⟨fun σ => j (β (placeDecompHom ι F σ)),
    (IsLocallyConstant.of_discrete (fun d => j (β d))).comp_continuous (continuous_placeDecompHom ι F),
    fun σ τ => ?_⟩
  rw [hj_smul, ← map_div, ← map_mul, map_mul (placeDecompHom ι F), hβ]
  apply Units.ext
  change completionEmbedding ι F (algebraMap F.1 _ _) = _
  rw [completionEmbedding_algebraMap]
  rfl

def ordComp (y : Additive (compField ι F)ˣ) : ℤ :=
  -WithZero.log (Valued.v (((compEquiv ι F).symm (y.toMul : compField ι F)) :
    (placeOfEmbedding ι F).1.adicCompletion F.1))

omit [Normal K.1 F.1] in
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Establish `h0 : ∀ z : Additive (compField ι F)ˣ, Valued.v (((compEquiv ι F).symm (z.toMul : compField ι F)) : (placeOfEmbedding ι F).1.adicCompletion F.1) ≠ 0` using `fun z => (map_ne_zero _).2 ((map_ne_zero _).2 (z.toMul).ne_zero)`. Unfold `ordComp`. Rewrite using `[toMul_add, Units.val_mul, map_mul, map_mul, WithZero.log_mul (h0 y) (h0 y'), neg_add]`.
-/
theorem ordComp_add (y y' : Additive (compField ι F)ˣ) :
    ordComp ι F (y + y') = ordComp ι F y + ordComp ι F y' := by
  have h0 : ∀ z : Additive (compField ι F)ˣ, Valued.v (((compEquiv ι F).symm (z.toMul : compField ι F)) :
      (placeOfEmbedding ι F).1.adicCompletion F.1) ≠ 0 := fun z =>
    (map_ne_zero _).2 ((map_ne_zero _).2 (z.toMul).ne_zero)
  unfold ordComp
  rw [toMul_add, Units.val_mul, map_mul, map_mul, WithZero.log_mul (h0 y) (h0 y'), neg_add]

omit [Normal K.1 F.1] in
/- English proof (translation)
Use `ordComp_add ι F y (-y)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel]`. Establish `h1 : ordComp ι F 0 = 0`. Simplify using `[ordComp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ordComp_neg (y : Additive (compField ι F)ˣ) : ordComp ι F (-y) = -ordComp ι F y := by
  have := ordComp_add ι F y (-y)
  rw [add_neg_cancel] at this
  have h1 : ordComp ι F 0 = 0 := by
    simp [ordComp]
  linarith

omit [Normal K.1 F.1] in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ordComp_add, ordComp_neg, ← sub_eq_add_neg]`.
-/
theorem ordComp_sub (y y' : Additive (compField ι F)ˣ) :
    ordComp ι F (y - y') = ordComp ι F y - ordComp ι F y' := by
  rw [sub_eq_add_neg, ordComp_add, ordComp_neg, ← sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨d, hd⟩` from `(decompositionToLocal_bijective v (placeOfEmbedding ι F).1).2 ((compEquiv ι F).trans (γ.trans (compEquiv ι F).symm))`. Establish `key : (compEquiv ι F).symm (γ (y : compField ι F)) = decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm (y : compField ι F))`. Use `DFunLike.congr_fun hd ((compEquiv ι F).symm (y : compField ι F))` as an intermediate fact. Rewrite `this` using `[AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]`. Conclude with `this.symm`.

Simplify using `only [ordComp, toMul_ofMul]`. Express the relevant statement in the definitionally equal form `-WithZero.log (Valued.v ((compEquiv ι F).symm (γ (y : compField ι F)))) = _`. Rewrite using `[key, valued_decompositionAlgEquiv]`.
-/
theorem ordComp_smul (γ : Gal(compField ι F/v.adicCompletion K.1)) (y : (compField ι F)ˣ) :
    ordComp ι F (Additive.ofMul (Units.map (γ : compField ι F →* compField ι F) y)) =
      ordComp ι F (Additive.ofMul y) := by
  obtain ⟨d, hd⟩ := (decompositionToLocal_bijective v (placeOfEmbedding ι F).1).2
    ((compEquiv ι F).trans (γ.trans (compEquiv ι F).symm))
  have key : (compEquiv ι F).symm (γ (y : compField ι F)) =
      decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm (y : compField ι F)) := by
    have := DFunLike.congr_fun hd ((compEquiv ι F).symm (y : compField ι F))
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [ordComp, toMul_ofMul]
  change -WithZero.log (Valued.v ((compEquiv ι F).symm (γ (y : compField ι F)))) = _
  rw [key, valued_decompositionAlgEquiv]

/- English proof (translation)
Establish `h : (compEquiv ι F).symm (embedComp ι F (f : F.1)) = algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) (f : F.1)`. Apply `(compEquiv ι F).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_compEquiv_apply, completionEmbedding_algebraMap, coe_embedComp_apply]`.

Simplify using `only [ordComp, ordPlace, toMul_ofMul]`. Express the relevant statement in the definitionally equal form `-WithZero.log (Valued.v ((compEquiv ι F).symm (embedComp ι F (f : F.1)))) = _`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `-WithZero.log (Valued.v ((f : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1)) = _`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.
-/
theorem ordComp_embedComp (f : F.1ˣ) :
    ordComp ι F (Additive.ofMul (Units.map (embedComp ι F).toRingHom.toMonoidHom f)) = ordPlace ι F f := by
  have h : (compEquiv ι F).symm (embedComp ι F (f : F.1)) =
      algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) (f : F.1) := by
    apply (compEquiv ι F).injective
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_compEquiv_apply, completionEmbedding_algebraMap, coe_embedComp_apply]
  simp only [ordComp, ordPlace, toMul_ofMul]
  change -WithZero.log (Valued.v ((compEquiv ι F).symm (embedComp ι F (f : F.1)))) = _
  rw [h]
  change -WithZero.log (Valued.v ((f : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

abbrev compDecomp : Gal(compField ι F/v.adicCompletion K.1) →* Gal(F.1/K.1) :=
  decompHom (v.adicCompletion K.1) (embedComp ι F)

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Use `symm`. Rewrite using `[decompHom_eq_iff]`. Introduce `x`. Rewrite using `[embedLevel_apply, embedLevel_apply, ← coe_embedComp_apply, ← coe_embedComp_apply, decompHom_apply]`. Conclude with `AlgEquiv.restrictNormal_commutes σ (compField ι F) (embedComp ι F x)`.
-/
theorem compDecomp_restrictNormalHom
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) σ) =
      decompHom (v.adicCompletion K.1) (embedLevel ι F) σ := by
  symm
  rw [decompHom_eq_iff]
  intro x
  rw [embedLevel_apply, embedLevel_apply, ← coe_embedComp_apply, ← coe_embedComp_apply,
    decompHom_apply]
  exact AlgEquiv.restrictNormal_commutes σ (compField ι F) (embedComp ι F x)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `decompHom_apply (embedComp ι F) γ (f : F.1)`.
-/
theorem units_embedComp_galUnitsHom (γ : Gal(compField ι F/v.adicCompletion K.1)) (f : F.1ˣ) :
    Units.map (embedComp ι F).toRingHom.toMonoidHom (galUnitsHom K.1 F.1 (compDecomp ι F γ) f) =
      galUnitsHom (v.adicCompletion K.1) (compField ι F) γ
        (Units.map (embedComp ι F).toRingHom.toMonoidHom f) := by
  apply Units.ext
  exact decompHom_apply (embedComp ι F) γ (f : F.1)

def compCocycleFun (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) :
    Gal(compField ι F/v.adicCompletion K.1) × Gal(compField ι F/v.adicCompletion K.1) →
      Additive (compField ι F)ˣ :=
  fun p => Additive.ofMul (Units.map (embedComp ι F).toRingHom.toMonoidHom
    (c (compDecomp ι F p.1, compDecomp ι F p.2)))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hc' : ∀ g h j, c (g * h, j) * c (g, h) = galUnitsHom K.1 F.1 g (c (h, j)) * c (g, h * j)` using `hc`. Rewrite using `[groupCohomology.mem_cocycles₂_iff]`. Introduce `g h j`. Establish `e` using `hc' (compDecomp ι F g) (compDecomp ι F h) (compDecomp ι F j)`. Establish `m1 : compDecomp ι F (g * h) = compDecomp ι F g * compDecomp ι F h` using `map_mul _ g h`.

Establish `m2 : compDecomp ι F (h * j) = compDecomp ι F h * compDecomp ι F j` using `map_mul _ h j`. Establish `s` using `units_embedComp_galUnitsHom ι F g (c (compDecomp ι F h, compDecomp ι F j))`. Establish `key' : c (compDecomp ι F (g * h), compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h) = galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)) * c (compDecomp ι F g, compDecomp ι F (h * j))` using `(congrArg (fun X => c (X, compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h)) m1).trans (e.trans (congrArg (fun X => galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)) * c (compDecomp ι F g, X)) m2.symm))`. Establish `key` using `congrArg (Units.map (embedComp ι F).toRingHom.toMonoidHom) key'`. Establish `mm1` using `map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom) (c (compDecomp ι F (g * h), compDecomp ι F j)) (c (compDecomp ι F g, compDecomp ι F h))`.

Establish `mm2` using `map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom) (galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j))) (c (compDecomp ι F g, compDecomp ι F (h * j)))`. Conclude with `congrArg Additive.ofMul (mm1.symm.trans (key.trans (mm2.trans (congrArg (· * _) s))))`.
-/
theorem compCocycleFun_mem (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c) :
    compCocycleFun ι F c ∈ groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F)) := by
  have hc' : ∀ g h j, c (g * h, j) * c (g, h) = galUnitsHom K.1 F.1 g (c (h, j)) * c (g, h * j) := hc
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  have e := hc' (compDecomp ι F g) (compDecomp ι F h) (compDecomp ι F j)
  have m1 : compDecomp ι F (g * h) = compDecomp ι F g * compDecomp ι F h := map_mul _ g h
  have m2 : compDecomp ι F (h * j) = compDecomp ι F h * compDecomp ι F j := map_mul _ h j
  have s := units_embedComp_galUnitsHom ι F g (c (compDecomp ι F h, compDecomp ι F j))
  have key' : c (compDecomp ι F (g * h), compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h) =
      galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)) *
        c (compDecomp ι F g, compDecomp ι F (h * j)) :=
    (congrArg (fun X => c (X, compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h)) m1).trans
      (e.trans (congrArg (fun X => galUnitsHom K.1 F.1 (compDecomp ι F g)
        (c (compDecomp ι F h, compDecomp ι F j)) * c (compDecomp ι F g, X)) m2.symm))
  have key := congrArg (Units.map (embedComp ι F).toRingHom.toMonoidHom) key'
  have mm1 := map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom)
    (c (compDecomp ι F (g * h), compDecomp ι F j)) (c (compDecomp ι F g, compDecomp ι F h))
  have mm2 := map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom)
    (galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)))
    (c (compDecomp ι F g, compDecomp ι F (h * j)))
  exact congrArg Additive.ofMul (mm1.symm.trans (key.trans (mm2.trans (congrArg (· * _) s))))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `h` using `exists_cocycle_brauerInflation (F := v.adicCompletion K.1) (Ω := AlgebraicClosure (v.adicCompletion K.1)) (compField ι F) (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ : groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F)))`. Take `⟨z, hz1, hz2⟩` from `h`. Establish `hz0 : cohomologyπ _ 2 z = 0`. Use `cohomologyπ_galUnits_eq_zero_of_coboundary z b hb fun u => ?_` and prove the remaining obligations. Rewrite using `[hz2 u]`.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `q0` using `compDecomp_restrictNormalHom ι F (u 0)`. Establish `q1` using `compDecomp_restrictNormalHom ι F (u 1)`. Establish `e'` using `congrArg (fun x : (AlgebraicClosure (v.adicCompletion K.1))ˣ => (x : AlgebraicClosure (v.adicCompletion K.1))) (hbc (u 0) (u 1))`.

Use `Eq.trans ?_ e'.symm` and prove the remaining obligations. Establish `e3 : ι ((c (compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 0)), compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 1))) : F.1) : ℚ̄) = ι ((c (decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 0), decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 1) …` using `congrArg (fun p => ι ((c p : F.1) : ℚ̄)) (Prod.ext q0 q1)`. Conclude with `e3`. Establish `hc'0 : (ConcreteCategory.hom (groupCohomology.H2π _)) (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ : groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))) = 0`. Apply `brauerInflation_injective (compField ι F)` to reduce the goal to its premises.

Rewrite using `[hz1, hz0, map_zero]`. Rewrite `hc'0` using `[groupCohomology.H2π_eq_zero_iff]`. Conclude with `hc'0`.
-/
theorem exists_compCocycle_coboundary
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
      (AlgebraicClosure (v.adicCompletion K.1))ˣ) (hb : IsLocallyConstant b)
    (hbc : ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
      Units.map (embedLevel ι F).toRingHom.toMonoidHom
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ β' : Gal(compField ι F/v.adicCompletion K.1) → Additive (compField ι F)ˣ,
      (groupCohomology.d₁₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))).hom β' =
        compCocycleFun ι F c := by
  have h := exists_cocycle_brauerInflation (F := v.adicCompletion K.1)
    (Ω := AlgebraicClosure (v.adicCompletion K.1)) (compField ι F)
    (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ :
      groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F)))
  obtain ⟨z, hz1, hz2⟩ := h
  have hz0 : cohomologyπ _ 2 z = 0 := by
    refine cohomologyπ_galUnits_eq_zero_of_coboundary z b hb fun u => ?_
    rw [hz2 u]
    apply Additive.toMul.injective
    apply Units.ext
    have q0 := compDecomp_restrictNormalHom ι F (u 0)
    have q1 := compDecomp_restrictNormalHom ι F (u 1)
    have e' := congrArg (fun x : (AlgebraicClosure (v.adicCompletion K.1))ˣ =>
      (x : AlgebraicClosure (v.adicCompletion K.1))) (hbc (u 0) (u 1))
    refine Eq.trans ?_ e'.symm
    have e3 : ι ((c (compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 0)),
        compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 1))) : F.1) : ℚ̄) =
        ι ((c (decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 1)) : F.1) : ℚ̄) :=
      congrArg (fun p => ι ((c p : F.1) : ℚ̄)) (Prod.ext q0 q1)
    exact e3
  have hc'0 : (ConcreteCategory.hom (groupCohomology.H2π _))
      (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ :
        groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))) = 0 := by
    apply brauerInflation_injective (compField ι F)
    rw [hz1, hz0, map_zero]
  rw [groupCohomology.H2π_eq_zero_iff] at hc'0
  exact hc'0

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `hmul : AlgEquiv.restrictNormalHom (compField ι F) (σ * τ) = AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ` using `map_mul _ σ τ`. Establish `key : (galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) - β' (AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ) + β' (AlgEquiv.restr …` using `congrFun hβ' (AlgEquiv.restrictNormalHom (compField ι F) σ, AlgEquiv.restrictNormalHom (compField ι F) τ)`. Establish `hs : ordComp ι F ((galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ))) = ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) τ))` using `ordComp_smul ι F (AlgEquiv.restrictNormalHom (compField ι F) σ) (Additive.toMul (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)))`. Establish `k1` using `congrArg (ordComp ι F) key`. Establish `k0` using `(ordComp_add ι F _ _).trans (congrArg (· + ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ))) ((ordComp_sub ι F _ _).trans (congrArg (· - ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ))) hs)))`.

Establish `k1` using `k0.symm.trans k1`. Establish `k2 : ordComp ι F (compCocycleFun ι F c (AlgEquiv.restrictNormalHom (compField ι F) σ, AlgEquiv.restrictNormalHom (compField ι F) τ)) = ordPlace ι F (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ, decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))` using `(ordComp_embedComp ι F _).trans (congrArg (fun p => ordPlace ι F (c p)) (Prod.ext (compDecomp_restrictNormalHom ι F σ) (compDecomp_restrictNormalHom ι F τ)))`. Rewrite using `[hmul, k1, k2]`.
-/
theorem ordComp_coboundary_eq (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ)
    (β' : Gal(compField ι F/v.adicCompletion K.1) → Additive (compField ι F)ˣ)
    (hβ' : (groupCohomology.d₁₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))).hom β' =
      compCocycleFun ι F c)
    (σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) -
        ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) (σ * τ))) +
        ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ)) =
      ordPlace ι F (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  have hmul : AlgEquiv.restrictNormalHom (compField ι F) (σ * τ) =
      AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ :=
    map_mul _ σ τ
  have key : (galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ
      (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) -
      β' (AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ) +
      β' (AlgEquiv.restrictNormalHom (compField ι F) σ) =
      compCocycleFun ι F c (AlgEquiv.restrictNormalHom (compField ι F) σ,
        AlgEquiv.restrictNormalHom (compField ι F) τ) :=
    congrFun hβ' (AlgEquiv.restrictNormalHom (compField ι F) σ, AlgEquiv.restrictNormalHom (compField ι F) τ)
  have hs : ordComp ι F ((galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ
      (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ))) =
      ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) :=
    ordComp_smul ι F (AlgEquiv.restrictNormalHom (compField ι F) σ)
      (Additive.toMul (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)))
  have k1 := congrArg (ordComp ι F) key
  have k0 := (ordComp_add ι F _ _).trans (congrArg (· + ordComp ι F
    (β' (AlgEquiv.restrictNormalHom (compField ι F) σ))) ((ordComp_sub ι F _ _).trans
      (congrArg (· - ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ *
        AlgEquiv.restrictNormalHom (compField ι F) τ))) hs)))
  have k1 := k0.symm.trans k1
  have k2 : ordComp ι F (compCocycleFun ι F c (AlgEquiv.restrictNormalHom (compField ι F) σ,
      AlgEquiv.restrictNormalHom (compField ι F) τ)) = ordPlace ι F
      (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) :=
    (ordComp_embedComp ι F _).trans (congrArg (fun p => ordPlace ι F (c p))
      (Prod.ext (compDecomp_restrictNormalHom ι F σ) (compDecomp_restrictNormalHom ι F τ)))
  rw [hmul, k1, k2]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨β', hβ'⟩` from `exists_compCocycle_coboundary ι F c hc b hb hbc`. Conclude with `⟨fun σ => ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ)), (IsLocallyConstant.of_discrete (fun γ => ordComp ι F (β' γ))).comp_continuous (InfiniteGalois.restrictNormalHom_continuous (compField ι F)), fun σ τ => ordComp_coboundary_eq ι F c β' hβ' σ τ⟩`.
-/
theorem exists_ord_coboundary_of_mulCoboundary
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
      (AlgebraicClosure (v.adicCompletion K.1))ˣ) (hb : IsLocallyConstant b)
    (hbc : ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
      Units.map (embedLevel ι F).toRingHom.toMonoidHom
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ h : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) → ℤ,
      IsLocallyConstant h ∧ ∀ σ τ, h τ - h (σ * τ) + h σ = ordPlace ι F
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  obtain ⟨β', hβ'⟩ := exists_compCocycle_coboundary ι F c hc b hb hbc
  exact ⟨fun σ => ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ)),
    (IsLocallyConstant.of_discrete (fun γ => ordComp ι F (β' γ))).comp_continuous
      (InfiniteGalois.restrictNormalHom_continuous (compField ι F)),
    fun σ τ => ordComp_coboundary_eq ι F c β' hβ' σ τ⟩

end Main

end

end GroundTheory.ProfCoh
