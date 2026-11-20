import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial
open scoped nonZeroDivisors

section Galois

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element F M`. Establish `hM : M = F⟮(α : Ω)⟯`. Rewrite using `[← lift_adjoin_simple F M α, hα, lift_top (K := M)]`. Establish `hint : IsIntegral F (α : Ω)` using `(Algebra.IsIntegral.isIntegral α).map M.val`. Establish `hsplit : ((minpoly F (α : Ω)).map (algebraMap F Ω)).Splits` using `IsAlgClosed.splits _`.

Use `adjoin_rootSet_isSplittingField hsplit` as an intermediate fact. Use `⟨adjoin F ((minpoly F (α : Ω)).rootSet Ω), ?_, IsSplittingField.finiteDimensional _ (minpoly F (α : Ω)), IsGalois.of_separable_splitting_field (minpoly.irreducible hint).separable⟩` and prove the remaining obligations. Conclude with `hM.le.trans (adjoin_simple_le_iff.2 (subset_adjoin F _ (mem_rootSet.2 ⟨minpoly.ne_zero hint, minpoly.aeval F _⟩)))`.
-/
theorem exists_isGalois_le {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω]
    [Algebra F Ω] (M : IntermediateField F Ω) [FiniteDimensional F M] :
    ∃ L : IntermediateField F Ω, M ≤ L ∧ FiniteDimensional F L ∧ IsGalois F L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F M
  have hM : M = F⟮(α : Ω)⟯ := by
    rw [← lift_adjoin_simple F M α, hα, lift_top (K := M)]
  have hint : IsIntegral F (α : Ω) := (Algebra.IsIntegral.isIntegral α).map M.val
  have hsplit : ((minpoly F (α : Ω)).map (algebraMap F Ω)).Splits := IsAlgClosed.splits _
  have := adjoin_rootSet_isSplittingField hsplit
  refine ⟨adjoin F ((minpoly F (α : Ω)).rootSet Ω), ?_,
    IsSplittingField.finiteDimensional _ (minpoly F (α : Ω)),
    IsGalois.of_separable_splitting_field (minpoly.irreducible hint).separable⟩
  exact hM.le.trans (adjoin_simple_le_iff.2
    (subset_adjoin F _ (mem_rootSet.2 ⟨minpoly.ne_zero hint, minpoly.aeval F _⟩)))

end Galois

section Models

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

omit [Algebra K ℂ] in

/- English proof (translation)
Take `⟨E, rfl⟩` from `ELL.exists_eq x`. Take `⟨C, hC⟩` from `exists_variableChange_of_j_eq E.curve W (by rw [hW, ELL.j_toEll])`. Use `⟨⟨(vcEndEquiv C hC).symm.trans E.endIso.some⟩, ?_⟩` and prove the remaining obligations. Conclude with `(CMCurve.toEll_eq_iff _ _).2 ⟨C⁻¹, inv_smul_eq_of_smul_eq C hC⟩`.
-/
theorem exists_cmCurve_toEll_of_j_eq (x : ELL K) (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (hW : W.j = ELL.j x) :
    ∃ h : Nonempty (isogEnd W ≃+* 𝓞 K), (⟨W, h⟩ : CMCurve K).toEll = x := by
  classical
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq E.curve W (by rw [hW, ELL.j_toEll])
  refine ⟨⟨(vcEndEquiv C hC).symm.trans E.endIso.some⟩, ?_⟩
  exact (CMCurve.toEll_eq_iff _ _).2 ⟨C⁻¹, inv_smul_eq_of_smul_eq C hC⟩

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]

include hK in

/- English proof (translation)
Take `⟨a, ha, -⟩` from `existsUnique_smul_eq (algebraMap K ℂ) hK A.toEll B.toEll`. Take `⟨I, rfl⟩` from `classGroup_mk_surjective hK a`. Take `⟨c, hc, hset⟩` from `homConstSet_of_smul (algebraMap K ℂ) hK ha`. Establish `hI : (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥`. Rewrite using `[Ne, FractionalIdeal.coeToSubmodule_eq_bot]`.

Conclude with `Units.ne_zero _`. Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `hmem : c * algebraMap K ℂ t ∈ (homConstSet A.curve B.curve : Set ℂ)`. Rewrite using `[hset]`. Conclude with `⟨_, map_mem_idealLattice _ ht, rfl⟩`.

Take `⟨Q, hQ⟩` from `mem_homConstSet.1 hmem`. Establish `hQ0 : Q ≠ 0`. Introduce and unpack `rfl`. Rewrite `hQ` using `[map_zero]`. Conclude with `mul_ne_zero hc ((_root_.map_ne_zero _).2 ht0) hQ.symm`.

Conclude with `⟨isogOfHom Q hQ0⟩`.
-/
theorem nonempty_isogeny_of_cmCurve (A B : CMCurve K) : Nonempty (Isogeny A.curve B.curve) := by
  classical
  obtain ⟨a, ha, -⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK A.toEll B.toEll
  obtain ⟨I, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨c, hc, hset⟩ := homConstSet_of_smul (algebraMap K ℂ) hK ha
  have hI : (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≠ ⊥ := by
    rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    exact Units.ne_zero _
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hmem : c * algebraMap K ℂ t ∈ (homConstSet A.curve B.curve : Set ℂ) := by
    rw [hset]
    exact ⟨_, map_mem_idealLattice _ ht, rfl⟩
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact mul_ne_zero hc ((_root_.map_ne_zero _).2 ht0) hQ.symm
  exact ⟨isogOfHom Q hQ0⟩

include hK in

/- English proof (translation)
Use `haveI := finite_ell hK`. Use `set x₀ := ellEquiv (algebraMap K ℂ) hK 1`. Use `set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯`. Establish `hJ : ∀ y, ELL.j y ∈ J` using `fun y ↦ ELL.j_mem_adjoin hK x₀ y`. Use `haveI : FiniteDimensional K J := adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral`.

Use `haveI : NumberField J := NumberField.of_module_finite K J`. Use `set E₀ : ELL K → WeierstrassCurve J := fun y ↦ ofJ (⟨ELL.j y, hJ y⟩ : J)`. Establish `hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y` using `fun y ↦ by`. Simplify using `only [E₀, ofJ_j]`. Both sides reduce to the same expression.

Establish `hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K), (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y` using `fun y ↦ exists_cmCurve_toEll_of_j_eq y _ (by show ((E₀ y).map (algebraMap J ℂ)).j = _`. Rewrite using `[map_j, hE₀j])`. Establish `hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧ Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁))`. Introduce and unpack `⟨y, z⟩`. Take `⟨hy, -⟩` from `hE₀ y`.

Take `⟨hz, -⟩` from `hE₀ z`. Take `⟨ψ⟩` from `nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩`. Take `⟨F₁, hF₁, φ, -⟩` from `Isogeny.exists_numberField_mapOf_eq ψ`. Conclude with `⟨F₁, hF₁, ⟨φ⟩⟩`. Use `choose F hFnum hFiso using hF`.

Establish `hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K)` using `fun p ↦ by haveI := hFnum p haveI : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))`. Conclude with `Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)`. Use `set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K`. Use `haveI : FiniteDimensional K M' := by haveI := hFfin infer_instance`. Take `⟨L, hM'L, hLfin, hLgal⟩` from `exists_isGalois_le M'`.

Establish `hJL : J ≤ L` using `le_trans (le_trans le_sup_right le_sup_left) hM'L`. Establish `hFL : ∀ p, (F p).restrictScalars K ≤ L` using `fun p ↦ le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L`. Use `set ι : J →+* L := (inclusion hJL).toRingHom`. Use `⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y), fun y ↦ (E₀ y).map ι, fun y ↦ inferInstance, fun y ↦ ?_, fun y z ↦ ?_⟩` and prove the remaining obligations. Use `exists_cmCurve_toEll_of_j_eq y _ ?_ show (((E₀ y).map ι).map (algebraMap L ℂ)).j = _` and prove the remaining obligations.

Rewrite using `[map_j, map_j]`. Conclude with `hE₀j y`. Take `⟨φ⟩` from `hFiso (y, z)`. Set `κ : F (y, z) →+* L` to `(inclusion (hFL (y, z))).toRingHom`. Establish `hκ : κ.comp (algebraMap J (F (y, z))) = ι`.

Use extensionality with `a`. Both sides reduce to the same expression. Establish `e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = (E₀ w).map ι` using `fun w ↦ by show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _`. Rewrite using `[WeierstrassCurve.map_map, hκ]`. Conclude with `⟨(φ.map κ).congr (e y) (e z)⟩`.
-/
theorem exists_models_isogenous (M : IntermediateField K ℂ) [FiniteDimensional K M] :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ _ : ∀ x : ELL K, ELL.j x ∈ L, ∃ (E : ELL K → WeierstrassCurve L) (_ : ∀ x, (E x).IsElliptic),
        (∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
          (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny (E x) (E y)) := by
  classical
  haveI := finite_ell hK
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯
  have hJ : ∀ y, ELL.j y ∈ J := fun y ↦ ELL.j_mem_adjoin hK x₀ y
  haveI : FiniteDimensional K J :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  haveI : NumberField J := NumberField.of_module_finite K J
  set E₀ : ELL K → WeierstrassCurve J := fun y ↦ ofJ (⟨ELL.j y, hJ y⟩ : J)
  have hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y := fun y ↦ by
    simp only [E₀, ofJ_j]
    rfl
  have hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y := fun y ↦
    exists_cmCurve_toEll_of_j_eq y _ (by
      show ((E₀ y).map (algebraMap J ℂ)).j = _
      rw [map_j, hE₀j])
  have hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧
      Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁)) := by
    rintro ⟨y, z⟩
    obtain ⟨hy, -⟩ := hE₀ y
    obtain ⟨hz, -⟩ := hE₀ z
    obtain ⟨ψ⟩ := nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩
    obtain ⟨F₁, hF₁, φ, -⟩ := Isogeny.exists_numberField_mapOf_eq ψ
    exact ⟨F₁, hF₁, ⟨φ⟩⟩
  choose F hFnum hFiso using hF
  have hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K) := fun p ↦ by
    haveI := hFnum p
    haveI : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))
    exact Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)
  set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K
  haveI : FiniteDimensional K M' := by
    haveI := hFfin
    infer_instance
  obtain ⟨L, hM'L, hLfin, hLgal⟩ := exists_isGalois_le M'
  have hJL : J ≤ L := le_trans (le_trans le_sup_right le_sup_left) hM'L
  have hFL : ∀ p, (F p).restrictScalars K ≤ L := fun p ↦
    le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L
  set ι : J →+* L := (inclusion hJL).toRingHom
  refine ⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y),
    fun y ↦ (E₀ y).map ι, fun y ↦ inferInstance, fun y ↦ ?_, fun y z ↦ ?_⟩
  · refine exists_cmCurve_toEll_of_j_eq y _ ?_
    show (((E₀ y).map ι).map (algebraMap L ℂ)).j = _
    rw [map_j, map_j]
    exact hE₀j y
  · obtain ⟨φ⟩ := hFiso (y, z)
    let κ : F (y, z) →+* L := (inclusion (hFL (y, z))).toRingHom
    have hκ : κ.comp (algebraMap J (F (y, z))) = ι := by
      ext a
      rfl
    have e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = (E₀ w).map ι := fun w ↦ by
      show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _
      rw [WeierstrassCurve.map_map, hκ]
    exact ⟨(φ.map κ).congr (e y) (e z)⟩

end Models

end

end Elliptic
end GroundTheory.Global
