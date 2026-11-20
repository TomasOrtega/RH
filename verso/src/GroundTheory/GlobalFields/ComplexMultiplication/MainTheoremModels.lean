import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldModels
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian

section ShortModel

variable {F F' : Type*} [Field F] [Field F']

/- English proof (translation)
Establish `h3 : (3 : F) = 0 ↔ (3 : F') = 0`. Rewrite using `[← map_ofNat f 3, map_eq_zero_iff f f.injective]`. Establish `hj0 : j = 0 ↔ f j = 0` using `(map_eq_zero_iff f f.injective).symm`. Establish `hj1728 : j = 1728 ↔ f j = 1728`. Rewrite using `[← map_ofNat f 1728]`.

Conclude with `f.injective.eq_iff.symm`. Unfold `ofJ`. Distinguish the cases in `a : j = 0`. Rewrite using `[if_pos a, if_pos (hj0.1 a)]`. Distinguish the cases in `b : (3 : F) = 0`.

Rewrite using `[if_pos b, if_pos (h3.1 b)]`. Apply the tactic sequence `ext <;> simp [ofJ1728]`. Rewrite using `[if_neg b, if_neg (mt h3.2 b)]`. Apply the tactic sequence `ext <;> simp [ofJ0]`. Rewrite using `[if_neg a, if_neg (mt hj0.2 a)]`.

Distinguish the cases in `b : j = 1728`. Rewrite using `[if_pos b, if_pos (hj1728.1 b)]`. Apply the tactic sequence `ext <;> simp [ofJ1728]`. Rewrite using `[if_neg b, if_neg (mt hj1728.2 b)]`. Apply the tactic sequence `ext <;> simp [ofJNe0Or1728, map_ofNat]`.
-/
theorem ofJ_map [DecidableEq F] [DecidableEq F'] (f : F →+* F') (j : F) :
    (ofJ j).map f = ofJ (f j) := by
  have h3 : (3 : F) = 0 ↔ (3 : F') = 0 := by
    rw [← map_ofNat f 3, map_eq_zero_iff f f.injective]
  have hj0 : j = 0 ↔ f j = 0 := (map_eq_zero_iff f f.injective).symm
  have hj1728 : j = 1728 ↔ f j = 1728 := by
    rw [← map_ofNat f 1728]
    exact f.injective.eq_iff.symm
  unfold ofJ
  by_cases a : j = 0
  · rw [if_pos a, if_pos (hj0.1 a)]
    by_cases b : (3 : F) = 0
    · rw [if_pos b, if_pos (h3.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt h3.2 b)]
      ext <;> simp [ofJ0]
  · rw [if_neg a, if_neg (mt hj0.2 a)]
    by_cases b : j = 1728
    · rw [if_pos b, if_pos (hj1728.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt hj1728.2 b)]
      ext <;> simp [ofJNe0Or1728, map_ofNat]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [toShortNF, toCharNeTwoNF, VariableChange.map, variableChange_a₂, VariableChange.mul_def, map_ofNat]`.
-/
theorem toShortNF_map (W : WeierstrassCurve F) [Invertible (2 : F)] [Invertible (3 : F)]
    [Invertible (2 : F')] [Invertible (3 : F')] (f : F →+* F') :
    W.toShortNF.map f = (W.map f).toShortNF := by
  ext <;> simp [toShortNF, toCharNeTwoNF, VariableChange.map, variableChange_a₂,
    VariableChange.mul_def, map_ofNat]

variable [CharZero F]

def shortModel (j : F) : WeierstrassCurve F :=
  letI : DecidableEq F := Classical.decEq F
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  (ofJ j).toShortNF • ofJ j

instance (j : F) : (shortModel j).IsElliptic := by
  unfold shortModel
  infer_instance

instance (j : F) : (shortModel j).IsShortNF := by
  unfold shortModel
  infer_instance

/- English proof (translation)
Unfold `shortModel`. Rewrite using `[variableChange_j, ofJ_j]`.
-/
theorem shortModel_j (j : F) : (shortModel j).j = j := by
  unfold shortModel
  rw [variableChange_j, ofJ_j]

variable [CharZero F']

/- English proof (translation)
Set `_ : Invertible (2 : F)` to `invertibleOfNonzero two_ne_zero`. Set `_ : Invertible (3 : F)` to `invertibleOfNonzero three_ne_zero`. Set `_ : Invertible (2 : F')` to `invertibleOfNonzero two_ne_zero`. Set `_ : Invertible (3 : F')` to `invertibleOfNonzero three_ne_zero`. Establish `e1 : shortModel j = (ofJ j).toShortNF • ofJ j`.

Unfold `shortModel`. Reduce the equality to equality of the corresponding arguments. Establish `e2 : shortModel (f j) = (ofJ (f j)).toShortNF • ofJ (f j)`. Unfold `shortModel`. Reduce the equality to equality of the corresponding arguments.

Rewrite using `[e1, e2, ← map_variableChange, toShortNF_map, ofJ_map]`.
-/
theorem shortModel_map (f : F →+* F') (j : F) : (shortModel j).map f = shortModel (f j) := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  let _ : Invertible (2 : F') := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F') := invertibleOfNonzero three_ne_zero
  have e1 : shortModel j = (ofJ j).toShortNF • ofJ j := by
    unfold shortModel
    congr
  have e2 : shortModel (f j) = (ofJ (f j)).toShortNF • ofJ (f j) := by
    unfold shortModel
    congr
  rw [e1, e2, ← map_variableChange, toShortNF_map, ofJ_map]

end ShortModel

section Models

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

/- English proof (translation)
Use `finite_ell hK` as an intermediate fact. Use `set x₀ := ellEquiv (algebraMap K ℂ) hK 1`. Use `set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯`. Establish `hJ : ∀ y, ELL.j y ∈ J` using `fun y ↦ ELL.j_mem_adjoin hK x₀ y`. Establish `: FiniteDimensional K J` using `adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral`.

Establish `: NumberField J` using `NumberField.of_module_finite K J`. Use `set E₀ : ELL K → WeierstrassCurve J := fun y ↦ shortModel (⟨ELL.j y, hJ y⟩ : J)`. Establish `hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y` using `fun y ↦ by`. Simplify using `only [E₀, shortModel_j]`. Both sides reduce to the same expression.

Establish `hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K), (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y` using `fun y ↦ exists_cmCurve_toEll_of_j_eq y _ (by show ((E₀ y).map (algebraMap J ℂ)).j = _`. Rewrite using `[map_j, hE₀j])`. Establish `hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧ Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁))`. Introduce and unpack `⟨y, z⟩`. Take `⟨hy, -⟩` from `hE₀ y`.

Take `⟨hz, -⟩` from `hE₀ z`. Take `⟨ψ⟩` from `nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩`. Take `⟨F₁, hF₁, φ, -⟩` from `Isogeny.exists_numberField_mapOf_eq ψ`. Conclude with `⟨F₁, hF₁, ⟨φ⟩⟩`. Use `choose F hFnum hFiso using hF`.

Establish `hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K)` using `fun p ↦ by`. Use `hFnum p` as an intermediate fact. Establish `: FiniteDimensional ℚ ((F p).restrictScalars K)` using `(inferInstance : FiniteDimensional ℚ (F p))`. Conclude with `Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)`. Use `set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K`.

Establish `: FiniteDimensional K M'`. Use `hFfin` as an intermediate fact. Use `infer_instance`. Take `⟨L, hM'L, hLfin, hLgal⟩` from `exists_isGalois_le M'`. Establish `hJL : J ≤ L` using `le_trans (le_trans le_sup_right le_sup_left) hM'L`.

Establish `hFL : ∀ p, (F p).restrictScalars K ≤ L` using `fun p ↦ le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L`. Use `set ι : J →+* L := (inclusion hJL).toRingHom`. Establish `hmodel : ∀ y, (E₀ y).map ι = shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L)` using `fun y ↦ by`. Rewrite using `[shortModel_map]`. Both sides reduce to the same expression.

Use `⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y), fun y ↦ ?_, fun y z ↦ ?_⟩` and prove the remaining obligations. Use `exists_cmCurve_toEll_of_j_eq y _ ?_ show ((shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L)).map (algebraMap L ℂ)).j = _` and prove the remaining obligations. Rewrite using `[map_j, shortModel_j]`. Both sides reduce to the same expression. Take `⟨φ⟩` from `hFiso (y, z)`.

Set `κ : F (y, z) →+* L` to `(inclusion (hFL (y, z))).toRingHom`. Establish `hκ : κ.comp (algebraMap J (F (y, z))) = ι`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = shortModel (⟨ELL.j w, hJL (hJ w)⟩ : L)` using `fun w ↦ by show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _`.

Rewrite using `[WeierstrassCurve.map_map, hκ, hmodel]`. Conclude with `⟨(φ.map κ).congr (e y) (e z)⟩`.
-/
theorem exists_shortModels_isogenous (M : IntermediateField K ℂ) [FiniteDimensional K M] :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ hL : ∀ x : ELL K, ELL.j x ∈ L,
        (∀ x, ∃ h : Nonempty (isogEnd ((shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ) ≃+* 𝓞 K),
          (⟨(shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny (shortModel (⟨ELL.j x, hL x⟩ : L))
          (shortModel (⟨ELL.j y, hL y⟩ : L))) := by
  classical
  have := finite_ell hK
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯
  have hJ : ∀ y, ELL.j y ∈ J := fun y ↦ ELL.j_mem_adjoin hK x₀ y
  have : FiniteDimensional K J :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  have : NumberField J := NumberField.of_module_finite K J
  set E₀ : ELL K → WeierstrassCurve J := fun y ↦ shortModel (⟨ELL.j y, hJ y⟩ : J)
  have hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y := fun y ↦ by
    simp only [E₀, shortModel_j]
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
    have := hFnum p
    have : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))
    exact Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)
  set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K
  have : FiniteDimensional K M' := by
    have := hFfin
    infer_instance
  obtain ⟨L, hM'L, hLfin, hLgal⟩ := exists_isGalois_le M'
  have hJL : J ≤ L := le_trans (le_trans le_sup_right le_sup_left) hM'L
  have hFL : ∀ p, (F p).restrictScalars K ≤ L := fun p ↦
    le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L
  set ι : J →+* L := (inclusion hJL).toRingHom
  have hmodel : ∀ y, (E₀ y).map ι = shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L) := fun y ↦ by
    rw [shortModel_map]
    rfl
  refine ⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y),
    fun y ↦ ?_, fun y z ↦ ?_⟩
  · refine exists_cmCurve_toEll_of_j_eq y _ ?_
    show ((shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L)).map (algebraMap L ℂ)).j = _
    rw [map_j, shortModel_j]
    rfl
  · obtain ⟨φ⟩ := hFiso (y, z)
    let κ : F (y, z) →+* L := (inclusion (hFL (y, z))).toRingHom
    have hκ : κ.comp (algebraMap J (F (y, z))) = ι := by
      ext a
      rfl
    have e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = shortModel (⟨ELL.j w, hJL (hJ w)⟩ : L) :=
      fun w ↦ by
        show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _
        rw [WeierstrassCurve.map_map, hκ, hmodel]
    exact ⟨(φ.map κ).congr (e y) (e z)⟩

end Models

end

end Elliptic
end GroundTheory.Global
