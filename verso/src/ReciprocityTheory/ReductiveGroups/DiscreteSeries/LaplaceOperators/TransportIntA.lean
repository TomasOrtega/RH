import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

noncomputable section

open Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA

def extL {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v i := if h : p i then v ⟨i, h⟩ else 0
  map_add' v w := by
    funext i
    by_cases h : p i <;> simp [h]
  map_smul' c v := by
    funext i
    by_cases h : p i <;> simp [h]

/- English proof (translation)
Introduce `v w h`. Use function extensionality and compare the values at `j`. Establish `hj` using `congrFun h j.1`. Simplify `hj` using `[extL, j.2]`.
-/
theorem extL_injective {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : Function.Injective (extL p) := by
  intro v w h
  funext j
  have hj := congrFun h j.1
  simpa [extL, j.2] using hj

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem form_conj {n : ℕ} (Q J : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) = star x ⬝ᵥ ((Qᴴ * J * Q) *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Formalism.REAL.Jm, Matrix.mulVec_diagonal]`. Apply the tactic sequence `by_cases h : ε i = true <;> simp [extL, h]`.
-/
theorem jm_ext_pos {n : ℕ} (ε : Fin n → Bool) (v : {i // ε i = true} → ℂ) :
    Formalism.REAL.Jm ε *ᵥ extL (fun i => ε i = true) v = extL (fun i => ε i = true) v := by
  funext i
  rw [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  by_cases h : ε i = true <;> simp [extL, h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Formalism.REAL.Jm, Matrix.mulVec_diagonal]`. Apply the tactic sequence `by_cases h : ε i = false <;> simp [extL, h]`.
-/
theorem jm_ext_neg {n : ℕ} (ε : Fin n → Bool) (v : {i // ε i = false} → ℂ) :
    Formalism.REAL.Jm ε *ᵥ extL (fun i => ε i = false) v = -extL (fun i => ε i = false) v := by
  funext i
  rw [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  by_cases h : ε i = false <;> simp [extL, h]

/- English proof (translation)
Unfold `pOf qOf`. Rewrite using `[← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun a _ h1 h2 => by simp_all)]`. Establish `hu : (Finset.univ.filter fun a => η a = true) ∪ (Finset.univ.filter fun a => η a = false) = Finset.univ`. Use extensionality with `a`. Apply the tactic sequence `cases h : η a <;> simp [h]`.

Rewrite using `[hu, Finset.card_univ, Fintype.card_fin]`.
-/
private theorem pq_lemma {n : ℕ} (η : Fin n → Bool) : pOf η + qOf η = n := by
  classical
  unfold pOf qOf
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun a _ h1 h2 => by simp_all)]
  have hu : (Finset.univ.filter fun a => η a = true) ∪ (Finset.univ.filter fun a => η a = false) =
      Finset.univ := by
    ext a
    cases h : η a <;> simp [h]
  rw [hu, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Set `f1 : ({i // ε' i = true} → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `Q.mulVecLin ∘ₗ extL (fun i => ε' i = true)`. Set `f2` to `extL (fun i : Fin n => ε i = false)`. Establish `hpos : ∀ u, extL (fun i => ε' i = true) u ≠ 0 → 0 < star (Q *ᵥ extL (fun i => ε' i = true) u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Q *ᵥ extL (fun i => ε' i = true) u))`.

Introduce `u hu`. Rewrite using `[form_conj, hQ, jm_ext_pos]`. Conclude with `Matrix.dotProduct_star_self_pos_iff.2 hu`. Establish `hf1 : Function.Injective f1`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `u hu`. Assume the negation of the conclusion as `hne`. Establish `hz : extL (fun i => ε' i = true) u ≠ 0` using `fun h => hne (extL_injective _ (by rw [h, map_zero]))`. Establish `h` using `hpos u hz`. Establish `hu' : Q *ᵥ extL (fun i => ε' i = true) u = 0` using `hu`.

Rewrite `h` using `[hu']`. Simplify using `at h`. Establish `hf2 : Function.Injective f2` using `extL_injective _`. Establish `hr1 : Module.finrank ℂ (LinearMap.range f1) = pOf ε'`. Rewrite using `[LinearMap.finrank_range_of_inj hf1, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]`.

Both sides reduce to the same expression. Establish `hr2 : Module.finrank ℂ (LinearMap.range f2) = qOf ε`. Rewrite using `[LinearMap.finrank_range_of_inj hf2, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]`. Both sides reduce to the same expression. Establish `hpq` using `pq_lemma ε`.

Establish `hsum` using `Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f1) (LinearMap.range f2)`. Rewrite `hsum` using `[hr1, hr2]`. Establish `hle : Module.finrank ℂ ↥(LinearMap.range f1 ⊔ LinearMap.range f2) ≤ n`. Establish `h` using `Submodule.finrank_le (LinearMap.range f1 ⊔ LinearMap.range f2)`. Rewrite `h` using `[Module.finrank_fin_fun]`. Then use the resulting hypothesis.

Establish `hne : LinearMap.range f1 ⊓ LinearMap.range f2 ≠ ⊥`. Introduce `hbot`. Rewrite `hsum` using `[hbot]`. Simplify using `at hsum`. Use linear arithmetic over natural numbers and integers.

Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.1 hy`. Take `⟨u, hu⟩` from `LinearMap.mem_range.1 hy1`. Take `⟨w, hw⟩` from `LinearMap.mem_range.1 hy2`. Establish `hu' : Q *ᵥ extL (fun i => ε' i = true) u = y` using `hu`.

Establish `hw' : extL (fun i => ε i = false) w = y` using `hw`. Establish `hz : extL (fun i => ε' i = true) u ≠ 0` using `fun h => by`. Rewrite `hu'` using `[h, Matrix.mulVec_zero]`. Conclude with `hy0 hu'.symm`. Establish `h1` using `hpos u hz`.

Rewrite `h1` using `[hu', ← hw', jm_ext_neg, hw', dotProduct_neg]`. Establish `h2 : 0 < star y ⬝ᵥ y` using `Matrix.dotProduct_star_self_pos_iff.2 hy0`. Establish `h3` using `add_pos h2 h1`. Rewrite `h3` using `[add_neg_cancel]`. Conclude with `lt_irrefl _ h3`.
-/
theorem pOf_le_of_conj {n : ℕ} (ε ε' : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε') : pOf ε' ≤ pOf ε := by
  classical
  by_contra hlt
  push_neg at hlt
  let f1 : ({i // ε' i = true} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Q.mulVecLin ∘ₗ extL (fun i => ε' i = true)
  let f2 := extL (fun i : Fin n => ε i = false)
  have hpos : ∀ u, extL (fun i => ε' i = true) u ≠ 0 →
      0 < star (Q *ᵥ extL (fun i => ε' i = true) u) ⬝ᵥ
        (Formalism.REAL.Jm ε *ᵥ (Q *ᵥ extL (fun i => ε' i = true) u)) := by
    intro u hu
    rw [form_conj, hQ, jm_ext_pos]
    exact Matrix.dotProduct_star_self_pos_iff.2 hu
  have hf1 : Function.Injective f1 := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hne
    have hz : extL (fun i => ε' i = true) u ≠ 0 := fun h =>
      hne (extL_injective _ (by rw [h, map_zero]))
    have h := hpos u hz
    have hu' : Q *ᵥ extL (fun i => ε' i = true) u = 0 := hu
    rw [hu'] at h
    simp at h
  have hf2 : Function.Injective f2 := extL_injective _
  have hr1 : Module.finrank ℂ (LinearMap.range f1) = pOf ε' := by
    rw [LinearMap.finrank_range_of_inj hf1, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hr2 : Module.finrank ℂ (LinearMap.range f2) = qOf ε := by
    rw [LinearMap.finrank_range_of_inj hf2, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hpq := pq_lemma ε
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f1) (LinearMap.range f2)
  rw [hr1, hr2] at hsum
  have hle : Module.finrank ℂ ↥(LinearMap.range f1 ⊔ LinearMap.range f2) ≤ n := by
    have h := Submodule.finrank_le (LinearMap.range f1 ⊔ LinearMap.range f2)
    rwa [Module.finrank_fin_fun] at h
  have hne : LinearMap.range f1 ⊓ LinearMap.range f2 ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsum
    simp at hsum
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hy1
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hy2
  have hu' : Q *ᵥ extL (fun i => ε' i = true) u = y := hu
  have hw' : extL (fun i => ε i = false) w = y := hw
  have hz : extL (fun i => ε' i = true) u ≠ 0 := fun h => by
    rw [h, Matrix.mulVec_zero] at hu'
    exact hy0 hu'.symm
  have h1 := hpos u hz
  rw [hu', ← hw', jm_ext_neg, hw', dotProduct_neg] at h1
  have h2 : 0 < star y ⬝ᵥ y := Matrix.dotProduct_star_self_pos_iff.2 hy0
  have h3 := add_pos h2 h1
  rw [add_neg_cancel] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Apply `pOf_le_of_conj ε ε' (P * P₀⁻¹)` to reduce the goal to its premises. Establish `h1 : P₀ * P₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ h0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [mul_assoc]`.

Use `_ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε' * P₀) * P₀⁻¹ := by rw [hP, hP₀]`. Use `_ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε' * (P₀ * P₀⁻¹) := by`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [mul_assoc]`. Use `_ = Formalism.REAL.Jm ε' := by rw [h1, Matrix.conjTranspose_one, one_mul, mul_one]`.
-/
theorem pOf_le_of_two {n : ℕ} (ε ε' : Fin n → Bool) (H P P₀ : Matrix (Fin n) (Fin n) ℂ)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = H) (hP₀ : P₀ᴴ * Formalism.REAL.Jm ε' * P₀ = H) (h0 : IsUnit P₀.det) :
    pOf ε' ≤ pOf ε := by
  apply pOf_le_of_conj ε ε' (P * P₀⁻¹)
  have h1 : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ h0
  calc (P * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P₀⁻¹) = (P₀⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P₀⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε' * P₀) * P₀⁻¹ := by rw [hP, hP₀]
    _ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε' * (P₀ * P₀⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε' := by rw [h1, Matrix.conjTranspose_one, one_mul, mul_one]

/- English proof (translation)
Take `⟨-, -, -, ε0, hε0, P0, hP0det, hP0⟩` from `Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r`. Establish `h1 : pOf ε0 ≤ pOf ε` using `pOf_le_of_two ε ε0 _ P P0 hP.2 hP0 hP0det`. Establish `h2 : pOf ε ≤ pOf ε0` using `pOf_le_of_two ε0 ε _ P0 P hP0 hP.2 ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)`. Establish `h0 : pOf ε0 = k + r` using `hε0`. Establish `hpq` using `pq_lemma ε`.

Apply the tactic sequence `constructor <;> omega`.
-/
theorem cayley_signature' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) : pOf ε = k + r ∧ qOf ε = r + 1 := by
  obtain ⟨-, -, -, ε0, hε0, P0, hP0det, hP0⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have h1 : pOf ε0 ≤ pOf ε := pOf_le_of_two ε ε0 _ P P0 hP.2 hP0 hP0det
  have h2 : pOf ε ≤ pOf ε0 :=
    pOf_le_of_two ε0 ε _ P0 P hP0 hP.2 ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
  have h0 : pOf ε0 = k + r := hε0
  have hpq := pq_lemma ε
  constructor <;> omega

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA
