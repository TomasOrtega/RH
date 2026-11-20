import Mathlib
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.FinalMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

section Gen

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_algebraMap_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, he, smul_eq_mul, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem inner_sum_orthonormal (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a b : Fin n → K) :
    h (∑ i, a i • e i) (∑ j, b j • e j) = ∑ i, star (a i) * b i := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, he,
    smul_eq_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/- English proof (translation)
Take `⟨e, -, -, rfl, -⟩` from `hL`. Conclude with `Submodule.fg_span (Set.finite_range e)`.
-/
theorem fg_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) : L.FG := by
  obtain ⟨e, -, -, rfl, -⟩ := hL
  exact Submodule.fg_span (Set.finite_range e)

/- English proof (translation)
Take `⟨e, -, -, rfl, he⟩` from `hL`. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy`. Establish `e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i` using `Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm`.

Establish `e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i` using `Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm`. Rewrite using `[e1, e2, inner_sum_orthonormal h e he]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a', ha'⟩` from `star_algebraMap_mem_range (a i)`. Rewrite using `[← ha', ← map_mul]`.

Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`.
-/
theorem integral_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsIntegralLat h L := by
  obtain ⟨e, -, -, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy
  have e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm
  have e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm
  rw [e1, e2, inner_sum_orthonormal h e he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a', ha'⟩ := star_algebraMap_mem_range (a i)
  rw [← ha', ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

/- English proof (translation)
Establish `hint` using `integral_of_orthonormal_basis h L hL`. Take `⟨e, -, hsp, rfl, he⟩` from `hL`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[dualBasic_mem_dual]`.

Establish `hz' : z ∈ Submodule.span K (Set.range e)` using `by rw [hsp]; trivial`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hz'`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `hz (e i) (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h2 : h (e i) (∑ j, c j • e j) = c i`.

Simplify using `only [map_sum, map_smul, he, smul_eq_mul]`. Simplify using `[Finset.sum_ite_eq]`. Rewrite `h1` using `[h2]`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h1`. Rewrite using `[← ho, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `z hz`. Rewrite using `[dualBasic_mem_dual]`. Introduce `y hy`. Conclude with `hint y hy z hz`.
-/
theorem unimodular_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by
  have hint := integral_of_orthonormal_basis h L hL
  obtain ⟨e, -, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro z hz
    rw [dualBasic_mem_dual] at hz
    have hz' : z ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hz'
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := hz (e i) (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : h (e i) (∑ j, c j • e j) = c i := by
      simp only [map_sum, map_smul, he, smul_eq_mul]
      simp [Finset.sum_ite_eq]
    rw [h2] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro z hz
    rw [dualBasic_mem_dual]
    intro y hy
    exact hint y hy z hz

/- English proof (translation)
Establish `hG` using `(final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2`. Conclude with `⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩`.
-/
theorem genus_orthonormal_integral_unimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by
  have hG := (final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2
  exact ⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩

/- English proof (translation)
Unfold `mass`. Use `split_ifs with hs`. Use `le_trans ?_ (hc _ hs.choose_spec)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun M _ => ?_` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0` into its components or cases. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Conclude with `inv_le_one_of_one_le₀ (by exact_mod_cast h0)`. Use `_ = (hs.choose.card : ℝ) := by simp`.

Conclude with `hB`.
-/
theorem mass_le_of_card_class_reps_le (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by
  classical
  unfold mass
  split_ifs with hs
  · refine le_trans ?_ (hc _ hs.choose_spec)
    calc ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ hs.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
      _ = (hs.choose.card : ℝ) := by simp
  · exact hB

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
