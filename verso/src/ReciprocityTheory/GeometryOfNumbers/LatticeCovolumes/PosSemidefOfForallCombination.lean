import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadStA

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_isFrame E' hE'`. Establish `hαv : LinearIndependent K (fun i => α (v i))` using `hv.2.1.map' α (LinearMap.ker_eq_bot.mpr hα)`. Take `⟨m, w', hw'w, hu⟩` from `HadamardFrameExtension.exists_append_frame (fun i => α (v i)) hαv (fun i => hαE _ (hv.1 i)) w hw`. Establish `hr : latRank K E' + m = latRank K E` using `hu.card_eq`. Establish `hI` using `HadamardFrameExtension.relIndex_le_of_append hE α hαE v hv w' hu`.

Establish `hI'` using `IsFrame.relIndex_ne_zero hE' hv`. Establish `hlogI` using `Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hI') (Nat.cast_le (α := ℝ).mpr hI)`. Establish `hdet : ∀ σ : K →+* ℂ, Real.log (h.gram σ (Fin.append (fun i => α (v i)) w')).det.re ≤ 2 * (latRank K E' : ℕ) * Real.log (A σ) + Real.log (h'.gram σ v).det.re + 2 * m * Real.log (lam σ)` using `fun σ => HadamardFrameExtension.log_det_append_le h' h α hα σ (A σ) (lam σ) (hA σ) (hlam σ) v hv.2.1 w' hu.2.1 (hnorm σ _ v) (fun j => by obtain ⟨i, hi⟩ := hw'w j; rw [hi]; exact hwl σ i)`. Establish `hsum` using `Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hdet σ)`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`.

Rewrite using `[arakelovDegree_eq_degreeOfFamily h' hE' hv, arakelovDegree_eq_degreeOfFamily h hE hu]`. Unfold `degreeOfFamily meanLog`. Establish `hd : (0 : ℝ) < finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Rewrite using `[← hr]`. Use `push_cast`.

Rewrite using `[div_le_iff₀ hd]`. Establish `e : ∀ X SA SL r' m' : ℝ, (X / finrank ℚ K + r' * (SA / finrank ℚ K) + (r' + m' - r') * (SL / finrank ℚ K)) * finrank ℚ K = X + r' * SA + m' * SL` using `by intros; field_simp; ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_le_deg_add (h' : HermFam K V') (h : HermFam K V)
    (E' : Submodule (𝓞 K) V') (E : Submodule (𝓞 K) V) (hE' : E'.FG) (hE : E.FG)
    (α : V' →ₗ[K] V) (hα : Function.Injective α) (hαE : ∀ x ∈ E', α x ∈ E)
    (A lam : (K →+* ℂ) → ℝ) (hA : ∀ σ, 0 < A σ) (hlam : ∀ σ, 0 < lam σ)
    (hnorm : ∀ σ (n : ℕ) (v : Fin n → V'),
      (((A σ : ℂ) ^ 2) • h'.gram σ v - h.gram σ (fun i => α (v i))).PosSemidef)
    (w : Fin (latRank K E) → V) (hw : IsFrame K E w) (hwl : ∀ σ i, h.nrm σ (w i) ≤ lam σ) :
    deg h' E' ≤ deg h E + (latRank K E' : ℝ) * meanLog K A +
      ((latRank K E : ℝ) - latRank K E') * meanLog K lam := by
  obtain ⟨v, hv⟩ := exists_isFrame E' hE'
  have hαv : LinearIndependent K (fun i => α (v i)) := hv.2.1.map' α (LinearMap.ker_eq_bot.mpr hα)
  obtain ⟨m, w', hw'w, hu⟩ :=
    HadamardFrameExtension.exists_append_frame (fun i => α (v i)) hαv (fun i => hαE _ (hv.1 i)) w hw
  have hr : latRank K E' + m = latRank K E := hu.card_eq
  have hI := HadamardFrameExtension.relIndex_le_of_append hE α hαE v hv w' hu
  have hI' := IsFrame.relIndex_ne_zero hE' hv
  have hlogI := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hI') (Nat.cast_le (α := ℝ).mpr hI)
  have hdet : ∀ σ : K →+* ℂ, Real.log (h.gram σ (Fin.append (fun i => α (v i)) w')).det.re ≤
      2 * (latRank K E' : ℕ) * Real.log (A σ) + Real.log (h'.gram σ v).det.re +
        2 * m * Real.log (lam σ) := fun σ =>
    HadamardFrameExtension.log_det_append_le h' h α hα σ (A σ) (lam σ) (hA σ) (hlam σ) v hv.2.1 w' hu.2.1 (hnorm σ _ v)
      (fun j => by obtain ⟨i, hi⟩ := hw'w j; rw [hi]; exact hwl σ i)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hdet σ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [arakelovDegree_eq_degreeOfFamily h' hE' hv, arakelovDegree_eq_degreeOfFamily h hE hu]
  unfold degreeOfFamily meanLog
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [← hr]; push_cast
  rw [div_le_iff₀ hd]
  have e : ∀ X SA SL r' m' : ℝ, (X / finrank ℚ K + r' * (SA / finrank ℚ K) + (r' + m' - r') *
      (SL / finrank ℚ K)) * finrank ℚ K = X + r' * SA + m' * SL := by
    intros; field_simp; ring
  rw [e]
  linarith

end ReciprocityTheory.GeometryOfNumbersTheory
