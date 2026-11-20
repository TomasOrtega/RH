import Formalism.SharpRestriction.CuspSpanNormBounds.PairOfInputs
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show FiniteDimensional ℂ ↥(⊥ : Submodule ℂ H) infer_instance`. Introduce `g _ v hv`.

Simplify using `only [Finset.sup_empty, Submodule.mem_bot] at hv`. Simplify using `[hv]`. Consider the case `insert a s ha ih`. Establish `hA` using `hs a (Finset.mem_insert_self a s)`. Establish `hS` using `ih (fun S hS' => hs S (Finset.mem_insert_of_mem hS'))`.

Rewrite using `[Finset.sup_insert]`. Use `hA.1` as an intermediate fact. Use `hS.1` as an intermediate fact. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [id] infer_instance`.

Introduce `g hg v hv`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hA.2 g hg x hx) (hS.2 g hg y hy)`.
-/
theorem finset_sup_kstable {n : ℕ} (ε : Fin n → Bool) (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (s : Finset (Submodule ℂ H)) (hs : ∀ S ∈ s, FiniteDimensional ℂ S ∧ IsKStableOn ε τ S) :
    FiniteDimensional ℂ ↥(s.sup (id : Submodule ℂ H → Submodule ℂ H)) ∧
      IsKStableOn ε τ (s.sup (id : Submodule ℂ H → Submodule ℂ H)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · show FiniteDimensional ℂ ↥(⊥ : Submodule ℂ H)
      infer_instance
    · intro g _ v hv
      simp only [Finset.sup_empty, Submodule.mem_bot] at hv
      simp [hv]
  | insert a s ha ih =>
    have hA := hs a (Finset.mem_insert_self a s)
    have hS := ih (fun S hS' => hs S (Finset.mem_insert_of_mem hS'))
    rw [Finset.sup_insert]
    have := hA.1
    have := hS.1
    refine ⟨?_, ?_⟩
    · simp only [id]
      infer_instance
    · intro g hg v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hA.2 g hg x hx) (hS.2 g hg y hy)

/- English proof (translation)
Take `⟨s, hsS, hws⟩` from `Submodule.mem_sSup_iff_exists_finset.1 hw`. Establish `h` using `finset_sup_kstable ε τ s (fun S hS => ⟨(hsS hS).1, (hsS hS).2.1⟩)`. Use `⟨s.sup (id : Submodule ℂ H → Submodule ℂ H), h.1, ?_, h.2⟩` and prove the remaining obligations. Rewrite using `[Finset.sup_eq_iSup]`. Conclude with `hws`.
-/
theorem kfin_of_mem_lowKSub {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (hw : w ∈ lowKSub ε lam τ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ w ∈ S ∧ IsKStableOn ε τ S := by
  obtain ⟨s, hsS, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  have h := finset_sup_kstable ε τ s (fun S hS => ⟨(hsS hS).1, (hsS hS).2.1⟩)
  refine ⟨s.sup (id : Submodule ℂ H → Submodule ℂ H), h.1, ?_, h.2⟩
  rw [Finset.sup_eq_iSup]
  exact hws

/- English proof (translation)
Take `⟨P, hP, -, hmem⟩` from `hw`. Take `⟨S, hfd, hwS, hst⟩` from `kfin_of_mem_lowKSub hmem`. Conclude with `⟨S, hfd, hwS, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hP hst⟩`.
-/
theorem kfinHpk_of_lowUnitH {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  obtain ⟨S, hfd, hwS, hst⟩ := kfin_of_mem_lowKSub hmem
  exact ⟨S, hfd, hwS, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hP hst⟩

/- English proof (translation)
Introduce `g₀ _`. Use `⟨Set.univ, fun _ => (0 : H), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem zero_mem_smoothVecs (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ _
  refine ⟨Set.univ, fun _ => (0 : H), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  simp

def smoothSub (σ : Mx k r → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := smoothVecs (k := k) (r := r) σ
  add_mem' := fun h1 h2 => Formalism.MainNotions.LeviCoordinates.smooth_vectors_add h1 h2
  zero_mem' := zero_mem_smoothVecs σ
  smul_mem' := fun c _ h => Formalism.MainNotions.LeviCoordinates.smooth_vectors_smul c h

/- English proof (translation)
Establish `hw : w0 ∈ smoothVecs (k` using `k) (r := r) σ := hKS k r ε lam H σ hσ w0 (kfinHpk_of_lowUnitH hw0)`. Establish `hle : DDsp σ w0 ≤ smoothSub σ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha hb) hw hg`.

Introduce `u hu`. Conclude with `hle hu`.
-/
theorem ddSmooth_of [CompleteSpace H] (hKS : Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hσ : IsDSHpk k r ε lam σ)
    (hw0 : IsLowUnitH k r ε lam σ w0) : DDSmoothAt σ w0 := by
  have hw : w0 ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hσ w0 (kfinHpk_of_lowUnitH hw0)
  have hle : DDsp σ w0 ≤ smoothSub σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha hb) hw hg
  intro u hu
  exact hle hu

end Smooth

end Formalism.MainNotions.DoubleDerivativeSmoothness
