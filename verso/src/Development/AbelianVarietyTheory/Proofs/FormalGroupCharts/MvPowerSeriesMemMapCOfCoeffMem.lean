import Mathlib

open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem mvPowerSeries_map_surjective {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by
  intro g
  refine ⟨fun n => Function.surjInv hφ (MvPowerSeries.coeff n g), ?_⟩
  ext n
  exact Function.surjInv_eq hφ _

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem mvPowerSeries_mem_map_C_of_coeff_mem {σ R : Type} [CommRing R] (I : Ideal R)
    (hI : I.FG) (g : MvPowerSeries σ R) (hg : ∀ n, MvPowerSeries.coeff n g ∈ I) :
    g ∈ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I := by
  classical
  obtain ⟨s, rfl⟩ := hI
  have h : ∀ n, ∃ c : R → R, ∑ a ∈ s, c a * a = MvPowerSeries.coeff n g := by
    intro n
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hg n)
    exact ⟨c, by simpa [smul_eq_mul] using hc⟩
  choose c hc using h
  let G : R → MvPowerSeries σ R := fun a n => c n a
  have : g = ∑ a ∈ s, G a * MvPowerSeries.C a := by
    ext n
    rw [map_sum, ← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coeff_mul_C]
    rfl
  rw [this]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_left _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem span_X_pow_le_sup_of_residue :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ ι : Type) [Finite σ] (f : ι → MvPowerSeries σ T) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j)) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : T →+* MvPowerSeries σ T) (maximalIdeal T) := by
  intro T _ _ _ σ ι _ f M h
  set φ : MvPowerSeries σ T →+* MvPowerSeries σ (ResidueField T) :=
    MvPowerSeries.map (residue T) with hφ
  have hs : Function.Surjective φ := mvPowerSeries_map_surjective _ residue_surjective
  have h1 : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) =
      Ideal.map φ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext1 i
    simp [hφ]
  have h2 : Ideal.span (Set.range fun j => φ (f j)) = Ideal.map φ (Ideal.span (Set.range f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h1, h2, ← Ideal.map_pow, Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_surjective φ hs] at h
  refine h.trans (sup_le_sup_left ?_ _)
  intro g hg
  refine mvPowerSeries_mem_map_C_of_coeff_mem _ (IsNoetherian.noetherian _) g fun n => ?_
  have h0 : φ g = 0 := by simpa using hg
  rw [← residue_eq_zero_iff]
  have := congrArg (MvPowerSeries.coeff n) h0
  simpa [hφ] using this

end GlobalTheory
