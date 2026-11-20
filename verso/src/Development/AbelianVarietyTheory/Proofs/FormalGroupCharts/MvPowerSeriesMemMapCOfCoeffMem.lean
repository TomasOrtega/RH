import Mathlib

open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `g`. Use `⟨fun n => Function.surjInv hφ (MvPowerSeries.coeff n g), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Conclude with `Function.surjInv_eq hφ _`.
-/
theorem mvPowerSeries_map_surjective {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by
  intro g
  refine ⟨fun n => Function.surjInv hφ (MvPowerSeries.coeff n g), ?_⟩
  ext n
  exact Function.surjInv_eq hφ _

/- English proof (translation)
Take `⟨s, rfl⟩` from `hI`. Establish `h : ∀ n, ∃ c : R → R, ∑ a ∈ s, c a * a = MvPowerSeries.coeff n g`. Introduce `n`. Take `⟨c, -, hc⟩` from `Submodule.mem_span_finset.1 (hg n)`. Conclude with `⟨c, by simpa [smul_eq_mul] using hc⟩`.

Use `choose c hc using h`. Set `G : R → MvPowerSeries σ R` to `fun a n => c n a`. Establish `: g = ∑ a ∈ s, G a * MvPowerSeries.C a`. Use extensionality with `n`. Rewrite using `[map_sum, ← hc n]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_mul_C]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `Ideal.sum_mem _ fun a ha => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations.

Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span ha)`.
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
Introduce `T _ _ _ σ ι _ f M h`. Use `set φ : MvPowerSeries σ T →+* MvPowerSeries σ (ResidueField T) := MvPowerSeries.map (residue T) with hφ`. Establish `hs : Function.Surjective φ` using `mvPowerSeries_map_surjective _ residue_surjective`. Establish `h1 : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) = Ideal.map φ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`.

Use `congr 2`. Use `ext1 i`. Simplify using `[hφ]`. Establish `h2 : Ideal.span (Set.range fun j => φ (f j)) = Ideal.map φ (Ideal.span (Set.range f))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite `h` using `[h1, h2, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_surjective φ hs]`. Use `h.trans (sup_le_sup_left ?_ _)` and prove the remaining obligations. Introduce `g hg`. Use `mvPowerSeries_mem_map_C_of_coeff_mem _ (IsNoetherian.noetherian _) g fun n => ?_` and prove the remaining obligations.

Establish `h0 : φ g = 0` using `by simpa using hg`. Rewrite using `[← residue_eq_zero_iff]`. Use `congrArg (MvPowerSeries.coeff n) h0` as an intermediate fact. Simplify `this` using `[hφ]`.
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
