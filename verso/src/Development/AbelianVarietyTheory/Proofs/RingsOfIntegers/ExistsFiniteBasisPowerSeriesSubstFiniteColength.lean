import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

open IsLocalRing MvPowerSeries

namespace GlobalTheory.FiniteColength

/- English proof (translation)
Use `set I : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range fun j => ψ (X j)) with hI`. Set `L : (Fin n → R) →ₗ[R] (MvPowerSeries σ R ⧸ I)` to `(Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Fintype.linearCombination R e`. Establish `hL : ∀ a, L a = Ideal.Quotient.mk I (∑ i, algebraMap R _ (a i) * e i)` using `fun a => by`. Simplify using `[L, Fintype.linearCombination_apply, Algebra.smul_def]`. Establish `hinj : Function.Injective L`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Rewrite `ha` using `[hL, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun]`. Take `⟨g, hg⟩` from `ha`. Use `choose c hc _ using fun j => he (g j)`.

Establish `h1 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (∑ j, c j i * X j) * e i`. Rewrite using `[← hg]`. Simplify using `only [map_sum, map_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hc j, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `h2 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (algebraMap R _ (a i)) * e i`. Simplify using `only [AlgHom.commutes]`. Establish `h3` using `(he _).unique h2 h1`.

Use function extensionality and compare the values at `i`. Establish `h4` using `congrArg constantCoeff (congrFun h3 i)`. Simplify `h4` using `[MvPowerSeries.algebraMap_apply]`. Establish `hsurj : Function.Surjective L`. Introduce `y`.

Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨c, hc, -⟩` from `he g`. Use `⟨fun i => constantCoeff (c i), ?_⟩` and prove the remaining obligations. Rewrite using `[hL, eq_comm, Ideal.Quotient.eq, hc, ← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← sub_mul]`. Conclude with `Ideal.mul_mem_right _ _ (algHom_sub_constantCoeff_mem ψ (K := I) (fun j => Ideal.subset_span ⟨j, rfl⟩) (c i))`. Rewrite using `[← (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq]`. Simplify using the standard rewrite rules.
-/
theorem finrank_quotient_eq_of_existsUnique {R : Type} [CommRing R] [Nontrivial R] {σ τ : Type}
    [Fintype τ] (ψ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R) {n : ℕ}
    (e : Fin n → MvPowerSeries σ R)
    (he : ∀ g, ∃! c : Fin n → MvPowerSeries τ R, g = ∑ i, ψ (c i) * e i) :
    Module.finrank R (MvPowerSeries σ R ⧸ Ideal.span (Set.range fun j => ψ (X j))) = n := by
  set I : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range fun j => ψ (X j)) with hI
  let L : (Fin n → R) →ₗ[R] (MvPowerSeries σ R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Fintype.linearCombination R e
  have hL : ∀ a, L a = Ideal.Quotient.mk I (∑ i, algebraMap R _ (a i) * e i) := fun a => by
    simp [L, Fintype.linearCombination_apply, Algebra.smul_def]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hL, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun] at ha
    obtain ⟨g, hg⟩ := ha
    choose c hc _ using fun j => he (g j)
    have h1 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (∑ j, c j i * X j) * e i := by
      rw [← hg]
      simp only [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (algebraMap R _ (a i)) * e i := by
      simp only [AlgHom.commutes]
    have h3 := (he _).unique h2 h1
    funext i
    have h4 := congrArg constantCoeff (congrFun h3 i)
    simpa [MvPowerSeries.algebraMap_apply] using h4
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, -⟩ := he g
    refine ⟨fun i => constantCoeff (c i), ?_⟩
    rw [hL, eq_comm, Ideal.Quotient.eq, hc, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    exact Ideal.mul_mem_right _ _
      (algHom_sub_constantCoeff_mem ψ (K := I) (fun j => Ideal.subset_span ⟨j, rfl⟩) (c i))
  rw [← (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq]
  simp

/- English proof (translation)
Introduce `V _ _ _ _ _ σ _ φ h0 hM`. Set `ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries σ V` to `substAlgHom (hasSubst_of_constantCoeff_zero h0)`. Establish `hX : (fun j => ψ (X j)) = φ` using `funext fun j => substAlgHom_X _ j`. Establish `h1 : ∀ j, constantCoeff (ψ (X j)) ∈ maximalIdeal V` using `fun j => by`. Simplify using `[congrFun hX j, h0]`.

Establish `h2 : FormalIsogeny.FiniteReduction fun j => ψ (X j)` using `hX ▸ FormalIsogeny.finiteReduction_iff.2 hM`. Take `⟨-, -, -, n, e, he⟩` from `FormalIsogeny.flat_injective_basis_of_finiteReduction ψ h1 h2 le_rfl`. Use `⟨n, e, ?_, fun f => ?_⟩` and prove the remaining obligations. Use `finrank_quotient_eq_of_existsUnique ψ e he` as an intermediate fact. Rewrite `this` using `[hX]`. Then use the resulting hypothesis.

Establish `hψ : ∀ g, ψ g = MvPowerSeries.subst φ g` using `fun g => substAlgHom_apply _ g`. Simplify `he f` using `only [hψ]`.
-/
theorem exists_basis_subst_finrank_quotient : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∃ (r : ℕ) (b : Fin r → MvPowerSeries σ V), Module.finrank V (MvPowerSeries σ V ⧸ Ideal.span (Set.range φ)) = r ∧ ∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i := by
  intro V _ _ _ _ _ σ _ φ h0 hM
  let ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries σ V :=
    substAlgHom (hasSubst_of_constantCoeff_zero h0)
  have hX : (fun j => ψ (X j)) = φ := funext fun j => substAlgHom_X _ j
  have h1 : ∀ j, constantCoeff (ψ (X j)) ∈ maximalIdeal V := fun j => by
    simp [congrFun hX j, h0]
  have h2 : FormalIsogeny.FiniteReduction fun j => ψ (X j) :=
    hX ▸ FormalIsogeny.finiteReduction_iff.2 hM
  obtain ⟨-, -, -, n, e, he⟩ :=
    FormalIsogeny.flat_injective_basis_of_finiteReduction ψ h1 h2 le_rfl
  refine ⟨n, e, ?_, fun f => ?_⟩
  · have := finrank_quotient_eq_of_existsUnique ψ e he
    rwa [hX] at this
  · have hψ : ∀ g, ψ g = MvPowerSeries.subst φ g := fun g => substAlgHom_apply _ g
    simpa only [hψ] using he f

end GlobalTheory.FiniteColength
