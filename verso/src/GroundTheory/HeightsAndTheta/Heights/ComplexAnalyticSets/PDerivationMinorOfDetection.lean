import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationMinorOfDetection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Introduce `T _ P _ h f hfP hind hdet`. Set `A` to `Localization.AtPrime P`. Set `K` to `ResidueField A`. Set `π : T →+* K` to `(residue A).comp (algebraMap T A)`. Establish `hπ : ∀ x, π x = 0 ↔ x ∈ P` using `fun x => by show residue A (algebraMap T A x) = 0 ↔ x ∈ P`.

Rewrite using `[residue_eq_zero_iff]`. Conclude with `IsLocalization.AtPrime.to_map_mem_maximal_iff A P x`. Set `v : Derivation ℤ T T → Fin h → K` to `fun D i => π (D (f i))`. Establish `hspan : Submodule.span K (Set.range v) = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Establish `hφv : ∀ w : Fin h → K, φ w = ∑ i, w i * φ (Pi.single i 1)` using `fun w => by conv_lhs => rw [pi_eq_sum_univ w]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`.

Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`. Use `choose a ha using fun i => residue_surjective (R := A) (φ (Pi.single i 1))`. Take `⟨s, hs⟩` from `IsLocalization.exist_integer_multiples P.primeCompl Finset.univ a`. Use `choose b hb using fun i => hs i (Finset.mem_univ i)`.

Establish `hπb : ∀ i, π (b i) = π s * φ (Pi.single i 1)` using `fun i => by`. Simplify using `only [π, RingHom.comp_apply, hb i, Algebra.smul_def, map_mul, ha]`. Establish `hsq` using `hdet (∑ i, b i * f i) (Ideal.sum_mem _ fun i _ => P.mul_mem_left _ (hfP i)) fun D => by`. Establish `h1 : ∑ i, b i * D (f i) ∈ P`. Establish `hD : φ (v D) = 0` using `hφ (Submodule.subset_span ⟨D, rfl⟩)`.

Rewrite `hD` using `[hφv]`. Rewrite using `[← hπ, map_sum]`. Simplify using `only [map_mul, hπb]`. Rewrite using `[show ∑ i, π s * φ (Pi.single i 1) * π (D (f i)) = π s * ∑ i, v D i * φ (Pi.single i 1) by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [v]; ring, hD, mul_zero]`.

Establish `hl : ∀ i, D (b i * f i) = b i * D (f i) + f i * D (b i)` using `fun i => by`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Rewrite using `[map_sum]`. Simplify using `only [hl, Finset.sum_add_distrib]`. Conclude with `P.add_mem h1 (Ideal.sum_mem _ fun i _ => P.mul_mem_right _ (hfP i))`.

Establish `hbP : ∀ i, b i ∈ P` using `fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).1 (hind (fun i => algebraMap T A (b i)) (by simpa only [map_sum, map_mul] using hsq) i)`. Establish `hsP : π s ≠ 0` using `fun h0 => s.2 ((hπ s).1 h0)`. Establish `he : ∀ i, φ (Pi.single i 1) = 0` using `fun i => by`. Use `(hπ (b i)).2 (hbP i)` as an intermediate fact. Rewrite `this` using `[hπb]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hsP`. Conclude with `hφ0 (LinearMap.ext fun w => by simp [hφv w, he])`. Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent'.{0} K v`. Set `bas` to `Module.Basis.mk hli (by rw [hsp, hspan])`. Establish `hfin : Finite κ` using `Module.Finite.finite_basis bas`.

Establish `hκ : Nat.card κ = h` using `by rw [← Module.finrank_eq_nat_card_basis bas, Module.finrank_fin_fun]`. Set `e : Fin h ≃ κ` to `(finCongr hκ.symm).trans (Finite.equivFin κ).symm`. Use `⟨fun j => a (e j), fun hmem => ?_⟩` and prove the remaining obligations. Establish `hunit : IsUnit (Matrix.of fun i j => v (a (e j)) i)`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`.

Conclude with `hli.comp e e.injective`. Establish `hne : π (Matrix.of fun i j => a (e j) (f i)).det ≠ 0`. Rewrite using `[RingHom.map_det]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero`. Conclude with `hne ((hπ _).2 hmem)`.
-/
theorem DerivationMinorOfDetection.proof : DerivationMinorOfDetection.Statement := by
  intro T _ P _ h f hfP hind hdet
  let A := Localization.AtPrime P
  let K := ResidueField A
  let π : T →+* K := (residue A).comp (algebraMap T A)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    show residue A (algebraMap T A x) = 0 ↔ x ∈ P
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff A P x
  let v : Derivation ℤ T T → Fin h → K := fun D i => π (D (f i))
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφv : ∀ w : Fin h → K, φ w = ∑ i, w i * φ (Pi.single i 1) := fun w => by
      conv_lhs => rw [pi_eq_sum_univ w]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    choose a ha using fun i => residue_surjective (R := A) (φ (Pi.single i 1))
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ a
    choose b hb using fun i => hs i (Finset.mem_univ i)
    have hπb : ∀ i, π (b i) = π s * φ (Pi.single i 1) := fun i => by
      simp only [π, RingHom.comp_apply, hb i, Algebra.smul_def, map_mul, ha]
    have hsq := hdet (∑ i, b i * f i) (Ideal.sum_mem _ fun i _ => P.mul_mem_left _ (hfP i)) fun D => by
      have h1 : ∑ i, b i * D (f i) ∈ P := by
        have hD : φ (v D) = 0 := hφ (Submodule.subset_span ⟨D, rfl⟩)
        rw [hφv] at hD
        rw [← hπ, map_sum]
        simp only [map_mul, hπb]
        rw [show ∑ i, π s * φ (Pi.single i 1) * π (D (f i)) = π s * ∑ i, v D i * φ (Pi.single i 1) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [v]; ring, hD, mul_zero]
      have hl : ∀ i, D (b i * f i) = b i * D (f i) + f i * D (b i) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      rw [map_sum]
      simp only [hl, Finset.sum_add_distrib]
      exact P.add_mem h1 (Ideal.sum_mem _ fun i _ => P.mul_mem_right _ (hfP i))
    have hbP : ∀ i, b i ∈ P := fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).1
      (hind (fun i => algebraMap T A (b i)) (by simpa only [map_sum, map_mul] using hsq) i)
    have hsP : π s ≠ 0 := fun h0 => s.2 ((hπ s).1 h0)
    have he : ∀ i, φ (Pi.single i 1) = 0 := fun i => by
      have := (hπ (b i)).2 (hbP i)
      rw [hπb] at this
      exact (mul_eq_zero.1 this).resolve_left hsP
    exact hφ0 (LinearMap.ext fun w => by simp [hφv w, he])
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  let bas := Module.Basis.mk hli (by rw [hsp, hspan])
  have hfin : Finite κ := Module.Finite.finite_basis bas
  have hκ : Nat.card κ = h := by rw [← Module.finrank_eq_nat_card_basis bas, Module.finrank_fin_fun]
  let e : Fin h ≃ κ := (finCongr hκ.symm).trans (Finite.equivFin κ).symm
  refine ⟨fun j => a (e j), fun hmem => ?_⟩
  have hunit : IsUnit (Matrix.of fun i j => v (a (e j)) i) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  have hne : π (Matrix.of fun i j => a (e j) (f i)).det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  exact hne ((hπ _).2 hmem)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
