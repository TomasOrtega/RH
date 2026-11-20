import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Rewrite using `[Finsupp.card_toMultiset]`. Both sides reduce to the same expression.
-/
theorem degree_eq_card_toMultiset {α : Type} (d : α →₀ ℕ) :
    d.degree = Multiset.card (Finsupp.toMultiset d) := by
  rw [Finsupp.card_toMultiset]
  rfl

/- English proof (translation)
Establish `h1 : List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ`. Use `List.ext_getElem (by rw [List.length_ofFn, List.length_map, hd]) fun n h₁ h₂ => ?_` and prove the remaining obligations. Establish `hn : n < (Finsupp.toMultiset m).toList.length` using `by rwa [List.length_map] at h₂`. Rewrite using `[List.getElem_ofFn, List.getElem_map]`. Simplify using `only [monoLines]`.

Rewrite using `[dif_pos hn]`. Both sides reduce to the same expression. Rewrite using `[h1, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, hm, Multiset.map_map]`.
-/
theorem ofFn_monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J J' : Type}
    (ℓ : J' → HermLine ι) (e : J → J') (μ : J →₀ ℕ) (m : J' →₀ ℕ) (d : ℕ)
    (hm : Finsupp.toMultiset m = (Finsupp.toMultiset μ).map e)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    ((Finsupp.toMultiset μ).map (ℓ ∘ e)).toList.Perm (List.ofFn (monoLines ℓ m d)) := by
  have h1 : List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, hd]) fun n h₁ h₂ => ?_
    have hn : n < (Finsupp.toMultiset m).toList.length := by rwa [List.length_map] at h₂
    rw [List.getElem_ofFn, List.getElem_map]
    simp only [monoLines]
    rw [dif_pos hn]
    rfl
  rw [h1, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, hm,
    Multiset.map_map]

/- English proof (translation)
Establish `hms : Finsupp.toMultiset (Finsupp.mapDomain some μ) = (Finsupp.toMultiset μ).map some` using `(Finsupp.toMultiset_map _ _).symm`. Establish `hcard : Multiset.card (Finsupp.toMultiset μ) = dimFl Ψ N + 1`. Rewrite using `[← degree_eq_card_toMultiset, hμ]`. Establish `hdeg : (Finsupp.mapDomain some μ).degree = dimFl Ψ N + 1`. Rewrite using `[degree_eq_card_toMultiset, hms, Multiset.card_map, hcard]`.

Establish `hnone : (Finsupp.mapDomain some μ) none = 0` using `Finsupp.mapDomain_notin_range _ _ (by simp)`. Establish `hlen : (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length = dimFl Ψ N + 1`. Rewrite using `[Multiset.length_toList, hms, Multiset.card_map, hcard]`. Establish `hperm` using `ofFn_monoLines_perm (M.line t) some μ (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) hms hlen`. Establish `hall : ∀ r ∈ (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList, IsSmoothHerm (M.line t r)`.

Introduce `r hr`. Rewrite `hr` using `[Multiset.mem_toList, hms, Multiset.mem_map]`. Take `⟨r', -, rfl⟩` from `hr`. Conclude with `M.x_smooth t r'`. Establish `hsm : ∀ j, IsSmoothHerm (monoLines (M.line t) (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) j)`.

Introduce `j`. Establish `hj : (j : ℕ) < (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length`. Rewrite using `[hlen]`. Conclude with `j.2`. Simplify using `only [monoLines]`.

Rewrite using `[dif_pos hj]`. Conclude with `hall _ (List.get_mem _ _)`. Establish `hmain` using `arNum_linear_arList_symm.2 M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) _ _ hsm (by simpa [Function.comp_def, RootModel.line] using hperm)`. Unfold `RootModel.arMono`. Rewrite using `[if_pos hdeg, hnone, pow_zero, mul_one]`.

Use `congr 1`. Conclude with `hmain.symm`.
-/
theorem arMono_mapDomain_some {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ) (μ : Ψ × Fin N →₀ ℕ)
    (hμ : μ.degree = dimFl Ψ N + 1) :
    M.arMono II t (Finsupp.mapDomain some μ) =
      arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ) := by
  classical
  have hms : Finsupp.toMultiset (Finsupp.mapDomain some μ) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map _ _).symm
  have hcard : Multiset.card (Finsupp.toMultiset μ) = dimFl Ψ N + 1 := by
    rw [← degree_eq_card_toMultiset, hμ]
  have hdeg : (Finsupp.mapDomain some μ).degree = dimFl Ψ N + 1 := by
    rw [degree_eq_card_toMultiset, hms, Multiset.card_map, hcard]
  have hnone : (Finsupp.mapDomain some μ) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, hms, Multiset.card_map, hcard]
  have hperm := ofFn_monoLines_perm (M.line t) some μ (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) hms hlen
  have hall : ∀ r ∈ (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList, IsSmoothHerm (M.line t r) := by
    intro r hr
    rw [Multiset.mem_toList, hms, Multiset.mem_map] at hr
    obtain ⟨r', -, rfl⟩ := hr
    exact M.x_smooth t r'
  have hsm : ∀ j, IsSmoothHerm (monoLines (M.line t) (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) j) := by
    intro j
    have hj : (j : ℕ) < (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length := by
      rw [hlen]; exact j.2
    simp only [monoLines]
    rw [dif_pos hj]
    exact hall _ (List.get_mem _ _)
  have hmain := arNum_linear_arList_symm.2 M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) _ _ hsm
    (by simpa [Function.comp_def, RootModel.line] using hperm)
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  congr 1
  exact hmain.symm

/- English proof (translation)
Introduce `Ψ _ _ N M II hII t F hF`. Establish `hmono : ∀ μ ∈ F.support, M.arFun II t (toA (monomial μ (F.coeff μ))) = F.coeff μ * (arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ))`. Introduce `μ hμ`. Establish `hdeg : μ.degree = dimFl Ψ N + 1`. Establish `h` using `hF (MvPolynomial.mem_support_iff.1 hμ)`.

Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `h`. Establish `h1 : toA (monomial μ (F.coeff μ)) = (F.coeff μ) • (basisMonomials (Option (Ψ × Fin N)) ℝ) (Finsupp.mapDomain some μ)`. Simplify using `[toA, MvPolynomial.rename_monomial, MvPolynomial.smul_monomial]`. Rewrite using `[h1, map_smul, RootModel.arFun, Module.Basis.constr_basis, smul_eq_mul, arMono_mapDomain_some M II hII t μ hdeg]`.

Establish `hsum : toA F = ∑ μ ∈ F.support, toA (monomial μ (F.coeff μ))`. Unfold `toA`. Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum]`. Rewrite using `[hsum, map_sum, Finset.sum_congr rfl hmono]`.

Unfold `arNum`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`.
-/
theorem arFun_toA_eq_arNum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (t : ℝ) (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N + 1) → M.arFun II t (toA F) = arNum (II M.K M.ι) M.P (M.x t) F / (M.δ : ℝ) := by
  intro Ψ _ _ N M II hII t F hF
  classical
  have hmono : ∀ μ ∈ F.support, M.arFun II t (toA (monomial μ (F.coeff μ))) =
      F.coeff μ * (arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ)) := by
    intro μ hμ
    have hdeg : μ.degree = dimFl Ψ N + 1 := by
      have h := hF (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact h
    have h1 : toA (monomial μ (F.coeff μ)) =
        (F.coeff μ) • (basisMonomials (Option (Ψ × Fin N)) ℝ) (Finsupp.mapDomain some μ) := by
      simp [toA, MvPolynomial.rename_monomial, MvPolynomial.smul_monomial]
    rw [h1, map_smul, RootModel.arFun, Module.Basis.constr_basis, smul_eq_mul,
      arMono_mapDomain_some M II hII t μ hdeg]
  have hsum : toA F = ∑ μ ∈ F.support, toA (monomial μ (F.coeff μ)) := by
    unfold toA
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
  rw [hsum, map_sum, Finset.sum_congr rfl hmono]
  unfold arNum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num
