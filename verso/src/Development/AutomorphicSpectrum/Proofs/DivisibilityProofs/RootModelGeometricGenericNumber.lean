import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralEqGenericIntersectionStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GeoModel

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Unfold `intNumL intNum mixedDiff`. Rewrite using `[List.ofFn_get]`.
-/
theorem intNumL_ofFn' {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

/- English proof (translation)
Establish `hcard : (Finsupp.toMultiset μ).card = dimFl Ψ N`. Rewrite using `[Finsupp.card_toMultiset, ← hμ, Finsupp.degree_apply]`. Both sides reduce to the same expression. Establish `hmap : Finsupp.toMultiset (μ.mapDomain some) = (Finsupp.toMultiset μ).map some` using `(Finsupp.toMultiset_map μ some).symm`. Establish `hdeg : (μ.mapDomain some).degree = dimFl Ψ N`.

Rewrite using `[← hμ]`. Proceed by induction on `μ using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => simp [Finsupp.mapDomain_add]`. Consider the case `single a b => simp`.

Establish `hnone : (μ.mapDomain some) none = 0` using `Finsupp.mapDomain_notin_range _ _ (by simp)`. Establish `hlen : (Finsupp.toMultiset (μ.mapDomain some)).toList.length = dimFl Ψ N`. Rewrite using `[Multiset.length_toList, hmap, Multiset.card_map, hcard]`. Unfold `RootModel.geoMono`. Rewrite using `[if_pos hdeg, hnone, pow_zero, mul_one]`.

Use `set L := monoLines (M.line 1) (μ.mapDomain some) (dimFl Ψ N) with hLdef`. Establish `hL : ∀ k : Fin (dimFl Ψ N), L k = M.line 1 ((Finsupp.toMultiset (μ.mapDomain some)).toList.get ⟨k, by rw [hlen]; exact k.2⟩)`. Introduce `k`. Simplify using `only [hLdef, monoLines]`. Rewrite using `[dif_pos (by rw [hlen]; exact k.2)]`.

Establish `hline : ∀ o, IsSmoothHerm (M.line 1 o)`. Introduce and unpack `(_ | r)`. Conclude with `M.A_smooth`. Conclude with `M.x_smooth 1 r`. Establish `hsm : ∀ j, IsSmoothHerm (L j)` using `fun j => by rw [hL j]; exact hline _`.

Rewrite using `[GlobalTheory.T.log_integral_eq_generic_intersection M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII _ _) L hsm, ← intNumL_ofFn']`. Use `congr 2`. Use `NumericalSegreProof.intNumL_perm ℚ _ ?_` and prove the remaining obligations. Establish `hlist : List.ofFn (fun j => (L j).a) = (Finsupp.toMultiset (μ.mapDomain some)).toList.map (fun o => (M.line 1 o).a)`. Apply `List.ext_getElem` to reduce the goal to its premises.

Simplify using `[hlen]`. Introduce `i h1 h2`. Simplify using `only [List.getElem_ofFn, List.getElem_map]`. Rewrite using `[hL]`. Both sides reduce to the same expression.

Rewrite using `[hlist, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, hmap, Multiset.map_map]`. Rewrite using `[classList, Multiset.coe_toList]`. Use `Multiset.map_congr rfl fun r _ => ?_` and prove the remaining obligations. Conclude with `M.x_deg 1 r`.
-/
theorem geoMono_mapDomain_some (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (μ : Ψ × Fin N →₀ ℕ) (hμ : μ.degree = dimFl Ψ N) :
    M.geoMono (μ.mapDomain some) = (intNumL ℚ (extTo ℚ M.P) (classList M.xdeg μ) : ℝ) / (M.δ : ℝ) := by
  have hcard : (Finsupp.toMultiset μ).card = dimFl Ψ N := by
    rw [Finsupp.card_toMultiset, ← hμ, Finsupp.degree_apply]
    rfl
  have hmap : Finsupp.toMultiset (μ.mapDomain some) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map μ some).symm
  have hdeg : (μ.mapDomain some).degree = dimFl Ψ N := by
    rw [← hμ]
    induction μ using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [Finsupp.mapDomain_add]
    | single a b => simp
  have hnone : (μ.mapDomain some) none = 0 := Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (μ.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [Multiset.length_toList, hmap, Multiset.card_map, hcard]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  set L := monoLines (M.line 1) (μ.mapDomain some) (dimFl Ψ N) with hLdef
  have hL : ∀ k : Fin (dimFl Ψ N), L k = M.line 1 ((Finsupp.toMultiset (μ.mapDomain some)).toList.get
      ⟨k, by rw [hlen]; exact k.2⟩) := by
    intro k
    simp only [hLdef, monoLines]
    rw [dif_pos (by rw [hlen]; exact k.2)]
  have hline : ∀ o, IsSmoothHerm (M.line 1 o) := by
    rintro (_ | r)
    · exact M.A_smooth
    · exact M.x_smooth 1 r
  have hsm : ∀ j, IsSmoothHerm (L j) := fun j => by rw [hL j]; exact hline _
  rw [GlobalTheory.T.log_integral_eq_generic_intersection M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII _ _) L hsm, ← intNumL_ofFn']
  congr 2
  refine NumericalSegreProof.intNumL_perm ℚ _ ?_
  have hlist : List.ofFn (fun j => (L j).a) =
      (Finsupp.toMultiset (μ.mapDomain some)).toList.map (fun o => (M.line 1 o).a) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      rw [hL]
      rfl
  rw [hlist, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, hmap, Multiset.map_map]
  rw [classList, Multiset.coe_toList]
  refine Multiset.map_congr rfl fun r _ => ?_
  exact M.x_deg 1 r

/- English proof (translation)
Introduce `Ψ _ _ N M _ II hII F hF`. Establish `h1 : toA F = ∑ μ ∈ F.support, F.coeff μ • basisMonomials (Option (Ψ × Fin N)) ℝ (μ.mapDomain some)` using `by conv_lhs => rw [toA, F.as_sum, map_sum]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[rename_monomial, coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_sum, genNum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hd : μ.degree = dimFl Ψ N`. Conclude with `(DFunLike.congr_fun Finsupp.degree_eq_weight_one μ).trans (hF (mem_support_iff.1 hμ))`. Rewrite using `[map_smul, RootModel.geoFun, Module.Basis.constr_basis, geoMono_mapDomain_some M II hII μ hd, smul_eq_mul, List.append_nil, mul_div_assoc]`.
-/
theorem geoFun_toA_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K]
    (II : IntersectionSystem), IsIntersectionSystem II → ∀ (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N) →
    M.geoFun (toA F) = genNum ℚ (extTo ℚ M.P) M.xdeg F [] / (M.δ : ℝ) := by
  intro Ψ _ _ N M _ II hII F hF
  have h1 : toA F = ∑ μ ∈ F.support, F.coeff μ • basisMonomials (Option (Ψ × Fin N)) ℝ (μ.mapDomain some) := by
    conv_lhs => rw [toA, F.as_sum, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_sum, genNum, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : μ.degree = dimFl Ψ N := by
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one μ).trans (hF (mem_support_iff.1 hμ))
  rw [map_smul, RootModel.geoFun, Module.Basis.constr_basis, geoMono_mapDomain_some M II hII μ hd,
    smul_eq_mul, List.append_nil, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num.GeoModel
