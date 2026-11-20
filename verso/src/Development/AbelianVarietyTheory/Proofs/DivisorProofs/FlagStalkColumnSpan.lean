import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

noncomputable section

namespace GlobalTheory.FlagZ.Univ

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `v ⟨j, hj, rfl⟩`. Use `set b := stalkStd X N x`. Use `set c := (g⁻¹ * h).1 with hc`. Establish `hh : h.1 = g.1 * c`.

Rewrite using `[hc, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `e : ∑ i, h.1 i j • b i = ∑ k, c k j • ∑ i, g.1 i k • b i`. Repeatedly rewrite using `[Finset.smul_sum, smul_smul, hh, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < l`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`.

Rewrite using `[H k j hj (not_lt.1 hk), zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem colSpan_le_of_inv_mul {X : Scheme.{0}} {N : ℕ} {x : X} (g h : GL (Fin N) (X.presheaf.stalk x)) (l : ℕ)
    (H : ∀ i j : Fin N, (j : ℕ) < l → l ≤ (i : ℕ) → (g⁻¹ * h).1 i j = 0) :
    colSpan h.1 l ≤ colSpan g.1 l := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨j, hj, rfl⟩
  set b := stalkStd X N x
  set c := (g⁻¹ * h).1 with hc
  have hh : h.1 = g.1 * c := by
    rw [hc, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have e : ∑ i, h.1 i j • b i = ∑ k, c k j • ∑ i, g.1 i k • b i := by
    simp_rw [Finset.smul_sum, smul_smul, hh, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  rw [e]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [H k j hj (not_lt.1 hk), zero_smul]
    exact Submodule.zero_mem _

/- English proof (translation)
Introduce `ι _ N τ l y g hg`. Establish `key : ∀ g h : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = flagPt Prod.fst Prod.snd h → colSpan (h τ).1 l ≤ colSpan (g τ).1 l`. Introduce `g h e`. Use `colSpan_le_of_inv_mul _ _ l fun i j hj hi => ?_` and prove the remaining obligations. Establish `hlN : l < N + 1` using `by omega`.

Conclude with `(flagPt_eq_iff_below ι (ι × Fin (N + 1)) N Prod.fst Prod.snd _ g h).1 e τ i j ⟨(τ, ⟨l, hlN⟩), rfl, hj, hi⟩`. Use `le_antisymm (iInf_le_of_le g (iInf_le _ hg)) (le_iInf fun h => le_iInf fun hh => ?_)` and prove the remaining obligations. Conclude with `key h g (hh.trans hg.symm)`.
-/
theorem stalkStep_eq_colSpan : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N)
    (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)),
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y →
      stalkStep ι N τ l y = colSpan (g τ).1 l := by
  intro ι _ N τ l y g hg
  have key : ∀ g h : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y),
      flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = flagPt Prod.fst Prod.snd h →
        colSpan (h τ).1 l ≤ colSpan (g τ).1 l := by
    intro g h e
    refine colSpan_le_of_inv_mul _ _ l fun i j hj hi => ?_
    have hlN : l < N + 1 := by omega
    exact (flagPt_eq_iff_below ι (ι × Fin (N + 1)) N Prod.fst Prod.snd _ g h).1 e τ i j
      ⟨(τ, ⟨l, hlN⟩), rfl, hj, hi⟩
  refine le_antisymm (iInf_le_of_le g (iInf_le _ hg)) (le_iInf fun h => le_iInf fun hh => ?_)
  exact key h g (hh.trans hg.symm)

end GlobalTheory.FlagZ.Univ
