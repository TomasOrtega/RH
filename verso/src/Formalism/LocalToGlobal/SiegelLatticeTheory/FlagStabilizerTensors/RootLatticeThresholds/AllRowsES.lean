import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsGA

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsES

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsFin
  Formalism.L2.SG.Pf.AllRowsRhoX

variable {D : D7}

abbrev CV (D : D7) : Type := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)

def Ea (a : CV D) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun γ : G0g D.nd =>
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)

/- English proof (translation)
Introduce `k` and use `⟨D.host.g_prime k⟩ ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) := by simp [Ea, MonoidAlgebra.coeff_ofCoeff]`.
-/
theorem Ea_coeff (a : CV D) (γ : G0g D.nd) :
    (Ea a).coeff γ = haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) := by
  simp [Ea, MonoidAlgebra.coeff_ofCoeff]

open Classical in
/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_filter]`. Unfold `ES`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[Ea_coeff]`. Both sides reduce to the same expression.
-/
theorem ES_eq (S : Set (Tup2 D)) : ES S = ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a := by
  apply MonoidAlgebra.ext
  ext γ
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_filter]
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Ea_coeff]
  · rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf a i, ← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf b i, h]`.
-/
theorem monicOf_inj {g : ℕ} [Fact g.Prime] {N : ℕ} {a b : Fin N → ZMod g}
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  rw [← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf a i, ← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf b i, h]

open Classical in
/- English proof (translation)
Establish `: ∀ k, Fact (D.host.g k).Prime` using `fun k => ⟨D.host.g_prime k⟩`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[coeff_mul_fin]`. Simplify using `only [Ea_coeff]`.

Establish `key : ∑ δ : G0g D.nd, (∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (δ kv)) * ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))).coeff ((δ⁻¹ * γ) kv) = ∏ kv : (Σ k : Fin 2, D …`. Simplify using `only [coeff_mul_fin]`. Rewrite using `[Fintype.prod_sum]`. Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Both sides reduce to the same expression. Rewrite using `[key]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Rewrite using `[Ea_coeff]`.

Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[D.ntypes.eSer_idem]`. Choose the witnesses or unpack the hypotheses as in `⟨kv, hkv⟩ : ∃ kv, a kv ≠ b kv := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hab (funext h)`. Establish `h0 : (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) * (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) = 0` using `D.ntypes.eSer_orth kv.1 _ _ fun h => hkv (monicOf_inj h)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; simp)]`. Simplify using the standard rewrite rules.
-/
theorem Ea_mul (a b : CV D) : Ea a * Ea b = if a = b then Ea a else 0 := by
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ea_coeff]
  have key : ∑ δ : G0g D.nd, (∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (δ kv)) *
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))).coeff ((δ⁻¹ * γ) kv) =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) *
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv)))).coeff (γ kv) := by
    simp only [coeff_mul_fin]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [key]
  split_ifs with hab
  · subst hab
    rw [Ea_coeff]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [D.ntypes.eSer_idem]
  · obtain ⟨kv, hkv⟩ : ∃ kv, a kv ≠ b kv := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have h0 : (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) * (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) = 0 :=
      D.ntypes.eSer_orth kv.1 _ _ fun h => hkv (monicOf_inj h)
    rw [Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; simp)]
    simp

open Classical in

/- English proof (translation)
Rewrite using `[ES_eq, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Simplify using `only [Ea_mul]`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd ha h), if_pos rfl]`.
-/
theorem ES_idem (S : Set (Tup2 D)) : ES S * ES S = ES S := by
  rw [ES_eq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Ea_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd ha h), if_pos rfl]

/- English proof (translation)
The claim follows from `central_of_class _ (ES_conj S) y`.
-/
theorem ES_central (S : Set (Tup2 D)) (y : MonoidAlgebra ℂ (G0g D.nd)) : ES S * y = y * ES S :=
  central_of_class _ (ES_conj S) y

/- English proof (translation)
The claim follows from `selfadj_of_central_idem _ (ES_idem S) (ES_central S)`.
-/
theorem ES_selfadj (S : Set (Tup2 D)) : conjA (ES S) = ES S :=
  selfadj_of_central_idem _ (ES_idem S) (ES_central S)

end Formalism.L2.SG.Pf.AllRowsES
