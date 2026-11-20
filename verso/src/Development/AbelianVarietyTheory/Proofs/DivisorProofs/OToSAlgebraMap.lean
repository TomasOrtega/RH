import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

open IsDedekindDomain NumberField Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.AdeleIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`.
-/
theorem one_tmul_mem {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    (1 : E) ⊗ₜ[F] y ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)

/- English proof (translation)
Rewrite using `[oToS_coe]`. Establish `h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r)`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]`.
-/
theorem oToS_algebraMap (r : 𝓞 F) :
    ((oToS F E (algebraMap (𝓞 F) (𝓞 E) r) : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) := by
  rw [oToS_coe]
  have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Take `⟨r, y, hy, e⟩` from `Formalism.UG.P.integral_adele_approximation_holds F d hd0 b hb`. Establish `ev : b v = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) d * y v`. Rewrite using `[e]`. Both sides reduce to the same expression.

Establish `hr : r ∈ v.asIdeal`. Rewrite `ev` using `[hv]`. Establish `e1 : algebraMap (𝓞 F) (v.adicCompletion F) r = -(algebraMap (𝓞 F) (v.adicCompletion F) d * y v)` using `eq_neg_of_add_eq_zero_left ev.symm`. Establish `e2` using `congrArg Valued.v e1`. Rewrite `e2` using `[Valuation.map_neg, Valuation.map_mul, Formalism.UG.P.csApprox_val_int, Formalism.UG.P.csApprox_val_int]`.

Rewrite `hd`, the goal using `[← v.intValuation_lt_one_iff_mem]`. Rewrite using `[e2]`. Establish `hy1 : Valued.v (y v) ≤ 1` using `hy v`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hy1) hd`. Establish `hz : ∀ x ∈ v.asIdeal, resS F w (oToS F E (algebraMap (𝓞 F) (𝓞 E) x)) = 0`.

Introduce `x hx`. Rewrite using `[resS_oToS, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `hx` using `[← hw]`. Conclude with `hx`. Establish `key : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) = oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + oToS F E (algebraMap (𝓞 F) (𝓞 E) d) * ⟨_, one_tmul_mem hy⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_add, Subring.coe_mul, oToS_algebraMap, oToS_algebraMap]`. Use `show (1 : E) ⊗ₜ[F] b = _ + _ * (1 : E) ⊗ₜ[F] y`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]`. Rewrite using `[key, map_add, map_mul, hz r hr, hz d hd, zero_mul, add_zero]`.
-/
theorem resS_eq_zero (w : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hw : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    {b : FiniteAdeleRing (𝓞 F) F} (hb : b ∈ intAd F) (hv : b v = 0) :
    resS F w ⟨_, one_tmul_mem hb⟩ = 0 := by
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F d hd0 b hb
  have ev : b v = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) d * y v := by
    rw [e]; rfl
  have hr : r ∈ v.asIdeal := by
    rw [hv] at ev
    have e1 : algebraMap (𝓞 F) (v.adicCompletion F) r = -(algebraMap (𝓞 F) (v.adicCompletion F) d * y v) :=
      eq_neg_of_add_eq_zero_left ev.symm
    have e2 := congrArg Valued.v e1
    rw [Valuation.map_neg, Valuation.map_mul, Formalism.UG.P.csApprox_val_int, Formalism.UG.P.csApprox_val_int] at e2
    rw [← v.intValuation_lt_one_iff_mem] at hd ⊢
    rw [e2]
    have hy1 : Valued.v (y v) ≤ 1 := hy v
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) hd
  have hz : ∀ x ∈ v.asIdeal, resS F w (oToS F E (algebraMap (𝓞 F) (𝓞 E) x)) = 0 := by
    intro x hx
    rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hw] at hx
    exact hx
  have key : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) =
      oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + oToS F E (algebraMap (𝓞 F) (𝓞 E) d) * ⟨_, one_tmul_mem hy⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, oToS_algebraMap, oToS_algebraMap]
    show (1 : E) ⊗ₜ[F] b = _ + _ * (1 : E) ⊗ₜ[F] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  rw [key, map_add, map_mul, hz r hr, hz d hd, zero_mul, add_zero]

open Classical in

def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if v ∈ S then 1 else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ind_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ind S v = if v ∈ S then 1 else 0 := rfl

/- English proof (translation)
Introduce `v`. Use `show ind S v ∈ v.adicCompletionIntegers F`. Rewrite using `[ind_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
theorem ind_mem (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S ∈ intAd F := by
  intro v
  show ind S v ∈ v.adicCompletionIntegers F
  rw [ind_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Use `show ind S v * ind S v = ind S v`. Rewrite using `[ind_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ind_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S * ind S = ind S := by
  apply Subtype.ext
  funext v
  show ind S v * ind S v = ind S v
  rw [ind_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `⟨⟨_, one_tmul_mem (ind_mem S)⟩, ?_, fun w v hw => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Apply `Subtype.ext show ((1 : E) ⊗ₜ[F] ind S) * ((1 : E) ⊗ₜ[F] ind S) = (1 : E) ⊗ₜ[F] ind S` to reduce the goal to its premises. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ind_mul_self]`. Establish `hb : 1 - ind S ∈ intAd F` using `sub_mem (one_mem _) (ind_mem S)`. Establish `h0` using `resS_eq_zero w v hw hb (by show 1 - ind S v = 0`.

Rewrite using `[ind_apply, if_pos hv, sub_self])`. Establish `e : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) = 1 - ⟨_, one_tmul_mem (ind_mem S)⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (1 : E) ⊗ₜ[F] (1 - ind S) = 1 - (1 : E) ⊗ₜ[F] ind S`. Rewrite using `[TensorProduct.tmul_sub]`.

Both sides reduce to the same expression. Rewrite `h0` using `[e, map_sub, map_one, sub_eq_zero]`. Conclude with `h0.symm`. Conclude with `resS_eq_zero w v hw (ind_mem S) (by rw [ind_apply, if_neg hv])`.
-/
theorem exists_idem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ ε : Formalism.L2.Herm.intAf F E, ε * ε = ε ∧ ∀ (w : Pl E) (v : HeightOneSpectrum (𝓞 F)),
      w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
        (v ∈ S → resS F w ε = 1) ∧ (v ∉ S → resS F w ε = 0) := by
  refine ⟨⟨_, one_tmul_mem (ind_mem S)⟩, ?_, fun w v hw => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · apply Subtype.ext
    show ((1 : E) ⊗ₜ[F] ind S) * ((1 : E) ⊗ₜ[F] ind S) = (1 : E) ⊗ₜ[F] ind S
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ind_mul_self]
  · have hb : 1 - ind S ∈ intAd F := sub_mem (one_mem _) (ind_mem S)
    have h0 := resS_eq_zero w v hw hb (by
      show 1 - ind S v = 0
      rw [ind_apply, if_pos hv, sub_self])
    have e : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) = 1 - ⟨_, one_tmul_mem (ind_mem S)⟩ := by
      apply Subtype.ext
      show (1 : E) ⊗ₜ[F] (1 - ind S) = 1 - (1 : E) ⊗ₜ[F] ind S
      rw [TensorProduct.tmul_sub]; rfl
    rw [e, map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  · exact resS_eq_zero w v hw (ind_mem S) (by rw [ind_apply, if_neg hv])

end GlobalTheory.AdeleIdem
