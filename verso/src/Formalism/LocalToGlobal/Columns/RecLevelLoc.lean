import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn resS)
open Formalism.UG Formalism.UG.P

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]`.
-/
theorem rll_eps_eq (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v = (1 : E) ⊗ₜ[F] (afsplitI v 1 : Formalism.L2.Herm.Af F) := by
  rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]

/- English proof (translation)
Establish `h : (∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) w = ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F) w` using `map_sum (evalV F w) _ _`. Rewrite using `[h]`. Distinguish the cases in `hw : w ∈ S`. Rewrite using `[if_pos hw, Finset.sum_eq_single w]`. Conclude with `afsplitI_self w 1`.

Introduce `v _ hv`. Conclude with `afsplitI_ne v w (Ne.symm hv) 1`. Introduce `h'`. Conclude with `absurd hw h'`. Rewrite using `[if_neg hw]`.

Use `Finset.sum_eq_zero fun v hv => afsplitI_ne v w ?_ 1` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hw hv`.
-/
theorem rll_sum_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) w = open Classical in if w ∈ S then 1 else 0 := by
  classical
  have h : (∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) w = ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F) w :=
    map_sum (evalV F w) _ _
  rw [h]
  by_cases hw : w ∈ S
  · rw [if_pos hw, Finset.sum_eq_single w]
    · exact afsplitI_self w 1
    · intro v _ hv; exact afsplitI_ne v w (Ne.symm hv) 1
    · intro h'; exact absurd hw h'
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun v hv => afsplitI_ne v w ?_ 1
    rintro rfl; exact hw hv

/- English proof (translation)
Take `⟨D, hD, hDx⟩` from `levelaf_denom (E := E) x`. Establish `hfin` using `levelaf_finite_places D hD`. Use `set S := hfin.toFinset with hS`. Establish `hmem : ∀ v, v ∈ S ↔ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1` using `fun v => by`. Rewrite using `[hS, Set.Finite.mem_toFinset]`.

Both sides reduce to the same expression. Set `w' : intAd F` to `Formalism.L2.DIV.mkAd (fun v => if v ∈ S then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) (fun v => by`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [hv, if_true]`. Conclude with `zero_mem _`.

Simplify using `only [hv, if_false]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]`. Establish `h1 : 1 ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D)` using `not_lt.1 (fun hlt => hv ((hmem v).2 hlt))`. Conclude with `inv_le_one_of_one_le₀ h1)`. Establish `key : algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) D * (w' : Formalism.L2.Herm.Af F) = 1 - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)`.

Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Establish `e1 : (algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) D * (w' : Formalism.L2.Herm.Af F)) v = algebraMap (𝓞 F) (v.adicCompletion F) D * (if v ∈ S then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹)` using `rfl`. Establish `e2 : ((1 : Formalism.L2.Herm.Af F) - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) v = 1 - (∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) v` using `rfl`. Rewrite using `[e1, e2, rll_sum_apply]`. Distinguish the cases in `hv : v ∈ S`.

Simplify using `[hv]`. Simplify using `only [hv, if_false, sub_zero]`. Conclude with `mul_inv_cancel₀ (levelaf_algebraMap_ne_zero v D hD)`. Establish `hx : x = ∑ v ∈ S, afsplitIE v (prV (E` using `E) v x) + ((1 : E) ⊗ₜ[F] (w' : Formalism.L2.Herm.Af F)) * (levelafC E D * x) := by`. Establish `e3 : ((1 : E) ⊗ₜ[F] (w' : Formalism.L2.Herm.Af F)) * (levelafC E D * x) = ((1 : E) ⊗ₜ[F] (1 - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F))) * x`.

Rewrite using `[← mul_assoc, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (w' : Formalism.L2.Herm.Af F), key]`. Rewrite using `[e3, TensorProduct.tmul_sub, TensorProduct.tmul_sum, sub_mul, Finset.sum_mul, ← Algebra.TensorProduct.one_def, one_mul]`. Establish `e4 : ∀ v ∈ S, afsplitIE v (prV (E` using `E) v x) = ((1 : E) ⊗ₜ[F] (afsplitI v 1 : Formalism.L2.Herm.Af F)) * x := fun v _ => by rw [afsplit_decomp, rll_eps_eq]`. Rewrite using `[Finset.sum_congr rfl e4]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hx]`. Use `add_mem (sum_mem fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ hDx)` and prove the remaining obligations. Conclude with `(Formalism.L2.DIV.adS F E w').2`.
-/
theorem rll_int_of_loc (x : E ⊗[F] Formalism.L2.Herm.Af F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v x ∈ Formalism.BasicNotions.intV E v) : x ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨D, hD, hDx⟩ := levelaf_denom (E := E) x
  have hfin := levelaf_finite_places D hD
  set S := hfin.toFinset with hS
  have hmem : ∀ v, v ∈ S ↔ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := fun v => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  let w' : intAd F := Formalism.L2.DIV.mkAd
    (fun v => if v ∈ S then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) (fun v => by
      by_cases hv : v ∈ S
      · simp only [hv, if_true]; exact zero_mem _
      · simp only [hv, if_false]
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
        have h1 : 1 ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) :=
          not_lt.1 (fun hlt => hv ((hmem v).2 hlt))
        exact inv_le_one_of_one_le₀ h1)
  have key : algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) D * (w' : Formalism.L2.Herm.Af F) =
      1 - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F) := by
    refine FiniteAdeleRing.ext _ fun v => ?_
    have e1 : (algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) D * (w' : Formalism.L2.Herm.Af F)) v =
        algebraMap (𝓞 F) (v.adicCompletion F) D *
          (if v ∈ S then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) := rfl
    have e2 : ((1 : Formalism.L2.Herm.Af F) - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) v =
        1 - (∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F)) v := rfl
    rw [e1, e2, rll_sum_apply]
    by_cases hv : v ∈ S
    · simp [hv]
    · simp only [hv, if_false, sub_zero]
      exact mul_inv_cancel₀ (levelaf_algebraMap_ne_zero v D hD)
  have hx : x = ∑ v ∈ S, afsplitIE v (prV (E := E) v x) +
      ((1 : E) ⊗ₜ[F] (w' : Formalism.L2.Herm.Af F)) * (levelafC E D * x) := by
    have e3 : ((1 : E) ⊗ₜ[F] (w' : Formalism.L2.Herm.Af F)) * (levelafC E D * x) =
        ((1 : E) ⊗ₜ[F] (1 - ∑ v ∈ S, (afsplitI v 1 : Formalism.L2.Herm.Af F))) * x := by
      rw [← mul_assoc, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (w' : Formalism.L2.Herm.Af F), key]
    rw [e3, TensorProduct.tmul_sub, TensorProduct.tmul_sum, sub_mul, Finset.sum_mul, ← Algebra.TensorProduct.one_def,
      one_mul]
    have e4 : ∀ v ∈ S, afsplitIE v (prV (E := E) v x) = ((1 : E) ⊗ₜ[F] (afsplitI v 1 : Formalism.L2.Herm.Af F)) * x :=
      fun v _ => by rw [afsplit_decomp, rll_eps_eq]
    rw [Finset.sum_congr rfl e4]
    abel
  rw [hx]
  refine add_mem (sum_mem fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ hDx)
  exact (Formalism.L2.DIV.adS F E w').2

end Int

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `afsplit_bc_mem hc.sig 1 v x (levU_le_UAd hc n ST SG H hx)`.
-/
theorem levLoc_le (v : HeightOneSpectrum (𝓞 F)) :
    levLoc hc n ST SG H v ≤ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := by
  rintro _ ⟨x, hx, rfl⟩
  exact afsplit_bc_mem hc.sig 1 v x (levU_le_UAd hc n ST SG H hx)

/- English proof (translation)
Establish `h1 : bc (prV (E` using `E) v) ((x * y⁻¹ : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, mul_inv_cancel]`. Establish `h2` using `Formalism.L2.DIV.reduction_local F E n 1 P v hv _ (x * y⁻¹).2 h1`. Rewrite `h2` using `[redFn, Formalism.L2.DIV.extendOne_of_mem _ (x * y⁻¹).2]`. Establish `h3 : redAt 1 P (x * y⁻¹) = 1` using `h2`.

Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `h3`.
-/
theorem rll_redAt_congr {P : Pl E} {v : HeightOneSpectrum (𝓞 F)} (hv : IsOver v P)
    (x y : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (h : bc (prV (E := E) v) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (prV (E := E) v) y) :
    redAt 1 P x = redAt 1 P y := by
  have h1 : bc (prV (E := E) v) ((x * y⁻¹ : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, mul_inv_cancel]
  have h2 := Formalism.L2.DIV.reduction_local F E n 1 P v hv _ (x * y⁻¹).2 h1
  rw [redFn, Formalism.L2.DIV.extendOne_of_mem _ (x * y⁻¹).2] at h2
  have h3 : redAt 1 P (x * y⁻¹) = 1 := h2
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Use `show redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG H x.2)⟩ = 1`. Establish `hv : IsOver (Formalism.L2.DIV.underPl F w.1) w.1` using `rfl`. Rewrite using `[rll_redAt_congr n hv _ 1 (by rw [h _ ⟨w.1, w.2, hv⟩]; exact (map_one _).symm), map_one]`.
-/
theorem levRed_eq_one (x : levU hc n ST SG H)
    (h : ∀ v ∈ plUnder F SG, bc (prV (E := E) v) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    levRed hc n ST SG H x = 1 := by
  apply Subtype.ext
  funext w
  show redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG H x.2)⟩ = 1
  have hv : IsOver (Formalism.L2.DIV.underPl F w.1) w.1 := rfl
  rw [rll_redAt_congr n hv _ 1 (by rw [h _ ⟨w.1, w.2, hv⟩]; exact (map_one _).symm), map_one]

/- English proof (translation)
Use `show (lam (levRed hc n ST SG H x))⁻¹ = 1`. Rewrite using `[levRed_eq_one hc n ST SG H x h, map_one, inv_one]`.
-/
theorem levTyp_eq_one {M : Type} [CommGroup M] (lam : H →* M) (x : levU hc n ST SG H)
    (h : ∀ v ∈ plUnder F SG, bc (prV (E := E) v) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    levTyp lam x = 1 := by
  show (lam (levRed hc n ST SG H x))⁻¹ = 1
  rw [levRed_eq_one hc n ST SG H x h, map_one, inv_one]

end Loc

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Rewrite using `[St_one, latS_std]`. Conclude with `afsplit_stab_iff _ x`.
-/
theorem rll_mem_St_iff (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E) ∧
        ∀ i j, ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  rw [St_one, latS_std]
  exact afsplit_stab_iff _ x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k.2, hk⟩`. Introduce and unpack `⟨h, hk⟩`. Conclude with `⟨⟨x, h⟩, hk, rfl⟩`.
-/
theorem rll_mem_mirAt {P : Pl E} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ mirAt (F := F) n P ↔ ∃ h : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
      redAt 1 P ⟨x, h⟩ ∈ mirab (kP P) n := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨x, h⟩, hk, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨hx.1.1, hx.1.2, fun P hP => ?_⟩` and prove the remaining obligations. Establish `h1 : x ∈ mirAt (F` using `F) n P := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 P) hP`. Conclude with `((rll_mem_mirAt n).1 h1).2`.

Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => (rll_mem_mirAt n).2 ⟨h2, h3 P hP⟩⟩`.
-/
theorem mem_mirabolicLevel_iff_reduction {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ J0 hc n ST ↔ x ∈ UAd hc n ∧ ∃ h : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
      ∀ P ∈ ST, redAt 1 P ⟨x, h⟩ ∈ mirab (kP P) n := by
  constructor
  · intro hx
    refine ⟨hx.1.1, hx.1.2, fun P hP => ?_⟩
    have h1 : x ∈ mirAt (F := F) n P := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 P) hP
    exact ((rll_mem_mirAt n).1 h1).2
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => (rll_mem_mirAt n).2 ⟨h2, h3 P hP⟩⟩

/- English proof (translation)
Rewrite using `[rll_mem_St_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Use `rll_int_of_loc _ fun v => ?_` and prove the remaining obligations. Take `⟨u, hu, hux⟩` from `h v`.

Establish `e : prV (E` using `E) v ((x : Matrix (Fin n) (Fin n) _) i j) = prV (E := E) v ((u : Matrix (Fin n) (Fin n) _) i j) := congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) hux.symm`. Rewrite using `[e]`. Conclude with `afsplit_prV_int v _ (((rll_mem_St_iff n u).1 hu).1 i j)`. Introduce `i j`. Use `rll_int_of_loc _ fun v => ?_` and prove the remaining obligations.

Take `⟨u, hu, hux⟩` from `h v`. Establish `hux' : bc (prV (E` using `E) v) u⁻¹ = bc (prV (E := E) v) x⁻¹ := by rw [map_inv, map_inv, hux]`. Establish `e : prV (E` using `E) v (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j) = prV (E := E) v (((u⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j) := congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fi …`. Rewrite using `[e]`. Conclude with `afsplit_prV_int v _ (((rll_mem_St_iff n u).1 hu).2 i j)`.
-/
theorem rll_St_of_loc (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
      bc (prV (E := E) v) u = bc (prV (E := E) v) x) :
    x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  rw [rll_mem_St_iff]
  constructor
  · intro i j
    refine rll_int_of_loc _ fun v => ?_
    obtain ⟨u, hu, hux⟩ := h v
    have e : prV (E := E) v ((x : Matrix (Fin n) (Fin n) _) i j) = prV (E := E) v ((u : Matrix (Fin n) (Fin n) _) i j) :=
      congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
        (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) hux.symm
    rw [e]
    exact afsplit_prV_int v _ (((rll_mem_St_iff n u).1 hu).1 i j)
  · intro i j
    refine rll_int_of_loc _ fun v => ?_
    obtain ⟨u, hu, hux⟩ := h v
    have hux' : bc (prV (E := E) v) u⁻¹ = bc (prV (E := E) v) x⁻¹ := by rw [map_inv, map_inv, hux]
    have e : prV (E := E) v (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j) =
        prV (E := E) v (((u⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j) :=
      congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
        (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) hux'.symm
    rw [e]
    exact afsplit_prV_int v _ (((rll_mem_St_iff n u).1 hu).2 i j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨levU_le_UAd hc n ST SG _ hx, fun v => ⟨x, hx, rfl⟩⟩`. Introduce and unpack `⟨hU, hloc⟩`. Establish `hSt : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))`.

Use `rll_St_of_loc n x fun v => ?_` and prove the remaining obligations. Take `⟨u, hu, hux⟩` from `hloc v`. Conclude with `⟨u, congruence_subgroup_le_stabilizer hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG _ hu), hux⟩`. Establish `hJ : x ∈ J0 hc n ST`. Use `(mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨hU, hSt, fun P hP => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, hux⟩` from `hloc (Formalism.L2.DIV.underPl F P)`. Take `⟨_, hS, hm⟩` from `(mem_mirabolicLevel_iff_reduction hc n ST).1 (unipotentLevel_le_mirabolicLevel hc n ST SG _ hu)`. Rewrite using `[rll_redAt_congr n (v := Formalism.L2.DIV.underPl F P) rfl ⟨x, hSt⟩ ⟨u, hS⟩ hux.symm]`. Conclude with `hm P hP`. Use `(mem_levU hc n ST SG _).2 ⟨hJ, fun w _ => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, hux⟩` from `hloc (Formalism.L2.DIV.underPl F w.1)`. Take `⟨hJu, hr⟩` from `(mem_levU hc n ST SG _).1 hu`. Establish `e : redG hc n ST SG ⟨x, hJ⟩ w = redG hc n ST SG ⟨u, hJu⟩ w` using `rll_redAt_congr n (v := Formalism.L2.DIV.underPl F w.1) rfl ⟨x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ⟨u, congruence_subgroup_le_stabilizer hc n ST hJu⟩ hux.symm`. Rewrite using `[e]`. Conclude with `hr w (Set.mem_univ _)`.
-/
theorem levU_eq_prod (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
    (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    x ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw) ↔
      x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) ∧
        ∀ v, bc (prV (E := E) v) x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v := by
  constructor
  · intro hx
    exact ⟨levU_le_UAd hc n ST SG _ hx, fun v => ⟨x, hx, rfl⟩⟩
  · rintro ⟨hU, hloc⟩
    have hSt : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      refine rll_St_of_loc n x fun v => ?_
      obtain ⟨u, hu, hux⟩ := hloc v
      exact ⟨u, congruence_subgroup_le_stabilizer hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG _ hu), hux⟩
    have hJ : x ∈ J0 hc n ST := by
      refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨hU, hSt, fun P hP => ?_⟩
      obtain ⟨u, hu, hux⟩ := hloc (Formalism.L2.DIV.underPl F P)
      obtain ⟨_, hS, hm⟩ := (mem_mirabolicLevel_iff_reduction hc n ST).1 (unipotentLevel_le_mirabolicLevel hc n ST SG _ hu)
      rw [rll_redAt_congr n (v := Formalism.L2.DIV.underPl F P) rfl ⟨x, hSt⟩ ⟨u, hS⟩ hux.symm]
      exact hm P hP
    refine (mem_levU hc n ST SG _).2 ⟨hJ, fun w _ => ?_⟩
    obtain ⟨u, hu, hux⟩ := hloc (Formalism.L2.DIV.underPl F w.1)
    obtain ⟨hJu, hr⟩ := (mem_levU hc n ST SG _).1 hu
    have e : redG hc n ST SG ⟨x, hJ⟩ w = redG hc n ST SG ⟨u, hJu⟩ w :=
      rll_redAt_congr n (v := Formalism.L2.DIV.underPl F w.1) rfl ⟨x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ⟨u, congruence_subgroup_le_stabilizer hc n ST hJu⟩ hux.symm
    rw [e]
    exact hr w (Set.mem_univ _)

end Prod

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (n : ℕ) [NeZero n] (ST : Finset (Pl E))

/- English proof (translation)
Unfold `baseLb`. Rewrite using `[(Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).mem_L]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hN, hf⟩`. Establish `hN' : x ∈ stdLat E n` using `hN`.

Use `choose r hr using (mem_stdLat x).1 hN'`. Use `⟨r, hr, fun P hP => ?_⟩` and prove the remaining obligations. Establish `h` using `hf ⟨P, hP⟩`. Establish `e : (Deco.base E n ST (∅ : Finset (Pl E))).f ⟨P, hP⟩ x = redP P (x (lastIdx n))` using `if_pos (le_locP _ _ hN')`. Rewrite `h` using `[e, ← hr, reduction_coe]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h`. Introduce and unpack `⟨r, hr, hP⟩`. Establish `hN : x ∈ stdLat E n` using `(mem_stdLat x).2 fun i => ⟨r i, hr i⟩`. Use `⟨hN, fun P => ?_⟩` and prove the remaining obligations. Establish `e : (Deco.base E n ST (∅ : Finset (Pl E))).f P x = redP P.1 (x (lastIdx n))` using `if_pos (le_locP _ _ hN)`.

Rewrite using `[e, ← hr, reduction_coe]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hP P.1 P.2)`.
-/
theorem rll_mem_baseLb (x : Fin n → E) :
    x ∈ baseLb E n ST ↔ ∃ r : Fin n → 𝓞 E, (∀ i, algebraMap (𝓞 E) E (r i) = x i) ∧
      ∀ P ∈ ST, r (lastIdx n) ∈ P.asIdeal := by
  unfold baseLb
  rw [(Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).mem_L]
  constructor
  · rintro ⟨hN, hf⟩
    have hN' : x ∈ stdLat E n := hN
    choose r hr using (mem_stdLat x).1 hN'
    refine ⟨r, hr, fun P hP => ?_⟩
    have h := hf ⟨P, hP⟩
    have e : (Deco.base E n ST (∅ : Finset (Pl E))).f ⟨P, hP⟩ x = redP P (x (lastIdx n)) :=
      if_pos (le_locP _ _ hN')
    rw [e, ← hr, reduction_coe] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rintro ⟨r, hr, hP⟩
    have hN : x ∈ stdLat E n := (mem_stdLat x).2 fun i => ⟨r i, hr i⟩
    refine ⟨hN, fun P => ?_⟩
    have e : (Deco.base E n ST (∅ : Finset (Pl E))).f P x = redP P.1 (x (lastIdx n)) :=
      if_pos (le_locP _ _ hN)
    rw [e, ← hr, reduction_coe]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hP P.1 P.2)

/- English proof (translation)
Introduce `h`. Establish `h1 : (∏ P ∈ ST, P.asIdeal) ≤ ⊥` using `h ▸ Ideal.prod_le_inf`. Establish `h2 : (∏ P ∈ ST, P.asIdeal) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun P _ => P.ne_bot`. Conclude with `h2 (le_bot_iff.1 h1)`.
-/
theorem rll_inf_ne_bot : (ST.inf fun P : Pl E => P.asIdeal) ≠ ⊥ := by
  intro h
  have h1 : (∏ P ∈ ST, P.asIdeal) ≤ ⊥ := h ▸ Ideal.prod_le_inf
  have h2 : (∏ P ∈ ST, P.asIdeal) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ => P.ne_bot
  exact h2 (le_bot_iff.1 h1)

/- English proof (translation)
Take `⟨q, hq⟩` from `Formalism.L2.DIV.cmpS_surj (F := F) _ (rll_inf_ne_bot ST) (Ideal.Quotient.mk _ t)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (ST.inf fun P : Pl E => P.asIdeal)) (Formalism.L2.DIV.oToS F E a) = Ideal.Quotient.mk _ t` using `hq`. Establish `hd` using `Ideal.Quotient.eq.1 hq'`. Establish `ha : a ∈ ST.inf fun P : Pl E => P.asIdeal`.

Rewrite using `[Submodule.mem_finsetInf]`. Introduce `P hP`. Establish `h1 : Formalism.L2.DIV.oToS F E a - t ∈ Formalism.L2.DIV.idS F P.asIdeal` using `Ideal.map_mono (Finset.inf_le hP) hd`. Establish `h2` using `(Formalism.L2.DIV.resS_eq_zero_iff P _).2 h1`. Rewrite `h2` using `[map_sub, h P hP, sub_zero, Formalism.L2.DIV.resS_oToS]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2`. Establish `: t = Formalism.L2.DIV.oToS F E a - (Formalism.L2.DIV.oToS F E a - t)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ha) hd`.
-/
theorem rll_mem_idS_inf (t : Formalism.L2.Herm.intAf F E) (h : ∀ P ∈ ST, resS F P t = 0) :
    t ∈ Formalism.L2.DIV.idS F (ST.inf fun P : Pl E => P.asIdeal) := by
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) _ (rll_inf_ne_bot ST) (Ideal.Quotient.mk _ t)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (ST.inf fun P : Pl E => P.asIdeal)) (Formalism.L2.DIV.oToS F E a) =
      Ideal.Quotient.mk _ t := hq
  have hd := Ideal.Quotient.eq.1 hq'
  have ha : a ∈ ST.inf fun P : Pl E => P.asIdeal := by
    rw [Submodule.mem_finsetInf]
    intro P hP
    have h1 : Formalism.L2.DIV.oToS F E a - t ∈ Formalism.L2.DIV.idS F P.asIdeal :=
      Ideal.map_mono (Finset.inf_le hP) hd
    have h2 := (Formalism.L2.DIV.resS_eq_zero_iff P _).2 h1
    rw [map_sub, h P hP, sub_zero, Formalism.L2.DIV.resS_oToS] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  have : t = Formalism.L2.DIV.oToS F E a - (Formalism.L2.DIV.oToS F E a - t) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ha) hd

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨l, hl, rfl⟩`.
-/
theorem rll_gen_mem {L : Submodule (𝓞 E) (Fin n → E)} {l : Fin n → E} (hl : l ∈ L) :
    (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) L :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem rll_single_incl (i : Fin n) (e : E) :
    (fun j => inclE (F := F) (Formalism.L2.Herm.Af F) ((Pi.single i e : Fin n → E) j)) =
      Pi.single i (inclE (F := F) (Formalism.L2.Herm.Af F) e) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Unfold `Formalism.L2.Herm.hatL latS at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨l, hl, rfl⟩` from `hz`. Take `⟨r, hr, hP⟩` from `(rll_mem_baseLb n ST l).1 hl`. Use `⟨fun i => Formalism.L2.DIV.oToS F E (r i), fun i => ?_, fun P hPS => ?_⟩` and prove the remaining obligations. Use `show _ = inclE (F := F) (Formalism.L2.Herm.Af F) (l i)`. Rewrite using `[← hr i]`.

Both sides reduce to the same expression. Rewrite using `[Formalism.L2.DIV.resS_oToS]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hP P hPS)`. Consider the case `zero => exact ⟨0, fun i => rfl, fun P _ => map_zero _⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨y, hy, hyP⟩` from `ha`. Take `⟨y', hy', hyP'⟩` from `hb`. Use `⟨y + y', fun i => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, Pi.add_apply, ← hy, ← hy']`. Both sides reduce to the same expression.

Rewrite using `[Pi.add_apply, map_add, hyP P hP, hyP' P hP, add_zero]`. Consider the case `smul s a _ ha`. Take `⟨y, hy, hyP⟩` from `ha`. Use `⟨fun i => s * y i, fun i => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, ← hy]`.

Both sides reduce to the same expression. Rewrite using `[map_mul, hyP P hP, mul_zero]`. Introduce and unpack `⟨y, hy, hyP⟩`. Establish `hz : z = ∑ i, (Pi.single i (z i) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)` using `(Finset.univ_sum_single z).symm`. Rewrite using `[hz]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = lastIdx n`. Substitute `hi` using the available equality. Establish `ht` using `rll_mem_idS_inf ST _ hyP`. Rewrite using `[← hy]`.

Generalize the expression as in `y (lastIdx n) = t at ht`. Unfold `Formalism.L2.DIV.idS Ideal.map at ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨a, ha, rfl⟩` from `ht`.

Establish `hl : (Pi.single (lastIdx n) (algebraMap (𝓞 E) E a) : Fin n → E) ∈ baseLb E n ST`. Use `(rll_mem_baseLb n ST _).2 ⟨Pi.single (lastIdx n) a, fun i => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = lastIdx n`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Rewrite using `[Pi.single_eq_same]`. Conclude with `(Submodule.mem_finsetInf.1 ha) P hP`. Use `rll_gen_mem (F := F) n hl` as an intermediate fact. Rewrite `this` using `[rll_single_incl]`.

Conclude with `this`. Consider the case `zero`. Rewrite using `[ZeroMemClass.coe_zero, Pi.single_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`.

Rewrite using `[AddMemClass.coe_add, Pi.single_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul s a _ ha`. Establish `e : (Pi.single (lastIdx n) (((s • a : Formalism.L2.Herm.intAf F E)) : E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) = s • Pi.single (lastIdx n) (a : E ⊗[F] Formalism.L2.Herm.Af F)`. Rewrite using `[← Pi.single_smul]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ ha`. Establish `hl : (Pi.single i (1 : E) : Fin n → E) ∈ baseLb E n ST`. Use `(rll_mem_baseLb n ST _).2 ⟨Pi.single i 1, fun j => ?_, fun P _ => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hi)]`.

Conclude with `zero_mem _`. Establish `h1` using `rll_gen_mem (F := F) n hl`. Rewrite `h1` using `[rll_single_incl, map_one]`. Establish `e : (Pi.single i (z i) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) = y i • (Pi.single i (1 : E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)`. Rewrite using `[← Pi.single_smul, ← hy]`.

Use `congr 1`. Use `show _ = (y i : E ⊗[F] Formalism.L2.Herm.Af F) * 1`. Rewrite using `[mul_one]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem rll_mem_hat_base (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (baseLb E n ST) ↔ ∃ y : Fin n → Formalism.L2.Herm.intAf F E,
      (∀ i, (y i : E ⊗[F] Formalism.L2.Herm.Af F) = z i) ∧ ∀ P ∈ ST, resS F P (y (lastIdx n)) = 0 := by
  constructor
  · intro hz
    unfold Formalism.L2.Herm.hatL latS at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      obtain ⟨r, hr, hP⟩ := (rll_mem_baseLb n ST l).1 hl
      refine ⟨fun i => Formalism.L2.DIV.oToS F E (r i), fun i => ?_, fun P hPS => ?_⟩
      · show _ = inclE (F := F) (Formalism.L2.Herm.Af F) (l i)
        rw [← hr i]; rfl
      · rw [Formalism.L2.DIV.resS_oToS]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hP P hPS)
    | zero => exact ⟨0, fun i => rfl, fun P _ => map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, hyP⟩ := ha
      obtain ⟨y', hy', hyP'⟩ := hb
      refine ⟨y + y', fun i => ?_, fun P hP => ?_⟩
      · rw [Pi.add_apply, Pi.add_apply, ← hy, ← hy']; rfl
      · rw [Pi.add_apply, map_add, hyP P hP, hyP' P hP, add_zero]
    | smul s a _ ha =>
      obtain ⟨y, hy, hyP⟩ := ha
      refine ⟨fun i => s * y i, fun i => ?_, fun P hP => ?_⟩
      · rw [Pi.smul_apply, ← hy]; rfl
      · rw [map_mul, hyP P hP, mul_zero]
  · rintro ⟨y, hy, hyP⟩
    have hz : z = ∑ i, (Pi.single i (z i) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := (Finset.univ_sum_single z).symm
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i = lastIdx n
    · subst hi
      have ht := rll_mem_idS_inf ST _ hyP
      rw [← hy]
      generalize y (lastIdx n) = t at ht
      unfold Formalism.L2.DIV.idS Ideal.map at ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨a, ha, rfl⟩ := ht
        have hl : (Pi.single (lastIdx n) (algebraMap (𝓞 E) E a) : Fin n → E) ∈ baseLb E n ST := by
          refine (rll_mem_baseLb n ST _).2 ⟨Pi.single (lastIdx n) a, fun i => ?_, fun P hP => ?_⟩
          · by_cases h : i = lastIdx n
            · subst h; simp
            · simp [h]
          · rw [Pi.single_eq_same]; exact (Submodule.mem_finsetInf.1 ha) P hP
        have := rll_gen_mem (F := F) n hl
        rw [rll_single_incl] at this
        exact this
      | zero =>
        rw [ZeroMemClass.coe_zero, Pi.single_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        rw [AddMemClass.coe_add, Pi.single_add]; exact Submodule.add_mem _ ha hb
      | smul s a _ ha =>
        have e : (Pi.single (lastIdx n) (((s • a : Formalism.L2.Herm.intAf F E)) : E ⊗[F] Formalism.L2.Herm.Af F) :
            Fin n → E ⊗[F] Formalism.L2.Herm.Af F) = s • Pi.single (lastIdx n) (a : E ⊗[F] Formalism.L2.Herm.Af F) := by
          rw [← Pi.single_smul]; rfl
        rw [e]; exact Submodule.smul_mem _ _ ha
    · have hl : (Pi.single i (1 : E) : Fin n → E) ∈ baseLb E n ST := by
        refine (rll_mem_baseLb n ST _).2 ⟨Pi.single i 1, fun j => ?_, fun P _ => ?_⟩
        · by_cases h : j = i
          · subst h; simp
          · simp [h]
        · rw [Pi.single_eq_of_ne (Ne.symm hi)]; exact zero_mem _
      have h1 := rll_gen_mem (F := F) n hl
      rw [rll_single_incl, map_one] at h1
      have e : (Pi.single i (z i) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) =
          y i • (Pi.single i (1 : E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        rw [← Pi.single_smul, ← hy]
        congr 1
        show _ = (y i : E ⊗[F] Formalism.L2.Herm.Af F) * 1
        rw [mul_one]
      rw [e]; exact Submodule.smul_mem _ _ h1

end Hat

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
Introduce `x`. Use `⟨h1 x, fun hx => ?_⟩` and prove the remaining obligations. Use `h2 _ hx` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem rll_stab_of_maps {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {m : Type} [Fintype m] [DecidableEq m]
    (Λ : Submodule R (m → A)) (g : GL m A) (h1 : ∀ x ∈ Λ, (g : Matrix m m A) *ᵥ x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ((g⁻¹ : GL m A) : Matrix m m A) *ᵥ x ∈ Λ) : g ∈ stabGL Λ := by
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

/- English proof (translation)
Take `⟨_, hS, hm⟩` from `(mem_mirabolicLevel_iff_reduction hc n ST).1 hk`. Take `⟨y, hy, hr⟩` from `St_one_int hS`. Take `⟨u, hu, huP⟩` from `(rll_mem_hat_base n ST z).1 hz`. Use `(rll_mem_hat_base n ST _).2 ⟨fun i => ∑ j, y i j * u j, fun i => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_int_apply hy]`.

Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hu j]`. Both sides reduce to the same expression. Rewrite using `[map_sum, Finset.sum_eq_single (lastIdx n)]`.

Rewrite using `[map_mul, huP P hP, mul_zero]`. Introduce `j _ hj`. Rewrite using `[map_mul, ← hr P, hm P hP j, if_neg hj, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mirabolicLevel_maps_baseLattice {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ J0 hc n ST)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (baseLb E n ST)) :
    (k : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) (baseLb E n ST) := by
  obtain ⟨_, hS, hm⟩ := (mem_mirabolicLevel_iff_reduction hc n ST).1 hk
  obtain ⟨y, hy, hr⟩ := St_one_int hS
  obtain ⟨u, hu, huP⟩ := (rll_mem_hat_base n ST z).1 hz
  refine (rll_mem_hat_base n ST _).2 ⟨fun i => ∑ j, y i j * u j, fun i => ?_, fun P hP => ?_⟩
  · rw [mulVec_int_apply hy]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hu j]; rfl
  · rw [map_sum, Finset.sum_eq_single (lastIdx n)]
    · rw [map_mul, huP P hP, mul_zero]
    · intro j _ hj
      rw [map_mul, ← hr P, hm P hP j, if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `k hk` and use `rll_stab_of_maps _ k (mirabolicLevel_maps_baseLattice hc n ST hk) (mirabolicLevel_maps_baseLattice hc n ST (Subgroup.inv_mem _ hk))`.
-/
theorem mirabolicLevel_le_stabilizer_base : J0 hc n ST ≤ stabGL (Formalism.L2.Herm.hatL (F := F) (baseLb E n ST)) := fun k hk =>
  rll_stab_of_maps _ k (mirabolicLevel_maps_baseLattice hc n ST hk) (mirabolicLevel_maps_baseLattice hc n ST (Subgroup.inv_mem _ hk))

/- English proof (translation)
Introduce `g hg`. Use `⟨levLoc_le hc n ST SG H v hg, ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `hg`. Conclude with `Formalism.L2.DIV.lc_stab_loc v _ x (mirabolicLevel_le_stabilizer_base hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG H hx))`.
-/
theorem levLoc_le_levelVL (v : HeightOneSpectrum (𝓞 F)) :
    levLoc hc n ST SG H v ≤ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := by
  intro g hg
  refine ⟨levLoc_le hc n ST SG H v hg, ?_⟩
  obtain ⟨x, hx, rfl⟩ := hg
  exact Formalism.L2.DIV.lc_stab_loc v _ x (mirabolicLevel_le_stabilizer_base hc n ST (unipotentLevel_le_mirabolicLevel hc n ST SG H hx))

end Stab

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
Rewrite using `[stdLat_eq_ug]`. Conclude with `easyc_latS_std (F := F) (n := Fin n) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring`.
-/
theorem rll_locL_std (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.L2.Herm.locL v (stdLat E n) =
      Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] v.adicCompletion F) (Formalism.BasicNotions.intV E v) := by
  rw [stdLat_eq_ug]
  exact easyc_latS_std (F := F) (n := Fin n) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring

def rll_put (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := afsplitU v g 1

/- English proof (translation)
The claim follows from `afsplit_right1 v g 1`.
-/
theorem rll_put_self (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) v) (rll_put n v g) = g := afsplit_right1 v g 1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[afsplit_coe_bc_prV, rll_put, afsplitU_coe, afsplitC_prV_ne v w h, Units.val_one, Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem rll_put_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) w) (rll_put n v g) = 1 := by
  apply Units.ext
  rw [afsplit_coe_bc_prV, rll_put, afsplitU_coe, afsplitC_prV_ne v w h, Units.val_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `afsplitU_mem v hc.sig 1 g 1 hg (one_mem _)`.
-/
theorem rll_put_mem_UAd (v : HeightOneSpectrum (𝓞 F)) {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hg : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) : rll_put n v g ∈ UAd hc n :=
  afsplitU_mem v hc.sig 1 g 1 hg (one_mem _)

/- English proof (translation)
Rewrite `hg` using `[rll_locL_std]`. Take `⟨h1, h2⟩` from `(afsplit_stab_iff _ g).1 hg`. Rewrite using `[rll_mem_St_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `i j`.

Rewrite using `[rll_put, afsplitU_coe]`. Conclude with `afsplitC_int v _ _ h1 (fun i j => by rw [Units.val_one]; exact afsplit_one_mem _ i j) i j`. Introduce `i j`. Rewrite using `[rll_put, afsplitU_inv_coe]`. Conclude with `afsplitC_int v _ _ h2 (fun i j => by rw [inv_one, Units.val_one]; exact afsplit_one_mem _ i j) i j`.
-/
theorem rll_put_mem_St (v : HeightOneSpectrum (𝓞 F)) {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hg : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) :
    rll_put n v g ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  rw [rll_locL_std] at hg
  obtain ⟨h1, h2⟩ := (afsplit_stab_iff _ g).1 hg
  rw [rll_mem_St_iff]
  constructor
  · intro i j
    rw [rll_put, afsplitU_coe]
    exact afsplitC_int v _ _ h1 (fun i j => by rw [Units.val_one]; exact afsplit_one_mem _ i j) i j
  · intro i j
    rw [rll_put, afsplitU_inv_coe]
    exact afsplitC_int v _ _ h2 (fun i j => by rw [inv_one, Units.val_one]; exact afsplit_one_mem _ i j) i j

/- English proof (translation)
Establish `hne : Formalism.L2.DIV.underPl F P ≠ v`. Introduce and unpack `rfl`. Conclude with `hP rfl`. Rewrite using `[rll_redAt_congr n (v := Formalism.L2.DIV.underPl F P) rfl _ 1 (by rw [rll_put_ne n v _ hne g]; exact (map_one _).symm), map_one]`.
-/
theorem rll_put_red (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hS : rll_put n v g ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (P : Pl E) (hP : ¬ IsOver v P) :
    redAt 1 P ⟨rll_put n v g, hS⟩ = 1 := by
  have hne : Formalism.L2.DIV.underPl F P ≠ v := by
    rintro rfl; exact hP rfl
  rw [rll_redAt_congr n (v := Formalism.L2.DIV.underPl F P) rfl _ 1
    (by rw [rll_put_ne n v _ hne g]; exact (map_one _).symm), map_one]

/- English proof (translation)
Proceed by induction on `ST using Finset.induction_on with`. Consider the case `empty => exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun P hP => absurd hP (Finset.notMem_empty P)⟩`. Consider the case `insert Q S _ ih`. Take `⟨d, hd, hdS⟩` from `ih (fun ⟨P, hP, hv⟩ => hT ⟨P, Finset.mem_insert_of_mem hP, hv⟩)`. Establish `hne : Formalism.L2.DIV.underPl F Q ≠ v`.

Introduce and unpack `rfl`. Conclude with `hT ⟨Q, Finset.mem_insert_self _ _, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hsv⟩ : ∃ s ∈ (Formalism.L2.DIV.underPl F Q).asIdeal, s ∉ v.asIdeal := by`. Assume the negation of the conclusion as `Hc`. Use `push Not at Hc`.

Conclude with `hne (HeightOneSpectrum.ext ((Formalism.L2.DIV.underPl F Q).isMaximal.eq_of_le v.isPrime.ne_top Hc))`. Use `⟨s * d, fun h => (v.isPrime.mem_or_mem h).elim hsv hd, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Break down `Finset.mem_insert.1 hP with rfl | hP` into its components or cases. Conclude with `Ideal.mul_mem_right _ _ hs`.

Conclude with `Ideal.mul_mem_left _ _ (hdS P hP)`.
-/
theorem rll_exists_d (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) :
    ∃ d : 𝓞 F, d ∉ v.asIdeal ∧ ∀ P ∈ ST, algebraMap (𝓞 F) (𝓞 E) d ∈ P.asIdeal := by
  classical
  induction ST using Finset.induction_on with
  | empty => exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun P hP => absurd hP (Finset.notMem_empty P)⟩
  | insert Q S _ ih =>
    obtain ⟨d, hd, hdS⟩ := ih (fun ⟨P, hP, hv⟩ => hT ⟨P, Finset.mem_insert_of_mem hP, hv⟩)
    have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
      rintro rfl; exact hT ⟨Q, Finset.mem_insert_self _ _, rfl⟩
    obtain ⟨s, hs, hsv⟩ : ∃ s ∈ (Formalism.L2.DIV.underPl F Q).asIdeal, s ∉ v.asIdeal := by
      by_contra Hc
      push Not at Hc
      exact hne (HeightOneSpectrum.ext ((Formalism.L2.DIV.underPl F Q).isMaximal.eq_of_le v.isPrime.ne_top Hc))
    refine ⟨s * d, fun h => (v.isPrime.mem_or_mem h).elim hsv hd, fun P hP => ?_⟩
    rw [map_mul]
    rcases Finset.mem_insert.1 hP with rfl | hP
    · exact Ideal.mul_mem_right _ _ hs
    · exact Ideal.mul_mem_left _ _ (hdS P hP)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem rll_latS_mono (v : HeightOneSpectrum (𝓞 F)) {L L' : Submodule (𝓞 E) (Fin n → E)} (h : L ≤ L') :
    Formalism.L2.Herm.locL v L ≤ Formalism.L2.Herm.locL v L' :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Unfold `Formalism.L2.Herm.locL latS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Set `c : Formalism.BasicNotions.intV E v` to `⟨(1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.L2.DIV.fr_inv_int v d hd⟩, rfl⟩)⟩`. Establish `hne : algebraMap (𝓞 F) (v.adicCompletion F) d ≠ 0` using `levelaf_algebraMap_ne_zero v d (fun h0 => hd (h0 ▸ zero_mem _))`.

Establish `e : (fun i => inclE (F` using `F) (v.adicCompletion F) (l i)) = c • (fun i => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) d • l) i)) := by`. Use function extensionality and compare the values at `i`. Use `show (l i) ⊗ₜ[F] (1 : v.adicCompletion F) = ((1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹) * (((algebraMap (𝓞 F) (𝓞 E) d • l) i) ⊗ₜ[F] 1)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Establish `e1 : (algebraMap (𝓞 F) (𝓞 E) d • l) i = (algebraMap (𝓞 F) F d) • l i`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]`. Use `congr 1`. Rewrite using `[e1, TensorProduct.smul_tmul, Algebra.smul_def]`. Establish `e2 : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) = algebraMap (𝓞 F) (v.adicCompletion F) d` using `(IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) d).symm`. Rewrite using `[e2, mul_inv_cancel₀ hne]`.

Rewrite using `[SetLike.mem_coe]`. Use `show (fun i => inclE (F := F) (v.adicCompletion F) (l i)) ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h l hl, rfl⟩)`.
-/
theorem rll_locL_le_of_smul (v : HeightOneSpectrum (𝓞 F)) {L L' : Submodule (𝓞 E) (Fin n → E)} {d : 𝓞 F}
    (hd : d ∉ v.asIdeal) (h : ∀ l ∈ L', algebraMap (𝓞 F) (𝓞 E) d • l ∈ L) :
    Formalism.L2.Herm.locL v L' ≤ Formalism.L2.Herm.locL v L := by
  unfold Formalism.L2.Herm.locL latS
  rw [Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  let c : Formalism.BasicNotions.intV E v := ⟨(1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹,
    Subring.subset_closure (Or.inr ⟨⟨_, Formalism.L2.DIV.fr_inv_int v d hd⟩, rfl⟩)⟩
  have hne : algebraMap (𝓞 F) (v.adicCompletion F) d ≠ 0 :=
    levelaf_algebraMap_ne_zero v d (fun h0 => hd (h0 ▸ zero_mem _))
  have e : (fun i => inclE (F := F) (v.adicCompletion F) (l i)) =
      c • (fun i => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) d • l) i)) := by
    funext i
    show (l i) ⊗ₜ[F] (1 : v.adicCompletion F) =
      ((1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹) * (((algebraMap (𝓞 F) (𝓞 E) d • l) i) ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have e1 : (algebraMap (𝓞 F) (𝓞 E) d • l) i = (algebraMap (𝓞 F) F d) • l i := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
      congr 1
    rw [e1, TensorProduct.smul_tmul, Algebra.smul_def]
    have e2 : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) = algebraMap (𝓞 F) (v.adicCompletion F) d :=
      (IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) d).symm
    rw [e2, mul_inv_cancel₀ hne]
  rw [SetLike.mem_coe]
  show (fun i => inclE (F := F) (v.adicCompletion F) (l i)) ∈ _
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h l hl, rfl⟩)

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨r, hr, _⟩ := (rll_mem_baseLb n ST x).1 hx exact (mem_stdLat x).2 fun i => ⟨r i, hr i⟩`.
-/
theorem rll_baseLb_le : baseLb E n ST ≤ stdLat E n := fun x hx => by
  obtain ⟨r, hr, _⟩ := (rll_mem_baseLb n ST x).1 hx
  exact (mem_stdLat x).2 fun i => ⟨r i, hr i⟩

/- English proof (translation)
Use `le_antisymm (rll_latS_mono n v (rll_baseLb_le n ST)) ?_` and prove the remaining obligations. Take `⟨d, hd, hdS⟩` from `rll_exists_d ST v hT`. Use `rll_locL_le_of_smul n v hd fun l hl => ?_` and prove the remaining obligations. Use `choose r hr using (mem_stdLat l).1 hl`. Use `(rll_mem_baseLb n ST _).2 ⟨fun i => algebraMap (𝓞 F) (𝓞 E) d * r i, fun i => ?_, fun P hP => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul, hr]`. Conclude with `Ideal.mul_mem_right _ _ (hdS P hP)`.
-/
theorem rll_locL_base (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) :
    Formalism.L2.Herm.locL v (baseLb E n ST) = Formalism.L2.Herm.locL v (stdLat E n) := by
  refine le_antisymm (rll_latS_mono n v (rll_baseLb_le n ST)) ?_
  obtain ⟨d, hd, hdS⟩ := rll_exists_d ST v hT
  refine rll_locL_le_of_smul n v hd fun l hl => ?_
  choose r hr using (mem_stdLat l).1 hl
  refine (rll_mem_baseLb n ST _).2 ⟨fun i => algebraMap (𝓞 F) (𝓞 E) d * r i, fun i => ?_, fun P hP => ?_⟩
  · rw [Pi.smul_apply, Algebra.smul_def, map_mul, hr]
  · exact Ideal.mul_mem_right _ _ (hdS P hP)

/- English proof (translation)
Use `le_antisymm (levLoc_le_levelVL hc n ST SG H v) fun g hg => ?_` and prove the remaining obligations. Establish `hgU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)` using `hg.1`. Establish `hgS : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))`. Rewrite using `[← rll_locL_base n ST v hT]`. Conclude with `hg.2`.

Establish `hS` using `rll_put_mem_St n v hgS`. Establish `hJ : rll_put n v g ∈ J0 hc n ST`. Use `(mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hgU, hS, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[rll_put_red n v g hS P (fun h => hT ⟨P, hP, h⟩)]`. Conclude with `Subgroup.one_mem _`.

Use `⟨rll_put n v g, (mem_levU hc n ST SG H).2 ⟨hJ, ?_⟩, rll_put_self n v g⟩` and prove the remaining obligations. Establish `: redG hc n ST SG ⟨rll_put n v g, hJ⟩ = 1`. Use function extensionality and compare the values at `w`. Conclude with `rll_put_red n v g (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 (fun h => hG ⟨w.1, w.2, h⟩)`. Rewrite using `[this]`.

Conclude with `Subgroup.one_mem _`.
-/
theorem levLoc_eq_levelVL (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (hG : v ∉ plUnder F SG) :
    levLoc hc n ST SG H v = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := by
  refine le_antisymm (levLoc_le_levelVL hc n ST SG H v) fun g hg => ?_
  have hgU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hg.1
  have hgS : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hg.2
  have hS := rll_put_mem_St n v hgS
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hgU, hS, fun P hP => ?_⟩
    rw [rll_put_red n v g hS P (fun h => hT ⟨P, hP, h⟩)]
    exact Subgroup.one_mem _
  refine ⟨rll_put n v g, (mem_levU hc n ST SG H).2 ⟨hJ, ?_⟩, rll_put_self n v g⟩
  have : redG hc n ST SG ⟨rll_put n v g, hJ⟩ = 1 := by
    funext w
    exact rll_put_red n v g (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 (fun h => hG ⟨w.1, w.2, h⟩)
  rw [this]; exact Subgroup.one_mem _

end Put

end Formalism.L2.Col
