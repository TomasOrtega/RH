import Formalism.LocalToGlobal.Columns.TiedGlLoc
import Formalism.LocalToGlobal.Columns.LevGCount

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

/- English proof (translation)
Take `⟨y, hy, hr⟩` from `St_one_int hk`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, hr w i j, gloE_resS, gloRho_apply]`. Establish `e : ((bc (gloPhi v spl) (bc (prV (E` using `E) v) k) : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = gloPhi v spl (prV (E := E) v (y i j : E ⊗[F] Formalism.L2.Herm.Af F)) := by`. Rewrite using `[← hy i j]`.

Both sides reduce to the same expression. Unfold `redM`. Establish `hm : ((bc (gloPhi v spl) (bc (prV (E` using `E) v) k) : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by`. Rewrite using `[e]`. Conclude with `gloPhi_int v spl halg _ (afsplit_prV_int v _ (y i j).2)`.

Rewrite using `[dif_pos hm]`. Use `congr 1`. Conclude with `Subtype.ext e.symm`.
-/
theorem gco_red_map {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w ⟨k, hk⟩ : GL (Fin n) (kP w)) : Matrix (Fin n) (Fin n) (kP w)).map
        (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  obtain ⟨y, hy, hr⟩ := St_one_int hk
  ext i j
  rw [Matrix.map_apply, hr w i j, gloE_resS, gloRho_apply]
  have e : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = gloPhi v spl (prV (E := E) v (y i j : E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← hy i j]; rfl
  unfold redM
  have hm : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [e]; exact gloPhi_int v spl halg _ (afsplit_prV_int v _ (y i j).2)
  rw [dif_pos hm]
  congr 1
  exact Subtype.ext e.symm

variable (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Take `⟨hJ, hred⟩` from `(mem_levU hc n ST SG _).1 hk`. Conclude with `⟨_, hred w (Set.mem_univ w), gco_red_map n v spl halg w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)⟩`. Introduce and unpack `⟨M, hM, hMx⟩`.

Establish `hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)` using `hx.1`. Establish `hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))`. Rewrite using `[← rll_locL_base n ST v hT]`. Conclude with `hx.2`. Establish `hS` using `rll_put_mem_St n v hxS`.

Establish `hJ : rll_put n v x ∈ J0 hc n ST`. Use `(mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]`. Conclude with `Subgroup.one_mem _`. Use `⟨rll_put n v x, (mem_levU hc n ST SG _).2 ⟨hJ, ?_⟩, rll_put_self n v x⟩` and prove the remaining obligations.

Introduce `w' _`. Use `show redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ∈ Hw w'`. Distinguish the cases in `hw' : IsOver v w'.1`. Take `rfl` from `huniq w' hw'`. Establish `h1` using `gco_red_map n v spl halg w'.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)`.

Rewrite `h1` using `[rll_put_self, ← hMx]`. Establish `h2 : redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ = M`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `congrFun (congrFun h1 i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply, Matrix.map_apply]`. Conclude with `(gloE v spl halg w'.1 hw).injective this`. Rewrite using `[h2]`. Conclude with `hM`. Rewrite using `[rll_put_red n v x _ w'.1 hw']`.

Conclude with `Subgroup.one_mem _`.
-/
theorem gco_mem_levLoc (w : SG) (hw : ∀ a ∈ w.1.asIdeal, gloRho v spl halg (oToS F E a) = 0) (hov : IsOver v w.1)
    (huniq : ∀ w' : SG, IsOver v w'.1 → w' = w) (hT : v ∉ plUnder F ST)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v ↔
      ∃ M ∈ Hw w, (M : Matrix (Fin n) (Fin n) (kP w.1)).map (gloE v spl halg w.1 hw) =
        redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hJ, hred⟩ := (mem_levU hc n ST SG _).1 hk
    exact ⟨_, hred w (Set.mem_univ w), gco_red_map n v spl halg w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)⟩
  · rintro ⟨M, hM, hMx⟩
    have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    have hS := rll_put_mem_St n v hxS
    have hJ : rll_put n v x ∈ J0 hc n ST := by
      refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
      rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
      exact Subgroup.one_mem _
    refine ⟨rll_put n v x, (mem_levU hc n ST SG _).2 ⟨hJ, ?_⟩, rll_put_self n v x⟩
    intro w' _
    show redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ∈ Hw w'
    by_cases hw' : IsOver v w'.1
    · obtain rfl := huniq w' hw'
      have h1 := gco_red_map n v spl halg w'.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
      rw [rll_put_self, ← hMx] at h1
      have h2 : redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ = M := by
        apply Units.ext
        ext i j
        have := congrFun (congrFun h1 i) j
        rw [Matrix.map_apply, Matrix.map_apply] at this
        exact (gloE v spl halg w'.1 hw).injective this
      rw [h2]; exact hM
    · rw [rll_put_red n v x _ w'.1 hw']
      exact Subgroup.one_mem _

include halg in

/- English proof (translation)
Establish `hL : latS (F` using `F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) = Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] v.adicCompletion F) (Formalism.BasicNotions.intV E v) := (rll_locL_base n ST v hT).trans (rll_locL_std n v)`. Rewrite using `[hL, inv_one, Units.val_one, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩ b`. Rewrite using `[← hyx b]`.

Conclude with `gloPhi_int v spl halg _ ((afsplit_mem_stdLat _ y).1 hy b)`. Introduce `hx`. Use `⟨fun b => spl.symm (x b, 0), (afsplit_mem_stdLat _ _).2 fun b => ?_, fun b => ?_⟩` and prove the remaining obligations. Use `(Formalism.L2.G.split_integral_completion F E v spl halg _).2 ?_` and prove the remaining obligations. Rewrite using `[RingEquiv.apply_symm_apply]`.

Conclude with `⟨hx b, zero_mem _⟩`. Use `show (spl (spl.symm (x b, 0))).1 = x b`. Rewrite using `[RingEquiv.apply_symm_apply]`.
-/
theorem gco_fr_lat (hT : v ∉ plUnder F ST) (x : Fin n → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST), ∀ b, gloPhi v spl (y b) = x b) ↔
      ∀ b, (((1 : GL (Fin n) (v.adicCompletion F))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F := by
  have hL : latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) =
      Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] v.adicCompletion F) (Formalism.BasicNotions.intV E v) :=
    (rll_locL_base n ST v hT).trans (rll_locL_std n v)
  rw [hL, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, hyx⟩ b
    rw [← hyx b]
    exact gloPhi_int v spl halg _ ((afsplit_mem_stdLat _ y).1 hy b)
  · intro hx
    refine ⟨fun b => spl.symm (x b, 0), (afsplit_mem_stdLat _ _).2 fun b => ?_, fun b => ?_⟩
    · refine (Formalism.L2.G.split_integral_completion F E v spl halg _).2 ?_
      rw [RingEquiv.apply_symm_apply]
      exact ⟨hx b, zero_mem _⟩
    · show (spl (spl.symm (x b, 0))).1 = x b
      rw [RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hfin : Finite (GLG E n SG)` using `inferInstance`. Establish `hfo : IsOfFinOrder (levRed hc n ST SG H x)` using `isOfFinOrder_of_finite _`. Take `⟨N, hN, hpow⟩` from `hfo.exists_pow_eq_one`. Establish `h1 : (levTyp lam x) ^ N = 1` using `by show ((lam (levRed hc n ST SG H x))⁻¹) ^ N = 1`. Rewrite using `[inv_pow, ← map_pow, hpow, map_one, inv_one]`.

Establish `h2 : ((levTyp lam x : ℂˣ) : ℂ) ^ N = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, h1, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h2 hN.ne'`.
-/
theorem gco_chi_unit (H : Subgroup (GLG E n SG)) (lam : H →* ℂˣ) (x : levU hc n ST SG H) :
    ‖((levTyp lam x : ℂˣ) : ℂ)‖ = 1 := by
  have hfin : Finite (GLG E n SG) := inferInstance
  have hfo : IsOfFinOrder (levRed hc n ST SG H x) := isOfFinOrder_of_finite _
  obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
  have h1 : (levTyp lam x) ^ N = 1 := by
    show ((lam (levRed hc n ST SG H x))⁻¹) ^ N = 1
    rw [inv_pow, ← map_pow, hpow, map_one, inv_one]
  have h2 : ((levTyp lam x : ℂˣ) : ℂ) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hN.ne'

end Core

end Formalism.L2.Col
