import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFnM : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rvhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rvhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

/- English proof (translation)
Establish `e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) = fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c`. Use function extensionality and compare the values at `g`. Simplify using `only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]`. Rewrite using `[e]`. Apply the tactic sequence `exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _ (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))`.
-/
theorem rim_herm (v w : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg 1 (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) := by
  have e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) =
      fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c := by
    funext g
    simp only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]
  rw [e]
  exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _
    (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))

/- English proof (translation)
Unfold `rowV`. Distinguish the cases in `h : p.val < r`. Simplify using `only [dif_pos h]`. Conclude with `rim_herm _ _`. Distinguish the cases in `h2 : p.val = r`.

Simplify using `only [dif_neg h, dif_pos h2]`. Conclude with `rim_herm _ _`. Simplify using `only [dif_neg h, dif_neg h2]`. Conclude with `pd_const _ 1`.
-/
theorem rim_rowV (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (p q : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => rowV k r z g J p q) := by
  unfold rowV
  by_cases h : p.val < r
  · simp only [dif_pos h]
    exact rim_herm _ _
  · by_cases h2 : p.val = r
    · simp only [dif_neg h, dif_pos h2]
      exact rim_herm _ _
    · simp only [dif_neg h, dif_neg h2]
      exact pd_const _ 1

/- English proof (translation)
The claim follows from `pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by simpa only [Matrix.of_apply] using rim_rowV z J a b`.
-/
theorem rim_alJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => alJ k r z g J) :=
  pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by
    simpa only [Matrix.of_apply] using rim_rowV z J a b

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rimCat {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) : List ι → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ rimCat Θs l

/- English proof (translation)
The claim follows from `| [] => fun T hT => absurd hT List.not_mem_nil | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)`.
-/
theorem rimCat_poly {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (rimCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)

/- English proof (translation)
The claim follows from `| [] => by simp [rimCat, B.opApply] | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]`.
-/
theorem rimCat_apply {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (rimCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [rimCat, B.opApply]
  | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]

/- English proof (translation)
Rewrite using `[rimCat, QMinOp.opOrder_append, ho i]`. Conclude with `max_eq_left (ri_order_le _ (rimCat_poly h l))`.
-/
theorem rimCat_order {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : ι) (l : List ι) :
    B.opOrder (rimCat Θs (i :: l)) = t := by
  rw [rimCat, QMinOp.opOrder_append, ho i]
  exact max_eq_left (ri_order_le _ (rimCat_poly h l))

/- English proof (translation)
Introduce `a b h`. Establish `h' : a.val < b.val` using `h`. Use `show (rowsR k r 0 a).val < (rowsR k r 0 b).val`. Simplify using `only [rowsR]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem residue_rows_strict_mono : StrictMono (rowsR k r 0) := by
  intro a b h
  have h' : a.val < b.val := h
  show (rowsR k r 0 a).val < (rowsR k r 0 b).val
  simp only [rowsR]
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `(residue_rows_strict_mono (k := k) (r := r))` and compare the differences between its conclusion and the goal.
-/
theorem rim_mem : rowsR k r 0 ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (residue_rows_strict_mono (k := k) (r := r))

/- English proof (translation)
Establish `h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)), ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧ ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ …` using `fun x => QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _ (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _`. Use `choose Θs hP hO hR using h`. Set `idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)))` to `((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList`. Establish `hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx`. Simplify using `only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]`.

Conclude with `rim_mem`. Use `⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by`. Consider the cases of `h' : idx with`. Consider the case `nil => rw [h'] at hmem`.

Conclude with `absurd hmem List.not_mem_nil`. Consider the case `cons i l => exact ⟨i, l, rfl⟩`. Rewrite using `[hl]`. Conclude with `rimCat_order hP hO _ _`. Introduce `UU F hF g hgU hg`.

Rewrite using `[rimCat_apply]`. Simplify using `only [idx]`. Rewrite using `[Finset.sum_map_toList, Finset.sum_product]`. Simplify using `only [rvhatOp, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]`.
-/
theorem rim_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rvhatOp k r z z' Y F g := by
  have h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)),
      ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ j ∈ ({()} : Finset Unit),
          (fun (_ : Unit) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (x.1 : ℕ)) * z' (wI k r x.1) * alJ k r z g x.2)) j g •
            qminorOp (Q.EH k r) x.2 ((fun (_ : Unit) => colsV k r x.1) j) (Q.uC k r (Fin.last r) Y - 1) F g := fun x =>
    QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _
      (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _
  choose Θs hP hO hR using h
  let idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1))) :=
    ((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList
  have hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx := by
    simp only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]
    exact rim_mem
  refine ⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩
  · obtain ⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by
      cases h' : idx with
      | nil => rw [h'] at hmem; exact absurd hmem List.not_mem_nil
      | cons i l => exact ⟨i, l, rfl⟩
    rw [hl]
    exact rimCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [rimCat_apply]
    simp only [idx]
    rw [Finset.sum_map_toList, Finset.sum_product]
    simp only [rvhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]

end ops

/- English proof (translation)
Introduce `ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y`. Take `⟨Θ, hP, hO, hR⟩` from `rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε`. Establish `hn : 0 < 2 * S.G.r + S.G.k + 1` using `by omega`. Use `⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp F hF g hg`.

Rewrite `hF` using `[hO]`. Establish `hgG : g ∈ B.GV S.G.k S.G.r` using `hg.1`. Establish `hsg : B.sgs p g ∈ B.GV S.G.k S.G.r` using `Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG`. Rewrite using `[hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]`. Establish `e2 : B.rho (T v).base p (B.opApply Θ F) g = B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g`.

Simplify using `only [B.rho]`. Rewrite using `[hR _ _ hF _ hsg hsg]`. Rewrite using `[e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]`. Simplify using `only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]`. Introduce `U F hU hF g hg`.

Establish `hgG : g ∈ B.GV S.G.k S.G.r` using `by simpa [Q.Glev] using hg.1`. Use `hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U', F', hU', hg₀U, hc, he⟩` from `hF g₀ hg₀`. Use `⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩` and prove the remaining obligations.

Simplify `hxG` using `[Q.Glev]`.
-/
theorem jDRRealInvM_of_inv (hI : JDRInvFnM) : JDRRealInvM := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
