import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section cell

variable {k ρ : ℕ}

/- English proof (translation)
Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Introduce `i h1 h2`. Break down `i with _ | i` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[PBH.shS]`.
-/
theorem finRange_one_add (ρ : ℕ) :
    List.finRange (1 + ρ) = (⟨0, by omega⟩ : Fin (1 + ρ)) :: (List.finRange ρ).map PBH.shS := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rcases i with _ | i
    · simp
    · simp [PBH.shS]

/- English proof (translation)
Use extensionality with `⟨p, hp⟩ ⟨q, hq⟩`. Establish `ha` using `a.isLt`. Unfold `w1 ιLev`. Simplify using `only [eI, esI, PBH.shS, Fin.mk.injEq]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega)`.
-/
theorem weyl_cell_shift_eq_level_embedding (a : Fin ρ) (x : ℂ) : w1 k (1 + ρ) (PBH.shS a) x = ιLev k 1 ρ (w1 k ρ a x) := by
  ext ⟨p, hp⟩ ⟨q, hq⟩
  have ha := a.isLt
  unfold w1 ιLev
  simp only [eI, esI, PBH.shS, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using Formalism.FourierDecayAlt.P.Dx2.Tower.lev_one (k := k) 1 ρ`. Consider the case `cons a l ih => rw [List.prod_cons, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, ih, List.map_cons, List.prod_cons]`.
-/
theorem iota_list_prod (l : List (Mx k ρ)) : ιLev k 1 ρ l.prod = (l.map (ιLev k 1 ρ)).prod := by
  induction l with
  | nil => simpa using Formalism.FourierDecayAlt.P.Dx2.Tower.lev_one (k := k) 1 ρ
  | cons a l ih => rw [List.prod_cons, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, ih, List.map_cons, List.prod_cons]

/- English proof (translation)
Unfold `wCell`. Rewrite using `[List.filter_eq_self.2 (fun a _ => by simp), List.filter_eq_self.2 (fun a _ => by simp), finRange_one_add, iota_list_prod]`. Rewrite using `[List.map_cons, List.prod_cons, PBH.consC_zero, List.map_map, List.map_map]`. Use `congr 2`. Use `List.map_congr_left (fun a _ => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp, PBH.consC_sh, weyl_cell_shift_eq_level_embedding]`.
-/
theorem wCell_consC (t : ℂ) (c : Fin ρ → ℂ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) =
      w1 k (1 + ρ) ⟨0, by omega⟩ t * ιLev k 1 ρ (wCell k ρ (Fin.last ρ) c) := by
  unfold wCell
  rw [List.filter_eq_self.2 (fun a _ => by simp),
    List.filter_eq_self.2 (fun a _ => by simp), finRange_one_add, iota_list_prod]
  rw [List.map_cons, List.prod_cons, PBH.consC_zero, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun a _ => ?_)
  simp only [Function.comp, PBH.consC_sh, weyl_cell_shift_eq_level_embedding]

/- English proof (translation)
Establish `hinv : ((Matrix.of fun _ _ : Fin 1 => t)ᴴ)⁻¹ = Matrix.of fun _ _ : Fin 1 => (star t)⁻¹`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Use extensionality with `a b`. Use `fin_cases a`. Use `fin_cases b`.

Simplify using `[Matrix.mul_apply, ht]`. Use extensionality with `i l`. Take `⟨x, rfl⟩` from `(U.eB k 1 ρ).surjective i`. Take `⟨y, rfl⟩` from `(U.eB k 1 ρ).surjective l`. Rewrite using `[U.mMap, PBH.weyl_lift_eq_pair, Matrix.mul_one, Matrix.one_mul, hinv, Ux3.block3_apply]`.

Establish `hX : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inl (Sum.inl x)) = ⟨0, by omega⟩` using `fun x => Fin.ext (by rw [Ux3.block_index_first_val]; simp)`. Establish `hV : ∀ v : Fin (2 * ρ + k + 1), U.eB k 1 ρ (Sum.inl (Sum.inr v)) = ⟨1 + v.val, by omega⟩` using `fun v => Fin.ext (by rw [Ux3.block_index_middle_val])`. Establish `hS : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inr x) = ⟨2 * (1 + ρ) + k, by omega⟩` using `fun x => Fin.ext (by rw [Ux3.block_index_last_val]; have := x.isLt; simp; omega)`. Apply the tactic sequence `rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>`. Apply the tactic sequence `simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.one_apply, …`.

Apply the tactic sequence `unfold w1 <;>`. Apply the tactic sequence `simp only [eI, esI, Fin.ext_iff] <;>`. Apply the tactic sequence `(have hx := x.isLt; have hy := y.isLt; split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega))`.
-/
theorem weyl_cell_zero_eq_embedding {t : ℂ} (ht : t ≠ 0) :
    w1 k (1 + ρ) ⟨0, by omega⟩ t = U.mMap k 1 ρ (Matrix.of fun _ _ => t) 1 := by
  have hinv : ((Matrix.of fun _ _ : Fin 1 => t)ᴴ)⁻¹ = Matrix.of fun _ _ : Fin 1 => (star t)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, ht]
  ext i l
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective l
  rw [U.mMap, PBH.weyl_lift_eq_pair, Matrix.mul_one, Matrix.one_mul, hinv, Ux3.block3_apply]
  have hX : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inl (Sum.inl x)) = ⟨0, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_first_val]; simp)
  have hV : ∀ v : Fin (2 * ρ + k + 1), U.eB k 1 ρ (Sum.inl (Sum.inr v)) = ⟨1 + v.val, by omega⟩ := fun v =>
    Fin.ext (by rw [Ux3.block_index_middle_val])
  have hS : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inr x) = ⟨2 * (1 + ρ) + k, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_last_val]; have := x.isLt; simp; omega)
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.one_apply, hX, hV, hS] <;>
    unfold w1 <;>
    simp only [eI, esI, Fin.ext_iff] <;>
    (have hx := x.isLt; have hy := y.isLt; split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega))

/- English proof (translation)
Rewrite using `[wCell_consC, Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, weyl_cell_zero_eq_embedding ht, ← Formalism.FourierDecayAlt.P.Dx2.MN.embG_eq, Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG, Matrix.one_mul]`.
-/
theorem cell_iota {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) * ιLev k 1 ρ g =
      U.mMap k 1 ρ (Matrix.of fun _ _ => t) (wCell k ρ (Fin.last ρ) c * g) := by
  rw [wCell_consC, Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, weyl_cell_zero_eq_embedding ht,
    ← Formalism.FourierDecayAlt.P.Dx2.MN.embG_eq, Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Finset.prod_congr rfl (fun a _ => if_pos (by rw [Fin.val_last]; exact a.isLt)), Finset.prod_congr rfl (fun (a : Fin ρ) _ => if_pos (by rw [Fin.val_last]; exact a.isLt))]`. Rewrite using `[← Fintype.prod_equiv (finCongr (Nat.add_comm ρ 1)) (fun a : Fin (ρ + 1) => ‖PBH.consC t c (finCongr (Nat.add_comm ρ 1) a)‖ ^ (Mdim k (1 + ρ) (finCongr (Nat.add_comm ρ 1) a) - 1)) _ (fun _ => rfl)]`. Rewrite using `[Fin.prod_univ_succ]`. Use `congrArg₂ (· * ·) ?_ ?_` and prove the remaining obligations. Establish `h0 : finCongr (Nat.add_comm ρ 1) (0 : Fin (ρ + 1)) = ⟨0, by omega⟩` using `Fin.ext rfl`.

Rewrite using `[h0, PBH.consC_zero]`. Use `congr 1`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hs : finCongr (Nat.add_comm ρ 1) a.succ = PBH.shS a` using `Fin.ext (by simp [PBH.shS])`. Rewrite using `[hs, PBH.consC_sh]`.

Use `congr 1`. Simplify using `only [Mdim, PBH.shS]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gauge_consC (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ a : Fin (1 + ρ), (if a.val < (Fin.last (1 + ρ)).val then ‖PBH.consC t c a‖ ^ (Mdim k (1 + ρ) a - 1)
      else 1 : ℝ)) =
      ‖t‖ ^ (2 * (1 + ρ) + k) *
        ∏ a : Fin ρ, (if a.val < (Fin.last ρ).val then ‖c a‖ ^ (Mdim k ρ a - 1) else 1 : ℝ) := by
  rw [Finset.prod_congr rfl (fun a _ => if_pos (by rw [Fin.val_last]; exact a.isLt)),
    Finset.prod_congr rfl (fun (a : Fin ρ) _ => if_pos (by rw [Fin.val_last]; exact a.isLt))]
  rw [← Fintype.prod_equiv (finCongr (Nat.add_comm ρ 1))
    (fun a : Fin (ρ + 1) => ‖PBH.consC t c (finCongr (Nat.add_comm ρ 1) a)‖ ^
      (Mdim k (1 + ρ) (finCongr (Nat.add_comm ρ 1) a) - 1)) _ (fun _ => rfl)]
  rw [Fin.prod_univ_succ]
  refine congrArg₂ (· * ·) ?_ ?_
  · have h0 : finCongr (Nat.add_comm ρ 1) (0 : Fin (ρ + 1)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [h0, PBH.consC_zero]
    congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    have hs : finCongr (Nat.add_comm ρ 1) a.succ = PBH.shS a := Fin.ext (by simp [PBH.shS])
    rw [hs, PBH.consC_sh]
    congr 1
    simp only [Mdim, PBH.shS]
    omega

/- English proof (translation)
Unfold `resG`. Rewrite using `[cell_iota ht, smul_smul, gauge_consC, ← Complex.ofReal_mul]`.
-/
theorem resG_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (J : Mx k (1 + ρ) → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k (1 + ρ) (Fin.last (1 + ρ)) J (PBH.consC t c) (ιLev k 1 ρ g) =
      ((‖t‖ ^ (2 * (1 + ρ) + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) c g := by
  unfold resG
  rw [cell_iota ht, smul_smul, gauge_consC, ← Complex.ofReal_mul]

/- English proof (translation)
Substitute `hn` using the available equality. Simplify using `only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]`. Conclude with `resG_consC ht J c g`.
-/
theorem resG_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (hn : n = 1 + ρ) {t : ℂ} (ht : t ≠ 0)
    (J : Mx k n → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k n (Fin.last n) J (fun l => PBH.consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn.symm (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) c g := by
  subst hn
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact resG_consC ht J c g

end cell

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

/- English proof (translation)
The claim follows from `pb_radHead_of module_form_eq_radial_form_one exists_zeta_normalized_haar hHP`.
-/
theorem pb_radHead_of_headPic (hHP : HeadPic) : KB.RadHead :=
  pb_radHead_of module_form_eq_radial_form_one exists_zeta_normalized_haar hHP

end Formalism.FourierDecayAlt.P
