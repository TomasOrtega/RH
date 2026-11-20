import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne

namespace Formalism.FourierDecayAlt.P.CutBP

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ENNReal

noncomputable section

section hs

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `e : B.hsInner (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) = B.hsInner X X`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]`. Unfold `Formalism.FourierDecayAlt.P.Dx2.VV.Cin`. Rewrite using `[Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (S.π_unitary hA hhA), Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (S.π'_unitary _ (WeylGroupFacts.uw_inv hhB))]`. Rewrite `e` using `[TBBx2.Tri.hsInner_self, TBBx2.Tri.hsInner_self]`.

Establish `e2` using `Complex.ofReal_injective e`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e2`.
-/
theorem hsVec_norm_CinL (S : B.RealPlaceData k r Wp Wq) {hA hB : B.Mat k r} (hhA : hA ∈ UWset k r S.z)
    (hhB : hB ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X)‖ = ‖B.hsVec X‖ := by
  have e : B.hsInner (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) =
      B.hsInner X X := by
    rw [Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]
    unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
    rw [Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (S.π_unitary hA hhA),
      Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (S.π'_unitary _ (WeylGroupFacts.uw_inv hhB))]
  rw [TBBx2.Tri.hsInner_self, TBBx2.Tri.hsInner_self] at e
  have e2 := Complex.ofReal_injective e
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e2

end hs

section wt

/- English proof (translation)
Establish `e : ∀ x y : ℕ, x + 1 + y = x + (y + 1)` using `fun x y => by omega`. Establish `e2 : ∀ m : ℕ, m + 1 - 3 = m - 2` using `fun m => by omega`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro d b`.

Simplify using `[C.nAux]`. Consider the case `succ n ih`. Introduce `d b`. Rewrite using `[List.ofFn_succ, Fin.prod_univ_succ]`. Simplify using `only [C.nAux]`.

Simplify using `[ih, e, e2, Fin.val_succ]`. Apply the tactic sequence `all_goals (by_cases hb : b = r + 1 <;> simp [hb])`. Apply the tactic sequence `all_goals (left; congr 1; first | ring | omega)`. Apply the tactic sequence `all_goals clear ih e e2`. Apply the tactic sequence `all_goals done`.
-/
theorem level_product_of_constant_weights (k r : ℕ) (GG : ℝ) : ∀ (n : ℕ) (d : Fin n → ℂ) (b : ℕ),
    C.nAux k r GG (fun _ _ => 1) b (List.ofFn fun i => ((1 : ℕ), d i)) =
      ∏ i : Fin n, (if b + (i : ℕ) = r + 1 then GG ^ (k - 1)
        else ‖d i‖ ^ (2 * (C.Mlev k r (b + (i : ℕ)) - 2))) := by
  have e : ∀ x y : ℕ, x + 1 + y = x + (y + 1) := fun x y => by omega
  have e2 : ∀ m : ℕ, m + 1 - 3 = m - 2 := fun m => by omega
  intro n
  induction n with
  | zero => intro d b; simp [C.nAux]
  | succ n ih =>
    intro d b
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [C.nAux]
    simp [ih, e, e2, Fin.val_succ]
    all_goals (by_cases hb : b = r + 1 <;> simp [hb])
    all_goals (left; congr 1; first | ring | omega)
    all_goals clear ih e e2
    all_goals done

/- English proof (translation)
Establish `h : ∀ {α : Type} (n : ℕ) (f : Fin (n + 1) → α) (z : α), (List.ofFn f).getLast?.getD z = f (Fin.last n)`. Introduce `α n f z`. Rewrite using `[List.getLast?_eq_getElem?]`. Simplify using `only [List.length_ofFn, Nat.add_sub_cancel]`. Rewrite using `[List.getElem?_eq_getElem (by simp), List.getElem_ofFn]`.

Both sides reduce to the same expression. Establish `h2` using `h r (fun i => ((1 : ℕ), c i)) (0, 0)`. Simplify using `only [D.ptLast, TBB.bigPt]`. Conclude with `h2`.
-/
theorem ptLast_bigPt (r : ℕ) (c : Fin (r + 1) → ℂ) : D.ptLast (TBB.bigPt r c) = (1, c (Fin.last r)) := by
  have h : ∀ {α : Type} (n : ℕ) (f : Fin (n + 1) → α) (z : α), (List.ofFn f).getLast?.getD z = f (Fin.last n) := by
    intro α n f z
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_ofFn, Nat.add_sub_cancel]
    rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
    rfl
  have h2 := h r (fun i => ((1 : ℕ), c i)) (0, 0)
  simp only [D.ptLast, TBB.bigPt]
  exact h2

/- English proof (translation)
Establish `hl : D.ptLast (List.ofFn fun l => ((1 : ℕ), c l)) = (1, c (Fin.last r))` using `ptLast_bigPt r c`. Establish `e : ∀ a : Fin r, (2 * (C.Mlev k r (1 + ((Fin.castSucc a : Fin (r + 1)) : ℕ)) - 2) : ℤ) = ((2 * (Mdim k r a - 2) : ℕ) : ℤ)`. Introduce `a`. Establish `ha` using `a.isLt`. Simplify using `only [C.Mlev, Mdim, Fin.coe_castSucc]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [TBB.nPt, TBB.bigPt]`. Rewrite using `[level_product_of_constant_weights, Fin.prod_univ_castSucc]`. Simplify using `only [bcWeight]`. Rewrite using `[if_pos hζ]`.

Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `a _`. Establish `ha` using `a.isLt`. Rewrite using `[if_neg (by simp only [Fin.coe_castSucc]; omega), e a, zpow_natCast]`.

Rewrite using `[if_pos (by simp only [Fin.val_last]; omega)]`. Simplify using `only [D.ptGG, hl]`.
-/
theorem nPt_bigPt (k r : ℕ) (T T' : ℝ) (c : Fin (r + 1) → ℂ) (hζ : T * T' ≤ Complex.normSq (c (Fin.last r))) :
    TBB.nPt k r (T * T') (TBB.bigPt r c) = bcWeight k r T T' ((fun j => c j.castSucc), c (Fin.last r)) := by
  have hl : D.ptLast (List.ofFn fun l => ((1 : ℕ), c l)) = (1, c (Fin.last r)) := ptLast_bigPt r c
  have e : ∀ a : Fin r, (2 * (C.Mlev k r (1 + ((Fin.castSucc a : Fin (r + 1)) : ℕ)) - 2) : ℤ) =
      ((2 * (Mdim k r a - 2) : ℕ) : ℤ) := by
    intro a
    have ha := a.isLt
    simp only [C.Mlev, Mdim, Fin.coe_castSucc]
    omega
  simp only [TBB.nPt, TBB.bigPt]
  rw [level_product_of_constant_weights, Fin.prod_univ_castSucc]
  simp only [bcWeight]
  rw [if_pos hζ]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    have ha := a.isLt
    rw [if_neg (by simp only [Fin.coe_castSucc]; omega), e a, zpow_natCast]
  · rw [if_pos (by simp only [Fin.val_last]; omega)]
    simp only [D.ptGG, hl]

end wt

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

/- English proof (translation)
Establish `hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1)` using `Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd`. Establish `hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d)` using `hG`. Establish `h'` using `Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'`. Use `show ‖B.hsVec (D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d))‖ = _`. Unfold `D.vecV`.

Rewrite using `[dif_pos ⟨hl, hG'⟩, dif_pos h']`. Take `⟨hγ, hZγ, -⟩` from `h'.choose_spec`. Establish `hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r))` using `Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'`. Establish `hc : ∀ a : Fin P.r, d a.castSucc ≠ 0` using `fun a => hd _`. Establish `hsec` using `p.T.base.sec.2 _ hζ`.

Establish `hγ' : bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))) ∈ B.GV P.k P.r` using `bigCellMem P.k P.r _ _ hc hsec.1`. Establish `hZγ'` using `Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ`. Establish `hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose`. Rewrite using `[← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]`. Conclude with `hG'`.

Establish `hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))))`. Rewrite using `[← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']`. Conclude with `hG'`. Take `⟨s, hs, s', hs', hγs⟩` from `Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z' ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩ _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)`. Take `⟨hA, hhA, nA, hnA, hfA, rfl⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs`.

Take `⟨hB, hhB, nB, hnB, hfB, rfl⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'`. Establish `hlaw` using `Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB hfB F`. Rewrite `hlaw` using `[← hγs]`. Rewrite using `[← hlaw, hsVec_norm_CinL p.T.base hhA hhB]`. Establish `hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1` using `Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)`.

Take `⟨hmono, hnz⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1`. Rewrite `hmono` using `[hw]`. Rewrite using `[hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]`.
-/
theorem hsVec_norm_V_bigPt (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ‖B.hsVec (p.V F (TBB.bigPt P.r d))‖ =
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))))‖ := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  show ‖B.hsVec (D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d))‖ = _
  unfold D.vecV
  rw [dif_pos ⟨hl, hG'⟩, dif_pos h']
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))) ∈ B.GV P.k P.r :=
    bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' := Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z'
      (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  rw [← hγs] at hlaw
  rw [← hlaw, hsVec_norm_CinL p.T.base hhA hhB]
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]

end vec

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

/- English proof (translation)
Unfold `bcWeight`. Use `split_ifs with h`. Conclude with `mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)`. Conclude with `le_refl 0`.
-/
theorem bcWeight_nonneg0 (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
  · exact le_refl 0

/- English proof (translation)
Use `set T := Tz P.k P.r p.T.base.z with hT`. Use `set T' := Tz P.k P.r p.T.base.z' with hT'`. Distinguish the cases in `hw : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0`. Rewrite using `[hw, zero_mul, ENNReal.ofReal_zero]`. Conclude with `bot_le`.

Establish `hk : 2 ≤ P.k` using `p.hl.2.2`. Establish `hTT : 0 < T * T'` using `mul_pos p.T.base.T_pos p.T.base.T'_pos`. Establish `hw'` using `hw`. Unfold `bcWeight at hw'`. Use `split_ifs at hw' with hle`.

Establish `hprod` using `left_ne_zero_of_mul hw'`. Establish `hgg` using `right_ne_zero_of_mul hw'`. Establish `hlt : T * T' < Complex.normSq (c (Fin.last P.r))`. Break down `hle.lt_or_eq with h | h` into its components or cases. Conclude with `h`.

Use the proof step `exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]`. Establish `hc : ∀ a : Fin P.r, c a.castSucc ≠ 0`. Introduce `a ha`. Apply `hprod` to reduce the goal to its premises. Use `Finset.prod_eq_zero (Finset.mem_univ a) ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[ha, norm_zero, zero_pow]`. Unfold `Mdim`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hlast : c (Fin.last P.r) ≠ 0`. Introduce `h0`. Rewrite `hlt` using `[h0, Complex.normSq_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : ∀ a, c a ≠ 0`.

Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hlast`. Consider the case `cast i => exact hc i`. Establish `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)` using `by show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)`.

Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`. Establish `hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hlt hp]`. Establish `hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)` using `Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd`.

Rewrite using `[TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]`. Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r))` using `nPt_bigPt P.k P.r T T' c hle`. Rewrite using `[hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]`. Conclude with `absurd rfl hw'`.
-/
theorem pt_le (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    ENNReal.ofReal (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2) ≤
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  by_cases hw : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0
  · rw [hw, zero_mul, ENNReal.ofReal_zero]; exact bot_le
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r T T' c hle
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · exact absurd rfl hw'

/- English proof (translation)
Unfold `LemB`. Rewrite using `[ENNReal.ofReal_one, one_mul]`. Use `set T := Tz P.k P.r p.T.base.z with hT`. Use `set T' := Tz P.k P.r p.T.base.z' with hT'`. Use `set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r T T' q * ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))‖ ^ 2 with hg`.

Establish `hβ : B.beta p.T.base F F = ∫ q, ((g q : ℝ) : ℂ)`. Unfold `B.beta betaBig`. Use `integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Simplify using `only [hg]`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hβ, integral_complex_ofReal, Complex.ofReal_re]`. Establish `key : ENNReal.ofReal (∫ q, g q) ≤ ∫⁻ q, ENNReal.ofReal (g q)`. Distinguish the cases in `hint : Integrable g`.

Rewrite using `[ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _))]`. Rewrite using `[integral_undef hint, ENNReal.ofReal_zero]`. Conclude with `bot_le`. Use `le_trans key ?_` and prove the remaining obligations. Set `e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ` to `(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm`.

Establish `hmp : MeasurePreserving e volume volume` using `(Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))`. Establish `he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r))`. Introduce `c`. Simplify using `[e, MeasurableEquiv.piFinSuccAbove]`. Both sides reduce to the same expression.

Rewrite using `[← hmp.lintegral_comp_emb e.measurableEmbedding]`. Unfold `TBB.jN2`. Use `lintegral_mono fun c => ?_` and prove the remaining obligations. Rewrite using `[he c]`. Conclude with `pt_le p F c`.
-/
theorem lemB_one (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : LemB p F 1 := by
  unfold LemB
  rw [ENNReal.ofReal_one, one_mul]
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r T T' q *
    ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))‖ ^ 2 with hg
  have hβ : B.beta p.T.base F F = ∫ q, ((g q : ℝ) : ℂ) := by
    unfold B.beta betaBig
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hg]
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hβ, integral_complex_ofReal, Complex.ofReal_re]
  have key : ENNReal.ofReal (∫ q, g q) ≤ ∫⁻ q, ENNReal.ofReal (g q) := by
    by_cases hint : Integrable g
    · rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _))]
    · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le
  refine le_trans key ?_
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_mono fun c => ?_
  rw [he c]
  exact pt_le p F c

end main

end

end Formalism.FourierDecayAlt.P.CutBP
