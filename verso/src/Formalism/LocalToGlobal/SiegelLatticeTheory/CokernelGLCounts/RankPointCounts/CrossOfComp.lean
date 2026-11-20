import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaCongG

noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount
  Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Unfold `Cross at h1 h2 ⊢`. Establish `d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det` using `fun f B => (RingHom.map_det f B).symm`. Rewrite `h1`, `h2` using `[ld_map, ld_map, d, d, ← map_mul, ← map_mul]`. Apply `g.e.injective` to reduce the goal to its premises. Conclude with `Prod.ext h1 h2`.
-/
theorem cross_of_comp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ} {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : Cross (A.map (π1 M g)) (A'.map (π1 M g))) (h2 : Cross (A.map (π2 M g)) (A'.map (π2 M g))) : Cross A A' := by
  unfold Cross at h1 h2 ⊢
  have d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det :=
    fun f B => (RingHom.map_det f B).symm
  rw [ld_map, ld_map, d, d, ← map_mul, ← map_mul] at h1 h2
  apply g.e.injective
  exact Prod.ext h1 h2

/- English proof (translation)
Introduce `hA hT hPH w w' Z Z' hk hZ hZ' p hne heq`. Use `set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc`. Establish `hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c` using `(cornerSh_of_kind δ _ _ p hk).symm`. Use `set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY`. Use `set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'`.

Establish `hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K` using `(D.s.atP p).Ep) D.R.rS := by`. Apply the tactic sequence `intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp`. Establish `eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y`. Unfold `FCount.thZ thL`. Rewrite using `[hcm]`.

Establish `eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y'`. Unfold `FCount.thZ thL`. Rewrite using `[hcm, hc']`. Rewrite `hne`, `heq` using `[eY]`. Rewrite `heq` using `[eY']`.

Establish `hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z')` using `cross_zhatLoc δ M p (cross_global hk hZ hZ')`. Establish `hZc : Cross (CntLocal.ZZP (M` using `M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by`. Unfold `CntLocal.ZZP`. Break down `hs : (M p).split with _ | g` into its components or cases. Unfold `Loc.HermSp.ZZplusOf`.

Rewrite using `[hs]`. Conclude with `hXc`. Use `cross_of_comp (M p) g ?_ ?_` and prove the remaining obligations. Rewrite using `[zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]`. Conclude with `cross_shift (cross_map _ hXc) _ _`.

Rewrite using `[zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]`. Conclude with `cross_shift (cross_transpose (cross_map _ hXc)) _ _`. Unfold `clsOf at hne heq`. Distinguish the cases in `h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det`. Use `swap`.

Conclude with `absurd (dif_neg h1) hne`. Rewrite `heq` using `[dif_pos h1]`. Distinguish the cases in `h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det`. Use `swap`. Rewrite using `[dif_neg h2] at heq; exact absurd heq (by simp)`.

Rewrite `heq` using `[dif_pos h2]`. Use `set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ`. Use `set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'`. Establish `hmap : ZZ.Z.map (M p).R.subtype = Y` using `rfl`. Establish `hmap' : ZZ'.Z.map (M p).R.subtype = Y'` using `rfl`.

Establish `hiso : Nonempty ((M p).Iso ZZ ZZ')` using `Quotient.exact (Option.some.inj heq)`. Establish `hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) = (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)`. Rewrite using `[hmap, hmap']`. Conclude with `kappa_eq hZc c h1.2 h2.2`. Take `⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩` from `hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ`.

Use `set L := l.map (M p).R.subtype with hLdef`. Use `set P := ρ.map (M p).R.subtype with hPdef`. Establish `hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0`. Apply the tactic sequence `intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp`. Establish `hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0`.

Apply the tactic sequence `intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp`. Establish `hYrel : Y' = L * Y * P`. Rewrite using `[← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]`. Establish `hZrel : CntLocal.ZZP (M` using `M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by`. Establish `e` using `hYrel`.

Rewrite `e` using `[hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM, corner_sandwich L P hL hP 1]`. Conclude with `add_right_cancel e`. Establish `hLR : ∀ i j, L i j ∈ (M p).R` using `fun i j => (l i j).2`. Establish `hPR : ∀ i j, P i j ∈ (M p).R` using `fun i j => (ρ i j).2`. Establish `hLu : ∃ y ∈ (M p).R, L.det * y = 1`.

Take `⟨v, hv⟩` from `hlu`. Use `⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩` and prove the remaining obligations. Establish `: L.det = ((l.det : (M p).R) : (D.s.atP p).Ep)` using `(RingHom.map_det (M p).R.subtype l).symm`. Rewrite using `[this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]`. Establish `hPu : ∃ y ∈ (M p).R, P.det * y = 1`.

Take `⟨v, hv⟩` from `hρu`. Use `⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩` and prove the remaining obligations. Establish `: P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep)` using `(RingHom.map_det (M p).R.subtype ρ).symm`. Rewrite using `[this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]`. Break down `hs : (M p).split with _ | g` into its components or cases.

Establish `hRO : (M p).R = (M p).L.O` using `by unfold Loc.Model.R; rw [hs]`. Establish `hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P`. Establish `e` using `hZrel`. Unfold `CntLocal.ZZP Loc.HermSp.ZZplusOf at e`. Rewrite `e` using `[hs]`.

Conclude with `e`. Take `⟨yL, hyL, hLy⟩` from `hLu`. Take `⟨yP, hyP, hPy⟩` from `hPu`. Conclude with `gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j) ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX`. Conclude with `gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel`.
-/
theorem gaPlusTh_of (hLO : LiftOrb) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' := by
  intro hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc
  have hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c := (cornerSh_of_kind δ _ _ p hk).symm
  set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY
  set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'
  have hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K := (D.s.atP p).Ep) D.R.rS := by
    intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  have eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y := by
    unfold FCount.thZ thL; rw [hcm]
  have eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y' := by
    unfold FCount.thZ thL; rw [hcm, hc']
  rw [eY] at hne heq
  rw [eY'] at heq

  have hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := cross_zhatLoc δ M p (cross_global hk hZ hZ')
  have hZc : Cross (CntLocal.ZZP (M := M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by
    unfold CntLocal.ZZP
    rcases hs : (M p).split with _ | g
    · unfold Loc.HermSp.ZZplusOf; rw [hs]; exact hXc
    · refine cross_of_comp (M p) g ?_ ?_
      · rw [zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]
        exact cross_shift (cross_map _ hXc) _ _
      · rw [zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]
        exact cross_shift (cross_transpose (cross_map _ hXc)) _ _
  unfold clsOf at hne heq
  by_cases h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  swap
  · exact absurd (dif_neg h1) hne
  rw [dif_pos h1] at heq
  by_cases h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det
  swap
  · rw [dif_neg h2] at heq; exact absurd heq (by simp)
  rw [dif_pos h2] at heq
  set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ
  set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'
  have hmap : ZZ.Z.map (M p).R.subtype = Y := rfl
  have hmap' : ZZ'.Z.map (M p).R.subtype = Y' := rfl
  have hiso : Nonempty ((M p).Iso ZZ ZZ') := Quotient.exact (Option.some.inj heq)
  have hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) =
      (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) := by
    rw [hmap, hmap']
    exact kappa_eq hZc c h1.2 h2.2
  obtain ⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩ := hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ
  set L := l.map (M p).R.subtype with hLdef
  set P := ρ.map (M p).R.subtype with hPdef
  have hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0 := by
    intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp
  have hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
    intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp
  have hYrel : Y' = L * Y * P := by
    rw [← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]
  have hZrel : CntLocal.ZZP (M := M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by
    have e := hYrel
    rw [hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM,
      corner_sandwich L P hL hP 1] at e
    exact add_right_cancel e
  have hLR : ∀ i j, L i j ∈ (M p).R := fun i j => (l i j).2
  have hPR : ∀ i j, P i j ∈ (M p).R := fun i j => (ρ i j).2
  have hLu : ∃ y ∈ (M p).R, L.det * y = 1 := by
    obtain ⟨v, hv⟩ := hlu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : L.det = ((l.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype l).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hPu : ∃ y ∈ (M p).R, P.det * y = 1 := by
    obtain ⟨v, hv⟩ := hρu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype ρ).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rcases hs : (M p).split with _ | g
  · have hRO : (M p).R = (M p).L.O := by unfold Loc.Model.R; rw [hs]
    have hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P := by
      have e := hZrel
      unfold CntLocal.ZZP Loc.HermSp.ZZplusOf at e
      rw [hs] at e
      exact e
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    exact gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j)
      ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX
  · exact gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
