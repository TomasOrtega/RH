import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NEqApply

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish `hdet : X0.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]`. Simplify using `[h1]`. Conclude with `Matrix.nonsing_inv_mul X0 (by rw [hdet]; exact isUnit_one)`.
-/
theorem inv_mul_of_unitri {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E}
    (h0 : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (h1 : ∀ a, X0 a a = 1) : X0⁻¹ * X0 = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
    simp [h1]
  exact Matrix.nonsing_inv_mul X0 (by rw [hdet]; exact isUnit_one)

/- English proof (translation)
Introduce `c`. Rewrite using `[map_sub, map_sub, (hx c).1, (hy c).1, (hx c).2, (hy c).2, sub_self]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem inW_sub {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  rw [map_sub, map_sub, (hx c).1, (hy c).1, (hx c).2, (hy c).2, sub_self]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Use `conv_lhs => rw [decomp X y]`. Rewrite using `[LinearMap.map_add₂, LinearMap.map_add₂, h_sum_left, h_sum_left]`. Simplify using `[(hw _).1, (hw _).2]`.
-/
theorem h_pW_left (y : (VS D).V) {w : (VS D).V} (hw : InW X w) : (VS D).hT y w = (VS D).hT (pW X y) w := by
  conv_lhs => rw [decomp X y]
  rw [LinearMap.map_add₂, LinearMap.map_add₂, h_sum_left, h_sum_left]
  simp [(hw _).1, (hw _).2]

/- English proof (translation)
Introduce `D X u X0 xs M hD`. Take `⟨h0, h1, hxs, hM⟩` from `hD`. Establish `hinv` using `inv_mul_of_unitri h0 h1`. Use `set n := nEq X X0 xs M hinv hxs hM with hn`. Establish `hnx : ∀ y, n y = nL X X0 xs M y` using `fun y => rfl`.

Establish `hFe : (X.Fu u).e = X.eX` using `X.Fu_e u`. Use `⟨n, ⟨fun x y => ?_, fun j x hx => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (VS D).hT (n x) (n y) = (VS D).hT x y`. Rewrite using `[hnx, hnx]`. Conclude with `nL_isom X X0 xs M hinv hxs hM x y`.

Use `show n x - x ∈ (X.Fu u).Xa j`. Establish `hx' : x ∈ (X.Fu u).Xa (j + 1)` using `hx`. Unfold `FlagG.Xa at hx' ⊢`. Rewrite `hx'`, the goal using `[hFe]`. Use `Submodule.span_induction (p := fun x _ => n x - x ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < j})) ?_ ?_ ?_ ?_ hx'` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, hi, rfl⟩`. Rewrite using `[hnx, nL_e]`. Unfold `nE`. Establish `e1 : ∑ b, X0 b i • X.eX b - X.eX i = ∑ b, (X0 b i - if b = i then 1 else 0) • X.eX b`. Simplify using `[sub_smul, Finset.sum_sub_distrib, ite_smul]`.

Rewrite using `[e1]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : (b : ℕ) < j`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)`. Establish `hbi : i ≤ b`.

Establish `: (i : ℕ) < j + 1` using `hi`. Conclude with `Fin.le_def.2 (by omega)`. Break down `hbi.lt_or_eq with hlt | heq` into its components or cases. Rewrite using `[h0 b i hlt, if_neg (ne_of_gt hlt), sub_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`.

Substitute `heq` using the available equality. Rewrite using `[h1, if_pos rfl, sub_self, zero_smul]`. Conclude with `Submodule.zero_mem _`. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`.

Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `c a _ ha`. Rewrite using `[map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ ha`.

Use `show n x - x ∈ (X.Fu u).X`. Establish `horth : ∀ c, (VS D).hT (X.eX c) x = 0`. Introduce `c`. Establish `hxo : x ∈ Lat.orth (VS D) (X.Fu u).X` using `hx`. Unfold `Lat.orth at hxo`.

Use `(Submodule.mem_iInf _).1 hxo (X.eX c)` as an intermediate fact. Rewrite `this` using `[Submodule.mem_iInf]`. Establish `hmem : X.eX c ∈ (X.Fu u).X`. Unfold `FlagG.X`. Rewrite using `[hFe]`.

Conclude with `Submodule.subset_span ⟨c, rfl⟩`. Conclude with `LinearMap.mem_ker.1 (this hmem)`. Unfold `FlagG.X`. Rewrite using `[hFe]`. Establish `hdec` using `decomp X x`.

Simplify using `only [horth, zero_smul, Finset.sum_const_zero, add_zero] at hdec`. Establish `e1 : n x - x = ∑ c, (VS D).hT (X.fY c) x • (nE X X0 c - X.eX c) + ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hdec, hnx, nL_apply]`. Simplify using `only [horth, zero_smul, Finset.sum_const_zero, add_zero]`.

Use `_ = _ := by`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))` and prove the remaining obligations.

Unfold `nE`. Conclude with `Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)) (Submodule.subset_span ⟨c, rfl⟩)`. Use function extensionality and compare the values at `b a`. Use `show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a`. Rewrite using `[hnx, nL_e]`.

Unfold `nE`. Rewrite using `[h_sum_right]`. Simplify using `[h_fe, Finset.sum_ite_eq]`. Use function extensionality and compare the values at `b`. Use `set y := n.symm (X.fY b) with hy`.

Establish `hny : n y = X.fY b` using `n.apply_symm_apply _`. Establish `hd : InW X (pW X y - xs b)` using `inW_sub X (inW_pW X y) (hxs b)`. Establish `hw0 : ∀ w, InW X w → (VS D).hT (pW X y - xs b) w = 0`. Introduce `w hw`. Rewrite using `[LinearMap.map_sub₂, ← h_pW_left X y hw]`.

Establish `: (VS D).hT y w = (VS D).hT (n y) (n w)` using `(nL_isom X X0 xs M hinv hxs hM y w).symm`. Rewrite using `[this, hny, hnx, h_f_nLw X X0 xs M hxs hw, sub_self]`. Use `show pW X y = xs b`. Rewrite using `[← sub_eq_zero]`. Use `(VS D).nondeg.1 _ fun v => ?_` and prove the remaining obligations.

Use `conv_lhs => rw [decomp X v]`. Rewrite using `[map_add, map_add, h_sum_right, h_sum_right, hw0 _ (inW_pW X v)]`. Simplify using `[(inW_left X (inW_pW X y) _).1, (inW_left X (inW_pW X y) _).2, (inW_left X (hxs b) _).1, (inW_left X (hxs b) _).2]`. Establish `hA : Aq X n = X0 * M`. Use function extensionality and compare the values at `b a`.

Use `show (VS D).hT (X.fY b) (n (X.fY a)) = (X0 * M) b a`. Rewrite using `[hnx, nL_f, h_f_nF X X0 xs M hxs]`. Use `show (Xq X n)⁻¹ * Aq X n = M`. Establish `hXq : Xq X n = X0`. Use function extensionality and compare the values at `b a`.

Use `show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a`. Rewrite using `[hnx, nL_e]`. Unfold `nE`. Rewrite using `[h_sum_right]`. Simplify using `[h_fe, Finset.sum_ite_eq]`.

Rewrite using `[hXq, hA, ← Matrix.mul_assoc, hinv, Matrix.one_mul]`.
-/
theorem dictEx_holds : DictEx := by
  intro D X u X0 xs M hD
  obtain ⟨h0, h1, hxs, hM⟩ := hD
  have hinv := inv_mul_of_unitri h0 h1
  set n := nEq X X0 xs M hinv hxs hM with hn
  have hnx : ∀ y, n y = nL X X0 xs M y := fun y => rfl
  have hFe : (X.Fu u).e = X.eX := X.Fu_e u
  refine ⟨n, ⟨fun x y => ?_, fun j x hx => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  ·
    show (VS D).hT (n x) (n y) = (VS D).hT x y
    rw [hnx, hnx]
    exact nL_isom X X0 xs M hinv hxs hM x y
  ·
    show n x - x ∈ (X.Fu u).Xa j
    have hx' : x ∈ (X.Fu u).Xa (j + 1) := hx
    unfold FlagG.Xa at hx' ⊢
    rw [hFe] at hx' ⊢
    refine Submodule.span_induction (p := fun x _ => n x - x ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < j}))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, hi, rfl⟩
      rw [hnx, nL_e]
      unfold nE
      have e1 : ∑ b, X0 b i • X.eX b - X.eX i = ∑ b, (X0 b i - if b = i then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < j
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · have hbi : i ≤ b := by
          have : (i : ℕ) < j + 1 := hi
          exact Fin.le_def.2 (by omega)
        rcases hbi.lt_or_eq with hlt | heq
        · rw [h0 b i hlt, if_neg (ne_of_gt hlt), sub_zero, zero_smul]
          exact Submodule.zero_mem _
        · subst heq
          rw [h1, if_pos rfl, sub_self, zero_smul]
          exact Submodule.zero_mem _
    · simp
    · intro a b _ _ ha hb
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ ha
  ·
    show n x - x ∈ (X.Fu u).X
    have horth : ∀ c, (VS D).hT (X.eX c) x = 0 := by
      intro c
      have hxo : x ∈ Lat.orth (VS D) (X.Fu u).X := hx
      unfold Lat.orth at hxo
      have := (Submodule.mem_iInf _).1 hxo (X.eX c)
      rw [Submodule.mem_iInf] at this
      have hmem : X.eX c ∈ (X.Fu u).X := by
        unfold FlagG.X
        rw [hFe]
        exact Submodule.subset_span ⟨c, rfl⟩
      exact LinearMap.mem_ker.1 (this hmem)
    unfold FlagG.X
    rw [hFe]
    have hdec := decomp X x
    simp only [horth, zero_smul, Finset.sum_const_zero, add_zero] at hdec
    have e1 : n x - x = ∑ c, (VS D).hT (X.fY c) x • (nE X X0 c - X.eX c) +
        ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b := by
      calc n x - x = (∑ c, (VS D).hT (X.fY c) x • nE X X0 c +
            (pW X x + ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b)) -
            (∑ c, (VS D).hT (X.fY c) x • X.eX c + pW X x) := by
            rw [← hdec, hnx, nL_apply]
            simp only [horth, zero_smul, Finset.sum_const_zero, add_zero]
        _ = _ := by
            simp only [smul_sub, Finset.sum_sub_distrib]
            abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    unfold nE
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      (Submodule.subset_span ⟨c, rfl⟩)
  ·
    funext b a
    show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
    rw [hnx, nL_e]
    unfold nE
    rw [h_sum_right]
    simp [h_fe, Finset.sum_ite_eq]
  ·
    funext b
    set y := n.symm (X.fY b) with hy
    have hny : n y = X.fY b := n.apply_symm_apply _
    have hd : InW X (pW X y - xs b) := inW_sub X (inW_pW X y) (hxs b)
    have hw0 : ∀ w, InW X w → (VS D).hT (pW X y - xs b) w = 0 := by
      intro w hw
      rw [LinearMap.map_sub₂, ← h_pW_left X y hw]
      have : (VS D).hT y w = (VS D).hT (n y) (n w) := (nL_isom X X0 xs M hinv hxs hM y w).symm
      rw [this, hny, hnx, h_f_nLw X X0 xs M hxs hw, sub_self]
    show pW X y = xs b
    rw [← sub_eq_zero]
    refine (VS D).nondeg.1 _ fun v => ?_
    conv_lhs => rw [decomp X v]
    rw [map_add, map_add, h_sum_right, h_sum_right, hw0 _ (inW_pW X v)]
    simp [(inW_left X (inW_pW X y) _).1, (inW_left X (inW_pW X y) _).2, (inW_left X (hxs b) _).1,
      (inW_left X (hxs b) _).2]
  ·
    have hA : Aq X n = X0 * M := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.fY a)) = (X0 * M) b a
      rw [hnx, nL_f, h_f_nF X X0 xs M hxs]
    show (Xq X n)⁻¹ * Aq X n = M
    have hXq : Xq X n = X0 := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
      rw [hnx, nL_e]
      unfold nE
      rw [h_sum_right]
      simp [h_fe, Finset.sum_ite_eq]
    rw [hXq, hA, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
