import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StarEqConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClRow

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Unfold `theta`. Use `split_ifs with h`. Take `⟨hint, -⟩` from `h.choose_spec`. Establish `hmem : (⟨h.choose, hint⟩ : 𝓞 D.host.E) • x ∈ (I : Submodule (𝓞 D.host.E) D.host.E)` using `Submodule.smul_mem _ _ hx`. Rewrite `hmem` using `[Algebra.smul_def, mul_comm]`. Then use the resulting hypothesis.

Rewrite using `[mul_zero]`. Conclude with `(I : Submodule (𝓞 D.host.E) D.host.E).zero_mem`.
-/
theorem theta_int_mem {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E} (hx : x ∈ I) :
    x * theta D ∈ I := by
  unfold theta
  split_ifs with h
  · obtain ⟨hint, -⟩ := h.choose_spec
    have hmem : (⟨h.choose, hint⟩ : 𝓞 D.host.E) • x ∈ (I : Submodule (𝓞 D.host.E) D.host.E) :=
      Submodule.smul_mem _ _ hx
    rwa [Algebra.smul_def, mul_comm] at hmem
  · rw [mul_zero]
    exact (I : Submodule (𝓞 D.host.E) D.host.E).zero_mem

/- English proof (translation)
Introduce `c`. Take `⟨h1, h2⟩` from `hx c`. Take `⟨h3, h4⟩` from `hy c`. Conclude with `⟨by rw [map_sub, h1, h3, sub_zero], by rw [map_sub, h2, h4, sub_zero]⟩`.
-/
theorem inW_sub {X : HidaSetting D} {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  obtain ⟨h1, h2⟩ := hx c
  obtain ⟨h3, h4⟩ := hy c
  exact ⟨by rw [map_sub, h1, h3, sub_zero], by rw [map_sub, h2, h4, sub_zero]⟩

/- English proof (translation)
Simplify using `only [blkQ, tauQ]`. Apply the tactic sequence `first | exact sub_zero _ | rfl | simp`.
-/
theorem xblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inl p)) - tauQ X u (Sum.inl (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (X0 p.1.1 p.1.2) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

/- English proof (translation)
Simplify using `only [blkQ, tauQ]`. Apply the tactic sequence `first | exact sub_zero _ | rfl | simp`.
-/
theorem rblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inr b)) - tauQ X u (Sum.inl (Sum.inr b)) (blkQ X u X0 xs M) =
      rowV X u (xs b) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

/- English proof (translation)
Introduce `D X u X0 xs M hok`. Establish `hup` using `hok.1`. Establish `hd` using `hok.2.1`. Establish `hW` using `hok.2.2.1`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hX : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a`. Introduce `b a hba`. Establish `h1` using `h (Sum.inl (Sum.inl ⟨(b, a), hba⟩))`. Rewrite `h1` using `[xblk]`.

Simplify using `only [cLat] at h1`. Take `⟨t, ht, hte⟩` from `(CovB.mem_closure_embV X _ _).1 h1`. Establish `: t = X0 b a` using `CovB.embVHom_injective X hte`. Rewrite using `[← this]`. Conclude with `ht`.

Establish `hR : ∀ b, xs b ∈ aaLb X b`. Introduce `b`. Establish `h1` using `h (Sum.inl (Sum.inr b))`. Rewrite `h1` using `[rblk]`. Simplify using `only [cLat] at h1`.

Take `⟨y, hy, hye⟩` from `(mem_cl_row X u b _).1 h1`. Establish `hz : rowV X u (xs b - y) = 0` using `by rw [rowV_sub, hye, sub_self]`. Use `rowV_inj X u _ (inW_sub (hW b) (aaLb_inW X hy)) hz` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`. Rewrite using `[this]`.

Conclude with `hy`. Establish `hG` using `Gp_mem X X0 xs hup hd hX hR`. Use `⟨hX, hR, ?_⟩` and prove the remaining obligations. Establish `hMu : ∀ b a : Fin D.R.rS, b < a → M b a ∈ iP D b a`. Introduce `b a hba`.

Establish `h1` using `h (Sum.inr (Sum.inl ⟨(b, a), hba⟩))`. Rewrite `h1` using `[kblk X u hok]`. Simplify using `only [cLat] at h1`. Take `⟨t, ht, hte⟩` from `(CovB.mem_closure_embV X _ _).1 h1`. Establish `: t = M b a` using `CovB.embVHom_injective X hte`.

Rewrite using `[← this]`. Conclude with `ht`. Introduce `b a`. Break down `lt_trichotomy b a with hba | hba | hba` into its components or cases. Conclude with `hMu b a hba`.

Substitute `hba` using the available equality. Establish `h1` using `h (Sum.inr (Sum.inr b))`. Rewrite `h1` using `[imblk X u hok]`. Take `⟨t, ht, htc, hte⟩` from `(mem_cl_im X u b _).1 h1`. Establish `hteq : t = xiA X0 xs M b` using `im_inj X htc (xiA_conj X hok b) fun v => congrFun hte v`.

Establish `hxi : xiA X0 xs M b ∈ iP D b b` using `by rw [← hteq]; exact ht`. Establish `e : M b b = xiA X0 xs M b - Gp D X0 xs b b * theta D` using `by unfold xiA; ring`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ hxi (theta_int_mem (hG b b))`. Establish `e` using `entry_rel X hok b a`.

Establish `e2 : M b a = -Gp D X0 xs b a - star (M a b)` using `by rw [← e]; ring`. Rewrite using `[e2]`. Use `Submodule.sub_mem _ (Submodule.neg_mem _ (hG b a)) ?_` and prove the remaining obligations. Establish `hab : M a b ∈ iP D b a` using `by rw [iP_comm]; exact hMu a b hba`. Conclude with `star_mem_iP hab`.

Introduce and unpack `⟨hX, hR, hM⟩`. Establish `hG` using `Gp_mem X X0 xs hup hd hX hR`. Introduce `p`. Break down `p with ((p | b) | (p | a))` into its components or cases. Rewrite using `[xblk]`.

Simplify using `only [cLat]`. Conclude with `(CovB.mem_closure_embV X _ _).2 ⟨X0 p.1.1 p.1.2, hX _ _ p.2, rfl⟩`. Rewrite using `[rblk]`. Simplify using `only [cLat]`. Conclude with `(mem_cl_row X u b _).2 ⟨xs b, hR b, rfl⟩`.

Rewrite using `[kblk X u hok]`. Simplify using `only [cLat]`. Conclude with `(CovB.mem_closure_embV X _ _).2 ⟨M p.1.1 p.1.2, hM _ _, rfl⟩`. Rewrite using `[imblk X u hok]`. Use `(mem_cl_im X u a _).2 ⟨xiA X0 xs M a, ?_, xiA_conj X hok a, rfl⟩` and prove the remaining obligations.

Conclude with `Submodule.add_mem _ (hM a a) (theta_int_mem (hG a a))`.
-/
theorem fibQ_holds : FibQ := by
  intro D X u X0 xs M hok
  have hup := hok.1
  have hd := hok.2.1
  have hW := hok.2.2.1
  constructor
  · intro h

    have hX : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a := by
      intro b a hba
      have h1 := h (Sum.inl (Sum.inl ⟨(b, a), hba⟩))
      rw [xblk] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = X0 b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht

    have hR : ∀ b, xs b ∈ aaLb X b := by
      intro b
      have h1 := h (Sum.inl (Sum.inr b))
      rw [rblk] at h1
      simp only [cLat] at h1
      obtain ⟨y, hy, hye⟩ := (mem_cl_row X u b _).1 h1
      have hz : rowV X u (xs b - y) = 0 := by rw [rowV_sub, hye, sub_self]
      have := rowV_inj X u _ (inW_sub (hW b) (aaLb_inW X hy)) hz
      rw [sub_eq_zero] at this
      rw [this]; exact hy
    have hG := Gp_mem X X0 xs hup hd hX hR
    refine ⟨hX, hR, ?_⟩

    have hMu : ∀ b a : Fin D.R.rS, b < a → M b a ∈ iP D b a := by
      intro b a hba
      have h1 := h (Sum.inr (Sum.inl ⟨(b, a), hba⟩))
      rw [kblk X u hok] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = M b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht
    intro b a
    rcases lt_trichotomy b a with hba | hba | hba
    · exact hMu b a hba
    · subst hba
      have h1 := h (Sum.inr (Sum.inr b))
      rw [imblk X u hok] at h1
      obtain ⟨t, ht, htc, hte⟩ := (mem_cl_im X u b _).1 h1
      have hteq : t = xiA X0 xs M b := im_inj X htc (xiA_conj X hok b) fun v => congrFun hte v
      have hxi : xiA X0 xs M b ∈ iP D b b := by rw [← hteq]; exact ht
      have e : M b b = xiA X0 xs M b - Gp D X0 xs b b * theta D := by unfold xiA; ring
      rw [e]
      exact Submodule.sub_mem _ hxi (theta_int_mem (hG b b))
    · have e := entry_rel X hok b a
      have e2 : M b a = -Gp D X0 xs b a - star (M a b) := by rw [← e]; ring
      rw [e2]
      refine Submodule.sub_mem _ (Submodule.neg_mem _ (hG b a)) ?_
      have hab : M a b ∈ iP D b a := by rw [iP_comm]; exact hMu a b hba
      exact star_mem_iP hab
  · rintro ⟨hX, hR, hM⟩
    have hG := Gp_mem X X0 xs hup hd hX hR
    intro p
    rcases p with ((p | b) | (p | a))
    · rw [xblk]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨X0 p.1.1 p.1.2, hX _ _ p.2, rfl⟩
    · rw [rblk]
      simp only [cLat]
      exact (mem_cl_row X u b _).2 ⟨xs b, hR b, rfl⟩
    · rw [kblk X u hok]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨M p.1.1 p.1.2, hM _ _, rfl⟩
    · rw [imblk X u hok]
      refine (mem_cl_im X u a _).2 ⟨xiA X0 xs M a, ?_, xiA_conj X hok a, rfl⟩
      exact Submodule.add_mem _ (hM a a) (theta_int_mem (hG a a))

end Formalism.L2.SG.Pf.NcReal.JX.NOf
