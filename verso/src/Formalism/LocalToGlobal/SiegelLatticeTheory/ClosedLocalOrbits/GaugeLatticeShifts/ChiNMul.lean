import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.ChiNMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Rewrite using `[X.g_eq]`. Conclude with `Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`.
-/
theorem gB_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[hA_symm]`. Use `(X.gramIntegral b a).2.2` as an intermediate fact. Rewrite `this` using `[if_neg (Ne.symm hab), sub_zero]`. Conclude with `Z_sig X.B.I X.B.g this`.
-/
theorem hfe : ∀ a b : Fin D.R.rS, a ≠ b → ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.e0 b)) := by
  intro a b hab
  rw [hA_symm]
  have := (X.gramIntegral b a).2.2
  rw [if_neg (Ne.symm hab), sub_zero] at this
  exact Z_sig X.B.I X.B.g this

/- English proof (translation)
Introduce `a` and use `((X.formsAtZero).2 a).2`.
-/
theorem hfz : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) X.z0) := fun a => ((X.formsAtZero).2 a).2

/- English proof (translation)
The claim follows from `pres1 X.B.I hx X.B.g _ _ (by rintro _ ⟨b, hb, rfl⟩ have hb' : b.1 < a.1 + 1 := hb exact Mo_mono X.B.I (Set.image_mono (lt_sub (by omega))) (hc1 b)) (mL_Mo X.B.I)`.
-/
theorem e_step' {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    (hc1 : ∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}))
    (a : Fin D.R.rS) : ∀ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}),
      (X.B.I.fmat x - 1) *ᵥ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) :=
  pres1 X.B.I hx X.B.g _ _ (by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.1 < a.1 + 1 := hb
    exact Mo_mono X.B.I (Set.image_mono (lt_sub (by omega))) (hc1 b)) (mL_Mo X.B.I)

/- English proof (translation)
Unfold `nxt`. Use `split_ifs with h`. Conclude with `hcy.1 ⟨a.1 + 1, h⟩`. Use `Mo_mono X.B.I ?_ hcy.2` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Use `b.2` as an intermediate fact. Conclude with `⟨b, show b.1 < a.1 + 1 by omega, rfl⟩`.
-/
theorem nxt_cong' {y : X.B.I.Gf} (hcy : Formalism.L2.SG.NormCut.NCong X y) (a : Fin D.R.rS) :
    (X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}) := by
  unfold nxt
  split_ifs with h
  · exact hcy.1 ⟨a.1 + 1, h⟩
  · refine Mo_mono X.B.I ?_ hcy.2
    rintro _ ⟨b, rfl⟩
    have := b.2
    exact ⟨b, show b.1 < a.1 + 1 by omega, rfl⟩

/- English proof (translation)
Unfold `chiN`. Use `psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_` and prove the remaining obligations. Establish `hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf` using `fun a => (X.vectorsInLattice.1 a).2`. Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Z_sum X.B.I X.B.g _ _ fun a _ => ?_` and prove the remaining obligations.

Conclude with `term_Z X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a) (Me_Q X.B.I X.B.g X.e0 X.f0 hf0 (hfe X) a (e_step' X hx hcx.1 a _ (nxt_cong' X hcy a)))`.
-/
theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hcx : Formalism.L2.SG.NormCut.NCong X x)
    (hcy : Formalism.L2.SG.NormCut.NCong X y) : chiN X (x * y) = chiN X x * chiN X y := by
  unfold chiN
  refine psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  exact term_Z X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a)
    (Me_Q X.B.I X.B.g X.e0 X.f0 hf0 (hfe X) a (e_step' X hx hcx.1 a _ (nxt_cong' X hcy a)))

/- English proof (translation)
Unfold `chiN`. Use `psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_` and prove the remaining obligations. Simplify using `only [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]`. Conclude with `Z_sum X.B.I X.B.g _ _ fun a _ => nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a`.
-/
theorem chiN_one : chiN X 1 = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  simp only [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  exact Z_sum X.B.I X.B.g _ _ fun a _ => nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a

/- English proof (translation)
Apply the tactic sequence `refine ⟨fun a => ?_, ?_⟩ <;>`. Rewrite using `[show X.B.I.fmat 1 = 1 from rfl, sub_self, Matrix.zero_mulVec]`. Conclude with `zero_mem _`.
-/
theorem ncong_one : Formalism.L2.SG.NormCut.NCong X 1 := by
  refine ⟨fun a => ?_, ?_⟩ <;>
  · rw [show X.B.I.fmat 1 = 1 from rfl, sub_self, Matrix.zero_mulVec]; exact zero_mem _

/- English proof (translation)
Establish `h` using `chiN_mul X hx hcx (Formalism.L2.SG.NormCut.ncong_inv X hx hcx)`. Rewrite `h` using `[mul_inv_cancel, chiN_one]`. Conclude with `eq_inv_of_mul_eq_one_right h.symm`.
-/
theorem chiN_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hcx : Formalism.L2.SG.NormCut.NCong X x) :
    chiN X x⁻¹ = (chiN X x)⁻¹ := by
  have h := chiN_mul X hx hcx (Formalism.L2.SG.NormCut.ncong_inv X hx hcx)
  rw [mul_inv_cancel, chiN_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨hk.1, hk.2.1, hk.2.2.1⟩`.
-/
theorem level_subgroup_norm_congruence {x : X.B.I.Gf} (hk : x ∈ X.K2) : x ∈ X.B.I.Kset ∧ Formalism.L2.SG.NormCut.NCong X x :=
  ⟨hk.1, hk.2.1, hk.2.2.1⟩

end Formalism.L2.SG.Pf.ChiNMul

namespace Formalism.L2.SG.NormCut

section ChiNOut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

/- English proof (translation)
Establish `s` using `colStab X w h h' hk`. Unfold `chiN`. Use `psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X) ?_` and prove the remaining obligations. Use `Z_sum X.B.I X.B.g _ _ fun a _ => ?_` and prove the remaining obligations. Establish `hf0 : X.f0 a ∈ X.B.I.Lf` using `(X.vectorsInLattice.1 a).2`.

Establish `hd : X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a - nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g`. Unfold `nxt`. Use `split_ifs`. Conclude with `s.1 _`. Conclude with `s.2`.

Rewrite using `[show X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a = nxt X.e0 X.z0 a + (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a - nxt X.e0 X.z0 a) by abel, hA_add_right]`. Conclude with `Z_add X.B.I X.B.g (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNMul.hfe X) (Formalism.L2.SG.Pf.ChiNMul.hfz X) a) (mL_Qs X.B.I X.B.g hf0 hd)`.
-/
theorem chiN_colDiff (w : D.what₂.Word) (h h' : Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    chiN X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) = 1 := by
  have s := colStab X w h h' hk
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have hd : X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    unfold nxt; split_ifs
    · exact s.1 _
    · exact s.2
  rw [show X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a =
    nxt X.e0 X.z0 a + (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a) by abel, hA_add_right]
  exact Z_add X.B.I X.B.g (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNMul.hfe X)
    (Formalism.L2.SG.Pf.ChiNMul.hfz X) a) (mL_Qs X.B.I X.B.g hf0 hd)

/- English proof (translation)
Introduce `t ρ ρ' hρ hρ' _`. Establish `hb : cs.lamOf (cs.base t.lam) = t.lam` using `cs.base_lam _ t.mem`. Establish `hb' : cs'.lamOf (cs'.base t.lam') = t.lam'` using `cs'.base_lam _ t.mem'`. Establish `k1K` using `Formalism.L2.SG.Pf.colLatK X cs ρ (cs.base t.lam) (hρ.trans hb.symm)`. Establish `k2K` using `Formalism.L2.SG.Pf.colLatK X cs' (cs'.base t.lam') ρ' (hb'.trans hρ'.symm)`.

Establish `κK` using `Formalism.L2.SG.Pf.termK X cs cs' (F0 := F0) (F0' := F0') t`. Establish `κN` using `adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X) t`. Establish `k1N` using `ncong_colDiff u _ _ k1K`. Establish `k2N` using `ncong_colDiff u' _ _ k2K`. Establish `hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt = (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) * kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt * (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X …`.

Unfold `kOf`. Use `group`. Rewrite using `[hκ, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I k1K κK) (ncong_mul X k1K k1N κN) k2N, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X k1K k1N κN, chiN_colDiff u _ _ k1K, chiN_colDiff u' _ _ k2K, one_mul, mul_one]`.
-/
theorem chiNIndep_of_frameTie (hTF : FrameTie X u u' F0 F0') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' _
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hb' : cs'.lamOf (cs'.base t.lam') = t.lam' := cs'.base_lam _ t.mem'
  have k1K := Formalism.L2.SG.Pf.colLatK X cs ρ (cs.base t.lam) (hρ.trans hb.symm)
  have k2K := Formalism.L2.SG.Pf.colLatK X cs' (cs'.base t.lam') ρ' (hb'.trans hρ'.symm)
  have κK := Formalism.L2.SG.Pf.termK X cs cs' (F0 := F0) (F0' := F0') t
  have κN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X) t
  have k1N := ncong_colDiff u _ _ k1K
  have k2N := ncong_colDiff u' _ _ k2K
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    unfold kOf; group
  rw [hκ, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I k1K κK) (ncong_mul X k1K k1N κN) k2N,
    Formalism.L2.SG.Pf.ChiNMul.chiN_mul X k1K k1N κN, chiN_colDiff u _ _ k1K, chiN_colDiff u' _ _ k2K, one_mul,
    mul_one]

end ChiNOut

end Formalism.L2.SG.NormCut
