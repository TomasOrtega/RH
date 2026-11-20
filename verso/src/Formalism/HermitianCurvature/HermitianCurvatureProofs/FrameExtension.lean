import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameExtension

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Conclude with `⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩`.
-/
theorem frame_weaken {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩

/- English proof (translation)
Use `t.isLt` as an intermediate fact. Use `u.isLt` as an intermediate fact. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private theorem hpk_apply_comm (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem star_hpk_apply (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[hpk_apply_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_hpk_eq_star_herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_apply_comm]
  ring

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simpa using he`. Consider the case `cast i => simpa using h1 i`.

Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simpa using hee`. Consider the case `cast j`.

Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`. Rewrite using `[if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]`. Consider the case `cast i`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`. Rewrite using `[if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]`. Consider the case `cast j`. Simplify using `only [Fin.snoc_castSucc]`. Rewrite using `[h2 i j]`.

Simplify using `[Fin.castSucc_inj]`. Rewrite `hv` using `[List.mem_singleton]`. Substitute `hv` using the available equality. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simpa using hez`.

Consider the case `cast i => simpa using h3 i v (by simp)`.
-/
theorem frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · induction a using Fin.lastCases with
    | last => simpa using he
    | cast i => simpa using h1 i
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa using hee
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [h2 i j]
        simp [Fin.castSucc_inj]
  · rw [List.mem_singleton] at hv
    subst hv
    induction a using Fin.lastCases with
    | last => simpa using hez
    | cast i => simpa using h3 i v (by simp)

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `[subA, EB, unitB, Fin.snoc_castSucc]`.
-/
theorem subA_EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]`. Simplify using the standard rewrite rules.
-/
theorem prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]
    simp

end Formalism.FourierDecayAlt.P.FrameExtension

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee`. Take `⟨hnt, hrep, hcont, -, hirr, hcap⟩` from `hty`. Establish `hR : IsRepW (n + 1) r z π` using `⟨hrep, hcont⟩`. Take `⟨Bs₀, hB₀⟩` from `hFE n r z e hz hT he hez hee`. Establish `hB₁` using `FrameExtension.frame_snoc hB₀ he hez hee`.

Use `set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ := Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁`. Establish `hsub : subA (EB π Bs₁) = EB π Bs₀` using `FrameExtension.subA_EB π Bs₀ e`. Take `⟨hgl, hq⟩` from `hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁`. Establish `hH : Hyp (EB π Bs₁) β L`. Use `⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩` and prove the remaining obligations.

Introduce `w v`. Rewrite using `[← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]`. Use `congr 1`. Unfold `cpol shf`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hu j]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hint, hS⟩` from `hBA Wp n (EB π Bs₁) β L hH`. Rewrite `hint`, `hS` using `[hsub]`. Use `⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)`. Introduce `Bs hBs M w v hv`. Rewrite using `[(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v, hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]`. Conclude with `Qr.mem_CapSp.1 hv w`.
-/
theorem qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w

end Formalism.FourierDecayAlt.P
