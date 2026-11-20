import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.Columns.ChainLawTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep GlobalTheory.LastSteps

/- English proof (translation)
Introduce `X Pr R Ch w h0 hh0 g g' g'' hJ hcomm hg' hred hcong`. Take `⟨σ₀⟩ : Nonempty (X.K →+* ℂ)` from `inferInstance`. Establish `hN : R.N R.m = (R.N R.m - 1) + 1` using `N_m_succ R`. Establish `ht` using `t_pos R`. Establish `hrr` using `r_eq_sym R`.

Establish `hX'` using `rank_X'_eq R`. Establish `hint : g'' ∈ GLint X.E (R.N R.m - 1) w.1`. Introduce `x`. Establish `h1` using `(Subgroup.mem_inf.1 hJ).1 x`. Rewrite `h1` using `[lamY_zero]`. Then use the resulting hypothesis.

Establish `hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (g'' x) = (h0⁻¹).1.mulVec (redV w.1 x)`. Introduce `x hx`. Set `v : Sp X.E (R.N R.m)` to `fun l => if hl : l.1 < R.N R.m - 1 then x ⟨l.1, hl⟩ else 0`. Establish `hv : v ∈ stdAt X.E (R.N R.m) w.1`. Rewrite using `[mem_stdAt]`.

Introduce `l`. Distinguish the cases in `hl : l.1 < R.N R.m - 1`. Simplify using `only [v, dif_pos hl]`. Conclude with `mem_stdAt.1 hx _`. Simplify using `only [v, dif_neg hl]`.

Conclude with `intAt_zero`. Establish `hpv : prXpG X.E (R.N R.m) v = x`. Use function extensionality and compare the values at `i`. Establish `hi : i.1 < R.N R.m - 1` using `i.2`. Simplify using `[prXpG, LinearMap.funLeft_apply, v, hi]`.

Establish `hgx : g'' x = prXpG X.E (R.N R.m) (g v)`. Establish `h2` using `LinearMap.congr_fun hcomm v`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2`. Rewrite using `[h2, hpv]`. Establish `hc` using `hcong v hv`.

Use function extensionality and compare the values at `i`. Establish `eL : redV w.1 (g'' x) i = redV w.1 (g' v) (Br.iC hN i)`. Rewrite using `[hgx]`. Use `show redP w.1 (g v (Br.iC hN i)) = redP w.1 (g' v (Br.iC hN i))`. Establish `hz` using `mem_stdAt.1 hc (Br.iC hN i)`.

Establish `hq : ((qOf w.1 : ℕ) : X.E) ≠ 0` using `qOf_ne_zero`. Establish `e : g v (Br.iC hN i) = g' v (Br.iC hN i) + (qOf w.1 : X.E) * (((((qOf w.1 : ℕ) : X.E) ^ 1)⁻¹ • (g v - g' v)) (Br.iC hN i))`. Simplify using `only [pow_one, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Rewrite using `[mul_inv_cancel_left₀ hq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, redP_add_q hz]`. Rewrite using `[eL, hred v hv, ← map_inv, diagEmb_val, (diagMat_mulVec hN _ _).1 i]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `show redP w.1 (v (Br.iC hN j)) = redP w.1 (x j)`.

Establish `hj : (Br.iC hN j).1 < R.N R.m - 1` using `j.2`. Simplify using `only [v, dif_pos hj]`. Both sides reduce to the same expression. Establish `hM : h0⁻¹ ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R)` using `inv_mem hh0`. Establish `e1 : psi0P Ch w.1 = Ch.psi0 w`.

Unfold `psi0P`. Rewrite using `[dif_pos w.2]`. Establish `e2 : chiP Ch w.1 = chiAt Ch w`. Unfold `chiP`. Rewrite using `[dif_pos w.2]`.

Establish `hlam : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap = ((lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0⁻¹, hM⟩ : X.Kˣ) : X.K)`. Rewrite using `[e1, e2]`. Conclude with `clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h0⁻¹, hM⟩ g'' hint hredr`. Establish `hr : ((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) = lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0, hh0⟩` using `rfl`. Establish `hprod : (⟨h0⁻¹, hM⟩ * ⟨h0, hh0⟩ : ↥(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R))) = 1` using `Subtype.ext (inv_mul_cancel h0)`.

Rewrite using `[hlam, hr, ← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]`.
-/
theorem lamGBS_top_mul_lam_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  intro X Pr R Ch w h0 hh0 g g' g'' hJ hcomm hg' hred hcong
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hN : R.N R.m = (R.N R.m - 1) + 1 := N_m_succ R
  have ht := t_pos R
  have hrr := r_eq_sym R
  have hX' := rank_X'_eq R
  have hint : g'' ∈ GLint X.E (R.N R.m - 1) w.1 := by
    intro x
    have h1 := (Subgroup.mem_inf.1 hJ).1 x
    rwa [lamY_zero] at h1
  have hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (g'' x) = (h0⁻¹).1.mulVec (redV w.1 x) := by
    intro x hx
    let v : Sp X.E (R.N R.m) := fun l => if hl : l.1 < R.N R.m - 1 then x ⟨l.1, hl⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) w.1 := by
      rw [mem_stdAt]
      intro l
      by_cases hl : l.1 < R.N R.m - 1
      · simp only [v, dif_pos hl]
        exact mem_stdAt.1 hx _
      · simp only [v, dif_neg hl]
        exact intAt_zero
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      have hi : i.1 < R.N R.m - 1 := i.2
      simp [prXpG, LinearMap.funLeft_apply, v, hi]
    have hgx : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have h2 := LinearMap.congr_fun hcomm v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2
      rw [h2, hpv]
    have hc := hcong v hv
    funext i
    have eL : redV w.1 (g'' x) i = redV w.1 (g' v) (Br.iC hN i) := by
      rw [hgx]
      show redP w.1 (g v (Br.iC hN i)) = redP w.1 (g' v (Br.iC hN i))
      have hz := mem_stdAt.1 hc (Br.iC hN i)
      have hq : ((qOf w.1 : ℕ) : X.E) ≠ 0 := qOf_ne_zero
      have e : g v (Br.iC hN i) = g' v (Br.iC hN i) +
          (qOf w.1 : X.E) * (((((qOf w.1 : ℕ) : X.E) ^ 1)⁻¹ • (g v - g' v)) (Br.iC hN i)) := by
        simp only [pow_one, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_inv_cancel_left₀ hq]
        ring
      rw [e, redP_add_q hz]
    rw [eL, hred v hv, ← map_inv, diagEmb_val, (diagMat_mulVec hN _ _).1 i]
    congr 1
    funext j
    show redP w.1 (v (Br.iC hN j)) = redP w.1 (x j)
    have hj : (Br.iC hN j).1 < R.N R.m - 1 := j.2
    simp only [v, dif_pos hj]
    rfl
  have hM : h0⁻¹ ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := inv_mem hh0
  have e1 : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have e2 : chiP Ch w.1 = chiAt Ch w := by
    unfold chiP
    rw [dif_pos w.2]
  have hlam : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap =
      ((lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0⁻¹, hM⟩ : X.Kˣ) : X.K) := by
    rw [e1, e2]
    exact clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h0⁻¹, hM⟩ g'' hint hredr
  have hr : ((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) =
      lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0, hh0⟩ := rfl
  have hprod : (⟨h0⁻¹, hM⟩ * ⟨h0, hh0⟩ : ↥(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R))) = 1 :=
    Subtype.ext (inv_mul_cancel h0)
  rw [hlam, hr, ← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]

end GlobalTheory.Mem.Col2.AdT
