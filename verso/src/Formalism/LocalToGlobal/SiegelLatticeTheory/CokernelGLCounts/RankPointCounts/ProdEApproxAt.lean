import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZhatOMMono
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EntInSandwich
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def ellP (p : PlF D) : (D.s.atP p).Fp := ((Loc.resChar p : ℕ) : (D.s.atP p).Fp)

/- English proof (translation)
Use `(D.s.atP p).char0` as an intermediate fact. Establish `hp` using `(D.s.atP p).ellPrime.out`. Conclude with `Nat.cast_ne_zero.2 hp.ne_zero`.
-/
theorem ellP_ne (p : PlF D) : ellP p ≠ 0 := by
  have := (D.s.atP p).char0
  have hp := (D.s.atP p).ellPrime.out
  exact Nat.cast_ne_zero.2 hp.ne_zero

/- English proof (translation)
The claim follows from `natCast_mem _ _`.
-/
theorem ellP_mem (p : PlF D) : ellP p ∈ 𝒪[(D.s.atP p).Fp] := natCast_mem _ _

variable {M δ}

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `mem_latS.1 hx`. Take `⟨-, -, -, hO, -, hsp⟩` from `hA`. Use `show _ ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R`. Break down `hM : (M p).split with _ | g` into its components or cases. Use `show _ ∈ (M p).L.O`.

Rewrite using `[hO]`. Conclude with `(D.s.atP p).O.mul_mem (alg_mem_O (ellP_mem p)) hy`. Break down `hR : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[hM, hR] at hsp`. Establish `hsp' : g.e = sg.e ∧ g.q = sg.q` using `by simpa [hM, hR] using hsp`.

Rewrite using `[Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]`. Establish `hy'` using `(Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg y).1 hy`. Establish `hq : ((g.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ellP p` using `by rw [hsp'.2]; exact sg.q_eq`. Establish `he : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ellP p) * y) = (ellP p * (sg.e y).1, ellP p * (sg.e y).2)`. Rewrite using `[map_mul, AlgEquiv.commutes, hsp'.1]`.

Both sides reduce to the same expression. Rewrite using `[he]`. Use `⟨Subring.mul_mem _ (ellP_mem p) hy'.1, Subring.mul_mem _ (ellP_mem p) hy'.2, (sg.e y).1 - (sg.e y).2, Subring.sub_mem _ hy'.1 hy'.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latS_R {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ latS (D.s.atP p) (ellP p)) :
    x ∈ (M p).R := by
  obtain ⟨y, hy, rfl⟩ := mem_latS.1 hx
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  show _ ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R
  rcases hM : (M p).split with _ | g
  · show _ ∈ (M p).L.O
    rw [hO]
    exact (D.s.atP p).O.mul_mem (alg_mem_O (ellP_mem p)) hy
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]
      have hy' := (Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg y).1 hy
      have hq : ((g.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ellP p := by rw [hsp'.2]; exact sg.q_eq
      have he : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ellP p) * y) =
          (ellP p * (sg.e y).1, ellP p * (sg.e y).2) := by
        rw [map_mul, AlgEquiv.commutes, hsp'.1]; rfl
      rw [he]
      refine ⟨Subring.mul_mem _ (ellP_mem p) hy'.1, Subring.mul_mem _ (ellP_mem p) hy'.2,
        (sg.e y).1 - (sg.e y).2, Subring.sub_mem _ hy'.1 hy'.2, ?_⟩
      rw [hq]; ring

variable (M δ)

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Formalism.L2.SG.Pf.ptMat_fσ]`. Both sides reduce to the same expression.
-/
theorem ptMat_mono : ptMat w = mono (Formalism.L2.SG.Pf.fσ w) (fun a => Formalism.L2.SG.Pf.pv w.1 a) := by
  ext a b
  rw [Formalism.L2.SG.Pf.ptMat_fσ]
  rfl

/- English proof (translation)
Use `set σ := Formalism.L2.SG.Pf.fσ w`. Establish `hσ : ∀ a, σ (σ a) = a` using `Formalism.L2.SG.Pf.fσ_fσ w`. Take `⟨ν, hν, κ, hY⟩` from `zzp_mono δ M u u' hA hσ (fun a => (-1) ^ (D.R.rS - (σ a).val) * Formalism.L2.SG.Pf.pv w.1 a) (fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Formalism.L2.SG.Pf.pv_ne' w a))`. Establish `hY0 : ProdE.Y0 M δ u u' w p = mono σ ν - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ`. Rewrite using `[← hY]`.

Unfold `ProdE.Y0`. Rewrite using `[ptMat_mono, zhatOM_mono]`. Use `⟨mono σ ν, mono σ (fun a => Ring.inverse (ν (σ a))), ?_, ?_, ⟨ν, hν, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[mono_mul]`.

Simplify using `only [mono, Matrix.of_apply, Matrix.one_apply, hσ]`. Use `split_ifs with h1 h2 h2`. Conclude with `Ring.mul_inverse_cancel _ (hν i)`. Conclude with `absurd h1.symm h2`. Conclude with `absurd h2.symm h1`.

Simplify using the standard rewrite rules. Use extensionality with `i j`. Rewrite using `[mul_mono hσ]`. Simplify using `only [mono, Matrix.of_apply, hσ, Matrix.one_apply]`. Distinguish the cases in `h : σ j = σ i`.

Establish `hij : i = j` using `by rw [← hσ i, ← h, hσ]`. Substitute `hij` using the available equality. Simplify using `only [if_true]`. Conclude with `Ring.inverse_mul_cancel _ (hν _)`. Establish `hij : i ≠ j` using `fun e => h (by rw [e])`.

Rewrite using `[if_neg h, if_neg hij, zero_mul]`. Introduce `l ρ hl hρ h`. Rewrite `h` using `[hY0]`. Conclude with `fix_of_fix hl hρ κ h`.
-/
theorem exists_unit_monomial_stable_of_Y0 {p : PlF D} (hA : Agree δ M p) :
    ∃ N Ni : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, N * Ni = 1 ∧ Ni * N = 1 ∧
      (∃ ν : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν a)) ∧ N = mono (Formalism.L2.SG.Pf.fσ w) ν) ∧
      ∀ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, IsLoUni l → IsUpUni ρ →
        l * ProdE.Y0 M δ u u' w p * ρ = ProdE.Y0 M δ u u' w p → l * N * ρ = N := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  obtain ⟨ν, hν, κ, hY⟩ := zzp_mono δ M u u' hA hσ (fun a => (-1) ^ (D.R.rS - (σ a).val) * Formalism.L2.SG.Pf.pv w.1 a)
    (fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Formalism.L2.SG.Pf.pv_ne' w a))
  have hY0 : ProdE.Y0 M δ u u' w p = mono σ ν - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
    rw [← hY]
    unfold ProdE.Y0
    rw [ptMat_mono, zhatOM_mono]
  refine ⟨mono σ ν, mono σ (fun a => Ring.inverse (ν (σ a))), ?_, ?_, ⟨ν, hν, rfl⟩, ?_⟩
  · ext i j
    rw [mono_mul]
    simp only [mono, Matrix.of_apply, Matrix.one_apply, hσ]
    split_ifs with h1 h2 h2
    · exact Ring.mul_inverse_cancel _ (hν i)
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  · ext i j
    rw [mul_mono hσ]
    simp only [mono, Matrix.of_apply, hσ, Matrix.one_apply]
    by_cases h : σ j = σ i
    · have hij : i = j := by rw [← hσ i, ← h, hσ]
      subst hij
      simp only [if_true]
      exact Ring.inverse_mul_cancel _ (hν _)
    · have hij : i ≠ j := fun e => h (by rw [e])
      rw [if_neg h, if_neg hij, zero_mul]
  · intro l ρ hl hρ h
    rw [hY0] at h
    exact fix_of_fix hl hρ κ h

end At

end Formalism.L2.SG.Pf.ProdEApprox
