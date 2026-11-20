import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopSrc

open GlobalTheory.DatumLaw

/- English proof (translation)
Substitute `hc` using the available equality. Establish `e : ∀ x : Sp E n, Loc.inX E n 0 x = x` using `fun x => by`. Use function extensionality and compare the values at `l`. Rewrite using `[CongLevel.inX_apply]`. Conclude with `dif_pos l.2`.

Establish `hr : r = κ` using `LinearEquiv.ext fun x => by`. Use `h x` as an intermediate fact. Rewrite `this` using `[e, e]`. Then use the resulting hypothesis. Substitute `hr` using the available equality. Use `⟨rfl, rfl, ?_⟩` and prove the remaining obligations.

Unfold `Loc.n1Arg`. Simplify using the standard rewrite rules.
-/
theorem of_zero {E : Type} [Field E] {n c : ℕ} (hc : c = 0) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : Sp E n ≃ₗ[E] Sp E n)
    (h : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (κ x)) :
    κ.toLinearMap ∘ₗ LinearMap.funLeft E E (Fin.castAdd c) = LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ r.toLinearMap ∧
      LinearEquiv.det κ = LinearEquiv.det r ∧ Loc.n1Arg r = 0 := by
  subst hc
  have e : ∀ x : Sp E n, Loc.inX E n 0 x = x := fun x => by
    funext l
    rw [CongLevel.inX_apply]
    exact dif_pos l.2
  have hr : r = κ := LinearEquiv.ext fun x => by
    have := h x
    rwa [e, e] at this
  subst hr
  refine ⟨rfl, rfl, ?_⟩
  unfold Loc.n1Arg
  simp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

/- English proof (translation)
Take `⟨a1, a2, a3, a4⟩` from `ranks R (j := m2 + 1) (by omega)`. Establish `b1` using `rank_X'_eq R`. Establish `b2 : R.r + (m2 + 1) * R.t ≤ R.N R.m - 1 + 0`. Rewrite using `[b1, add_zero]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _`.

Establish `hb : R.r ≤ R.N R.m - 1 + 0` using `by omega`. Unfold `rhoS`. Unfold `Jat at hg`. Unfold `PhiTop lamRow`. Generalize the expression as in `R.N R.m - 1 = n at *`.

Establish `e1` using `fun ψ χ => hm ▸ phiGS_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (rS := R.rS) (r := R.r) (t := R.t) (i := m2 + 1) (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)`. Establish `e2` using `fun ψ χ => hm ▸ phiG_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (r := R.r) (t := R.t) (i := m2 + 1) (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)`. Use `split_ifs at hg ⊢`. Rewrite using `[e1]`. Conclude with `phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x`.

Rewrite using `[e2, LocE.lamGB, lamGv_eq]`. Conclude with `phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x`. Conclude with `phiQ_source _ (by omega) a2 a3 hb hg x`.
-/
theorem phiTop_source (sharp : Bool) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) {g : AutY X R (m2 + 1)}
    (hg : g ∈ Jat (Pr := Pr) sharp (m2 + 1) P.1) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P.1 (x ∘ₗ g.toLinearMap) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp (m2 + 1) P.1 g.toLinearMap * PhiTop Ch mu sharp m2 P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := m2 + 1) (by omega)
  have b1 := rank_X'_eq R
  have b2 : R.r + (m2 + 1) * R.t ≤ R.N R.m - 1 + 0 := by
    rw [b1, add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hb : R.r ≤ R.N R.m - 1 + 0 := by omega
  unfold rhoS
  unfold Jat at hg
  unfold PhiTop lamRow
  generalize R.N R.m - 1 = n at *
  have e1 := fun ψ χ => hm ▸ phiGS_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (rS := R.rS) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  have e2 := fun ψ χ => hm ▸ phiG_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  split_ifs at hg ⊢
  · rw [e1]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [e2, LocE.lamGB, lamGv_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_source _ (by omega) a2 a3 hb hg x

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hX hPr hL b P κ c hG hQ x`. Establish `hc : cOf R (m2 + 1) = 0`. Use `hL.hm` as an intermediate fact. Unfold `cOf`. Use linear arithmetic over natural numbers and integers.

Establish `key : ∃ r ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P), (∀ x, r (Loc.inX X.E _ (cOf R (m2 + 1)) x) = Loc.inX X.E _ (cOf R (m2 + 1)) (κ.1 x)) ∧ (c : X.K) = chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) r := by`. Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Take `⟨h, rfl⟩` from `hG hP`. Take `⟨g, hg, hred⟩` from `(hL.grpG (m2 + 1) b ⟨P.1, hP⟩ _).1 h`. Establish `hgi : g ∈ GLint X.E (R.N (m2 + 1)) P.1` using `hL.int (m2 + 1) b P hg`.

Establish `e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ` using `redGL_eq _ hred`. Establish `h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ) = 1`. Rewrite using `[map_mul, map_inv, e, inv_mul_cancel]`. Establish `h2` using `CongLevel.cong_mem_prCat X Pr R cst.sharp (m2 + 1) P.1 hP (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG (m2 + 1) b P hP) _ ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ).2 fun x hx => by`. Rewrite using `[redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]`.

Establish `h3 : κ.1 ∈ prCat (Pr` using `Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := by`. Use `mul_mem hg h2` as an intermediate fact. Rewrite `this` using `[Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Then use the resulting hypothesis. Take `⟨r, hr, hrx⟩` from `h3`. Conclude with `⟨r, hr, hrx, hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩`.

Establish `hP'` using `(@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP`. Take `⟨h, rfl⟩` from `hQ hP' hP`. Establish `h3` using `h`. Rewrite `h3` using `[hL.grpQ, Subgroup.mem_subgroupOf]`. Take `⟨r, hr, hrx⟩` from `h3`.

Conclude with `⟨r, hr, hrx, hL.chrQ (m2 + 1) b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩`. Take `⟨r, hr, hrx, hcr⟩` from `key`. Rewrite `hr`, `hcr` using `[hL.last_h]`. Establish `hJ : r ∈ Jat (Pr` using `Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2`. Take `⟨e1, e2, e3⟩` from `of_zero hc r κ.1 hrx`.

Unfold `chiInv at hcr`. Rewrite `hcr` using `[e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one]`. Rewrite using `[e1, e2, hcr, ← LinearMap.comp_assoc]`. Conclude with `phiTop_source Ch sel mu cst.sharp hL.hm P hJ _`.
-/
theorem phiTop_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N (m2 + 1)) P.1) (c : X.Kˣ), (∀ hP : P.1 ∈ Pr.vGs, ∃ h : redGL _ P.1 κ ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H, c = (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨_, h⟩) → (∀ hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K), P.1 ∉ Pr.vGs → ∃ h : κ ∈ (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).H, c = (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).lam ⟨κ, h⟩) → ∀ x : HomE X.E (R.N (m2 + 1)) ((R.N R.m - 1) + 0), PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = (c : X.K) * PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL b P κ c hG hQ x
  have hc : cOf R (m2 + 1) = 0 := by
    have := hL.hm
    unfold cOf
    omega
  have key : ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P),
      (∀ x, r (Loc.inX X.E _ (cOf R (m2 + 1)) x) = Loc.inX X.E _ (cOf R (m2 + 1)) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) r := by
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨h, rfl⟩ := hG hP
      obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ _).1 h
      have hgi : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hg
      have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
      have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ) = 1 := by
        rw [map_mul, map_inv, e, inv_mul_cancel]
      have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp (m2 + 1) P.1 hP
        (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG (m2 + 1) b P hP)
        _ ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ).2 fun x hx => by
          rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
      have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := by
        have := mul_mem hg h2
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
    · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
      obtain ⟨h, rfl⟩ := hQ hP' hP
      have h3 := h
      rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrQ (m2 + 1) b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩
  obtain ⟨r, hr, hrx, hcr⟩ := key
  rw [hL.last_h] at hr hcr
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2
  obtain ⟨e1, e2, e3⟩ := of_zero hc r κ.1 hrx
  unfold chiInv at hcr
  rw [e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one] at hcr
  rw [e1, e2, hcr, ← LinearMap.comp_assoc]
  exact phiTop_source Ch sel mu cst.sharp hL.hm P hJ _

end GlobalTheory.TopSrc

end
