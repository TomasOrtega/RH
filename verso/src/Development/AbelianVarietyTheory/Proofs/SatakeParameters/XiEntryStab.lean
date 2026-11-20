import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
open Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.MatLaw

noncomputable section

namespace GlobalTheory.FiLaw

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u i hi al be p p' a ha x`. Establish `hd` using `(tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2`. Take `⟨κ, c, hκ, hc, ec⟩` from `exists_pass hd (1 : FrmG (L.levG i al) (L.levQ i al)) p`. Take `⟨κ', c', hκ', hc', ec'⟩` from `exists_pass hd a p'`. Establish `key` using `xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)`.

Establish `e1 : x ∘ₗ ((1 : FrmG (L.levG i al) (L.levQ i al)).1.1.symm.toLinearMap) = x` using `LinearMap.ext fun v => rfl`. Rewrite `key` using `[one_smul, ha, e1, ec, ec']`. Simplify using `only [Prod.snd_one, Prod.fst_one, map_one, mul_one, inv_one] at key`. Rewrite using `[← key]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations. Establish `h1 : ((κ P)⁻¹).1 = 1`. Establish `h` using `hκ P`. Rewrite `h` using `[one_smul]`. Simplify using `using h`.

Establish `h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det a.1.1`. Establish `h` using `congrArg LinearEquiv.det (hκ' P)`. Rewrite `h` using `[ha, map_mul, map_mul, Subgroup.coe_inv, map_inv]`. Rewrite `h` using `[mul_left_comm]`. Establish `h'` using `mul_left_cancel (h.symm.trans (mul_one _).symm)`.

Conclude with `(mul_inv_eq_one.1 h').symm`. Rewrite using `[Pi.inv_apply, Pi.inv_apply, h1, map_one, Units.val_one, rhoT_inv, ← muAt_det, h2]`. Unfold `rhoS`. Rewrite using `[GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one, one_mul]`.
-/
theorem xiEntry_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (a : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)), a • p' = p' → ∀ x, XiEntry Ch sel mu cst L i al be p p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (i + 1) be).chr a.2.1 * (L.levQ (i + 1) be).chr a.2.2 : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u i hi al be p p' a ha x
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd (1 : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd a p'
  have key := xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  have e1 : x ∘ₗ ((1 : FrmG (L.levG i al) (L.levQ i al)).1.1.symm.toLinearMap) = x := LinearMap.ext fun v => rfl
  rw [one_smul, ha, e1, ec, ec'] at key
  simp only [Prod.snd_one, Prod.fst_one, map_one, mul_one, inv_one] at key
  rw [← key]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have h1 : ((κ P)⁻¹).1 = 1 := by
    have h := hκ P
    rw [one_smul] at h
    simpa using h
  have h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det a.1.1 := by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [ha, map_mul, map_mul, Subgroup.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    have h' := mul_left_cancel (h.symm.trans (mul_one _).symm)
    exact (mul_inv_eq_one.1 h').symm
  rw [Pi.inv_apply, Pi.inv_apply, h1, map_one, Units.val_one, rhoT_inv, ← muAt_det, h2]
  unfold rhoS
  rw [GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one, one_mul]

end GlobalTheory.FiLaw
