import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.FrobSame

open Polynomial

/- English proof (translation)
Establish `hall : ∀ k, s.esymm k = t.esymm k`. Introduce `k`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using `[Multiset.esymm]`. Distinguish the cases in `hkr : k ≤ r`.

Conclude with `h k hk hkr`. Rewrite using `[Multiset.esymm, Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega), Multiset.powersetCard_eq_empty _ (by omega)]`. Establish `hp : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod`. Rewrite using `[Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]`. Simplify using `only [hall]`.

Rewrite using `[← Polynomial.roots_multiset_prod_X_sub_C s, ← Polynomial.roots_multiset_prod_X_sub_C t, hp]`.
-/
theorem multiset_eq_of_esymm {s t : Multiset ℂ} {r : ℕ} (hs : Multiset.card s = r) (ht : Multiset.card t = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → s.esymm k = t.esymm k) : s = t := by
  have hall : ∀ k, s.esymm k = t.esymm k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · by_cases hkr : k ≤ r
      · exact h k hk hkr
      · rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega),
          Multiset.powersetCard_eq_empty _ (by omega)]
  have hp : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    simp only [hall]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, ← Polynomial.roots_multiset_prod_X_sub_C t, hp]

end GlobalTheory.FrobSame

namespace GlobalTheory.FrobSame

/- English proof (translation)
Introduce `D cf Rw Sb eig hE hC j hj1 hjm σ σ' hσ hgσ hσ' hgσ' P hP hPS heq`. Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hi : i < D.R.m` using `by omega`. Take `⟨hu, he⟩` from `hE ⟨i, hi⟩ σ hσ hgσ P hP hPS`. Take `⟨hu', he'⟩` from `hE ⟨i, hi⟩ σ' hσ' hgσ' P hP hPS`.

Take `⟨π, hπ⟩` from `hC (i + 1) hj1 hjm σ hσ hgσ`. Take `⟨π', hπ'⟩` from `hC (i + 1) hj1 hjm σ' hσ' hgσ'`. Establish `hcard : (D.naut.frobEig (Rw.locR σ P)).card = D.R.r`. Rewrite using `[D.naut.frobEig_card _ hu, ← hπ.2.2.1 P hP, D.naut.locG_dim]`. Establish `hcard' : (D.naut.frobEig (Rw.locR σ' P)).card = D.R.r`.

Rewrite using `[D.naut.frobEig_card _ hu', ← hπ'.2.2.1 P hP, D.naut.locG_dim]`. Establish `hq0 : ((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ≠ 0`. Establish `e : Formalism.ConjugateSelfDual.normV P = Ideal.absNorm P.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `GlobalTheory.GalChar.absNorm_ne_zero P` after adjusting the coercions. Set `f : ℂ → ℂ` to `fun a => a⁻¹ * (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹`. Establish `hfi : Function.Injective f`. Introduce `a b hab`.

Establish `hc : (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ ≠ 0` using `mul_ne_zero (inv_ne_zero (Units.ne_zero _)) (inv_ne_zero (pow_ne_zero _ hq0))`. Simplify using `only [f, mul_assoc] at hab`. Conclude with `inv_injective (mul_right_cancel₀ hc hab)`. Establish `hmap : (D.naut.frobEig (Rw.locR σ' P)).map f = (D.naut.frobEig (Rw.locR σ P)).map f`. Use `multiset_eq_of_esymm (r := D.R.r) (by rw [Multiset.card_map, hcard']) (by rw [Multiset.card_map, hcard]) fun k hk1 hkr => ?_` and prove the remaining obligations.

Establish `e1` using `he k hk1 hkr`. Establish `e2` using `he' k hk1 hkr`. Rewrite `e2` using `[heq k hk1 hkr, e1]`. Conclude with `(mul_left_cancel₀ (pow_ne_zero (k * (D.R.r - k) / 2) hq0) e2).symm`. Conclude with `Multiset.map_injective hfi hmap`.
-/
theorem frobEig_eq_of_eig_eq : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  intro D cf Rw Sb eig hE hC j hj1 hjm σ σ' hσ hgσ hσ' hgσ' P hP hPS heq
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  obtain ⟨hu, he⟩ := hE ⟨i, hi⟩ σ hσ hgσ P hP hPS
  obtain ⟨hu', he'⟩ := hE ⟨i, hi⟩ σ' hσ' hgσ' P hP hPS
  obtain ⟨π, hπ⟩ := hC (i + 1) hj1 hjm σ hσ hgσ
  obtain ⟨π', hπ'⟩ := hC (i + 1) hj1 hjm σ' hσ' hgσ'
  have hcard : (D.naut.frobEig (Rw.locR σ P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu, ← hπ.2.2.1 P hP, D.naut.locG_dim]
  have hcard' : (D.naut.frobEig (Rw.locR σ' P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu', ← hπ'.2.2.1 P hP, D.naut.locG_dim]
  have hq0 : ((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ≠ 0 := by
    have e : Formalism.ConjugateSelfDual.normV P = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [e]; exact_mod_cast GlobalTheory.GalChar.absNorm_ne_zero P
  let f : ℂ → ℂ := fun a => a⁻¹ * (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹
  have hfi : Function.Injective f := by
    intro a b hab
    have hc : (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero (Units.ne_zero _)) (inv_ne_zero (pow_ne_zero _ hq0))
    simp only [f, mul_assoc] at hab
    exact inv_injective (mul_right_cancel₀ hc hab)
  have hmap : (D.naut.frobEig (Rw.locR σ' P)).map f = (D.naut.frobEig (Rw.locR σ P)).map f := by
    refine multiset_eq_of_esymm (r := D.R.r) (by rw [Multiset.card_map, hcard'])
      (by rw [Multiset.card_map, hcard]) fun k hk1 hkr => ?_
    have e1 := he k hk1 hkr
    have e2 := he' k hk1 hkr
    rw [heq k hk1 hkr, e1] at e2
    exact (mul_left_cancel₀ (pow_ne_zero (k * (D.R.r - k) / 2) hq0) e2).symm
  exact Multiset.map_injective hfi hmap

end GlobalTheory.FrobSame
