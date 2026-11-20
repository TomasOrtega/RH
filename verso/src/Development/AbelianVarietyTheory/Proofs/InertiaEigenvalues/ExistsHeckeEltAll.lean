import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceOfValuationRing
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HkSupComm

section Keep

open Formalism.L2.NTheta GlobalTheory.HeckeParts GlobalTheory.HeckeSupSt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

/- English proof (translation)
Take `⟨c, hβ⟩` from `hL.βW i`. Establish `hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Rewrite using `[one_pow, Nat.cast_one]`. Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`. Establish `hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P`.

Introduce `PP hPP`. Establish `hPP' : PP ∈ R.Pg` using `hPP.elim id fun h => absurd h (Finset.notMem_empty _)`. Establish `hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))` using `by rw [hA]; exact hPP'`. Use `⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.conjIdeal_asIdeal]`.

Use `PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_` and prove the remaining obligations. Take `⟨a', ha', e⟩` from `h a ha`. Rewrite using `[Formalism.L2.Col.mem_conjP]`. Establish `: Formalism.L2.Col.cO D.host.E a = a'` using `RingOfIntegers.ext e.symm`. Rewrite using `[this]` and apply the resulting hypothesis.

Take `⟨e, he⟩` from `GlobalTheory.MovedIdem.exists_isIdemAt P hso.1`. Take `⟨ϖ, h1, h2⟩` from `SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)`. Take `⟨-, hrep, hel⟩` from `GlobalTheory.SplitPlace.split_local (Wc D i) P e he`. Take `⟨α, hα⟩` from `(hel ϖ h1 h2).1 k (hk.trans (r_le_rank_Wc i))`. Take `⟨Lp, hLp, -, hs, hK⟩` from `loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he`.

Take `⟨Rc, hA, h3, h4⟩` from `hrep α hα.2.1`. Conclude with `⟨α, Rc, ⟨e, ϖ, he, h1, h2, hα⟩, isDC_of_splits hs levG_le_flag ((hLp α).2 hα.2.1) (fun a ha => (hLp a).2 (hA a ha)) hK (fun γ hγ => (h3 γ hγ).2) h4⟩`.
-/
theorem exists_heckeElt_all {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hL : R.toLevCh.Is A.μ0) (hA : R.Sb = R.Pg) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k : ℕ} (hk : k ≤ D.R.r) :
    ∃ α Rc, IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by rw [hA]; exact hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hso.1
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨-, hrep, hel⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨α, hα⟩ := (hel ϖ h1 h2).1 k (hk.trans (r_le_rank_Wc i))
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨Rc, hA, h3, h4⟩ := hrep α hα.2.1
  exact ⟨α, Rc, ⟨e, ϖ, he, h1, h2, hα⟩, isDC_of_splits hs levG_le_flag ((hLp α).2 hα.2.1) (fun a ha => (hLp a).2 (hA a ha)) hK
    (fun γ hγ => (h3 γ hγ).2) h4⟩

end Keep

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T0 A3 T _ R cG S Y H hLev hAll hSup hRd i i' k P hsp hS0 hkr la hl hW`. Establish `hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))` using `GlobalTheory.ExportPin.Model.covered_of_allPlaces R hLev hAll i P hS0 hsp`. Take `⟨α, Rc, ha, hR⟩` from `exists_heckeElt_all hLev hAll i' hso hkr`. Establish `hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `h`.

Rewrite `h` using `[Nat.cast_mul]`. Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hS0 (D.ntw.placesOver_subset_exceptional i 0 h)`. Conclude with `hS0 (D.ntw.placesOver_subset_exceptional i 1 h)`. Establish `hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R.toRealDat i' P k α Rc` using `⟨hso, hg, hkr, ha, hR⟩`.

Use `hSup i' P k α Rc hd _ ?_ hW la ?_` and prove the remaining obligations. Introduce `x`. Establish `h` using `hRd i' k P hsp hso hkr α Rc ha hR ((Y.fi i').e.symm x)`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢`. Rewrite using `[h]`.

Use `congr 1`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC`. Rewrite using `[inv_pow]`. Introduce `p hp hpP hpla`. Establish `hpl : p ≠ D.ntw.l i`.

Introduce and unpack `rfl`. Conclude with `hS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hpP)`. Establish `hcop : IsCoprime (p : 𝓞 T.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F)` using `Nat.Coprime.cast ((Nat.coprime_primes hp (D.ntw.lPrime i).out).2 hpl)`. Take `⟨u, v, huv⟩` from `hcop`. Conclude with `la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hpla) (la.asIdeal.mul_mem_left _ hl)))`.
-/
theorem keeps_transport : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) → GlobalTheory.ExportPin.Reads R cG S Y H.hL → ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i → k ≤ D.R.r → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ (hW : ∀ x ∈ (R.FW i').WK, ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) x ∈ (R.FW i').WK), GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) hW := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R cG S Y H hLev hAll hSup hRd i i' k P hsp hS0 hkr la hl hW
  have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) :=
    GlobalTheory.ExportPin.Model.covered_of_allPlaces R hLev hAll i P hS0 hsp
  obtain ⟨α, Rc, ha, hR⟩ := exists_heckeElt_all hLev hAll i' hso hkr
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hR⟩
  refine hSup i' P k α Rc hd _ ?_ hW la ?_
  · intro x
    have h := hRd i' k P hsp hso hkr α Rc ha hR ((Y.fi i').e.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h]
    congr 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC
    rw [inv_pow]
  · intro p hp hpP hpla
    have hpl : p ≠ D.ntw.l i := by
      rintro rfl
      exact hS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hpP)
    have hcop : IsCoprime (p : 𝓞 T.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp (D.ntw.lPrime i).out).2 hpl)
    obtain ⟨u, v, huv⟩ := hcop
    exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hpla) (la.asIdeal.mul_mem_left _ hl)))

end GlobalTheory.HkSupComm

namespace GlobalTheory.HkSupComm

section Alg
variable {D : D7} (S : RatDat D.ntw)

def toF (j : ℕ) (x : ↥(S.A j).WK) : FmK S j := x

def tm (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : ↥(S.A j).WK) : Fm S i j b := (1 : KB S i b) ⊗ₜ[S.Ks] toF S j x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hkFR_tm (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (x : ↥(S.A j).WK) :
    hkFR S i j b hL hs k P (tm S i j b x) = tm S i j b ⟨hL k P x.1, hs k P _ x.2⟩ := by
  rfl

/- English proof (translation)
Introduce `z hz`. Use `Submodule.span_induction (p := fun z _ => hkFR S i j b hL hs k P z ∈ Bsup S i j b) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨x0, hx, rfl⟩`. Take `⟨s, ⟨u, hu⟩, hsm⟩` from `h _ hx`. Establish `hs0 : s ≠ 0`.

Introduce and unpack `rfl`. Establish `hinj` using `IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))`. Rewrite `hu` using `[map_zero]`. Conclude with `u.ne_zero (hinj (by rw [map_zero]; exact hu.symm))`. Establish `hwk : s • hL k P (x0 : ↥(S.A j).WK).1 ∈ (S.A j).WK` using `(S.A j).WK.smul_mem s (hs k P _ (x0 : ↥(S.A j).WK).2)`.

Establish `e : toF S j ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ = s⁻¹ • toF S j ⟨_, hwk⟩`. Express the relevant statement in the definitionally equal form `(⟨_, _⟩ : ↥(S.A j).WK) = s⁻¹ • (⟨_, hwk⟩ : ↥(S.A j).WK)`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `hL k P (x0 : ↥(S.A j).WK).1 = s⁻¹ • (s • hL k P (x0 : ↥(S.A j).WK).1)`. Rewrite using `[inv_smul_smul₀ hs0]`.

Establish `key : tm S i j b ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ = ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩`. Unfold `tm`. Rewrite using `[e, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Use `erw [TensorProduct.smul_tmul']`. Use `congr 1`.

Establish `e3 : ιK S i b s⁻¹ = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i)`. Rewrite using `[map_inv₀, hu]`. Establish `h5 : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) * algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u : D.ntw.O i) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Conclude with `(eq_inv_of_mul_eq_one_left h5).symm`.

Establish `hgen : tm S i j b ⟨_, hwk⟩ ∈ Bsup S i j b` using `Submodule.subset_span ⟨_, hsm, rfl⟩`. Use `Submodule.smul_mem _ ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) hgen` as an intermediate fact. Establish `e4 : ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩ = ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) • tm S i j b ⟨_, hwk⟩`. Rewrite using `[e3]`. Both sides reduce to the same expression.

Rewrite `this` using `[← e4, ← key]`. Conclude with `this`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `add_mem hx hy`. Introduce `a x _ hx`. Express the relevant statement in the definitionally equal form `hkFR S i j b hL hs k P (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) a • x) ∈ Bsup S i j b`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem hkFR_bsup (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host)
    (h : ∀ x ∈ (S.A j).MK, ∃ s : S.Ks, (∃ u : (D.ntw.O i)ˣ, ιK S i b s = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) ∧
      s • hL k P x ∈ (S.A j).MK) :
    ∀ z ∈ Bsup S i j b, hkFR S i j b hL hs k P z ∈ Bsup S i j b := by
  intro z hz
  refine Submodule.span_induction (p := fun z _ => hkFR S i j b hL hs k P z ∈ Bsup S i j b) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x0, hx, rfl⟩
    obtain ⟨s, ⟨u, hu⟩, hsm⟩ := h _ hx
    have hs0 : s ≠ 0 := by
      rintro rfl
      have hinj := IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [map_zero] at hu
      exact u.ne_zero (hinj (by rw [map_zero]; exact hu.symm))
    have hwk : s • hL k P (x0 : ↥(S.A j).WK).1 ∈ (S.A j).WK := (S.A j).WK.smul_mem s (hs k P _ (x0 : ↥(S.A j).WK).2)
    have e : toF S j ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ = s⁻¹ • toF S j ⟨_, hwk⟩ := by
      change (⟨_, _⟩ : ↥(S.A j).WK) = s⁻¹ • (⟨_, hwk⟩ : ↥(S.A j).WK)
      apply Subtype.ext
      change hL k P (x0 : ↥(S.A j).WK).1 = s⁻¹ • (s • hL k P (x0 : ↥(S.A j).WK).1)
      rw [inv_smul_smul₀ hs0]
    have key : tm S i j b ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ =
        ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩ := by
      unfold tm
      rw [e, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      erw [TensorProduct.smul_tmul']
      congr 1
    have e3 : ιK S i b s⁻¹ = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) := by
      rw [map_inv₀, hu]
      have h5 : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) *
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u : D.ntw.O i) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      exact (eq_inv_of_mul_eq_one_left h5).symm
    have hgen : tm S i j b ⟨_, hwk⟩ ∈ Bsup S i j b := Submodule.subset_span ⟨_, hsm, rfl⟩
    have := Submodule.smul_mem _ ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) hgen
    have e4 : ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩ = ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) • tm S i j b ⟨_, hwk⟩ := by
      rw [e3]; rfl
    rw [← e4, ← key] at this
    exact this
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro a x _ hx
    change hkFR S i j b hL hs k P (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) a • x) ∈ Bsup S i j b
    rw [map_smul]
    exact Submodule.smul_mem _ a hx
end Alg

section Act
variable {D : D7} (S : RatDat D.ntw)

def hLr (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) :
    Module.End S.Ks (FmK S j) :=
  ((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx

/- English proof (translation)
Establish `hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Conclude with `hc (S.eG.symm g) (show ↥(S.A j).WK from x).1`. Establish `h2` using `LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z`. Rewrite `h2` using `[map_mul, map_mul]`.

Express the relevant statement in the definitionally equal form `Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ • Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) = (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ • Module.End.baseChangeHom S …`. Rewrite using `[map_smul]`. Use `congr 1`.
-/
theorem hkFR_act (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hc : ∀ g x, hL k P ((S.A j).ρ g x) = (S.A j).ρ g (hL k P x)) (g : G0g D.nd) (z : Fm S i j b) :
    hkFR S i j b hL hs k P (actG S i j b hst hχ g z) = actG S i j b hst hχ g (hkFR S i j b hL hs k P z) := by
  have hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hc (S.eG.symm g) (show ↥(S.A j).WK from x).1
  have h2 := LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z
  rw [map_mul, map_mul] at h2
  change Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) =
    (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))
        (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) z)
  rw [map_smul]
  congr 1
end Act

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat3 D A3 T.Q.c.F} {cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd}
  {S : RatDat D.ntw} (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)

/- English proof (translation)
Introduce `x hx`. Establish `h1 : (Y.fi i').e.symm x ∈ (S.A ((i' : ℕ) + 1)).WK`. Rewrite using `[(Y.fi i').wk, LinearEquiv.apply_symm_apply]`. Conclude with `hx`. Establish `h2` using `H.hs ((i' : ℕ) + 1) (by omega) (by have := i'.2; omega) k P _ h1`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Conclude with `((Y.fi i').wk _).1 h2`.
-/
theorem hW_of (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host) :
    ∀ x ∈ (R.FW i').WK, ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) x ∈ (R.FW i').WK := by
  intro x hx
  have h1 : (Y.fi i').e.symm x ∈ (S.A ((i' : ℕ) + 1)).WK := by
    rw [(Y.fi i').wk, LinearEquiv.apply_symm_apply]; exact hx
  have h2 := H.hs ((i' : ℕ) + 1) (by omega) (by have := i'.2; omega) k P _ h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact ((Y.fi i').wk _).1 h2

/- English proof (translation)
Apply `(Y.fi i').e.injective` to reduce the goal to its premises. Establish `h` using `LinearMap.congr_fun (hK.rho ((Y.fi i').eG g)) ((Y.fi i').e x)`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h`. Rewrite using `[(Y.fi i').rho, ← h, ← (Y.fi i').rho, LinearEquiv.symm_apply_apply]`.
-/
theorem rho_comm (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host) (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
      (hW_of Y H i' k P)) (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  apply (Y.fi i').e.injective
  have h := LinearMap.congr_fun (hK.rho ((Y.fi i').eG g)) ((Y.fi i').e x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(Y.fi i').rho, ← h, ← (Y.fi i').rho, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Establish `hx' : (Y.fi i').e x ∈ (R.FW i').MK` using `((Y.fi i').mkK x).1 hx`. Take `⟨hwk, hn⟩ : ∃ h : (Y.fi i').e x ∈ (R.FW i').WK, ∀ lp y, (R.FW i').nrm lp y ⟨_, h⟩ ≤ 1` from `hx'`. Take `⟨la, hl, hla⟩` from `GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)`. Establish `hb` using `(hK la hl).sup ⟨_, hwk⟩ (fun y => hn la y)`. Take `⟨s', hs'la, hs'mk⟩` from `GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (R.FW i') hMK.2 la _ hb`.

Establish `e1 : ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) ((Y.fi i').e x) = (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x)`. Simplify using the standard rewrite rules. Use `⟨(Y.fi i').eK.symm (s' : T.Q.c.F), ?_, ?_⟩` and prove the remaining obligations. Establish `n1 : FinitePlace.mk la (s' : T.Q.c.F) = 1`. Rewrite using `[FinitePlace.mk_apply]`.

Conclude with `(FinitePlace.norm_eq_one_iff_notMem _ la s').2 hs'la`. Establish `hs0 : (s' : T.Q.c.F) ≠ 0`. Introduce `h0`. Establish `: s' = 0` using `by exact_mod_cast h0`. Conclude with `hs'la (this ▸ la.asIdeal.zero_mem)`.

Take `⟨a, ha⟩` from `(hla s').2 n1.le`. Take `⟨a', ha'⟩` from `(hla (s' : T.Q.c.F)⁻¹).2 (by rw [map_inv₀, n1, inv_one])`. Establish `hmul : a * a' = 1`. Apply `IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))` to reduce the goal to its premises. Establish `h1 : ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom) ((s' : T.Q.c.F) * (s' : T.Q.c.F)⁻¹) = 1`.

Rewrite using `[mul_inv_cancel₀ hs0, map_one]`. Rewrite `h1` using `[map_mul]`. Rewrite using `[map_mul, ha, ha', map_one]`. Conclude with `h1`. Use `⟨⟨a, a', hmul, by rw [mul_comm]; exact hmul⟩, ?_⟩` and prove the remaining obligations.

Conclude with `ha.symm`. Rewrite using `[(Y.fi i').mkK]`. Establish `e2 : (Y.fi i').e ((Y.fi i').eK.symm (s' : T.Q.c.F) • H.hL ((i' : ℕ) + 1) k P x) = s' • (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x)`. Rewrite using `[← algebraMap_smul D.what₂.LL, map_smul, ← (Y.fi i').eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul, algebraMap_smul]`. Rewrite using `[e2, ← e1]`.

Conclude with `hs'mk`.
-/
theorem mk_smul (i : D.ntw.Tw) (b : Bool) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hMK : (R.FW i').MKFull)
    (hK : ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
      (hW_of Y H i' k P))
    (x : S.WL ((i' : ℕ) + 1)) (hx : x ∈ (S.A ((i' : ℕ) + 1)).MK) :
    ∃ s : S.Ks, (∃ u : (D.ntw.O i)ˣ, ιK S i b s = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) ∧
      s • H.hL ((i' : ℕ) + 1) k P x ∈ (S.A ((i' : ℕ) + 1)).MK := by
  have hx' : (Y.fi i').e x ∈ (R.FW i').MK := ((Y.fi i').mkK x).1 hx
  obtain ⟨hwk, hn⟩ : ∃ h : (Y.fi i').e x ∈ (R.FW i').WK, ∀ lp y, (R.FW i').nrm lp y ⟨_, h⟩ ≤ 1 := hx'
  obtain ⟨la, hl, hla⟩ := GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)
  have hb := (hK la hl).sup ⟨_, hwk⟩ (fun y => hn la y)
  obtain ⟨s', hs'la, hs'mk⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (R.FW i') hMK.2 la _ hb
  have e1 : ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) ((Y.fi i').e x) =
      (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x) := by
    simp
  refine ⟨(Y.fi i').eK.symm (s' : T.Q.c.F), ?_, ?_⟩
  · have n1 : FinitePlace.mk la (s' : T.Q.c.F) = 1 := by
      rw [FinitePlace.mk_apply]; exact (FinitePlace.norm_eq_one_iff_notMem _ la s').2 hs'la
    have hs0 : (s' : T.Q.c.F) ≠ 0 := by
      intro h0
      have : s' = 0 := by exact_mod_cast h0
      exact hs'la (this ▸ la.asIdeal.zero_mem)
    obtain ⟨a, ha⟩ := (hla s').2 n1.le
    obtain ⟨a', ha'⟩ := (hla (s' : T.Q.c.F)⁻¹).2 (by rw [map_inv₀, n1, inv_one])
    have hmul : a * a' = 1 := by
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      have h1 : ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom) ((s' : T.Q.c.F) * (s' : T.Q.c.F)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ hs0, map_one]
      rw [map_mul] at h1
      rw [map_mul, ha, ha', map_one]
      exact h1
    refine ⟨⟨a, a', hmul, by rw [mul_comm]; exact hmul⟩, ?_⟩
    exact ha.symm
  · rw [(Y.fi i').mkK]
    have e2 : (Y.fi i').e ((Y.fi i').eK.symm (s' : T.Q.c.F) • H.hL ((i' : ℕ) + 1) k P x) =
        s' • (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x) := by
      rw [← algebraMap_smul D.what₂.LL, map_smul, ← (Y.fi i').eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
        algebraMap_smul]
    rw [e2, ← e1]
    exact hs'mk

end

/- English proof (translation)
Establish `hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i → k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.K …` using `fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _`. Establish `hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j` using `fun j h1 h2 => ⟨⟨j - 1, by omega⟩, by simp only; omega⟩`. Introduce `i _ b j hj g k P hk`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨i', rfl⟩` from `hidx j h1 h2`.

Take `⟨_, hkr, hsp, hS0⟩` from `hk`. Take `⟨la, hl, -⟩` from `GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)`. Establish `hc` using `rho_comm Y H i' k P la (hK i i' k P hsp hS0 hkr la hl)`. Use `LinearMap.ext fun x => (Y.eF i _ b h1 h2).injective ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[Y.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, Y.act, map_smul, hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (Y.rho _ h1 h2) (Y.chi _ h1 h2) hc]`.
-/
theorem commG (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL) :
    GlobalTheory.LiftLeaf.CommG D := by
  have hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
        (hW_of Y H i' k P) :=
    fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  intro i _ b j hj g k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i', rfl⟩ := hidx j h1 h2
  obtain ⟨_, hkr, hsp, hS0⟩ := hk
  obtain ⟨la, hl, -⟩ := GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)
  have hc := rho_comm Y H i' k P la (hK i i' k P hsp hS0 hkr la hl)
  refine LinearMap.ext fun x => (Y.eF i _ b h1 h2).injective ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Y.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, Y.act, map_smul,
    hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (Y.rho _ h1 h2) (Y.chi _ h1 h2) hc]

/- English proof (translation)
Establish `hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i → k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.K …` using `fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _`. Establish `hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j` using `fun j h1 h2 => ⟨⟨j - 1, by omega⟩, by simp only; omega⟩`. Take `⟨i', rfl⟩` from `hidx j h1 h2`. Take `⟨u, hu1⟩` from `hU i b P hS0 hsp`. Establish `hu : H.cHk i b k P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u ^ k : (D.ntw.O i)ˣ) : D.ntw.O i)`.

Rewrite using `[H.cHk_pow, hu1, Units.val_pow_eq_pow_val, map_pow]`. Rewrite using `[H.hkEq i _ b h1 h2 k P f hS0 hsp hkr, hu, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (hkFR_bsup S i _ b (H.hL _) (H.hs _ h1 h2) k P (fun x hx => mk_smul Y H i b i' k P (hMK i') (hK i i' k P hsp hS0 hkr) x hx) _ hf)`.
-/
theorem eF_hkF_mem_bsup (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces) (hMK : ∀ i, (R.FW i).MKFull)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL)
    (hU : ∀ i b P, P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
      ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u)
    (i : D.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (hS0 : P ∉ D.ntw.S0 i)
    (hsp : Formalism.BasicNotions.IsSplitPl D.host P) (hkr : k ≤ D.R.r) (f : D.nexp.Fm i j b) (hf : Y.eF i j b h1 h2 f ∈ Bsup S i j b) :
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k P f) ∈ Bsup S i j b := by
  have hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
        (hW_of Y H i' k P) :=
    fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨i', rfl⟩ := hidx j h1 h2
  obtain ⟨u, hu1⟩ := hU i b P hS0 hsp
  have hu : H.cHk i b k P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u ^ k : (D.ntw.O i)ˣ) : D.ntw.O i) := by
    rw [H.cHk_pow, hu1, Units.val_pow_eq_pow_val, map_pow]
  rw [H.hkEq i _ b h1 h2 k P f hS0 hsp hkr, hu, algebraMap_smul]
  exact Submodule.smul_mem _ _ (hkFR_bsup S i _ b (H.hL _) (H.hs _ h1 h2) k P
    (fun x hx => mk_smul Y H i b i' k P (hMK i') (hK i i' k P hsp hS0 hkr) x hx) _ hf)

/- English proof (translation)
Use `⟨?_, commG D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd⟩` and prove the remaining obligations. Introduce `i _ j hj b k P hk f hf`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨_, hkr, hsp, hS0⟩` from `hk`. Conclude with `(hB i j b h1 h2 _).2 (eF_hkF_mem_bsup D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hMK hSup hRd hU i j b h1 h2 k P hS0 hsp hkr f ((hB i j b h1 h2 f).1 hf))`.
-/
theorem supHk_commG (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hB : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ Y.eF i j b h1 h2 x ∈ Bsup S i j b)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces) (hMK : ∀ i, (R.FW i).MKFull)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL)
    (hU : ∀ i b P, P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
      ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) :
    GlobalTheory.SupLaw.SupHk D ∧ GlobalTheory.LiftLeaf.CommG D := by
  refine ⟨?_, commG D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd⟩
  intro i _ j hj b k P hk f hf
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨_, hkr, hsp, hS0⟩ := hk
  exact (hB i j b h1 h2 _).2 (eF_hkF_mem_bsup D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hMK hSup hRd hU i j b h1 h2 k P hS0 hsp hkr f
    ((hB i j b h1 h2 f).1 hf))

end GlobalTheory.HkSupComm
