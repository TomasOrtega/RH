import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaDec

/- English proof (translation)
Apply the tactic sequence `refine ⟨1, Nat.coprime_one_left q, ?_, ?_⟩ <;>`. Introduce `x hx`. Rewrite using `[Nat.cast_one, one_smul]` and apply the resulting hypothesis.
-/
theorem eqAt_refl {D : D7} {N : ℕ} (q : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqAt D q L L := by
  refine ⟨1, Nat.coprime_one_left q, ?_, ?_⟩ <;>
  · intro x hx
    rwa [Nat.cast_one, one_smul]

/- English proof (translation)
Take `⟨s, hcop, hto, hback⟩` from `h`. Conclude with `⟨s, hcop, hback, hto⟩`.
-/
theorem eqAt_symm {D : D7} {N : ℕ} {q : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁) :
    EqAt D q L₁ L := by
  obtain ⟨s, hcop, hto, hback⟩ := h
  exact ⟨s, hcop, hback, hto⟩

/- English proof (translation)
Take `⟨a, ha, hL₁, hL₁'⟩` from `h`. Take `⟨b, hb, hL₂, hL₂'⟩` from `h'`. Use `⟨a * b, Nat.Coprime.mul ha hb, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : ((b : D.host.E) • ((a : D.host.E) • x)) ∈ L₂` using `hL₂ _ (hL₁ x hx)`. Rewrite `h1` using `[smul_smul, mul_comm, ← Nat.cast_mul]`. Then use the resulting hypothesis.

Establish `h1 : ((a : D.host.E) • ((b : D.host.E) • x)) ∈ L` using `hL₁' _ (hL₂' x hx)`. Rewrite `h1` using `[smul_smul, ← Nat.cast_mul]`. Then use the resulting hypothesis.
-/
theorem eqAt_trans {D : D7} {N : ℕ} {q : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁)
    (h' : EqAt D q L₁ L₂) : EqAt D q L L₂ := by
  obtain ⟨a, ha, hL₁, hL₁'⟩ := h
  obtain ⟨b, hb, hL₂, hL₂'⟩ := h'
  refine ⟨a * b, Nat.Coprime.mul ha hb, fun x hx => ?_, fun x hx => ?_⟩
  ·
    have h1 : ((b : D.host.E) • ((a : D.host.E) • x)) ∈ L₂ := hL₂ _ (hL₁ x hx)
    rwa [smul_smul, mul_comm, ← Nat.cast_mul] at h1
  ·
    have h1 : ((a : D.host.E) • ((b : D.host.E) • x)) ∈ L := hL₁' _ (hL₂' x hx)
    rwa [smul_smul, ← Nat.cast_mul] at h1

/- English proof (translation)
Introduce `_ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ X hX Q hQ x`. Use `set S := ch.S.toGridChoice with hSdef`. Use `set u := S.N.u X with hudef`. Establish `hN : 0 < ∏ q ∈ Q, q` using `Finset.prod_pos fun q hq => (hQ q hq).pos`. Take `⟨r, s, k, hr, hs, hk, hxu⟩` from `GlobalTheory.RatSplitLat.exists_rat_split_lat (ch.G.V X) (S.N.fr X) (∏ q ∈ Q, q) hN (x * u)`.

Establish `hsQ : s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q` using `GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit _ Q s hs`. Establish `hstd : GlobalTheory.SumSize.latAt S X (k * u⁻¹) = stdL D _` using `GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL S X hX k hk`. Use `⟨r, s, k * u⁻¹, hr, hsQ, hstd, fun q hq => ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ g ∈ GlobalTheory.MovedKappaEx.splitOff (ch.G.V X) Q, ∀ y : FinPt ch.G X, EqAt D q (GlobalTheory.SumSize.latAt S X (g * y)) (GlobalTheory.SumSize.latAt S X y)`. Introduce `g hg`.

Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hgen`. Take `⟨e, he, hoff, hsupp⟩` from `hgen`. Introduce `y`. Conclude with `GlobalTheory.MovedSplitEq.eqAt_latAt_mul S X hX q (hQ q hq) e he (hoff q hq) g y hsupp`.

Consider the case `one`. Introduce `y`. Rewrite using `[one_mul]`. Conclude with `_root_.GlobalTheory.MovedKappaDec.eqAt_refl q _`. Consider the case `mul g₁ g₂ _ _ ih₁ ih₂`.

Introduce `y`. Rewrite using `[mul_assoc]`. Conclude with `_root_.GlobalTheory.MovedKappaDec.eqAt_trans (ih₁ (g₂ * y)) (ih₂ y)`. Consider the case `inv g _ ih`. Introduce `y`.

Establish `h` using `ih (g⁻¹ * y)`. Rewrite `h` using `[mul_inv_cancel_left]`. Conclude with `_root_.GlobalTheory.MovedKappaDec.eqAt_symm h`. Establish `h` using `key s hsQ (k * u⁻¹)`. Rewrite `h` using `[hstd]`. Then use the resulting hypothesis.

Rewrite using `[← mul_assoc, ← hxu, mul_inv_cancel_right]`.
-/
theorem exists_dec : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ X hX Q hQ x
  set S := ch.S.toGridChoice with hSdef
  set u := S.N.u X with hudef
  have hN : 0 < ∏ q ∈ Q, q := Finset.prod_pos fun q hq => (hQ q hq).pos

  obtain ⟨r, s, k, hr, hs, hk, hxu⟩ :=
    GlobalTheory.RatSplitLat.exists_rat_split_lat (ch.G.V X) (S.N.fr X) (∏ q ∈ Q, q) hN (x * u)
  have hsQ : s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q := GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit _ Q s hs
  have hstd : GlobalTheory.SumSize.latAt S X (k * u⁻¹) = stdL D _ := GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL S X hX k hk
  refine ⟨r, s, k * u⁻¹, hr, hsQ, hstd, fun q hq => ?_, ?_⟩
  ·
    have key : ∀ g ∈ GlobalTheory.MovedKappaEx.splitOff (ch.G.V X) Q, ∀ y : FinPt ch.G X,
        EqAt D q (GlobalTheory.SumSize.latAt S X (g * y)) (GlobalTheory.SumSize.latAt S X y) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hgen =>
        obtain ⟨e, he, hoff, hsupp⟩ := hgen
        intro y
        exact GlobalTheory.MovedSplitEq.eqAt_latAt_mul S X hX q (hQ q hq) e he (hoff q hq) g y hsupp
      | one =>
        intro y
        rw [one_mul]
        exact _root_.GlobalTheory.MovedKappaDec.eqAt_refl q _
      | mul g₁ g₂ _ _ ih₁ ih₂ =>
        intro y
        rw [mul_assoc]
        exact _root_.GlobalTheory.MovedKappaDec.eqAt_trans (ih₁ (g₂ * y)) (ih₂ y)
      | inv g _ ih =>
        intro y
        have h := ih (g⁻¹ * y)
        rw [mul_inv_cancel_left] at h
        exact _root_.GlobalTheory.MovedKappaDec.eqAt_symm h
    have h := key s hsQ (k * u⁻¹)
    rwa [hstd] at h
  · rw [← mul_assoc, ← hxu, mul_inv_cancel_right]

end GlobalTheory.MovedKappaDec

end
