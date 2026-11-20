import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spPiSub
end UpperTheory.TNZ.Grp.P_spPiSub
namespace UpperTheory.TNZ.Grp
open P_spPiSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Introduce `hOrd hL Y _ _ τ _ _ ν hν hc hI`. Set `χ : Fin G.s → kˣ →* ℂˣ` to `fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))`. Establish `hχ : ∀ a, IsSmoothChar (χ a)` using `fun a => isSmoothChar_absPow _`. Establish `hsupp : ∀ a, HasSupport (G.twD τ a) (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))`. Introduce `a`.

Establish `h1` using `(hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)`. Rewrite `h1` using `[Multiset.map_map]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Name the introduced variables `j _`.

Conclude with `(IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm`. Establish `hcOf : ∀ i, IsSmoothChar (G.cOf ν i)` using `fun i => (hν _ _).mul (isSmoothChar_absPow _)`. Establish `hS` using `SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth) (fun a => (hsupp a).isIrreducible) hsupp hI`. Establish `hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)` using `sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))`. Take `⟨h, x, hx, -, -, e', he⟩` from `hS`.

Rewrite `hx` using `[hsum]`. Take `⟨σ, hσ⟩` from `exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx`. Take `rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _)` from `funext fun b => (hσ b).symm`. Establish `hn : h = n` using `by simpa using Fintype.card_congr σ`. Substitute `hn` using the available equality.

Set `φ` to `multiProdEquiv e' fun b => (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm`. Establish `hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b))` using `(he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)`. Conclude with `hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq`.
-/
theorem step_spPiSub_alt {n : ℕ} (G : Grp k n) : G.Step_spPiSub_alt := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq
end UpperTheory.TNZ.Grp
end
end
