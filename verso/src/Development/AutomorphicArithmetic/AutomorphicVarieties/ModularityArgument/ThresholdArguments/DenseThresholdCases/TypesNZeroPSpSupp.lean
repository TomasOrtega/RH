import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)
end P_spSupp
open P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}
/- English proof (translation)
Introduce `hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac`. Establish `hG` using `hLit.loc.geo`. Establish `hZ` using `hLit.loc.zel`. Establish `hBZ` using `hLit.loc.bz`. Establish `hs' : ∀ a, IsSmooth (G.twD τ a)` using `fun a => isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar`.

Establish `hi' : ∀ a, (G.twD τ a).IsIrreducible` using `fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _`. Establish `hτJ : (piTensor (G.twD τ)).IsIrreducible` using `isIrreducible_piTensor_twD G hBZ τ hs' hi'`. Establish `hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π)`. Rewrite using `[piTensor_twD_eq]`. Conclude with `GlobalTheory.LocGL.isSubquotient_twist hjac _`.

Take `⟨s, hsπ⟩` from `GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)`. Establish `hsπ' : HasSupport π s` using `hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm`. Establish `hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) : Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ)`. Introduce `j`. Take `⟨X, _, _, υ, hυ, hυs⟩` from `GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j)) (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)`.

Establish `h1 : IsSubquotient υ (G.twD τ j)` using `GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs`. Conclude with `⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs, GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩`. Use `choose y hy hyE using hy`. Take `⟨t, ht, hst⟩` from `GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy`. Establish `hsm : ∀ a j, IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2)))` using `fun a j => (hν a j).mul (isSmoothChar_absPow _)`.

Establish `htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i)`. Introduce `j`. Take `⟨φ⟩` from `hyE j`. Use `GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j) (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_` and prove the remaining obligations. Conclude with `((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)`.

Conclude with `(hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)`. Establish `hc : ∀ i, IsSmoothChar (G.cOf ν i)` using `fun i => (hν _ _).mul (isSmoothChar_absPow _)`. Establish `hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i)`. Rewrite using `[hst, Finset.sum_congr rfl fun j _ => htj j]`. Conclude with `sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by`.

Unfold `Grp.cOf`. Rewrite using `[Equiv.symm_apply_apply])`. Take `⟨h, x, hx, -, -, e, he⟩` from `hsπ'`. Rewrite `hx` using `[hsF]`. Take `⟨σ, hσ⟩` from `exists_equiv_of_map_eq x _ hx`.

Take `rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a))` from `funext hσ`. Take `rfl : h = n` from `by simpa using Fintype.card_congr σ`. Set `φ` to `multiProdEquiv e fun a => (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm`. Establish `h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a)))` using `he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`. Establish `h2` using `h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))`.

Conclude with `hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2`.
-/
theorem step_spSupp_alt (G : Grp k n) : G.Step_spSupp_alt := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _
  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy
  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])
  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2
end UpperTheory.TNZ.Grp
end
end
