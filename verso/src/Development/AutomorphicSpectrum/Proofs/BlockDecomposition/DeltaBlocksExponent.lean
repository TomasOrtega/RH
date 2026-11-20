import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardResidueEqQV

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DlBridgeAt

/- English proof (translation)
Take `⟨y, hy⟩` from `valuation_surjective (uniformizer k)`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[map_zero]`. Conclude with `uniformizer_ne_zero hy.symm`.

Establish `hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k` using `hy`. Establish `h1 : ord k (Units.mk0 y hy0) = 1` using `ord_eq_one hu`. Establish `h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0`. Establish `h3` using `ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)`. Rewrite `h3` using `[inv_mul_cancel_right]`.

Use linear arithmetic over natural numbers and integers. Establish `h4` using `ord_eq_zero_iff.1 h2`. Rewrite `h4` using `[Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu]`. Establish `hne : uniformizer k ≠ 0` using `uniformizer_ne_zero`. Conclude with `(mul_inv_eq_one₀ hne).1 h4`.
-/
theorem val_eq_uniformizer_of_ord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (h : ord k ϖ = 1) :
    valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_ne_zero hy.symm
  have hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k := hy
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hu
  have h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0 := by
    have h3 := ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right] at h3
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu] at h4
  have hne : uniformizer k ≠ 0 := uniformizer_ne_zero
  exact (mul_inv_eq_one₀ hne).1 h4

end GlobalTheory.CompanionTheory.DlBridgeAt

open GlobalTheory.CompanionTheory.DlBridgeAt in

/- English proof (translation)
Introduce `E _ _ _ w ϖ hϖ`. Establish `hord : ord (w.adicCompletion E) ϖ = 1` using `(GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ`. Use `⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩` and prove the remaining obligations. Establish `hinv` using `GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x`. Establish `hv` using `val_deltaHalf (w.adicCompletion E) (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)`.

Establish `hm` using `deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)`. Establish `hpos` using `modulus_pos (w.adicCompletion E) (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)`. Rewrite `hinv` using `[Units.val_inv_eq_inv_val, hv]`. Rewrite using `[hv, hm]`. Express the relevant statement in the definitionally equal form `_ = GlobalTheory.BCT.qh w ^ _ at hinv`.

Rewrite using `[← hinv]`. Use `set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit) (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef`. Establish `hs : √m * √m = m` using `Real.mul_self_sqrt hpos.le`. Establish `hs0 : √m ≠ 0` using `(Real.sqrt_pos.2 hpos).ne'`. Establish `key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹` using `fun s h => by field_simp`.

Establish `h5` using `key _ hs0`. Rewrite `h5` using `[hs]`. Rewrite using `[← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]`.
-/
theorem GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  intro E _ _ _ w ϖ hϖ
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  refine ⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩
  have hinv := GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x
  have hv := val_deltaHalf (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  have hm := deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)
  have hpos := modulus_pos (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  rw [Units.val_inv_eq_inv_val, hv] at hinv
  rw [hv, hm]
  change _ = GlobalTheory.BCT.qh w ^ _ at hinv
  rw [← hinv]
  set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef
  have hs : √m * √m = m := Real.mul_self_sqrt hpos.le
  have hs0 : √m ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹ := fun s h => by field_simp
  have h5 := key _ hs0
  rw [hs] at h5
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]

end
