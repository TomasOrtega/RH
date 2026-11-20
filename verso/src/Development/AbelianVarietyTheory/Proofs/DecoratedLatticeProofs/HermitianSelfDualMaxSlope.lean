import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatHermHermUnitAniso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLatticeCovolumeNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MuMaxNonposOfLcvNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualFormInvMemSubfield
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvMulVecStarMemDual

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntegralDualSlope

variable {K : Type} [Field K] [NumberField K]

noncomputable def coordDual {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) :=
  (Formalism.HN.dualLat M).map
    ((Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap.restrictScalars (𝓞 K))

omit [NumberField K] in

/- English proof (translation)
Use `conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x, map_sum]`. Simplify using `[dotProduct, mul_comm]`.
-/
theorem coords_dotProduct {n : ℕ} (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    (Pi.basisFun K (Fin n)).dualBasis.equivFun f ⬝ᵥ x = f x := by
  conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x, map_sum]
  simp [dotProduct, mul_comm]

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hy`. Introduce `x hx`. Take `⟨a, ha⟩` from `hf x hx`. Use `Submodule.mem_one.2 ⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`.

Conclude with `(coords_dotProduct f x).symm`.
-/
theorem dotProduct_mem_one {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → K}
    (hy : y ∈ coordDual M) : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨f, hf, rfl⟩ := hy
  intro x hx
  obtain ⟨a, ha⟩ := hf x hx
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [ha]
  exact (coords_dotProduct f x).symm

/- English proof (translation)
Establish `hfg` using `Formalism.HN.DualPolygon.dualLat_fg M hM.span_eq_top`. Establish `hinj : Function.Injective (Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap` using `(Pi.basisFun K (Fin n)).dualBasis.equivFun.injective`. Establish `hM0 : M ≠ ⊥`. Introduce and unpack `rfl`. Establish `h` using `hM.span_eq_top`.

Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Rewrite `h` using `[Submodule.bot_coe, Submodule.span_zero_singleton]`. Conclude with `bot_ne_top h`. Use `⟨hfg.map _, fun h => ?_, ?_⟩` and prove the remaining obligations. Use `Formalism.HN.DualPolygon.dual_ne_bot (Pi.basisFun K (Fin n)) M hM.fg hM.span_eq_top hM0 ?_` and prove the remaining obligations.

Use `(Submodule.eq_bot_iff _).2 fun f hf => hinj ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `(Submodule.eq_bot_iff _).1 h _ (Submodule.mem_map_of_mem hf)`. Establish `hu` using `Formalism.HN.DualPolygon.dualFrame_unit X hX`. Use `(Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X) (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) _ hu hu hinj (fun v x => by` as an intermediate fact.

Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt`. Use the proof step `simp) _ hfg).2.2.2.1`. Unfold `Formalism.HN.muMaxDef coordDual`. Rewrite using `[this]`.
-/
theorem coordDual_spec [StarRing K] [IsTotallyComplex K] {n : ℕ} (hn : 0 < n)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    (coordDual M).FG ∧ coordDual M ≠ ⊥ ∧
      Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) (coordDual M) =
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
          (Formalism.HN.dualLat M) := by
  have hfg := Formalism.HN.DualPolygon.dualLat_fg M hM.span_eq_top
  have hinj : Function.Injective (Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap :=
    (Pi.basisFun K (Fin n)).dualBasis.equivFun.injective
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h := hM.span_eq_top
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  refine ⟨hfg.map _, fun h => ?_, ?_⟩
  · refine Formalism.HN.DualPolygon.dual_ne_bot (Pi.basisFun K (Fin n)) M hM.fg hM.span_eq_top hM0 ?_
    refine (Submodule.eq_bot_iff _).2 fun f hf => hinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ (Submodule.mem_map_of_mem hf)
  · have hu := Formalism.HN.DualPolygon.dualFrame_unit X hX
    have := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
      (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) _ hu hu hinj (fun v x => by
        unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
        simp) _ hfg).2.2.2.1
    unfold Formalism.HN.muMaxDef coordDual
    rw [this]

/- English proof (translation)
Introduce `K _ _ _ _ K0 hK0 v0 hv0 n H X hH M hM hle hn`. Establish `hX : ∀ v, IsUnit (X v).det` using `fun v => (hH.2 v).1`. Take `⟨hfg, hne, heq⟩` from `coordDual_spec hn M hM X hX`. Take `⟨hherm, hdet, -⟩` from `GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n 0 H X hH`. Establish `hG` using `GlobalTheory.isRatHerm_dualFrame K K0 n H X hH`.

Establish `hint` using `GlobalTheory.DualInt.dual_form_integral K n H hherm hdet M hle`. Establish `key` using `GlobalTheory.muMax_nonpos_of_lcv_nonneg K (Formalism.L2.DIV.toHLat (Formalism.HN.dualFrame X) (coordDual M)) (Formalism.HN.DualPolygon.dualFrame_unit X hX) hfg hne (fun N hN _ => by`. Establish `hNfg : Submodule.FG (N : Submodule (𝓞 K) (Fin n → K))` using `(hfg.of_le hN)`. Conclude with `GlobalTheory.T.hermitian_lattice_covolume_nonneg K K0 hK0 v0 hv0 n _ _ hG N hNfg (fun y hy y' hy' => hint y y' (dotProduct_mem_one (hN hy)) (dotProduct_mem_one (hN hy'))))`. Conclude with `heq.symm.trans_le key`.
-/
theorem muMaxDual_nonpos :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
      IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      IsRatHerm K0 H X → ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → 0 < n → (Formalism.L2.DIV.toHLat X M).muMaxDual ≤ 0 := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n H X hH M hM hle hn
  have hX : ∀ v, IsUnit (X v).det := fun v => (hH.2 v).1
  obtain ⟨hfg, hne, heq⟩ := coordDual_spec hn M hM X hX
  obtain ⟨hherm, hdet, -⟩ := GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n 0 H X hH
  have hG := GlobalTheory.isRatHerm_dualFrame K K0 n H X hH
  have hint := GlobalTheory.DualInt.dual_form_integral K n H hherm hdet M hle
  have key := GlobalTheory.muMax_nonpos_of_lcv_nonneg K (Formalism.L2.DIV.toHLat (Formalism.HN.dualFrame X) (coordDual M))
    (Formalism.HN.DualPolygon.dualFrame_unit X hX) hfg hne (fun N hN _ => by
      have hNfg : Submodule.FG (N : Submodule (𝓞 K) (Fin n → K)) :=
        (hfg.of_le hN)
      exact GlobalTheory.T.hermitian_lattice_covolume_nonneg K K0 hK0 v0 hv0 n _ _ hG N hNfg (fun y hy y' hy' =>
        hint y y' (dotProduct_mem_one (hN hy)) (dotProduct_mem_one (hN hy'))))
  exact heq.symm.trans_le key

end GlobalTheory.IntegralDualSlope
