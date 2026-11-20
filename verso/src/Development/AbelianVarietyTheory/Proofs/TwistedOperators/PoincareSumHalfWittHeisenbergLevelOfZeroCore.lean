import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

open scoped Topology

namespace GlobalTheory.BumpMixLevel

variable {D : D7}

/- English proof (translation)
Establish `hfin : (d.extY T a).map (infPart D) = 0`. Rewrite using `[HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]`. Establish `h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T (d.extX T x) (d.extY T a) = 0`. Rewrite using `[← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hfin, GlobalTheory.FinTranslate.symplOH_zero_right]`. Conclude with `Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl`.
-/
theorem symplOH_ext_fin {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ)
    (ha : a.map (infPart D) = 0) :
    symplOH S T (d.extX T x) (d.extY T a) = pairA D.host.F 0 (symplOH S T (d.extX T x) (d.extY T a)).2 := by
  have hfin : (d.extY T a).map (infPart D) = 0 := by
    rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T (d.extX T x) (d.extY T a) = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hfin, GlobalTheory.FinTranslate.symplOH_zero_right]
  exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl

/- English proof (translation)
Establish `hX : Continuous (d.extX T)` using `continuous_id.matrix_mul continuous_const`. Establish `hY : Continuous (d.extY T)` using `continuous_id.matrix_mul continuous_const`. Establish `hs : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2` using `continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp continuous_fst) (hY.comp continuous_snd))`. Establish `hZ` using `GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1`. Establish `hO` using `(isOpen_interior (s := {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1})).preimage hs`.

Establish `hsub : K ×ˢ ({0} : Set (Mx D T.rank ρ)) ⊆ (fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2) ⁻¹' interior {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1}`. Introduce and unpack `⟨k, a⟩ ⟨-, ha⟩`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Simplify using `only [Set.mem_preimage, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, Prod.snd_zero]`.

Conclude with `mem_interior_iff_mem_nhds.2 hZ`. Take `⟨u, v, -, hv, hKu, h0v, huv⟩` from `generalized_tube_lemma hK isCompact_singleton hO hsub`. Take `⟨U, hUo, hU⟩` from `GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ v (hv.mem_nhds (h0v rfl))`. Use `⟨U, hUo, fun a ha hfin k hk => ?_⟩` and prove the remaining obligations. Establish `h1` using `huv (Set.mk_mem_prod (hKu hk) (hU a ha hfin))`.

Establish `h2 : (symplOH S T (d.extX T k) (d.extY T a)).2 ∈ {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1}` using `interior_subset h1`. Rewrite using `[symplOH_ext_fin d k a hfin]`. Conclude with `h2`.
-/
theorem exists_level_pair (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (K : Set (Mx D T.rank ρ)) (hK : IsCompact K) :
    ∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧
      ∀ a ∈ U, a.map (infPart D) = 0 → ∀ k ∈ K, ψ (symplOH S T (d.extX T k) (d.extY T a)) = 1 := by
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hs : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp continuous_fst) (hY.comp continuous_snd))
  have hZ := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
  have hO := (isOpen_interior (s := {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1})).preimage hs
  have hsub : K ×ˢ ({0} : Set (Mx D T.rank ρ)) ⊆
      (fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2) ⁻¹'
        interior {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} := by
    rintro ⟨k, a⟩ ⟨-, ha⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_preimage, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, Prod.snd_zero]
    exact mem_interior_iff_mem_nhds.2 hZ
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ v (hv.mem_nhds (h0v rfl))
  refine ⟨U, hUo, fun a ha hfin k hk => ?_⟩
  have h1 := huv (Set.mk_mem_prod (hKu hk) (hU a ha hfin))
  have h2 : (symplOH S T (d.extX T k) (d.extY T a)).2 ∈ {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} :=
    interior_subset h1
  rw [symplOH_ext_fin d k a hfin]
  exact h2

/- English proof (translation)
Introduce `D ψ hψ S S₀ T ρ d h0 β hβ`. Use `haveI : LocallyCompactSpace (Mx D T.rank ρ) := (GlobalTheory.MixModel.lattice_Mx D T.rank ρ).2.1`. Take `⟨Uβ, hUβo, hUβ⟩` from `hβ.level`. Take `⟨C, hC, hC0⟩` from `exists_compact_mem_nhds (0 : Mx D T.rank ρ)`. Take `⟨UC, hUCo, hUC⟩` from `GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ C hC0`.

Take `⟨UY, hUYo, hUY⟩` from `GlobalTheory.BumpMixLevel.exists_level_pair ψ hψ d (tsupport β ∪ C) (hβ.supp.isCompact.union hC)`. Set `pX : WO S T →+ Mx D T.rank ρ` to `{ toFun := fun u => u ⬝ d.jX, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }`. Set `pY : WO S T →+ Mx D T.rank ρ` to `{ toFun := fun u => u ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }`. Establish `hpX : Continuous pX` using `continuous_id.matrix_mul continuous_const`. Establish `hpY : Continuous pY` using `continuous_id.matrix_mul continuous_const`.

Use `⟨(Uβ ⊓ UC).comap pX ⊓ UY.comap pY, ((hUβo.inter hUCo).preimage hpX).inter (hUYo.preimage hpY), ?_⟩` and prove the remaining obligations. Introduce `u hu hfin`. Establish `hsub0 : ∀ z : WO S₀ T, z = 0` using `fun z => Matrix.ext fun i j => absurd j.isLt (by omega)`. Establish `hw : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY)` using `fun w => by conv_lhs => rw [eq_coords d w]`. Rewrite using `[hsub0 (w ⬝ d.j0), map_zero, add_zero]`.

Establish `hx₀ : u ⬝ d.jX ∈ Uβ ∧ u ⬝ d.jX ∈ UC` using `hu.1`. Establish `ha₀ : u ⬝ d.jY ∈ UY` using `hu.2`. Establish `hfx : (u ⬝ d.jX).map (infPart D) = 0` using `by rw [Matrix.map_mul, hfin, Matrix.zero_mul]`. Establish `hfa : (u ⬝ d.jY).map (infPart D) = 0` using `by rw [Matrix.map_mul, hfin, Matrix.zero_mul]`. Establish `h00 : ψ (symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY))) = 1` using `hUY _ ha₀ hfa _ (Or.inr (hUC _ hx₀.2 hfx))`.

Use function extensionality and compare the values at `w`. Establish `hs : symplOH S T w u = symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) - symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))` using `by conv_lhs => rw [hw w, hw u]`. Simplify using `only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, d.symplOH_extX_extX, d.symplOH_extY_extY, zero_add, add_zero]`. Rewrite using `[GlobalTheory.MixModel.symplOH_skew S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))]`. Normalize the expressions using the abelian group laws.

Simplify using `only [heisO, poinX]`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_mul, Matrix.add_mul]`. Establish `hb : β (w ⬝ d.jX + u ⬝ d.jX + rat γ) = β (w ⬝ d.jX + rat γ)`.

Rewrite using `[add_right_comm]`. Conclude with `hUβ _ hx₀.1 hfx _`. Rewrite using `[hb]`. Distinguish the cases in `hk : β (w ⬝ d.jX + rat γ) = 0`. Rewrite using `[hk, mul_zero, mul_zero, mul_zero]`.

Establish `hkK : ψ (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) = 1` using `hUY _ ha₀ hfa _ (Or.inl (subset_tsupport β hk))`. Rewrite using `[← mul_assoc, ← d.symplOH_extX_extY T, ← d.symplOH_extX_extY T, ← AddChar.map_add_eq_mul, hs]`. Establish `he : symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) - symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) + symplOH S T (d.extX T (w ⬝ d.jX + u ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY + u ⬝ d.jY)) = symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY)) …`. Simplify using `only [map_add, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]`. Normalize the expressions using the abelian group laws.

Rewrite using `[he]`. Simplify using `only [AddChar.map_add_eq_mul, hkK, h00, mul_one]`.
-/
theorem poinX_heis_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  intro D ψ hψ S S₀ T ρ d h0 β hβ
  haveI : LocallyCompactSpace (Mx D T.rank ρ) := (GlobalTheory.MixModel.lattice_Mx D T.rank ρ).2.1
  obtain ⟨Uβ, hUβo, hUβ⟩ := hβ.level
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : Mx D T.rank ρ)
  obtain ⟨UC, hUCo, hUC⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ C hC0
  obtain ⟨UY, hUYo, hUY⟩ := GlobalTheory.BumpMixLevel.exists_level_pair ψ hψ d (tsupport β ∪ C) (hβ.supp.isCompact.union hC)
  let pX : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jX, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let pY : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  have hpX : Continuous pX := continuous_id.matrix_mul continuous_const
  have hpY : Continuous pY := continuous_id.matrix_mul continuous_const
  refine ⟨(Uβ ⊓ UC).comap pX ⊓ UY.comap pY, ((hUβo.inter hUCo).preimage hpX).inter (hUYo.preimage hpY), ?_⟩
  intro u hu hfin
  have hsub0 : ∀ z : WO S₀ T, z = 0 := fun z => Matrix.ext fun i j => absurd j.isLt (by omega)
  have hw : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    conv_lhs => rw [eq_coords d w]
    rw [hsub0 (w ⬝ d.j0), map_zero, add_zero]
  have hx₀ : u ⬝ d.jX ∈ Uβ ∧ u ⬝ d.jX ∈ UC := hu.1
  have ha₀ : u ⬝ d.jY ∈ UY := hu.2
  have hfx : (u ⬝ d.jX).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have hfa : (u ⬝ d.jY).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have h00 : ψ (symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inr (hUC _ hx₀.2 hfx))
  funext w
  have hs : symplOH S T w u = symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) := by
    conv_lhs => rw [hw w, hw u]
    simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, d.symplOH_extX_extX,
      d.symplOH_extY_extY, zero_add, add_zero]
    rw [GlobalTheory.MixModel.symplOH_skew S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))]
    abel
  simp only [heisO, poinX]
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Matrix.add_mul, Matrix.add_mul]
  have hb : β (w ⬝ d.jX + u ⬝ d.jX + rat γ) = β (w ⬝ d.jX + rat γ) := by
    rw [add_right_comm]; exact hUβ _ hx₀.1 hfx _
  rw [hb]
  by_cases hk : β (w ⬝ d.jX + rat γ) = 0
  · rw [hk, mul_zero, mul_zero, mul_zero]
  have hkK : ψ (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inl (subset_tsupport β hk))
  rw [← mul_assoc, ← d.symplOH_extX_extY T, ← d.symplOH_extX_extY T, ← AddChar.map_add_eq_mul, hs]
  have he : symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) +
      symplOH S T (d.extX T (w ⬝ d.jX + u ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY + u ⬝ d.jY)) =
      symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY)) +
        (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY)) +
          symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) +
        symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) := by
    simp only [map_add, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
    abel
  rw [he]
  simp only [AddChar.map_add_eq_mul, hkK, h00, mul_one]

end GlobalTheory.BumpMixLevel
