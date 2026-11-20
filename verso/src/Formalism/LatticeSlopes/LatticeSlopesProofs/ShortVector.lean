import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

universe u

/- English proof (translation)
Set `b` to `Module.finBasis ℤ L`. Rewrite using `[covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `only [Matrix.gram, Matrix.of_apply, Basis.map_apply]`.

Conclude with `hf (b i) (b j)`.
-/
theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)

/- English proof (translation)
Use `set n := finrank ℝ W with hn_def`. Set `b` to `Module.finBasis ℤ L`. Establish `hfund` using `ZLattice.isAddFundamentalDomain b MeasureTheory.volume`. Establish `hcov : ZLattice.covolume L = MeasureTheory.volume.real (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L))` using `ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund`. Establish `hFfin : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) ≠ ⊤` using `(ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne`.

Establish `hc : 0 < covol L`. Rewrite using `[hC W L]`. Conclude with `ZLattice.covolume_pos L _`. Establish `hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) = ENNReal.ofReal (covol L)`. Rewrite using `[hC W L, hcov, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hFfin]`.

Use `set t := covol L ^ ((1 : ℝ) / (n : ℝ)) with ht_def`. Establish `ht : 0 ≤ t` using `Real.rpow_nonneg hc.le _`. Establish `htn : t ^ n = covol L`. Rewrite using `[ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]`. Set `o` to `stdOrthonormalBasis ℝ W`.

Use `set S : Set W := {x | ∀ i, |o.repr x i| ≤ t} with hS`. Establish `hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t`. Introduce `x hx`. Rewrite using `[← o.repr.norm_map x, EuclideanSpace.norm_eq]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hx i) 2`. Use `_ = Real.sqrt (n : ℝ) * t := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]`. Establish `hsymm : ∀ x ∈ S, -x ∈ S`. Introduce `x hx i`. Simplify `hx i` using `[map_neg]`. Establish `hconv : Convex ℝ S`.

Introduce `x hx y hy a c ha hc hac i`. Simplify using `only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]`. Use `_ ≤ a * t + c * t := by gcongr`.

Conclude with `hx i`. Conclude with `hy i`. Use `_ = t := by rw [← add_mul, hac, one_mul]`. Establish `hclosed : IsClosed S`. Rewrite using `[hS, Set.setOf_forall]`.

Conclude with `isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const`. Establish `hcpt : IsCompact S`. Use `Metric.isCompact_of_isClosed_isBounded hclosed ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (0 : W)) (r := Real.sqrt (n : ℝ) * t)).subset ?_` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `hnorm x hx`. Establish `hSeq : S = (WithLp.ofLp ∘ o.measurableEquiv) ⁻¹' Set.Icc (fun _ => -t) (fun _ => t)`. Use extensionality with `x`. Simplify using `only [hS, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_Icc, Pi.le_def, abs_le, forall_and]`.

Both sides reduce to the same expression. Establish `hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n`. Rewrite using `[hSeq, ((PiLp.volume_preserving_ofLp (Fin n)).comp o.measurePreserving_measurableEquiv).measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) * 2 ^ n ≤ MeasureTheory.volume S`. Rewrite using `[hF, hvolS, ← ENNReal.ofReal_pow (by linarith), show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp, ← ENNReal.ofReal_mul hc.le]`.

Apply `le_of_eq` to reduce the goal to its premises. Use `congr 1`. Rewrite using `[show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]`. Use `haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hn`. Use `haveI hLc : Countable L := b.equivFun.injective.countable`.

Use `haveI : Countable L.toAddSubgroup := hLc`. Take `⟨x, hx0, hxS⟩` from `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas`. Use `⟨(x : W), x.2, ?_, hnorm _ hxS⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hx0 (Subtype.ext h0)`.
-/
theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  classical
  set n := finrank ℝ W with hn_def
  let b := Module.finBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b MeasureTheory.volume
  have hcov : ZLattice.covolume L = MeasureTheory.volume.real
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund
  have hFfin : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hc : 0 < covol L := by
    rw [hC W L]
    exact ZLattice.covolume_pos L _
  have hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
      ENNReal.ofReal (covol L) := by
    rw [hC W L, hcov, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hFfin]

  set t := covol L ^ ((1 : ℝ) / (n : ℝ)) with ht_def
  have ht : 0 ≤ t := Real.rpow_nonneg hc.le _
  have htn : t ^ n = covol L := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  let o := stdOrthonormalBasis ℝ W
  set S : Set W := {x | ∀ i, |o.repr x i| ≤ t} with hS
  have hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t := by
    intro x hx
    rw [← o.repr.norm_map x, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖o.repr x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, t ^ 2) := by
          apply Real.sqrt_le_sqrt
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Real.sqrt (n : ℝ) * t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i
    simpa [map_neg] using hx i
  have hconv : Convex ℝ S := by
    intro x hx y hy a c ha hc hac i
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |a * o.repr x i + c * o.repr y i| ≤ |a * o.repr x i| + |c * o.repr y i| := abs_add_le _ _
      _ = a * |o.repr x i| + c * |o.repr y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
      _ ≤ a * t + c * t := by
          gcongr
          · exact hx i
          · exact hy i
      _ = t := by rw [← add_mul, hac, one_mul]
  have hclosed : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hcpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine (Metric.isBounded_closedBall (x := (0 : W)) (r := Real.sqrt (n : ℝ) * t)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm x hx
  have hSeq : S = (WithLp.ofLp ∘ o.measurableEquiv) ⁻¹'
      Set.Icc (fun _ => -t) (fun _ => t) := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_Icc,
      Pi.le_def, abs_le, forall_and]
    rfl
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n := by
    rw [hSeq, ((PiLp.volume_preserving_ofLp (Fin n)).comp
      o.measurePreserving_measurableEquiv).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) *
      2 ^ n ≤ MeasureTheory.volume S := by
    rw [hF, hvolS, ← ENNReal.ofReal_pow (by linarith),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp,
      ← ENNReal.ofReal_mul hc.le]
    apply le_of_eq
    congr 1
    rw [show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hn
  haveI hLc : Countable L := b.equivFun.injective.countable
  haveI : Countable L.toAddSubgroup := hLc
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas
  refine ⟨(x : W), x.2, ?_, hnorm _ hxS⟩
  intro h0
  exact hx0 (Subtype.ext h0)

/- English proof (translation)
Introduce `E _ _ _ L hL hne`. Use `haveI : DiscreteTopology L := hL`. Establish `hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E)` using `fun x hx => Submodule.subset_span hx`. Set `L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E))` to `L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)`. Set `e : L ≃ₗ[ℤ] L₀` to `{ toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩ invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`.

Use `haveI : DiscreteTopology L₀ := by`. Use `DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _`. Establish `himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨⟨x, hsub x hx⟩, hx, rfl⟩`.

Use `haveI : IsZLattice ℝ L₀ := by`. Use `⟨?_⟩` and prove the remaining obligations. Apply `Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]`. Use `letI : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _`.

Use `haveI : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩`. Establish `hcov : covol L₀ = covol L` using `covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)`. Establish `hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L`. Rewrite using `[← ZLattice.rank ℝ L₀]`. Conclude with `e.finrank_eq.symm`.

Use `haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne`. Establish `hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E))`. Rewrite using `[hrk]`. Conclude with `Module.finrank_pos`. Take `⟨x, hx, hx0, hxn⟩` from `exists_short_vector_of_isZLattice hC L₀ hpos`.

Use `⟨(x : E), hx, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hx0 (Subtype.ext h0)`. Rewrite `hxn` using `[hrk, hcov]`. Conclude with `hxn`.
-/
theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  haveI : DiscreteTopology L := hL

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  letI : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _
  haveI : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩
  have hcov : covol L₀ = covol L :=
    covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)
  have hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L := by
    rw [← ZLattice.rank ℝ L₀]
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [hrk]
    exact Module.finrank_pos
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ hpos
  refine ⟨(x : E), hx, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · rw [hrk, hcov] at hxn
    exact hxn

end Formalism.F
