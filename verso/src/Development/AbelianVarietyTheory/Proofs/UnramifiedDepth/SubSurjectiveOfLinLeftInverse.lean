import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemSupSpanXPowIffAndIsAdicComplete

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

/- English proof (translation)
Establish `h` using `(mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance`. Rewrite `h` using `[Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span]`. Then use the resulting hypothesis.
-/
private theorem isAdicComplete_germIdeal (R κ : Type) [CommRing R] [Finite κ] :
    IsAdicComplete (germIdeal κ R) (MvPowerSeries κ R) := by
  have h := (mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance
  rwa [Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span] at h

/- English proof (translation)
Distinguish the cases in `h0 : e = 0`. Conclude with `Or.inl h0`. Use `right`. Take `⟨k, hk⟩` from `Finsupp.ne_iff.1 h0`. Establish `hle : Finsupp.single k 1 ≤ e`.

Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.2 hk`. Take `⟨c, hc⟩` from `exists_add_of_le hle`. Establish `hd : e.degree = 1 + c.degree` using `by rw [hc, map_add, Finsupp.degree_single]`. Establish `: c = 0` using `(Finsupp.degree_eq_zero_iff c).1 (by omega)`.

Conclude with `⟨k, by rw [hc, this, add_zero]⟩`.
-/
private theorem eq_zero_or_single {κ : Type} {e : κ →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ ∃ k, e = Finsupp.single k 1 := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · right
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
    have hle : Finsupp.single k 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hd : e.degree = 1 + c.degree := by rw [hc, map_add, Finsupp.degree_single]
    have : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    exact ⟨k, by rw [hc, this, add_zero]⟩

/- English proof (translation)
Introduce `R _ d r φ A' h0 hA`. Use `set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha`. Establish `ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2`. Introduce and unpack `⟨i, j⟩`. Use `fin_cases i`.

Both sides reduce to the same expression. Establish `hs : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]`. Set `f : PS R 1 d →+* PS R 1 r` to `(MvPowerSeries.substAlgHom (R := R) hs).toRingHom`. Establish `hf : ∀ u, f u = sub ![φ] u` using `fun u => by`. Express the relevant statement in the definitionally equal form `MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u`.

Rewrite using `[MvPowerSeries.coe_substAlgHom]`. Establish `hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2` using `fun q => by`. Express the relevant statement in the definitionally equal form `MvPowerSeries.substAlgHom hs _ = _`. Rewrite using `[MvPowerSeries.substAlgHom_X, ha']`. Establish `hC1` using `isAdicComplete_germIdeal R (Fin 1 × Fin d)`.

Establish `hC2` using `isAdicComplete_germIdeal R (Fin 1 × Fin r)`. Establish `hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[germIdeal_eq_span, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨q, rfl⟩, rfl⟩`.

Rewrite using `[hfX]`. Conclude with `RingHom.mem_ker.2 (h0 _)`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_ (IsAdicComplete.le_jacobson_bot _) ?_` and prove the remaining obligations. Rewrite using `[germIdeal_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_range _)`.

Rewrite using `[smul_eq_mul, ← pow_two] conv_lhs => rw [germIdeal_eq_span]`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨⟨i0, i⟩, rfl⟩`. Take `rfl : i0 = 0` from `Subsingleton.elim _ _`. Establish `h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f`.

Use `Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[← hfX (0, j)]`. Conclude with `Ideal.mem_map_of_mem _ (X_mem_germIdeal _)`. Establish `h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈ germIdeal (Fin 1 × Fin r) R ^ 2`. Use `mem_germIdeal_pow_iff.2 fun e he => ?_` and prove the remaining obligations.

Break down `eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩` into its components or cases. Simplify using `[h0]`. Take `rfl : k0 = 0` from `Subsingleton.elim _ _`. Establish `h3` using `congrFun (congrFun hA i) k`. Rewrite `h3` using `[Matrix.mul_apply, Matrix.one_apply]`.

Simplify using `only [lin, Matrix.of_apply] at h3`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[h3, MvPowerSeries.coeff_X]`. Simplify using `[Finsupp.single_left_inj, eq_comm]`.

Establish `h4` using `Submodule.add_mem_sup h1 h2`. Rewrite `h4` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hsurj : Function.Surjective f`. Establish `: IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r)`. Rewrite using `[hmap]`.

Conclude with `hC2.toIsHausdorff`. Use `surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩` and prove the remaining obligations. Establish `h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) = MvPowerSeries.C (MvPowerSeries.constantCoeff y)` using `(MvPowerSeries.substAlgHom (R := R) hs).commutes _`.

Rewrite using `[RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]`. Conclude with `RingHom.mem_ker.2 (by simp)`. Introduce `y`. Take `⟨x, hx⟩` from `hsurj y`. Conclude with `⟨x, (hf x).symm.trans hx⟩`.
-/
theorem sub_surjective_of_lin_leftInverse : ∀ (R : Type) [CommRing R] (d r : ℕ) (φ : Fin d → PS R 1 r) (A' : Matrix (Fin r) (Fin d) R), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → A' * lin φ = 1 → Function.Surjective (fun f : PS R 1 d => sub ![φ] f) := by
  intro R _ d r φ A' h0 hA
  classical
  set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha
  have ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2 := by
    rintro ⟨i, j⟩
    fin_cases i
    rfl
  have hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]
  let f : PS R 1 d →+* PS R 1 r := (MvPowerSeries.substAlgHom (R := R) hs).toRingHom
  have hf : ∀ u, f u = sub ![φ] u := fun u => by
    change MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u
    rw [MvPowerSeries.coe_substAlgHom]
  have hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2 := fun q => by
    change MvPowerSeries.substAlgHom hs _ = _
    rw [MvPowerSeries.substAlgHom_X, ha']
  have hC1 := isAdicComplete_germIdeal R (Fin 1 × Fin d)
  have hC2 := isAdicComplete_germIdeal R (Fin 1 × Fin r)
  have hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R := by
    apply le_antisymm
    · rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hfX]
      exact RingHom.mem_ker.2 (h0 _)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [germIdeal_eq_span]
        exact Submodule.fg_span (Set.finite_range _)
      · rw [smul_eq_mul, ← pow_two]
        conv_lhs => rw [germIdeal_eq_span]
        rw [Ideal.span_le]
        rintro _ ⟨⟨i0, i⟩, rfl⟩
        obtain rfl : i0 = 0 := Subsingleton.elim _ _
        have h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f := by
          refine Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_
          rw [← hfX (0, j)]
          exact Ideal.mem_map_of_mem _ (X_mem_germIdeal _)
        have h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈
            germIdeal (Fin 1 × Fin r) R ^ 2 := by
          refine mem_germIdeal_pow_iff.2 fun e he => ?_
          rcases eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩
          · simp [h0]
          · obtain rfl : k0 = 0 := Subsingleton.elim _ _
            have h3 := congrFun (congrFun hA i) k
            rw [Matrix.mul_apply, Matrix.one_apply] at h3
            simp only [lin, Matrix.of_apply] at h3
            rw [map_sub, map_sum]
            simp only [map_smul, smul_eq_mul]
            rw [h3, MvPowerSeries.coeff_X]
            simp [Finsupp.single_left_inj, eq_comm]
        have h4 := Submodule.add_mem_sup h1 h2
        rwa [add_sub_cancel] at h4
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r) := by
      rw [hmap]
      exact hC2.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩
    have h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff y) :=
      (MvPowerSeries.substAlgHom (R := R) hs).commutes _
    rw [RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]
    exact RingHom.mem_ker.2 (by simp)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, (hf x).symm.trans hx⟩

end GlobalTheory.ChF
