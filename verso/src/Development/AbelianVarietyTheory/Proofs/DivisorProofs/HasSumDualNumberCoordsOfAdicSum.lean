import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdicDual

/- English proof (translation)
Establish `bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) → ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c`. Introduce `E _ _ f hf t c h0 hc y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hc y hy`. Consider the case `zero => simpa using h0`.

Consider the case `add y z _ _ k1 k2 => rw [map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2)`. Consider the case `smul a y _ k1 => rw [hf, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (h1 a)).trans k1`. Take `⟨N, ⟨t, rfl⟩, -, -, h⟩` from `h`.

Take `⟨u, rfl⟩` from `IsNoetherian.noetherian I`. Take `⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖g y‖ ≤ c` from `⟨∑ y ∈ t, ‖g y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y hy => Finset.single_le_sum (f := fun y : M => ‖g y‖) (fun _ _ => norm_nonneg _) hy⟩`. Take `⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r` from `⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _, by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha => show ‖φ a‖₊ < 1 from h2 a (Submodule.subset_span ha), fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩`. Establish `hI` using `bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr`. Establish `hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set M), ‖g y‖ ≤ r ^ n * c`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using bd g hg t c hc0 hc`. Consider the case `succ n ih`. Introduce `y hy`.

Rewrite `hy` using `[pow_succ', Submodule.mul_smul]`. Use `Submodule.smul_induction_on hy (fun a ha z hz => ?_) (fun y z k1 k2 => by rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2))` and prove the remaining obligations. Rewrite using `[hg, norm_mul, pow_succ', _root_.mul_assoc]`. Conclude with `mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0`. Use `Metric.tendsto_nhds.2 fun e he => ?_` and prove the remaining obligations.

Establish `lim` using `(tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c`. Rewrite `lim` using `[zero_mul]`. Take `⟨n, hn⟩` from `(lim.eventually (gt_mem_nhds he)).exists`. Take `⟨S, hS⟩` from `h n`. Use `Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_` and prove the remaining obligations.

Use `show dist _ _ < e`. Rewrite using `[dist_comm, dist_eq_norm, ← map_sum, ← map_sub]`. Conclude with `(hP n _ (hS T hT)).trans_lt hn`.
-/
theorem hasSum_of_sumI {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} {C : Type} [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (h1 : ∀ a, ‖φ a‖ ≤ 1) (h2 : ∀ a ∈ I, ‖φ a‖ < 1)
    {M : Type} [AddCommGroup M] [Module R M] (g : M →+ C) (hg : ∀ (a : R) y, g (a • y) = φ a * g y)
    {Ix : Type} {x : Ix → M} {s : M} (h : GlobalTheory.UT.SumI I x s) : HasSum (fun i => g (x i)) (g s) := by
  have bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) →
      ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c := by
    intro E _ _ f hf t c h0 hc y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using h0
    | add y z _ _ k1 k2 => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2)
    | smul a y _ k1 => rw [hf, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h1 a)).trans k1
  obtain ⟨N, ⟨t, rfl⟩, -, -, h⟩ := h
  obtain ⟨u, rfl⟩ := IsNoetherian.noetherian I
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖g y‖ ≤ c :=
    ⟨∑ y ∈ t, ‖g y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
      fun y hy => Finset.single_le_sum (f := fun y : M => ‖g y‖) (fun _ _ => norm_nonneg _) hy⟩
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r :=
    ⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _,
      by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha =>
        show ‖φ a‖₊ < 1 from h2 a (Submodule.subset_span ha),
      fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩
  have hI := bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr
  have hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set M), ‖g y‖ ≤ r ^ n * c := by
    intro n
    induction n with
    | zero => simpa using bd g hg t c hc0 hc
    | succ n ih =>
      intro y hy
      rw [pow_succ', Submodule.mul_smul] at hy
      refine Submodule.smul_induction_on hy (fun a ha z hz => ?_)
        (fun y z k1 k2 => by rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2))
      rw [hg, norm_mul, pow_succ', _root_.mul_assoc]
      exact mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0
  refine Metric.tendsto_nhds.2 fun e he => ?_
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c
  rw [zero_mul] at lim
  obtain ⟨n, hn⟩ := (lim.eventually (gt_mem_nhds he)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_
  show dist _ _ < e
  rw [dist_comm, dist_eq_norm, ← map_sum, ← map_sub]
  exact (hP n _ (hS T hT)).trans_lt hn

/- English proof (translation)
Introduce `V _ _ _ I C _ _ _ hC Ix x s h`. Set `φ : V →+* C` to `(algebraMap (FractionRing V) C).comp (algebraMap V _)`. Prove the components needed by the constructor for the conclusion. Conclude with `hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.fstHom V V V).toLinearMap.toAddMonoidHom) (fun a y => by simp) h`. Conclude with `hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.sndHom V V).toAddMonoidHom) (fun a y => by simp) h`.
-/
theorem hasSum_fst_snd : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  intro V _ _ _ I C _ _ _ hC Ix x s h
  let φ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  constructor
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.fstHom V V V).toLinearMap.toAddMonoidHom)
      (fun a y => by simp) h
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.sndHom V V).toAddMonoidHom)
      (fun a y => by simp) h

end GlobalTheory.AdicDual

end
