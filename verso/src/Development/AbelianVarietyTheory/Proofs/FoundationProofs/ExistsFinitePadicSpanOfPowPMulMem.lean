import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

/- English proof (translation)
Use `show _ = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) m)`. Rewrite using `[zp, algebraMap_zp_eq, HahnSeries.C_apply]`.
-/
theorem zp_eq_algebraMap_zpAlg {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] (m : ℤ_[p]) :
    zp Ω m = @algebraMap ℤ_[p] Ω _ _ (zpAlg p Ω) m := by
  show _ = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) m)
  rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]

/- English proof (translation)
Introduce `p _ Ω _ _ hc d E hE v`. Use `letI := zpAlg p Ω`. Use `haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : CharZero Ω := Basic.charZero_of_isClo hc`. Establish `hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x` using `fun m x => by`.

Rewrite using `[Algebra.smul_def, zp_eq_algebraMap_zpAlg]`. Establish `hpv : ((p : Ω) ^ v) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)`. Use `set S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E) with hS`. Set `S' : Submodule ℤ_[p] Ω` to `{ carrier := {y | IsInt p y ∧ (p : Ω) ^ v * y ∈ S} add_mem' := by`. Introduce and unpack `x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩`.

Conclude with `⟨IsIntegral.add hx1 hy1, by rw [mul_add]; exact S.add_mem hx2 hy2⟩`. Use the proof step `zero_mem' := ⟨isIntegral_zero, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨hx1, hx2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]`. Conclude with `IsIntegral.mul isIntegral_algebraMap hx1`. Rewrite using `[mul_smul_comm]`. Conclude with `S.smul_mem c hx2 }`. Establish `hle : S' ≤ Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v))`.

Introduce and unpack `y ⟨_, hy⟩`. Take `⟨c, hc'⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `: y = ((p : Ω) ^ v * y) / (p : Ω) ^ v` using `by field_simp`.

Rewrite using `[this, ← hc', Finset.sum_div]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[smul_div_assoc]`. Establish `hnoeth : IsNoetherian ℤ_[p] (Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v)))` using `isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))`. Establish `hfg : S'.FG` using `isNoetherian_submodule.1 hnoeth S' hle`.

Take `⟨m, f, hf⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Establish `hfmem : ∀ j, f j ∈ S'` using `fun j => hf ▸ Submodule.subset_span ⟨j, rfl⟩`. Establish `halgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨t, rfl⟩` from `hx`. Conclude with `(isAlgZp_iff _).1 (hE t).2`. Consider the case `zero => exact isAlgebraic_zero`. Consider the case `add x y _ _ hx hy => exact hx.add hy`.

Consider the case `smul c x _ hx`. Rewrite using `[Algebra.smul_def]`. Conclude with `(isAlgebraic_algebraMap c).mul hx`. Use `⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[isAlgZp_iff]`.

Establish `h1 : IsAlgebraic ℤ_[p] ((p : Ω) ^ v * f j)` using `halgS _ (hfmem j).2`. Establish `h2 : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹)`. Use `IsAlgebraic.inv ?_` and prove the remaining obligations. Establish `: ((p : Ω) ^ v) = algebraMap ℤ_[p] Ω ((p : ℤ_[p]) ^ v)` using `by simp`. Rewrite using `[this]`.

Conclude with `isAlgebraic_algebraMap _`. Use `h2.mul h1` as an intermediate fact. Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ hpv, one_mul]`. Then use the resulting hypothesis. Introduce `l y hy hyl`. Establish `hyS : y ∈ S'`.

Use `⟨hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hyl]`. Use `S.sum_mem fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← hsm]`. Conclude with `S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)`.

Rewrite `hyS` using `[← hf]`. Take `⟨μ, hμ⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS`. Conclude with `⟨μ, by rw [← hμ]; exact Finset.sum_congr rfl fun j _ => hsm _ _⟩`.
-/
theorem exists_fin_span_of_pow_mul :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
      (∀ t, IsInt p (E t) ∧ IsAlgZp p (E t)) → ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
        (∀ j, IsInt p (f j) ∧ IsAlgZp p (f j)) ∧ ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt p y →
          (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t → ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω := Basic.charZero_of_isClo hc
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, zp_eq_algebraMap_zpAlg]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  set S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E) with hS
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt p y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        exact ⟨IsIntegral.add hx1 hy1, by rw [mul_add]; exact S.add_mem hx2 hy2⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hx1
        · rw [mul_smul_comm]; exact S.smul_mem c hx2 }
  have hle : S' ≤ Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v)) := by
    rintro y ⟨_, hy⟩
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    have : y = ((p : Ω) ^ v * y) / (p : Ω) ^ v := by field_simp
    rw [this, ← hc', Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_div_assoc]
  have hnoeth : IsNoetherian ℤ_[p] (Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem : ∀ j, f j ∈ S' := fun j => hf ▸ Submodule.subset_span ⟨j, rfl⟩
  have halgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (isAlgZp_iff _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]; exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · rw [isAlgZp_iff]
    have h1 : IsAlgebraic ℤ_[p] ((p : Ω) ^ v * f j) := halgS _ (hfmem j).2
    have h2 : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) := by
      refine IsAlgebraic.inv ?_
      have : ((p : Ω) ^ v) = algebraMap ℤ_[p] Ω ((p : ℤ_[p]) ^ v) := by simp
      rw [this]; exact isAlgebraic_algebraMap _
    have := h2.mul h1
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at this
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsm]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by rw [← hμ]; exact Finset.sum_congr rfl fun j _ => hsm _ _⟩

end GlobalTheory.GeoFix
