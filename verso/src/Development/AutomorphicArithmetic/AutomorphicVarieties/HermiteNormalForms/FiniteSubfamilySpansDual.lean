import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rankhs

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Take `⟨b, hbs, hspan, hli⟩` from `exists_linearIndependent ℝ (f '' S)`. Establish `hbfin : b.Finite` using `hli.setFinite`. Establish `hch : ∀ φ ∈ b, ∃ y, y ∈ S ∧ f y = φ` using `fun φ hφ => hbs hφ`. Use `choose g hgS hgf using hch`. Use `⟨hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2)), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `haveI : Fintype b := hbfin.fintype`. Combine the equalities or inequalities in the displayed calculation. Introduce `y hy`. Take `⟨φ, _, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `hgS _ _`.

Introduce `k hk y hy`. Establish `hsub : b ⊆ LinearMap.ker (Module.Dual.eval ℝ E k)`. Introduce `φ hφ`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hgf φ hφ]`. Conclude with `hk _ (Finset.mem_image.mpr ⟨⟨φ, hbfin.mem_toFinset.mpr hφ⟩, Finset.mem_attach _ _, rfl⟩)`.

Establish `hle` using `Submodule.span_le.mpr hsub`. Rewrite `hle` using `[hspan]`. Establish `hm` using `hle (Submodule.subset_span ⟨y, hy, rfl⟩)`. Rewrite `hm` using `[LinearMap.mem_ker, Module.Dual.eval_apply]`. Then use the resulting hypothesis.
-/
private theorem UpperTheory.V.KT.finite_subfamily_spans_dual {E Y : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (f : Y → Module.Dual ℝ E) (S : Set Y) :
    ∃ M : Finset Y, M.card ≤ Module.finrank ℝ E ∧ (∀ y ∈ M, y ∈ S) ∧
      ∀ k : E, (∀ y ∈ M, f y k = 0) → ∀ y ∈ S, f y k = 0 := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ (f '' S)
  have hbfin : b.Finite := hli.setFinite
  have hch : ∀ φ ∈ b, ∃ y, y ∈ S ∧ f y = φ := fun φ hφ => hbs hφ
  choose g hgS hgf using hch
  refine ⟨hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2)), ?_, ?_, ?_⟩
  · haveI : Fintype b := hbfin.fintype
    calc (hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2))).card
        ≤ hbfin.toFinset.attach.card := Finset.card_image_le
      _ = hbfin.toFinset.card := Finset.card_attach
      _ = Fintype.card b := hbfin.card_toFinset
      _ ≤ Module.finrank ℝ (Module.Dual ℝ E) := hli.fintype_card_le_finrank
      _ = Module.finrank ℝ E := Subspace.dual_finrank_eq
  · intro y hy
    obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hy
    exact hgS _ _
  · intro k hk y hy
    have hsub : b ⊆ LinearMap.ker (Module.Dual.eval ℝ E k) := by
      intro φ hφ
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hgf φ hφ]
      exact hk _ (Finset.mem_image.mpr ⟨⟨φ, hbfin.mem_toFinset.mpr hφ⟩, Finset.mem_attach _ _, rfl⟩)
    have hle := Submodule.span_le.mpr hsub
    rw [hspan] at hle
    have hm := hle (Submodule.subset_span ⟨y, hy, rfl⟩)
    rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at hm

/- English proof (translation)
Introduce `L _ _ _ N v`. Take `⟨M, hMc, hMS, hMk⟩` from `UpperTheory.V.KT.finite_subfamily_spans_dual (E := HS L N) (fun y : Lat L N => (ev y : Module.Dual ℝ (HS L N))) {y | y ≠ 0 ∧ q v.1 y = 1}`. Use `⟨M, hMc.trans (rankhs L N), fun y hy => (hMS y hy).2, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Establish `hk : ∀ y ∈ M, ev y (h - v.1) = 0`.

Introduce `y hy`. Rewrite using `[map_sub, ev_apply, ev_apply, hh y hy, (hMS y hy).2, sub_self]`. Establish `hall` using `hMk (h - v.1) hk`. Establish `h0 : h - v.1 = 0`. Apply `v.2.2` to reduce the goal to its premises.

Introduce `y hy`. Establish `hy' : q v.1 y.1 = 1`. Rewrite using `[← ev_apply]`. Conclude with `hy`. Conclude with `hall y.1 ⟨y.2, hy'⟩`.

Conclude with `sub_eq_zero.mp h0`.
-/
theorem UpperTheory.V.KT.vxdet :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    ∃ M : Finset (Lat L N), M.card ≤ dd L N * N ∧ (∀ y ∈ M, q v.1 y = 1) ∧
      ∀ h : HS L N, (∀ y ∈ M, q h y = 1) → h = v.1 := by
  intro L _ _ _ N v
  obtain ⟨M, hMc, hMS, hMk⟩ := UpperTheory.V.KT.finite_subfamily_spans_dual (E := HS L N)
    (fun y : Lat L N => (ev y : Module.Dual ℝ (HS L N))) {y | y ≠ 0 ∧ q v.1 y = 1}
  refine ⟨M, hMc.trans (rankhs L N), fun y hy => (hMS y hy).2, ?_⟩
  intro h hh
  have hk : ∀ y ∈ M, ev y (h - v.1) = 0 := by
    intro y hy
    rw [map_sub, ev_apply, ev_apply, hh y hy, (hMS y hy).2, sub_self]
  have hall := hMk (h - v.1) hk
  have h0 : h - v.1 = 0 := by
    apply v.2.2
    intro y hy
    have hy' : q v.1 y.1 = 1 := by
      rw [← ev_apply]
      exact hy
    exact hall y.1 ⟨y.2, hy'⟩
  exact sub_eq_zero.mp h0
