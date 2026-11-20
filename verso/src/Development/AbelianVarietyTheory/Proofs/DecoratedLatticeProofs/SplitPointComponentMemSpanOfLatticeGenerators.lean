import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.FullLatFrame

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : GlobalTheory.FinPl.SplitPt D k)

/- English proof (translation)
Rewrite using `[← GlobalTheory.FinPl.FrameLat.sec_one q]`. Conclude with `(q.int_iff 1).1 (one_mem _)`.
-/
theorem e_int : finPart D q.e ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q]; exact (q.int_iff 1).1 (one_mem _)

/- English proof (translation)
Rewrite using `[q.int_iff, q.sec_pr, map_mul]`. Use `GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, ?_⟩)` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `one_mem _`. Both sides reduce to the same expression.
-/
theorem pr_int_mem (o : 𝓞 D.host.E) : q.pr (incA D (o : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

/- English proof (translation)
Rewrite using `[q.int_iff, q.sec_pr, map_mul]`. Use `GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨α, hα, 1, ?_⟩)` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem pr_pair_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) :
    q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨α, hα, 1, ?_⟩)
  rfl

variable {S : HSp D}

def aux₃ (x : Fin S.rank → D.host.E) : Fin S.rank → k := fun a => q.pr (incA D (x a))

/- English proof (translation)
Rewrite `hx` using `[← hG]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`. Establish `h : aux₃ q (0 : Fin S.rank → D.host.E) = 0` using `by funext a; simp [aux₃]`.

Rewrite using `[h]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `h : aux₃ q (x + y) = aux₃ q x + aux₃ q y` using `by funext a; simp [aux₃]`. Rewrite using `[h]`.

Conclude with `add_mem hx hy`. Consider the case `smul o x _ hx`. Establish `h : aux₃ q (o • x) = (⟨_, pr_int_mem q o⟩ : 𝒪[k]) • aux₃ q x`. Use function extensionality and compare the values at `a`. Use `show q.pr (incA D (o • x a)) = q.pr (incA D (o : D.host.E)) * q.pr (incA D (x a))`.

Rewrite using `[Algebra.smul_def, map_mul, map_mul]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem splitPointComponent_mem_span_of_lattice_generators {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    aux₃ q x ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  rw [← hG] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have h : aux₃ q (0 : Fin S.rank → D.host.E) = 0 := by funext a; simp [aux₃]
    rw [h]; exact zero_mem _
  | add x y _ _ hx hy =>
    have h : aux₃ q (x + y) = aux₃ q x + aux₃ q y := by funext a; simp [aux₃]
    rw [h]; exact add_mem hx hy
  | smul o x _ hx =>
    have h : aux₃ q (o • x) = (⟨_, pr_int_mem q o⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show q.pr (incA D (o • x a)) = q.pr (incA D (o : D.host.E)) * q.pr (incA D (x a))
      rw [Algebra.smul_def, map_mul, map_mul]
    rw [h]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, -, c, hc, x, hx, rfl⟩` from `hy`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Establish `h : (fun a => q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x a))) = (⟨_, pr_pair_mem q hα⟩ : 𝒪[k]) • aux₃ q x`. Use function extensionality and compare the values at `a`. Use `show _ = q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * q.pr (incA D (x a))`. Rewrite using `[← map_mul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `_ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x a)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ (splitPointComponent_mem_span_of_lattice_generators q G hG hx)`. Consider the case `zero`.

Establish `h : (fun a => q.pr ((0 : Fin S.rank → AE D) a)) = 0` using `by funext a; simp`. Rewrite using `[h]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `h : (fun a => q.pr ((y + z) a)) = (fun a => q.pr (y a)) + fun a => q.pr (z a)` using `by funext a; simp`.

Rewrite using `[h]`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy`. Establish `h : (fun a => q.pr ((-y) a)) = -fun a => q.pr (y a)` using `by funext a; simp`. Rewrite using `[h]`.

Conclude with `neg_mem hy`.
-/
theorem pr_mem_span {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L (· = q.v)) :
    (fun a => q.pr (y a)) ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have h : (fun a => q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x a))) =
        (⟨_, pr_pair_mem q hα⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show _ = q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * q.pr (incA D (x a))
      rw [← map_mul]
      congr 1
      change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x a)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]; exact Submodule.smul_mem _ _ (splitPointComponent_mem_span_of_lattice_generators q G hG hx)
  | zero =>
    have h : (fun a => q.pr ((0 : Fin S.rank → AE D) a)) = 0 := by funext a; simp
    rw [h]; exact zero_mem _
  | add y z _ _ hy hz =>
    have h : (fun a => q.pr ((y + z) a)) = (fun a => q.pr (y a)) + fun a => q.pr (z a) := by funext a; simp
    rw [h]; exact add_mem hy hz
  | neg y _ hy =>
    have h : (fun a => q.pr ((-y) a)) = -fun a => q.pr (y a) := by funext a; simp
    rw [h]; exact neg_mem hy

def latW (L : GlobalTheory.FinPl.Lat S) : Submodule 𝒪[k] (Fin S.rank → k) where
  carrier := {w | (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)}
  add_mem' := by
    intro x y hx hy
    have h : (fun i => q.sec ((x + y) i)) = (fun i => q.sec (x i)) + fun i => q.sec (y i) := by funext i; simp
    simp only [Set.mem_setOf_eq] at *
    rw [h]; exact add_mem hx hy
  zero_mem' := by
    have h : (fun i => q.sec ((0 : Fin S.rank → k) i)) = 0 := by funext i; simp
    simp only [Set.mem_setOf_eq]
    rw [h]; exact zero_mem _
  smul_mem' := by
    intro c x hx
    have h : (fun i => q.sec ((c • x) i)) = fun i => q.sec (c : k) * q.sec (x i) := by
      funext i; rw [← GlobalTheory.FinPl.FrameLat.sec_mul q]; rfl
    simp only [Set.mem_setOf_eq] at *
    rw [h]
    exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV ((q.int_iff c).1 c.2) hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latW {L : GlobalTheory.FinPl.Lat S} (w : Fin S.rank → k) :
    w ∈ latW q L ↔ (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := Iff.rfl

/- English proof (translation)
Take `⟨G, hG⟩` from `hL.fg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.FG.of_le (Submodule.fg_span ((G.finite_toSet).image (aux₃ q))) ?_` and prove the remaining obligations. Introduce `w hw`. Establish `h` using `pr_mem_span q G hG hw`.

Simplify `h` using `only [q.pr_sec]`. Rewrite using `[eq_top_iff]`. Establish `hinc : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)), aux₃ q x ∈ Submodule.span k (latW q L : Set (Fin S.rank → k))`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_latW]`. Conclude with `GlobalTheory.FinPl.FrameLat.sec_inc_mem hx`. Consider the case `zero`.

Establish `h : aux₃ q (0 : Fin S.rank → D.host.E) = 0` using `by funext a; simp [aux₃]`. Rewrite using `[h]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `h : aux₃ q (x + y) = aux₃ q x + aux₃ q y` using `by funext a; simp [aux₃]`.

Rewrite using `[h]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `h : aux₃ q (c • x) = q.pr (incA D c) • aux₃ q x`. Use function extensionality and compare the values at `a`.

Use `show q.pr (incA D (c * x a)) = q.pr (incA D c) * q.pr (incA D (x a))`. Rewrite using `[map_mul, map_mul]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hx`. Introduce `w _`.

Rewrite using `[pi_eq_sum_univ w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h` using `hinc (Pi.single i 1) (by rw [hL.span_eq_top]; trivial)`. Establish `e : aux₃ q (Pi.single i (1 : D.host.E)) = fun j => if i = j then (1 : k) else 0`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[aux₃]`. Simplify using `[aux₃, Pi.single_apply, hij, Ne.symm hij]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem latW_isLattice (L : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L) : (latW q L).IsLattice k := by
  obtain ⟨G, hG⟩ := hL.fg
  refine ⟨?_, ?_⟩
  · refine Submodule.FG.of_le (Submodule.fg_span ((G.finite_toSet).image (aux₃ q))) ?_
    intro w hw
    have h := pr_mem_span q G hG hw
    simpa only [q.pr_sec] using h
  · rw [eq_top_iff]
    have hinc : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)),
        aux₃ q x ∈ Submodule.span k (latW q L : Set (Fin S.rank → k)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        rw [SetLike.mem_coe, mem_latW]
        exact GlobalTheory.FinPl.FrameLat.sec_inc_mem hx
      | zero =>
        have h : aux₃ q (0 : Fin S.rank → D.host.E) = 0 := by funext a; simp [aux₃]
        rw [h]; exact zero_mem _
      | add x y _ _ hx hy =>
        have h : aux₃ q (x + y) = aux₃ q x + aux₃ q y := by funext a; simp [aux₃]
        rw [h]; exact add_mem hx hy
      | smul c x _ hx =>
        have h : aux₃ q (c • x) = q.pr (incA D c) • aux₃ q x := by
          funext a
          show q.pr (incA D (c * x a)) = q.pr (incA D c) * q.pr (incA D (x a))
          rw [map_mul, map_mul]
        rw [h]; exact Submodule.smul_mem _ _ hx
    intro w _
    rw [pi_eq_sum_univ w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h := hinc (Pi.single i 1) (by rw [hL.span_eq_top]; trivial)
    have e : aux₃ q (Pi.single i (1 : D.host.E)) = fun j => if i = j then (1 : k) else 0 := by
      funext j
      by_cases hij : i = j
      · subst hij; simp [aux₃]
      · simp [aux₃, Pi.single_apply, hij, Ne.symm hij]
    rwa [e] at h

end GlobalTheory.LocMod.FullLatFrame

namespace GlobalTheory.LocMod.FullLatFrame

/- English proof (translation)
Introduce `D k _ _ _ _ q S L Y _ _ _ hL hY`. Use `haveI hΛ : (latW q L).IsLattice k := latW_isLattice q L hL`. Set `b` to `(Module.finBasisOfFinrankEq 𝒪[k] (latW q L) (Submodule.IsLattice.finrank_of_pi k (latW q L))).reindex ((finCongr (Fintype.card_fin _)).trans (Fintype.equivFinOfCardEq hY).symm)`. Set `b'` to `b.extendOfIsLattice k`. Establish `hkey : ∀ c : Y → 𝒪[k], b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : latW q L) : _ → k)`.

Introduce `c`. Rewrite using `[Module.Basis.equivFun_symm_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.extendOfIsLattice_apply]`. Both sides reduce to the same expression.

Use `⟨⟨LinearMap.toMatrix' b'.equivFun.symm.toLinearMap, LinearMap.toMatrix' b'.equivFun.toLinearMap, ?_, ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules. Rewrite using `[← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules.

Simplify using `only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]`. Rewrite using `[← mem_latW]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `h2 : b'.equivFun.symm y = _` using `hkey fun i => ⟨y i, h i⟩`. Rewrite using `[h2]`.

Conclude with `Subtype.property _`. Establish `h1` using `hkey (b.repr ⟨_, h⟩)`. Rewrite `h1` using `[b.sum_repr]`. Rewrite using `[← b'.equivFun.symm.injective h1]`. Conclude with `fun i => (b.repr ⟨_, h⟩ i).2`.
-/
theorem exists_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y], q.UnitAA →
    Submodule.IsLattice D.host.E L → Fintype.card Y = S.rank → ∃ F : GlobalTheory.LocMod.Frame k S.rank Y, ∀ y : Y → k,
      (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := by
  intro D k _ _ _ _ q S L Y _ _ _ hL hY
  haveI hΛ : (latW q L).IsLattice k := latW_isLattice q L hL
  let b := (Module.finBasisOfFinrankEq 𝒪[k] (latW q L) (Submodule.IsLattice.finrank_of_pi k (latW q L))).reindex
    ((finCongr (Fintype.card_fin _)).trans (Fintype.equivFinOfCardEq hY).symm)
  let b' := b.extendOfIsLattice k
  have hkey : ∀ c : Y → 𝒪[k], b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : latW q L) : _ → k) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.extendOfIsLattice_apply]
    rfl
  refine ⟨⟨LinearMap.toMatrix' b'.equivFun.symm.toLinearMap, LinearMap.toMatrix' b'.equivFun.toLinearMap, ?_, ?_⟩,
    fun y => ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  simp only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
  rw [← mem_latW]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : b'.equivFun.symm y = _ := hkey fun i => ⟨y i, h i⟩
    rw [h2]
    exact Subtype.property _
  · have h1 := hkey (b.repr ⟨_, h⟩)
    rw [b.sum_repr] at h1
    rw [← b'.equivFun.symm.injective h1]
    exact fun i => (b.repr ⟨_, h⟩ i).2

end GlobalTheory.LocMod.FullLatFrame
