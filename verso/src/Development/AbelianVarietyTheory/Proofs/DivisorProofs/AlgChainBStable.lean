import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial TensorProduct

namespace GlobalTheory.ChainStab

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.hw`. Conclude with `⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩`.
-/
theorem hw_rowHom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
  unfold Formalism.GradedWeylDivisibility.hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩

/- English proof (translation)
Introduce `m hm`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]`.
-/
theorem homZ_of_homN {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f (fun i => (μ i : ℤ)) := by
  intro m hm
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨μ, hf⟩`. Consider the case `cons x w ih`. Take `⟨μ', h⟩` from `ih`. Conclude with `⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩`.
-/
theorem applyWord_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ' : Fin r → ℤ, IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w f) μ' := by
  induction w with
  | nil => exact ⟨μ, hf⟩
  | cons x w ih =>
    obtain ⟨μ', h⟩ := ih
    exact ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩

/- English proof (translation)
Distinguish the cases in `hg : f = 0`. Use `right`. Rewrite using `[hg, map_zero]`. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.1 hg`. Establish `hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0)`.

Introduce `d hd`. Establish `h1` using `hf hd`. Establish `h2` using `hf hm0`. Rewrite `h1`, `h2` using `[Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast]`. Use function extensionality and compare the values at `i`.

Conclude with `congrFun (h1.trans h2.symm) i` after adjusting the coercions. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]`. Use `split_ifs`. Use `left`. Both sides reduce to the same expression.

Use `right`. Both sides reduce to the same expression.
-/
theorem comp_of_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (m : Fin r → ℕ) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = f ∨
      weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = 0 := by
  classical
  by_cases hg : f = 0
  · right; rw [hg, map_zero]
  · obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hg
    have hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0) := by
      intro d hd
      have h1 := hf hd
      have h2 := hf hm0
      rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast] at h1 h2
      funext i
      exact_mod_cast congrFun (h1.trans h2.symm) i
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]
    split_ifs
    · left; rfl
    · right; rfl

/- English proof (translation)
Take `⟨μ0, h0⟩` from `hw_rowHom R hn ν`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Take `⟨μ, hμ⟩` from `applyWord_homZ _ _ (homZ_of_homN _ _ h0) w`.

Apply the tactic sequence `rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]`. Conclude with `Submodule.subset_span ⟨w, rfl⟩`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem weyl_comp_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  obtain ⟨μ0, h0⟩ := hw_rowHom R hn ν
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := applyWord_homZ _ _ (homZ_of_homN _ _ h0) w
    rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
The claim follows from `LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩`.
-/
theorem tprod_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (x : ∀ i, A i) (hx : ∀ i, x i ∈ B i) :
    PiTensorProduct.tprod O x ∈ tensSub B :=
  LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩

/- English proof (translation)
Take `⟨z, rfl⟩` from `LinearMap.mem_range.1 hy`. Use `LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Both sides reduce to the same expression.
-/
theorem map_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (f : ∀ i, A i →ₗ[O] A i)
    (hf : ∀ i, ∀ x ∈ B i, f i x ∈ B i) (y : ⨂[O] i, A i) (hy : y ∈ tensSub B) :
    PiTensorProduct.map f y ∈ tensSub B := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  refine LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam : ι → ℕ → ℕ}

/- English proof (translation)
Introduce `y hy`. Establish `h1 : grp O N lam g = PiTensorProduct.map (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i))` using `rfl`. Rewrite using `[h1]`. Use `map_mem_tensSub _ _ (fun i x hx => ?_) y hy` and prove the remaining obligations. Unfold `chainB at hx ⊢`.

Use `split_ifs at hx ⊢ with hi`. Conclude with `Submodule.mem_top`. Conclude with `Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx`.
-/
theorem grp_stab (s : Finset ι) (g : ι → GL (Fin N) O) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), grp O N lam g y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  have h1 : grp O N lam g = PiTensorProduct.map
      (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i)) := rfl
  rw [h1]
  refine map_mem_tensSub _ _ (fun i x hx => ?_) y hy
  unfold chainB at hx ⊢
  split_ifs at hx ⊢ with hi
  · exact Submodule.mem_top
  · exact Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx

/- English proof (translation)
Introduce `y hy`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.1 hy`. Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c f`. Rewrite using `[map_smul, PiTensorProduct.map_tprod, map_smul]`.

Use `Submodule.smul_mem _ c ?_` and prove the remaining obligations. Set `x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i))` to `fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))`. Establish `hc` using `Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2`. Express the relevant statement in the definitionally equal form `a (PiTensorProduct.tprod O x) ∈ _`. Rewrite using `[ha x ⟨_, hc⟩ rfl]`.

Apply `tprod_mem_tensSub` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `hi : i = τ`. Substitute `hi` using the available equality. Rewrite using `[Function.update_self]`.

Establish `hf` using `(f i).2`. Unfold `chainB at hf ⊢`. Use `split_ifs at hf ⊢ with hs`. Conclude with `Submodule.mem_top`. Conclude with `weyl_comp_mem O le_rfl (res N (lam i)) w _ hf`.

Rewrite using `[Function.update_of_ne hi]`. Conclude with `(f i).2`. Consider the case `add y₁ y₂ h₁ h₂`. Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))`.
-/
theorem proj_stab (s : Finset ι) (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam))
    (ha : IsProj O N lam τ w a) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), a y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, PiTensorProduct.map_tprod, map_smul]
    refine Submodule.smul_mem _ c ?_
    let x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)) := fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))
    have hc := Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2
    change a (PiTensorProduct.tprod O x) ∈ _
    rw [ha x ⟨_, hc⟩ rfl]
    apply tprod_mem_tensSub
    intro i
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      have hf := (f i).2
      unfold chainB at hf ⊢
      split_ifs at hf ⊢ with hs
      · exact Submodule.mem_top
      · exact weyl_comp_mem O le_rfl (res N (lam i)) w _ hf
    · rw [Function.update_of_ne hi]
      exact (f i).2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))

end GlobalTheory.ChainStab

namespace GlobalTheory.ExpFrame

open GlobalTheory.ChainStab

/- English proof (translation)
Introduce `O _ _ _ _ N ι _ _ lam s a`. Set `L` to `tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)`. Set `St : Subalgebra O (Module.End O (NablaT O N lam))` to `{ carrier := {f | ∀ x ∈ L, f x ∈ L} mul_mem' := fun ha hb x hx => ha _ (hb x hx) add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx) algebraMap_mem' := fun c x hx => by`. Rewrite using `[Module.algebraMap_end_apply]`. Conclude with `L.smul_mem c hx }`.

Establish `hle : alg O N lam ≤ St` using `Algebra.adjoin_le (by`. Introduce and unpack `f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)`. Conclude with `grp_stab s g`. Conclude with `proj_stab s τ w f hf)`. Introduce `x hx`.

Conclude with `hle a.2 x hx`.
-/
theorem alg_chainB_stable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (s : Finset ι) (a : alg O N lam),
    ∀ x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s), a • x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s) := by
  intro O _ _ _ _ N ι _ _ lam s a
  let L := tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)
  let St : Subalgebra O (Module.End O (NablaT O N lam)) :=
    { carrier := {f | ∀ x ∈ L, f x ∈ L}
      mul_mem' := fun ha hb x hx => ha _ (hb x hx)
      add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Module.algebraMap_end_apply]; exact L.smul_mem c hx }
  have hle : alg O N lam ≤ St := Algebra.adjoin_le (by
    rintro f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)
    · exact grp_stab s g
    · exact proj_stab s τ w f hf)
  intro x hx
  exact hle a.2 x hx

end GlobalTheory.ExpFrame

end
