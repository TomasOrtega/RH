import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveAppTopOfSmoothOfIsProperOfGeometrically

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Use `⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Set `O : Bool → Y.Opens` to `fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩`. Establish `hd : O true ⊓ O false = ⊥` using `le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩`. Establish `hcov : ⨆ i, O i = ⊤` using `top_unique fun y _ => by`.

Break down `hc (Set.mem_univ y) with h | h` into its components or cases. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩`. Take `⟨s, hs⟩` from `TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by`. Establish `sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T)` using `fun T hT => by`.

Substitute `hT` using the available equality. Use `infer_instance`. Apply the tactic sequence `cases i <;> cases j`. Conclude with `(map_zero _).trans (map_zero _).symm`. Conclude with `(sub _ ((inf_comm _ _).trans hd)).elim _ _`.

Conclude with `(sub _ hd).elim _ _`. Conclude with `(map_one _).trans (map_one _).symm)`. Break down `H s with h | h` into its components or cases. Establish `h₁ : u ∈ Y.basicOpen s` using `(mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by`. Rewrite using `[show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]`.

Conclude with `mem_of_isUnit isUnit_one hu)`. Rewrite `h₁` using `[h]`. Conclude with `h₁`. Establish `h₁` using `(mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))`. Rewrite `h₁` using `[show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero]`.

Conclude with `h₁`.
-/
theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun _ => 1⟩, fun i j => by erw [Inh.linComb_triv_g, _root_.one_mul] exact (map_one _).trans (map_one _).symm⟩`.
-/
theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

/- English proof (translation)
Take `⟨E, hE⟩` from `P.sec F g X' π f' h`. Establish `key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i, rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i` using `fun s => by`. Take `⟨w, hw⟩` from `E.surjective (fnSec π s)`. Take `⟨c, hc⟩` from `hv w.1 w.2`. Use `⟨c, fun i => ?_⟩` and prove the remaining obligations.

Establish `e` using `hE w i`. Rewrite `e` using `[hw]`. Use `((rs_rs _ _ s).symm.trans e).trans ?_` and prove the remaining obligations. Rewrite using `[← loc_smul, ← hc]`. Both sides reduce to the same expression.

Take `⟨c₁, h₁⟩` from `key 1`. Establish `hu : ∀ i, IsUnit (loc P π f' v i)` using `fun i => isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)`. Use `preconnectedSpace_of_functions X' fun s => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `key s`. Distinguish the cases in `h0 : c = 0`.

Use `Or.inl (le_bot_iff.1 fun y hy => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_mem P (π y)`. Use `(mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy` as an intermediate fact. Rewrite `this` using `[hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero]`. Then use the resulting hypothesis. Use `Or.inr (top_unique fun y _ => ?_)` and prove the remaining obligations.

Take `⟨i, hi⟩` from `exists_mem P (π y)`. Use `(mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi`.
-/
theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

/- English proof (translation)
Introduce `R _ _ Z s K _ x hp hs hc`. Establish `hp' : IsProjBy s` using `(GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp`. Take `⟨P⟩` from `nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)`. Establish `hpr : IsProper s` using `isProper_of_isProjBy R Z s hp'`. Establish `h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s (Spec.map (CommRingCat.ofHom x))` using `IsPullback.of_hasPullback _ _`.

Establish `hbij` using `bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _ (pullback.snd s (spMap x)) inferInstance inferInstance hc`. Take `⟨v, -, hu, hline⟩` from `loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)`. Take `⟨x₀, -⟩` from `(pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`.

Take `⟨i, hi⟩` from `exists_mem P ((pullback.fst s (spMap x)) x₀)`. Establish `h₁` using `mem_of_isUnit (hu i) (y := x₀) hi`. Rewrite `h₁` using `[← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero]`. Conclude with `h₁`. Take `⟨δ, v₀, hδ, hker⟩` from `exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)`.

Set `p : PrimeSpectrum R` to `s ((pullback.fst s (spMap x)) x₀)`. Establish `hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0` using `fun a ha h0 => by`. Establish `e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀)` using `congrArg (fun t => t x₀) h₀.w`. Apply `ha` to reduce the goal to its premises. Rewrite using `[e]`.

Express the relevant statement in the definitionally equal form `x a ∈ (pullback.snd s (spMap x) x₀).asIdeal`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Take `⟨_, ⟨ε, rfl⟩, hε, hεs⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range`. Use `⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩` and prove the remaining obligations.

Use `⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩` and prove the remaining obligations. Set `g : R →+* F` to `(algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)`. Establish `hg : IsUnit (g δ * g ε)`. Rewrite using `[← map_mul]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map (algebraMap (Localization.Away (δ * ε)) F)`.

Establish `h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s (Spec.map (CommRingCat.ofHom g))`. Use `h.paste_horiz (IsPullback.of_hasPullback s _)` as an intermediate fact. Rewrite `this` using `[← Spec.map_comp]`. Then use the resulting hypothesis. Establish `hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s` using `hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0`. Take `⟨z, hz⟩` from `hmem`.

Take `⟨y, -⟩` from `Scheme.exists_preimage_of_isPullback h' z _ hz`. Use `preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))` as an intermediate fact. Conclude with `⟨⟨y⟩⟩`.
-/
theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
