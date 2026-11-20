import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ConnFibre

open GlobalTheory.AbLaw.Seesaw

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

/- English proof (translation)
Set `F` to `(Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop`. Establish `hF : F.hom.IsIntegral`. Apply `RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)` to reduce the goal to its premises. Conclude with `isIntegral_appTop_of_universallyClosed p`. Use `algebraize [F.hom]`.

Establish `h : Function.Surjective F.hom` using `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2`. Introduce `s`. Take `⟨c, hc⟩` from `h s`. Conclude with `⟨_, hc⟩`.
-/
theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

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
Introduce `V _ _ _ B hs hp Y₀ b hb hc`. Take `⟨P⟩` from `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj V B.left B.hom hs hp _ (Inh.trivLB_isLB _)`. Establish `hpr : IsProper B.hom` using `GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hp`. Set `L` to `AlgebraicClosure (IsLocalRing.ResidueField V)`. Set `g₀ : V →+* L` to `(algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)`.

Establish `hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V` using `fun a => (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)`. Set `q : V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1) →+* L` to `Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (by simpa using ha)`. Set `y₀ : Spec (CommRingCat.of L) ⟶ _` to `Spec.map (CommRingCat.ofHom q)`. Establish `h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom (Spec.map (CommRingCat.ofHom g₀))`. Use `(IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb` as an intermediate fact.

Rewrite `this` using `[← Spec.map_comp]`. Then use the resulting hypothesis. Establish `hs₀ : Smooth Y₀.hom` using `MorphismProperty.of_isPullback hb hs`. Establish `hi` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc`. Establish `hint : IsIntegral (pullback Y₀.hom y₀)` using `GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)`. Establish `hpr₀ : IsProper (pullback.snd Y₀.hom y₀)` using `MorphismProperty.of_isPullback h₀ hpr`.

Take `⟨v, -, hu, hline⟩` from `loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)`. Take `⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀)` from `inferInstance`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Take `⟨i, hi⟩` from `exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)`.

Establish `h₁` using `mem_of_isUnit (hu i) (y := x₀) hi`. Rewrite `h₁` using `[← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero]`. Conclude with `h₁`. Take `⟨δ, v₀, hδ, hker⟩` from `exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))`. Establish `hδ' : IsUnit δ`.

Assume the negation of the conclusion as `hn`. Conclude with `hδ ((hg₀ δ).2 hn)`. Establish `hsurj : Surjective B.hom`. Set `O : (Spec (CommRingCat.of V)).Opens` to `⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩`. Establish `hO : O = ⊤`.

Use `(IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩` and prove the remaining obligations. Establish `e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) = Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀)` using `congrArg (fun t => t x₀) h₀.w`. Use `e.trans (PrimeSpectrum.ext ?_)` and prove the remaining obligations. Use `((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top fun a ha => ?_).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal`.

Rewrite using `[(hg₀ a).2 ha]`. Conclude with `zero_mem _`. Conclude with `⟨fun z => hO.ge (Set.mem_univ z)⟩`. Use `⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩` and prove the remaining obligations. Establish `: Surjective snd` using `MorphismProperty.of_isPullback h hsurj`.

Take `⟨z, -⟩` from `snd.surjective (⊥ : PrimeSpectrum F)`. Use `preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))` as an intermediate fact. Conclude with `⟨⟨z⟩⟩`.
-/
theorem geometricallyConnected_of_closedFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))), Smooth B.hom → IsProjBy B.hom → ∀ (Y₀ : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1))))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (thick V (IsLocalRing.maximalIdeal V) 0) → GeometricallyConnected Y₀.hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B hs hp Y₀ b hb hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj V B.left B.hom hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hp
  let L := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* L := (algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)
  have hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V := fun a =>
    (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)
  let q : V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1) →+* L :=
    Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (by simpa using ha)
  let y₀ : Spec (CommRingCat.of L) ⟶ _ := Spec.map (CommRingCat.ofHom q)
  have h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb
    rwa [← Spec.map_comp] at this
  have hs₀ : Smooth Y₀.hom := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc
  have hint : IsIntegral (pullback Y₀.hom y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)
  have hpr₀ : IsProper (pullback.snd Y₀.hom y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hδ' : IsUnit δ := by
    by_contra hn
    exact hδ ((hg₀ δ).2 hn)
  have hsurj : Surjective B.hom := by
    let O : (Spec (CommRingCat.of V)).Opens := ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩
    have hO : O = ⊤ := by
      refine (IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩
      have e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext ?_)
      refine ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top
        fun a ha => ?_).symm
      change g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal
      rw [(hg₀ a).2 ha]
      exact zero_mem _
    exact ⟨fun z => hO.ge (Set.mem_univ z)⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback h hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnFibre
