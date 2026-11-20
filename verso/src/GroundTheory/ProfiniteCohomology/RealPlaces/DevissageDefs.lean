import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.CupSequence
import GroundTheory.ProfiniteCohomology.PoincarePairs.Devissage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section ResMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

noncomputable abbrev tateCompactCochainsResMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (g : A ⟶ B) :
    tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _) ⟶
      tateCompactCochains φ ψ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom B) (fun _ => 𝟙 _) :=
  tateCompactCochainsMap φ ψ (Aᵥ := fun v => Rep.res (φ v).toMonoidHom A)
    (Bᵥ := fun v => Rep.res (φ v).toMonoidHom B) (Aᵣ := fun w => Rep.res (ψ w).toMonoidHom A)
    (Bᵣ := fun w => Rep.res (ψ w).toMonoidHom B) g
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)

noncomputable abbrev tateCompactCohomologyResMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (g : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyRes φ ψ A n ⟶ tateCompactCohomologyRes φ ψ B n :=
  HomologicalComplex.homologyMap (tateCompactCochainsResMap φ ψ g) n

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

/- English proof (translation)
Use extensionality with `n : 1`. Use `ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) => Prod.ext (Prod.ext ?_ ?_) ?_)` and prove the remaining obligations. Conclude with `congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_add g₁ g₂)`. Consider the cases of `n with`. Consider the case `zero => rfl`.

Consider the case `succ n => exact Subsingleton.elim _ _`. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n`. Use `Prod.ext (funext fun v => ?_) (funext fun w => ?_)` and prove the remaining obligations.

Conclude with `congrArg (fun F => (F.f n).hom (p.2.1 v)) (cochainsMap_add ((Rep.resFunctor (φ v).toMonoidHom).map g₁) ((Rep.resFunctor (φ v).toMonoidHom).map g₂))`. Conclude with `congrArg (fun F => (F.f n).hom (p.2.2 w)) (cochainsMap_add ((Rep.resFunctor (ψ w).toMonoidHom).map g₁) ((Rep.resFunctor (ψ w).toMonoidHom).map g₂))`.
-/
theorem tateCompactCochainsResMap_add (g₁ g₂ : A ⟶ B) :
    tateCompactCochainsResMap φ ψ (g₁ + g₂) =
      tateCompactCochainsResMap φ ψ g₁ + tateCompactCochainsResMap φ ψ g₂ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_add g₁ g₂)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v)) (cochainsMap_add
          ((Rep.resFunctor (φ v).toMonoidHom).map g₁) ((Rep.resFunctor (φ v).toMonoidHom).map g₂))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w)) (cochainsMap_add
          ((Rep.resFunctor (ψ w).toMonoidHom).map g₁) ((Rep.resFunctor (ψ w).toMonoidHom).map g₂))

/- English proof (translation)
Use extensionality with `n : 1`. Use `ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) => Prod.ext (Prod.ext ?_ ?_) ?_)` and prove the remaining obligations. Conclude with `congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_zero (A := A) (B := B))`. Consider the cases of `n with`. Consider the case `zero => rfl`.

Consider the case `succ n => exact Subsingleton.elim _ _`. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n`. Use `Prod.ext (funext fun v => ?_) (funext fun w => ?_)` and prove the remaining obligations.

Conclude with `congrArg (fun F => (F.f n).hom (p.2.1 v)) (cochainsMap_zero (A := Rep.res (φ v).toMonoidHom A) (B := Rep.res (φ v).toMonoidHom B))`. Conclude with `congrArg (fun F => (F.f n).hom (p.2.2 w)) (cochainsMap_zero (A := Rep.res (ψ w).toMonoidHom A) (B := Rep.res (ψ w).toMonoidHom B))`.
-/
theorem tateCompactCochainsResMap_zero :
    tateCompactCochainsResMap φ ψ (0 : A ⟶ B) = 0 := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_zero (A := A) (B := B))
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v))
          (cochainsMap_zero (A := Rep.res (φ v).toMonoidHom A) (B := Rep.res (φ v).toMonoidHom B))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w))
          (cochainsMap_zero (A := Rep.res (ψ w).toMonoidHom A) (B := Rep.res (ψ w).toMonoidHom B))

/- English proof (translation)
Use extensionality with `n : 1`. Use `ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) => Prod.ext (Prod.ext rfl ?_) ?_)` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n => exact Subsingleton.elim _ _`.

Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n => rfl`.
-/
theorem tateCompactCochainsResMap_id : tateCompactCochainsResMap φ ψ (𝟙 A) = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

/- English proof (translation)
Use extensionality with `n : 1`. Use `ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) => Prod.ext (Prod.ext rfl ?_) ?_)` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n => exact Subsingleton.elim _ _`.

Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ n => rfl`.
-/
theorem tateCompactCochainsResMap_comp (g : A ⟶ B) (g' : B ⟶ C) :
    tateCompactCochainsResMap φ ψ (g ≫ g') =
      tateCompactCochainsResMap φ ψ g ≫ tateCompactCochainsResMap φ ψ g' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

/- English proof (translation)
Rewrite using `[tateCompactCohomologyResMap, tateCompactCochainsResMap_add, HomologicalComplex.homologyMap_add]`. Both sides reduce to the same expression.
-/
theorem tateCompactCohomologyResMap_add (g₁ g₂ : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g₁ + g₂) n =
      tateCompactCohomologyResMap φ ψ g₁ n + tateCompactCohomologyResMap φ ψ g₂ n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_add,
    HomologicalComplex.homologyMap_add]
  rfl

/- English proof (translation)
Rewrite using `[tateCompactCohomologyResMap, tateCompactCochainsResMap_zero, HomologicalComplex.homologyMap_zero]`. Both sides reduce to the same expression.
-/
theorem tateCompactCohomologyResMap_zero (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (0 : A ⟶ B) n = 0 := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_zero,
    HomologicalComplex.homologyMap_zero]
  rfl

/- English proof (translation)
Rewrite using `[tateCompactCohomologyResMap, tateCompactCochainsResMap_id, HomologicalComplex.homologyMap_id]`. Both sides reduce to the same expression.
-/
theorem tateCompactCohomologyResMap_id (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (𝟙 A) n = 𝟙 _ := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_id,
    HomologicalComplex.homologyMap_id]
  rfl

/- English proof (translation)
Rewrite using `[tateCompactCohomologyResMap, tateCompactCochainsResMap_comp, HomologicalComplex.homologyMap_comp]`. Both sides reduce to the same expression.
-/
theorem tateCompactCohomologyResMap_comp (g : A ⟶ B) (g' : B ⟶ C) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g ≫ g') n =
      tateCompactCohomologyResMap φ ψ g n ≫ tateCompactCohomologyResMap φ ψ g' n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction with`. Consider the case `empty => simp [tateCompactCohomologyResMap_zero]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, tateCompactCohomologyResMap_add, ih]`.
-/
theorem tateCompactCohomologyResMap_finsetSum {J : Type*} (s : Finset J) (f : J → (A ⟶ B))
    (m : ℕ) :
    tateCompactCohomologyResMap φ ψ (∑ j ∈ s, f j) m =
      ∑ j ∈ s, tateCompactCohomologyResMap φ ψ (f j) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [tateCompactCohomologyResMap_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tateCompactCohomologyResMap_add, ih]

/- English proof (translation)
Establish `h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0`. Rewrite using `[Finset.sum_const, Finset.card_range]`. Use extensionality with `a`. Conclude with `hm a`. Establish `e : (tateCompactCohomologyResMap φ ψ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x = (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom x` using `by rw [h0]`.

Rewrite `e` using `[tateCompactCohomologyResMap_finsetSum, tateCompactCohomologyResMap_zero]`. Simplify using `only [tateCompactCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e`. Simplify using `using e`.
-/
theorem nsmul_tateCompactCohomologyRes_eq_zero {m : ℕ} (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : tateCompactCohomologyRes φ ψ A n) : m • x = 0 := by
  have h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0 := by
    rw [Finset.sum_const, Finset.card_range]
    ext a
    exact hm a
  have e : (tateCompactCohomologyResMap φ ψ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x =
      (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom x := by rw [h0]
  rw [tateCompactCohomologyResMap_finsetSum, tateCompactCohomologyResMap_zero] at e
  simp only [tateCompactCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e
  simpa using e

end ResMap

section Sequence

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]

noncomputable def tateCompactδRes (hS : S.ShortExact) (n : ℕ) :
    tateCompactCohomologyRes φ ψ S.X₃ n ⟶ tateCompactCohomologyRes φ ψ S.X₁ (n + 1) :=
  tateCompactδ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
    (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

variable (hS : S.ShortExact)

include hS in

/- English proof (translation)
The claim follows from `tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) (fun w => (Rep.shortExact_res (ψ w).toMonoi …`.
-/
theorem tateCompactRes_exact₂ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.f n) (tateCompactCohomologyResMap φ ψ S.g n)
      (by rw [← tateCompactCohomologyResMap_comp, S.zero, tateCompactCohomologyResMap_zero])).Exact :=
  tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

/- English proof (translation)
The claim follows from `tateCompactCohomology_exact₃ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) (fun w => (Rep.shortExact_res (ψ w).toMonoi …`.
-/
theorem tateCompactRes_exact₃ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.g n) (tateCompactδRes φ ψ hS n)
      (tateCompactCohomologyMap₂₃_tateCompactδ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
        (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n)).Exact :=
  tateCompactCohomology_exact₃ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

/- English proof (translation)
The claim follows from `tateCompactCohomology_exact₁ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) (fun w => (Rep.shortExact_res (ψ w).toMonoi …`.
-/
theorem tateCompactRes_exact₁ (n : ℕ) :
    (ShortComplex.mk (tateCompactδRes φ ψ hS n) (tateCompactCohomologyResMap φ ψ S.f (n + 1))
      (tateCompactδ_tateCompactCohomologyMap₁₂ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
        (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n)).Exact :=
  tateCompactCohomology_exact₁ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

end Sequence

section CupRes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

noncomputable def tateCompactCupRes {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomologyRes φ ψ A r →ₗ[k] cohomology B s →ₗ[k] tateCompactCohomologyRes φ ψ C n :=
  tateCompactCup φ ψ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom μ) h

def tateCompactDualityMap (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] :
    cohomology M r →+ (tateCompactCohomologyRes φ ψ (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp ((bilinAddHom (tateCompactCupRes φ ψ (dualEvalPairing D M)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tateCompactDualityMap_apply (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ}
    (h : r + s = m) (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G)
    [IsDiscreteRep M] [IsDiscreteRep (dualRep D M)] (x : cohomology M r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D M) s) :
    tateCompactDualityMap φ ψ D h t M x y =
      t (tateCompactCupRes φ ψ (dualEvalPairing D M) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end CupRes

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

structure TateCompactDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep D] (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) :
    Prop where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (tateCompactCohomologyRes φ ψ M 4)

  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))

end Hypotheses

end GroundTheory.ProfCoh
