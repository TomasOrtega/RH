import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto
namespace RelBC
open TensorProduct

/- English proof (translation)
Establish `key : ∀ (s : Finset ι) (w : ι → M), (∀ i ∈ s, w i ∈ Submodule.span R (X i)) → (∀ i, i ∉ s → w i ∈ X i) → f w ∈ T`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro w _ hw; exact h w fun i => hw i (by simp)`. Consider the case `insert i s hi ih`.

Introduce `w h1 h2`. Establish `hup : ∀ x ∈ Submodule.span R (X i), f (Function.update w i x) ∈ T`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Use `ih _ (fun j hj => ?_) (fun j hj => ?_)` and prove the remaining obligations. Establish `hji : j ≠ i` using `fun e => hi (e ▸ hj)`. Rewrite using `[Function.update_of_ne hji]`. Conclude with `h1 j (Finset.mem_insert_of_mem hj)`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hx`. Rewrite using `[Function.update_of_ne hji]`. Conclude with `h2 j (by simp [hji, hj])`.

Consider the case `zero`. Rewrite using `[f.map_coord_zero i (Function.update_self i 0 w)]`. Conclude with `T.zero_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[f.map_update_add]`.

Conclude with `T.add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[f.map_update_smul]`. Conclude with `T.smul_mem c hx`. Use `hup _ (h1 i (Finset.mem_insert_self _ _))` as an intermediate fact.

Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis. Conclude with `key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)`.
-/
theorem multilinear_mem_of_span {R ι M N : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : MultilinearMap R (fun _ : ι => M) N) (X : ι → Set M) (T : Submodule R N)
    (h : ∀ w : ι → M, (∀ i, w i ∈ X i) → f w ∈ T) (v : ι → M)
    (hv : ∀ i, v i ∈ Submodule.span R (X i)) : f v ∈ T := by
  have key : ∀ (s : Finset ι) (w : ι → M), (∀ i ∈ s, w i ∈ Submodule.span R (X i)) → (∀ i, i ∉ s → w i ∈ X i) →
      f w ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ hw; exact h w fun i => hw i (by simp)
    | insert i s hi ih =>
      intro w h1 h2
      have hup : ∀ x ∈ Submodule.span R (X i), f (Function.update w i x) ∈ T := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          refine ih _ (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun e => hi (e ▸ hj)
            rw [Function.update_of_ne hji]
            exact h1 j (Finset.mem_insert_of_mem hj)
          · by_cases hji : j = i
            · subst hji
              rw [Function.update_self]
              exact hx
            · rw [Function.update_of_ne hji]
              exact h2 j (by simp [hji, hj])
        | zero =>
          rw [f.map_coord_zero i (Function.update_self i 0 w)]
          exact T.zero_mem
        | add x y _ _ hx hy =>
          rw [f.map_update_add]
          exact T.add_mem hx hy
        | smul c x _ hx =>
          rw [f.map_update_smul]
          exact T.smul_mem c hx
      have := hup _ (h1 i (Finset.mem_insert_self _ _))
      rwa [Function.update_eq_self] at this
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)

/- English proof (translation)
Establish `hc : (f.liftBaseChange Q : Q ⊗[P] M → N) = φ.liftBaseChange R ∘ (Algebra.IsPushout.cancelBaseChange P Q R₀ R M).symm`. Use function extensionality and compare the values at `z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢`.

Rewrite using `[hx, hy]`. Consider the case `tmul s m => simp [e]`. Establish `hb : Function.Bijective (φ.liftBaseChange R)`. Establish `: (φ.liftBaseChange R : R ⊗[R₀] M → N) = hφ.equiv`. Use function extensionality and compare the values at `z`.

Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul s m => simp`. Rewrite using `[this]`.

Conclude with `hφ.equiv.bijective`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange Q) ?_) fun x => ?_` and prove the remaining obligations. Use `swap`. Express the relevant statement in the definitionally equal form `(f.liftBaseChange Q) (1 ⊗ₜ x) = f x`. Rewrite using `[LinearMap.liftBaseChange_tmul, one_smul]`.

Rewrite using `[hc]`. Conclude with `hb.comp (LinearEquiv.bijective _)`.
-/
theorem isBaseChange_of_pushout {P Q R₀ R M N : Type*} [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [Algebra R₀ R] [IsScalarTower P Q R] [IsScalarTower P R₀ R]
    [Algebra.IsPushout P Q R₀ R] [AddCommGroup M] [Module P M] [Module R₀ M] [IsScalarTower P R₀ M]
    [AddCommGroup N] [Module P N] [Module Q N] [Module R N] [Module R₀ N] [IsScalarTower P Q N] [IsScalarTower Q R N]
    [IsScalarTower R₀ R N] (φ : M →ₗ[R₀] N) (f : M →ₗ[P] N) (e : ∀ x, f x = φ x) (hφ : IsBaseChange R φ) :
    IsBaseChange Q f := by
  have hc : (f.liftBaseChange Q : Q ⊗[P] M → N) =
      φ.liftBaseChange R ∘ (Algebra.IsPushout.cancelBaseChange P Q R₀ R M).symm := by
    funext z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  have hb : Function.Bijective (φ.liftBaseChange R) := by
    have : (φ.liftBaseChange R : R ⊗[R₀] M → N) = hφ.equiv := by
      funext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s m => simp
    rw [this]
    exact hφ.equiv.bijective
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange Q) ?_) fun x => ?_
  swap
  · change (f.liftBaseChange Q) (1 ⊗ₜ x) = f x
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  rw [hc]
  exact hb.comp (LinearEquiv.bijective _)

/- English proof (translation)
Establish `hc : ∀ z : Q ⊗[P] U, j (g.liftBaseChange Q z) = hf.equiv (u.lTensor Q z)`. Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul s m => simp [hg]`. Establish `hinj : Function.Injective (g.liftBaseChange Q)` using `fun x y h => by`. Establish `h2` using `congrArg j h`. Rewrite `h2` using `[hc, hc]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (M := Q) u hu (hf.equiv.injective h2)`.

Establish `hsurj : Function.Surjective (g.liftBaseChange Q)`. Introduce `v`. Establish `h3 : j v ∈ LinearMap.range (j ∘ₗ g.liftBaseChange Q)`. Use `(Submodule.span_le.2 ?_) (hs v)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `⟨1 ⊗ₜ x, by simp [hg]⟩`. Take `⟨z, hz⟩` from `h3`. Conclude with `⟨z, hj hz⟩`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange Q) ⟨hinj, hsurj⟩) fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g.liftBaseChange Q) (1 ⊗ₜ x) = g x`.

Rewrite using `[LinearMap.liftBaseChange_tmul, one_smul]`.
-/
theorem isBaseChange_restrict {P Q U M V N : Type*} [CommRing P] [CommRing Q] [Algebra P Q] [Module.Flat P Q]
    [AddCommGroup U] [Module P U] [AddCommGroup M] [Module P M] [AddCommGroup V] [Module P V] [Module Q V]
    [IsScalarTower P Q V] [AddCommGroup N] [Module P N] [Module Q N] [IsScalarTower P Q N]
    (f : M →ₗ[P] N) (hf : IsBaseChange Q f) (u : U →ₗ[P] M) (hu : Function.Injective u) (g : U →ₗ[P] V)
    (j : V →ₗ[Q] N) (hj : Function.Injective j) (hg : ∀ x, j (g x) = f (u x))
    (hs : ∀ v, j v ∈ Submodule.span Q (Set.range fun x => f (u x))) : IsBaseChange Q g := by
  have hc : ∀ z : Q ⊗[P] U, j (g.liftBaseChange Q z) = hf.equiv (u.lTensor Q z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m => simp [hg]
  have hinj : Function.Injective (g.liftBaseChange Q) := fun x y h => by
    have h2 := congrArg j h
    rw [hc, hc] at h2
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := Q) u hu (hf.equiv.injective h2)
  have hsurj : Function.Surjective (g.liftBaseChange Q) := by
    intro v
    have h3 : j v ∈ LinearMap.range (j ∘ₗ g.liftBaseChange Q) := by
      refine (Submodule.span_le.2 ?_) (hs v)
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, by simp [hg]⟩
    obtain ⟨z, hz⟩ := h3
    exact ⟨z, hj hz⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange Q) ⟨hinj, hsurj⟩) fun x => ?_
  change (g.liftBaseChange Q) (1 ⊗ₜ x) = g x
  rw [LinearMap.liftBaseChange_tmul, one_smul]

/- English proof (translation)
Establish `h1 : ∀ (r : R), ∀ x ∈ X, r • x ∈ Submodule.span Q X`. Introduce `r x hx`. Establish `hr` using `hG r`. Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem c hc => exact Submodule.subset_span (hX c hc x hx)`.

Consider the case `zero => rw [zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_smul]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul q a _ ha => rw [smul_assoc]`.

Conclude with `Submodule.smul_mem _ q ha`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`.

Consider the case `smul r x _ hx`. Establish `h2 : ∀ z ∈ Submodule.span Q X, r • z ∈ Submodule.span Q X`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 r x hx`.

Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul q a _ ha => rw [smul_comm r q a]`.

Conclude with `Submodule.smul_mem _ q ha`. Conclude with `h2 x hx`.
-/
theorem mem_span_of_mem_span {Q R N : Type*} [CommRing Q] [CommRing R] [Algebra Q R] [AddCommGroup N] [Module R N]
    [Module Q N] [IsScalarTower Q R N] (G : Set R) (hG : ∀ r : R, r ∈ Submodule.span Q G) (X : Set N)
    (hX : ∀ c ∈ G, ∀ x ∈ X, c • x ∈ X) {y : N} (hy : y ∈ Submodule.span R X) : y ∈ Submodule.span Q X := by
  have h1 : ∀ (r : R), ∀ x ∈ X, r • x ∈ Submodule.span Q X := by
    intro r x hx
    have hr := hG r
    induction hr using Submodule.span_induction with
    | mem c hc => exact Submodule.subset_span (hX c hc x hx)
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul q a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ q ha
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul r x _ hx =>
    have h2 : ∀ z ∈ Submodule.span Q X, r • z ∈ Submodule.span Q X := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx => exact h1 r x hx
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | smul q a _ ha => rw [smul_comm r q a]; exact Submodule.smul_mem _ q ha
    exact h2 x hx

/- English proof (translation)
Use `letI : Module Q N := Module.compHom N (algebraMap Q R)`. Use `letI : Module P N := Module.compHom N (algebraMap P R)`. Use `haveI : IsScalarTower Q R N := ⟨fun q r n => by`. Express the relevant statement in the definitionally equal form `(q • r) • n = algebraMap Q R q • (r • n)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`.

Use `haveI : IsScalarTower P Q N := ⟨fun p q n => by`. Express the relevant statement in the definitionally equal form `algebraMap Q R (p • q) • n = algebraMap P R p • algebraMap Q R q • n`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]⟩`. Set `f : M →ₗ[P] N` to `{ toFun := φ map_add' := map_add φ map_smul' := fun p x => by`. Express the relevant statement in the definitionally equal form `φ (p • x) = algebraMap P R p • φ x`.

Rewrite using `[← algebraMap_smul R₀ p x, map_smul, ← algebraMap_smul R (algebraMap P R₀ p), ← IsScalarTower.algebraMap_apply] }`. Establish `hf : IsBaseChange Q f` using `isBaseChange_of_pushout φ f (fun _ => rfl) hφ`. Set `jq : V →ₗ[Q] N` to `{ toFun := j, map_add' := map_add j, map_smul' := hq }`. Use `isBaseChange_restrict f hf u hu g jq hj hg fun v => ?_` and prove the remaining obligations. Use `mem_span_of_mem_span (Set.range (algebraMap R₀ R)) (fun r => ?_) _ ?_ (hs v)` and prove the remaining obligations.

Establish `hpo : IsBaseChange Q (IsScalarTower.toAlgHom P R₀ R).toLinearMap` using `Algebra.IsPushout.out`. Proceed by induction on `r using hpo.inductionOn with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul m => exact Submodule.subset_span ⟨m, rfl⟩`. Consider the case `smul s n h => exact Submodule.smul_mem _ s h`.

Consider the case `add a b ha hb => exact Submodule.add_mem _ ha hb`. Introduce and unpack `_ ⟨c, rfl⟩ _ ⟨x, rfl⟩`. Take `⟨x', hx'⟩` from `hU c x`. Use `⟨x', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (u x') = _`.

Rewrite using `[hx', map_smul]`. Conclude with `(algebraMap_smul R c _).symm`.
-/
theorem isBaseChange_core {P Q R₀ R M N U V : Type*} [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [Algebra R₀ R] [IsScalarTower P Q R] [IsScalarTower P R₀ R]
    [Algebra.IsPushout P Q R₀ R] [Module.Flat P Q] [AddCommGroup M] [Module P M] [Module R₀ M] [IsScalarTower P R₀ M]
    [AddCommGroup N] [Module R N] [Module R₀ N] [IsScalarTower R₀ R N] [AddCommGroup U] [Module P U]
    [AddCommGroup V] [Module P V] [Module Q V] [IsScalarTower P Q V]
    (φ : M →ₗ[R₀] N) (hφ : IsBaseChange R φ) (u : U →ₗ[P] M) (hu : Function.Injective u)
    (hU : ∀ (c : R₀) x, ∃ x', u x' = c • u x) (g : U →ₗ[P] V) (j : V →+ N) (hj : Function.Injective j)
    (hq : ∀ (q : Q) v, j (q • v) = algebraMap Q R q • j v) (hg : ∀ x, j (g x) = φ (u x))
    (hs : ∀ v, j v ∈ Submodule.span R (Set.range fun x => φ (u x))) : IsBaseChange Q g := by
  letI : Module Q N := Module.compHom N (algebraMap Q R)
  letI : Module P N := Module.compHom N (algebraMap P R)
  haveI : IsScalarTower Q R N := ⟨fun q r n => by
    change (q • r) • n = algebraMap Q R q • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower P Q N := ⟨fun p q n => by
    change algebraMap Q R (p • q) • n = algebraMap P R p • algebraMap Q R q • n
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]⟩
  let f : M →ₗ[P] N :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun p x => by
        change φ (p • x) = algebraMap P R p • φ x
        rw [← algebraMap_smul R₀ p x, map_smul, ← algebraMap_smul R (algebraMap P R₀ p),
          ← IsScalarTower.algebraMap_apply] }
  have hf : IsBaseChange Q f := isBaseChange_of_pushout φ f (fun _ => rfl) hφ
  let jq : V →ₗ[Q] N := { toFun := j, map_add' := map_add j, map_smul' := hq }
  refine isBaseChange_restrict f hf u hu g jq hj hg fun v => ?_
  refine mem_span_of_mem_span (Set.range (algebraMap R₀ R)) (fun r => ?_) _ ?_ (hs v)
  · have hpo : IsBaseChange Q (IsScalarTower.toAlgHom P R₀ R).toLinearMap := Algebra.IsPushout.out
    induction r using hpo.inductionOn with
    | zero => exact Submodule.zero_mem _
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n h => exact Submodule.smul_mem _ s h
    | add a b ha hb => exact Submodule.add_mem _ ha hb
  · rintro _ ⟨c, rfl⟩ _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hU c x
    refine ⟨x', ?_⟩
    change φ (u x') = _
    rw [hx', map_smul]
    exact (algebraMap_smul R c _).symm

/- English proof (translation)
Use `set T := Submodule.span R (Set.range fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) with hT`. Establish `hgen : ∀ (h₀ : R₀) (h : Fin a → R₀), (h₀ ∈ I₀ ∨ ∃ k, h k ∈ I₀) → form K (θ h₀) (fun k => θ (h k)) ∈ T` using `fun h₀ h hh => Submodule.subset_span ⟨⟨form K h₀ h, Submodule.subset_span ⟨h₀, h, hh, rfl⟩⟩, omMap_form θ h₀ h⟩`. Establish `hW : ∀ (Y : Fin a → Set R₀) (c : R), (∀ h : Fin a → R₀, (∀ i, h i ∈ Y i) → c • exteriorPower.ιMulti R a (fun i => KaehlerDifferential.D K R (θ (h i))) ∈ T) → ∀ v : Fin a → Ω[R⁄K], (∀ i, v i ∈ Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' Y i)) → c • exteriorPowe …`. Introduce `Y c hP v hv`. Use `multilinear_mem_of_span (exteriorPower.ιMulti R a (M := Ω[R⁄K])).toMultilinearMap (fun i => (fun y => KaehlerDifferential.D K R (θ y)) '' Y i) (T.comap (c • LinearMap.id)) (fun w hw => by choose h hh hw using hw` as an intermediate fact.

Establish `e : w = fun i => KaehlerDifferential.D K R (θ (h i))` using `funext fun i => (hw i).symm`. Substitute `e` using the available equality. Conclude with `hP h hh) v hv`. Conclude with `this`. Establish `hJ1 : ∀ g₀ ∈ J, ∀ v : Fin a → Ω[R⁄K], g₀ • exteriorPower.ιMulti R a v ∈ T`.

Introduce `g₀ hg v`. Establish `hg'` using `hJ hg`. Use `clear hg`. Proceed by induction on `hg' using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨y, hy, rfl⟩` from `hx`. Use `hW (fun _ => Set.univ) (θ y) (fun h _ => hgen y h (Or.inl hy)) v fun i => ?_` and prove the remaining obligations. Rewrite using `[Set.image_univ]`. Conclude with `hD (v i)`. Consider the case `zero => rw [zero_smul]`.

Conclude with `T.zero_mem`. Consider the case `add x y _ _ hx hy => rw [add_smul]`. Conclude with `T.add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_eq_mul, mul_smul]`. Conclude with `T.smul_mem c hx`.

Use `set W := Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' (I₀ : Set R₀)) with hWdef`. Establish `hDy : ∀ y ∈ I₀, KaehlerDifferential.D K R (θ y) ∈ W` using `fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩`. Establish `hWs : ∀ y ∈ I₀, ∀ ω : Ω[R⁄K], θ y • ω ∈ W`. Introduce `y hy ω`. Establish `hω` using `hD ω`.

Proceed by induction on `hω using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Establish `e : KaehlerDifferential.D K R (θ (y * h)) = θ y • KaehlerDifferential.D K R (θ h) + θ h • KaehlerDifferential.D K R (θ y)`. Rewrite using `[map_mul, Derivation.leibniz]`.

Establish `e2 : θ y • KaehlerDifferential.D K R (θ h) = KaehlerDifferential.D K R (θ (y * h)) - θ h • KaehlerDifferential.D K R (θ y)`. Rewrite using `[e, add_sub_cancel_right]`. Express the relevant statement in the definitionally equal form `θ y • KaehlerDifferential.D K R (θ h) ∈ W`. Rewrite using `[e2]`. Conclude with `W.sub_mem (hDy _ (I₀.mul_mem_right h hy)) (W.smul_mem _ (hDy y hy))`.

Consider the case `zero => rw [smul_zero]`. Conclude with `W.zero_mem`. Consider the case `add x z _ _ hx hz => rw [smul_add]`. Conclude with `W.add_mem hx hz`. Consider the case `smul c x _ hx => rw [smul_comm]`.

Conclude with `W.smul_mem c hx`. Establish `hJ2 : ∀ g ∈ J, KaehlerDifferential.D K R g ∈ W ∧ ∀ ω : Ω[R⁄K], g • ω ∈ W`. Introduce `g hg`. Establish `hg'` using `hJ hg`. Use `clear hg`.

Proceed by induction on `hg' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `⟨hDy y hy, hWs y hy⟩`. Consider the case `zero => exact ⟨by rw [map_zero]; exact W.zero_mem, fun ω => by rw [zero_smul]; exact W.zero_mem⟩`.

Consider the case `add x y _ _ hx hy`. Conclude with `⟨by rw [map_add]; exact W.add_mem hx.1 hy.1, fun ω => by rw [add_smul]; exact W.add_mem (hx.2 ω) (hy.2 ω)⟩`. Consider the case `smul c x _ hx`. Use `⟨?_, fun ω => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Derivation.leibniz]`.

Conclude with `W.add_mem (W.smul_mem c hx.1) (hx.2 _)`. Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `W.smul_mem c (hx.2 ω)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g₀, g, hg, rfl⟩`.

Break down `hg with hg | ⟨k, hk⟩` into its components or cases. Conclude with `hJ1 g₀ hg _`. Establish `h3` using `hW (fun i => if i = k then (I₀ : Set R₀) else Set.univ) 1 (fun h hh => by`. Establish `h4` using `hgen 1 h (Or.inr ⟨k, by simpa using hh k⟩)`. Rewrite `h4` using `[map_one]`.

Conclude with `h4) (fun i => KaehlerDifferential.D K R (g i)) (fun i => by`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using `using (hJ2 _ hk).1`. Simplify using `only [if_neg hi, Set.image_univ]`.

Conclude with `hD _)`. Rewrite `h3` using `[one_smul]`. Conclude with `T.smul_mem g₀ h3`.
-/
theorem relOm_le_span {K R₀ R : Type} [CommRing K] [CommRing R₀] [CommRing R] [Algebra K R₀] [Algebra K R]
    (θ : R₀ →ₐ[K] R)
    (hD : ∀ ω : Ω[R⁄K], ω ∈ Submodule.span R (Set.range fun h => KaehlerDifferential.D K R (θ h)))
    (I₀ : Ideal R₀) (J : Ideal R) (hJ : J ≤ Ideal.span (θ '' (I₀ : Set R₀))) (a : ℕ) :
    relOm K J a ≤ Submodule.span R (Set.range fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) := by
  set T := Submodule.span R (Set.range fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) with hT
  have hgen : ∀ (h₀ : R₀) (h : Fin a → R₀), (h₀ ∈ I₀ ∨ ∃ k, h k ∈ I₀) →
      form K (θ h₀) (fun k => θ (h k)) ∈ T := fun h₀ h hh =>
    Submodule.subset_span ⟨⟨form K h₀ h, Submodule.subset_span ⟨h₀, h, hh, rfl⟩⟩, omMap_form θ h₀ h⟩
  have hW : ∀ (Y : Fin a → Set R₀) (c : R),
      (∀ h : Fin a → R₀, (∀ i, h i ∈ Y i) →
        c • exteriorPower.ιMulti R a (fun i => KaehlerDifferential.D K R (θ (h i))) ∈ T) →
      ∀ v : Fin a → Ω[R⁄K], (∀ i, v i ∈ Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' Y i)) →
      c • exteriorPower.ιMulti R a v ∈ T := by
    intro Y c hP v hv
    have := multilinear_mem_of_span (exteriorPower.ιMulti R a (M := Ω[R⁄K])).toMultilinearMap
      (fun i => (fun y => KaehlerDifferential.D K R (θ y)) '' Y i) (T.comap (c • LinearMap.id)) (fun w hw => by
        choose h hh hw using hw
        have e : w = fun i => KaehlerDifferential.D K R (θ (h i)) := funext fun i => (hw i).symm
        subst e
        exact hP h hh) v hv
    exact this
  have hJ1 : ∀ g₀ ∈ J, ∀ v : Fin a → Ω[R⁄K], g₀ • exteriorPower.ιMulti R a v ∈ T := by
    intro g₀ hg v
    have hg' := hJ hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine hW (fun _ => Set.univ) (θ y) (fun h _ => hgen y h (Or.inl hy)) v fun i => ?_
      rw [Set.image_univ]
      exact hD (v i)
    | zero => rw [zero_smul]; exact T.zero_mem
    | add x y _ _ hx hy => rw [add_smul]; exact T.add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_smul]; exact T.smul_mem c hx
  set W := Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' (I₀ : Set R₀)) with hWdef
  have hDy : ∀ y ∈ I₀, KaehlerDifferential.D K R (θ y) ∈ W := fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hWs : ∀ y ∈ I₀, ∀ ω : Ω[R⁄K], θ y • ω ∈ W := by
    intro y hy ω
    have hω := hD ω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e : KaehlerDifferential.D K R (θ (y * h)) =
          θ y • KaehlerDifferential.D K R (θ h) + θ h • KaehlerDifferential.D K R (θ y) := by
        rw [map_mul, Derivation.leibniz]
      have e2 : θ y • KaehlerDifferential.D K R (θ h) =
          KaehlerDifferential.D K R (θ (y * h)) - θ h • KaehlerDifferential.D K R (θ y) := by
        rw [e, add_sub_cancel_right]
      change θ y • KaehlerDifferential.D K R (θ h) ∈ W
      rw [e2]
      exact W.sub_mem (hDy _ (I₀.mul_mem_right h hy)) (W.smul_mem _ (hDy y hy))
    | zero => rw [smul_zero]; exact W.zero_mem
    | add x z _ _ hx hz => rw [smul_add]; exact W.add_mem hx hz
    | smul c x _ hx => rw [smul_comm]; exact W.smul_mem c hx
  have hJ2 : ∀ g ∈ J, KaehlerDifferential.D K R g ∈ W ∧ ∀ ω : Ω[R⁄K], g • ω ∈ W := by
    intro g hg
    have hg' := hJ hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨hDy y hy, hWs y hy⟩
    | zero => exact ⟨by rw [map_zero]; exact W.zero_mem, fun ω => by rw [zero_smul]; exact W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨by rw [map_add]; exact W.add_mem hx.1 hy.1, fun ω => by rw [add_smul]; exact W.add_mem (hx.2 ω) (hy.2 ω)⟩
    | smul c x _ hx =>
      refine ⟨?_, fun ω => ?_⟩
      · rw [smul_eq_mul, Derivation.leibniz]
        exact W.add_mem (W.smul_mem c hx.1) (hx.2 _)
      · rw [smul_eq_mul, mul_smul]
        exact W.smul_mem c (hx.2 ω)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g₀, g, hg, rfl⟩
  rcases hg with hg | ⟨k, hk⟩
  · exact hJ1 g₀ hg _
  · have h3 := hW (fun i => if i = k then (I₀ : Set R₀) else Set.univ) 1 (fun h hh => by
      have h4 := hgen 1 h (Or.inr ⟨k, by simpa using hh k⟩)
      rw [map_one] at h4
      exact h4) (fun i => KaehlerDifferential.D K R (g i)) (fun i => by
      by_cases hi : i = k
      · subst hi
        simpa using (hJ2 _ hk).1
      · simp only [if_neg hi, Set.image_univ]
        exact hD _)
    rw [one_smul] at h3
    exact T.smul_mem g₀ h3

/- English proof (translation)
Use `letI : Algebra R₀ R := θ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower K R₀ R := .of_algHom θ`. Use `haveI : IsScalarTower P R₀ R := .of_algebraMap_eq fun p => (hθ p).symm`. Use `haveI hpo : Algebra.IsPushout P Q R₀ R := ⟨by`. Establish `e : (IsScalarTower.toAlgHom P R₀ R).toLinearMap = f` using `LinearMap.ext fun x => (hf x).symm`.

Rewrite using `[e]`. Conclude with `hb⟩`. Use `haveI : Algebra.IsPushout P R₀ Q R := Algebra.IsPushout.symm hpo`. Use `haveI : Algebra.FormallyEtale R₀ R := Algebra.FormallyEtale.of_equiv (Algebra.IsPushout.equiv P R₀ Q R)`. Establish `h1` using `KaehlerDifferential.isBaseChange_of_formallyEtale K R₀ R`.

Establish `hD : ∀ ω : Ω[R⁄K], ω ∈ Submodule.span R (Set.range fun h => KaehlerDifferential.D K R (θ h))`. Introduce `ω`. Proceed by induction on `ω using h1.inductionOn with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `smul s n h => exact Submodule.smul_mem _ s h`.

Consider the case `add a b ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `tmul m`. Establish `hm : m ∈ (⊤ : Submodule R₀ Ω[R₀⁄K])` using `trivial`. Rewrite `hm` using `[← KaehlerDifferential.span_range_derivation]`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`. Rewrite using `[KaehlerDifferential.map_D]`. Conclude with `Submodule.subset_span ⟨y, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[map_smul, ← algebraMap_smul R c]`.

Conclude with `Submodule.smul_mem _ _ hx`. Establish `h2` using `GlobalTheory.TopForm.isBaseChange_exteriorPower h1 a`. Establish `he : ∀ ω : Om K R₀ a, GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) ω = omMap θ a ω`. Introduce `ω`. Establish `hs : ω ∈ (⊤ : Submodule R₀ (Om K R₀ a))` using `trivial`.

Rewrite `hs` using `[← exteriorPower.ιMulti_span]`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Rewrite using `[GlobalTheory.exteriorPowerMapOver_ιMulti, omMap_ιMulti]`.

Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `smul c x _ hx`. Rewrite using `[map_smul, omMap_smul, hx]`. Conclude with `(algebraMap_smul R c _).symm`.

Use `isBaseChange_core (R₀ := R₀) (R := R) _ h2 ((relOm K I₀ a).subtype.restrictScalars P) Subtype.val_injective (fun c x => ⟨c • x, rfl⟩) g j hj hq (fun x => by rw [hg]; exact (he _).symm) fun v => ?_` and prove the remaining obligations. Establish `h3` using `relOm_le_span θ hD I₀ J hJ a (hr v)`. Establish `hfun : (fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) = fun x : relOm K I₀ a => GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) (x : Om K R₀ a)`. Use function extensionality and compare the values at `fun x => (he _).symm`. Rewrite `h3` using `[hfun]`.

Conclude with `h3`.
-/
theorem isBaseChange_relOm {K P Q R₀ R : Type} [CommRing K] [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra K R₀] [Algebra K R] [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [IsScalarTower P Q R]
    [Algebra.Etale P Q] (θ : R₀ →ₐ[K] R) (hθ : ∀ p, θ (algebraMap P R₀ p) = algebraMap P R p)
    (f : R₀ →ₗ[P] R) (hf : ∀ x, f x = θ x) (hb : IsBaseChange Q f)
    (I₀ : Ideal R₀) (J : Ideal R) (hJ : J ≤ Ideal.span (θ '' (I₀ : Set R₀))) (a : ℕ)
    {V : Type} [AddCommGroup V] [Module P V] [Module Q V] [IsScalarTower P Q V] (j : V →+ Om K R a)
    (hj : Function.Injective j) (hq : ∀ (q : Q) v, j (q • v) = algebraMap Q R q • j v)
    (hr : ∀ v, j v ∈ relOm K J a) (g : relOm K I₀ a →ₗ[P] V)
    (hg : ∀ x, j (g x) = omMap θ a (x : Om K R₀ a)) : IsBaseChange Q g := by
  letI : Algebra R₀ R := θ.toRingHom.toAlgebra
  haveI : IsScalarTower K R₀ R := .of_algHom θ
  haveI : IsScalarTower P R₀ R := .of_algebraMap_eq fun p => (hθ p).symm
  haveI hpo : Algebra.IsPushout P Q R₀ R := ⟨by
    have e : (IsScalarTower.toAlgHom P R₀ R).toLinearMap = f := LinearMap.ext fun x => (hf x).symm
    rw [e]
    exact hb⟩
  haveI : Algebra.IsPushout P R₀ Q R := Algebra.IsPushout.symm hpo
  haveI : Algebra.FormallyEtale R₀ R := Algebra.FormallyEtale.of_equiv (Algebra.IsPushout.equiv P R₀ Q R)
  have h1 := KaehlerDifferential.isBaseChange_of_formallyEtale K R₀ R
  have hD : ∀ ω : Ω[R⁄K], ω ∈ Submodule.span R (Set.range fun h => KaehlerDifferential.D K R (θ h)) := by
    intro ω
    induction ω using h1.inductionOn with
    | zero => exact Submodule.zero_mem _
    | smul s n h => exact Submodule.smul_mem _ s h
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul m =>
      have hm : m ∈ (⊤ : Submodule R₀ Ω[R₀⁄K]) := trivial
      rw [← KaehlerDifferential.span_range_derivation] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨y, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [map_smul, ← algebraMap_smul R c]
        exact Submodule.smul_mem _ _ hx
  have h2 := GlobalTheory.TopForm.isBaseChange_exteriorPower h1 a
  have he : ∀ ω : Om K R₀ a, GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) ω = omMap θ a ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule R₀ (Om K R₀ a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti, omMap_ιMulti]
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [map_smul, omMap_smul, hx]
      exact (algebraMap_smul R c _).symm
  refine isBaseChange_core (R₀ := R₀) (R := R) _ h2 ((relOm K I₀ a).subtype.restrictScalars P) Subtype.val_injective
    (fun c x => ⟨c • x, rfl⟩) g j hj hq (fun x => by rw [hg]; exact (he _).symm) fun v => ?_
  have h3 := relOm_le_span θ hD I₀ J hJ a (hr v)
  have hfun : (fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) =
      fun x : relOm K I₀ a => GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) (x : Om K R₀ a) :=
    funext fun x => (he _).symm
  rw [hfun] at h3
  exact h3

end RelBC

/- English proof (translation)
Use `haveI := etale_Aa C`. Use `letI i1 : Algebra (Aa C) (C.R S) := inferInstanceAs (Algebra (Aa C) (Rb C S))`. Use `letI i2 : Algebra (Bp K n d) (C.R S) := inferInstanceAs (Algebra (Bp K n d) (Rb C S))`. Use `haveI i3 : IsScalarTower (Bp K n d) (Aa C) (C.R S) := inferInstanceAs (IsScalarTower (Bp K n d) (Aa C) (Rb C S))`. Establish `hJ : C.I S ≤ Ideal.span (θ '' (I0 n K S : Set (R0 K n d S)))`.

Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Use `Ideal.subset_span ⟨mon K (oneE (Sum.inr k)) (oneE_mem S _), Ideal.subset_span ⟨k, hk, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← poly_X, hθ]`. Simplify using `[toR, phi]`.

Conclude with `RelBC.isBaseChange_relOm (K := K) (P := Bp K n d) (Q := Aa C) (R₀ := R0 K n d S) (R := C.R S) θ hθ (thetaLin C θ hθ) (fun _ => rfl) hb (I0 n K S) (C.I S) hJ a (V := relA C S a) (AddSubgroupClass.subtype (relOm K (C.I S) a)) Subtype.val_injective (fun _ _ => rfl) (fun v => v.2) (p …`.
-/
theorem isBaseChange_psi {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)
    {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ hθ)) (a : ℕ) : IsBaseChange (Aa C) (psi C θ hθ a) := by
  haveI := etale_Aa C
  letI i1 : Algebra (Aa C) (C.R S) := inferInstanceAs (Algebra (Aa C) (Rb C S))
  letI i2 : Algebra (Bp K n d) (C.R S) := inferInstanceAs (Algebra (Bp K n d) (Rb C S))
  haveI i3 : IsScalarTower (Bp K n d) (Aa C) (C.R S) := inferInstanceAs (IsScalarTower (Bp K n d) (Aa C) (Rb C S))
  have hJ : C.I S ≤ Ideal.span (θ '' (I0 n K S : Set (R0 K n d S))) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Ideal.subset_span ⟨mon K (oneE (Sum.inr k)) (oneE_mem S _), Ideal.subset_span ⟨k, hk, rfl⟩, ?_⟩
    rw [← poly_X, hθ]
    simp [toR, phi]
  exact RelBC.isBaseChange_relOm (K := K) (P := Bp K n d) (Q := Aa C) (R₀ := R0 K n d S) (R := C.R S) θ hθ
    (thetaLin C θ hθ) (fun _ => rfl) hb (I0 n K S) (C.I S) hJ a
    (V := relA C S a) (AddSubgroupClass.subtype (relOm K (C.I S) a)) Subtype.val_injective (fun _ _ => rfl)
    (fun v => v.2) (psi C θ hθ a) (fun _ => rfl)

end GlobalTheory.CompanionTheory.SurjectionOntoH4
