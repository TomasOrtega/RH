import Mathlib
import GroundTheory.ProfiniteCohomology.CoinducedModules
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology Filter Topology

universe u

section FinTuple

variable {α : Type*} {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]`.

Simplify using the standard rewrite rules.
-/
theorem contractNth_zero_cons (op : α → α → α) (x : α) (g : Fin (n + 1) → α) :
    Fin.contractNth 0 op (Fin.cons x g : Fin (n + 2) → α) =
      Fin.cons (op x (g 0)) (fun i => g i.succ) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
    simp
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]
    simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]`. Simplify using the standard rewrite rules. Break down `lt_trichotomy (i : ℕ) j with h | h | h` into its components or cases.

Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]`. Simplify using `only [Fin.cons_succ, ← Fin.succ_castSucc]`. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ h]`. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h)]`. Simplify using `only [Fin.cons_succ, ← Fin.succ_castSucc]`.

Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h]`. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]`. Simplify using `only [Fin.cons_succ]`. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h]`.
-/
theorem contractNth_succ_cons (op : α → α → α) (x : α) (g : Fin (n + 1) → α) (j : Fin (n + 1)) :
    Fin.contractNth j.succ op (Fin.cons x g : Fin (n + 2) → α) =
      Fin.cons x (Fin.contractNth j op g) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
    simp
  · rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ h]

end FinTuple

section Tube

variable {G : Type*} [TopologicalSpace G] [CompactSpace G]

/- English proof (translation)
Establish `key` using `isCompact_univ.eventually_forall_of_forall_eventually (x₀ := g₀) (K := (Set.univ : Set G)) (P := fun g x => f (Fin.cons x g) = f (Fin.cons x g₀)) ?_`. Conclude with `key.mono fun g hg x => hg x (Set.mem_univ x)`. Introduce `y _`. Establish `hc1 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 z.1 : Fin (n + 1) → G)` using `Continuous.finCons (A := fun _ => G) continuous_snd continuous_fst`. Establish `hc2 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 g₀ : Fin (n + 1) → G)` using `Continuous.finCons (A := fun _ => G) continuous_snd continuous_const`.

Establish `h1` using `(hf.comp_continuous hc1).eventually_eq (g₀, y)`. Establish `h2` using `(hf.comp_continuous hc2).eventually_eq (g₀, y)`. Use `filter_upwards [h1, h2] with z hz1 hz2`. Simplify using `only [Function.comp_apply] at hz1 hz2`. Rewrite using `[hz1, hz2]`.
-/
theorem eventually_forall_cons_eq {n : ℕ} {Y : Type*} {f : (Fin (n + 1) → G) → Y}
    (hf : IsLocallyConstant f) (g₀ : Fin n → G) :
    ∀ᶠ g in 𝓝 g₀, ∀ x : G, f (Fin.cons x g) = f (Fin.cons x g₀) := by
  have key := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := g₀)
    (K := (Set.univ : Set G)) (P := fun g x => f (Fin.cons x g) = f (Fin.cons x g₀)) ?_
  · exact key.mono fun g hg x => hg x (Set.mem_univ x)
  intro y _
  have hc1 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 z.1 : Fin (n + 1) → G) :=
    Continuous.finCons (A := fun _ => G) continuous_snd continuous_fst
  have hc2 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 g₀ : Fin (n + 1) → G) :=
    Continuous.finCons (A := fun _ => G) continuous_snd continuous_const
  have h1 := (hf.comp_continuous hc1).eventually_eq (g₀, y)
  have h2 := (hf.comp_continuous hc2).eventually_eq (g₀, y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]

end Tube

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]

noncomputable def coindHomotopyApply {n : ℕ} (f : (Fin (n + 1) → G) → LocallyConstant G X)
    (hf : IsLocallyConstant f) (g : Fin n → G) : LocallyConstant G X :=
  ⟨fun x => f (Fin.cons x g) 1,
    (hf.comp_continuous (continuous_id.finCons continuous_const)).comp fun φ => φ 1⟩

omit [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup X] [Module k X] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindHomotopyApply_apply {n : ℕ} (f : (Fin (n + 1) → G) → LocallyConstant G X)
    (hf : IsLocallyConstant f) (g : Fin n → G) (x : G) :
    coindHomotopyApply f hf g x = f (Fin.cons x g) 1 :=
  rfl

omit [IsTopologicalGroup G] [AddCommGroup X] [Module k X] in
/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g₀`. Use `filter_upwards [eventually_forall_cons_eq hf g₀] with g hg`. Conclude with `LocallyConstant.ext fun x => by simp [hg x]`.
-/
theorem isLocallyConstant_coindHomotopyApply {n : ℕ}
    (f : (Fin (n + 1) → G) → LocallyConstant G X) (hf : IsLocallyConstant f) :
    IsLocallyConstant (coindHomotopyApply f hf) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  filter_upwards [eventually_forall_cons_eq hf g₀] with g hg
  exact LocallyConstant.ext fun x => by simp [hg x]

variable (k X) in

noncomputable def coindHomotopy (n : ℕ) :
    locallyConstantCochains (discreteCoind k G X) (n + 1) →ₗ[k]
      locallyConstantCochains (discreteCoind k G X) n where
  toFun f := ⟨coindHomotopyApply (X := X) f.1 f.2,
    isLocallyConstant_coindHomotopyApply (X := X) f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompactSpace G] in

/- English proof (translation)
Establish `hsum : ∀ (F : Fin (n + 1) → LocallyConstant G X) (y : G), (∑ i, F i) y = ∑ i, F i y` using `fun F y => map_sum (LocallyConstant.evalAddMonoidHom y) F Finset.univ`. Establish `hs : ∀ j : Fin (n + 1), ((-1 : k) ^ ((j : ℕ) + 1 + 1)) = -((-1 : k) ^ ((j : ℕ) + 1))` using `fun j => by`. Rewrite using `[pow_succ, mul_neg_one]`. Rewrite using `[hψ, inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := n + 1)]`. Simplify using `only [LocallyConstant.coe_add, Pi.add_apply, hsum, LocallyConstant.coe_smul, Pi.smul_apply, discreteCoindRep_apply, Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons, hφ, one_mul, Fin.val_zero, Fin.val_succ, hs]`.

Simplify using `only [zero_add, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem coindHomotopy_identity_apply {n : ℕ}
    (f : (Fin (n + 1) → G) → LocallyConstant G X) (φ : (Fin n → G) → LocallyConstant G X)
    (ψ : (Fin (n + 1) → G) → LocallyConstant G X)
    (hφ : ∀ g x, φ g x = f (Fin.cons x g) 1)
    (hψ : ∀ g x, ψ g x =
      ((inhomogeneousCochains.d (discreteCoind k G X) (n + 1)).hom f (Fin.cons x g) :
        LocallyConstant G X) 1)
    (g : Fin (n + 1) → G) (x : G) :
    ((inhomogeneousCochains.d (discreteCoind k G X) n).hom φ g : LocallyConstant G X) x +
      ψ g x = f g x := by
  have hsum : ∀ (F : Fin (n + 1) → LocallyConstant G X) (y : G), (∑ i, F i) y = ∑ i, F i y :=
    fun F y => map_sum (LocallyConstant.evalAddMonoidHom y) F Finset.univ
  have hs : ∀ j : Fin (n + 1), ((-1 : k) ^ ((j : ℕ) + 1 + 1)) =
      -((-1 : k) ^ ((j : ℕ) + 1)) := fun j => by
    rw [pow_succ, mul_neg_one]
  rw [hψ, inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply,
    Fin.sum_univ_succ (n := n + 1)]
  simp only [LocallyConstant.coe_add, Pi.add_apply, hsum, LocallyConstant.coe_smul,
    Pi.smul_apply, discreteCoindRep_apply, Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons,
    contractNth_succ_cons, hφ, one_mul, Fin.val_zero, Fin.val_succ, hs]
  simp only [zero_add, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib]
  abel

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Apply `LocallyConstant.ext` to reduce the goal to its premises. Introduce `x`. Conclude with `coindHomotopy_identity_apply (k := k) f.1 _ _ (fun _ _ => rfl) (fun _ _ => rfl) g x`.
-/
theorem coindHomotopy_identity (n : ℕ)
    (f : locallyConstantCochains (discreteCoind k G X) (n + 1)) :
    (dLocallyConstant (discreteCoind k G X) n).hom (coindHomotopy k X n f) +
      coindHomotopy k X (n + 1) ((dLocallyConstant (discreteCoind k G X) (n + 1)).hom f) = f := by
  apply Subtype.ext
  funext g
  apply LocallyConstant.ext
  intro x
  exact coindHomotopy_identity_apply (k := k) f.1 _ _ (fun _ _ => rfl) (fun _ _ => rfl) g x

variable (k G X) in

/- English proof (translation)
Rewrite using `[cohomology, ← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]`. Introduce `f hf`. Set `f' : locallyConstantCochains (discreteCoind k G X) (n + 1)` to `f`. Establish `hf' : (dLocallyConstant (discreteCoind k G X) (n + 1)).hom f' = 0`. Express the relevant statement in the definitionally equal form `((cochainsComplex (discreteCoind k G X)).d (n + 1) (n + 2)).hom f = 0 at hf`.

Rewrite `hf` using `[cochainsComplex_d]`. Conclude with `hf`. Use `⟨coindHomotopy k X n f', ?_⟩` and prove the remaining obligations. Use `coindHomotopy_identity n f'` as an intermediate fact. Rewrite `this` using `[hf', map_zero, add_zero]`.

Express the relevant statement in the definitionally equal form `((cochainsComplex (discreteCoind k G X)).d n (n + 1)).hom (coindHomotopy k X n f') = f`. Rewrite using `[cochainsComplex_d]`. Conclude with `this`.
-/
theorem isZero_cohomology_discreteCoind (n : ℕ) :
    Limits.IsZero (cohomology (discreteCoind k G X) (n + 1)) := by
  rw [cohomology, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f hf
  let f' : locallyConstantCochains (discreteCoind k G X) (n + 1) := f
  have hf' : (dLocallyConstant (discreteCoind k G X) (n + 1)).hom f' = 0 := by
    change ((cochainsComplex (discreteCoind k G X)).d (n + 1) (n + 2)).hom f = 0 at hf
    rw [cochainsComplex_d] at hf
    exact hf
  refine ⟨coindHomotopy k X n f', ?_⟩
  have := coindHomotopy_identity n f'
  rw [hf', map_zero, add_zero] at this
  change ((cochainsComplex (discreteCoind k G X)).d n (n + 1)).hom (coindHomotopy k X n f') = f
  rw [cochainsComplex_d]
  exact this

variable (k G X) in

noncomputable def cohomologyZeroDiscreteCoindIso :
    cohomology (discreteCoind k G X) 0 ≅ ModuleCat.of k X :=
  H0Iso (discreteCoind k G X) ≪≫ (invariantsDiscreteCoindEquiv k G X).toModuleIso

end GroundTheory.ProfCoh
