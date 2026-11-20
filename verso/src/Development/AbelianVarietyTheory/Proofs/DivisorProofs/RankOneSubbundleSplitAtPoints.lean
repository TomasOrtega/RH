import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.QCoh

namespace GlobalTheory.VB

/- English proof (translation)
Set `p : T → Submodule κ (Fin k → κ)` to `fun t => { carrier := {c | ∑ i, σ t (c i) * u t i ∈ IsLocalRing.maximalIdeal (R t)} add_mem' := fun {a b} ha hb => by`. Simplify `Ideal.add_mem _ (Set.mem_setOf.1 ha) (Set.mem_setOf.1 hb)` using `[add_mul, Finset.sum_add_distrib]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun a c hc => by`. Simplify `Ideal.mul_mem_left _ (σ t a) (Set.mem_setOf.1 hc) }` using `[Finset.mul_sum, mul_assoc]`.

Take `⟨c, hc⟩` from `Submodule.exists_forall_notMem_of_forall_ne_top p fun t ht => by`. Take `⟨i, hi⟩` from `hu t`. Establish `h : ∑ j, σ t ((Pi.single i 1 : Fin k → κ) j) * u t j ∈ IsLocalRing.maximalIdeal (R t)` using `ht.ge (Submodule.mem_top (x := Pi.single i 1))`. Rewrite `h` using `[Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one, one_mul]`. Conclude with `h hi`.

Conclude with `⟨c, fun t => not_not.1 (hc t)⟩`.
-/
theorem exists_forall_isUnit_sum_mul {κ : Type} [Field κ] [Infinite κ] {T : Type} [Finite T]
    (R : T → Type) [∀ t, CommRing (R t)] [∀ t, IsLocalRing (R t)] (σ : ∀ t, κ →+* R t) {k : ℕ}
    (u : ∀ t, Fin k → R t) (hu : ∀ t, ∃ i, IsUnit (u t i)) :
    ∃ c : Fin k → κ, ∀ t, IsUnit (∑ i, σ t (c i) * u t i) := by
  let p : T → Submodule κ (Fin k → κ) := fun t =>
    { carrier := {c | ∑ i, σ t (c i) * u t i ∈ IsLocalRing.maximalIdeal (R t)}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul, Finset.sum_add_distrib] using Ideal.add_mem _ (Set.mem_setOf.1 ha) (Set.mem_setOf.1 hb)
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simpa [Finset.mul_sum, mul_assoc] using Ideal.mul_mem_left _ (σ t a) (Set.mem_setOf.1 hc) }
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p fun t ht => by
    obtain ⟨i, hi⟩ := hu t
    have h : ∑ j, σ t ((Pi.single i 1 : Fin k → κ) j) * u t j ∈ IsLocalRing.maximalIdeal (R t) :=
      ht.ge (Submodule.mem_top (x := Pi.single i 1))
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
      one_mul] at h
    exact h hi
  exact ⟨c, fun t => not_not.1 (hc t)⟩

/- English proof (translation)
Take `⟨v, hv⟩` from `h.exists_left_inv`. Use `⟨(v • l).smulRight (g 0), g.ext fun i => ?_⟩` and prove the remaining obligations. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Simplify using `[hv]`.
-/
theorem exists_retraction_of_isUnit {R P M : Type} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] (g : Module.Basis (Fin 1) R P) (f : P →ₗ[R] M) (l : M →ₗ[R] R)
    (h : IsUnit (l (f (g 0)))) : ∃ ρ : M →ₗ[R] P, ρ ∘ₗ f = LinearMap.id := by
  obtain ⟨v, hv⟩ := h.exists_left_inv
  refine ⟨(v • l).smulRight (g 0), g.ext fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [hv]

variable {X : Scheme.{0}} {F G : X.Modules}

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun ψ : G ⟶ F => stalkLinear ψ x) fun a b => stalkLinear_add a b x) φ s`.
-/
theorem stalkLinear_finset_sum {ι : Type} (s : Finset ι) (φ : ι → (G ⟶ F)) (x : X) :
    stalkLinear (∑ i ∈ s, φ i) x = ∑ i ∈ s, stalkLinear (φ i) x :=
  map_sum (AddMonoidHom.mk' (fun ψ : G ⟶ F => stalkLinear ψ x) fun a b => stalkLinear_add a b x) φ s

/- English proof (translation)
Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[stalkLinear_germ, smulHom_app_apply, germ_smul]`. Conclude with `congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)`.
-/
theorem stalkLinear_smulHom_apply (a : Γ(X, ⊤)) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinear (smulHom F a) x t = X.presheaf.germ ⊤ x trivial a • t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ, smulHom_app_apply, germ_smul]
  exact congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)

/- English proof (translation)
Use `Abelian.hasFiniteBiproducts (C := X.Modules)` as an intermediate fact. Set `e` to `biproduct.isoCoproduct fun _ : Fin k => G`. Establish `he : e.hom ≫ φ = ∑ i, biproduct.π (fun _ : Fin k => G) i ≫ Sigma.ι (fun _ : Fin k => G) i ≫ φ`. Rewrite using `[biproduct.isoCoproduct_hom, biproduct.desc_eq, Preadditive.sum_comp]`. Simplify using `only [Category.assoc]`.

Use `top_le_iff.1 fun t _ => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `stalkLinear_surjective (e.hom ≫ φ) x t`. Rewrite using `[he, stalkLinear_finset_sum, LinearMap.sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[stalkLinear_comp]`.

Conclude with `h i _`.
-/
theorem eq_top_of_epi_sigma {k : ℕ} (φ : (∐ fun _ : Fin k => G) ⟶ F) [Epi φ] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
    (h : ∀ i t, stalkLinear (Sigma.ι (fun _ : Fin k => G) i ≫ φ) x t ∈ N) : N = ⊤ := by
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  let e := biproduct.isoCoproduct fun _ : Fin k => G
  have he : e.hom ≫ φ = ∑ i, biproduct.π (fun _ : Fin k => G) i ≫
      Sigma.ι (fun _ : Fin k => G) i ≫ φ := by
    rw [biproduct.isoCoproduct_hom, biproduct.desc_eq, Preadditive.sum_comp]
    simp only [Category.assoc]
  refine top_le_iff.1 fun t _ => ?_
  obtain ⟨t, rfl⟩ := stalkLinear_surjective (e.hom ≫ φ) x t
  rw [he, stalkLinear_finset_sum, LinearMap.sum_apply]
  refine sum_mem fun i _ => ?_
  rw [stalkLinear_comp]
  exact h i _

/- English proof (translation)
Use `mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩` and prove the remaining obligations. Establish `hη` using `genericPoint_mem hx`. Use `sub_eq_zero.1 (h W hη _ (hφ ?_))` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, map_zero, sub_eq_zero]`. Conclude with `congrArg _ e`.
-/
theorem IsTorsionFree.mono_of_injective_generic [IsIntegral X] (h : IsTorsionFree G) (φ : G ⟶ F)
    (hφ : Function.Injective (stalkLinear φ (genericPoint X))) : Mono φ := by
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  refine sub_eq_zero.1 (h W hη _ (hφ ?_))
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, map_zero, sub_eq_zero]
  exact congrArg _ e

/- English proof (translation)
Introduce `κ _ _ C _ _ hp F r hF S hS`. Take `⟨_, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hp`. Use `hF.isFiniteQC` as an intermediate fact. Take `⟨n, k, φ, hφ⟩` from `(hA.eventually_exists_epi_sigma F).exists`. Establish `hG` using `isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))`.

Generalize the expression as in `GlobalTheory.LB.toMod (lbZPow A (-n)) = G at φ hφ hG`. Set `ψ : Fin k → (G ⟶ F)` to `fun i => Sigma.ι (fun _ : Fin k => G) i ≫ φ`. Establish `b` using `fun x => (hF.nonempty_basis_stalk x).some`. Establish `g` using `fun x => (hG.nonempty_basis_stalk x).some`. Set `T : Set C` to `insert (genericPoint C) S`.

Establish `: Finite T` using `(hS.insert _).to_subtype`. Take `⟨c, hc⟩` from `exists_forall_isUnit_sum_mul (fun x : T => C.presheaf.stalk x.1) (fun x => (C.presheaf.germ ⊤ x.1 trivial).hom.comp (algebraMap κ Γ(C, ⊤))) (fun x i => (b x.1).coord 0 (stalkLinear (ψ i) x.1 (g x.1 0))) fun x => by by_contra! H`. Establish `h` using `eq_top_of_epi_sigma φ x.1 (Submodule.comap ((b x.1).coord 0) (IsLocalRing.maximalIdeal (C.presheaf.stalk x.1))) fun i t => by`. Rewrite using `[Submodule.mem_comap, ← (g x.1).sum_repr t, Fin.sum_univ_one, map_smul, map_smul]`. Conclude with `Ideal.mul_mem_left _ _ (H i)`.

Establish `h1` using `h.ge (Submodule.mem_top (x := b x.1 0))`. Rewrite `h1` using `[Submodule.mem_comap, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`. Conclude with `h1 isUnit_one`. Set `α : G ⟶ F` to `∑ i, ψ i ≫ smulHom F (algebraMap κ Γ(C, ⊤) (c i))`. Establish `key : ∀ x ∈ T, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :), ρ ∘ₗ stalkLinear α x = LinearMap.id` using `fun x hx => by`.

Use `exists_retraction_of_isUnit (g x) _ ((b x).coord 0) ?_` and prove the remaining obligations. Use `hc ⟨x, hx⟩ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[stalkLinear_finset_sum, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[stalkLinear_comp, LinearMap.comp_apply, stalkLinear_smulHom_apply, map_smul]`.

Both sides reduce to the same expression. Use `⟨G, α, hG, hG.isTorsionFree.mono_of_injective_generic α ?_, fun x hx => key x (Set.mem_insert_of_mem _ hx)⟩` and prove the remaining obligations. Take `⟨ρ, hρ⟩` from `key _ (Set.mem_insert _ _)`. Conclude with `LinearMap.injective_of_comp_eq_id _ _ hρ`.
-/
theorem exists_line_subsheaf_split_at_finite : ∀ (κ : Type) [Field κ] [Infinite κ] (C : Scheme.{0})
    [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjOver (strHom κ C) → ∀ (F : C.Modules) (r : ℕ),
    IsVB F (r + 1) → ∀ S : Set C, S.Finite → ∃ (G : C.Modules) (φ : G ⟶ F), IsVB G 1 ∧ Mono φ ∧
      ∀ x ∈ S, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
        ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id := by
  intro κ _ _ C _ _ hp F r hF S hS
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have := hF.isFiniteQC
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma F).exists
  have hG := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize GlobalTheory.LB.toMod (lbZPow A (-n)) = G at φ hφ hG
  let ψ : Fin k → (G ⟶ F) := fun i => Sigma.ι (fun _ : Fin k => G) i ≫ φ
  have b := fun x => (hF.nonempty_basis_stalk x).some
  have g := fun x => (hG.nonempty_basis_stalk x).some
  let T : Set C := insert (genericPoint C) S
  have : Finite T := (hS.insert _).to_subtype
  obtain ⟨c, hc⟩ := exists_forall_isUnit_sum_mul (fun x : T => C.presheaf.stalk x.1)
    (fun x => (C.presheaf.germ ⊤ x.1 trivial).hom.comp (algebraMap κ Γ(C, ⊤)))
    (fun x i => (b x.1).coord 0 (stalkLinear (ψ i) x.1 (g x.1 0))) fun x => by
      by_contra! H
      have h := eq_top_of_epi_sigma φ x.1
        (Submodule.comap ((b x.1).coord 0) (IsLocalRing.maximalIdeal (C.presheaf.stalk x.1)))
        fun i t => by
          rw [Submodule.mem_comap, ← (g x.1).sum_repr t, Fin.sum_univ_one, map_smul, map_smul]
          exact Ideal.mul_mem_left _ _ (H i)
      have h1 := h.ge (Submodule.mem_top (x := b x.1 0))
      rw [Submodule.mem_comap, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same] at h1
      exact h1 isUnit_one
  let α : G ⟶ F := ∑ i, ψ i ≫ smulHom F (algebraMap κ Γ(C, ⊤) (c i))
  have key : ∀ x ∈ T, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
      ρ ∘ₗ stalkLinear α x = LinearMap.id := fun x hx => by
    refine exists_retraction_of_isUnit (g x) _ ((b x).coord 0) ?_
    convert hc ⟨x, hx⟩ using 1
    rw [stalkLinear_finset_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stalkLinear_comp, LinearMap.comp_apply, stalkLinear_smulHom_apply, map_smul]
    rfl
  refine ⟨G, α, hG, hG.isTorsionFree.mono_of_injective_generic α ?_,
    fun x hx => key x (Set.mem_insert_of_mem _ hx)⟩
  obtain ⟨ρ, hρ⟩ := key _ (Set.mem_insert _ _)
  exact LinearMap.injective_of_comp_eq_id _ _ hρ

end GlobalTheory.VB
