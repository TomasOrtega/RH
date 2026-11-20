import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section Sequence

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]

omit [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] in

instance isDiscreteRep_map_resFunctor_X₁ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsDiscreteRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₁ :=
  IsDiscreteRep.res (continuous_toMonoidHom ψ) _

omit [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₃] in
instance isDiscreteRep_map_resFunctor_X₂ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsDiscreteRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₂ :=
  IsDiscreteRep.res (continuous_toMonoidHom ψ) _

omit [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] in
instance isDiscreteRep_map_resFunctor_X₃ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsDiscreteRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₃ :=
  IsDiscreteRep.res (continuous_toMonoidHom ψ) _

noncomputable def compactδRes (hS : S.ShortExact) (n : ℕ) :
    compactCohomologyRes φ S.X₃ n ⟶ compactCohomologyRes φ S.X₁ (n + 1) :=
  compactδ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n

variable (hS : S.ShortExact)

include hS in

/- English proof (translation)
The claim follows from `compactCohomology_exact₂ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n`.
-/
theorem compactRes_exact₂ (n : ℕ) :
    (ShortComplex.mk (compactCohomologyResMap φ S.f n) (compactCohomologyResMap φ S.g n)
      (by rw [← compactCohomologyResMap_comp, S.zero, compactCohomologyResMap_zero])).Exact :=
  compactCohomology_exact₂ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n

/- English proof (translation)
The claim follows from `compactCohomology_exact₃ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n`.
-/
theorem compactRes_exact₃ (n : ℕ) :
    (ShortComplex.mk (compactCohomologyResMap φ S.g n) (compactδRes φ hS n)
      ((compactCochains_shortExact φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
        (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)).comp_δ n
          (n + 1) rfl)).Exact :=
  compactCohomology_exact₃ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n

/- English proof (translation)
The claim follows from `compactCohomology_exact₁ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n`.
-/
theorem compactRes_exact₁ (n : ℕ) :
    (ShortComplex.mk (compactδRes φ hS n) (compactCohomologyResMap φ S.f (n + 1))
      ((compactCochains_shortExact φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
        (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)).δ_comp n
          (n + 1) rfl)).Exact :=
  compactCohomology_exact₁ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS) n

end Sequence

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (D : Rep.{u} (ULift.{u} ℤ) G)
  [IsDiscreteRep D] {N : ℕ}

/- English proof (translation)
Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] at ha <;> simpa using ha`.
-/
theorem eq_zero_of_neg_neg_one_pow_zsmul {A : Type*} [AddCommGroup A] (s : ℕ) {a : A}
    (ha : (-(-1 : ℤ) ^ s) • a = 0) : a = 0 := by
  rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] at ha <;> simpa using ha

/- English proof (translation)
Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] <;> simp`.
-/
theorem neg_neg_one_pow_zsmul_zsmul {A : Type*} [AddCommGroup A] (s : ℕ) (a : A) :
    (-(-1 : ℤ) ^ s) • ((-(-1 : ℤ) ^ s) • a) = a := by
  rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] <;> simp

/- English proof (translation)
Establish `e : (-1 : R) ^ s • b = ((-1 : ℤ) ^ s) • b`. Rewrite using `[← Int.cast_smul_eq_zsmul R]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h` using `[e]`.

Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ s with e | e <;> rw [e] at h ⊢`. Rewrite `h` using `[one_smul]`. Rewrite using `[eq_neg_of_add_eq_zero_right h, map_neg, neg_smul, one_smul]`. Rewrite `h` using `[neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]`. Rewrite using `[← h, neg_neg, one_smul]`.
-/
theorem map_eq_of_add_neg_one_pow_smul_eq_zero {R Z A : Type*} [Ring R] [AddCommGroup Z]
    [Module R Z] [AddCommGroup A] (t : Z →+ A) (s : ℕ) {a b : Z}
    (h : a + (-1 : R) ^ s • b = 0) : t b = (-(-1 : ℤ) ^ s) • t a := by
  have e : (-1 : R) ^ s • b = ((-1 : ℤ) ^ s) • b := by
    rw [← Int.cast_smul_eq_zsmul R]
    push_cast
    rfl
  rw [e] at h
  rcases neg_one_pow_eq_or ℤ s with e | e <;> rw [e] at h ⊢
  · rw [one_smul] at h
    rw [eq_neg_of_add_eq_zero_right h, map_neg, neg_smul, one_smul]
  · rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    rw [← h, neg_neg, one_smul]

variable {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]

/- English proof (translation)
Establish `key` using `compactCup_compactδ_add_compactCup_δ φ (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D) (c := fun _ => 𝟙 _) (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X …`. Rewrite using `[compactDualityMap_apply, compactDualityMap_apply]`. Conclude with `map_eq_of_add_neg_one_pow_smul_eq_zero t s key`.
-/
theorem compactDualityMap_δ {n : ℕ} (t : compactCohomologyRes φ D (n + 1) →+ ZMod N) (hS : S.ShortExact)
    (hT : (dualShortComplex D S).ShortExact) {r s : ℕ} (h₁ : r + 1 + s = n + 1)
    (h₀ : r + (s + 1) = n + 1) (q : cohomology S.X₃ r)
    (y : compactCohomologyRes φ (dualRep D S.X₁) s) :
    compactDualityMap φ D h₁ t S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      (-(-1 : ℤ) ^ s) • compactDualityMap φ D h₀ t S.X₃ q ((compactδRes φ hT s).hom y) := by
  have key := compactCup_compactδ_add_compactCup_δ φ
    (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D) (c := fun _ => 𝟙 _)
    (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X₁)
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₃))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₂))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₁))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (tensorHom_dualEvalPairing D S.g) (tensorHom_dualEvalPairing D S.f).symm
    (fun v => resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun v => (resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    hT (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hT) hS
    (show s + 1 + r = n + 1 by omega) (show s + (r + 1) = n + 1 by omega) y q
  rw [compactDualityMap_apply, compactDualityMap_apply]
  exact map_eq_of_add_neg_one_pow_smul_eq_zero t s key

end Sign

section Embedding

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}

/- English proof (translation)
Set `W` to `fixingOpenSubgroup M ⊓ U₀`. Establish `hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m` using `fun w hw m => fixingOpenSubgroup_apply M ((inf_le_left : fixingOpenSubgroup M ⊓ U₀ ≤ fixingOpenSubgroup M) hw) m`. Set `e` to `(Finite.equivFin (M →+ ZMod n)).symm`. Set `F : ∀ _ : Fin (Nat.card (M →+ ZMod n)), M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)` to `fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))`. Use `⟨W, inf_le_right, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Take `⟨χ, hχ⟩` from `zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)`. Apply `hχ` to reduce the goal to its premises. Establish `hj` using `congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab`.

Express the relevant statement in the definitionally equal form `(biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a = (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj`. Rewrite `hj` using `[biproduct.lift_π]`. Establish `h1` using `congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj`. Simplify using `only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply, Equiv.apply_symm_apply] at h1`. Rewrite `h1` using `[charHom_hom_apply, charHom_hom_apply]`.

Express the relevant statement in the definitionally equal form `χ a = χ b at h1`. Rewrite using `[map_sub, h1, sub_self]`.
-/
theorem exists_injective_biproduct_coind_le [NeZero n] (U₀ : OpenSubgroup Γ)
    (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    ∃ (W : OpenSubgroup Γ) (_ : W ≤ U₀) (J : Type) (_ : Fintype J)
      (i : M ⟶ ⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)),
      Function.Injective i.hom := by
  let W := fixingOpenSubgroup M ⊓ U₀
  have hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m :=
    fun w hw m => fixingOpenSubgroup_apply M
      ((inf_le_left : fixingOpenSubgroup M ⊓ U₀ ≤ fixingOpenSubgroup M) hw) m
  let e := (Finite.equivFin (M →+ ZMod n)).symm
  let F : ∀ _ : Fin (Nat.card (M →+ ZMod n)),
      M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :=
    fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))
  refine ⟨W, inf_le_right, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩
  intro a b hab
  by_contra hne
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)
  apply hχ
  have hj := congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) =>
    Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab
  change (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a =
    (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj
  rw [biproduct.lift_π] at hj
  have h1 := congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj
  simp only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply,
    Equiv.apply_symm_apply] at h1
  rw [charHom_hom_apply, charHom_hom_apply] at h1
  change χ a = χ b at h1
  rw [map_sub, h1, sub_self]

end Embedding

section Core

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

structure CompactGroupDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep D] (t : compactCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactCohomologyRes φ M 4)

  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (compactDualityMap φ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))

namespace CompactGroupDualityHypotheses

variable {φ} {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}
  (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in
/- English proof (translation)
The claim follows from `finite_of_nonempty_addEquiv H.nonempty_addEquiv`.
-/
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv H.nonempty_addEquiv

include H in
/- English proof (translation)
The claim follows from `nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d`.
-/
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d

include H in

/- English proof (translation)
Take `⟨W, hW, J, _, i, hi⟩` from `exists_injective_biproduct_coind_le (n := n) U₀ M hM`. Establish `hφ : ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactDualityMap φ D h t (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G))` using `fun h => bijective_compactDualityMap_biproduct φ D h t _ fun _ => H.bijective_coind W hW h`. Establish `hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G) : Type u), n • x = 0`. Introduce `x`. Rewrite using `[biproduct_eq_sum _ x, Finset.smul_sum]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]`. Establish `hmono : Mono i` using `(Rep.mono_iff_injective i).2 hi`. Set `S` to `ShortComplex.mk i (cokernel.π i) (cokernel.condition i)`. Establish `hS : S.ShortExact` using `ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono (inferInstance : Epi (cokernel.π i))`.

Establish `hQd : IsDiscreteRep (cokernel i)` using `isDiscreteRep_X₃_of_shortExact hS`. Establish `hsurj : Function.Surjective (cokernel.π i).hom` using `(Rep.epi_iff_surjective _).1 inferInstance`. Establish `hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) G) : Type u)` using `Finite.of_surjective _ hsurj`. Use `⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i, cokernel.condition i, hS, hnI, fun x => ?_, hφ⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj x`.

Rewrite using `[← map_nsmul, hnI, map_zero]`.
-/
theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) G) (_ : IsDiscreteRep I) (_ : IsDiscreteRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactDualityMap φ D h t I) := by
  obtain ⟨W, hW, J, _, i, hi⟩ := exists_injective_biproduct_coind_le (n := n) U₀ M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactDualityMap φ D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) :
        Rep.{u} (ULift.{u} ℤ) G)) :=
    fun h => bijective_compactDualityMap_biproduct φ D h t _ fun _ => H.bijective_coind W hW h
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype
      (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsDiscreteRep (cokernel i) := isDiscreteRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) G) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

end CompactGroupDualityHypotheses

end Core

section Steps

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactGroupDualityHypotheses

variable (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in

/- English proof (translation)
Use `H.finite_D` as an intermediate fact. Take `⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩` from `H.exists_devissage M hM`. Establish `hi : Function.Injective i.hom` using `(Rep.mono_iff_injective i).1 hS.mono_f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `h1 : compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((cohomologyMap i 0).hom x) = 0`. Use extensionality with `y`. Rewrite using `[compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i x y, hx]`. Both sides reduce to the same expression. Establish `h2 : (cohomologyMap i 0).hom x = 0` using `(injective_iff_map_eq_zero _).1 (hI (rfl : 0 + 3 = 3)).1 _ h1`.

Conclude with `(injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2`.
-/
theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((cohomologyMap i 0).hom x) = 0 := by
    ext y
    rw [compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i x y, hx]
    rfl
  have h2 : (cohomologyMap i 0).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI (rfl : 0 + 3 = 3)).1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

/- English proof (translation)
Use `H.finite_D` as an intermediate fact. Take `⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩` from `H.exists_devissage M hM`. Set `S` to `ShortComplex.mk i p w`. Establish `hT : (dualShortComplex D S).ShortExact` using `dualShortComplex_shortExact H.nonempty_addEquiv hS hnI`. Establish `hsurj : Function.Surjective (compactCohomologyResMap φ (dualMap D i) 3).hom`.

Introduce `y`. Establish `: Subsingleton (compactCohomologyRes φ (dualRep D Q) 4)` using `H.subsingleton_four (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)`. Conclude with `(ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT 3) y (Subsingleton.elim _ _)`. Introduce `l`. Take `⟨v, hv⟩` from `(hI (rfl : 0 + 3 = 3)).2 (l.comp (compactCohomologyResMap φ (dualMap D i) 3).hom.toAddMonoidHom)`.

Establish `hpv : (cohomologyMap p 0).hom v = 0`. Apply `(injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)` to reduce the goal to its premises. Use extensionality with `y`. Rewrite using `[compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t p v y, hv]`. Express the relevant statement in the definitionally equal form `l ((compactCohomologyResMap φ (dualMap D p) 3 ≫ compactCohomologyResMap φ (dualMap D i) 3).hom y) = 0`.

Rewrite using `[← compactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero, compactCohomologyResMap_zero]`. Conclude with `map_zero l`. Take `⟨m, hm⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Take `⟨z, rfl⟩` from `hsurj y`. Rewrite using `[← compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i m z]`. Express the relevant statement in the definitionally equal form `compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((cohomologyMap S.f 0).hom m) z = _`. Rewrite using `[hm, hv]`. Both sides reduce to the same expression.
-/
theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (compactCohomologyResMap φ (dualMap D i) 3).hom := by
    intro y
    have : Subsingleton (compactCohomologyRes φ (dualRep D Q) 4) :=
      H.subsingleton_four (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT 3) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := (hI (rfl : 0 + 3 = 3)).2
    (l.comp (compactCohomologyResMap φ (dualMap D i) 3).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t p v y, hv]
    change l ((compactCohomologyResMap φ (dualMap D p) 3 ≫
      compactCohomologyResMap φ (dualMap D i) 3).hom y) = 0
    rw [← compactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      compactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i m z]
  change compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((cohomologyMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
/- English proof (translation)
Assemble the required witnesses or components as `⟨H.injective_zero M hM, H.surjective_zero M hM⟩`.
-/
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

variable {r s : ℕ} (h₁ : r + 1 + s = 3) (h₀ : r + (s + 1) = 3)

include H in

/- English proof (translation)
Use `H.finite_D` as an intermediate fact. Take `⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩` from `H.exists_devissage M hM`. Set `S` to `ShortComplex.mk i p w`. Establish `hT : (dualShortComplex D S).ShortExact` using `dualShortComplex_shortExact H.nonempty_addEquiv hS hnI`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `h1 : compactDualityMap φ D h₁ t I ((cohomologyMap i (r + 1)).hom x) = 0`. Use extensionality with `y`. Rewrite using `[compactDualityMap_cohomologyMap φ D h₁ t i x y, hx]`. Both sides reduce to the same expression.

Establish `hix : (cohomologyMap i (r + 1)).hom x = 0` using `(injective_iff_map_eq_zero _).1 (hI h₁).1 _ h1`. Take `⟨q, hq⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix`. Establish `hker : ((compactCohomologyResMap φ (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤ (compactDualityMap φ D h₀ t Q q).ker`. Introduce `z hz`. Take `⟨y, hy⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₁ φ hT s) z hz`.

Rewrite using `[AddMonoidHom.mem_ker, ← hy]`. Establish `e` using `compactDualityMap_δ φ D t hS hT h₁ h₀ q y`. Express the relevant statement in the definitionally equal form `compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e`. Rewrite `e` using `[hq, hx, AddMonoidHom.zero_apply]`. Conclude with `eq_zero_of_neg_neg_one_pow_zsmul s e.symm`.

Take `⟨ψ, hψ⟩` from `zmod_exists_comp_eq_of_ker_le (nsmul_compactCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker`. Take `⟨v, hv⟩` from `(ih I hnI).2 ψ`. Establish `hpv : (cohomologyMap p r).hom v = q`. Apply `(ih Q hnQ).1` to reduce the goal to its premises. Use extensionality with `z`.

Rewrite using `[compactDualityMap_cohomologyMap φ D h₀ t p v z, hv, ← hψ]`. Both sides reduce to the same expression. Rewrite using `[← hq, ← hpv]`. Conclude with `congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)`.
-/
theorem injective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Injective (compactDualityMap φ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : compactDualityMap φ D h₁ t I ((cohomologyMap i (r + 1)).hom x) = 0 := by
    ext y
    rw [compactDualityMap_cohomologyMap φ D h₁ t i x y, hx]
    rfl
  have hix : (cohomologyMap i (r + 1)).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI h₁).1 _ h1
  obtain ⟨q, hq⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix
  have hker : ((compactCohomologyResMap φ (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤
      (compactDualityMap φ D h₀ t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₁ φ hT s) z hz
    rw [AddMonoidHom.mem_ker, ← hy]
    have e := compactDualityMap_δ φ D t hS hT h₁ h₀ q y
    change compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
    rw [hq, hx, AddMonoidHom.zero_apply] at e
    exact eq_zero_of_neg_neg_one_pow_zsmul s e.symm
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_compactCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨v, hv⟩ := (ih I hnI).2 ψ
  have hpv : (cohomologyMap p r).hom v = q := by
    apply (ih Q hnQ).1
    ext z
    rw [compactDualityMap_cohomologyMap φ D h₀ t p v z, hv, ← hψ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)

include H in

/- English proof (translation)
Use `H.finite_D` as an intermediate fact. Take `⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩` from `H.exists_devissage M hM`. Set `S` to `ShortComplex.mk i p w`. Establish `hT : (dualShortComplex D S).ShortExact` using `dualShortComplex_shortExact H.nonempty_addEquiv hS hnI`. Introduce `l`.

Take `⟨v, hv⟩` from `(hI h₁).2 (l.comp (compactCohomologyResMap φ (dualMap D i) s).hom.toAddMonoidHom)`. Establish `hpv : (cohomologyMap p (r + 1)).hom v = 0`. Apply `(injective_iff_map_eq_zero _).1 (H.injective_succ h₁ h₀ ih Q hnQ)` to reduce the goal to its premises. Use extensionality with `y`. Rewrite using `[compactDualityMap_cohomologyMap φ D h₁ t p v y, hv]`.

Express the relevant statement in the definitionally equal form `l ((compactCohomologyResMap φ (dualMap D p) s ≫ compactCohomologyResMap φ (dualMap D i) s).hom y) = 0`. Rewrite using `[← compactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero, compactCohomologyResMap_zero]`. Conclude with `map_zero l`. Take `⟨x', hx'⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv`. Use `set ν := l - compactDualityMap φ D h₁ t M x' with hν`.

Establish `hker : ((compactδRes φ hT s).hom.toAddMonoidHom).ker ≤ ν.ker`. Introduce `y hy`. Take `⟨z, hz⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT s) y hy`. Rewrite using `[AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `l ((compactCohomologyResMap φ (dualMap D i) s).hom z) = compactDualityMap φ D h₁ t M x' ((compactCohomologyResMap φ (dualMap D i) s).hom z)`.

Rewrite using `[← compactDualityMap_cohomologyMap φ D h₁ t i x' z]`. Express the relevant statement in the definitionally equal form `_ = compactDualityMap φ D h₁ t I ((cohomologyMap S.f (r + 1)).hom x') z`. Rewrite using `[hx', hv]`. Both sides reduce to the same expression. Take `⟨ψ, hψ⟩` from `zmod_exists_comp_eq_of_ker_le (nsmul_compactCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker`.

Take `⟨q, hq⟩` from `(ih Q hnQ).2 ψ`. Use `⟨x' + (-(-1 : ℤ) ^ s) • (δ hS r (r + 1) rfl).hom q, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Establish `e` using `compactDualityMap_δ φ D t hS hT h₁ h₀ q y`. Express the relevant statement in the definitionally equal form `compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e`.

Establish `hψy : ψ ((compactδRes φ hT s).hom y) = ν y` using `congrArg (fun f => f y) hψ`. Rewrite using `[map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq, neg_neg_one_pow_zsmul_zsmul]`. Express the relevant statement in the definitionally equal form `_ + ψ ((compactδRes φ hT s).hom y) = l y`. Rewrite using `[hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]`.
-/
theorem surjective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (compactDualityMap φ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := (hI h₁).2 (l.comp (compactCohomologyResMap φ (dualMap D i) s).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p (r + 1)).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_succ h₁ h₀ ih Q hnQ)
    ext y
    rw [compactDualityMap_cohomologyMap φ D h₁ t p v y, hv]
    change l ((compactCohomologyResMap φ (dualMap D p) s ≫
      compactCohomologyResMap φ (dualMap D i) s).hom y) = 0
    rw [← compactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      compactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv
  set ν := l - compactDualityMap φ D h₁ t M x' with hν
  have hker : ((compactδRes φ hT s).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT s) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((compactCohomologyResMap φ (dualMap D i) s).hom z) =
      compactDualityMap φ D h₁ t M x' ((compactCohomologyResMap φ (dualMap D i) s).hom z)
    rw [← compactDualityMap_cohomologyMap φ D h₁ t i x' z]
    change _ = compactDualityMap φ D h₁ t I ((cohomologyMap S.f (r + 1)).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_compactCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨q, hq⟩ := (ih Q hnQ).2 ψ
  refine ⟨x' + (-(-1 : ℤ) ^ s) • (δ hS r (r + 1) rfl).hom q, ?_⟩
  ext y
  have e := compactDualityMap_δ φ D t hS hT h₁ h₀ q y
  change compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
  have hψy : ψ ((compactδRes φ hT s).hom y) = ν y := congrArg (fun f => f y) hψ
  rw [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq,
    neg_neg_one_pow_zsmul_zsmul]
  change _ + ψ ((compactδRes φ hT s).hom y) = l y
  rw [hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H in
/- English proof (translation)
Assemble the required witnesses or components as `⟨H.injective_succ h₁ h₀ ih M hM, H.surjective_succ h₁ h₀ ih M hM⟩`.
-/
theorem bijective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (compactDualityMap φ D h₁ t M) :=
  ⟨H.injective_succ h₁ h₀ ih M hM, H.surjective_succ h₁ h₀ ih M hM⟩

end CompactGroupDualityHypotheses

end Steps

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactGroupDualityHypotheses

variable (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in

/- English proof (translation)
Establish `b0` using `fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) => H.bijective_zero M hM`. Establish `b1` using `fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 0) (s := 2) rfl rfl b0 M hM`. Establish `b2` using `fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 1) (s := 1) rfl rfl b1 M hM`. Establish `b3` using `fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 2) (s := 0) rfl rfl b2 M hM`. Take `⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (r = 0 ∧ s = 3) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) ∨ (r = 3 ∧ s = 0)` from `by omega`.

Conclude with `b0 M hM`. Conclude with `b1 M hM`. Conclude with `b2 M hM`. Conclude with `b3 M hM`.
-/
theorem bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M) := by
  have b0 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_zero M hM
  have b1 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 0) (s := 2) rfl rfl b0 M hM
  have b2 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 1) (s := 1) rfl rfl b1 M hM
  have b3 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 2) (s := 0) rfl rfl b2 M hM
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 3) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) ∨ (r = 3 ∧ s = 0) := by omega
  · exact b0 M hM
  · exact b1 M hM
  · exact b2 M hM
  · exact b3 M hM

end CompactGroupDualityHypotheses

end Main

end GroundTheory.ProfCoh
