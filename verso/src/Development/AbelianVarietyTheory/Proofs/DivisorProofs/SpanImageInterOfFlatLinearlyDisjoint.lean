import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
open GlobalTheory.Desc

open TensorProduct

namespace GlobalTheory.FlatSpanInter

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [SetLike.mem_coe, Submodule.mem_span_set']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, r, t, ht, rfl⟩`. Conclude with `⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩`.

Introduce and unpack `⟨n, r, t, rfl⟩`. Conclude with `⟨n, r, fun i => t i, fun i => (t i).2, by simp [Algebra.smul_def]⟩`.
-/
theorem spanBy_algebraMap_eq {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] [Algebra R₁ F₁] (T : Set F₁) :
    spanBy (algebraMap R₁ F₁) T = (Submodule.span R₁ T : Set F₁) := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, by simp [Algebra.smul_def]⟩

variable {R R₁ F F₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [CommRing F₁]
  [Algebra R R₁] [Algebra R F] [Algebra R₁ F₁] [Algebra R F₁] [IsScalarTower R R₁ F₁]

/- English proof (translation)
Use `set u : F := (algebraMap R F d)⁻¹`. Establish `hu : u * algebraMap R F d = 1` using `inv_mul_cancel₀ (fun h => hd (hc₀ (by rw [h, map_zero])))`. Establish `key : ∀ z : R₁ ⊗[R] F, LinearMap.lTensor R₁ (LinearMap.mulLeft R u) (d • z) = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r f`. Rewrite using `[← TensorProduct.tmul_smul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc, hu, one_mul]`. Consider the case `add a b ha hb => rw [smul_add, map_add, ha, hb]`. Rewrite using `[← key x, hx, map_zero]`.
-/
theorem smul_injective_tensor (hc₀ : Function.Injective (algebraMap R F)) {d : R} (hd : d ≠ 0)
    (x : R₁ ⊗[R] F) (hx : d • x = 0) : x = 0 := by
  set u : F := (algebraMap R F d)⁻¹
  have hu : u * algebraMap R F d = 1 :=
    inv_mul_cancel₀ (fun h => hd (hc₀ (by rw [h, map_zero])))
  have key : ∀ z : R₁ ⊗[R] F, LinearMap.lTensor R₁ (LinearMap.mulLeft R u) (d • z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.smul_def,
        ← mul_assoc, hu, one_mul]
    | add a b ha hb => rw [smul_add, map_add, ha, hb]
  rw [← key x, hx, map_zero]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Use `set bB := Module.Basis.span hli`. Use `set bb := Algebra.TensorProduct.basis R₁ bB`. Establish `hval : ∀ j, ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) (bb j) = θ (v j)`.

Introduce `j`. Simplify using `[bb, bB, Algebra.TensorProduct.basis_apply, Module.Basis.span_apply, LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]`. Establish `e1 : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) y = ∑ j, algebraMap R₁ F₁ (bb.repr y j) * θ (v j)` using `by conv_lhs => rw [← bb.sum_repr y]`. Simplify using `only [map_sum, map_smul, hval, Algebra.smul_def]`. Rewrite `e1` using `[hy]`.

Use `set e := (Fintype.equivFin ι).symm`. Establish `h0` using `hLD _ (v ∘ e) (by`. Introduce `r hr`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 (hli.comp e e.injective) r (by simpa [Algebra.smul_def] using hr) i)`.

Use the proof step `(fun i => bb.repr y (e i)) (by`. Rewrite using `[e1, ← Equiv.sum_comp e]`. Use the proof step `rfl)`. Establish `hr : bb.repr y = 0`. Use extensionality with `j`.

Simplify using `using congrFun h0 (e.symm j)`. Conclude with `bb.repr.map_eq_zero_iff.1 hr`.
-/
theorem free_injective (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁))
    {ι : Type} [Fintype ι] (v : ι → F) (hli : LinearIndependent R v) :
    Function.Injective ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set bB := Module.Basis.span hli
  set bb := Algebra.TensorProduct.basis R₁ bB
  have hval : ∀ j, ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) (bb j) = θ (v j) := by
    intro j
    simp [bb, bB, Algebra.TensorProduct.basis_apply, Module.Basis.span_apply, LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
  have e1 : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) y =
        ∑ j, algebraMap R₁ F₁ (bb.repr y j) * θ (v j) := by
    conv_lhs => rw [← bb.sum_repr y]
    simp only [map_sum, map_smul, hval, Algebra.smul_def]
  rw [hy] at e1
  set e := (Fintype.equivFin ι).symm
  have h0 := hLD _ (v ∘ e) (by
      intro r hr
      funext i
      exact Fintype.linearIndependent_iff.1 (hli.comp e e.injective) r
        (by simpa [Algebra.smul_def] using hr) i)
    (fun i => bb.repr y (e i)) (by
      rw [e1, ← Equiv.sum_comp e]
      rfl)
  have hr : bb.repr y = 0 := by
    ext j
    simpa using congrFun h0 (e.symm j)
  exact bb.repr.map_eq_zero_iff.1 hr

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Take `⟨S, rfl⟩` from `TensorProduct.exists_finset x`. Use `set g : S → F := fun i => (i : R₁ × F).2`. Take `⟨s, hli, hmax⟩` from `exists_maximal_linearIndepOn R g`.

Establish `ha : ∀ i, ∃ a : R, a ≠ 0 ∧ a • g i ∈ Submodule.span R (g '' s)`. Introduce `i`. Distinguish the cases in `hi : i ∈ s`. Conclude with `⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩`. Conclude with `hmax i hi`.

Use `choose a ha0 ha using ha`. Use `set d := ∏ i, a i`. Establish `hd : d ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)`. Establish `hdg : ∀ i, d • g i ∈ Submodule.span R (Set.range fun j : s => g j)`. Introduce `i`.

Rewrite using `[← Set.image_eq_range]`. Take `⟨e, he⟩ : a i ∣ d` from `Finset.dvd_prod_of_mem a (Finset.mem_univ i)`. Rewrite using `[he, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (ha i)`. Use `haveI : Fintype s := Fintype.ofFinite s`.

Use `set B := Submodule.span R (Set.range fun j : s => g j)`. Use `set y : R₁ ⊗[R] B := ∑ i : S, (i : R₁ × F).1 ⊗ₜ ⟨d • g i, hdg i⟩`. Establish `hy : B.subtype.baseChange R₁ y = d • ∑ i ∈ S, i.1 ⊗ₜ i.2`. Rewrite using `[Finset.smul_sum, ← Finset.sum_coe_sort S]`. Simplify using `only [y, map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, g]`.

Establish `hz : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ (B.subtype.baseChange R₁)) y = 0`. Rewrite using `[LinearMap.comp_apply, hy, LinearMap.map_smul_of_tower, hx, smul_zero]`. Establish `hy0 : y = 0` using `free_injective θ hLD (fun j : s => g j) hli (by rw [hz, map_zero])`. Conclude with `smul_injective_tensor hc₀ hd _ (by rw [← hy, hy0, map_zero])`.
-/
theorem liftBaseChange_injective (hc₀ : Function.Injective (algebraMap R F)) (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁)) :
    Function.Injective (LinearMap.liftBaseChange R₁ θ.toLinearMap) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set g : S → F := fun i => (i : R₁ × F).2
  obtain ⟨s, hli, hmax⟩ := exists_maximal_linearIndepOn R g
  have ha : ∀ i, ∃ a : R, a ≠ 0 ∧ a • g i ∈ Submodule.span R (g '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · exact hmax i hi
  choose a ha0 ha using ha
  set d := ∏ i, a i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hdg : ∀ i, d • g i ∈ Submodule.span R (Set.range fun j : s => g j) := by
    intro i
    rw [← Set.image_eq_range]
    obtain ⟨e, he⟩ : a i ∣ d := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rw [he, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha i)
  haveI : Fintype s := Fintype.ofFinite s
  set B := Submodule.span R (Set.range fun j : s => g j)
  set y : R₁ ⊗[R] B := ∑ i : S, (i : R₁ × F).1 ⊗ₜ ⟨d • g i, hdg i⟩
  have hy : B.subtype.baseChange R₁ y = d • ∑ i ∈ S, i.1 ⊗ₜ i.2 := by
    rw [Finset.smul_sum, ← Finset.sum_coe_sort S]
    simp only [y, map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, g]
  have hz : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ (B.subtype.baseChange R₁)) y = 0 := by
    rw [LinearMap.comp_apply, hy, LinearMap.map_smul_of_tower, hx, smul_zero]
  have hy0 : y = 0 := free_injective θ hLD (fun j : s => g j) hli (by rw [hz, map_zero])
  exact smul_injective_tensor hc₀ hd _ (by rw [← hy, hy0, map_zero])

/- English proof (translation)
Rewrite using `[spanBy_algebraMap_eq, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]`. Use `congr 2`. Use extensionality with `p`. Simplify using `[LinearMap.liftBaseChange_tmul]`.
-/
theorem spanBy_image_eq_map (θ : F →ₐ[R] F₁) (P : Submodule R F) :
    spanBy (algebraMap R₁ F₁) (θ '' P) =
      ((P.baseChange R₁).map (LinearMap.liftBaseChange R₁ θ.toLinearMap) : Set F₁) := by
  rw [spanBy_algebraMap_eq, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  congr 2
  ext p
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory.FlatSpanInter

/- English proof (translation)
Introduce `R R₁ F F₁ _ _ _ _ _ ρ c₀ c₁ θ hρ hc₀ hcomp hLD M N hM0 hMa hMs hN0 hNa hNs`. Use `letI : Algebra R R₁ := ρ.toAlgebra`. Use `letI : Algebra R F := c₀.toAlgebra`. Use `letI : Algebra R₁ F₁ := c₁.toAlgebra`. Use `letI : Algebra R F₁ := (c₁.comp ρ).toAlgebra`.

Use `haveI : IsScalarTower R R₁ F₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Module.Flat R R₁ := hρ`. Set `θa : F →ₐ[R] F₁` to `{ θ with commutes' := fun r => RingHom.congr_fun hcomp r }`. Set `MS : Submodule R F` to `{ carrier := M, add_mem' := fun ha hb => hMa _ ha _ hb, zero_mem' := hM0, smul_mem' := fun r a ha => hMs r a ha }`. Set `NS : Submodule R F` to `{ carrier := N, add_mem' := fun ha hb => hNa _ ha _ hb, zero_mem' := hN0, smul_mem' := fun r a ha => hNs r a ha }`.

Establish `hinj` using `GlobalTheory.FlatSpanInter.liftBaseChange_injective (R₁ := R₁) hc₀ θa hLD`. Establish `kI : spanBy c₁ (θ '' (M ∩ N)) = _` using `GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa (MS ⊓ NS)`. Establish `kM : spanBy c₁ (θ '' M) = _` using `GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa MS`. Establish `kN : spanBy c₁ (θ '' N) = _` using `GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa NS`. Rewrite using `[kI, kM, kN, GlobalTheory.baseChange_inf, Submodule.map_inf _ hinj, Submodule.coe_inf]`.
-/
theorem GlobalTheory.Desc.spanBy_image_inter : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁]
    (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ →
    θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) →
    (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) →
    spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  intro R R₁ F F₁ _ _ _ _ _ ρ c₀ c₁ θ hρ hc₀ hcomp hLD M N hM0 hMa hMs hN0 hNa hNs
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R F := c₀.toAlgebra
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  letI : Algebra R F₁ := (c₁.comp ρ).toAlgebra
  haveI : IsScalarTower R R₁ F₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat R R₁ := hρ
  let θa : F →ₐ[R] F₁ := { θ with commutes' := fun r => RingHom.congr_fun hcomp r }
  let MS : Submodule R F :=
    { carrier := M, add_mem' := fun ha hb => hMa _ ha _ hb, zero_mem' := hM0,
      smul_mem' := fun r a ha => hMs r a ha }
  let NS : Submodule R F :=
    { carrier := N, add_mem' := fun ha hb => hNa _ ha _ hb, zero_mem' := hN0,
      smul_mem' := fun r a ha => hNs r a ha }
  have hinj := GlobalTheory.FlatSpanInter.liftBaseChange_injective (R₁ := R₁) hc₀ θa hLD
  have kI : spanBy c₁ (θ '' (M ∩ N)) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa (MS ⊓ NS)
  have kM : spanBy c₁ (θ '' M) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa MS
  have kN : spanBy c₁ (θ '' N) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa NS
  rw [kI, kM, kN, GlobalTheory.baseChange_inf, Submodule.map_inf _ hinj, Submodule.coe_inf]
