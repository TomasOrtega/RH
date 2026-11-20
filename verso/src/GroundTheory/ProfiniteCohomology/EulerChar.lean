import Mathlib
import GroundTheory.ProfiniteCohomology.EulerCharDefs
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
import GroundTheory.ProfiniteCohomology.Shapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Counting

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/- English proof (translation)
Establish `h1` using `AddSubgroup.card_mul_index f.toAddMonoidHom.ker`. Rewrite `h1` using `[AddSubgroup.index_ker]`. Conclude with `h1.symm`.
-/
theorem card_eq_card_ker_mul_card_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h1 := AddSubgroup.card_mul_index f.toAddMonoidHom.ker
  rw [AddSubgroup.index_ker] at h1
  exact h1.symm

end Counting

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Simplify using `[eulerChar, Finset.prod_range_succ, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eulerChar_eq (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar A = (Nat.card (cohomology A 0) : ℚ) * Nat.card (cohomology A 2) /
      Nat.card (cohomology A 1) := by
  simp [eulerChar, Finset.prod_range_succ, div_eq_mul_inv]
  ring

section ShortExact

/- English proof (translation)
Rewrite `hT` using `[ShortComplex.moduleCat_exact_iff_range_eq_ker]`. Rewrite using `[hT]`.
-/
theorem card_range_eq_card_ker_of_exact {T : ShortComplex (ModuleCat k)} (hT : T.Exact) :
    Nat.card (LinearMap.range T.f.hom) = Nat.card (LinearMap.ker T.g.hom) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hT
  rw [hT]

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

/- English proof (translation)
Establish `hk` using `fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom`. Establish `e2 : ∀ i, Nat.card (LinearMap.range (cohomologyMap S.f i).hom) = Nat.card (LinearMap.ker (cohomologyMap S.g i).hom)` using `fun i => card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)`. Establish `e30 : Nat.card (LinearMap.range (cohomologyMap S.g 0).hom) = Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom)` using `card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)`. Establish `e31 : Nat.card (LinearMap.range (cohomologyMap S.g 1).hom) = Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom)` using `card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)`. Establish `e32 : Nat.card (LinearMap.range (cohomologyMap S.g 2).hom) = Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom)` using `card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)`.

Establish `e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) = Nat.card (LinearMap.ker (cohomologyMap S.f 1).hom)` using `card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)`. Establish `e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) = Nat.card (LinearMap.ker (cohomologyMap S.f 2).hom)` using `card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)`. Establish `h0 : Nat.card (LinearMap.ker (cohomologyMap S.f 0).hom) = 1`. Use `hS.mono_f` as an intermediate fact. Establish `hm : Mono (cohomologyMap S.f 0)` using `HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (cochainsMap S.f) 0 (fun i => by simp)`.

Rewrite using `[LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]`. Simplify using the standard rewrite rules. Establish `htop : Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) = 1` using `Nat.card_of_subsingleton (0 : LinearMap.range (δ hS 2 3 rfl).hom)`. Establish `hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0` using `Nat.card_pos.ne'`. Establish `hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0` using `Nat.card_pos.ne'`.

Establish `hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0` using `Nat.card_pos.ne'`. Rewrite `hA1` using `[hk (cohomologyMap S.f 1), ← e10]`. Rewrite `hB1` using `[hk (cohomologyMap S.g 1), ← e2 1]`. Rewrite `hC1` using `[hk (δ hS 1 2 rfl), ← e31]`. Rewrite using `[eulerChar_eq, eulerChar_eq, eulerChar_eq, hk (cohomologyMap S.f 0), hk (cohomologyMap S.f 1), hk (cohomologyMap S.f 2), hk (cohomologyMap S.g 0), hk (cohomologyMap S.g 1), hk (cohomologyMap S.g 2), hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl), h0, htop, ← e2 0, ← e2 1 …`.

Simplify using `only [mul_ne_zero_iff] at hA1 hB1 hC1`. Take `⟨hz0, hx1⟩` from `hA1`. Take `⟨-, hy1⟩` from `hB1`. Take `⟨-, hz1⟩` from `hC1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem eulerChar_shortExact_of_finite (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)]
    [Subsingleton (cohomology S.X₁ 3)] :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (cohomologyMap S.f i).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)
  have e30 : Nat.card (LinearMap.range (cohomologyMap S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (cohomologyMap S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (cohomologyMap S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (cohomologyMap S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (cohomologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (cochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have htop : Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) = 1 :=
    Nat.card_of_subsingleton (0 : LinearMap.range (δ hS 2 3 rfl).hom)
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (cohomologyMap S.f 1), ← e10] at hA1
  rw [hk (cohomologyMap S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerChar_eq, eulerChar_eq, eulerChar_eq,
    hk (cohomologyMap S.f 0), hk (cohomologyMap S.f 1), hk (cohomologyMap S.f 2),
    hk (cohomologyMap S.g 0), hk (cohomologyMap S.g 1), hk (cohomologyMap S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, htop, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

end ShortExact

section Hypothesis

variable {P : ℕ → Prop}

/- English proof (translation)
Take `⟨hfin, -⟩` from `hG A ‹_› hA`. Establish `h0` using `hfin 0`. Establish `h1` using `hfin 1`. Establish `h2` using `hfin 2`. Rewrite using `[eulerChar_eq]`.

Establish `p0 : (0 : ℚ) < Nat.card (cohomology A 0)` using `by exact_mod_cast Nat.card_pos`. Establish `p1 : (0 : ℚ) < Nat.card (cohomology A 1)` using `by exact_mod_cast Nat.card_pos`. Establish `p2 : (0 : ℚ) < Nat.card (cohomology A 2)` using `by exact_mod_cast Nat.card_pos`. Check the signs of the components of the expression.
-/
theorem eulerChar_pos (hG : HasFiniteCohomology k G P) (A : Rep.{u} k G) [IsDiscreteRep A]
    [Finite A] (hA : P (Nat.card A)) : 0 < eulerChar A := by
  obtain ⟨hfin, -⟩ := hG A ‹_› hA
  have h0 := hfin 0
  have h1 := hfin 1
  have h2 := hfin 2
  rw [eulerChar_eq]
  have p0 : (0 : ℚ) < Nat.card (cohomology A 0) := by exact_mod_cast Nat.card_pos
  have p1 : (0 : ℚ) < Nat.card (cohomology A 1) := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℚ) < Nat.card (cohomology A 2) := by exact_mod_cast Nat.card_pos
  positivity

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

/- English proof (translation)
Take `⟨f₁, z₁⟩` from `hG S.X₁ ‹_› h₁`. Use `f₁ 1` as an intermediate fact. Use `z₁ 3 le_rfl` as an intermediate fact. Use `(hG S.X₂ ‹_› h₂).1 1` as an intermediate fact. Use `(hG S.X₃ ‹_› h₃).1 1` as an intermediate fact.

Conclude with `eulerChar_shortExact_of_finite hS`.
-/
theorem eulerChar_shortExact_of_mem (hG : HasFiniteCohomology k G P) (hS : S.ShortExact)
    [Finite S.X₁] [Finite S.X₂] [Finite S.X₃] (h₁ : P (Nat.card S.X₁))
    (h₂ : P (Nat.card S.X₂)) (h₃ : P (Nat.card S.X₃)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  obtain ⟨f₁, z₁⟩ := hG S.X₁ ‹_› h₁
  have := f₁ 1
  have := z₁ 3 le_rfl
  have := (hG S.X₂ ‹_› h₂).1 1
  have := (hG S.X₃ ‹_› h₃).1 1
  exact eulerChar_shortExact_of_finite hS

/- English proof (translation)
Establish `hinj : Function.Injective S.f.hom` using `(Rep.mono_iff_injective _).1 hS.mono_f`. Establish `hsurj : Function.Surjective S.g.hom` using `(Rep.epi_iff_surjective _).1 hS.epi_g`. Establish `: Finite S.X₁` using `Finite.of_injective _ hinj`. Establish `: Finite S.X₃` using `Finite.of_surjective _ hsurj`. Establish `h₁ : P (Nat.card S.X₁)` using `hP _ _ (AddSubgroup.card_dvd_of_injective S.f.hom.toLinearMap.toAddMonoidHom hinj) h₂`.

Establish `h₃ : P (Nat.card S.X₃)`. Use `hP _ _ ⟨Nat.card (LinearMap.ker S.g.hom.toLinearMap), ?_⟩ h₂` and prove the remaining obligations. Rewrite using `[card_eq_card_ker_mul_card_range S.g.hom.toLinearMap, LinearMap.range_eq_top.2 hsurj, mul_comm]`. Use `congr 1`. Conclude with `Nat.card_congr (Submodule.topEquiv).toEquiv`.

Conclude with `eulerChar_shortExact_of_mem hG hS h₁ h₂ h₃`.
-/
theorem eulerChar_shortExact (hP : ∀ m n, m ∣ n → P n → P m) (hG : HasFiniteCohomology k G P)
    (hS : S.ShortExact) [Finite S.X₂] (h₂ : P (Nat.card S.X₂)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have : Finite S.X₁ := Finite.of_injective _ hinj
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have h₁ : P (Nat.card S.X₁) :=
    hP _ _ (AddSubgroup.card_dvd_of_injective S.f.hom.toLinearMap.toAddMonoidHom hinj) h₂
  have h₃ : P (Nat.card S.X₃) := by
    refine hP _ _ ⟨Nat.card (LinearMap.ker S.g.hom.toLinearMap), ?_⟩ h₂
    rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap,
      LinearMap.range_eq_top.2 hsurj, mul_comm]
    congr 1
    exact Nat.card_congr (Submodule.topEquiv).toEquiv
  exact eulerChar_shortExact_of_mem hG hS h₁ h₂ h₃

noncomputable def eulerCharUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) : ℚˣ :=
  haveI := A.property.1
  haveI := A.property.2.1
  Units.mk0 (eulerChar A.obj) (eulerChar_pos hG A.obj A.property.2.2).ne'

/- English proof (translation)
The claim follows from `A.property.1 (eulerCharUnit hG A : ℚ) = eulerChar A.obj := rfl`.
-/
theorem coe_eulerCharUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) :
    haveI := A.property.1
    (eulerCharUnit hG A : ℚ) = eulerChar A.obj :=
  rfl

noncomputable def eulerCharHom (hG : HasFiniteCohomology k G P) :
    GrothendieckGroup k G P →+ Additive ℚˣ :=
  QuotientAddGroup.lift (grothendieckRelations k G P)
    (FreeAbelianGroup.lift fun A => Additive.ofMul (eulerCharUnit hG A)) (by
      rw [grothendieckRelations, AddSubgroup.closure_le]
      rintro x ⟨S, h₁, h₂, h₃, hS, rfl⟩
      have := h₁.1
      have := h₂.1
      have := h₃.1
      have := h₁.2.1
      have := h₂.2.1
      have := h₃.2.1
      have key := eulerChar_shortExact_of_mem hG hS h₁.2.2 h₂.2.2 h₃.2.2
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [sub_sub, sub_eq_zero, ← ofMul_mul]
      congr 1
      ext
      simp only [Units.val_mul, coe_eulerCharUnit]
      exact key)

end Hypothesis

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G)

/- English proof (translation)
Simplify using `only [eulerChar]`. Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.card_congr (shapiroIso U B q).toLinearEquiv.toEquiv]`.
-/
theorem eulerChar_coind (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] :
    eulerChar (Rep.coind (U : Subgroup G).subtype B) = eulerChar B := by
  simp only [eulerChar]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.card_congr (shapiroIso U B q).toLinearEquiv.toEquiv]

/- English proof (translation)
The claim follows from `(eulerChar_coind U _).symm`.
-/
theorem eulerChar_res_eq_eulerChar_coind (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar (Rep.res (U : Subgroup G).subtype A) =
      eulerChar (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  (eulerChar_coind U _).symm

noncomputable def coindValues (B : Rep.{u} k (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype B →+ (G ⧸ (U : Subgroup G) → B) :=
  AddMonoidHom.mk' (fun f c => f.1 (Quotient.out c)⁻¹) fun _ _ => rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
/- English proof (translation)
Introduce `f g hfg`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul (U : Subgroup G) x⁻¹`. Establish `hx : x = (U : Subgroup G).subtype u * (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)))⁻¹`.

Rewrite using `[show (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G))) = x⁻¹ * u from hu]`. Simplify using the standard rewrite rules. Establish `h` using `congrFun hfg (QuotientGroup.mk x⁻¹)`. Simplify using `only [coindValues, AddMonoidHom.mk'_apply] at h`. Rewrite using `[hx, f.2 u, g.2 u, h]`.
-/
theorem coindValues_injective (B : Rep.{u} k (U : Subgroup G)) :
    Function.Injective (coindValues U B) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) x⁻¹
  have hx : x = (U : Subgroup G).subtype u * (Quotient.out
      (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)))⁻¹ := by
    rw [show (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G))) = x⁻¹ * u from hu]
    simp
  have h := congrFun hfg (QuotientGroup.mk x⁻¹)
  simp only [coindValues, AddMonoidHom.mk'_apply] at h
  rw [hx, f.2 u, g.2 u, h]

instance finite_coind (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Finite (Rep.coind (U : Subgroup G).subtype B) :=
  Finite.of_injective _ (coindValues_injective U B)

/- English proof (translation)
Establish `h` using `AddSubgroup.card_dvd_of_injective (coindValues U B) (coindValues_injective U B)`. Rewrite `h` using `[Nat.card_fun]`. Then use the resulting hypothesis.
-/
theorem card_coind_dvd (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Nat.card (Rep.coind (U : Subgroup G).subtype B) ∣ Nat.card B ^ (U : Subgroup G).index := by
  have h := AddSubgroup.card_dvd_of_injective (coindValues U B) (coindValues_injective U B)
  rwa [Nat.card_fun] at h

end Shapiro

end GroundTheory.ProfCoh
