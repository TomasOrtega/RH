import Mathlib
import GroundTheory.LocalFields.ArtinConductorIrreducible
import GroundTheory.LocalFields.ArtinConductorDiscriminant
import GroundTheory.LocalFields.BrauerInduction

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

open scoped Classical

section Dual

variable {G : Type*} [Group G]

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `hχ`. Conclude with `⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, ρ.dual,`. Use function extensionality and compare the values at `fun g ↦ char_dual ρ g⟩`.
-/
theorem IsCharacter.comp_inv {χ : G → ℂ} (hχ : IsCharacter χ) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (σ : Representation ℂ G W), σ.character = fun g ↦ χ g⁻¹ := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  exact ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, ρ.dual,
    funext fun g ↦ char_dual ρ g⟩

end Dual

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Linear

/- English proof (translation)
Simplify using `only [charArtinConductor, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]`.
-/
theorem charArtinConductor_add (f g : (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (f + g) = charArtinConductor K L f + charArtinConductor K L g := by
  simp only [charArtinConductor, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

/- English proof (translation)
Simplify using `only [charArtinConductor, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem charArtinConductor_zsmul (n : ℤ) (f : (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (n • f) = n * charArtinConductor K L f := by
  simp only [charArtinConductor, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  ring

/- English proof (translation)
Simplify using `[charArtinConductor]`.
-/
theorem charArtinConductor_zero : charArtinConductor K L (0 : (L ≃ₐ[K] L) → ℂ) = 0 := by
  simp [charArtinConductor]

end Linear

variable [IsGalois K L]

/- English proof (translation)
Use `set M := IntermediateField.fixedField H`. Set `e : H ≃* (L ≃ₐ[M] L)` to `(MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans (IntermediateField.fixingSubgroupEquiv M)`. Establish `hcomp : H.subtype.comp e.symm.toMonoidHom = AlgEquiv.restrictScalarsHom K`. Use extensionality with `σ x`. Both sides reduce to the same expression.

Take `⟨n, hn⟩` from `exists_nat_charArtinConductor_inducedFun M (l.comp e.symm.toMonoidHom)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn, inducedFun_eq_indFun, ← hcomp, indLin]`. Use `congr 1`. Use `(indFun_comp_toMonoidHom H.subtype e.symm (fun h ↦ (l h : ℂ))).symm` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression.
-/
theorem exists_nat_charArtinConductor_indLin (H : Subgroup (L ≃ₐ[K] L)) (l : H →* ℂˣ) :
    ∃ n : ℕ, charArtinConductor K L (indLin H l) = n := by
  set M := IntermediateField.fixedField H
  let e : H ≃* (L ≃ₐ[M] L) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
      (IntermediateField.fixingSubgroupEquiv M)
  have hcomp : H.subtype.comp e.symm.toMonoidHom = AlgEquiv.restrictScalarsHom K := by
    ext σ x
    rfl
  obtain ⟨n, hn⟩ := exists_nat_charArtinConductor_inducedFun M (l.comp e.symm.toMonoidHom)
  refine ⟨n, ?_⟩
  rw [← hn, inducedFun_eq_indFun, ← hcomp, indLin]
  congr 1
  convert (indFun_comp_toMonoidHom H.subtype e.symm (fun h ↦ (l h : ℂ))).symm
  rfl

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨H, -, l, rfl⟩` from `hx`. Take `⟨n, hn⟩` from `exists_nat_charArtinConductor_indLin H l`. Conclude with `⟨n, by rw [hn]; push_cast; rfl⟩`.

Consider the case `zero => exact ⟨0, by rw [charArtinConductor_zero]; simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [charArtinConductor_add, ha, hb]; push_cast; ring⟩`.

Consider the case `smul n x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨n * a, by rw [charArtinConductor_zsmul, ha]; push_cast; ring⟩`.
-/
theorem exists_int_charArtinConductor_of_mem_spanZ {E : Subgroup (L ≃ₐ[K] L) → Prop}
    {f : (L ≃ₐ[K] L) → ℂ} (hf : f ∈ spanZ E) : ∃ k : ℤ, charArtinConductor K L f = k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, -, l, rfl⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_charArtinConductor_indLin H l
    exact ⟨n, by rw [hn]; push_cast; rfl⟩
  | zero => exact ⟨0, by rw [charArtinConductor_zero]; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [charArtinConductor_add, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨n * a, by rw [charArtinConductor_zsmul, ha]; push_cast; ring⟩

section Conditional

variable {E : Subgroup (L ≃ₐ[K] L) → Prop}

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_int_charArtinConductor_of_mem_spanZ h`. Establish `hq : artinConductor ρ = k`. Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Rewrite using `[artinConductor_eq_charArtinConductor, hk]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hk0 : 0 ≤ k`. Use `artinConductor_nonneg ρ` as an intermediate fact. Rewrite `this` using `[hq]`. Conclude with `this` after adjusting the coercions.

Use `⟨k.toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `(Int.toNat_of_nonneg hk0).symm` after adjusting the coercions.
-/
theorem exists_nat_artinConductor_of_mem_spanZ {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (L ≃ₐ[K] L) V) (h : ρ.character ∈ spanZ E) :
    ∃ n : ℕ, artinConductor ρ = n := by
  obtain ⟨k, hk⟩ := exists_int_charArtinConductor_of_mem_spanZ h
  have hq : artinConductor ρ = k := by
    apply Rat.cast_injective (α := ℂ)
    rw [artinConductor_eq_charArtinConductor, hk]
    push_cast
    rfl
  have hk0 : 0 ≤ k := by
    have := artinConductor_nonneg ρ
    rw [hq] at this
    exact_mod_cast this
  refine ⟨k.toNat, ?_⟩
  rw [hq]
  exact_mod_cast (Int.toNat_of_nonneg hk0).symm

omit [IsGalois K L] in

/- English proof (translation)
Introduce `σ τ`. Simplify using `only [artinCharacter_conj]`.
-/
theorem isClassFun_artinCharacter : IsClassFun (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) := by
  intro σ τ
  simp only [artinCharacter_conj]

omit [IsGalois K L] in

/- English proof (translation)
Introduce `σ τ`. Establish `h1 : τ * σ * τ⁻¹ = 1 ↔ σ = 1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun x ↦ τ⁻¹ * x * τ) h` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Establish `h0 : τ * σ * τ⁻¹ ∈ lowerRamificationGroup K L 0 ↔ σ ∈ lowerRamificationGroup K L 0`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `(lowerRamificationGroup_normal K L 0).conj_mem _ h τ⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `h`. Conclude with `(lowerRamificationGroup_normal K L 0).conj_mem _ h τ`.

Simplify using `only [swanCharacter, artinCharacter_conj]`. Use `congr 3`. Conclude with `if_congr h1 rfl rfl`. Conclude with `if_congr h0 rfl rfl`.
-/
theorem isClassFun_swanCharacter : IsClassFun (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) := by
  classical
  intro σ τ
  have h1 : τ * σ * τ⁻¹ = 1 ↔ σ = 1 := by
    constructor
    · intro h
      have := congrArg (fun x ↦ τ⁻¹ * x * τ) h
      simpa [mul_assoc] using this
    · rintro rfl
      simp
  have h0 : τ * σ * τ⁻¹ ∈ lowerRamificationGroup K L 0 ↔ σ ∈ lowerRamificationGroup K L 0 := by
    constructor
    · intro h
      have := (lowerRamificationGroup_normal K L 0).conj_mem _ h τ⁻¹
      simpa [mul_assoc] using this
    · intro h
      exact (lowerRamificationGroup_normal K L 0).conj_mem _ h τ
  simp only [swanCharacter, artinCharacter_conj]
  congr 3
  · exact if_congr h1 rfl rfl
  · exact if_congr h0 rfl rfl

omit [IsGalois K L] in

/- English proof (translation)
Rewrite using `[charInner_apply, charArtinConductor]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _`.
-/
theorem charInner_artinCharacter (ψ : (L ≃ₐ[K] L) → ℂ) :
    charInner (L ≃ₐ[K] L) (fun σ ↦ (artinCharacter K L σ : ℂ)) ψ =
      charArtinConductor K L (fun σ ↦ ψ σ⁻¹) := by
  rw [charInner_apply, charArtinConductor]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _

omit [IsGalois K L] in

/- English proof (translation)
Rewrite using `[charInner_apply, charSwanConductor]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _`.
-/
theorem charInner_swanCharacter (ψ : (L ≃ₐ[K] L) → ℂ) :
    charInner (L ≃ₐ[K] L) (fun σ ↦ (swanCharacter K L σ : ℂ)) ψ =
      charSwanConductor K L (fun σ ↦ ψ σ⁻¹) := by
  rw [charInner_apply, charSwanConductor]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _

/- English proof (translation)
Rewrite using `[isCharacter_iff]`. Use `⟨isClassFun_artinCharacter, fun ψ hψ ↦ ?_⟩` and prove the remaining obligations. Take `⟨W, _, _, _, σ, hσ⟩` from `(mem_irrChars.mp hψ).isCharacter.comp_inv`. Take `⟨n, hn⟩` from `exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[charInner_artinCharacter, ← hσ, ← artinConductor_eq_charArtinConductor, hn]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isCharacter_artinCharacter_of (hB : ∀ χ : (L ≃ₐ[K] L) → ℂ, IsCharacter χ → χ ∈ spanZ E) :
    IsCharacter (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) := by
  rw [isCharacter_iff]
  refine ⟨isClassFun_artinCharacter, fun ψ hψ ↦ ?_⟩
  obtain ⟨W, _, _, _, σ, hσ⟩ := (mem_irrChars.mp hψ).isCharacter.comp_inv
  obtain ⟨n, hn⟩ := exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))
  refine ⟨n, ?_⟩
  rw [charInner_artinCharacter, ← hσ, ← artinConductor_eq_charArtinConductor, hn]
  push_cast
  rfl

/- English proof (translation)
Rewrite using `[isCharacter_iff]`. Use `⟨isClassFun_swanCharacter, fun ψ hψ ↦ ?_⟩` and prove the remaining obligations. Take `⟨W, _, _, _, σ, hσ⟩` from `(mem_irrChars.mp hψ).isCharacter.comp_inv`. Take `⟨n, hn⟩` from `exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))`. Take `⟨k, hk⟩` from `exists_nat_swanConductor_eq_of_artinConductor_eq σ hn`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[charInner_swanCharacter, ← hσ, ← swanConductor_eq_charSwanConductor, hk]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isCharacter_swanCharacter_of (hB : ∀ χ : (L ≃ₐ[K] L) → ℂ, IsCharacter χ → χ ∈ spanZ E) :
    IsCharacter (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) := by
  rw [isCharacter_iff]
  refine ⟨isClassFun_swanCharacter, fun ψ hψ ↦ ?_⟩
  obtain ⟨W, _, _, _, σ, hσ⟩ := (mem_irrChars.mp hψ).isCharacter.comp_inv
  obtain ⟨n, hn⟩ := exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))
  obtain ⟨k, hk⟩ := exists_nat_swanConductor_eq_of_artinConductor_eq σ hn
  refine ⟨k, ?_⟩
  rw [charInner_swanCharacter, ← hσ, ← swanConductor_eq_charSwanConductor, hk]
  push_cast
  rfl

end Conditional

section Final

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in

/- English proof (translation)
The claim follows from `mem_spanZ_of_mono (fun _ hK _ hψ ↦ hK.exists_eq_indLin hψ) hχ`.
-/
theorem IsCharacter.mem_spanZ_isElementary {χ : (L ≃ₐ[K] L) → ℂ} (hχ : IsCharacter χ) :
    χ ∈ spanZ (IsElementary (G := L ≃ₐ[K] L)) :=
  mem_spanZ_of_mono (fun _ hK _ hψ ↦ hK.exists_eq_indLin hψ) hχ

/- English proof (translation)
The claim follows from `exists_nat_artinConductor_of_mem_spanZ ρ (isCharacter_character ρ).mem_spanZ_isElementary`.
-/
theorem exists_nat_artinConductor {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ∃ n : ℕ, artinConductor ρ = n :=
  exists_nat_artinConductor_of_mem_spanZ ρ (isCharacter_character ρ).mem_spanZ_isElementary

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `hχ`. Take `⟨n, hn⟩` from `exists_nat_artinConductor ρ`. Conclude with `⟨n, by rw [← artinConductor_eq_charArtinConductor, hn]; push_cast; rfl⟩`.
-/
theorem exists_nat_charArtinConductor {χ : (L ≃ₐ[K] L) → ℂ} (hχ : IsCharacter χ) :
    ∃ n : ℕ, charArtinConductor K L χ = n := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨n, hn⟩ := exists_nat_artinConductor ρ
  exact ⟨n, by rw [← artinConductor_eq_charArtinConductor, hn]; push_cast; rfl⟩

/- English proof (translation)
The claim follows from `let ⟨_, hn⟩ := exists_nat_artinConductor ρ exists_nat_swanConductor_eq_of_artinConductor_eq ρ hn`.
-/
theorem exists_nat_swanConductor {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ∃ k : ℕ, swanConductor ρ = k :=
  let ⟨_, hn⟩ := exists_nat_artinConductor ρ
  exists_nat_swanConductor_eq_of_artinConductor_eq ρ hn

/- English proof (translation)
The claim follows from `isCharacter_artinCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary`.
-/
theorem isCharacter_artinCharacter : IsCharacter (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) :=
  isCharacter_artinCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary

/- English proof (translation)
The claim follows from `isCharacter_swanCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary`.
-/
theorem isCharacter_swanCharacter : IsCharacter (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) :=
  isCharacter_swanCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary

/- English proof (translation)
Establish `hf : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, charArtinConductor K L χ = n` using `fun χ hχ ↦ exists_nat_charArtinConductor (mem_irrChars.mp hχ).isCharacter`. Establish `hd : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, χ 1 = n` using `fun χ hχ ↦`. Set `⟨n, _, hn⟩` to `(mem_irrChars.mp hχ).exists_one`. Use the proof step `⟨n, hn⟩`. Use `choose! f hf using hf`.

Use `choose! d hd using hd`. Take `⟨n, hn, hsum⟩` from `addVal_discr_eq_sum_irrChars (K := K) (L := L) b`. Use `⟨f, d, fun χ hχ ↦ ⟨hf χ hχ, hd χ hχ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`. Use `congr 1`.

Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Rewrite using `[hsum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun χ hχ ↦ by rw [hf χ hχ, hd χ hχ]`.
-/
theorem addVal_discr_eq_sum_irrChars_nat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    ∃ f d : ((L ≃ₐ[K] L) → ℂ) → ℕ, (∀ χ ∈ irrChars (L ≃ₐ[K] L),
      charArtinConductor K L χ = f χ ∧ χ 1 = d χ) ∧
      IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) =
        ((∑ χ ∈ irrChars (L ≃ₐ[K] L), d χ * f χ : ℕ) : ℕ∞) := by
  have hf : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, charArtinConductor K L χ = n := fun χ hχ ↦
    exists_nat_charArtinConductor (mem_irrChars.mp hχ).isCharacter
  have hd : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, χ 1 = n := fun χ hχ ↦
    let ⟨n, _, hn⟩ := (mem_irrChars.mp hχ).exists_one
    ⟨n, hn⟩
  choose! f hf using hf
  choose! d hd using hd
  obtain ⟨n, hn, hsum⟩ := addVal_discr_eq_sum_irrChars (K := K) (L := L) b
  refine ⟨f, d, fun χ hχ ↦ ⟨hf χ hχ, hd χ hχ⟩, ?_⟩
  rw [hn]
  congr 1
  apply Nat.cast_injective (R := ℂ)
  rw [hsum]
  push_cast
  exact Finset.sum_congr rfl fun χ hχ ↦ by rw [hf χ hχ, hd χ hχ]

/- English proof (translation)
Take `⟨f, d, hfd, hval⟩` from `addVal_discr_eq_sum_irrChars_nat b`. Use `⟨f, d, hfd, ?_⟩` and prove the remaining obligations. Establish `hne : Algebra.discr 𝒪[K] b ≠ 0`. Introduce `h0`. Rewrite `hval` using `[h0, IsDiscreteValuationRing.addVal_zero]`.

Conclude with `ENat.top_ne_natCast _ hval`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨m, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`. Establish `hm : m = ∑ χ ∈ irrChars (L ≃ₐ[K] L), d χ * f χ`. Use `IsDiscreteValuationRing.addVal_def _ u hϖ m hu` as an intermediate fact.

Rewrite `this` using `[hval]`. Conclude with `this.symm` after adjusting the coercions. Rewrite using `[hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, hm]`. Repeatedly rewrite using `[← pow_mul]`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun χ _ ↦ mul_comm _ _`.
-/
theorem span_discr_eq_prod_irrChars {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    ∃ f d : ((L ≃ₐ[K] L) → ℂ) → ℕ, (∀ χ ∈ irrChars (L ≃ₐ[K] L),
      charArtinConductor K L χ = f χ ∧ χ 1 = d χ) ∧
      Ideal.span {Algebra.discr 𝒪[K] b} =
        ∏ χ ∈ irrChars (L ≃ₐ[K] L), (IsLocalRing.maximalIdeal 𝒪[K] ^ f χ) ^ d χ := by
  obtain ⟨f, d, hfd, hval⟩ := addVal_discr_eq_sum_irrChars_nat b
  refine ⟨f, d, hfd, ?_⟩
  have hne : Algebra.discr 𝒪[K] b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hval
    exact ENat.top_ne_natCast _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hm : m = ∑ χ ∈ irrChars (L ≃ₐ[K] L), d χ * f χ := by
    have := IsDiscreteValuationRing.addVal_def _ u hϖ m hu
    rw [hval] at this
    exact_mod_cast this.symm
  rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, hm]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_congr rfl fun χ _ ↦ mul_comm _ _

end Final

end GroundTheory.LocalField
