import Mathlib
import GroundTheory.AutomorphicForms.InductionParabolic

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {ρ' : Representation ℂ G V'}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

/- English proof (translation)
Use `⟨hρ, fun K hKc hKo => ?_⟩` and prove the remaining obligations. Use `hρ'.2 K hKc hKo` as an intermediate fact. Conclude with `Module.Finite.of_injective (fixedMap ρ f K) (fixedMap_injective ρ hf)`.
-/
theorem isAdmissible_of_injective (hρ : IsSmooth ρ) (hρ' : IsAdmissible ρ')
    (f : Representation.IntertwiningMap ρ ρ') (hf : Function.Injective f) : IsAdmissible ρ := by
  refine ⟨hρ, fun K hKc hKo => ?_⟩
  have := hρ'.2 K hKc hKo
  exact Module.Finite.of_injective (fixedMap ρ f K) (fixedMap_injective ρ hf)

end General

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

section Permute

variable (F) in

def permuteGL (s : Equiv.Perm (Fin n)) : GL (Fin n) F ≃* GL (Fin n) F :=
  Units.mapEquiv (reindexAlgEquiv F F s).toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem permuteGL_apply (s : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (i j : Fin n) :
    permuteGL F s g i j = g (s.symm i) (s.symm j) := rfl

/- English proof (translation)
Rewrite using `[mem_integralGL_iff, mem_integralGL_iff, ← map_inv]`. Simplify using `only [permuteGL_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Simplify using `using h1 (s i) (s j)`. Simplify using `using h2 (s i) (s j)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨fun i j => h1 _ _, fun i j => h2 _ _⟩`.
-/
theorem permuteGL_mem_integralGL_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ integralGL F n ↔ g ∈ integralGL F n := by
  rw [mem_integralGL_iff, mem_integralGL_iff, ← map_inv]
  simp only [permuteGL_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (s i) (s j)
    · simpa using h2 (s i) (s j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

/- English proof (translation)
Rewrite using `[mem_blockUpper, mem_blockUpper]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Use `@h (s i) (s j) hij` as an intermediate fact. Simplify `this` using `[permuteGL_apply]`.

Introduce `h i j hij`. Rewrite using `[permuteGL_apply]`. Conclude with `h (show β (s (s.symm j)) < β (s (s.symm i)) by simpa using hij)`.
-/
theorem permuteGL_mem_blockUpper_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ blockUpper F n β ↔ g ∈ blockUpper F n (β ∘ s) := by
  rw [mem_blockUpper, mem_blockUpper]
  constructor
  · intro h i j hij
    have := @h (s i) (s j) hij
    simpa [permuteGL_apply] using this
  · intro h i j hij
    rw [permuteGL_apply]
    exact h (show β (s (s.symm j)) < β (s (s.symm i)) by simpa using hij)

end Permute

/- English proof (translation)
Use `set s : Equiv.Perm (Fin n) := Tuple.sort β`. Establish `hs : Monotone (β ∘ s)` using `Tuple.monotone_sort β`. Take `⟨p, hp, k, hk, hpk⟩` from `exists_blockUpper_mul_integralGL F n hs ((permuteGL F s).symm g)`. Use `⟨permuteGL F s p, (permuteGL_mem_blockUpper_iff s).2 hp, permuteGL F s k, (permuteGL_mem_integralGL_iff s).2 hk, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← hpk, MulEquiv.apply_symm_apply]`.
-/
theorem exists_blockUpper_mul_integralGL' (g : GL (Fin n) F) :
    ∃ p ∈ blockUpper F n β, ∃ k ∈ integralGL F n, g = p * k := by
  set s : Equiv.Perm (Fin n) := Tuple.sort β
  have hs : Monotone (β ∘ s) := Tuple.monotone_sort β
  obtain ⟨p, hp, k, hk, hpk⟩ :=
    exists_blockUpper_mul_integralGL F n hs ((permuteGL F s).symm g)
  refine ⟨permuteGL F s p, (permuteGL_mem_blockUpper_iff s).2 hp, permuteGL F s k,
    (permuteGL_mem_integralGL_iff s).2 hk, ?_⟩
  rw [← map_mul, ← hpk, MulEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[levi, Subgroup.coe_inf]`. Conclude with `(Measures.isClosed_blockUpper F n β).inter (Measures.isClosed_blockUpper F n (OrderDual.toDual ∘ β))`.
-/
theorem isClosed_levi : IsClosed (levi F n β : Set (GL (Fin n) F)) := by
  rw [levi, Subgroup.coe_inf]
  exact (Measures.isClosed_blockUpper F n β).inter
    (Measures.isClosed_blockUpper F n (OrderDual.toDual ∘ β))

/- English proof (translation)
Use `show ((NNReal.sqrt (modularCharacter p) : ℝ) : ℂ) = 1`. Rewrite using `[Measures.modularCharacter_eq_one_of_mem_integralGL p hp]`. Simplify using the standard rewrite rules.
-/
theorem sqrtModular_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : sqrtModular F n β p = 1 := by
  show ((NNReal.sqrt (modularCharacter p) : ℝ) : ℂ) = 1
  rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
  simp

/- English proof (translation)
Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `isClosed_levi.isClosedEmbedding_subtypeVal.isCompact_preimage hK`.
-/
theorem isCompact_subgroupOf_levi {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) :
    IsCompact ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [Subgroup.coe_subgroupOf]
  exact isClosed_levi.isClosedEmbedding_subtypeVal.isCompact_preimage hK

/- English proof (translation)
Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hK.preimage continuous_subtype_val`.
-/
theorem isOpen_subgroupOf_levi {K : Subgroup (GL (Fin n) F)}
    (hK : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [Subgroup.coe_subgroupOf]
  exact hK.preimage continuous_subtype_val

section Admissible

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[Subgroup.mem_subgroupOf]`. Establish `h1` using `((f : parabolicIndSpace F n β σ).2.1 (leviIncl y) k)`. Rewrite `h1` using `[inflateTwist_apply, leviProj_leviIncl, sqrtModular_of_mem_integralGL _ (congruenceSubgroup_le F n m hy), one_smul]`. Rewrite using `[← h1]`.

Establish `hc : k⁻¹ * (y : GL (Fin n) F) * k ∈ congruenceSubgroup F n m`. Simplify using `using conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem hk) hy`. Establish `h2` using `congrArg (fun x : parabolicIndSpace F n β σ => (x : GL (Fin n) F → W) k) (f.2 _ hc)`. Simplify using `only [coe_indRep_apply] at h2`. Rewrite using `[show ((leviIncl y : blockUpper F n β) : GL (Fin n) F) * k = k * (k⁻¹ * (y : GL (Fin n) F) * k) by rw [leviIncl_coe]; group]`.

Conclude with `h2`.
-/
theorem apply_mem_fixedVectors {m : ℕ}
    (f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) :
    ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) k ∈
      fixedVectors σ ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 (leviIncl y) k)
  rw [inflateTwist_apply, leviProj_leviIncl,
    sqrtModular_of_mem_integralGL _ (congruenceSubgroup_le F n m hy), one_smul] at h1
  rw [← h1]
  have hc : k⁻¹ * (y : GL (Fin n) F) * k ∈ congruenceSubgroup F n m := by
    simpa using conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem hk) hy
  have h2 := congrArg (fun x : parabolicIndSpace F n β σ => (x : GL (Fin n) F → W) k)
    (f.2 _ hc)
  simp only [coe_indRep_apply] at h2
  rw [show ((leviIncl y : blockUpper F n β) : GL (Fin n) F) * k = k * (k⁻¹ * (y : GL (Fin n) F) * k)
    by rw [leviIncl_coe]; group]
  exact h2

/- English proof (translation)
Take `⟨p, hp, k, hk, rfl⟩` from `exists_blockUpper_mul_integralGL' (β := β) x`. Use `set K₀ := integralGL F n`. Use `set Km := congruenceSubgroup F n m`. Use `set c : K₀ ⧸ Km.subgroupOf K₀ := QuotientGroup.mk (⟨k, hk⟩ : K₀)`. Use `⟨⟨p, hp⟩, c, fun f => ?_⟩` and prove the remaining obligations.

Establish `h1` using `((f : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ k)`. Simplify using `only [inflateTwist_apply] at h1`. Rewrite using `[h1]`. Take `⟨y, hyk⟩` from `QuotientGroup.mk_out_eq_mul (Km.subgroupOf K₀) (⟨k, hk⟩ : K₀)`. Establish `hym : (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) ∈ Km` using `Subgroup.mem_subgroupOf.1 ((Km.subgroupOf K₀).inv_mem y.2)`.

Establish `h2` using `congrArg (fun z : parabolicIndSpace F n β σ => (z : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F)) (f.2 _ hym)`. Simplify using `only [coe_indRep_apply] at h2`. Establish `h3 : ((Quotient.out c : K₀) : GL (Fin n) F) * (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) = k`. Establish `: (Quotient.out c : K₀) = ⟨k, hk⟩ * (y : K₀)` using `hyk`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[h3]`. Rewrite using `[h2]`.
-/
theorem exists_apply_eq_out (m : ℕ) (x : GL (Fin n) F) :
    ∃ (p : blockUpper F n β) (c : integralGL F n ⧸ (congruenceSubgroup F n m).subgroupOf
      (integralGL F n)), ∀ f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
      ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x =
        sqrtModular F n β p • σ (leviProj F n β p)
          (((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : integralGL F n) : GL (Fin n) F)) := by
  obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) x
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  set c : K₀ ⧸ Km.subgroupOf K₀ := QuotientGroup.mk (⟨k, hk⟩ : K₀)
  refine ⟨⟨p, hp⟩, c, fun f => ?_⟩
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ k)
  simp only [inflateTwist_apply] at h1
  rw [h1]
  obtain ⟨y, hyk⟩ := QuotientGroup.mk_out_eq_mul (Km.subgroupOf K₀) (⟨k, hk⟩ : K₀)
  have hym : (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) ∈ Km :=
    Subgroup.mem_subgroupOf.1 ((Km.subgroupOf K₀).inv_mem y.2)
  have h2 := congrArg
    (fun z : parabolicIndSpace F n β σ => (z : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F))
    (f.2 _ hym)
  simp only [coe_indRep_apply] at h2
  have h3 : ((Quotient.out c : K₀) : GL (Fin n) F) * (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) = k := by
    have : (Quotient.out c : K₀) = ⟨k, hk⟩ * (y : K₀) := hyk
    rw [this]
    simp
  rw [h3] at h2
  rw [h2]

/- English proof (translation)
Use `⟨isSmooth_parabolicInd σ, fun K hKc hKo => ?_⟩` and prove the remaining obligations. Take `⟨m, -, hm⟩` from `(hasBasis_nhds_one F n).mem_iff.1 (hKo.mem_nhds K.one_mem)`. Establish `hle : congruenceSubgroup F n m ≤ K` using `hm`. It suffices to establish `h : FiniteDimensional ℂ (fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) from Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)`. Use `set K₀ := integralGL F n`.

Use `set Km := congruenceSubgroup F n m`. Establish `: CompactSpace K₀` using `isCompact_iff_compactSpace.1 (isCompact_integralGL F n)`. Establish `hQ : Finite (K₀ ⧸ Km.subgroupOf K₀)`. Use `Subgroup.quotient_finite_of_isOpen _ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `(isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val`. Use `set L : Subgroup (levi F n β) := Km.subgroupOf (levi F n β)`. Establish `hL : FiniteDimensional ℂ (fixedVectors σ L)` using `hσ.2 L (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)) (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m))`. Set `ev : fixedVectors (parabolicInd F n β σ) Km →ₗ[ℂ] (K₀ ⧸ Km.subgroupOf K₀ → fixedVectors σ L)` to `LinearMap.pi fun c => LinearMap.codRestrict _ ((LinearMap.proj (((Quotient.out c : K₀) : GL (Fin n) F))).comp ((parabolicIndSpace F n β σ).subtype.comp (fixedVectors _ Km).subtype)) fun f => apply_mem_fixedVectors f (Quotient.out c).2`. Establish `hinj : Function.Injective ev`.

Introduce `f g hfg`. Establish `hz : ∀ c : K₀ ⧸ Km.subgroupOf K₀, ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F) = ((g : parabolicIndSpace F n β σ) : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F)` using `fun c => congrArg Subtype.val (congrFun hfg c)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Take `⟨p, c, hp⟩` from `exists_apply_eq_out (σ := σ) m x`. Rewrite using `[hp f, hp g, hz c]`. Conclude with `FiniteDimensional.of_injective ev hinj`.
-/
theorem isAdmissible_parabolicInd (hσ : IsAdmissible σ) : IsAdmissible (parabolicInd F n β σ) := by
  classical
  refine ⟨isSmooth_parabolicInd σ, fun K hKc hKo => ?_⟩
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hKo.mem_nhds K.one_mem)
  have hle : congruenceSubgroup F n m ≤ K := hm
  suffices h : FiniteDimensional ℂ
      (fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) from
    Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  set L : Subgroup (levi F n β) := Km.subgroupOf (levi F n β)
  have hL : FiniteDimensional ℂ (fixedVectors σ L) :=
    hσ.2 L (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m))

  let ev : fixedVectors (parabolicInd F n β σ) Km →ₗ[ℂ] (K₀ ⧸ Km.subgroupOf K₀ → fixedVectors σ L) :=
    LinearMap.pi fun c =>
      LinearMap.codRestrict _
        ((LinearMap.proj (((Quotient.out c : K₀) : GL (Fin n) F))).comp
          ((parabolicIndSpace F n β σ).subtype.comp (fixedVectors _ Km).subtype))
        fun f => apply_mem_fixedVectors f (Quotient.out c).2
  have hinj : Function.Injective ev := by
    intro f g hfg
    have hz : ∀ c : K₀ ⧸ Km.subgroupOf K₀,
        ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F)
          = ((g : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : K₀) : GL (Fin n) F) :=
      fun c => congrArg Subtype.val (congrFun hfg c)
    apply Subtype.ext
    apply Subtype.ext
    funext x
    obtain ⟨p, c, hp⟩ := exists_apply_eq_out (σ := σ) m x
    rw [hp f, hp g, hz c]
  exact FiniteDimensional.of_injective ev hinj

end Admissible

end Parabolic

end GroundTheory.Automorphic
