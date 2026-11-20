import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetCoeff

/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ`. Establish `hKc` using `GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m`. Establish `hKo` using `GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m`. Establish `hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π) ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N β))` using `fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)`. Take `⟨⟨w, hw⟩, hwy⟩` from `GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩`.

Establish `hqw : Representation.Coinvariants.mk (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y` using `congrArg Subtype.val hwy`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 1 := by`. Establish `h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0` using `fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')`. Use `push_neg at h0`. Take `⟨f, hf⟩` from `h0`.

Conclude with `⟨(f y)⁻¹ • f, by simp [hf]⟩`. Establish `hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j`. Introduce `j g hg`. Conclude with `((show Commute a g from hcomm g hg).pow_left j)`. Establish `hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeU …`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro z hz`. Simplify using `using hz`. Consider the case `succ j ih`.

Introduce `z hz`. Use `hconj _ (ih z hz)` as an intermediate fact. Establish `e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a`. Rewrite using `[pow_succ]`. Use `group`.

Rewrite using `[e]` and apply the resulting hypothesis. Establish `hq : ∀ j : ℕ, Representation.Coinvariants.mk (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) = Λ ^ j • y`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp [hqw]`.

Consider the case `succ j ih`. Establish `e : π (a ^ (j + 1)) w = π a (π (a ^ j) w)`. Rewrite using `[pow_succ', map_mul, Module.End.mul_apply]`. Establish `e2` using `GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩ (π (a ^ j) w)`. Rewrite using `[e]`.

Use `e2.symm.trans ?_` and prove the remaining obligations. Rewrite using `[ih, map_smul, hΛ, smul_smul, pow_succ]`. Establish `hkey : ∀ j : ℕ, Representation.Coinvariants.mk (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) = Representation.Coinvariants.mk (π.comp (GroundTheory.Automorphic.Parabolic.unipotent …`. Introduce `j`. Use `GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm) (fun z hz => ?_) (fun g hg => ?_)` and prove the remaining obligations.

Establish `hz'` using `(Subgroup.mem_inf.1 (hpowz j z hz)).1`. Establish `hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹` using `by group`. Establish `: π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w)`. Simplify using `only [← Module.End.mul_apply, ← map_mul]`. Use `congr 2`.

Use `group`. Rewrite using `[this, hw _ hz']`. Establish `hc` using `hpowc j g (Subgroup.mem_inf.1 hg).2`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply, hw g (Subgroup.mem_inf.1 hg).1]`. Use `⟨w, f ∘ₗ Representation.Coinvariants.mk (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ (GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ GroundTheory.Automorphic.fixedProj π hπ.1 hKc …` and prove the remaining obligations.

Introduce `g hg`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`. Rewrite using `[GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]`. Introduce `j`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`. Rewrite using `[hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]`.
-/
theorem exists_coeff_geometric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  classical
  intro k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m
  have hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π)
      ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf
        (GroundTheory.Automorphic.Parabolic.levi k N β)) :=
    fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨⟨w, hw⟩, hwy⟩ :=
    GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩
  have hqw : Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y :=
    congrArg Subtype.val hwy
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π),
      f y = 1 := by
    have h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0 :=
      fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')
    push_neg at h0
    obtain ⟨f, hf⟩ := h0
    exact ⟨(f y)⁻¹ • f, by simp [hf]⟩

  have hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j := by
    intro j g hg
    exact ((show Commute a g from hcomm g hg).pow_left j)
  have hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β,
      (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
        GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β := by
    intro j
    induction j with
    | zero => intro z hz; simpa using hz
    | succ j ih =>
      intro z hz
      have := hconj _ (ih z hz)
      have e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a := by
        rw [pow_succ]; group
      rwa [e]
  have hq : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) =
      Λ ^ j • y := by
    intro j
    induction j with
    | zero => simp [hqw]
    | succ j ih =>
      have e : π (a ^ (j + 1)) w = π a (π (a ^ j) w) := by
        rw [pow_succ', map_mul, Module.End.mul_apply]
      have e2 := GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩
        (π (a ^ j) w)
      rw [e]
      refine e2.symm.trans ?_
      rw [ih, map_smul, hΛ, smul_smul, pow_succ]
  have hkey : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype)
      (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) =
      Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) := by
    intro j
    refine GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo
      (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm)
      (fun z hz => ?_) (fun g hg => ?_)
    · have hz' := (Subgroup.mem_inf.1 (hpowz j z hz)).1
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      have : π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [this, hw _ hz']
    · have hc := hpowc j g (Subgroup.mem_inf.1 hg).2
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
        hw g (Subgroup.mem_inf.1 hg).1]
  refine ⟨w, f ∘ₗ Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ
      (GroundTheory.Automorphic.fixedVectors π
        (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ
      GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo, hw, ?_, ?_⟩
  · intro g hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]
  · intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.JacquetCoeff
