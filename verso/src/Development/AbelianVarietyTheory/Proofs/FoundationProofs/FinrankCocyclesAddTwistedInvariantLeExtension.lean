import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

/- English proof (translation)
Set `r : G → G` to `fun x => (Quotient.mk (QuotientGroup.rightRel Γ) x).out`. Establish `hr : ∀ x, x * (r x)⁻¹ ∈ Γ` using `fun x => QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel Γ) x)))`. Establish `hrγ : ∀ (γ : Γ) (x : G), r (γ * x) = r x` using `fun γ x => by`. Establish `: Quotient.mk (QuotientGroup.rightRel Γ) ((γ : G) * x) = Quotient.mk (QuotientGroup.rightRel Γ) x`. Apply `Eq.symm` to reduce the goal to its premises.

Apply `Quotient.sound` to reduce the goal to its premises. Apply `QuotientGroup.rightRel_apply.2` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `only [r, this]`. Use `⟨fun x => ρ (r x) (z ⟨x * (r x)⁻¹, hr x⟩), fun γ x => ?_⟩` and prove the remaining obligations.

Establish `h1 : (⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩ : Γ) = γ * ⟨x * (r x)⁻¹, hr x⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hrγ, mul_assoc]`. Use `show ρ (r (γ * x)) (z ⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩) = _`. Rewrite using `[h1, hz, hrγ, map_add, ← hmul]`.

Simplify using the standard rewrite rules.
-/
theorem exists_extend_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u : G → E, ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := by
  classical
  let r : G → G := fun x => (Quotient.mk (QuotientGroup.rightRel Γ) x).out
  have hr : ∀ x, x * (r x)⁻¹ ∈ Γ := fun x =>
    QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq
      (Quotient.mk (QuotientGroup.rightRel Γ) x)))
  have hrγ : ∀ (γ : Γ) (x : G), r (γ * x) = r x := fun γ x => by
    have : Quotient.mk (QuotientGroup.rightRel Γ) ((γ : G) * x)
        = Quotient.mk (QuotientGroup.rightRel Γ) x := by
      apply Eq.symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.2
      simp
    simp only [r, this]
  refine ⟨fun x => ρ (r x) (z ⟨x * (r x)⁻¹, hr x⟩), fun γ x => ?_⟩
  have h1 : (⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩ : Γ) = γ * ⟨x * (r x)⁻¹, hr x⟩ := by
    apply Subtype.ext
    simp [hrγ, mul_assoc]
  show ρ (r (γ * x)) (z ⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩) = _
  rw [h1, hz, hrγ, map_add, ← hmul]
  simp

/- English proof (translation)
Take `⟨u0, hu0⟩` from `exists_extend_cocyc Γ ρ hmul z hz`. Set `u : G → E` to `fun x => (1 / 4 : ℂ) • (u0 x + ρ (s ^ 3) (u0 (x * s)) + ρ (s ^ 2) (u0 (x * s ^ 2)) + ρ s (u0 (x * s ^ 3)))`. Establish `e1 : s * s ^ 3 = 1` using `by rw [← hs]; group`. Establish `e2 : s ^ 2 * s ^ 2 = 1` using `by rw [← hs]; group`. Establish `e3 : s ^ 3 * s = 1` using `by rw [← hs]; group`.

Establish `key : ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x` using `fun γ x => by`. Simplify using `only [u, mul_assoc, hu0, map_add, ← hmul, e1, e2, e3, mul_one]`. Use `module`. Establish `key1 : ∀ γ : Γ, u γ - u 1 = z γ` using `fun γ => by`. Use `key γ 1` as an intermediate fact.

Rewrite `this` using `[mul_one, hone]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Use `⟨u, ⟨fun γ hγ x => ?_, fun x => ?_⟩, key1⟩` and prove the remaining obligations. Establish `h1` using `key ⟨γ, hγ⟩ x`.

Establish `h2` using `key1 ⟨γ, hγ⟩`. Simplify using `only at h1 h2`. Rewrite using `[h1, h2]`. Normalize the expressions using the abelian group laws. Establish `f1 : s * s = s ^ 2` using `(pow_two s).symm`.

Establish `f2 : s * s ^ 2 = s ^ 3` using `by group`. Establish `f3 : s ^ 2 * s = s ^ 3` using `by group`. Simplify using `only [u, mul_assoc, map_add, map_smul, ← hmul, e1, e3, f1, f2, f3, mul_one, hone]`. Use `module`.
-/
theorem exists_extn_of_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u ∈ extn Γ ρ s, ∀ γ : Γ, u γ - u 1 = z γ := by
  obtain ⟨u0, hu0⟩ := exists_extend_cocyc Γ ρ hmul z hz
  let u : G → E := fun x => (1 / 4 : ℂ) •
    (u0 x + ρ (s ^ 3) (u0 (x * s)) + ρ (s ^ 2) (u0 (x * s ^ 2)) + ρ s (u0 (x * s ^ 3)))
  have e1 : s * s ^ 3 = 1 := by rw [← hs]; group
  have e2 : s ^ 2 * s ^ 2 = 1 := by rw [← hs]; group
  have e3 : s ^ 3 * s = 1 := by rw [← hs]; group
  have key : ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := fun γ x => by
    simp only [u, mul_assoc, hu0, map_add, ← hmul, e1, e2, e3, mul_one]
    module
  have key1 : ∀ γ : Γ, u γ - u 1 = z γ := fun γ => by
    have := key γ 1
    rw [mul_one, hone] at this
    rw [this]; abel
  refine ⟨u, ⟨fun γ hγ x => ?_, fun x => ?_⟩, key1⟩
  · have h1 := key ⟨γ, hγ⟩ x
    have h2 := key1 ⟨γ, hγ⟩
    simp only at h1 h2
    rw [h1, h2]; abel
  · have f1 : s * s = s ^ 2 := (pow_two s).symm
    have f2 : s * s ^ 2 = s ^ 3 := by group
    have f3 : s ^ 2 * s = s ^ 3 := by group
    simp only [u, mul_assoc, map_add, map_smul, ← hmul, e1, e3, f1, f2, f3, mul_one, hone]
    module

def extnToCocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : extn Γ ρ s →ₗ[ℂ] cocyc Γ ρ where
  toFun u := ⟨fun γ => u.1 γ - u.1 1, fun γ δ => by
    have := u.2.1 γ γ.2 δ
    simp only [Subgroup.coe_mul]
    rw [← this]; abel⟩
  map_add' u v := by
    apply Subtype.ext; funext γ
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' c u := by
    apply Subtype.ext; funext γ
    simp [smul_sub]

/- English proof (translation)
Introduce and unpack `f ⟨h1, h2⟩`. Use `⟨fun γ hγ x => ?_, h2⟩` and prove the remaining obligations. Use `h1 γ hγ 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[h1 γ hγ, this]`.

Simplify using the standard rewrite rules.
-/
theorem twInv_le_extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) :
    twInv Γ s (ρ s) ≤ extn Γ ρ s := by
  rintro f ⟨h1, h2⟩
  refine ⟨fun γ hγ x => ?_, h2⟩
  have := h1 γ hγ 1
  rw [mul_one] at this
  rw [h1 γ hγ, this]; simp

/- English proof (translation)
Establish `hsurj : Function.Surjective (extnToCocyc Γ ρ s)`. Introduce and unpack `⟨z, hz⟩`. Take `⟨u, hu, h⟩` from `exists_extn_of_cocyc Γ ρ s hmul hone hs z hz`. Conclude with `⟨⟨u, hu⟩, Subtype.ext (funext h)⟩`. Use `⟨Module.Finite.of_surjective _ hsurj, ?_⟩` and prove the remaining obligations.

Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker (extnToCocyc Γ ρ s)`. Rewrite `hrk` using `[LinearMap.range_eq_top.2 hsurj, finrank_top]`. Set `i : twInv Γ s (ρ s) →ₗ[ℂ] LinearMap.ker (extnToCocyc Γ ρ s)` to `(Submodule.inclusion (twInv_le_extn Γ ρ s)).codRestrict _ (fun f => by`. Rewrite using `[LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `γ`. Use `f.2.1 γ γ.2 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Use `show f.1 γ - f.1 1 = 0`. Rewrite using `[this, sub_self])`.

Establish `hi : Function.Injective i`. Introduce `a b hab`. Conclude with `Submodule.inclusion_injective _ (congrArg Subtype.val hab)`. Use `LinearMap.finrank_le_finrank_of_injective hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_cocyc_add_twInv_le_extn {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (hfd : FiniteDimensional ℂ (extn Γ ρ s)) :
    FiniteDimensional ℂ (cocyc Γ ρ) ∧
      Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s))
        ≤ Module.finrank ℂ (extn Γ ρ s) := by
  have hsurj : Function.Surjective (extnToCocyc Γ ρ s) := by
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, h⟩ := exists_extn_of_cocyc Γ ρ s hmul hone hs z hz
    exact ⟨⟨u, hu⟩, Subtype.ext (funext h)⟩
  refine ⟨Module.Finite.of_surjective _ hsurj, ?_⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (extnToCocyc Γ ρ s)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  let i : twInv Γ s (ρ s) →ₗ[ℂ] LinearMap.ker (extnToCocyc Γ ρ s) :=
    (Submodule.inclusion (twInv_le_extn Γ ρ s)).codRestrict _ (fun f => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext; funext γ
      have := f.2.1 γ γ.2 1
      rw [mul_one] at this
      show f.1 γ - f.1 1 = 0
      rw [this, sub_self])
  have hi : Function.Injective i := by
    intro a b hab
    exact Submodule.inclusion_injective _ (congrArg Subtype.val hab)
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
