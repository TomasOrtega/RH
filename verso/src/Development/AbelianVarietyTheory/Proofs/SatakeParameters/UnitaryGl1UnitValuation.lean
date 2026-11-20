import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section
namespace GlobalTheory.Hk3.LatModel
open Classical

section Abstract
variable {W G : Type} [AddCommGroup W] [Group G]

def rho0 (c : W → W → ℂ) (x : W) : Module.End ℂ (W → ℂ) where
  toFun f z := c z x * f (z + x)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' r f := by funext z; simp; ring

def om0 (a : G → W → W) (a1 : ∀ x, a 1 x = x) (am : ∀ g h x, a (g * h) x = a g (a h x)) : G →* Module.End ℂ (W → ℂ) where
  toFun g := { toFun := fun f z => f (a g⁻¹ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext f z; simp [a1]
  map_mul' g h := by ext f z; simp [am]

def s0 (A : AddSubgroup W) : W → ℂ := fun z => if z ∈ A then 1 else 0

/- English proof (translation)
Establish `mul0 : ∀ x y, rho0 c x * rho0 c y = c x y • rho0 c (x + y)`. Introduce `x y`. Use extensionality with `f z`. Simplify using `[rho0, hl, hr, add_assoc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `nrm : ∀ g x, om0 a a1 am g * rho0 c x = rho0 c (a g x) * om0 a a1 am g`. Introduce `g x`. Use extensionality with `f z`. Establish `h1 : c (a g⁻¹ z) x = c z (a g x)`. Rewrite using `[← ha g, ← am]`.

Simplify using `[a1]`. Establish `h2 : a g⁻¹ (a g x) = x` using `by rw [← am]; simp [a1]`. Simplify using `[rho0, om0, h1, aa, h2]`. Establish `oms : ∀ g, om0 a a1 am g (s0 A) = s0 A`. Introduce `g`.

Use function extensionality and compare the values at `z`. Use `show s0 A (a g⁻¹ z) = s0 A z`. Simplify using `only [s0, haA]`. Establish `vac : ∀ u ∈ A, rho0 c u (s0 A) = s0 A`. Introduce `u hu`.

Use function extensionality and compare the values at `z`. Use `show c z u * s0 A (z + u) = s0 A z`. Distinguish the cases in `hz : z ∈ A`. Simplify using `[s0, hz, A.add_mem hz hu, hA z hz u hu]`. Establish `: z + u ∉ A` using `fun h => hz (by simpa using A.sub_mem h hu)`.

Simplify using `[s0, hz, this]`. Set `N : Submodule ℂ (W → ℂ)` to `Submodule.span ℂ (Set.range fun x => rho0 c x (s0 A))`. Establish `hρ : ∀ x, ∀ f ∈ N, rho0 c x f ∈ N`. Introduce `x f hf`. Establish `: N.map (rho0 c x) ≤ N`.

Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `congrArg (fun T => T (s0 A)) (mul0 x y)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite using `[this]`.

Conclude with `N.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)`. Conclude with `this ⟨f, hf, rfl⟩`. Establish `hω : ∀ g, ∀ f ∈ N, om0 a a1 am g f ∈ N`. Introduce `g f hf`. Establish `: N.map (om0 a a1 am g) ≤ N`.

Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `congrArg (fun T => T (s0 A)) (nrm g y)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, oms] at this`. Rewrite using `[this]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Conclude with `this ⟨f, hf, rfl⟩`. Establish `r0 : rho0 c 0 = 1` using `by ext f z; simp [rho0, h0]`. Establish `hs0 : s0 A ∈ N` using `Submodule.subset_span ⟨0, by simp [r0]⟩`. Establish `anti : ∀ x y, c x y * c y x = 1`.

Introduce `x y`. Use `hs (x + y)` as an intermediate fact. Rewrite `this` using `[hl, hr, hr, hs, hs]`. Simplify using `using this`. Establish `eqv : ∀ f ∈ N, ∀ u ∈ A, ∀ z, f (z + u) = c z u * f z`.

Introduce `f hf u hu`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨x, rfl⟩` from `hf`. Introduce `z`.

Use `show c (z + u) x * s0 A (z + u + x) = c z u * (c z x * s0 A (z + x))`. Distinguish the cases in `hz : z + x ∈ A`. Establish `h2 : z + u + x ∈ A` using `by have := A.add_mem hz hu; rwa [add_right_comm] at this`. Establish `h3` using `hA u hu _ hz`. Rewrite `h3` using `[hr]`.

Establish `h4` using `anti z u`. Establish `h5 : c u x = c z u`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[s0, hz, h2, hl, h5]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : z + u + x ∉ A` using `fun h => hz (by have := A.sub_mem h hu; rwa [show z + u + x - u = z + x by abel] at this)`. Simplify using `[s0, hz, h2]`. Consider the case `zero => intro z`. Simplify using the standard rewrite rules. Consider the case `add f g _ _ h1 h2 => intro z`.

Simplify using `[h1 z, h2 z, mul_add]`. Consider the case `smul r f _ h1 => intro z`. Simplify using `[h1 z]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨N, inferInstance, inferInstance, fun x => (rho0 c x).restrict (hρ x), { toFun := fun g => (om0 a a1 am g).restrict (hω g), map_one' := ?_, map_mul' := ?_ }, ⟨s0 A, hs0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `f z`. Simplify using the standard rewrite rules. Introduce `g h`. Use extensionality with `f z`. Simplify using the standard rewrite rules.

Introduce `h`. Use `congrFun (congrArg Subtype.val h) 0` as an intermediate fact. Simplify using `[s0] at this`. Use extensionality with `f z`. Simplify using `[r0]`.

Introduce `x y`. Use `LinearMap.ext fun f => Subtype.ext ?_` and prove the remaining obligations. Conclude with `congrArg (fun T => T f.1) (mul0 x y)`. Introduce `u hu`. Conclude with `Subtype.ext (vac u hu)`.

Apply `Submodule.map_injective_of_injective N.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Both sides reduce to the same expression. Introduce `g x`. Use `LinearMap.ext fun f => Subtype.ext ?_` and prove the remaining obligations.

Conclude with `congrArg (fun T => T f.1) (nrm g x)`. Introduce and unpack `g ⟨t, ht⟩ hv`. Establish `hv' : ∀ u ∈ A, ∀ z, c z u * t (z + u) = t z` using `fun u hu z => congrFun (congrArg Subtype.val (hv u hu)) z`. Establish `ht0 : t = t 0 • s0 A`. Use function extensionality and compare the values at `z`.

Distinguish the cases in `hz : z ∈ A`. Use `eqv t ht z hz 0` as an intermediate fact. Rewrite `this` using `[hA 0 A.zero_mem z hz]`. Simplify `this` using `[s0, hz]`. Take `⟨u, hu, hne⟩` from `hnd z hz`.

Establish `h1` using `hv' u hu z`. Rewrite `h1` using `[eqv t ht u hu, ← mul_assoc]`. Establish `: t z = 0`. Assume the negation of the conclusion as `h`. Conclude with `hne (mul_right_cancel₀ h (by rw [h1, one_mul]))`.

Simplify using `[s0, hz, this]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show om0 a a1 am g t = t`. Rewrite using `[ht0, map_smul, oms]`. Introduce `x hx h`.

Take `⟨r, hr'⟩` from `Submodule.mem_span_singleton.1 h`. Establish `h1` using `congrFun (congrArg Subtype.val hr') (-x)`. Establish `hx' : -x ∉ A` using `fun h => hx (by simpa using A.neg_mem h)`. Establish `h2 : c (-x) x ≠ 0` using `left_ne_zero_of_mul_eq_one (anti _ _)`. Express the relevant statement in the definitionally equal form `r * s0 A (-x) = c (-x) x * s0 A (-x + x) at h1`.

Simplify using `[s0, hx'] at h1`. Conclude with `h2 h1.symm`.
-/
theorem exists_model (A : AddSubgroup W) (c : W → W → ℂ)
    (hl : ∀ x y z, c (x + y) z = c x z * c y z) (hr : ∀ x y z, c x (y + z) = c x y * c x z)
    (hs : ∀ x, c x x = 1) (h0 : ∀ x, c x 0 = 1) (hA : ∀ u ∈ A, ∀ v ∈ A, c u v = 1)
    (hnd : ∀ z, z ∉ A → ∃ u ∈ A, c z u * c z u ≠ 1)
    (a : G → W → W) (a1 : ∀ x, a 1 x = x) (am : ∀ g h x, a (g * h) x = a g (a h x))
    (aa : ∀ g x y, a g (x + y) = a g x + a g y) (ha : ∀ g x y, c (a g x) (a g y) = c x y) (haA : ∀ g x, a g x ∈ A ↔ x ∈ A) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (ρ : W → Module.End ℂ M) (ω : G →* Module.End ℂ M) (s : M),
      s ≠ 0 ∧ ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = c x y • ρ (x + y)) ∧ (∀ u ∈ A, ρ u s = s) ∧
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ ∧ (∀ g x, ω g * ρ x = ρ (a g x) * ω g) ∧
      (∀ g t, (∀ u ∈ A, ρ u t = t) → ω g t = t) ∧ ∀ x, x ∉ A → ρ x s ∉ Submodule.span ℂ {s} := by
  have mul0 : ∀ x y, rho0 c x * rho0 c y = c x y • rho0 c (x + y) := by
    intro x y; ext f z
    simp [rho0, hl, hr, add_assoc]; ring
  have nrm : ∀ g x, om0 a a1 am g * rho0 c x = rho0 c (a g x) * om0 a a1 am g := by
    intro g x; ext f z
    have h1 : c (a g⁻¹ z) x = c z (a g x) := by
      rw [← ha g, ← am]; simp [a1]
    have h2 : a g⁻¹ (a g x) = x := by rw [← am]; simp [a1]
    simp [rho0, om0, h1, aa, h2]
  have oms : ∀ g, om0 a a1 am g (s0 A) = s0 A := by
    intro g; funext z
    show s0 A (a g⁻¹ z) = s0 A z
    simp only [s0, haA]
  have vac : ∀ u ∈ A, rho0 c u (s0 A) = s0 A := by
    intro u hu; funext z
    show c z u * s0 A (z + u) = s0 A z
    by_cases hz : z ∈ A
    · simp [s0, hz, A.add_mem hz hu, hA z hz u hu]
    · have : z + u ∉ A := fun h => hz (by simpa using A.sub_mem h hu)
      simp [s0, hz, this]
  let N : Submodule ℂ (W → ℂ) := Submodule.span ℂ (Set.range fun x => rho0 c x (s0 A))
  have hρ : ∀ x, ∀ f ∈ N, rho0 c x f ∈ N := by
    intro x f hf
    have : N.map (rho0 c x) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun T => T (s0 A)) (mul0 x y)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [this]
      exact N.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    exact this ⟨f, hf, rfl⟩
  have hω : ∀ g, ∀ f ∈ N, om0 a a1 am g f ∈ N := by
    intro g f hf
    have : N.map (om0 a a1 am g) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun T => T (s0 A)) (nrm g y)
      simp only [Module.End.mul_apply, oms] at this
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact this ⟨f, hf, rfl⟩
  have r0 : rho0 c 0 = 1 := by ext f z; simp [rho0, h0]
  have hs0 : s0 A ∈ N := Submodule.subset_span ⟨0, by simp [r0]⟩
  have anti : ∀ x y, c x y * c y x = 1 := by
    intro x y
    have := hs (x + y)
    rw [hl, hr, hr, hs, hs] at this
    simpa using this
  have eqv : ∀ f ∈ N, ∀ u ∈ A, ∀ z, f (z + u) = c z u * f z := by
    intro f hf u hu
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨x, rfl⟩ := hf
      intro z
      show c (z + u) x * s0 A (z + u + x) = c z u * (c z x * s0 A (z + x))
      by_cases hz : z + x ∈ A
      · have h2 : z + u + x ∈ A := by have := A.add_mem hz hu; rwa [add_right_comm] at this
        have h3 := hA u hu _ hz
        rw [hr] at h3
        have h4 := anti z u
        have h5 : c u x = c z u := by
          calc c u x = (c z u * c u z) * c u x := by rw [h4, one_mul]
            _ = c z u := by rw [mul_assoc, h3, mul_one]
        simp [s0, hz, h2, hl, h5]; ring
      · have h2 : z + u + x ∉ A := fun h => hz (by have := A.sub_mem h hu; rwa [show z + u + x - u = z + x by abel] at this)
        simp [s0, hz, h2]
    | zero => intro z; simp
    | add f g _ _ h1 h2 => intro z; simp [h1 z, h2 z, mul_add]
    | smul r f _ h1 => intro z; simp [h1 z]; ring
  refine ⟨N, inferInstance, inferInstance, fun x => (rho0 c x).restrict (hρ x),
    { toFun := fun g => (om0 a a1 am g).restrict (hω g), map_one' := ?_, map_mul' := ?_ }, ⟨s0 A, hs0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext f z; simp
  · intro g h; ext f z; simp
  · intro h
    have := congrFun (congrArg Subtype.val h) 0
    simp [s0] at this
  · ext f z; simp [r0]
  · intro x y; refine LinearMap.ext fun f => Subtype.ext ?_
    exact congrArg (fun T => T f.1) (mul0 x y)
  · intro u hu; exact Subtype.ext (vac u hu)
  · apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl
  · intro g x; refine LinearMap.ext fun f => Subtype.ext ?_
    exact congrArg (fun T => T f.1) (nrm g x)
  · rintro g ⟨t, ht⟩ hv
    have hv' : ∀ u ∈ A, ∀ z, c z u * t (z + u) = t z := fun u hu z => congrFun (congrArg Subtype.val (hv u hu)) z
    have ht0 : t = t 0 • s0 A := by
      funext z
      by_cases hz : z ∈ A
      · have := eqv t ht z hz 0
        rw [hA 0 A.zero_mem z hz] at this
        simpa [s0, hz] using this
      · obtain ⟨u, hu, hne⟩ := hnd z hz
        have h1 := hv' u hu z
        rw [eqv t ht u hu, ← mul_assoc] at h1
        have : t z = 0 := by
          by_contra h
          exact hne (mul_right_cancel₀ h (by rw [h1, one_mul]))
        simp [s0, hz, this]
    apply Subtype.ext
    show om0 a a1 am g t = t
    rw [ht0, map_smul, oms]
  · intro x hx h
    obtain ⟨r, hr'⟩ := Submodule.mem_span_singleton.1 h
    have h1 := congrFun (congrArg Subtype.val hr') (-x)
    have hx' : -x ∉ A := fun h => hx (by simpa using A.neg_mem h)
    have h2 : c (-x) x ≠ 0 := left_ne_zero_of_mul_eq_one (anti _ _)
    change r * s0 A (-x) = c (-x) x * s0 A (-x + x) at h1
    simp [s0, hx'] at h1
    exact h2 h1.symm
end Abstract

section Concrete
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ratCirc : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by simp⟩)

/- English proof (translation)
Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H r`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `h' : ((r : ℝ) : AddCircle (1 : ℝ)) = 0` using `h`.

Take `⟨k, hk⟩` from `(QuotientAddGroup.eq_zero_iff _).1 h'`. Use `(QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩` and prove the remaining obligations. Establish `: ((k : ℚ) : ℝ) = r` using `by simpa using hk`. Simplify using `using (by exact_mod_cast this : (k : ℚ) = r)`.
-/
theorem ratCirc_ne (x : AddCircle (1 : ℚ)) (hx : x ≠ 0) : ratCirc x ≠ 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H r =>
    intro h
    apply hx
    have h' : ((r : ℝ) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h'
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩
    have : ((k : ℚ) : ℝ) = r := by simpa using hk
    simpa using (by exact_mod_cast this : (k : ℚ) = r)

/- English proof (translation)
Set `O : AddSubgroup L` to `(Formalism.UG.intL L).toAddSubgroup`. Establish `hne : (QuotientAddGroup.mk ϖ⁻¹ : L ⧸ O) ≠ 0`. Rewrite using `[Ne, QuotientAddGroup.eq_zero_iff]`. Conclude with `hϖ`. Take `⟨χ, hχ⟩` from `CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne`.

Set `φ : L →+ AddCircle (1 : ℝ)` to `ratCirc.comp ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)).comp (QuotientAddGroup.mk' O))`. Use `⟨{ toFun := fun a => (AddCircle.toCircle (φ a) : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := by intro a b; simp [AddCircle.toCircle_add] }, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `h1 : (QuotientAddGroup.mk' O) a = 0` using `(QuotientAddGroup.eq_zero_iff _).2 ha`. Establish `: φ a = 0` using `by show ratCirc ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)) ((QuotientAddGroup.mk' O) a)) = 0`.

Rewrite using `[h1, map_zero, map_zero]`. Use `show (AddCircle.toCircle (φ a) : ℂ) = 1`. Simplify using `[this]`. Introduce `h`. Establish `h1 : AddCircle.toCircle (φ ϖ⁻¹) = AddCircle.toCircle (0 : AddCircle (1 : ℝ))`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddCircle.toCircle_zero]`. Conclude with `h`. Conclude with `ratCirc_ne _ hχ (AddCircle.injective_toCircle one_ne_zero h1)`.
-/
theorem exists_psi (ϖ : L) (hϖ : ϖ⁻¹ ∉ Formalism.UG.intL L) :
    ∃ ψ : AddChar L ℂ, (∀ a ∈ Formalism.UG.intL L, ψ a = 1) ∧ ψ ϖ⁻¹ ≠ 1 := by
  let O : AddSubgroup L := (Formalism.UG.intL L).toAddSubgroup
  have hne : (QuotientAddGroup.mk ϖ⁻¹ : L ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hϖ
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let φ : L →+ AddCircle (1 : ℝ) := ratCirc.comp ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)).comp (QuotientAddGroup.mk' O))
  refine ⟨{ toFun := fun a => (AddCircle.toCircle (φ a) : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := by intro a b; simp [AddCircle.toCircle_add] }, ?_, ?_⟩
  · intro a ha
    have h1 : (QuotientAddGroup.mk' O) a = 0 := (QuotientAddGroup.eq_zero_iff _).2 ha
    have : φ a = 0 := by
      show ratCirc ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)) ((QuotientAddGroup.mk' O) a)) = 0
      rw [h1, map_zero, map_zero]
    show (AddCircle.toCircle (φ a) : ℂ) = 1
    simp [this]
  · intro h
    have h1 : AddCircle.toCircle (φ ϖ⁻¹) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Subtype.ext; rw [AddCircle.toCircle_zero]; exact h
    exact ratCirc_ne _ hχ (AddCircle.injective_toCircle one_ne_zero h1)

/- English proof (translation)
Take `⟨-, -, -, -, -, h2, hc⟩` from `h`. Assume the negation of the conclusion as `hne`. Establish `hle : Valued.v (2 : L) ≤ 1`. Use `(Valued.v (R := L)).integer.add_mem (one_mem _) (one_mem _)` as an intermediate fact. Rewrite `this` using `[one_add_one_eq_two]`.

Conclude with `this`. Establish `hlt` using `lt_of_le_of_ne hle hne`. Use `set R := (Valued.v (R := L)).valuationSubring`. Express the relevant statement in the definitionally equal form `Nat.card (R ⧸ IsLocalRing.maximalIdeal R) = q ^ 2 at hc`. Establish `hm : (2 : R) ∈ IsLocalRing.maximalIdeal R`.

Rewrite using `[Valuation.mem_maximalIdeal_iff]`. Conclude with `hlt`. Establish `h20 : (2 : R ⧸ IsLocalRing.maximalIdeal R) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hm` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `hodd : Odd (Nat.card (R ⧸ IsLocalRing.maximalIdeal R))` using `by rw [hc]; exact hq.pow`. Take `⟨k, hk⟩` from `hodd`. Establish `h3 : ((Nat.card (R ⧸ IsLocalRing.maximalIdeal R) : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0`. Rewrite using `[← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`.

Rewrite `h3` using `[hk]`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[h20]`. Simplify using `at h3`.
-/
theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  by_contra hne
  have hle : Valued.v (2 : L) ≤ 1 := by
    have := (Valued.v (R := L)).integer.add_mem (one_mem _) (one_mem _)
    rw [one_add_one_eq_two] at this; exact this
  have hlt := lt_of_le_of_ne hle hne
  set R := (Valued.v (R := L)).valuationSubring
  change Nat.card (R ⧸ IsLocalRing.maximalIdeal R) = q ^ 2 at hc
  have hm : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h20 : (2 : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rwa [map_ofNat] at this
  have hodd : Odd (Nat.card (R ⧸ IsLocalRing.maximalIdeal R)) := by rw [hc]; exact hq.pow
  obtain ⟨k, hk⟩ := hodd
  have h3 : ((Nat.card (R ⧸ IsLocalRing.maximalIdeal R) : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    rw [← nsmul_one]; exact card_nsmul_eq_zero'
  rw [hk] at h3
  push_cast at h3
  rw [h20] at h3
  simp at h3

/- English proof (translation)
Establish `h : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * _ * _ = _` using `g.2`. Establish `h1` using `congrFun (congrFun h 0) 0`. Simplify using `[Matrix.mul_apply, Formalism.UG.cT] at h1`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Valued.v h1`.

Rewrite `h2` using `[map_mul, hv, map_one, ← sq]`. Break down `lt_trichotomy (Valued.v ((g : GL (Fin 1) L) 0 0)) 1 with h | h | h` into its components or cases. Conclude with `absurd h2 (pow_lt_one₀ zero_le h two_ne_zero).ne`. Conclude with `h`. Conclude with `absurd h2 (one_lt_pow₀ h two_ne_zero).ne'`.
-/
theorem unitary_gl1_unit_valuation {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (g : Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)) :
    σ ((g : GL (Fin 1) L) 0 0) * (g : GL (Fin 1) L) 0 0 = 1 ∧ Valued.v ((g : GL (Fin 1) L) 0 0) = 1 := by
  have h : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * _ * _ = _ := g.2
  have h1 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT] at h1
  refine ⟨h1, ?_⟩
  have h2 := congrArg Valued.v h1
  rw [map_mul, hv, map_one, ← sq] at h2
  rcases lt_trichotomy (Valued.v ((g : GL (Fin 1) L) 0 0)) 1 with h | h | h
  · exact absurd h2 (pow_lt_one₀ zero_le h two_ne_zero).ne
  · exact h
  · exact absurd h2 (one_lt_pow₀ h two_ne_zero).ne'

/- English proof (translation)
Simplify using `[locH, Matrix.trace, Matrix.mul_apply]`.
-/
theorem local_hermitian_form_gl1 (σ : L →+* L) (δ : L) (x y : Matrix (Fin 1) (Fin 1) L) :
    locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y = δ * (σ (y 0 0) * x 0 0) := by
  simp [locH, Matrix.trace, Matrix.mul_apply]

/- English proof (translation)
Establish `h2` using `v_two h hq`. Take `⟨hσ, hv, hϖσ, hϖ, ⟨x0, -, hx0⟩, -, -⟩` from `id h`. Establish `hmem : ∀ a : L, a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1` using `fun a => Iff.rfl`. Establish `hϖi : Valued.v ϖ⁻¹ = WithZero.exp 1`. Rewrite using `[map_inv₀, hϖ]`.

Both sides reduce to the same expression. Establish `hϖn : ϖ⁻¹ ∉ Formalism.UG.intL L`. Rewrite using `[hmem, hϖi, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Take `⟨ψ, hψ1, hψ2⟩` from `exists_psi ϖ hϖn`.

Use `set δ := σ x0 - x0 with hδ`. Establish `hσδ : σ δ = -δ` using `by rw [hδ, map_sub, hσ]; ring`. Establish `hδ0 : δ ≠ 0` using `by intro h0; rw [h0] at hx0; simp at hx0`. Set `A : AddSubgroup (Matrix (Fin 1) (Fin 1) L)` to `(Formalism.UG.intL L).toAddSubgroup.comap (Matrix.entryAddMonoidHom L 0 0)`. Establish `hAm : ∀ u, u ∈ A ↔ Valued.v (u 0 0) ≤ 1` using `fun u => Iff.rfl`.

Establish `hAm' : ∀ u : Matrix (Fin 1) (Fin 1) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ↔ u ∈ A` using `fun u => ⟨fun hu => hu 0 0, fun hu i j => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact hu⟩`. Set `c : Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L → ℂ` to `fun x y => ψ ((locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y + σ (locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y)) / 2)`. Establish `hc : ∀ x y, c x y = ψ (δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) / 2)`. Introduce `x y`. Simplify using `only [c, local_hermitian_form_gl1, map_mul, hσ, hσδ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Set `U` to `Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)`. Set `a : U × U → Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L` to `fun p x => ((p.2 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * x * (((p.1 : GL (Fin 1) L)⁻¹ : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)`. Establish `ha0 : ∀ p (_ : Matrix (Fin 1) (Fin 1) L), ∃ t : L, σ t * t = 1 ∧ Valued.v t = 1 ∧ ∀ x, a p x 0 0 = t * x 0 0`.

Introduce `p`. Take `⟨e1, e2⟩` from `unitary_gl1_unit_valuation hv p.2`. Take `⟨f1, f2⟩` from `unitary_gl1_unit_valuation hv p.1⁻¹`. Use `fun _ => ⟨(p.2 : GL (Fin 1) L) 0 0 * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0, ?_, by rw [map_mul, e2, f2, one_mul], fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Take the linear combination `e1 * (σ (((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) + f1`. Simplify using `only [a, Matrix.mul_apply, Fin.sum_univ_one, Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton, Subgroup.coe_inv]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨M, i1, i2, ρ, ω, s, s0', r0, rm, rv, rs, rn, rf, rx⟩` from `exists_model (G := U × U) A c (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring) (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring) (by intro x; rw [hc]; …`. Introduce `u hu w hw`.

Rewrite using `[hc]`. Apply `hψ1` to reduce the goal to its premises. Rewrite using `[hmem, map_div₀, h2, div_one, map_mul, hx0, one_mul]`. Rewrite `hu`, `hw` using `[hAm]`. Use `(Valuation.map_sub_le _ ?_ ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, hv]`. Conclude with `mul_le_one' hw hu`. Rewrite using `[map_mul, hv]`. Conclude with `mul_le_one' hw hu)`. Use the proof step `(by`.

Introduce `z hz`. Rewrite `hz` using `[hAm, not_le]`. Establish `hz0 : z 0 0 ≠ 0` using `by intro h0; rw [h0] at hz; simp at hz`. Establish `hϖ0 : ϖ ≠ 0` using `by intro h0; rw [h0] at hϖ; simp at hϖ`. Use `⟨Matrix.of fun _ _ => σ (ϖ⁻¹ / (2 * δ * z 0 0)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hAm, Matrix.of_apply, hv, map_div₀, hϖi, map_mul, map_mul, h2, hx0, one_mul, one_mul]`. Establish `hne : Valued.v (z 0 0) ≠ 0` using `(zero_lt_one.trans hz).ne'`. Rewrite using `[div_le_one₀ (zero_lt_one.trans hz)]`. Rewrite `hz`, the goal using `[← WithZero.exp_log hne]`. Rewrite `hz` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hc, ← AddChar.map_add_eq_mul]`. Establish `hσz : σ (z 0 0) ≠ 0` using `(map_ne_zero σ).2 hz0`. Use `hψ2 using 2` and compare the differences between its conclusion and the goal.

Establish `e : σ (ϖ⁻¹ / (2 * δ * z 0 0)) = ϖ⁻¹ / (2 * -δ * σ (z 0 0))`. Rewrite using `[map_div₀, map_inv₀, hϖσ, map_mul, map_mul, hσδ, map_ofNat]`. Rewrite using `[Matrix.of_apply, hσ, e]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Use `a (by intro x; simp [a]) (by`. Introduce `g k x`. Take `⟨t1, -, -, h1⟩` from `ha0 g x`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`.

Simplify using `only [a, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc])`. Use the proof step `(by intro g x y; simp only [a, Matrix.mul_add, Matrix.add_mul])`. Use the proof step `(by`. Introduce `g x y`. Take `⟨t, t1, -, h1⟩` from `ha0 g x`.

Rewrite using `[hc, hc, h1, h1]`. Use `congr 2`. Simplify using `only [map_mul]`. Take the linear combination `δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) * t1)`. Use the proof step `(by`.

Introduce `g x`. Take `⟨t, -, t2, h1⟩` from `ha0 g x`. Rewrite using `[hAm, hAm, h1, map_mul, t2, one_mul])`. Establish `hs : LocVac ρ s` using `fun u hu => rv u ((hAm' u).1 hu)`. Use `⟨δ, ψ, M, i1, i2, ρ, ω, s, ⟨h, hq, one_mem _, one_mem _, ?_, ?_, ⟨hx0, hσδ⟩, fun a ha _ => hψ1 a ha, ⟨1, one_mem _, map_one σ, by simpa using hψ2⟩, r0, rm, ?_, fun g k x => rn (g, k) x, ?_⟩, s0', hs, rs, ⟨fun _ _ => ϖ⁻¹, rx _ hϖn⟩⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify using the standard rewrite rules. Introduce `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`.

Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff, ← rs]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨x, s, hs, rfl⟩`.

Introduce `g k _ _ t ht`. Conclude with `rf (g, k) t fun u hu => ht u ((hAm' u).2 hu)`.
-/
theorem exists_locPair [CharZero L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    ∃ (δ : L) (ψ : AddChar L ℂ) (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M)
      (ρ : Matrix (Fin 1) (Fin 1) L → Module.End ℂ M)
      (ω : Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) × Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) →* Module.End ℂ M) (s : M),
      LocPair ϖ σ q δ 1 1 ψ ρ ω ∧ s ≠ 0 ∧ LocVac ρ s ∧ Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ ∧
        ∃ x, ρ x s ∉ Submodule.span ℂ {s} := by
  have h2 := v_two h hq
  obtain ⟨hσ, hv, hϖσ, hϖ, ⟨x0, -, hx0⟩, -, -⟩ := id h
  have hmem : ∀ a : L, a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := fun a => Iff.rfl
  have hϖi : Valued.v ϖ⁻¹ = WithZero.exp 1 := by
    rw [map_inv₀, hϖ]; rfl
  have hϖn : ϖ⁻¹ ∉ Formalism.UG.intL L := by
    rw [hmem, hϖi, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_psi ϖ hϖn
  set δ := σ x0 - x0 with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := by intro h0; rw [h0] at hx0; simp at hx0
  let A : AddSubgroup (Matrix (Fin 1) (Fin 1) L) := (Formalism.UG.intL L).toAddSubgroup.comap (Matrix.entryAddMonoidHom L 0 0)
  have hAm : ∀ u, u ∈ A ↔ Valued.v (u 0 0) ≤ 1 := fun u => Iff.rfl
  have hAm' : ∀ u : Matrix (Fin 1) (Fin 1) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ↔ u ∈ A := fun u =>
    ⟨fun hu => hu 0 0, fun hu i j => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact hu⟩
  let c : Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L → ℂ := fun x y =>
    ψ ((locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y + σ (locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y)) / 2)
  have hc : ∀ x y, c x y = ψ (δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) / 2) := by
    intro x y
    simp only [c, local_hermitian_form_gl1, map_mul, hσ, hσδ]
    congr 1; ring
  let U := Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)
  let a : U × U → Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L := fun p x =>
    ((p.2 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * x * (((p.1 : GL (Fin 1) L)⁻¹ : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)
  have ha0 : ∀ p (_ : Matrix (Fin 1) (Fin 1) L), ∃ t : L, σ t * t = 1 ∧ Valued.v t = 1 ∧ ∀ x, a p x 0 0 = t * x 0 0 := by
    intro p
    obtain ⟨e1, e2⟩ := unitary_gl1_unit_valuation hv p.2
    obtain ⟨f1, f2⟩ := unitary_gl1_unit_valuation hv p.1⁻¹
    refine fun _ => ⟨(p.2 : GL (Fin 1) L) 0 0 * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0, ?_, by rw [map_mul, e2, f2, one_mul], fun x => ?_⟩
    · rw [map_mul]; linear_combination e1 * (σ (((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) + f1
    · simp only [a, Matrix.mul_apply, Fin.sum_univ_one, Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton, Subgroup.coe_inv]; ring
  obtain ⟨M, i1, i2, ρ, ω, s, s0', r0, rm, rv, rs, rn, rf, rx⟩ := exists_model (G := U × U) A c
    (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring)
    (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring)
    (by intro x; rw [hc]; simp [mul_comm])
    (by intro x; rw [hc]; simp)
    (by
      intro u hu w hw
      rw [hc]; apply hψ1
      rw [hmem, map_div₀, h2, div_one, map_mul, hx0, one_mul]
      rw [hAm] at hu hw
      refine (Valuation.map_sub_le _ ?_ ?_)
      · rw [map_mul, hv]; exact mul_le_one' hw hu
      · rw [map_mul, hv]; exact mul_le_one' hw hu)
    (by
      intro z hz
      rw [hAm, not_le] at hz
      have hz0 : z 0 0 ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
      have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0] at hϖ; simp at hϖ
      refine ⟨Matrix.of fun _ _ => σ (ϖ⁻¹ / (2 * δ * z 0 0)), ?_, ?_⟩
      · rw [hAm, Matrix.of_apply, hv, map_div₀, hϖi, map_mul, map_mul, h2, hx0, one_mul, one_mul]
        have hne : Valued.v (z 0 0) ≠ 0 := (zero_lt_one.trans hz).ne'
        rw [div_le_one₀ (zero_lt_one.trans hz)]
        rw [← WithZero.exp_log hne] at hz ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
        rw [WithZero.exp_le_exp]; omega
      · rw [hc, ← AddChar.map_add_eq_mul]
        have hσz : σ (z 0 0) ≠ 0 := (map_ne_zero σ).2 hz0
        convert hψ2 using 2
        have e : σ (ϖ⁻¹ / (2 * δ * z 0 0)) = ϖ⁻¹ / (2 * -δ * σ (z 0 0)) := by
          rw [map_div₀, map_inv₀, hϖσ, map_mul, map_mul, hσδ, map_ofNat]
        rw [Matrix.of_apply, hσ, e]
        field_simp
        ring)
    a (by intro x; simp [a]) (by
      intro g k x
      obtain ⟨t1, -, -, h1⟩ := ha0 g x
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp only [a, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc])
    (by intro g x y; simp only [a, Matrix.mul_add, Matrix.add_mul])
    (by
      intro g x y
      obtain ⟨t, t1, -, h1⟩ := ha0 g x
      rw [hc, hc, h1, h1]; congr 2
      simp only [map_mul]
      linear_combination δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) * t1)
    (by
      intro g x
      obtain ⟨t, -, t2, h1⟩ := ha0 g x
      rw [hAm, hAm, h1, map_mul, t2, one_mul])
  have hs : LocVac ρ s := fun u hu => rv u ((hAm' u).1 hu)
  refine ⟨δ, ψ, M, i1, i2, ρ, ω, s, ⟨h, hq, one_mem _, one_mem _, ?_, ?_, ⟨hx0, hσδ⟩, fun a ha _ => hψ1 a ha,
    ⟨1, one_mem _, map_one σ, by simpa using hψ2⟩, r0, rm, ?_, fun g k x => rn (g, k) x, ?_⟩, s0', hs, rs, ⟨fun _ _ => ϖ⁻¹, rx _ hϖn⟩⟩
  · intro i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp
  · intro i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp
  · rw [eq_top_iff, ← rs]
    apply Submodule.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, s, hs, rfl⟩
  · intro g k _ _ t ht
    exact rf (g, k) t fun u hu => ht u ((hAm' u).2 hu)

end Concrete

end GlobalTheory.Hk3.LatModel
end
