import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvectorExistence

noncomputable section

namespace UpperTheory.Gal.LocD

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector φ hc`.
-/
private theorem common_eigenvector {T D : Type} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D]
    (φ : T → Module.End ℂ D) (hc : ∀ s t, Commute (φ s) (φ t)) :
    ∃ (l : D) (a : T → ℂ), l ≠ 0 ∧ ∀ t, φ t l = a t • l :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector φ hc

/- English proof (translation)
Introduce `T J _ _ _ _ _ ρ`. Establish `hcomm : ∀ s t, Commute (ρ s) (ρ t)` using `fun s t => by`. Express the relevant statement in the definitionally equal form `ρ s * ρ t = ρ t * ρ s`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Use `haveI : Nontrivial (Module.Dual ℂ J) := by`.

Take `⟨y, hy⟩` from `exists_ne (0 : J)`. Establish `hex : ∃ g : Module.Dual ℂ J, g y ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)`.

Take `⟨g, hg⟩` from `hex`. Conclude with `⟨g, 0, fun h => hg (by simp [h])⟩`. Take `⟨l, a, hl0, hl⟩` from `common_eigenvector (fun t => (ρ t).dualMap) (fun s t => by`. Express the relevant statement in the definitionally equal form `(ρ s).dualMap * (ρ t).dualMap = (ρ t).dualMap * (ρ s).dualMap`. Use extensionality with `g y`.

Establish `h` using `congrArg (fun F : Module.End ℂ J => F y) (hcomm s t).eq`. Simplify using `only [Module.End.mul_apply] at h`. Simplify using `[Module.End.mul_apply, LinearMap.dualMap_apply, h])`. Establish `hact : ∀ t y, l (ρ t y) = a t * l y` using `fun t y => by`. Use `congrArg (fun g : Module.Dual ℂ J => g y) (hl t)` as an intermediate fact.

Simplify `this` using `[LinearMap.dualMap_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨y₀, hy₀⟩ : ∃ y, l y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hl0 (LinearMap.ext h)`.

Set `am : T →* ℂ` to `{ toFun := a map_one' := by`. Use `hact 1 y₀` as an intermediate fact. Simplify using `only [map_one, Module.End.one_apply] at this`. Conclude with `(mul_right_cancel₀ hy₀ (by rw [one_mul]; exact this)).symm`. Use the proof step `map_mul' := fun s t => by`.

Use `hact (s * t) y₀` as an intermediate fact. Rewrite `this` using `[map_mul, Module.End.mul_apply, hact s, hact t, ← mul_assoc]`. Conclude with `(mul_right_cancel₀ hy₀ this).symm }`. Use `⟨am.toHomUnits, l, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hl0`.

Introduce `t y`. Simplify `hact t y` using `[am]`. Establish `hval : ∀ t, ((am.toHomUnits t : ℂˣ) : ℂ) = a t` using `fun t => by simp [am]`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute (fun t => ρ t) (fun s t _ => hcomm s t) (fun t => Module.End.iSup_maxGenEigenspace_eq_top (ρ t))`. Choose the witnesses or unpack the hypotheses as in `⟨χ, y, hy, hly⟩ : ∃ (χ : T → ℂ) (y : J), y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t) : Submodule ℂ J) ∧ l y ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `: (⊤ : Submodule ℂ J) ≤ LinearMap.ker l`. Rewrite using `[← htop]`. Conclude with `iSup_le fun χ y hy => LinearMap.mem_ker.2 (h χ y hy)`.

Conclude with `hl0 (LinearMap.ker_eq_top.1 (top_le_iff.1 this))`. Establish `hpow : ∀ (t : T) (c : ℂ) (m : ℕ) (z : J), l (((ρ t - c • 1) ^ m) z) = (a t - c) ^ m * l z`. Introduce `t c m`. Proceed by induction on `m with`. Consider the case `zero => intro z`.

Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `z`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Simplify using `[hact, pow_succ, sub_mul, mul_assoc]`.

Establish `hχ : ∀ t, χ t = a t`. Introduce `t`. Take `⟨m, hm⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hy t)`. Establish `h0` using `hpow t (χ t) m y`. Rewrite `h0` using `[hm, map_zero]`.

Establish `: (a t - χ t) ^ m = 0`. Break down `mul_eq_zero.1 h0.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hly`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at this`. Conclude with `(sub_eq_zero.1 ((pow_eq_zero_iff hm0).1 this)).symm`. Introduce `hbot`. Establish `hy' : y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) ((am.toHomUnits t : ℂˣ) : ℂ) : Submodule ℂ J)`.

Simplify using `only [hval, ← hχ]`. Conclude with `hy`. Rewrite `hy'` using `[hbot, Submodule.mem_bot]`. Conclude with `hly (by rw [hy', map_zero])`.
-/
theorem eigZero : EigZero := by
  intro T J _ _ _ _ _ ρ
  have hcomm : ∀ s t, Commute (ρ s) (ρ t) := fun s t => by
    change ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  haveI : Nontrivial (Module.Dual ℂ J) := by
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    have hex : ∃ g : Module.Dual ℂ J, g y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, 0, fun h => hg (by simp [h])⟩
  obtain ⟨l, a, hl0, hl⟩ := common_eigenvector (fun t => (ρ t).dualMap) (fun s t => by
    change (ρ s).dualMap * (ρ t).dualMap = (ρ t).dualMap * (ρ s).dualMap
    ext g y
    have h := congrArg (fun F : Module.End ℂ J => F y) (hcomm s t).eq
    simp only [Module.End.mul_apply] at h
    simp [Module.End.mul_apply, LinearMap.dualMap_apply, h])
  have hact : ∀ t y, l (ρ t y) = a t * l y := fun t y => by
    have := congrArg (fun g : Module.Dual ℂ J => g y) (hl t)
    simpa [LinearMap.dualMap_apply] using this
  obtain ⟨y₀, hy₀⟩ : ∃ y, l y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl0 (LinearMap.ext h)
  let am : T →* ℂ :=
    { toFun := a
      map_one' := by
        have := hact 1 y₀
        simp only [map_one, Module.End.one_apply] at this
        exact (mul_right_cancel₀ hy₀ (by rw [one_mul]; exact this)).symm
      map_mul' := fun s t => by
        have := hact (s * t) y₀
        rw [map_mul, Module.End.mul_apply, hact s, hact t, ← mul_assoc] at this
        exact (mul_right_cancel₀ hy₀ this).symm }
  refine ⟨am.toHomUnits, l, ?_, ?_, ?_⟩
  · exact hl0
  · intro t y
    simpa [am] using hact t y
  · have hval : ∀ t, ((am.toHomUnits t : ℂˣ) : ℂ) = a t := fun t => by simp [am]
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun t => ρ t) (fun s t _ => hcomm s t)
      (fun t => Module.End.iSup_maxGenEigenspace_eq_top (ρ t))
    obtain ⟨χ, y, hy, hly⟩ : ∃ (χ : T → ℂ) (y : J),
        y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t) : Submodule ℂ J) ∧ l y ≠ 0 := by
      by_contra h
      push_neg at h
      have : (⊤ : Submodule ℂ J) ≤ LinearMap.ker l := by
        rw [← htop]
        exact iSup_le fun χ y hy => LinearMap.mem_ker.2 (h χ y hy)
      exact hl0 (LinearMap.ker_eq_top.1 (top_le_iff.1 this))
    have hpow : ∀ (t : T) (c : ℂ) (m : ℕ) (z : J), l (((ρ t - c • 1) ^ m) z) = (a t - c) ^ m * l z := by
      intro t c m
      induction m with
      | zero => intro z; simp
      | succ m ih =>
        intro z
        rw [pow_succ, Module.End.mul_apply, ih]
        simp [hact, pow_succ, sub_mul, mul_assoc]
    have hχ : ∀ t, χ t = a t := by
      intro t
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hy t)
      have h0 := hpow t (χ t) m y
      rw [hm, map_zero] at h0
      have : (a t - χ t) ^ m = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact h
        · exact absurd h hly
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at this
      exact (sub_eq_zero.1 ((pow_eq_zero_iff hm0).1 this)).symm
    intro hbot
    have hy' : y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) ((am.toHomUnits t : ℂˣ) : ℂ) : Submodule ℂ J) := by
      simp only [hval, ← hχ]
      exact hy
    rw [hbot, Submodule.mem_bot] at hy'
    exact hly (by rw [hy', map_zero])

end UpperTheory.Gal.LocD

end
