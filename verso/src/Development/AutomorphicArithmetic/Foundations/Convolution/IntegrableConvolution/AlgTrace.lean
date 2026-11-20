import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatImage
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.UnitsTrace

/- English proof (translation)
Establish `key : ∀ a, g (Function.surjInv hp (p a)) = g a`. Introduce `a`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Apply `h` to reduce the goal to its premises. Rewrite using `[map_sub, Function.surjInv_eq hp, sub_self]`.

Use `⟨{ toFun := fun b => g (Function.surjInv hp b) map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, key⟩` and prove the remaining obligations. Rewrite using `[← map_one p, key, map_one]`. Introduce `x y`. Take `⟨x, rfl⟩` from `hp x`. Take `⟨y, rfl⟩` from `hp y`.

Simplify using `only [← map_mul p, key, map_mul g]`. Rewrite using `[← map_zero p, key, map_zero]`. Introduce `x y`. Take `⟨x, rfl⟩` from `hp x`. Take `⟨y, rfl⟩` from `hp y`.

Simplify using `only [← map_add p, key, map_add g]`. Introduce `c`. Simplify using `only [← p.commutes c, key, g.commutes]`.
-/
private theorem factor_alg {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (p : A →ₐ[ℂ] B) (hp : Function.Surjective p) (g : A →ₐ[ℂ] C) (h : ∀ a, p a = 0 → g a = 0) :
    ∃ r : B →ₐ[ℂ] C, ∀ a, r (p a) = g a := by
  have key : ∀ a, g (Function.surjInv hp (p a)) = g a := by
    intro a
    rw [← sub_eq_zero, ← map_sub]
    apply h
    rw [map_sub, Function.surjInv_eq hp, sub_self]
  refine ⟨{ toFun := fun b => g (Function.surjInv hp b)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, key⟩
  · rw [← map_one p, key, map_one]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_mul p, key, map_mul g]
  · rw [← map_zero p, key, map_zero]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_add p, key, map_add g]
  · intro c
    simp only [← p.commutes c, key, g.commutes]

/- English proof (translation)
Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 r => rw [AlgHom.commutes]`. Conclude with `(Algebra.commutes r S).symm`. Consider the case `grade1 x => rw [FreeAlgebra.lift_ι_apply]`. Conclude with `h x`.

Consider the case `mul a b ha hb => rw [map_mul]`. Conclude with `ha.mul_right hb`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `ha.add_right hb`.
-/
private theorem comm_lift {X E : Type} [Ring E] [Algebra ℂ E] (T : X → E) (S : E) (h : ∀ x, Commute S (T x))
    (a : FreeAlgebra ℂ X) : Commute S (FreeAlgebra.lift ℂ T a) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r S).symm
  | grade1 x => rw [FreeAlgebra.lift_ι_apply]; exact h x
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

/- English proof (translation)
Introduce `W X _ _ _ m T hcomm hirr U hU`. Break down `subsingleton_or_nontrivial W with hW | hW` into its components or cases. Use `⟨1, one_ne_zero, fun i₀ S _ => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Use `congr 1`.

Use extensionality with `w`. Conclude with `Subsingleton.elim _ _`. Set `ρ : Fin (m + 1) → (FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W)` to `fun i => FreeAlgebra.lift ℂ (T i)`. Establish `hρι : ∀ i x, ρ i (FreeAlgebra.ι ℂ x) = T i x` using `fun i x => FreeAlgebra.lift_ι_apply _ _`. Establish `hρT : ∀ i j, i ≠ j → ∀ a y, Commute (ρ i a) (T j y)` using `fun i j hij a y => (comm_lift (T i) (T j y) (fun x => (hcomm i j hij x y).symm) a).symm`.

Establish `hρρ : ∀ i j, i ≠ j → ∀ a b, Commute (ρ i a) (ρ j b)` using `fun i j hij a b => comm_lift (T j) (ρ i a) (hρT i j hij a) b`. Establish `hρU : ∀ i a w, U (ρ (i + 1) a w) = ρ i a (U w)`. Introduce `i a`. Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 r => intro w`.

Simplify using `[Algebra.algebraMap_eq_smul_one]`. Consider the case `grade1 x => intro w`. Rewrite using `[hρι, hρι, hU]`. Consider the case `mul a b ha hb => intro w`. Simplify using `only [map_mul, Module.End.mul_apply, ha, hb]`.

Consider the case `add a b ha hb => intro w`. Simplify using `only [map_add, LinearMap.add_apply, ha, hb]`. Establish `hker : ∀ a, ρ 0 a = 0 → ∀ i, ρ i a = 0`. Introduce `a ha i`. Proceed by induction on `i using Fin.induction with`.

Consider the case `zero => exact ha`. Consider the case `succ i ih`. Rewrite using `[← Fin.coeSucc_eq_succ]`. Use extensionality with `w`. Apply `U.injective` to reduce the goal to its premises.

Rewrite using `[hρU, ih]`. Simplify using the standard rewrite rules. Take `⟨d, -, ⟨e⟩⟩` from `UpperTheory.ConvolutionTheory.L1.matImage (FreeAlgebra ℂ X) W (ρ 0) {b | ∃ j, j ≠ 0 ∧ ∃ x, b = T j x} (by`. Introduce and unpack `a b ⟨j, hj, x, rfl⟩`. Conclude with `hρT 0 j hj.symm a x)`.

Use the proof step `(by`. Introduce `P h1 h2`. Apply `hirr P` to reduce the goal to its premises. Introduce `i x w hw`. Distinguish the cases in `hi : i = 0`.

Substitute `hi` using the available equality. Rewrite using `[← hρι]`. Conclude with `h1 _ w hw`. Conclude with `h2 _ ⟨i, hi, x, rfl⟩ w hw)`. Set `p : FreeAlgebra ℂ X →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ` to `(e : (ρ 0).range →ₐ[ℂ] _).comp (ρ 0).rangeRestrict`.

Establish `hp : Function.Surjective p` using `e.surjective.comp (ρ 0).rangeRestrict_surjective`. Establish `hp0 : ∀ a, p a = 0 → ρ 0 a = 0`. Introduce `a ha`. Establish `h1 : e ((ρ 0).rangeRestrict a) = 0` using `ha`. Establish `h2 : (ρ 0).rangeRestrict a = 0` using `(map_eq_zero_iff e e.injective).1 h1`.

Conclude with `congrArg Subtype.val h2`. Use `choose r hr using fun i => factor_alg p hp (ρ i) (fun a ha => hker a (hp0 a ha) i)`. Take `⟨c, hc, H⟩` from `UpperTheory.ConvolutionTheory.L1.unitsTrace W m d r (by`. Introduce `i j hij a b`. Take `⟨a, rfl⟩` from `hp a`.

Take `⟨b, rfl⟩` from `hp b`. Rewrite using `[hr, hr]`. Conclude with `hρρ i j hij a b)`. Use the proof step `(by`. Introduce `P h`.

Apply `hirr P` to reduce the goal to its premises. Introduce `i x w hw`. Rewrite using `[← hρι, ← hr]`. Conclude with `h _ _ w hw)`. Use `U`.

Use the proof step `(by`. Introduce `i a w`. Take `⟨a, rfl⟩` from `hp a`. Rewrite using `[hr, hr, hρU])`. Use `⟨c, hc, fun i₀ S hS => H i₀ S ?_⟩` and prove the remaining obligations.

Introduce `j hj a`. Take `⟨a, rfl⟩` from `hp a`. Rewrite using `[hr]`. Conclude with `comm_lift (T j) S (hS j hj) a`.
-/
theorem UpperTheory.ConvolutionTheory.L1.algTrace :
    UpperTheory.ConvolutionTheory.L1.AlgTrace := by
  intro W X _ _ _ m T hcomm hirr U hU
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨1, one_ne_zero, fun i₀ S _ => ?_⟩
    rw [one_mul]
    congr 1
    ext w
    exact Subsingleton.elim _ _
  let ρ : Fin (m + 1) → (FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W) := fun i => FreeAlgebra.lift ℂ (T i)
  have hρι : ∀ i x, ρ i (FreeAlgebra.ι ℂ x) = T i x := fun i x => FreeAlgebra.lift_ι_apply _ _
  have hρT : ∀ i j, i ≠ j → ∀ a y, Commute (ρ i a) (T j y) := fun i j hij a y =>
    (comm_lift (T i) (T j y) (fun x => (hcomm i j hij x y).symm) a).symm
  have hρρ : ∀ i j, i ≠ j → ∀ a b, Commute (ρ i a) (ρ j b) := fun i j hij a b =>
    comm_lift (T j) (ρ i a) (hρT i j hij a) b
  have hρU : ∀ i a w, U (ρ (i + 1) a w) = ρ i a (U w) := by
    intro i a
    induction a using FreeAlgebra.induction with
    | grade0 r => intro w; simp [Algebra.algebraMap_eq_smul_one]
    | grade1 x => intro w; rw [hρι, hρι, hU]
    | mul a b ha hb => intro w; simp only [map_mul, Module.End.mul_apply, ha, hb]
    | add a b ha hb => intro w; simp only [map_add, LinearMap.add_apply, ha, hb]
  have hker : ∀ a, ρ 0 a = 0 → ∀ i, ρ i a = 0 := by
    intro a ha i
    induction i using Fin.induction with
    | zero => exact ha
    | succ i ih =>
      rw [← Fin.coeSucc_eq_succ]
      ext w
      apply U.injective
      rw [hρU, ih]
      simp
  obtain ⟨d, -, ⟨e⟩⟩ := UpperTheory.ConvolutionTheory.L1.matImage (FreeAlgebra ℂ X) W (ρ 0) {b | ∃ j, j ≠ 0 ∧ ∃ x, b = T j x}
    (by
      rintro a b ⟨j, hj, x, rfl⟩
      exact hρT 0 j hj.symm a x)
    (by
      intro P h1 h2
      apply hirr P
      intro i x w hw
      by_cases hi : i = 0
      · subst hi
        rw [← hρι]
        exact h1 _ w hw
      · exact h2 _ ⟨i, hi, x, rfl⟩ w hw)
  let p : FreeAlgebra ℂ X →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ := (e : (ρ 0).range →ₐ[ℂ] _).comp (ρ 0).rangeRestrict
  have hp : Function.Surjective p := e.surjective.comp (ρ 0).rangeRestrict_surjective
  have hp0 : ∀ a, p a = 0 → ρ 0 a = 0 := by
    intro a ha
    have h1 : e ((ρ 0).rangeRestrict a) = 0 := ha
    have h2 : (ρ 0).rangeRestrict a = 0 := (map_eq_zero_iff e e.injective).1 h1
    exact congrArg Subtype.val h2
  choose r hr using fun i => factor_alg p hp (ρ i) (fun a ha => hker a (hp0 a ha) i)
  obtain ⟨c, hc, H⟩ := UpperTheory.ConvolutionTheory.L1.unitsTrace W m d r
    (by
      intro i j hij a b
      obtain ⟨a, rfl⟩ := hp a
      obtain ⟨b, rfl⟩ := hp b
      rw [hr, hr]
      exact hρρ i j hij a b)
    (by
      intro P h
      apply hirr P
      intro i x w hw
      rw [← hρι, ← hr]
      exact h _ _ w hw)
    U
    (by
      intro i a w
      obtain ⟨a, rfl⟩ := hp a
      rw [hr, hr, hρU])
  refine ⟨c, hc, fun i₀ S hS => H i₀ S ?_⟩
  intro j hj a
  obtain ⟨a, rfl⟩ := hp a
  rw [hr]
  exact comm_lift (T j) S (hS j hj) a
