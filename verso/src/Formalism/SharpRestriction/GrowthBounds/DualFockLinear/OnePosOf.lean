import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LetterRowOperator

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

/- English proof (translation)
Consider the cases of `vec`. Simplify using `only [Bool.false_eq_true, if_false, letterRowOperator] split_ifs`. Rewrite using `[sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[zero_sub, neg_mul, mul_neg]`.

Normalize the expressions using the abelian group laws. Simplify using `[letterRowOperator]`.
-/
theorem Ed_comm_eq (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) (X : Module.End K (VV K m d)) :
    Ed K (m + 1) d a b * X - X * Ed K (m + 1) d a b =
      if vec = true then letterRowOperator K m vec d a b * X - X * letterRowOperator K m vec d a b
      else -(letterRowOperator K m vec d b a * X - X * letterRowOperator K m vec d b a) := by
  cases vec
  · simp only [Bool.false_eq_true, if_false, letterRowOperator]
    split_ifs
    · rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
      abel
    · rw [zero_sub, neg_mul, mul_neg]
      abel
  · simp [letterRowOperator]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `K _ _ m hm vec d c ν hν hνc β hβ s hs`. Take `⟨A, hA⟩` from `exists_A (K := K) hR hR2 hm vec d`. Establish `huniq : ∀ T T' : Module.End K (VV K m d), (∀ P Q, fockR (thV K m vec d (T P)) (thV K m vec d Q) = fockR (thV K m vec d (T' P)) (thV K m vec d Q)) → T = T'`. Introduce `T T' h`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations.

Establish `h0` using `uniqV hR hm vec d (T P - T' P) (fun Q => by rw [map_sub, fR_sub_left, h P Q, sub_self])`. Conclude with `sub_eq_zero.1 h0`. Establish `hadd1 : ∀ x x' y, A (x + x') y = A x y + A x' y`. Introduce `x x' y`. Apply `huniq` to reduce the goal to its premises.

Introduce `P Q`. Rewrite using `[LinearMap.add_apply, map_add, fR_add_left, hA, hA, hA, mul_add, fR_add_right]`. Establish `hsmul1 : ∀ (t : K) x y, A (t • x) y = t • A x y`. Introduce `t x y`. Apply `huniq` to reduce the goal to its premises.

Introduce `P Q`. Rewrite using `[LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_right]`. Establish `hadd2 : ∀ x y y', A x (y + y') = A x y + A x y'`. Introduce `x y y'`. Apply `huniq` to reduce the goal to its premises.

Introduce `P Q`. Rewrite using `[LinearMap.add_apply, map_add, fR_add_left, hA, hA, hA, mul_add, fR_add_left]`. Establish `hsmul2 : ∀ (t : K) x y, A x (t • y) = t • A x y`. Introduce `t x y`. Apply `huniq` to reduce the goal to its premises.

Introduce `P Q`. Rewrite using `[LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_left]`. Set `Aₗ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] Module.End K (VV K m d)` to `LinearMap.mk₂ K A hadd1 hsmul1 hadd2 hsmul2`. Take `⟨J, bs, μ, hspan, hRE, hμ⟩` from `hW K m ν hν`. Set `WW` to `Submodule.map₂ Aₗ (dualWeyl K (m + 1) (m + 1) ν) (dualWeyl K (m + 1) (m + 1) ν)`.

Set `Sg` to `Set.image2 (fun x y => Aₗ x y) (Set.range bs) (Set.range bs)`. Establish `hWWspan : WW = Submodule.span K Sg` using `by show Submodule.map₂ Aₗ _ _ = _`. Rewrite using `[← hspan, Submodule.map₂_span_span]`. Establish `hbmem : ∀ i, bs i ∈ dualWeyl K (m + 1) (m + 1) ν` using `fun i => by`. Rewrite using `[← hspan]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `hAmem : ∀ x y, x ∈ dualWeyl K (m + 1) (m + 1) ν → y ∈ dualWeyl K (m + 1) (m + 1) ν → A x y ∈ WW` using `fun x y hx hy => Submodule.apply_mem_map₂ Aₗ hx hy`. Establish `hcomm : ∀ x y (a a' : Fin (m + 1)), x ∈ dualWeyl K (m + 1) (m + 1) ν → y ∈ dualWeyl K (m + 1) (m + 1) ν → Ed K (m + 1) d a a' * A x y - A x y * Ed K (m + 1) d a a' ∈ WW`. Introduce `x y a a' hx hy`. Rewrite using `[Ed_comm_eq K m vec d a a' (A x y)]`.

Use `split_ifs`. Rewrite using `[comm_A hAdj hT hR hm vec d A hA a a' x y]`. Conclude with `WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a a' y hy)) (hAmem _ _ (hSt K (m + 1) ν a' a x hx) hy)`. Rewrite using `[comm_A hAdj hT hR hm vec d A hA a' a x y]`. Conclude with `WW.neg_mem (WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a' a y hy)) (hAmem _ _ (hSt K (m + 1) ν a a' x hx) hy))`.

Establish `hstab : ∀ A' ∈ WW, ∀ a a' : Fin (m + 1), Ed K (m + 1) d a a' * A' - A' * Ed K (m + 1) d a a' ∈ WW`. Introduce `A' hA' a a'`. Rewrite `hA'` using `[hWWspan]`. Proceed by induction on `hA' using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩` from `hx`. Conclude with `hcomm _ _ a a' (hbmem i) (hbmem j)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Establish `e : Ed K (m + 1) d a a' * (x + y) - (x + y) * Ed K (m + 1) d a a' = (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') + (Ed K (m + 1) d a a' * y - y * Ed K (m + 1) d a a')`.

Rewrite using `[mul_add, add_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `WW.add_mem hx hy`. Consider the case `smul t x _ hx`.

Establish `e : Ed K (m + 1) d a a' * (t • x) - (t • x) * Ed K (m + 1) d a a' = t • (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a')`. Rewrite using `[mul_smul_comm, smul_mul_assoc, smul_sub]`. Rewrite using `[e]`. Conclude with `WW.smul_mem t hx`. Establish `hwt : ∀ A' ∈ Sg, ∃ ω : Fin (m + 1) → ℤ, (∀ a, Ed K (m + 1) d a a * A' - A' * Ed K (m + 1) d a a = (ω a : K) • A') ∧ ∀ a, ω a ≤ c`.

Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩`. Use `⟨fun a => if vec then (μ j a : ℤ) - μ i a else (μ i a : ℤ) - μ j a, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `show Ed K (m + 1) d a a * A (bs i) (bs j) - A (bs i) (bs j) * Ed K (m + 1) d a a = _`. Rewrite using `[Ed_comm_eq K m vec d a a (A (bs i) (bs j)), comm_A hAdj hT hR hm vec d A hA a a (bs i) (bs j), hRE j a, hRE i a, hsmul1, hsmul2]`. Simplify using `only`.

Rewrite using `[show (Aₗ (bs i)) (bs j) = A (bs i) (bs j) from rfl]`. Apply the tactic sequence `split_ifs <;> push_cast <;> rw [sub_smul] <;> abel`. Simplify using `only`. Establish `h1` using `hμ j a`. Establish `h2` using `hμ i a`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `hmain` using `hOB K (m + 1) d c WW Sg hstab hWWspan hwt (A β s) (hAmem β s hβ hs)`. Establish `hset : {B | ∃ l : List (Fin (m + 1) × Fin (m + 1)), l.length ≤ c ∧ B = EdWord K (m + 1) d l} = EdWord K (m + 1) d '' {l | l.length ≤ c}`. Use extensionality with `B`. Simplify using `[eq_comm]`.

Rewrite `hmain` using `[hset, Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨f, hf, hfA⟩` from `hmain`. Use `⟨f.support, f, fun l hl => (Finsupp.mem_supported K f).1 hf hl, ?_⟩` and prove the remaining obligations. Introduce `P hP Q hQ`. Establish `hP' : P ∈ homogeneousSubmodule (Fin (m + 1)) K d` using `(mem_Hd_iff P).1 hP`.

Establish `hQ' : Q ∈ homogeneousSubmodule (Fin (m + 1)) K d` using `(mem_Hd_iff Q).1 hQ`. Establish `h1` using `hA β s ⟨P, hP'⟩ ⟨Q, hQ'⟩`. Establish `hcoe : ((A β s ⟨P, hP'⟩ : VV K m d) : MvPolynomial (Fin (m + 1)) K) = ∑ l ∈ f.support, f l • word1 l P`. Rewrite using `[← hfA, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul, EdWord_coe]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hcoe]`. Both sides reduce to the same expression.
-/
theorem onePos_of (hOB : OpBound) (hAdj : RestAdj) (hSt : RestStab) (hT : RestTheta) (hW : RestWt) (hR : RestRep)
    (hR2 : RestRep2) : OnePos := by
  intro K _ _ m hm vec d c ν hν hνc β hβ s hs
  obtain ⟨A, hA⟩ := exists_A (K := K) hR hR2 hm vec d
  have huniq : ∀ T T' : Module.End K (VV K m d),
      (∀ P Q, fockR (thV K m vec d (T P)) (thV K m vec d Q) =
        fockR (thV K m vec d (T' P)) (thV K m vec d Q)) → T = T' := by
    intro T T' h
    refine LinearMap.ext fun P => ?_
    have h0 := uniqV hR hm vec d (T P - T' P) (fun Q => by rw [map_sub, fR_sub_left, h P Q, sub_self])
    exact sub_eq_zero.1 h0
  have hadd1 : ∀ x x' y, A (x + x') y = A x y + A x' y := by
    intro x x' y
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add, fR_add_left, hA, hA, hA, mul_add, fR_add_right]
  have hsmul1 : ∀ (t : K) x y, A (t • x) y = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_right]
  have hadd2 : ∀ x y y', A x (y + y') = A x y + A x y' := by
    intro x y y'
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add, fR_add_left, hA, hA, hA, mul_add, fR_add_left]
  have hsmul2 : ∀ (t : K) x y, A x (t • y) = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_left]
  let Aₗ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] Module.End K (VV K m d) :=
    LinearMap.mk₂ K A hadd1 hsmul1 hadd2 hsmul2
  obtain ⟨J, bs, μ, hspan, hRE, hμ⟩ := hW K m ν hν
  let WW := Submodule.map₂ Aₗ (dualWeyl K (m + 1) (m + 1) ν) (dualWeyl K (m + 1) (m + 1) ν)
  let Sg := Set.image2 (fun x y => Aₗ x y) (Set.range bs) (Set.range bs)
  have hWWspan : WW = Submodule.span K Sg := by
    show Submodule.map₂ Aₗ _ _ = _
    rw [← hspan, Submodule.map₂_span_span]
  have hbmem : ∀ i, bs i ∈ dualWeyl K (m + 1) (m + 1) ν := fun i => by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hAmem : ∀ x y, x ∈ dualWeyl K (m + 1) (m + 1) ν → y ∈ dualWeyl K (m + 1) (m + 1) ν →
      A x y ∈ WW := fun x y hx hy => Submodule.apply_mem_map₂ Aₗ hx hy
  have hcomm : ∀ x y (a a' : Fin (m + 1)), x ∈ dualWeyl K (m + 1) (m + 1) ν →
      y ∈ dualWeyl K (m + 1) (m + 1) ν →
      Ed K (m + 1) d a a' * A x y - A x y * Ed K (m + 1) d a a' ∈ WW := by
    intro x y a a' hx hy
    rw [Ed_comm_eq K m vec d a a' (A x y)]
    split_ifs
    · rw [comm_A hAdj hT hR hm vec d A hA a a' x y]
      exact WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a a' y hy)) (hAmem _ _ (hSt K (m + 1) ν a' a x hx) hy)
    · rw [comm_A hAdj hT hR hm vec d A hA a' a x y]
      exact WW.neg_mem (WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a' a y hy))
        (hAmem _ _ (hSt K (m + 1) ν a a' x hx) hy))
  have hstab : ∀ A' ∈ WW, ∀ a a' : Fin (m + 1),
      Ed K (m + 1) d a a' * A' - A' * Ed K (m + 1) d a a' ∈ WW := by
    intro A' hA' a a'
    rw [hWWspan] at hA'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := hx
      exact hcomm _ _ a a' (hbmem i) (hbmem j)
    | zero => simp
    | add x y _ _ hx hy =>
      have e : Ed K (m + 1) d a a' * (x + y) - (x + y) * Ed K (m + 1) d a a' =
          (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') +
            (Ed K (m + 1) d a a' * y - y * Ed K (m + 1) d a a') := by
        rw [mul_add, add_mul]
        abel
      rw [e]
      exact WW.add_mem hx hy
    | smul t x _ hx =>
      have e : Ed K (m + 1) d a a' * (t • x) - (t • x) * Ed K (m + 1) d a a' =
          t • (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]
      exact WW.smul_mem t hx
  have hwt : ∀ A' ∈ Sg, ∃ ω : Fin (m + 1) → ℤ,
      (∀ a, Ed K (m + 1) d a a * A' - A' * Ed K (m + 1) d a a = (ω a : K) • A') ∧ ∀ a, ω a ≤ c := by
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    refine ⟨fun a => if vec then (μ j a : ℤ) - μ i a else (μ i a : ℤ) - μ j a, fun a => ?_, fun a => ?_⟩
    · show Ed K (m + 1) d a a * A (bs i) (bs j) - A (bs i) (bs j) * Ed K (m + 1) d a a = _
      rw [Ed_comm_eq K m vec d a a (A (bs i) (bs j)), comm_A hAdj hT hR hm vec d A hA a a (bs i) (bs j),
        hRE j a, hRE i a, hsmul1, hsmul2]
      dsimp only
      rw [show (Aₗ (bs i)) (bs j) = A (bs i) (bs j) from rfl]
      split_ifs <;> push_cast <;> rw [sub_smul] <;> abel
    · dsimp only
      have h1 := hμ j a
      have h2 := hμ i a
      split_ifs <;> omega
  have hmain := hOB K (m + 1) d c WW Sg hstab hWWspan hwt (A β s) (hAmem β s hβ hs)
  have hset : {B | ∃ l : List (Fin (m + 1) × Fin (m + 1)), l.length ≤ c ∧ B = EdWord K (m + 1) d l} =
      EdWord K (m + 1) d '' {l | l.length ≤ c} := by
    ext B
    simp [eq_comm]
  rw [hset, Finsupp.mem_span_image_iff_linearCombination] at hmain
  obtain ⟨f, hf, hfA⟩ := hmain
  refine ⟨f.support, f, fun l hl => (Finsupp.mem_supported K f).1 hf hl, ?_⟩
  intro P hP Q hQ
  have hP' : P ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff P).1 hP
  have hQ' : Q ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff Q).1 hQ
  have h1 := hA β s ⟨P, hP'⟩ ⟨Q, hQ'⟩
  have hcoe : ((A β s ⟨P, hP'⟩ : VV K m d) : MvPolynomial (Fin (m + 1)) K) =
      ∑ l ∈ f.support, f l • word1 l P := by
    rw [← hfA, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, EdWord_coe]
  calc fockR (theta K m vec P * s) (theta K m vec Q * β)
      = fockR (thV K m vec d ⟨P, hP'⟩ * s) (thV K m vec d ⟨Q, hQ'⟩ * β) := rfl
    _ = fockR (thV K m vec d (A β s ⟨P, hP'⟩)) (thV K m vec d ⟨Q, hQ'⟩) := h1.symm
    _ = fockR (theta K m vec (∑ l ∈ f.support, f l • word1 l P)) (theta K m vec Q) := by
      rw [← hcoe]
      rfl

end Formalism.MainNotions.TestSideCounting
