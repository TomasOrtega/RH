import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDual

/- English proof (translation)
Establish `: (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = L0c D V`. Use extensionality with `v`. Rewrite using `[SetLike.mem_coe, GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem lamHat_eq_hat {D : D7} (V : HSp D) :
    LamHat V = GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  have : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    rw [SetLike.mem_coe, GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]
    rfl
  rw [this]
  rfl

/- English proof (translation)
Unfold `intAE GlobalTheory.AdLat.hat1`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, x, rfl⟩`.

Conclude with `⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩`. Introduce and unpack `⟨a, ha, y, hy, rfl⟩`. Take `⟨x, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hy`. Conclude with `⟨a, ha, x, rfl⟩`.
-/
theorem integralTensorAdeles_eq_adelicCompletion_one (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    exact ⟨a, ha, x, rfl⟩

/- English proof (translation)
Unfold `hR Formalism.UG.hform GlobalTheory.AdLat.hermA`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_comm (sigR _ _ _), ← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem hR_eq_hermA {D : D7} (V : HSp D)
    (z y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y =
      GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y z := by
  unfold hR Formalism.UG.hform GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, mul_comm (sigR _ _ _), ← mul_assoc]
  rfl

/- English proof (translation)
Introduce `a ha y hy`. Rewrite `hy`, the goal using `[lamHat_eq_hat]`. Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem a ha`. Take `⟨s, hs, o, rfl⟩` from `ha`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨t, ht, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x, (GlobalTheory.Member.latC V).smul_mem o hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero`. Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add u w _ _ hu hw`. Simplify using `only [Pi.add_apply, mul_add]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu`. Simplify using `only [Pi.neg_apply, mul_neg]`.

Conclude with `neg_mem hu`. Consider the case `zero`. Simplify using `only [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw`.

Simplify using `only [add_mul]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu`. Simplify using `only [neg_mul]`. Conclude with `neg_mem hu`.
-/
theorem smul_mem_lamHat {D : D7} (V : HSp D) :
    ∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V := by
  intro a ha y hy
  rw [lamHat_eq_hat] at hy ⊢
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        (GlobalTheory.Member.latC V).smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

/- English proof (translation)
Introduce `D V`. Use `⟨fun y => ?_, smul_mem_lamHat V⟩` and prove the remaining obligations. Take `⟨-, -, hfg, hspan, hcc, -, -, hG, hdet, -, hL⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Establish `key` using `GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D) V.gram.transpose 1 hfg hspan hcc hG hdet one_ne_zero hL`. Rewrite `key` using `[← integralTensorAdeles_eq_adelicCompletion_one, ← lamHat_eq_hat]`.

Simplify using `only [hR_eq_hermA]`. Prove the components needed by the constructor for the conclusion. Introduce `hy z hz`. Rewrite `hz` using `[lamHat_eq_hat]`. Proceed by induction on `hz using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨t, ht, x, hx, rfl⟩` from `hz`. Establish `h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D` using `AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩`. Establish `h2` using `(key _).2 (smul_mem_lamHat V _ h1 y hy) x hx`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Unfold `GlobalTheory.AdLat.hermA`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) = (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) * GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.h …`. Simplify using `[GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0` using `by simp [GlobalTheory.AdLat.hermA]`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Consider the case `add u w _ _ hu hw`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) = GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u + GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w`. Simplify using `only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Rewrite using `[this]`. Conclude with `add_mem hu hw`.

Consider the case `neg u _ hu`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) = -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u`. Simplify using `only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]`. Rewrite using `[this]`. Conclude with `neg_mem hu`.

Introduce `h`. Use `(key y).1 fun x hx => h _ ?_` and prove the remaining obligations. Rewrite using `[lamHat_eq_hat]`. Conclude with `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩`.
-/
theorem lamHat_selfDual_and_module : ∀ {D : D7} (V : HSp D), (∀ y, y ∈ LamHat V ↔ ∀ z ∈ LamHat V, hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D) ∧ (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) := by
  intro D V
  refine ⟨fun y => ?_, smul_mem_lamHat V⟩
  obtain ⟨-, -, hfg, hspan, hcc, -, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D)
    V.gram.transpose 1 hfg hspan hcc hG hdet one_ne_zero hL
  rw [← integralTensorAdeles_eq_adelicCompletion_one, ← lamHat_eq_hat] at key
  simp only [hR_eq_hermA]
  constructor
  · intro hy z hz
    rw [lamHat_eq_hat] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_lamHat V _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    rw [lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

end GlobalTheory.LatDual
