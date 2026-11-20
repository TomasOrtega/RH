import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDFrameLattice

open NumberField GlobalTheory.PlaceModel

/- English proof (translation)
Unfold `Formalism.L2.Herm.dualL`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨b, hb⟩` from `RingHom.mem_range.mp (hz x hx)`. Conclude with `⟨b, hb⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add z w _ _ hz hw`. Take `⟨b, hb⟩` from `hz`.

Take `⟨a, ha⟩` from `hw`. Use `⟨b + a, ?_⟩` and prove the remaining obligations. Establish `e1 : ((b + a : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) + a` using `by push_cast; ring`. Rewrite using `[e1, hb, ha, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, mul_add]`. Consider the case `smul a z _ hz`. Take `⟨b, hb⟩` from `hz`.

Use `⟨a * b, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have e1 : ((a * b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a * b := by first | (push_cast; ring) | push_cast | simp`. Rewrite using `[e1, hb, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨b, hb⟩` from `hy x hx`. Conclude with `RingHom.mem_range.mpr ⟨b, hb⟩`.
-/
theorem mem_dualL_iff {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.dualL D.sp.cm V Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  unfold Formalism.L2.Herm.dualL
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb⟩ := RingHom.mem_range.mp (hz x hx)
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨b, hb⟩ := hz
      obtain ⟨a, ha⟩ := hw
      refine ⟨b + a, ?_⟩
      have e1 : ((b + a : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) + a := by push_cast; ring
      rw [e1, hb, ha, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, mul_add]
    | smul a z _ hz =>
      obtain ⟨b, hb⟩ := hz
      refine ⟨a * b, ?_⟩
      have e1 : ((a * b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a * b := by first | (push_cast; ring) | push_cast | simp
      rw [e1, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · intro hy
    apply Submodule.subset_span
    intro x hx
    obtain ⟨b, hb⟩ := hy x hx
    exact RingHom.mem_range.mpr ⟨b, hb⟩

/- English proof (translation)
Introduce `D V β Λ N h`. Take `⟨c, hc⟩` from `h`. Take `⟨-, hdual, hN, hin, hout⟩` from `hc`. Use `set M : ℕ := N ^ c with hM`. Establish `hMpos : 0 < M` using `hN`.

Establish `hME : (M : D.host.E) ≠ 0` using `by exact_mod_cast hMpos.ne'`. Unfold `IsSelfDualC`. Use `⟨?_, fun y => ?_⟩` and prove the remaining obligations. Use `swap`. Establish `e : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ` using `hdual`.

Establish `key` using `mem_dualL_iff V Λ y`. Rewrite `key` using `[e]`. Conclude with `key`. Set `f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V` to `V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)`. Establish `hf : ∀ x, f x = ∑ i, x i • V.frame i` using `fun x => by simp [f]`.

Establish `hfinj : Function.Injective f` using `V.frame.equivFun.symm.injective`. Establish `hL` using `V.standardTuple_isLattice`. Set `s : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)` to `M • LinearMap.id`. Establish `hs : ∀ x, s x = M • x` using `fun x => by simp [s]`. Establish `hsinj : Function.Injective s`.

Introduce `x x' hxx`. Rewrite `hxx` using `[hs, hs]`. Conclude with `nsmul_right_injective hMpos.ne' hxx`. Establish `hout' : ∀ x ∈ Λ, f (M • x) ∈ V.L0`. Introduce `x hx`.

Establish `h1` using `hout x hx`. Rewrite `h1` using `[Nat.cast_smul_eq_nsmul]`. Rewrite using `[hf]`. Conclude with `h1`. Establish `hfg : Λ.FG`.

Use `Submodule.fg_of_fg_map_injective (f ∘ₗ s) (hfinj.comp hsinj) (Submodule.FG.of_le hL.fg ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[LinearMap.comp_apply, hs]`. Conclude with `hout' x hx`. Establish `h1 : ∀ x, f x ∈ V.L0 → x ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))`.

Introduce `x hx`. Establish `hx' : x ∈ Formalism.MainNotions.StandardLattice.L0c D V` using `by show ∑ i, x i • V.frame i ∈ V.L0`. Rewrite using `[← hf]`. Conclude with `hx`. Establish `hxΛ` using `hin x hx'`.

Rewrite `hxΛ` using `[Nat.cast_smul_eq_nsmul]`. Establish `ex : x = (M : D.host.E)⁻¹ • (M • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, inv_mul_cancel₀ hME, one_smul]`. Rewrite using `[ex]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hxΛ)`.

Establish `h2 : Submodule.span D.host.E (V.frame.equivFun '' (V.L0 : Set V.V)) ≤ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Apply `h1` to reduce the goal to its premises. Use `show V.frame.equivFun.symm (V.frame.equivFun w) ∈ V.L0`.

Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `hw`. Establish `h3 : Submodule.span D.host.E (V.frame.equivFun '' (V.L0 : Set V.V)) = ⊤`. Establish `hm` using `Submodule.map_span (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)) (V.L0 : Set V.V)`. Rewrite `hm` using `[hL.span_eq_top, Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe]`.

Conclude with `hm.symm`. Use `⟨hfg, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← h3]`. Conclude with `h2`.
-/
theorem isSelfDualC_of_isSDFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  intro D V β Λ N h
  obtain ⟨c, hc⟩ := h
  obtain ⟨-, hdual, hN, hin, hout⟩ := hc
  set M : ℕ := N ^ c with hM
  have hMpos : 0 < M := hN
  have hME : (M : D.host.E) ≠ 0 := by exact_mod_cast hMpos.ne'
  unfold IsSelfDualC
  refine ⟨?_, fun y => ?_⟩
  swap
  · have e : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ := hdual
    have key := mem_dualL_iff V Λ y
    rw [e] at key
    exact key
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
      V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)
    have hf : ∀ x, f x = ∑ i, x i • V.frame i := fun x => by simp [f]
    have hfinj : Function.Injective f := V.frame.equivFun.symm.injective
    have hL := V.standardTuple_isLattice
    let s : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := M • LinearMap.id
    have hs : ∀ x, s x = M • x := fun x => by simp [s]
    have hsinj : Function.Injective s := by
      intro x x' hxx
      rw [hs, hs] at hxx
      exact nsmul_right_injective hMpos.ne' hxx
    have hout' : ∀ x ∈ Λ, f (M • x) ∈ V.L0 := by
      intro x hx
      have h1 := hout x hx
      rw [Nat.cast_smul_eq_nsmul] at h1
      rw [hf]
      exact h1
    have hfg : Λ.FG := by
      refine Submodule.fg_of_fg_map_injective (f ∘ₗ s) (hfinj.comp hsinj) (Submodule.FG.of_le hL.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.comp_apply, hs]
      exact hout' x hx
    have h1 : ∀ x, f x ∈ V.L0 → x ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
      intro x hx
      have hx' : x ∈ Formalism.MainNotions.StandardLattice.L0c D V := by
        show ∑ i, x i • V.frame i ∈ V.L0
        rw [← hf]
        exact hx
      have hxΛ := hin x hx'
      rw [Nat.cast_smul_eq_nsmul] at hxΛ
      have ex : x = (M : D.host.E)⁻¹ • (M • x) := by
        rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, inv_mul_cancel₀ hME, one_smul]
      rw [ex]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hxΛ)
    have h2 : Submodule.span D.host.E (V.frame.equivFun '' (V.L0 : Set V.V)) ≤
        Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      apply h1
      show V.frame.equivFun.symm (V.frame.equivFun w) ∈ V.L0
      rw [LinearEquiv.symm_apply_apply]
      exact hw
    have h3 : Submodule.span D.host.E (V.frame.equivFun '' (V.L0 : Set V.V)) = ⊤ := by
      have hm := Submodule.map_span (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)) (V.L0 : Set V.V)
      rw [hL.span_eq_top, Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe] at hm
      exact hm.symm
    refine ⟨hfg, ?_⟩
    rw [eq_top_iff, ← h3]
    exact h2

end GlobalTheory.SDFrameLattice
