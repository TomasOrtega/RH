import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

/- English proof (translation)
Introduce `La hL`. Use `set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hL.fg`. Use `⟨s.image f.toAddMonoidHom, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.coe_image, ← AddMonoidHom.map_closure, hs]`. Use `set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS`. Use `set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT`. Establish `key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T`. Introduce `a s hs`.

Take `⟨d, hd, hint⟩` from `exists_integral_multiples ℤ ℚ ({a} : Finset E)`. Establish `hda : IsIntegral ℤ (d • a)` using `hint a (Finset.mem_singleton_self a)`. Take `⟨x, hx, rfl⟩` from `(AddSubgroup.mem_map).mp hs`. Set `b : 𝓞 E` to `⟨d • a, hda⟩`. Establish `hbx : ((b : E) • x) ∈ La` using `hL.smul_mem b x hx`.

Establish `hfb : f ((b : E) • x) ∈ S` using `(AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩`. Establish `hd' : ((d : ℚ)) ≠ 0` using `by exact_mod_cast hd`. Establish `heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x)`. Rewrite using `[map_smul]`. Use `show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)`.

Rewrite using `[zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hd', one_smul]`. Rewrite using `[heq]`. Conclude with `T.smul_mem _ (Submodule.subset_span hfb)`. Establish `stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T`. Introduce `a y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem s hs => exact key a s hs`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `T.add_mem hy hz`.

Consider the case `smul q y _ hy`. Rewrite using `[smul_comm]`. Conclude with `T.smul_mem q hy`. Set `T' : Submodule E (ι → E)` to `{ carrier := T add_mem' := fun hy hz => T.add_mem hy hz zero_mem' := T.zero_mem smul_mem' := fun a y hy => stable a y hy }`. Establish `hspan : Submodule.span E S = ⊤`.

Establish `hSim : S = f '' (La : Set W)`. Rewrite using `[hS, AddSubgroup.coe_map]`. Both sides reduce to the same expression. Rewrite using `[hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `v.equivFun.surjective`.

Establish `hle : Submodule.span E S ≤ T'` using `Submodule.span_le.mpr fun s hs => Submodule.subset_span hs`. Rewrite `hle` using `[hspan]`. Conclude with `eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)`.
-/
theorem CoordLatticeFullRank.proof (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by
  intro La hL
  set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf
  refine ⟨?_, ?_⟩
  · classical
    obtain ⟨s, hs⟩ := hL.fg
    refine ⟨s.image f.toAddMonoidHom, ?_⟩
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hs]
  set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS
  set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT

  have key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T := by
    intro a s hs
    obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({a} : Finset E)
    have hda : IsIntegral ℤ (d • a) := hint a (Finset.mem_singleton_self a)
    obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_map).mp hs
    let b : 𝓞 E := ⟨d • a, hda⟩
    have hbx : ((b : E) • x) ∈ La := hL.smul_mem b x hx
    have hfb : f ((b : E) • x) ∈ S := (AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩
    have hd' : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
    have heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x) := by
      rw [map_smul]
      show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)
      rw [zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [heq]
    exact T.smul_mem _ (Submodule.subset_span hfb)

  have stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key a s hs
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact T.add_mem hy hz
    | smul q y _ hy =>
      rw [smul_comm]
      exact T.smul_mem q hy
  let T' : Submodule E (ι → E) :=
    { carrier := T
      add_mem' := fun hy hz => T.add_mem hy hz
      zero_mem' := T.zero_mem
      smul_mem' := fun a y hy => stable a y hy }
  have hspan : Submodule.span E S = ⊤ := by
    have hSim : S = f '' (La : Set W) := by
      rw [hS, AddSubgroup.coe_map]; rfl
    rw [hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact v.equivFun.surjective
  have hle : Submodule.span E S ≤ T' := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
