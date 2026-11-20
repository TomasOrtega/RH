import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRankStatement

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CentreInherit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

def stab (φ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | finRep E n k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

/- English proof (translation)
Set `S` to `spanK E n ψ`. Set `ev : GA E n → Module.Dual ℂ S` to `fun h => (LinearMap.proj h).comp ((Sm E n).subtype.comp S.subtype)`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Establish `h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Establish `h2 : ∀ h, v.1.1 h = 0` using `fun h => hv _ (Submodule.subset_span ⟨h, rfl⟩)`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext (Subtype.ext (funext h2))`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0, Submodule.dualAnnihilator_bot]`. Establish `hmem : ∀ k, cptRep E n k ψ ∈ S` using `fun k => Submodule.subset_span ⟨k, rfl⟩`. Establish `key : ∀ m ∈ Submodule.span ℂ (Set.range ev), (fun k => m ⟨cptRep E n k ψ, hmem k⟩) ∈ W'`. Introduce `m hm`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx => obtain ⟨h, rfl⟩ := hx`. Conclude with `hW h`. Consider the case `zero => exact W'.zero_mem`. Consider the case `add x y _ _ hx hy => exact W'.add_mem hx hy`. Consider the case `smul c x _ hx => exact W'.smul_mem c hx`.

Set `ℓ : Module.Dual ℂ S` to `(LinearMap.proj g).comp ((Sm E n).subtype.comp (z.comp S.subtype))`. Establish `e : (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) = fun k => ℓ ⟨cptRep E n k ψ, hmem k⟩`. Use function extensionality and compare the values at `k`. Establish `h1` using `LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ`. Simplify using `only [Module.End.mul_apply] at h1`.

Use `show _ = (z (cptRep E n k ψ)).1 g`. Rewrite using `[h1]`. Rewrite using `[e]`. Conclude with `key ℓ (hspan ▸ Submodule.mem_top)`.
-/
theorem ktype_of_central {ψ : Sm E n} (hk : FiniteDimensional ℂ (spanK E n ψ)) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') (g : GA E n) :
    (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  let S := spanK E n ψ
  let ev : GA E n → Module.Dual ℂ S := fun h => (LinearMap.proj h).comp ((Sm E n).subtype.comp S.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ h, v.1.1 h = 0 := fun h => hv _ (Submodule.subset_span ⟨h, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have hmem : ∀ k, cptRep E n k ψ ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ m ∈ Submodule.span ℂ (Set.range ev), (fun k => m ⟨cptRep E n k ψ, hmem k⟩) ∈ W' := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨h, rfl⟩ := hx; exact hW h
    | zero => exact W'.zero_mem
    | add x y _ _ hx hy => exact W'.add_mem hx hy
    | smul c x _ hx => exact W'.smul_mem c hx
  let ℓ : Module.Dual ℂ S := (LinearMap.proj g).comp ((Sm E n).subtype.comp (z.comp S.subtype))
  have e : (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) = fun k => ℓ ⟨cptRep E n k ψ, hmem k⟩ := by
    funext k
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simp only [Module.End.mul_apply] at h1
    show _ = (z (cptRep E n k ψ)).1 g
    rw [h1]
  rw [e]
  exact key ℓ (hspan ▸ Submodule.mem_top)

/- English proof (translation)
Establish `hs : z ψ ∈ fixL E n (stab ψ)` using `Zalg_stable (V := fixL E n (stab ψ)) (fun X _ h => lie_mem_fixL _ X h) hz ψ (fun k hk => hk)`. Use `⟨⟨Zalg_stable (V := leftInv E n) (fun X _ h => lie_mem_leftInv X h) hz ψ hA.left, ?_, ?_, ?_, growth_of_tame (Zalg_stable (V := tame E n) (fun X _ h => lie_mem_tame X h) hz ψ htame)⟩, Zalg_stable (V := fixL E n L') (fun X _ h => lie_mem_fixL L' X h) hz ψ hL, ktype_of_central hA.k …` and prove the remaining obligations. Conclude with `isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hA.level.mem_nhds (by simp)) fun k hk => hs k hk)`. Use `hA.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k ψ)).map z) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ`. Simplify `h1` using `only [Module.End.mul_apply]`. Use `hA.zfin` as an intermediate fact.

Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun y : Module.End ℂ (Sm E n) => y ψ) '' Zalg E n)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z', hz', rfl⟩`. Conclude with `Submodule.subset_span ⟨z' * z, mul_mem hz' hz, rfl⟩`.
-/
theorem central_of_tame {ψ : Sm E n} (hA : IsAutForm ψ) (htame : ψ ∈ tame E n) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hL : ∀ k ∈ L', finRep E n k ψ = ψ) (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') :
    IsAutForm (z ψ) ∧ (∀ k ∈ L', finRep E n k (z ψ) = z ψ) ∧
      ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  have hs : z ψ ∈ fixL E n (stab ψ) :=
    Zalg_stable (V := fixL E n (stab ψ)) (fun X _ h => lie_mem_fixL _ X h) hz ψ (fun k hk => hk)
  refine ⟨⟨Zalg_stable (V := leftInv E n) (fun X _ h => lie_mem_leftInv X h) hz ψ hA.left, ?_, ?_, ?_,
    growth_of_tame (Zalg_stable (V := tame E n) (fun X _ h => lie_mem_tame X h) hz ψ htame)⟩,
    Zalg_stable (V := fixL E n L') (fun X _ h => lie_mem_fixL L' X h) hz ψ hL,
    ktype_of_central hA.kfin hz W' hW⟩
  · exact isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hA.level.mem_nhds (by simp)) fun k hk => hs k hk)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k ψ)).map z)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simpa only [Module.End.mul_apply] using h1
  · have := hA.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun y : Module.End ℂ (Sm E n) => y ψ) '' Zalg E n)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    exact Submodule.subset_span ⟨z' * z, mul_mem hz' hz, rfl⟩

end GlobalTheory.CentreInherit

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CentreInherit

/- English proof (translation)
Introduce `E _ _ _ n hH L' W' ψ hA hL hW ψ' hψ'`. Establish `htame : ψ ∈ tame E n` using `GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank E n hH ψ hA`. Proceed by induction on `hψ' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`.

Conclude with `central_of_tame hA htame hz L' W' hL hW`. Consider the case `zero => exact ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun k _ => map_zero _, fun g => by`. Use `W'.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Use the proof step `simp⟩`.

Consider the case `add x y _ _ hx hy`. Use `⟨GlobalTheory.HCF.FormsSub.isAutForm_add hx.1 hy.1, fun k hk => by rw [map_add, hx.2.1 k hk, hy.2.1 k hk], fun g => ?_⟩` and prove the remaining obligations. Use `W'.add_mem (hx.2.2 g) (hy.2.2 g) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[map_add]`.

Consider the case `smul c x _ hx`. Use `⟨GlobalTheory.HCF.FormsSub.isAutForm_smul c hx.1, fun k hk => by rw [map_smul, hx.2.1 k hk], fun g => ?_⟩` and prove the remaining obligations. Use `W'.smul_mem c (hx.2.2 g) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[map_smul]`.
-/
theorem centre_preserves_forms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  intro E _ _ _ n hH L' W' ψ hA hL hW ψ' hψ'
  have htame : ψ ∈ tame E n := GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank E n hH ψ hA
  induction hψ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact central_of_tame hA htame hz L' W' hL hW
  | zero => exact ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun k _ => map_zero _, fun g => by
      convert W'.zero_mem using 1; funext k; simp⟩
  | add x y _ _ hx hy =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_add hx.1 hy.1, fun k hk => by rw [map_add, hx.2.1 k hk, hy.2.1 k hk],
      fun g => ?_⟩
    convert W'.add_mem (hx.2.2 g) (hy.2.2 g) using 1
    funext k; simp [map_add]
  | smul c x _ hx =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_smul c hx.1, fun k hk => by rw [map_smul, hx.2.1 k hk], fun g => ?_⟩
    convert W'.smul_mem c (hx.2.2 g) using 1
    funext k; simp [map_smul]

end GlobalTheory.CentreInherit
