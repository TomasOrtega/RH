import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨⟨Δ, hΔ⟩, -⟩` from `h`. Rewrite using `[← hΔ.deg_eq]`. Conclude with `Nat.mul_pos Δ.len_pos Δ.d_pos`.
-/
theorem IsUnitaryLSeg.deg_pos {x : IrrGL k} (h : IsUnitaryLSeg x) : 0 < x.1 := by
  obtain ⟨⟨Δ, hΔ⟩, -⟩ := h
  rw [← hΔ.deg_eq]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

/- English proof (translation)
Take `⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨φ⟩⟩` from `H`. Establish `hpos : ∀ a, 1 ≤ (x a).1` using `fun a => by`. Take `⟨y, s, hy, -, e⟩` from `exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)`. Rewrite using `[e]`. Conclude with `hy.deg_pos`.

Establish `h1 : h ≤ 1`. Use `Finset.sum_le_sum (s := Finset.univ) fun a _ => hpos a` as an intermediate fact. Simplify `this` using `[hd]`. Establish `h0 : h ≠ 0` using `by rintro rfl; simp at hd`. Take `rfl : h = 1` from `by omega`.

Establish `hl` using `congrArg List.length hx`. Consider the cases of `τ with`. Consider the case `cons p τ => simp [factors] at hl`. Use linear arithmetic over natural numbers and integers. Consider the case `nil`.

Establish `hm : x 0 ∈ δ`. Establish `: List.ofFn x = δ` using `by simpa [factors] using hx`. Rewrite using `[← this]`. Conclude with `List.mem_ofFn.2 ⟨0, rfl⟩`. Take `⟨y, rfl⟩ : ∃ y, x = fun _ => y` from `⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩`.

Take `⟨n, c⟩` from `y`. Take `rfl : n = 1` from `by simpa using hd`. Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_one (⟨1, c⟩ : IrrGL k) hd`. Conclude with `isUnitarisable_of_equiv (ψ.trans φ.symm) (hδ _ hm).2`.
-/
theorem IsComplementaryProduct.isUnitarisable_one {π : Representation ℂ (GL (Fin 1) k) V}
    (H : IsComplementaryProduct π) : IsUnitarisable π := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨φ⟩⟩ := H
  have hpos : ∀ a, 1 ≤ (x a).1 := fun a => by
    obtain ⟨y, s, hy, -, e⟩ := exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)
    rw [e]; exact hy.deg_pos
  have h1 : h ≤ 1 := by
    have := Finset.sum_le_sum (s := Finset.univ) fun a _ => hpos a
    simpa [hd] using this
  have h0 : h ≠ 0 := by rintro rfl; simp at hd
  obtain rfl : h = 1 := by omega
  have hl := congrArg List.length hx
  cases τ with
  | cons p τ => simp [factors] at hl; omega
  | nil =>
    have hm : x 0 ∈ δ := by
      have : List.ofFn x = δ := by simpa [factors] using hx
      rw [← this]; exact List.mem_ofFn.2 ⟨0, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
    obtain ⟨n, c⟩ := y
    obtain rfl : n = 1 := by simpa using hd
    obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨1, c⟩ : IrrGL k) hd
    exact isUnitarisable_of_equiv (ψ.trans φ.symm) (hδ _ hm).2

/- English proof (translation)
Introduce `H` and use `by have hu := (isUnitarisable_ofChar_iff _).1 H.isUnitarisable_one refine hs ((absPow_ofReal_eq_one (k := k)).1 (MonoidHom.ext fun z => Units.ext ?_) : s = 0) have h := hu (Matrix.GeneralLinearGroup.scalar (Fin 1) z) have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGr …`.
-/
theorem not_isComplementaryProduct_absPow {s : ℝ} (hs : s ≠ 0) :
    ¬ IsComplementaryProduct (detRep (Fin 1) (absPow k s)) := fun H => by
  have hu := (isUnitarisable_ofChar_iff _).1 H.isUnitarisable_one
  refine hs ((absPow_ofReal_eq_one (k := k)).1 (MonoidHom.ext fun z => Units.ext ?_) : s = 0)
  have h := hu (Matrix.GeneralLinearGroup.scalar (Fin 1) z)
  have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [detChar_apply, h2, val_absPow_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k z).le _)] at h
  rw [val_absPow_ofReal, h]; simp

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `⟨hs, fun s d e he => absurd ?_ he⟩` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `u hu`. Use `det_eq_one_of_mem_unipRad k hu` as an intermediate fact. Rewrite using `[Subgroup.mem_bot]`.

Use extensionality with `i j`. Establish `h` using `congrArg Units.val this`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify using `using h`.
-/
theorem isCuspidal_of_isSmooth_one {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  rw [eq_bot_iff]
  intro u hu
  have := det_eq_one_of_mem_unipRad k hu
  rw [Subgroup.mem_bot]
  ext i j
  have h := congrArg Units.val this
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsComplementaryProduct.isUnitarisable_one, isComplementaryProduct_of_isCuspidal one_pos hi (isCuspidal_of_isSmooth_one hs)⟩`.
-/
theorem isComplementaryProduct_one_iff {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : IsComplementaryProduct π ↔ IsUnitarisable π :=
  ⟨IsComplementaryProduct.isUnitarisable_one,
    isComplementaryProduct_of_isCuspidal one_pos hi (isCuspidal_of_isSmooth_one hs)⟩

/- English proof (translation)
Set `L` to `(PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm`. Establish `h1 : ∀ g : GL (Fin 0) k, g = 1` using `fun g => Subsingleton.elim _ _`. Set `f : (Representation.trivial ℂ (GL (Fin 0) k) ℂ).IntertwiningMap (prodIrr x hd)` to `{ toFun := fun v => ⟨⟨fun _ => L v, fun p g => by`. Take `rfl : p = 1` from `Subtype.ext (h1 _)`. Use the proof step `simp⟩, mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [h1 g]; simp)⟩`.

Use the proof step `map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))`. Use the proof step `map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun _ => L.map_smul c v))`. Use the proof step `isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun _ => rfl)) }`. Use `⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩⟩⟩` and prove the remaining obligations. Conclude with `L.injective (congrArg (fun φ => φ.1.1 1) h)`.

Rewrite using `[h1 g]`. Conclude with `L.apply_symm_apply _`.
-/
theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((Representation.trivial ℂ (GL (Fin 0) k) ℂ).Equiv (prodIrr x hd)) := by
  let L := (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm
  have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Subsingleton.elim _ _
  let f : (Representation.trivial ℂ (GL (Fin 0) k) ℂ).IntertwiningMap (prodIrr x hd) :=
    { toFun := fun v => ⟨⟨fun _ => L v, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (h1 _)
          simp⟩, mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [h1 g]; simp)⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun _ => L.map_smul c v))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun _ => rfl)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩⟩⟩
  · exact L.injective (congrArg (fun φ => φ.1.1 1) h)
  · rw [h1 g]; exact L.apply_symm_apply _

/- English proof (translation)
Establish `h1 : ∀ g : GL (Fin 0) k, π g = 1` using `fun g => by rw [Subsingleton.elim g 1, map_one]`. Set `e : Subrepresentation π ≃o Submodule ℂ V` to `{ toFun := fun S => S.toSubmodule invFun := fun S => ⟨S, fun g v hv => by rw [h1]; exact hv⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_rel_iff' := Iff.rfl }`. Establish `hsimp : IsSimpleModule ℂ V` using `(isSimpleModule_iff ℂ V).2 (e.isSimpleOrder_iff.1 hi)`. Establish `hr : Module.finrank ℂ V = 1` using `isSimpleModule_iff_finrank_eq_one.1 hsimp`. Establish `: Module.Finite ℂ V` using `Module.finite_of_finrank_eq_succ hr`.

Set `a : V ≃ₗ[ℂ] ℂ` to `LinearEquiv.ofFinrankEq _ _ (by simp [hr])`. Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl`. Conclude with `⟨[], [], by simp, by simp, 0, Fin.elim0, rfl, rfl, ⟨(Representation.Equiv.mk a fun g => by rw [h1]; ext; simp).trans ψ⟩⟩`.
-/
theorem isComplementaryProduct_zero {π : Representation ℂ (GL (Fin 0) k) V} (hi : π.IsIrreducible) :
    IsComplementaryProduct π := by
  have h1 : ∀ g : GL (Fin 0) k, π g = 1 := fun g => by rw [Subsingleton.elim g 1, map_one]
  let e : Subrepresentation π ≃o Submodule ℂ V :=
    { toFun := fun S => S.toSubmodule
      invFun := fun S => ⟨S, fun g v hv => by rw [h1]; exact hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hsimp : IsSimpleModule ℂ V := (isSimpleModule_iff ℂ V).2 (e.isSimpleOrder_iff.1 hi)
  have hr : Module.finrank ℂ V = 1 := isSimpleModule_iff_finrank_eq_one.1 hsimp
  have : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ hr
  let a : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simp [hr])
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  exact ⟨[], [], by simp, by simp, 0, Fin.elim0, rfl, rfl,
    ⟨(Representation.Equiv.mk a fun g => by rw [h1]; ext; simp).trans ψ⟩⟩

end GlobalTheory.GenericUnitary
