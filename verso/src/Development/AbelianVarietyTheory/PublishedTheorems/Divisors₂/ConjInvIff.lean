import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory.Published.SiegelModel

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

omit [NumberField K] in

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem conjInv_iff (h : HermFam K (Fin m → K)) : ConjInv h ↔ h.IsConjInv := Iff.rfl

/- English proof (translation)
Introduce `σ x y`. Simplify using `[stdHerm]`.
-/
theorem conjInv_std : ConjInv (stdHerm K m) := by
  intro σ x y
  simp [stdHerm]

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin m)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span (Submodule.subset_span ⟨i, (Pi.basisFun_apply K (Fin m) i).symm⟩)`.
-/
theorem full_std : Full (stdLat K m) := by
  classical
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun K (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span (Submodule.subset_span ⟨i, (Pi.basisFun_apply K (Fin m) i).symm⟩)

omit [NumberField K] in
/- English proof (translation)
Simplify using `[latBC]`.
-/
theorem latBC_self (L : Submodule (𝓞 K) (Fin m → K)) : latBC K L = L := by
  simp [latBC]

omit [NumberField K] in
/- English proof (translation)
Introduce `σ i j`. Use `congr 1`.
-/
theorem isBC_self (h : HermFam K (Fin m → K)) : IsBC h h := by
  intro σ i j
  congr 1

/- English proof (translation)
The claim follows from `Submodule.FG.of_le hL inf_le_left`.
-/
theorem lineLat_fg {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG) (x : Fin m → K) : (lineLat L x).FG :=
  Submodule.FG.of_le hL inf_le_left

/- English proof (translation)
Take `⟨s, rfl⟩` from `hL`. Set `f : (Fin m → K) → (Fin m → K')` to `fun v i => algebraMap K K' (v i)`. Use `⟨(s.finite_toSet.image f).toFinset, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`. Use `le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_` and prove the remaining obligations.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Express the relevant statement in the definitionally equal form `f v ∈ Submodule.span (𝓞 K') (f '' s)`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => have : f 0 = 0 := by ext i; simp [f]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: f (x + y) = f x + f y` using `by ext i; simp [f]`.

Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `: f (a • x) = (algebraMap (𝓞 K) (𝓞 K') a) • f x`. Use extensionality with `i`.

Simplify using `only [f, Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem latBC_fg (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG) :
    (latBC K' L).FG := by
  obtain ⟨s, rfl⟩ := hL
  let f : (Fin m → K) → (Fin m → K') := fun v i => algebraMap K K' (v i)
  refine ⟨(s.finite_toSet.image f).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  change f v ∈ Submodule.span (𝓞 K') (f '' s)
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => have : f 0 = 0 := by ext i; simp [f]
            rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := by ext i; simp [f]
      rw [this]; exact add_mem hx hy
  | smul a x _ hx =>
      have : f (a • x) = (algebraMap (𝓞 K) (𝓞 K') a) • f x := by
        ext i
        simp only [f, Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use `⟨K, inferInstance, inferInstance, inferInstance, h, fun _ => 1, isBC_self h, fun e => one_ne_zero (congrFun e 0), ?_⟩` and prove the remaining obligations. Establish `: lineLat L (fun _ : Fin 1 => (1 : K)) = L`. Use `inf_eq_left.mpr fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Conclude with `⟨v 0, by ext i; simp [Subsingleton.elim i 0]⟩`.

Rewrite using `[latBC_self, this]`. Simplify using `[hε.le]`.
-/
theorem rank_one (h : HermFam K (Fin 1 → K)) (L : Submodule (𝓞 K) (Fin 1 → K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin 1 → K')) (x : Fin 1 → K'),
      IsBC h h' ∧ x ≠ 0 ∧ deg h L / (1 : ℕ) - Real.log (1 : ℕ) / 2 - ε ≤ deg h' (lineLat (latBC K' L) x) := by
  refine ⟨K, inferInstance, inferInstance, inferInstance, h, fun _ => 1, isBC_self h, fun e => one_ne_zero (congrFun e 0), ?_⟩
  have : lineLat L (fun _ : Fin 1 => (1 : K)) = L := by
    refine inf_eq_left.mpr fun v _ => ?_
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    exact ⟨v 0, by ext i; simp [Subsingleton.elim i 0]⟩
  rw [latBC_self, this]
  simp [hε.le]

/- English proof (translation)
Take `⟨K', i1, i2, i3, h', x, a, b, c⟩` from `H K m (stdHerm K m) (stdLat K m) hm conjInv_std full_std ε hε`. Use `⟨K', i1, i2, i3, h', x, a, b, ?_⟩` and prove the remaining obligations. Rewrite `c` using `[deg_stdLat]`. Simplify `c` using `[neg_div]`.
-/
theorem std_line (H : AbsoluteSiegel) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin m → K')) (x : Fin m → K'),
      IsBC (stdHerm K m) h' ∧ x ≠ 0 ∧ - Real.log m / 2 - ε ≤ deg h' (lineLat (latBC K' (stdLat K m)) x) := by
  obtain ⟨K', i1, i2, i3, h', x, a, b, c⟩ := H K m (stdHerm K m) (stdLat K m) hm conjInv_std full_std ε hε
  refine ⟨K', i1, i2, i3, h', x, a, b, ?_⟩
  rw [deg_stdLat] at c
  simpa [neg_div] using c

end GlobalTheory.Published.SiegelModel
