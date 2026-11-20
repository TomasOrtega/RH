import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((invT a R g)⁻¹).valᵀ = g.val`. Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `((g⁻¹)⁻¹).valᵀᵀ = g.val`. Rewrite using `[inv_inv, Matrix.transpose_transpose]`.
-/
theorem invT_invT_gl {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  rw [inv_inv, Matrix.transpose_transpose]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ`. Rewrite using `[← map_inv]`. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem map_invT_gl {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  change p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ
  rw [← map_inv]
  ext i j
  rfl

/- English proof (translation)
Apply `ga_ext` to reduce the goal to its premises. Rewrite using `[map_invT_gl, pInf_infGL, pInf_infGL]`. Rewrite using `[map_invT_gl, pFin_infGL, pFin_infGL, map_one]`.
-/
theorem invT_infGL (y : GL (Fin a) (Cinf E)) : invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) := by
  apply ga_ext
  · rw [map_invT_gl, pInf_infGL, pInf_infGL]
  · rw [map_invT_gl, pFin_infGL, pFin_infGL, map_one]

/- English proof (translation)
Establish `key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖` using `fun y => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j => (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)`. Use `le_antisymm (key x) ?_` and prove the remaining obligations. Simplify using `using key xᵀ`.
-/
theorem norm_toL_transpose (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL xᵀ‖ = ‖toL x‖ := by
  have key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖ := fun y =>
    pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j =>
      (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)
  refine le_antisymm (key x) ?_
  simpa using key xᵀ

/- English proof (translation)
Express the relevant statement in the definitionally equal form `1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖`. Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _`. Rewrite using `[inv_inv, norm_toL_transpose, norm_toL_transpose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  rw [← map_inv]
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _
  rw [inv_inv, norm_toL_transpose, norm_toL_transpose]
  ring

/- English proof (translation)
Use `⟨hk.1, ?_, fun N => ?_⟩` and prove the remaining obligations. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_ set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)` and prove the remaining obligations. Establish `e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) = fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i`. Use function extensionality and compare the values at `x`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j'` using `fun i' j' => (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)`. Conclude with `measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i) ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i) fun i' j' => (measurable_pi_apply w).comp (h …`. Simplify using `only [height_invT]`.

Conclude with `hk.2.2 N`.
-/
theorem isRapidInf_invT {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : IsRapidInf ν k γ) : IsRapidInf ν k (fun x => invT a (Cinf E) (γ x)) := by
  refine ⟨hk.1, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
    set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    have e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) =
        fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i := by
      funext x
      rw [← map_inv]; rfl
    rw [e]
    have hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j' := fun i' j' =>
      (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)
    exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i)
      ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
        ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i)
      fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
  · simp only [height_invT]
    exact hk.2.2 N

/- English proof (translation)
Unfold `kerInf`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `show k x * F (invT a (Ad E) g * infGL E a (γ x)) = k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))`. Rewrite using `[map_mul, invT_infGL, invT_invT_gl]`.
-/
theorem kerInf_comp_invT {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) :
    kerInf ν k γ F (invT a (Ad E) g) =
      kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) g := by
  unfold kerInf
  congr 1
  funext x
  show k x * F (invT a (Ad E) g * infGL E a (γ x)) =
    k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))
  rw [map_mul, invT_infGL, invT_invT_gl]

/- English proof (translation)
Set `T : Submodule ℂ (GA E a → ℂ)` to `(rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))`. Establish `memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra` using `fun G => Submodule.mem_comap`. Establish `hle : rspan π ≤ T`. Use `rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_` and prove the remaining obligations. Rewrite using `[memT]`.

Establish `h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V` using `Submodule.mem_map_of_mem hφ`. Conclude with `mem_rspan h1`. Rewrite `hF`, the goal using `[memT]`. Establish `h2` using `rt_mem_rspan hF (invT a (Ad E) h)`. Establish `e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h))`.

Use function extensionality and compare the values at `g`. Rewrite using `[map_mul, invT_invT_gl]`. Rewrite using `[e]`. Conclude with `h2`. Rewrite `hF`, the goal using `[memT]`.

Establish `h3` using `kerInf_mem_rspan hF ν (isRapidInf_invT hk)`. Establish `e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) = kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h))`. Use function extensionality and compare the values at `fun g => kerInf_comp_invT ν k γ F g`. Rewrite using `[e]`. Conclude with `h3`.

Rewrite `hF`, the goal using `[← rspan_eq_mspanR]`. Conclude with `(memT F).1 (hle hF)`.
-/
theorem comp_invT_mem_mspanR (π : CuspSub E a) (F : GA E a → ℂ) (hF : F ∈ mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ mspanR π.contra := by
  let T : Submodule ℂ (GA E a → ℂ) :=
    (rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))
  have memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra := fun G =>
    Submodule.mem_comap
  have hle : rspan π ≤ T := by
    refine rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_
    · rw [memT]
      have h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V := Submodule.mem_map_of_mem hφ
      exact mem_rspan h1
    · rw [memT] at hF ⊢
      have h2 := rt_mem_rspan hF (invT a (Ad E) h)
      have e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h)) := by
        funext g; rw [map_mul, invT_invT_gl]
      rw [e]; exact h2
    · rw [memT] at hF ⊢
      have h3 := kerInf_mem_rspan hF ν (isRapidInf_invT hk)
      have e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) =
          kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) :=
        funext fun g => kerInf_comp_invT ν k γ F g
      rw [e]; exact h3
  rw [← rspan_eq_mspanR] at hF ⊢
  exact (memT F).1 (hle hF)

/- English proof (translation)
Assemble the required witnesses or components as `⟨comp_invT_mem_mspanR π φ.1 (rspan_eq_mspanR π ▸ mem_rspan hφ), rspan_eq_mspanR π.contra ▸ rspan_ne_bot _⟩`.
-/
example (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) :
    (fun g => φ.1 (invT a (Ad E) g)) ∈ mspanR π.contra ∧ mspanR π.contra ≠ ⊥ :=
  ⟨comp_invT_mem_mspanR π φ.1 (rspan_eq_mspanR π ▸ mem_rspan hφ), rspan_eq_mspanR π.contra ▸ rspan_ne_bot _⟩

/- English proof (translation)
Introduce `_ _ _ _ _ π F hF` and use `comp_invT_mem_mspanR π F hF`.
-/
theorem invT_mem_mspanR_contra : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  fun _ _ _ _ _ π F hF => comp_invT_mem_mspanR π F hF

end GlobalTheory.JSW
