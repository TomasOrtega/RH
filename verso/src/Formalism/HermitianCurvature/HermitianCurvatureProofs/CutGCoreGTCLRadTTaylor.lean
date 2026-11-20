import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut

open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Introduce `σ`. Proceed by induction on `σ using Equiv.Perm.swap_induction_on with`. Consider the case `one => intro v`. Both sides reduce to the same expression. Consider the case `swap_mul f x y hxy ih`.

Introduce `v`. Rewrite using `[Equiv.Perm.coe_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem perm_of_swaps {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W)
    (h : ∀ (a b : Fin n), a ≠ b → ∀ v : Fin n → E, T (v ∘ Equiv.swap a b) = T v) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), T (v ∘ σ) = T v := by
  classical
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro v; rfl
  | swap_mul f x y hxy ih =>
    intro v
    rw [Equiv.Perm.coe_mul]
    calc T (v ∘ (⇑(Equiv.swap x y) ∘ ⇑f)) = T ((v ∘ Equiv.swap x y) ∘ f) := rfl
      _ = T (v ∘ Equiv.swap x y) := ih _
      _ = T v := h x y hxy v

/- English proof (translation)
Establish `hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ∞` using `fun k => by first`. Consider the case `exact WithTop.coe_le_coe.2 le_top`. Consider the case `exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `W _ _ f U hU hf x hx σ v`. Rewrite using `[Subsingleton.elim (v ∘ σ) v]`. Consider the case `succ n ih`. Introduce `W _ _ f U hU hf x hx`.

Use `perm_of_swaps (iteratedFDeriv ℝ (n + 1) f x) ?_` and prove the remaining obligations. Introduce `a b hab`. Break down `n with _ | m` into its components or cases. Conclude with `absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab`. Establish `hfx : ContDiffAt ℝ ∞ f x` using `hf.contDiffAt (hU.mem_nhds hx)`.

Establish `hmul : ∀ σ τ : Equiv.Perm (Fin (m + 1 + 1)), (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) → (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) → ∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ ⇑(σ * τ)) = iterat …`. Introduce `σ τ hσ hτ v`. Rewrite using `[Equiv.Perm.coe_mul]`. Conclude with `(hτ (v ∘ σ)).trans (hσ v)`. Establish `T1 : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∀ v : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap a'.succ b'.succ) = iteratedFDeriv ℝ (m + 1 + 1) f x v`.

Introduce `a' b' _ v`. Rewrite using `[iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]`. Establish `h0 : (v ∘ Equiv.swap a'.succ b'.succ) 0 = v 0`. Simplify using `only [Function.comp_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a').symm (Fin.succ_ne_zero b').symm]`.

Establish `ht : Fin.tail (v ∘ Equiv.swap a'.succ b'.succ) = Fin.tail v ∘ Equiv.swap a' b'`. Use function extensionality and compare the values at `i`. Simplify using `only [Fin.tail, Function.comp_apply]`. Rewrite using `[(Fin.succ_injective _).swap_apply]`. Rewrite using `[h0, ht]`.

Establish `hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x` using `(hfx.iteratedFDeriv_right (m := 1) (i := m + 1) (by`. Use `hle (1 + (m + 1))` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Conclude with `this)).differentiableAt one_ne_zero`. Rewrite using `[← fderiv_continuousMultilinear_apply_const_apply hgd, ← fderiv_continuousMultilinear_apply_const_apply hgd]`.

Rewrite using `[Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih W f U hU hf y hy (Equiv.swap a' b') (Fin.tail v)))]`. Establish `T2 : ∀ v : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) = iteratedFDeriv ℝ (m + 1 + 1) f x v`. Introduce `v`. Establish `hrepr : ∀ w : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x w = fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (Fin.tail w 0) (Fin.tail (Fin.tail w))`. Introduce `w`.

Rewrite using `[iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]`. Use `first`. Consider the case `rfl`. Consider the case `simp [continuousMultilinearCurryLeftEquiv_symm_apply]`. Rewrite using `[hrepr, hrepr]`.

Establish `hg : ContDiffAt ℝ 2 (iteratedFDeriv ℝ m f) x` using `hfx.iteratedFDeriv_right (by have := hle (2 + m); push_cast at this ⊢; exact this)`. Establish `hs` using `hg.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])`. Establish `e0 : (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = Fin.tail v 0`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail]`. Establish `e1 : Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = v 0`.

Simplify using `only [Fin.tail, Function.comp_apply, Equiv.swap_apply_right]`. Establish `e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v)`. Use function extensionality and compare the values at `i`. Simplify using `only [Fin.tail, Function.comp_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]`.

Rewrite using `[e0, e1, e2, hs (Fin.tail v 0) (v 0)]`. Establish `T0 : ∀ b' : Fin (m + 1), ∀ v : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 b'.succ) = iteratedFDeriv ℝ (m + 1 + 1) f x v`. Introduce `b'`. Distinguish the cases in `hb : b' = 0`. Substitute `hb` using the available equality.

Conclude with `T2`. Establish `e` using `Equiv.swap_mul_swap_mul_swap (x := (0 : Fin (m + 1 + 1))) (y := Fin.succ 0) (z := b'.succ) (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero b').symm`. Rewrite using `[Equiv.swap_comm, ← e]`. Establish `h1` using `T1 0 b' (Ne.symm hb)`. Conclude with `hmul _ _ (hmul _ _ h1 T2) h1`.

Consider the cases of `a using Fin.cases with`. Consider the case `zero`. Consider the cases of `b using Fin.cases with`. Consider the case `zero => exact absurd rfl hab`. Consider the case `succ b' => exact T0 b'`.

Consider the case `succ a'`. Consider the cases of `b using Fin.cases with`. Consider the case `zero => intro v`. Rewrite using `[Equiv.swap_comm]`. Conclude with `T0 a' v`.

Consider the case `succ b' => exact T1 a' b' (fun h => hab (h ▸ rfl))`.
-/
theorem symm_iter : ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (U : Set E),
    IsOpen U → ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  intro n
  induction n with
  | zero =>
    intro W _ _ f U hU hf x hx σ v
    rw [Subsingleton.elim (v ∘ σ) v]
  | succ n ih =>
    intro W _ _ f U hU hf x hx
    refine perm_of_swaps (iteratedFDeriv ℝ (n + 1) f x) ?_
    intro a b hab
    rcases n with _ | m
    · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
    have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
    have hmul : ∀ σ τ : Equiv.Perm (Fin (m + 1 + 1)),
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        ∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ ⇑(σ * τ)) = iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul]
      exact (hτ (v ∘ σ)).trans (hσ v)
    have T1 : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap a'.succ b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro a' b' _ v
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have h0 : (v ∘ Equiv.swap a'.succ b'.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a').symm (Fin.succ_ne_zero b').symm]
      have ht : Fin.tail (v ∘ Equiv.swap a'.succ b'.succ) = Fin.tail v ∘ Equiv.swap a' b' := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [(Fin.succ_injective _).swap_apply]
      rw [h0, ht]
      have hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x :=
        (hfx.iteratedFDeriv_right (m := 1) (i := m + 1) (by
          have := hle (1 + (m + 1)); push_cast at this ⊢; exact this)).differentiableAt one_ne_zero
      rw [← fderiv_continuousMultilinear_apply_const_apply hgd,
        ← fderiv_continuousMultilinear_apply_const_apply hgd]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx)
        (fun y hy => ih W f U hU hf y hy (Equiv.swap a' b') (Fin.tail v)))]
    have T2 : ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro v
      have hrepr : ∀ w : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x w =
          fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (Fin.tail w 0) (Fin.tail (Fin.tail w)) := by
        intro w
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
        first
        | rfl
        | simp [continuousMultilinearCurryLeftEquiv_symm_apply]
      rw [hrepr, hrepr]
      have hg : ContDiffAt ℝ 2 (iteratedFDeriv ℝ m f) x :=
        hfx.iteratedFDeriv_right (by have := hle (2 + m); push_cast at this ⊢; exact this)
      have hs := hg.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      have e0 : (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = Fin.tail v 0 := by
        simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail]
      have e1 : Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = v 0 := by
        simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_right]
      have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]
      rw [e0, e1, e2, hs (Fin.tail v 0) (v 0)]
    have T0 : ∀ b' : Fin (m + 1), ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro b'
      by_cases hb : b' = 0
      · subst hb; exact T2
      · have e := Equiv.swap_mul_swap_mul_swap (x := (0 : Fin (m + 1 + 1))) (y := Fin.succ 0)
          (z := b'.succ) (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero b').symm
        rw [Equiv.swap_comm, ← e]
        have h1 := T1 0 b' (Ne.symm hb)
        exact hmul _ _ (hmul _ _ h1 T2) h1
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b' => exact T0 b'
    | succ a' =>
      cases b using Fin.cases with
      | zero => intro v; rw [Equiv.swap_comm]; exact T0 a' v
      | succ b' => exact T1 a' b' (fun h => hab (h ▸ rfl))

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/- English proof (translation)
The claim follows from `m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)`.
-/
theorem poly_contDiff {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ζ => m (fun _ => ζ - a)) := m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)

/- English proof (translation)
Establish `hg : ContDiff ℝ i (fun ζ : E => m (fun _ => ζ))` using `m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)`. Use `set L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E with hL`. Establish `hcomp : (fun ζ : E => m (fun _ => ζ)) ∘ L = ((2 : ℝ) ^ j) • (fun ζ : E => m (fun _ => ζ))`. Use function extensionality and compare the values at `ζ`. Simplify using `only [Function.comp_apply, Pi.smul_apply, hL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]`.

Rewrite using `[m.map_smul_univ (fun _ => (2 : ℝ)) (fun _ => ζ)]`. Simplify using `[Finset.prod_const]`. Establish `h1` using `ContinuousLinearMap.iteratedFDeriv_comp_right L hg 0 (i := i) le_rfl`. Rewrite `h1` using `[hcomp, iteratedFDeriv_const_smul_apply hg.contDiffAt, map_zero]`. Establish `hne : (2 : ℝ) ^ j ≠ (2 : ℝ) ^ i`.

Introduce `h`. Apply `hij` to reduce the goal to its premises. Establish `: (2 : ℕ) ^ j = 2 ^ i` using `by exact_mod_cast h`. Conclude with `(Nat.pow_right_injective le_rfl this).symm`. Use extensionality with `v`.

Establish `key : ((2 : ℝ) ^ j) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = ((2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v`. Establish `hv` using `congrArg (fun T => T v) h1`. Simplify using `only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv`. Rewrite using `[hv, hL]`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]`.

Rewrite using `[ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0) (fun _ => (2 : ℝ)) v]`. Simplify using `[Finset.prod_const]`. Establish `h0 : ((2 : ℝ) ^ j - (2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = 0`. Rewrite using `[sub_smul, key, sub_self]`. Rewrite using `[ContinuousMultilinearMap.zero_apply]`.

Conclude with `(smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)`.
-/
theorem poly_hom {j i : ℕ} (hij : i ≠ j) (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ)) 0 = 0 := by
  have hg : ContDiff ℝ i (fun ζ : E => m (fun _ => ζ)) :=
    m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  set L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E with hL
  have hcomp : (fun ζ : E => m (fun _ => ζ)) ∘ L = ((2 : ℝ) ^ j) • (fun ζ : E => m (fun _ => ζ)) := by
    funext ζ
    simp only [Function.comp_apply, Pi.smul_apply, hL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [m.map_smul_univ (fun _ => (2 : ℝ)) (fun _ => ζ)]
    simp [Finset.prod_const]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right L hg 0 (i := i) le_rfl
  rw [hcomp, iteratedFDeriv_const_smul_apply hg.contDiffAt, map_zero] at h1
  have hne : (2 : ℝ) ^ j ≠ (2 : ℝ) ^ i := by
    intro h
    apply hij
    have : (2 : ℕ) ^ j = 2 ^ i := by exact_mod_cast h
    exact (Nat.pow_right_injective le_rfl this).symm
  ext v
  have key : ((2 : ℝ) ^ j) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v =
      ((2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v := by
    have hv := congrArg (fun T => T v) h1
    simp only [ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv
    rw [hv, hL]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0)
      (fun _ => (2 : ℝ)) v]
    simp [Finset.prod_const]
  have h0 : ((2 : ℝ) ^ j - (2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = 0 := by
    rw [sub_smul, key, sub_self]
  rw [ContinuousMultilinearMap.zero_apply]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[dif_pos rfl, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, poly_hom h m]`.

Both sides reduce to the same expression.
-/
theorem poly_at {j i : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) (v : Fin i → E) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ - a)) a v =
      if h : i = j then ∑ σ : Equiv.Perm (Fin j), m (fun k => (v ∘ Fin.cast h.symm) (σ k)) else 0 := by
  by_cases h : i = j
  · subst h
    rw [dif_pos rfl, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self,
      ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
    rfl
  · rw [dif_neg h, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, poly_hom h m]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

/- English proof (translation)
Introduce `V _ _ ψ U ζ₀ N hU hζ hψ i hi`. Establish `hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)` using `fun k => by first`. Consider the case `exact WithTop.coe_le_coe.2 le_top`. Consider the case `exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)`. Establish `hψat : ContDiffAt ℝ i ψ ζ₀` using `(hψ.contDiffAt (hU.mem_nhds hζ)).of_le (hle i)`.

Establish `hS : ContDiff ℝ i (fun ζ : ℂ => ∑ j ∈ Finset.range (N + 1), ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀))` using `ContDiff.sum fun j _ => (poly_contDiff _ _).const_smul _`. Use `(iteratedFDeriv_sub_apply hψat hS.contDiffAt).trans ?_` and prove the remaining obligations. Rewrite using `[sub_eq_zero, iteratedFDeriv_sum (fun j _ => (poly_contDiff _ _).const_smul _)]`. Use extensionality with `v`. Rewrite using `[Finset.sum_apply, ContinuousMultilinearMap.sum_apply]`.

Establish `hterm : ∀ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ i (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ v = if j = i then ((i.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) else 0`. Introduce `j _`. Rewrite using `[show (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) = ((j.factorial : ℝ)⁻¹) • (fun ζ : ℂ => iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) from rfl, iteratedFDeriv_const_smul_apply ((poly_contDiff _ _).contDiffAt), ContinuousMultilinearMap.smul_appl …`. Use `split_ifs with h1 h2 h2`. Substitute `h1` using the available equality.

Both sides reduce to the same expression. Conclude with `absurd h1.symm h2`. Conclude with `absurd h2.symm h1`. Rewrite using `[smul_zero]`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hi))]`.

Establish `hs : ∀ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) = iteratedFDeriv ℝ i ψ ζ₀ v` using `fun σ => symm_iter i V ψ U hU hψ ζ₀ hζ σ v`. Rewrite using `[Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_smul]`.
-/
theorem taylor_expansion_holds : GTCLRTaylor := by
  intro V _ _ ψ U ζ₀ N hU hζ hψ i hi
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  have hψat : ContDiffAt ℝ i ψ ζ₀ := (hψ.contDiffAt (hU.mem_nhds hζ)).of_le (hle i)
  have hS : ContDiff ℝ i (fun ζ : ℂ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) :=
    ContDiff.sum fun j _ => (poly_contDiff _ _).const_smul _
  refine (iteratedFDeriv_sub_apply hψat hS.contDiffAt).trans ?_
  rw [sub_eq_zero, iteratedFDeriv_sum (fun j _ => (poly_contDiff _ _).const_smul _)]
  ext v
  rw [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      iteratedFDeriv ℝ i (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ v =
        if j = i then ((i.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ)
        else 0 := by
    intro j _
    rw [show (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) =
        ((j.factorial : ℝ)⁻¹) • (fun ζ : ℂ => iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) from rfl,
      iteratedFDeriv_const_smul_apply ((poly_contDiff _ _).contDiffAt),
      ContinuousMultilinearMap.smul_apply, poly_at]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hi))]
  have hs : ∀ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) = iteratedFDeriv ℝ i ψ ζ₀ v :=
    fun σ => symm_iter i V ψ U hU hψ ζ₀ hζ σ v
  rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_smul]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
