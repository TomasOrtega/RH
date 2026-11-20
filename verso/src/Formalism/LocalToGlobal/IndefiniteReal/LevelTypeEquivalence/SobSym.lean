import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterSymmR

namespace Formalism.IndefR.Eqv

open scoped ContDiff

section Sym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Conclude with `ENat.natCast_lt_top m` after adjusting the coercions.
-/
theorem natCast_lt_inf' (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m

/- English proof (translation)
Rewrite using `[minSmoothness_of_isRCLikeNormedField]`. Conclude with `(natCast_lt_inf' 2).le` after adjusting the coercions.
-/
theorem two_le_inf : minSmoothness ℝ 2 ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact_mod_cast (natCast_lt_inf' 2).le

/- English proof (translation)
Use `first`. Consider the case `(rw [(WithTop.coe_natCast m).symm, ← WithTop.coe_add, top_add])`. Consider the case `simp`. Consider the case `(norm_cast; simp)`.
-/
theorem inf_add_nat (m : ℕ) : (∞ : WithTop ℕ∞) + (m : WithTop ℕ∞) ≤ ∞ := by
  first
    | (rw [(WithTop.coe_natCast m).symm, ← WithTop.coe_add, top_add])
    | simp
    | (norm_cast; simp)

/- English proof (translation)
Establish `key : ∀ u : Fin (m + 2) → E, iteratedFDeriv ℝ (m + 2) g x u = fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m g)) x (u 0) (u 1) (Fin.tail (Fin.tail u))`. Introduce `u`. Rewrite using `[iteratedFDeriv_succ_apply_left]`. Establish `hL : iteratedFDeriv ℝ (m + 1) g = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) H).symm ∘ fderiv ℝ (iteratedFDeriv ℝ m g)`. Rewrite using `[iteratedFDeriv_succ_eq_comp_left]`.

Rewrite using `[hL, LinearIsometryEquiv.comp_fderiv]`. Both sides reduce to the same expression. Rewrite using `[key, key]`. Establish `hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ m g) x` using `((hg.iteratedFDeriv_right (m := ∞) (i := m) (inf_add_nat m)).contDiffAt).isSymmSndFDerivAt two_le_inf`. Establish `e0 : (v ∘ Equiv.swap 0 1) 0 = v 1` using `by simp`.

Establish `e1 : (v ∘ Equiv.swap 0 1) 1 = v 0` using `by simp`. Establish `e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v)`. Use function extensionality and compare the values at `j`. Simplify using `only [Fin.tail, Function.comp_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => by`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this)]`. Rewrite using `[e0, e1, e2, hs (v 1) (v 0)]`.
-/
theorem iterated_fderiv_swap_first_two {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {g : E → H} (hg : ContDiff ℝ ∞ g) (m : ℕ)
    (x : E) (v : Fin (m + 2) → E) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (m + 2) g x v := by
  have key : ∀ u : Fin (m + 2) → E, iteratedFDeriv ℝ (m + 2) g x u =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m g)) x (u 0) (u 1) (Fin.tail (Fin.tail u)) := by
    intro u
    rw [iteratedFDeriv_succ_apply_left]
    have hL : iteratedFDeriv ℝ (m + 1) g =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) H).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ m g) := by
      rw [iteratedFDeriv_succ_eq_comp_left]
    rw [hL, LinearIsometryEquiv.comp_fderiv]
    rfl
  rw [key, key]
  have hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ m g) x :=
    ((hg.iteratedFDeriv_right (m := ∞) (i := m) (inf_add_nat m)).contDiffAt).isSymmSndFDerivAt two_le_inf
  have e0 : (v ∘ Equiv.swap 0 1) 0 = v 1 := by simp
  have e1 : (v ∘ Equiv.swap 0 1) 1 = v 0 := by simp
  have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext j
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => by
      have := congrArg Fin.val h; simp at this)]
  rw [e0, e1, e2, hs (v 1) (v 0)]

/- English proof (translation)
Set `A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H →L[ℝ] H` to `ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H (u ∘ σ) - ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H u`. Establish `hzero : (fun y => A (Φ y)) = fun _ => 0`. Use function extensionality and compare the values at `y`. Simplify using `only [A, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply, hinv, sub_self]`. Establish `h1 : fderiv ℝ (fun y => A (Φ y)) x = A.comp (fderiv ℝ Φ x)` using `(A.hasFDerivAt.comp x (hΦ x).hasFDerivAt).fderiv`.

Rewrite `h1` using `[hzero, fderiv_const_apply]`. Establish `h2` using `congrArg (fun T => T w) h1`. Simplify using `only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply, A, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply] at h2`. Conclude with `(sub_eq_zero.mp h2.symm)`.
-/
theorem fderiv_inv {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H} (hΦ : Differentiable ℝ Φ) (σ : Equiv.Perm (Fin n))
    (hinv : ∀ y u, Φ y (u ∘ σ) = Φ y u) (x w : E) (u : Fin n → E) :
    fderiv ℝ Φ x w (u ∘ σ) = fderiv ℝ Φ x w u := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H →L[ℝ] H :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H (u ∘ σ) -
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H u
  have hzero : (fun y => A (Φ y)) = fun _ => 0 := by
    funext y
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply, hinv, sub_self]
  have h1 : fderiv ℝ (fun y => A (Φ y)) x = A.comp (fderiv ℝ Φ x) :=
    (A.hasFDerivAt.comp x (hΦ x).hasFDerivAt).fderiv
  rw [hzero, fderiv_const_apply] at h1
  have h2 := congrArg (fun T => T w) h1
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply, A,
    ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply] at h2
  exact (sub_eq_zero.mp h2.symm)

/- English proof (translation)
Establish `hgen : σ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Discharge the goal by the elementary cases of `trivial`. Use `revert v`. Proceed by induction on `hgen using Submonoid.closure_induction with`.

Consider the case `mem τ hτ`. Take `⟨i, rfl⟩` from `hτ`. Introduce `v`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => exact iterated_fderiv_swap_first_two hg m x v`.

Consider the case `succ a`. Rewrite using `[iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]`. Establish `hΦ : Differentiable ℝ (iteratedFDeriv ℝ (m + 1) g)` using `hg.differentiable_iteratedFDeriv (natCast_lt_inf' (m + 1))`. Establish `hne0 : ∀ j : Fin (m + 2), j ≠ 0 → True` using `fun _ _ => trivial`. Establish `h0 : (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) 0 = v 0`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (fun h => by have := congrArg Fin.val h; simp at this) (fun h => by have := congrArg Fin.val h; simp at this)]`. Establish `ht : Fin.tail (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) = Fin.tail v ∘ Equiv.swap a.castSucc a.succ`. Use function extensionality and compare the values at `j`. Simplify using `only [Fin.tail, Function.comp_apply]`.

Use `congr 1`. Rewrite using `[show a.succ.castSucc = a.castSucc.succ from rfl]`. Conclude with `(Fin.succ_injective _).swap_apply _ _ _`. Rewrite using `[h0, ht]`. Conclude with `fderiv_inv hΦ _ (fun y u => IH H g hg y u _) x (v 0) (Fin.tail v)`.

Consider the case `one => intro v`. Both sides reduce to the same expression. Consider the case `mul τ ρ _ _ hτ hρ`. Introduce `v`. Establish `e : v ∘ ⇑(τ * ρ) = (v ∘ τ) ∘ ρ` using `rfl`.

Rewrite using `[e, hρ (v ∘ τ), hτ v]`.
-/
theorem iterSymm_succ (m : ℕ) (IH : ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (x : E) (v : Fin (m + 1) → E) (σ : Equiv.Perm (Fin (m + 1))),
      iteratedFDeriv ℝ (m + 1) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 1) g x v)
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H) (hg : ContDiff ℝ ∞ g) (x : E)
    (v : Fin (m + 2) → E) (σ : Equiv.Perm (Fin (m + 2))) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 2) g x v := by
  have hgen : σ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  revert v
  induction hgen using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    intro v
    cases i using Fin.cases with
    | zero => exact iterated_fderiv_swap_first_two hg m x v
    | succ a =>
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have hΦ : Differentiable ℝ (iteratedFDeriv ℝ (m + 1) g) :=
        hg.differentiable_iteratedFDeriv (natCast_lt_inf' (m + 1))
      have hne0 : ∀ j : Fin (m + 2), j ≠ 0 → True := fun _ _ => trivial
      have h0 : (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => by have := congrArg Fin.val h; simp at this)
          (fun h => by have := congrArg Fin.val h; simp at this)]
      have ht : Fin.tail (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) =
          Fin.tail v ∘ Equiv.swap a.castSucc a.succ := by
        funext j
        simp only [Fin.tail, Function.comp_apply]
        congr 1
        rw [show a.succ.castSucc = a.castSucc.succ from rfl]
        exact (Fin.succ_injective _).swap_apply _ _ _
      rw [h0, ht]
      exact fderiv_inv hΦ _ (fun y u => IH H g hg y u _) x (v 0) (Fin.tail v)
  | one => intro v; rfl
  | mul τ ρ _ _ hτ hρ =>
    intro v
    have e : v ∘ ⇑(τ * ρ) = (v ∘ τ) ∘ ρ := rfl
    rw [e, hρ (v ∘ τ), hτ v]

/- English proof (translation)
Introduce `E H _ _ _ _ g hg n`. Use `match n with`. Consider the case `0`. Introduce `x v σ`. Establish `: σ = 1` using `Equiv.ext fun a => a.elim0`.

Rewrite using `[this]`. Both sides reduce to the same expression. Consider the case `m + 1`. Proceed by induction on `m generalizing H g with`. Consider the case `zero`.

Introduce `x v σ`. Establish `: σ = 1` using `Equiv.ext fun a => Fin.ext (by have := (σ a).isLt; have := a.isLt; simp)`. Rewrite using `[this]`. Both sides reduce to the same expression. Consider the case `succ m ih => exact iterSymm_succ m (fun H _ _ g hg => ih H g hg) H g hg`.
-/
theorem iterSymmR : IterSymmR := by
  intro E H _ _ _ _ g hg n
  match n with
  | 0 =>
    intro x v σ
    have : σ = 1 := Equiv.ext fun a => a.elim0
    rw [this]; rfl
  | m + 1 =>
    induction m generalizing H g with
    | zero =>
      intro x v σ
      have : σ = 1 := Equiv.ext fun a => Fin.ext (by have := (σ a).isLt; have := a.isLt; simp)
      rw [this]; rfl
    | succ m ih => exact iterSymm_succ m (fun H _ _ g hg => ih H g hg) H g hg

end Sym

end Formalism.IndefR.Eqv
