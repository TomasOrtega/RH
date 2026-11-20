import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep

noncomputable section

open Filter Topology Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.TypeSum.SmoothFrechet
open scoped ContDiff

namespace GlobalTheory.FamSmooth

section Mat
variable {n : ℕ} {k : ℕ}

/- English proof (translation)
Use `List.ext_getElem (by simp) fun j h1 h2 => ?_` and prove the remaining obligations. Simplify using `only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff, eq_comm]`.
-/
theorem ofFn_update_eq_set {M : Type} (f : Fin k → M) (i : Fin k) (a : M) :
    List.ofFn (Function.update f i a) = (List.ofFn f).set i a := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff, eq_comm]

def facs (Xs : Fin k → Mx n) : List ((Fin k → ℝ) → Mx n) := List.ofFn fun i t => NormedSpace.exp (t i • Xs i)

/- English proof (translation)
The claim follows from `| [], _ => one_mem_UJ ε | x :: l, h => by rw [List.prod_cons] exact mul_mem_UJ (h x List.mem_cons_self) (list_prod_mem l fun y hy => h y (List.mem_cons_of_mem _ hy))`.
-/
theorem list_prod_mem {ε : Fin n → Bool} : ∀ l : List (Mx n), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => one_mem_UJ ε
  | x :: l, h => by
    rw [List.prod_cons]
    exact mul_mem_UJ (h x List.mem_cons_self) (list_prod_mem l fun y hy => h y (List.mem_cons_of_mem _ hy))

/- English proof (translation)
Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)`. Proceed by induction on `fs with`. Consider the case `nil => intro _`. Simplify using `using contDiff_const`.

Consider the case `cons f fs ih`. Introduce `h`. Simplify using `only [List.map_cons, List.prod_cons]`. Conclude with `(h f List.mem_cons_self).mul (ih fun g hg => h g (List.mem_cons_of_mem _ hg))`.
-/
theorem contDiff_listProd (fs : List ((Fin k → ℝ) → Mx n)) :
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    (∀ f ∈ fs, ContDiff ℝ ∞ f) → ContDiff ℝ ∞ (fun t => (fs.map (· t)).prod) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  induction fs with
  | nil => intro _; simpa using contDiff_const
  | cons f fs ih =>
    intro h
    simp only [List.map_cons, List.prod_cons]
    exact (h f List.mem_cons_self).mul (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

/- English proof (translation)
Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)`. Introduce `f hf`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hf`. Establish `he : ContDiff ℝ ∞ (NormedSpace.exp : Mx n → Mx n)` using `contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt`.

Conclude with `he.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)`.
-/
theorem contDiff_facs (Xs : Fin k → Mx n) :
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    ∀ f ∈ facs Xs, ContDiff ℝ ∞ f := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Mx n → Mx n) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact he.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)

def ctL : Mx n →ₗ[ℝ] Mx n where
  toFun M := Mᴴ
  map_add' := conjTranspose_add
  map_smul' r M := by simp [conjTranspose_smul]

/- English proof (translation)
Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)`. Establish `e : (fun t => φ ((B t)⁻¹ * X * B t)) = fun t => φ (Jm ε * ctL (B t) * Jm ε * X * B t)`. Use function extensionality and compare the values at `t`. Rewrite using `[inv_eq_UJ (hU t)]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `hc : ContDiff ℝ ∞ fun t => ctL (B t)` using `((LinearMap.toContinuousLinearMap ctL).contDiff.comp hB :)`. Conclude with `(LinearMap.toContinuousLinearMap φ).contDiff.comp ((((contDiff_const.mul hc).mul contDiff_const).mul contDiff_const).mul hB)`.
-/
theorem contDiff_coef (ε : Fin n → Bool) (φ : Mx n →ₗ[ℝ] ℝ) (X : Mx n) (B : (Fin k → ℝ) → Mx n)
    (hB : letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      ContDiff ℝ ∞ B) (hU : ∀ t, B t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => φ ((B t)⁻¹ * X * B t) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have e : (fun t => φ ((B t)⁻¹ * X * B t)) = fun t => φ (Jm ε * ctL (B t) * Jm ε * X * B t) := by
    funext t; rw [inv_eq_UJ (hU t)]; rfl
  rw [e]
  have hc : ContDiff ℝ ∞ fun t => ctL (B t) := ((LinearMap.toContinuousLinearMap ctL).contDiff.comp hB :)
  exact (LinearMap.toContinuousLinearMap φ).contDiff.comp
    ((((contDiff_const.mul hc).mul contDiff_const).mul contDiff_const).mul hB)

end Mat

section Partials
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using continuous_fst`. Simplify using `only [Fin.cons_succ]`. Conclude with `(continuous_apply j).comp continuous_snd`.
-/
theorem continuous_cons_pair {k : ℕ} :
    Continuous (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k+1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `F d _ _ t`. Simplify using `using hasFDerivAt_of_subsingleton F t`.

Consider the case `succ k ih`. Introduce `F d hd hc t`. Set `f : ℝ → (Fin k → ℝ) → E` to `fun x y => F (Fin.cons x y)`. Set `f₁ : ℝ → (Fin k → ℝ) → ℝ →L[ℝ] E` to `fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (d 0 (Fin.cons x y))`. Set `f₂ : ℝ → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] E` to `fun x y => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d j.succ (Fin.cons x y))`.

Establish `df₁ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f · v.2) (↿f₁ v) v.1`. Introduce `v`. Establish `h` using `hd 0 (Fin.cons v.1 v.2)`. Simplify using `only [Fin.update_cons_zero, Fin.cons_zero] at h`. Conclude with `h.hasFDerivAt`.

Establish `df₂ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f v.1 ·) (↿f₂ v) v.2`. Introduce `v`. Use `ih (fun y => F (Fin.cons v.1 y)) (fun j y => d j.succ (Fin.cons v.1 y)) ?_ ?_ v.2` and prove the remaining obligations. Introduce `j y`. Establish `h` using `hd j.succ (Fin.cons v.1 y)`.

Simplify using `only [Fin.cons_succ] at h`. Use `h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `[Fin.cons_update]`. Introduce `j`. Conclude with `(hc j.succ).comp (continuous_cons_pair.comp (continuous_const.prodMk continuous_id))`.

Establish `cf₁ : Continuous ↿f₁` using `(ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp ((hc 0).comp continuous_cons_pair)`. Establish `cf₂ : Continuous ↿f₂` using `by show Continuous fun p : ℝ × (Fin k → ℝ) => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d j.succ (Fin.cons p.1 p.2))`. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E (ContinuousLinearMap.proj j)).continuous.comp ((hc j.succ).comp continuous_cons_pair)`. Set `ι : (Fin (k+1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ)` to `(ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ)`.

Establish `key` using `hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ι t) (f := f) (f₁ := f₁) (f₂ := f₂) (Eventually.of_forall df₁) (Eventually.of_forall df₂) cf₁.continuousAt cf₂.continuousAt`. Establish `k2` using `key.hasFDerivAt.comp t ι.hasFDerivAt`. Establish `ht : (Fin.cons (t 0) (fun j => t j.succ) : Fin (k+1) → ℝ) = t` using `Fin.cons_self_tail t`. Use `(k2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_fderiv ?_` and prove the remaining obligations. Use `show F v = F (Fin.cons (v 0) (Fin.tail v))`.

Rewrite using `[Fin.cons_self_tail]`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[ι, f₁, f₂, Function.HasUncurry.uncurry, Fin.sum_univ_succ, ht]`.
-/
theorem hasFDerivAt_of_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → E) (d : Fin k → (Fin k → ℝ) → E),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k
  induction k with
  | zero =>
    intro F d _ _ t
    simpa using hasFDerivAt_of_subsingleton F t
  | succ k ih =>
    intro F d hd hc t
    let f : ℝ → (Fin k → ℝ) → E := fun x y => F (Fin.cons x y)
    let f₁ : ℝ → (Fin k → ℝ) → ℝ →L[ℝ] E :=
      fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (d 0 (Fin.cons x y))
    let f₂ : ℝ → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] E :=
      fun x y => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
        (d j.succ (Fin.cons x y))
    have df₁ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f · v.2) (↿f₁ v) v.1 := by
      intro v
      have h := hd 0 (Fin.cons v.1 v.2)
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h
      exact h.hasFDerivAt
    have df₂ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f v.1 ·) (↿f₂ v) v.2 := by
      intro v
      refine ih (fun y => F (Fin.cons v.1 y)) (fun j y => d j.succ (Fin.cons v.1 y)) ?_ ?_ v.2
      · intro j y
        have h := hd j.succ (Fin.cons v.1 y)
        simp only [Fin.cons_succ] at h
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
        simp [Fin.cons_update]
      · intro j
        exact (hc j.succ).comp (continuous_cons_pair.comp (continuous_const.prodMk continuous_id))
    have cf₁ : Continuous ↿f₁ :=
      (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp
        ((hc 0).comp continuous_cons_pair)
    have cf₂ : Continuous ↿f₂ := by
      show Continuous fun p : ℝ × (Fin k → ℝ) => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d j.succ (Fin.cons p.1 p.2))
      refine continuous_finset_sum _ fun j _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E
        (ContinuousLinearMap.proj j)).continuous.comp ((hc j.succ).comp continuous_cons_pair)
    let ι : (Fin (k+1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ)
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ι t) (f := f) (f₁ := f₁) (f₂ := f₂)
      (Eventually.of_forall df₁) (Eventually.of_forall df₂) cf₁.continuousAt cf₂.continuousAt
    have k2 := key.hasFDerivAt.comp t ι.hasFDerivAt
    have ht : (Fin.cons (t 0) (fun j => t j.succ) : Fin (k+1) → ℝ) = t := Fin.cons_self_tail t
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_fderiv ?_
    · show F v = F (Fin.cons (v 0) (Fin.tail v))
      rw [Fin.cons_self_tail]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [ι, f₁, f₂, Function.HasUncurry.uncurry, Fin.sum_univ_succ, ht]

/- English proof (translation)
Rewrite using `[contDiff_succ_iff_hasFDerivAt]`. Use `⟨fun t => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t), ?_, hasFDerivAt_of_partials k F d hd fun i => (hc i).continuous⟩` and prove the remaining obligations. Conclude with `ContDiff.sum fun i _ => (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E (ContinuousLinearMap.proj i)).contDiff.comp (hc i)`.
-/
theorem contDiff_succ_of_partials {k : ℕ} (m : ℕ) (F : (Fin k → ℝ) → E) (d : Fin k → (Fin k → ℝ) → E)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (hc : ∀ i, ContDiff ℝ m (d i)) : ContDiff ℝ (m + 1) F := by
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun t => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t), ?_,
    hasFDerivAt_of_partials k F d hd fun i => (hc i).continuous⟩
  exact ContDiff.sum fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E (ContinuousLinearMap.proj i)).contDiff.comp (hc i)

end Partials

section Main

variable {n k : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hσ.1.1, hσ.1.2, 1, 0, fun g hg => by rw [pow_zero, mul_one] exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hσ.2.1 g hg x, one_mul]⟩`.
-/
theorem modRep_of_isURepOn {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : ModRep ε σ :=
  ⟨hσ.1.1, hσ.1.2, 1, 0, fun g hg => by
    rw [pow_zero, mul_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hσ.2.1 g hg x, one_mul]⟩

/- English proof (translation)
Establish `e : (facs Xs).map (· (Function.update t i s)) = ((facs Xs).map (· t)).set i (NormedSpace.exp (s • Xs i))`. Rewrite using `[facs, List.map_ofFn, List.map_ofFn, ← ofFn_update_eq_set]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp_apply, Function.update_apply]`.

Use `split_ifs with hj`. Substitute `hj` using the available equality. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[e, List.prod_set, if_pos (by simp [facs]), List.map_drop]`.
-/
theorem prod_update (Xs : Fin k → Mx n) (t : Fin k → ℝ) (i : Fin k) (s : ℝ) :
    ((facs Xs).map (· (Function.update t i s))).prod =
      (((facs Xs).map (· t)).take i).prod * NormedSpace.exp (s • Xs i) *
        (((facs Xs).drop (i + 1)).map (· t)).prod := by
  have e : (facs Xs).map (· (Function.update t i s)) =
      ((facs Xs).map (· t)).set i (NormedSpace.exp (s • Xs i)) := by
    rw [facs, List.map_ofFn, List.map_ofFn, ← ofFn_update_eq_set]
    congr 1
    funext j
    simp only [Function.comp_apply, Function.update_apply]
    split_ifs with hj
    · subst hj; rfl
    · rfl
  rw [e, List.prod_set, if_pos (by simp [facs]), List.map_drop]

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ v hv k Xs hX`. Establish `h` using `modRep_of_isURepOn hσ`. Take `⟨d, b, φ, hb⟩` from `exists_frame ε`. Establish `hmem : ∀ t, ∀ x ∈ (facs Xs).map (· t), x ∈ UJset ε`. Introduce `t x hx`.

Take `⟨f, hf, rfl⟩` from `List.mem_map.1 hx`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hf`. Conclude with `exp_mem_UJ (hX i) (t i)`. Establish `hmemD : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).drop i).map (· t), x ∈ UJset ε` using `fun i t x hx => hmem t x (by rw [List.map_drop] at hx; exact List.mem_of_mem_drop hx)`. Establish `hmemT : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).map (· t)).take i, x ∈ UJset ε` using `fun i t x hx => hmem t x (List.mem_of_mem_take hx)`.

Set `P : (Fin k → ℝ) → Mx n` to `fun t => ((facs Xs).map (· t)).prod`. Establish `hPU : ∀ t, P t ∈ UJset ε` using `fun t => list_prod_mem _ (hmem t)`. Establish `hPc : Continuous P`. Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)`.

Conclude with `(contDiff_listProd _ (contDiff_facs Xs)).continuous`. Set `B : Fin k → (Fin k → ℝ) → Mx n` to `fun i t => (((facs Xs).drop (i + 1)).map (· t)).prod`. Establish `hBU : ∀ i t, B i t ∈ UJset ε` using `fun i t => list_prod_mem _ (hmemD _ t)`. Set `c : Fin k → Fin d → (Fin k → ℝ) → ℝ` to `fun i j t => φ j ((B i t)⁻¹ * Xs i * B i t)`. Establish `hc : ∀ i j, ContDiff ℝ ∞ (c i j)` using `fun i j => contDiff_coef ε (φ j) (Xs i) (B i) (contDiff_listProd _ fun f hf => contDiff_facs Xs f (List.mem_of_mem_drop hf)) (hBU i)`.

Set `F : Fam ε σ → (Fin k → ℝ) → H` to `fun u t => σ (P t) (u.1 [])`. Establish `hd : ∀ (u : Fam ε σ) i t, HasDerivAt (fun s : ℝ => F u (Function.update t i s)) (∑ j, c i j t • F (der σ (b j) u) t) (t i)`. Introduce `u i t`. Establish `hA : (((facs Xs).map (· t)).take i).prod ∈ UJset ε` using `list_prod_mem _ (hmemT _ t)`. Establish `hB` using `hBU i t`.

Set `Y : lie (Jm ε)` to `⟨Xs i, hX i⟩`. Establish `e1 : ∀ s, F u (Function.update t i s) = σ (((facs Xs).map (· t)).take i).prod ((act h (exp_mem_UJ (hX i) s) (act h hB u)).1 [])`. Introduce `s`. Use `show σ (((facs Xs).map (· (Function.update t i s))).prod) (u.1 []) = _`. Rewrite using `[prod_update, sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) s)) hB, sigma_mul hσ hA (exp_mem_UJ (hX i) s)]`.

Both sides reduce to the same expression. Establish `h1` using `((σ (((facs Xs).map (· t)).take i).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t i) (hasDerivAt_act h Y [] (act h hB u) (t i))`. Use `(h1.congr_of_eventuallyEq (Eventually.of_forall e1)).congr_deriv ?_` and prove the remaining obligations. Establish `eP : P t = (((facs Xs).map (· t)).take i).prod * NormedSpace.exp (t i • Xs i) * B i t`. Use `prod_update Xs t i (t i)` as an intermediate fact.

Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis. Use `show σ _ ((act h _ (der σ Y (act h hB u))).1 []) = _`. Rewrite using `[der_act]`. Establish `e2` using `map_der_eq hb 1 (adInv hB Y) u []`. Simplify using `only [ContinuousLinearMap.one_apply] at e2`.

Use `show σ _ (σ (NormedSpace.exp (t i • Xs i)) (σ (B i t) ((der σ (adInv hB Y) u).1 []))) = _`. Rewrite using `[e2, ← sigma_mul hσ hA (exp_mem_UJ (hX i) (t i)), ← sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) (t i))) hB, ← eP, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `(σ (P t)).map_smul_of_tower _ _`. Establish `key : ∀ m : ℕ, ∀ u : Fam ε σ, ContDiff ℝ m (F u)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `u`. Rewrite using `[Nat.cast_zero, contDiff_zero]`.

Conclude with `(hσ.2.2 (u.1 [])).comp_continuous hPc hPU`. Consider the case `succ m ih`. Introduce `u`. Rewrite using `[Nat.cast_succ]`. Conclude with `contDiff_succ_of_partials m (F u) _ (hd u) fun i => ContDiff.sum fun j _ => (contDiff_infty.1 (hc i j) m).smul (ih _)`.

Establish `eF : F ⟨v, hv⟩ = fun t => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (v [])`. Use function extensionality and compare the values at `t`. Simplify using `[F, P, facs, List.map_ofFn, Function.comp_def]`. Rewrite using `[← eF]`. Conclude with `contDiff_infty.2 fun m => key m ⟨v, hv⟩`.
-/
theorem famSmooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ v ∈ GlobalTheory.TypeSum.Fam ε σ, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v []) := by
  intro n ε H _ _ _ σ hσ v hv k Xs hX
  have h := modRep_of_isURepOn hσ
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  have hmem : ∀ t, ∀ x ∈ (facs Xs).map (· t), x ∈ UJset ε := by
    intro t x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
    exact exp_mem_UJ (hX i) (t i)
  have hmemD : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).drop i).map (· t), x ∈ UJset ε := fun i t x hx =>
    hmem t x (by rw [List.map_drop] at hx; exact List.mem_of_mem_drop hx)
  have hmemT : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).map (· t)).take i, x ∈ UJset ε := fun i t x hx =>
    hmem t x (List.mem_of_mem_take hx)
  let P : (Fin k → ℝ) → Mx n := fun t => ((facs Xs).map (· t)).prod
  have hPU : ∀ t, P t ∈ UJset ε := fun t => list_prod_mem _ (hmem t)
  have hPc : Continuous P := by
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    exact (contDiff_listProd _ (contDiff_facs Xs)).continuous
  let B : Fin k → (Fin k → ℝ) → Mx n := fun i t => (((facs Xs).drop (i + 1)).map (· t)).prod
  have hBU : ∀ i t, B i t ∈ UJset ε := fun i t => list_prod_mem _ (hmemD _ t)
  let c : Fin k → Fin d → (Fin k → ℝ) → ℝ := fun i j t => φ j ((B i t)⁻¹ * Xs i * B i t)
  have hc : ∀ i j, ContDiff ℝ ∞ (c i j) := fun i j => contDiff_coef ε (φ j) (Xs i) (B i)
    (contDiff_listProd _ fun f hf => contDiff_facs Xs f (List.mem_of_mem_drop hf)) (hBU i)
  let F : Fam ε σ → (Fin k → ℝ) → H := fun u t => σ (P t) (u.1 [])
  have hd : ∀ (u : Fam ε σ) i t, HasDerivAt (fun s : ℝ => F u (Function.update t i s))
      (∑ j, c i j t • F (der σ (b j) u) t) (t i) := by
    intro u i t
    have hA : (((facs Xs).map (· t)).take i).prod ∈ UJset ε := list_prod_mem _ (hmemT _ t)
    have hB := hBU i t
    let Y : lie (Jm ε) := ⟨Xs i, hX i⟩
    have e1 : ∀ s, F u (Function.update t i s) =
        σ (((facs Xs).map (· t)).take i).prod ((act h (exp_mem_UJ (hX i) s) (act h hB u)).1 []) := by
      intro s
      show σ (((facs Xs).map (· (Function.update t i s))).prod) (u.1 []) = _
      rw [prod_update, sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) s)) hB, sigma_mul hσ hA (exp_mem_UJ (hX i) s)]
      rfl
    have h1 := ((σ (((facs Xs).map (· t)).take i).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t i)
      (hasDerivAt_act h Y [] (act h hB u) (t i))
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall e1)).congr_deriv ?_
    have eP : P t = (((facs Xs).map (· t)).take i).prod * NormedSpace.exp (t i • Xs i) * B i t := by
      have := prod_update Xs t i (t i)
      rwa [Function.update_eq_self] at this
    show σ _ ((act h _ (der σ Y (act h hB u))).1 []) = _
    rw [der_act]
    have e2 := map_der_eq hb 1 (adInv hB Y) u []
    simp only [ContinuousLinearMap.one_apply] at e2
    show σ _ (σ (NormedSpace.exp (t i • Xs i)) (σ (B i t) ((der σ (adInv hB Y) u).1 []))) = _
    rw [e2, ← sigma_mul hσ hA (exp_mem_UJ (hX i) (t i)),
      ← sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) (t i))) hB, ← eP, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (σ (P t)).map_smul_of_tower _ _
  have key : ∀ m : ℕ, ∀ u : Fam ε σ, ContDiff ℝ m (F u) := by
    intro m
    induction m with
    | zero =>
      intro u
      rw [Nat.cast_zero, contDiff_zero]
      exact (hσ.2.2 (u.1 [])).comp_continuous hPc hPU
    | succ m ih =>
      intro u
      rw [Nat.cast_succ]
      exact contDiff_succ_of_partials m (F u) _ (hd u) fun i =>
        ContDiff.sum fun j _ => (contDiff_infty.1 (hc i j) m).smul (ih _)
  have eF : F ⟨v, hv⟩ = fun t => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (v []) := by
    funext t
    simp [F, P, facs, List.map_ofFn, Function.comp_def]
  rw [← eF]
  exact contDiff_infty.2 fun m => key m ⟨v, hv⟩

end Main

end GlobalTheory.FamSmooth
