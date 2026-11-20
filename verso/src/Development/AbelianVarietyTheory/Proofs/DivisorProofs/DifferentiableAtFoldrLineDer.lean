import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThK.RealLineGrowthDerivative
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

/- English proof (translation)
Establish `key : ∀ c : E, c ≠ 0 → ∀ g : GL (Fin n) (R ⊗[F] E), g ∈ HR R σ (c • M) ↔ g ∈ HR R σ M`. Introduce `c hc g`. Establish `hu : IsUnit (inclR (F` using `F) R c) := (IsUnit.mk0 c hc).map _`. Establish `e : JR (F` using `F) R (c • M) = inclR (F := F) R c • JR (F := F) R M := Matrix.ext fun i j => map_mul (inclR (F := F) R) c (M i j)`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _ ↔ Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _`.

Rewrite using `[e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]`. Use extensionality with `g`. Rewrite using `[key c₀ h₀, key c₁ h₁]`.
-/
theorem hr_smul_eq (R : Type) [CommRing R] [Algebra F R] (M : Matrix (Fin n) (Fin n) E) {c₀ c₁ : E} (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    HR R σ (c₀ • M) = HR R σ (c₁ • M) := by
  have key : ∀ c : E, c ≠ 0 → ∀ g : GL (Fin n) (R ⊗[F] E), g ∈ HR R σ (c • M) ↔ g ∈ HR R σ M := by
    intro c hc g
    have hu : IsUnit (inclR (F := F) R c) := (IsUnit.mk0 c hc).map _
    have e : JR (F := F) R (c • M) = inclR (F := F) R c • JR (F := F) R M :=
      Matrix.ext fun i j => map_mul (inclR (F := F) R) c (M i j)
    change Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _ ↔ Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _
    rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]
  ext g
  rw [key c₀ h₀, key c₁ h₁]

/- English proof (translation)
Take `⟨w, τ, Z, hZ, hy⟩` from `hγ`. Establish `hmap : ∀ c : E, (c • J.map σ).map τ.1 = τ.1 c • (J.map σ).map τ.1` using `fun c => Matrix.ext fun i j => map_mul τ.1 c _`. Establish `hZ' : Zᴴ * (J.map σ).map τ.1 + (J.map σ).map τ.1 * Z = 0`. Rewrite `hZ` using `[hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]`. Conclude with `(smul_eq_zero.1 hZ).resolve_left ((map_ne_zero τ.1).2 h₀)`.

Use `⟨w, τ, Z, by rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hZ', smul_zero], fun t => ?_⟩` and prove the remaining obligations. Take `⟨y, e1, e2⟩` from `hy t`. Use `⟨⟨y.1, (SetLike.ext_iff.1 (hr_smul_eq _ (J.map σ) h₀ h₁) y.1).1 y.2⟩, ?_, e2⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((toGAd hσ J h₀).symm (γ t)).1 = _`.

Rewrite using `[e1]`. Both sides reduce to the same expression.
-/
theorem isRealLine_move (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) {c₀ c₁ : E} (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)
    {γ : ℝ → GAd σ (c₀ • J.map σ)} (hγ : IsRealLine σ (c₀ • J.map σ) γ) :
    IsRealLine σ (c₁ • J.map σ) (fun t => toGAd hσ J h₁ ((toGAd hσ J h₀).symm (γ t))) := by
  obtain ⟨w, τ, Z, hZ, hy⟩ := hγ
  have hmap : ∀ c : E, (c • J.map σ).map τ.1 = τ.1 c • (J.map σ).map τ.1 := fun c =>
    Matrix.ext fun i j => map_mul τ.1 c _
  have hZ' : Zᴴ * (J.map σ).map τ.1 + (J.map σ).map τ.1 * Z = 0 := by
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hZ
    exact (smul_eq_zero.1 hZ).resolve_left ((map_ne_zero τ.1).2 h₀)
  refine ⟨w, τ, Z, by rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hZ', smul_zero], fun t => ?_⟩
  obtain ⟨y, e1, e2⟩ := hy t
  refine ⟨⟨y.1, (SetLike.ext_iff.1 (hr_smul_eq _ (J.map σ) h₀ h₁) y.1).1 y.2⟩, ?_, e2⟩
  apply Subtype.ext
  show ((toGAd hσ J h₀).symm (γ t)).1 = _
  rw [e1]
  rfl

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons γ l ih`. Use function extensionality and compare the values at `x`.

Simplify using `only [List.foldr_cons, List.map_cons, ih, lineDer, map_mul]`.
-/
theorem foldr_lineDer_comp {K₀ K₁ : Matrix (Fin n) (Fin n) E} (e : GAd σ K₀ ≃* GAd σ K₁) (f : GAd σ K₁ → ℂ) :
    ∀ l : List (ℝ → GAd σ K₀), l.foldr lineDer (fun x => f (e x)) =
      fun x => (l.map fun γ t => e (γ t)).foldr lineDer f (e x) := by
  intro l
  induction l with
  | nil => rfl
  | cons γ l ih =>
    funext x
    simp only [List.foldr_cons, List.map_cons, ih, lineDer, map_mul]

variable {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Rewrite using `[List.ofFn_succ', List.concat_eq_append, List.prod_append]`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last]`.
-/
theorem prod_ofFn_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/- English proof (translation)
Set `v : Fin (m + 1) → ℝ` to `Pi.single (Fin.last m) 1`. Set `L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)` to `ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i`. Establish `hL : ∀ s t, Fin.snoc (α` using `fun _ => ℝ) s t = L s + t • v := fun s t => by`. Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `[L, v]`. Simplify using `[L, v, Fin.castSucc_ne_last]`. Establish `hd : ∀ s, deriv (fun t => H (Fin.snoc (α` using `fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by`. Simplify using `only [hL]`. Establish `h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0`.

Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)`. Establish `h2` using `(hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)`. Rewrite `h2` using `[zero_smul, add_zero]`. Establish `h3` using `h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)`. Conclude with `h3.deriv`.

Simplify using `only [hd]`. Conclude with `((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const`.
-/
theorem contDiff_partial_last {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun s : Fin m → ℝ => deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 := by
  let v : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  let L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i
  have hL : ∀ s t, Fin.snoc (α := fun _ => ℝ) s t = L s + t • v := fun s t => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, v]
    · simp [L, v, Fin.castSucc_ne_last]
  have hd : ∀ s, deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by
    simp only [hL]
    have h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)
    have h2 := (hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)
    rw [zero_smul, add_zero] at h2
    have h3 := h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h3.deriv
  simp only [hd]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _ m δ hδ x`. Conclude with `hf m δ hδ x`. Consider the case `cons γ l ih`.

Introduce `hl m δ hδ x`. Establish `hl' : ∀ γ' ∈ l, IsRealLine σ J γ'` using `fun γ' h => hl γ' (List.mem_cons_of_mem _ h)`. Establish `hγ : IsRealLine σ J γ` using `hl γ List.mem_cons_self`. Establish `hH` using `ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ) (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x`. Use `contDiff_partial_last hH` as an intermediate fact.

Simplify using `only [prod_ofFn_snoc, ← mul_assoc] at this`. Simplify `this` using `only [List.foldr_cons, lineDer]`.
-/
theorem contDiff_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ (m : ℕ) (δ : Fin m → ℝ → GAd σ J),
      (∀ i, IsRealLine σ J (δ i)) → ∀ x,
      ContDiff ℝ ∞ fun s : Fin m → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => δ i (s i)).prod) := by
  intro l
  induction l with
  | nil => intro _ m δ hδ x; exact hf m δ hδ x
  | cons γ l ih =>
    intro hl m δ hδ x
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    have hH := ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ)
      (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x
    have := contDiff_partial_last hH
    simp only [prod_ofFn_snoc, ← mul_assoc] at this
    simpa only [List.foldr_cons, lineDer] using this

/- English proof (translation)
Establish `h` using `(contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)`. Establish `h'` using `(h.differentiable (by simp)) 0`. Establish `e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t)`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h'`.
-/
theorem differentiableAt_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (x : GAd σ J) :
    DifferentiableAt ℝ (fun t => l.foldr lineDer f (x * γ t)) 0 := by
  have h := (contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

/- English proof (translation)
Introduce `l hl`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons γ l ih`. Establish `hl' : ∀ γ' ∈ l, IsRealLine σ J γ'` using `fun γ' h => hl γ' (List.mem_cons_of_mem _ h)`.

Establish `hγ : IsRealLine σ J γ` using `hl γ List.mem_cons_self`. Use function extensionality and compare the values at `x`. Simplify using `only [List.foldr_cons, ih hl', lineDer]`. Establish `d1` using `differentiableAt_foldr_lineDer hf₁ l hl' hγ x`. Establish `d2` using `differentiableAt_foldr_lineDer hf₂ l hl' hγ x`.

Conclude with `(d1.hasDerivAt.sub (d2.hasDerivAt.const_mul c)).deriv`.
-/
theorem foldr_lineDer_sub {f₁ f₂ : GAd σ J → ℂ} (hf₁ : GlobalTheory.UAut.IsSm σ J f₁) (hf₂ : GlobalTheory.UAut.IsSm σ J f₂) (c : ℂ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (fun x => f₁ x - c * f₂ x) = fun x => l.foldr lineDer f₁ x - c * l.foldr lineDer f₂ x := by
  intro l hl
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    funext x
    simp only [List.foldr_cons, ih hl', lineDer]
    have d1 := differentiableAt_foldr_lineDer hf₁ l hl' hγ x
    have d2 := differentiableAt_foldr_lineDer hf₂ l hl' hγ x
    exact (d1.hasDerivAt.sub (d2.hasDerivAt.const_mul c)).deriv

end GlobalTheory.ThK.RealLineGrowthDerivative

end
