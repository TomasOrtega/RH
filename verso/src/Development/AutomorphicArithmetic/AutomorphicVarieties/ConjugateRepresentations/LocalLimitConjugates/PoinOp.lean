import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeLim

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

/- English proof (translation)
Establish `hδ : δ = γ⁻¹` using `eq_inv_of_mul_eq_one_right h`. Substitute `hδ` using the available equality. Use extensionality with `v`. Rewrite using `[Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]`. Establish `hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v`.

Use function extensionality and compare the values at `i`. Conclude with `Geo.ρ_inv_apply G γ⁻¹ (v i)`. Rewrite using `[hv]`.
-/
private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

/- English proof (translation)
Set `L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ))` to `ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹) (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m) (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)`. Establish `hL : ∀ m, L m = G.tr q γ m` using `fun m => rfl`. Establish `key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)), L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t)`. Introduce `f`. Simplify using `only [intervalIntegral, map_sub, L.integral_comp_comm]`.

Establish `hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p)`. Introduce `t`. Simplify using `[map_add, map_smul, map_sub, Geo.ρ_inv_apply]`. Rewrite using `[← hL]`. Unfold `coneOp`.

Rewrite using `[key]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[map_smul]`. Use `beta_reduce`.

Rewrite using `[hpt]`. Use `congr 1`. Use extensionality with `v`. Rewrite using `[hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify using `[Geo.ρ_inv_apply]`. Introduce `j`. Simplify using the standard rewrite rules.
-/
private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add, map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hconv q`. Establish `hD` using `coneD V (Fin d → ℂ) G.Y G.isOpen hconv`. Set `f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)` to `fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0`. Establish `hwm : ∀ (w : G.Om (q + 1)) (s : S), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧ ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0` using `fun w => w.2`. Establish `hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q`.

Introduce `p hp w`. Use `fun s => ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)`. Introduce `x hx`. Conclude with `if_neg hx`.

Set `K : V → G.Om (q + 1) → G.Om q` to `fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0`. Establish `hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w`. Introduce `p hp w`. Simplify using `[K, hp]`. Use `⟨K, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `p hp w hw0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s x`. Distinguish the cases in `hx : x ∈ G.Y`. Rewrite using `[Geo.dOm_apply G (K p w) s hx, hK p hp w]`.

Establish `hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0`. Introduce `y hy`. Establish `h0` using `congrArg (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0`. Rewrite `h0` using `[Geo.dOm_apply G w s hy]`. Simplify using `using h0`.

Establish `hloc : extDeriv (f p w s) x = extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x`. Rewrite using `[← extDerivWithin_univ, ← extDerivWithin_univ]`. Apply `Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)` to reduce the goal to its premises. Rewrite using `[nhdsWithin_univ]`. Conclude with `Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)`.

Rewrite using `[hloc]`. Conclude with `(hD p hp q _ (hwm w s).1).2 hclosed x hx`. Establish `h1` using `((G.dOm q (K p w)).2 s).2 x hx`. Establish `h2` using `(hwm w s).2 x hx`. Rewrite using `[h1, h2]`.

Introduce `γ p hp w`. Establish `hp' : G.ρ γ p ∈ G.Y` using `G.maps γ p hp`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s x`. Use `show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) = ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x`.

Rewrite using `[hK p hp, hK _ hp']`. Distinguish the cases in `hx : x ∈ G.Y`. Establish `hx' : G.ρ γ⁻¹ x ∈ G.Y` using `G.maps γ⁻¹ x hx`. Simplify using `only [f, if_pos hx, if_pos hx']`. Conclude with `tr_coneOp G q γ _ p x`.

Establish `hx' : G.ρ γ⁻¹ x ∉ G.Y`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `h2` using `G.maps γ _ h`. Establish `h3` using `Geo.ρ_inv_apply G γ⁻¹ x`.

Rewrite `h3` using `[inv_inv]`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Simplify using `only [f, if_neg hx, if_neg hx', map_zero]`. Introduce `p hp w hw s C hC hCc`. Establish `h` using `coneLim V (Fin d → ℂ) G.Y hconv p hp q (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc`.

Use `h.congr ?_` and prove the remaining obligations. Use `filter_upwards with k`. Introduce `x hx`. Rewrite using `[hK p hp]`. Simplify using `[f, hC hx]`.
-/
theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
