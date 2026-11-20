import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hK : ∀ x : S.topologicalClosure, ∃ w, R (x : H) w ∧ ‖w‖ ≤ C * ‖(x : H)‖` using `fun x => hex x x.2`. Use `choose l hl hb using hK`. Establish `hl0 : l 0 = 0`. Use `hb 0` as an intermediate fact. Simplify using `using this`.

Set `L₀ : S.topologicalClosure →ₗ[ℂ] V` to `{ toFun := l map_add' := fun x y => by`. Use `hlin 1 x y (l x) (l y) (hl x) (hl y)` as an intermediate fact. Conclude with `huniq _ _ _ (hl (x + y)) (by simpa using this)`. Use the proof step `map_smul' := fun a x => by`. Use `hlin a x 0 (l x) (l 0) (hl x) (hl 0)` as an intermediate fact.

Conclude with `huniq _ _ _ (hl (a • x)) (by simpa [hl0] using this) }`. Set `L : S.topologicalClosure →L[ℂ] V` to `L₀.mkContinuous C (fun x => hb x)`. Use `⟨(ContinuousLinearMap.adjoint L v : S.topologicalClosure), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(ContinuousLinearMap.adjoint L v).2`. Introduce `x hx w hw`.

Establish `hxk : x ∈ S.topologicalClosure` using `S.le_topologicalClosure hx`. Establish `hw' : w = l ⟨x, hxk⟩` using `huniq x w _ hw (hl ⟨x, hxk⟩)`. Use `ContinuousLinearMap.adjoint_inner_left L (⟨x, hxk⟩ : S.topologicalClosure) v` as an intermediate fact. Rewrite using `[hw']`. Conclude with `this`.
-/
theorem riesz_of_relation {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (S : Submodule ℂ H) (R : H → V → Prop) (C : ℝ)
    (hex : ∀ x ∈ closure (S : Set H), ∃ w, R x w ∧ ‖w‖ ≤ C * ‖x‖)
    (huniq : ∀ x w w', R x w → R x w' → w = w')
    (hlin : ∀ (a : ℂ) x y w w', R x w → R y w' → R (a • x + y) (a • w + w')) (v : V) :
    ∃ κ ∈ closure (S : Set H), ∀ x ∈ S, ∀ w, R x w → ⟪κ, x⟫_ℂ = ⟪v, w⟫_ℂ := by
  classical
  have hK : ∀ x : S.topologicalClosure, ∃ w, R (x : H) w ∧ ‖w‖ ≤ C * ‖(x : H)‖ := fun x =>
    hex x x.2
  choose l hl hb using hK
  have hl0 : l 0 = 0 := by
    have := hb 0
    simpa using this
  let L₀ : S.topologicalClosure →ₗ[ℂ] V :=
    { toFun := l
      map_add' := fun x y => by
        have := hlin 1 x y (l x) (l y) (hl x) (hl y)
        exact huniq _ _ _ (hl (x + y)) (by simpa using this)
      map_smul' := fun a x => by
        have := hlin a x 0 (l x) (l 0) (hl x) (hl 0)
        exact huniq _ _ _ (hl (a • x)) (by simpa [hl0] using this) }
  let L : S.topologicalClosure →L[ℂ] V := L₀.mkContinuous C (fun x => hb x)
  refine ⟨(ContinuousLinearMap.adjoint L v : S.topologicalClosure), ?_, ?_⟩
  · exact (ContinuousLinearMap.adjoint L v).2
  · intro x hx w hw
    have hxk : x ∈ S.topologicalClosure := S.le_topologicalClosure hx
    have hw' : w = l ⟨x, hxk⟩ := huniq x w _ hw (hl ⟨x, hxk⟩)
    have := ContinuousLinearMap.adjoint_inner_left L (⟨x, hxk⟩ : S.topologicalClosure) v
    rw [hw']
    exact this

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Use function extensionality and compare the values at `g`. Simplify using `[Rw, ih, Rd]`.
-/
theorem Rw_zero {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp [Rw, ih, Rd]

/- English proof (translation)
Use `⟨contDiffOn_const, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Rw_zero]`. Conclude with `MemLp.zero`.
-/
theorem sob_zero {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Sob μ (0 : Mat n → V) := by
  refine ⟨contDiffOn_const, fun w => ?_⟩
  rw [Rw_zero]
  exact MemLp.zero

/- English proof (translation)
Introduce `n _ _ μ _ E _ Ω T F c hS h hh v`. Take `⟨hLg, hUn, hRC, hSob, hAlg, hWS, hWC, hCS, hSm, hPW, hM, hsym, hres, hinv, hOm, hbd⟩` from `hS`. Take `⟨C, hC⟩` from `hSm n μ E Ω T F hLg hUn hRC hSob hAlg hCS hOm h hh`. Take `⟨-, -, -, -, hCl, hOps, -⟩` from `hCS`. Take `⟨hc1, hc2, -⟩` from `hCl n μ E.V hUn`.

Establish `hmem : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ` using `fun hf => hf.2 []`. Establish `hsum : ∀ (a : ℂ) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → Sob μ (a • f + f')` using `fun a f f' hf hf' => ((hOps n μ E.V hLg hUn hRC f hf).2.2.2.1 a f' hf').1`. Establish `hsec : ∀ (a : ℂ) (f f' : Mat n → E.V), IsSec E f → IsSec E f' → IsSec E (a • f + f')`. Introduce `a f f' hf hf' g hg k`. Simplify using `[hf g hg k, hf' g hg k]`.

Establish `h0 : cls μ (0 : Mat n → E.V) = 0`. Simplify using `using hc2 (-1) 0 0 (hmem (sob_zero μ E.V)) (hmem (sob_zero μ E.V))`. Set `S : Submodule ℂ (Lp E.V 2 μ)` to `{ carrier := secCls μ E zero_mem' := ⟨0, sob_zero μ E.V, fun g _ k => by simp, h0⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨f, hf, hs, rfl⟩ ⟨f', hf', hs', rfl⟩`. Conclude with `⟨1 • f + f', hsum 1 f f' hf hf', hsec 1 f f' hs hs', by`.

Simplify using `using hc2 1 f f' (hmem hf) (hmem hf')⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a _ ⟨f, hf, hs, rfl⟩`. Use `⟨a • f + 0, hsum a f 0 hf (sob_zero μ E.V), hsec a f 0 hs (fun g _ k => by simp), ?_⟩` and prove the remaining obligations. Use `hc2 a f 0 (hmem hf) (hmem (sob_zero μ E.V))` as an intermediate fact.

Simplify `this }` using `[h0]`. Set `R : Lp E.V 2 μ → E.V → Prop` to `fun x w => ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h x ∧ f' 1 = w`. Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Take `⟨κ, hκ, hrep⟩` from `riesz_of_relation S R C (fun x hx => by`. Take `⟨f', a, b, d, e⟩` from `hC x hx`.

Conclude with `⟨f' 1, ⟨f', a, b, d, rfl⟩, e⟩)`. Use the proof step `(by`. Introduce and unpack `x _ _ ⟨f, hf, -, hcf, rfl⟩ ⟨f', hf', -, hcf', rfl⟩`. Conclude with `hc1 f f' hf.1.continuousOn hf'.1.continuousOn (hmem hf) (hmem hf') (hcf.trans hcf'.symm) 1 h1)`. Use the proof step `(by`.

Introduce and unpack `a x y _ _ ⟨f, hf, hs, hcf, rfl⟩ ⟨f', hf', hs', hcf', rfl⟩`. Use `⟨a • f + f', hsum a f f' hf hf', hsec a f f' hs hs', ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hc2 a f f' (hmem hf) (hmem hf'), hcf, hcf', map_add, map_smul]) v`. Use `⟨κ, hκ, fun φ f' hφ hφs hf' hf's hcl => ?_⟩` and prove the remaining obligations. Conclude with `hrep (cls μ φ) ⟨φ, hφ, hφs, rfl⟩ (f' 1) ⟨f', hf', hf's, hcl, rfl⟩`.
-/
theorem evAdj : EvAdj := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  obtain ⟨hLg, hUn, hRC, hSob, hAlg, hWS, hWC, hCS, hSm, hPW, hM, hsym, hres, hinv, hOm, hbd⟩ := hS
  obtain ⟨C, hC⟩ := hSm n μ E Ω T F hLg hUn hRC hSob hAlg hCS hOm h hh
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  obtain ⟨hc1, hc2, -⟩ := hCl n μ E.V hUn
  have hmem : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  have hsum : ∀ (a : ℂ) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → Sob μ (a • f + f') := fun a f f' hf hf' =>
    ((hOps n μ E.V hLg hUn hRC f hf).2.2.2.1 a f' hf').1
  have hsec : ∀ (a : ℂ) (f f' : Mat n → E.V), IsSec E f → IsSec E f' → IsSec E (a • f + f') := by
    intro a f f' hf hf' g hg k
    simp [hf g hg k, hf' g hg k]
  have h0 : cls μ (0 : Mat n → E.V) = 0 := by
    simpa using hc2 (-1) 0 0 (hmem (sob_zero μ E.V)) (hmem (sob_zero μ E.V))
  let S : Submodule ℂ (Lp E.V 2 μ) :=
    { carrier := secCls μ E
      zero_mem' := ⟨0, sob_zero μ E.V, fun g _ k => by simp, h0⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, hs, rfl⟩ ⟨f', hf', hs', rfl⟩
        exact ⟨1 • f + f', hsum 1 f f' hf hf', hsec 1 f f' hs hs', by
          simpa using hc2 1 f f' (hmem hf) (hmem hf')⟩
      smul_mem' := by
        rintro a _ ⟨f, hf, hs, rfl⟩
        refine ⟨a • f + 0, hsum a f 0 hf (sob_zero μ E.V), hsec a f 0 hs (fun g _ k => by simp), ?_⟩
        have := hc2 a f 0 (hmem hf) (hmem (sob_zero μ E.V))
        simpa [h0] using this }
  let R : Lp E.V 2 μ → E.V → Prop := fun x w =>
    ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h x ∧ f' 1 = w
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  obtain ⟨κ, hκ, hrep⟩ := riesz_of_relation S R C
    (fun x hx => by
      obtain ⟨f', a, b, d, e⟩ := hC x hx
      exact ⟨f' 1, ⟨f', a, b, d, rfl⟩, e⟩)
    (by
      rintro x _ _ ⟨f, hf, -, hcf, rfl⟩ ⟨f', hf', -, hcf', rfl⟩
      exact hc1 f f' hf.1.continuousOn hf'.1.continuousOn (hmem hf) (hmem hf') (hcf.trans hcf'.symm) 1 h1)
    (by
      rintro a x y _ _ ⟨f, hf, hs, hcf, rfl⟩ ⟨f', hf', hs', hcf', rfl⟩
      refine ⟨a • f + f', hsum a f f' hf hf', hsec a f f' hs hs', ?_, rfl⟩
      rw [hc2 a f f' (hmem hf) (hmem hf'), hcf, hcf', map_add, map_smul]) v
  refine ⟨κ, hκ, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  exact hrep (cls μ φ) ⟨φ, hφ, hφs, rfl⟩ (f' 1) ⟨f', hf', hf's, hcl, rfl⟩

end GlobalTheory.CompanionTheory.KerFc
