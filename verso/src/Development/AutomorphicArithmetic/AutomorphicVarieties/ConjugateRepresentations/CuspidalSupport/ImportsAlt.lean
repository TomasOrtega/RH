import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Introduce `hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀`. Take `⟨φ, hφ, hne⟩` from `hIwa E r s φ₀ m B h₀ hne₀`. Take `⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩` from `hSlice E r s φ hφ.aut`. Take `⟨ψ, hψ, hNI, hcap⟩` from `hCtCap E (r + s) r φ hφ.aut`. Rewrite `hne`, `hs₁`, `hs₂` using `[← hψ]`.

Establish `hψ0 : ψ ≠ 0`. Introduce and unpack `rfl`. Take `⟨x, y, h⟩` from `hne`. Conclude with `h rfl`. Take `⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩` from `hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂`.

Use `⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩` and prove the remaining obligations. Use `hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_` and prove the remaining obligations. Establish `e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2` using `by push_cast; ring`. Establish `e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2` using `by push_cast; ring`. Rewrite using `[e1, e2]`.

Use `hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_` and prove the remaining obligations. Rewrite using `[hcap t u, (hφ.cap t).2 u, hψ]`. Simplify using `only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `MeasureTheory.integral_const_mul _ _`. Use `filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃`.

Establish `hv` using `hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw`. Take `⟨ϖ, hu⟩` from `exists_isUnifV w`. Use `hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_` and prove the remaining obligations. Take `⟨G, hG, hsum⟩` from `hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj`. Use `hw₃ ϖ hu _ G _ hG fun x y => ?_` and prove the remaining obligations.

Rewrite using `[hsum x y]`. Establish `: tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ` using `hv.2.2.2 ϖ hu j hj`. Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite using `[hν.2.1 w]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hν'.2.1 w]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
