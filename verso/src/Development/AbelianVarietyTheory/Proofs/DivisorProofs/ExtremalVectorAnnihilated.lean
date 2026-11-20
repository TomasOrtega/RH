import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ExtKill

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]`. Use `_ = 0 := by rw [hX]; simp`.
-/
theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]`. Use `_ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp`.
-/
theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

/- English proof (translation)
Rewrite using `[← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Proceed by induction on `l with`. Consider the case `nil => simp [h2]`. Consider the case `cons a l ih`.

Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, ih]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold `dRep`. Simplify using `only [exp_smul_conj hP]`.
-/
theorem dRep_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [exp_smul_conj hP]

/- English proof (translation)
Introduce `k Xs hXs`. Establish `h` using `hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)`. Establish `e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod`. Introduce `t`. Establish `: (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P`.

Rewrite using `[List.map_ofFn]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `exp_smul_conj_inv hP _ _`. Rewrite using `[this, prod_conj_inv hP, conj_cancel hP]`.

Simplify `h` using `only [e]`.
-/
theorem smoothVec_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

/- English proof (translation)
Introduce `D θ V S M J χ T hθ hT v hv ρ p s hε`. Establish `hP` using `M.fr_unit ρ`. Establish `hG` using `M.fr_gram ρ`. Take `⟨-, hlow, hwt⟩` from `hv ρ`. Establish `hlow' : (v ρ : M.H ρ) ∈ lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ)` using `hlow`.

Use `⟨fun a b hab => ?_, fun t g => ?_⟩` and prove the remaining obligations. Take `⟨hs, hd⟩` from `GlobalTheory.T.right_derivative_multiplicity_map_value_eq D θ V S M J χ T hθ hT v ρ`. Establish `hs'` using `smoothVec_conj (σ := M.σ ρ) hP hG hs`. Use `set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ`. Take `⟨hX, hY⟩` from `GlobalTheory.SmoothAutCheck.parts_mem V ρ Z`.

Establish `hXY` using `GlobalTheory.SmoothAutCheck.parts_sum V ρ Z`. Unfold `RderC`. Generalize the expression as in `(1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢`. Generalize the expression as in `(1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢`. Take `⟨u, hu, eu⟩` from `hd X hX`.

Take `⟨u', hu', eu'⟩` from `hd Y hY`. Establish `hX'` using `lie_conj hP hG hX`. Establish `hY'` using `lie_conj hP hG hY`. Establish `hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) = Matrix.single a b 1`. Rewrite using `[← conj_cancel hP (Matrix.single a b 1), ← hZ, ← hXY]`.

Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) + Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0`. Break down `hab with h | h | h` into its components or cases. Conclude with `GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE`. Conclude with `GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE`.

Conclude with `GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p s hε (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE`. Establish `h0 : u + Complex.I • u' = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (u : M.H ρ) + Complex.I • (u' : M.H ρ) = 0`. Rewrite using `[hu, hu', ← key, ← dRep_conj hP, ← dRep_conj hP]`.

Both sides reduce to the same expression. Rewrite using `[eu, eu', ← T.map_update_smul, ← T.map_update_add, h0, T.map_update_zero]`. Establish `hK` using `Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) t`. Establish `hg` using `GlobalTheory.HolDict.ModelRep.conj_mem_inv hP hG (kset_uj hK)`. Establish `h` using `hT.equiv ρ _ hg v (Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) • v ρ) (by`.

Unfold `DSModel.rep`. Rewrite using `[conj_cancel hP, hwt t hK]`. Use the proof step `rfl)`. Rewrite `h` using `[T.map_update_smul, Function.update_eq_self]`. Conclude with `(congrFun h g).symm`.
-/
theorem kill_and_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ v : M.Vec, IsExtVec M v → ∀ (ρ : D.what₂.Tau) (p : ℕ) (s : Bool), (∀ a : Fin V.rank, M.ε ρ a = if (a : ℕ) < p then s else !s) → (∀ a b, KillPair (M.ε ρ) a b → RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧ ∀ (t : Fin V.rank → ℝ) (g : GA D V), T v (g * atTau θ V ρ ((M.fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I)) * M.fr ρ)) = Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) * T v g := by
  intro D θ V S M J χ T hθ hT v hv ρ p s hε
  have hP := M.fr_unit ρ
  have hG := M.fr_gram ρ
  obtain ⟨-, hlow, hwt⟩ := hv ρ
  have hlow' : (v ρ : M.H ρ) ∈ lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
  refine ⟨fun a b hab => ?_, fun t g => ?_⟩
  · obtain ⟨hs, hd⟩ := GlobalTheory.T.right_derivative_multiplicity_map_value_eq D θ V S M J χ T hθ hT v ρ
    have hs' := smoothVec_conj (σ := M.σ ρ) hP hG hs
    set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
    obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
    have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
    unfold RderC
    generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
    obtain ⟨u, hu, eu⟩ := hd X hX
    obtain ⟨u', hu', eu'⟩ := hd Y hY
    have hX' := lie_conj hP hG hX
    have hY' := lie_conj hP hG hY
    have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) = Matrix.single a b 1 := by
      rw [← conj_cancel hP (Matrix.single a b 1), ← hZ, ← hXY]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
        Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
      rcases hab with h | h | h
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
      · exact GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p s hε (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
    have h0 : u + Complex.I • u' = 0 := by
      apply Subtype.ext
      show (u : M.H ρ) + Complex.I • (u' : M.H ρ) = 0
      rw [hu, hu', ← key, ← dRep_conj hP, ← dRep_conj hP]
      rfl
    rw [eu, eu', ← T.map_update_smul, ← T.map_update_add, h0, T.map_update_zero]
  · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) t
    have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hP hG (kset_uj hK)
    have h := hT.equiv ρ _ hg v (Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) • v ρ) (by
      unfold DSModel.rep
      rw [conj_cancel hP, hwt t hK]
      rfl)
    rw [T.map_update_smul, Function.update_eq_self] at h
    exact (congrFun h g).symm

end GlobalTheory.HolRead.ExtKill
