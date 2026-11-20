import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactModel

/- English proof (translation)
Establish `hJ : Formalism.REAL.Jm (allPos k) = 1`. Simplify using `[Formalism.REAL.Jm, allPos]`. Establish `h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)` using `hg`. Rewrite `h` using `[hJ, Matrix.mul_one]`. Use `⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩` and prove the remaining obligations.

Rewrite using `[hJ, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem mem_Kset_of_mem_UJset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g ∈ Formalism.REAL.Kset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rw [hJ, Matrix.mul_one] at h
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩
  rw [hJ, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Establish `hd : IsUnit g.det` using `(Matrix.isUnit_iff_isUnit_det g).1 hg`. Proceed by induction on `l with`. Consider the case `nil => simp [Matrix.nonsing_inv_mul _ hd]`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, ih]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hd]`.
-/
theorem list_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : (l.map fun x => g⁻¹ * x * g).prod = g⁻¹ * l.prod * g := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp [Matrix.nonsing_inv_mul _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, -, -⟩` from `hσ`. Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `hJ : IsUnit (Formalism.REAL.Jm ε)` using `IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)`. Establish `hG : IsUnit G`. Rewrite using `[← h]`.

Conclude with `(((Matrix.isUnit_conjTranspose _).2 hP).mul hJ).mul hP`. Establish `hu' : uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε` using `hu`. Establish `huu : IsUnit u`. Establish `: IsUnit (uᴴ * Formalism.REAL.Jm ε * u)` using `by rw [hu']; exact hJ`. Rewrite `this` using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_mul]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det u).2 (isUnit_of_mul_isUnit_right this)`. Use `set g : Matrix (Fin n) (Fin n) ℂ := P⁻¹ * u * P with hgdef`. Establish `hPi : IsUnit P⁻¹` using `Matrix.isUnit_nonsing_inv_iff.2 hP`. Establish `hg : IsUnit g` using `(hPi.mul huu).mul hP`. Establish `hgd : IsUnit g.det` using `(Matrix.isUnit_iff_isUnit_det g).1 hg`.

Establish `hPg : P * g = u * P`. Rewrite using `[hgdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]`. Establish `hug : u = P * g * P⁻¹`. Rewrite using `[hPg, Matrix.mul_nonsing_inv_cancel_right _ _ hd]`. Establish `hgG : gᴴ * G * g = G`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Pᴴ * (uᴴ * Formalism.REAL.Jm ε * u) * P := by`. Rewrite using `[hPg]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = G := by rw [hu', h]`. Use `clear_value g`. Introduce `k Xs hX`. Establish `hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0`.

Introduce `i`. Establish `hXi : (Xs i)ᴴ * G + G * Xs i = 0` using `hX i`. Establish `e1 : G * g⁻¹ = gᴴ * G` using `by conv_lhs => rw [← hgG]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ hgd]`. Establish `e2 : (g⁻¹)ᴴ * G = G * g` using `by conv_lhs => rw [← hgG]`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hgd]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by`.

Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hXi]; simp`. Establish `hs` using `hw k (fun i => g⁻¹ * Xs i * g) hY`. Establish `hs2` using `((σ u).restrictScalars ℝ).contDiff.comp hs`.

Use `hs2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Establish `hmem : ∀ Zs : Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, (Zs i)ᴴ * G + G * Zs i = 0) → P * (List.ofFn fun i => NormedSpace.exp (t i • Zs i)).prod * P⁻¹ ∈ UJset ε` using `fun Zs hZ => by`. Use `GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun a ha => ?_)` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 ha`.

Conclude with `GlobalTheory.GardingVec.exp_mem hG (hZ i) _`. Establish `e3 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod = g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g`. Rewrite using `[← list_prod_conj hg, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Rewrite using `[Function.comp_apply, ← Matrix.exp_conj' _ _ hg]`. Simplify using the standard rewrite rules. Establish `a` using `hmul _ (hmem Xs hX) _ hu`. Establish `b` using `hmul _ hu _ (hmem _ hY)`. Establish `e4 : P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ * u = u * (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹)`.

Rewrite using `[e3, hug]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hgd]`. Rewrite `a` using `[e4, b]`. Conclude with `(congrArg (fun f => f w) a).symm`.
-/
theorem smoothVec_stable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ UJset ε) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ u w) := by
  obtain ⟨⟨h1, hmul⟩, -, -⟩ := hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : IsUnit (Formalism.REAL.Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul hJ).mul hP
  have hu' : uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε := hu
  have huu : IsUnit u := by
    have : IsUnit (uᴴ * Formalism.REAL.Jm ε * u) := by rw [hu']; exact hJ
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det u).2 (isUnit_of_mul_isUnit_right this)
  set g : Matrix (Fin n) (Fin n) ℂ := P⁻¹ * u * P with hgdef
  have hPi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hP
  have hg : IsUnit g := (hPi.mul huu).mul hP
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hPg : P * g = u * P := by
    rw [hgdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hug : u = P * g * P⁻¹ := by
    rw [hPg, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (uᴴ * Formalism.REAL.Jm ε * u) * P := by
          rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hu', h]
  clear_value g
  intro k Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := by
    intro i
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    have e1 : G * g⁻¹ = gᴴ * G := by
      conv_lhs => rw [← hgG]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    have e2 : (g⁻¹)ᴴ * G = G * g := by
      conv_lhs => rw [← hgG]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hgd]
      simp
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hw k (fun i => g⁻¹ * Xs i * g) hY
  have hs2 := ((σ u).restrictScalars ℝ).contDiff.comp hs
  convert hs2 using 1
  funext t
  have hmem : ∀ Zs : Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, (Zs i)ᴴ * G + G * Zs i = 0) →
      P * (List.ofFn fun i => NormedSpace.exp (t i • Zs i)).prod * P⁻¹ ∈ UJset ε := fun Zs hZ => by
    refine GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun a ha => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact GlobalTheory.GardingVec.exp_mem hG (hZ i) _
  have e3 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← list_prod_conj hg, List.map_ofFn]
    congr 2
    funext i
    rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hg]
    simp
  have a := hmul _ (hmem Xs hX) _ hu
  have b := hmul _ hu _ (hmem _ hY)
  have e4 : P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ * u
      = u * (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) := by
    rw [e3, hug]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv_cancel_left _ _ hgd]
  rw [e4, b] at a
  exact (congrArg (fun f => f w) a).symm

/- English proof (translation)
Introduce `D V S M τ hε`. Take `⟨-, -, hrep, hirr, -, ⟨T, hT⟩, -⟩` from `M.ds τ`. Establish `hT'` using `hT`. Rewrite `hT'` using `[hε]`. Establish `hTtop : T = ⊤`.

Take `⟨hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩` from `hT'`. Use `(hirr T T.closed_of_finiteDimensional fun g hg => hst g ?_).resolve_left ?_` and prove the remaining obligations. Rewrite `hg` using `[hε]`. Conclude with `mem_Kset_of_mem_UJset hg`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩`.

Substitute `hTtop` using the available equality. Establish `hfd : FiniteDimensional ℂ (M.H τ)`. Use `hT'.1` as an intermediate fact. Conclude with `Module.Finite.equiv Submodule.topEquiv`. Use `⟨hfd, ?_, hε ▸ hrep, hT'⟩` and prove the remaining obligations.

Use `(hirr (M.sm τ) (M.sm τ).closed_of_finiteDimensional fun u hu v hv => ?_).resolve_left (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)` and prove the remaining obligations. Establish `hle : (M.sm τ).map (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ) ≤ M.sm τ`. Use `(Submodule.map_span_le _ _ _).2 fun w hw => Submodule.subset_span ?_` and prove the remaining obligations. Conclude with `smoothVec_stable hrep (M.fr_unit τ) (M.fr_gram τ) hu hw`. Conclude with `hle ⟨v, hv, rfl⟩`.
-/
theorem model_allPos : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau),
    M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧
      IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧
      IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  intro D V S M τ hε
  obtain ⟨-, -, hrep, hirr, -, ⟨T, hT⟩, -⟩ := M.ds τ
  have hT' := hT
  rw [hε] at hT'
  have hTtop : T = ⊤ := by
    obtain ⟨hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩ := hT'
    refine (hirr T T.closed_of_finiteDimensional fun g hg => hst g ?_).resolve_left ?_
    · rw [hε] at hg
      exact mem_Kset_of_mem_UJset hg
    · exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  subst hTtop
  have hfd : FiniteDimensional ℂ (M.H τ) := by
    have := hT'.1
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfd, ?_, hε ▸ hrep, hT'⟩
  refine (hirr (M.sm τ) (M.sm τ).closed_of_finiteDimensional fun u hu v hv => ?_).resolve_left
    (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  have hle : (M.sm τ).map (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ) ≤ M.sm τ := by
    refine (Submodule.map_span_le _ _ _).2 fun w hw => Submodule.subset_span ?_
    exact smoothVec_stable hrep (M.fr_unit τ) (M.fr_gram τ) hu hw
  exact hle ⟨v, hv, rfl⟩

end GlobalTheory.CompactModel
