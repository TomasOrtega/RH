import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

noncomputable section

namespace GlobalTheory.BaseFrameChange

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [gram_eq, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x m : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (x * m) = mᵀ * gram τ G x * m.map (starRingEnd ℂ) := by
  simp only [gram_eq, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]

def Orth (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

/- English proof (translation)
The claim follows from `((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).1`.
-/
theorem Orth.dom {X : Data E r} {x : Frame X.Ψ r} (h : Orth X x) : x ∈ X.dom :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).1

/- English proof (translation)
The claim follows from `((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).2 τ i`.
-/
theorem Orth.unit {X : Data E r} {x : Frame X.Ψ r} (h : Orth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).2 τ i

/- English proof (translation)
The claim follows from `isUnit_iff_ne_zero.2 ((Orth.dom (X := X) (x := fun τ => x₀ τ.1) (fun τ => h τ.1 τ.2)) τ).1`.
-/
theorem isUnit_det_of_x0Orth {X : Data E r} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h : IsOrthogonalFrame X x₀) (τ : X.Ψ) :
    IsUnit (x₀ τ.1).det :=
  isUnit_iff_ne_zero.2 ((Orth.dom (X := X) (x := fun τ => x₀ τ.1) (fun τ => h τ.1 τ.2)) τ).1

def pass (Ψ : Finset (E →+* ℂ)) (x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Frame Ψ r :=
  fun τ => ((x₀ τ.1)⁻¹ * x₁ τ.1 : Matrix (Fin r) (Fin r) ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) (τ : Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_pass {Ψ : Finset (E →+* ℂ)} (x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (τ : Ψ) :
    mat (pass Ψ x₀ x₁) τ = (x₀ τ.1)⁻¹ * x₁ τ.1 := rfl

/- English proof (translation)
The claim follows from `funext fun τ => h τ`.
-/
theorem frame_ext {Ψ : Finset (E →+* ℂ)} {x y : Frame Ψ r} (h : ∀ τ, mat x τ = mat y τ) : x = y :=
  funext fun τ => h τ

/- English proof (translation)
The claim follows from `frame_ext fun τ => by simp only [mat_rmul, mat_lact, Matrix.mul_assoc]`.
-/
theorem rmul_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    rmul (lact γ x) b = lact γ (rmul x b) :=
  frame_ext fun τ => by simp only [mat_rmul, mat_lact, Matrix.mul_assoc]

/- English proof (translation)
The claim follows from `frame_ext fun τ => by simp only [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) :=
  frame_ext fun τ => by simp only [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `τ`. Rewrite using `[mat_rmul, gram_mul, h τ, ← h₀ τ.1 τ.2, ← gram_mul, mat_pass, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₀ τ), h₁ τ.1 τ.2, h₀ τ.1 τ.2]`.
-/
theorem Orth.pass {X : Data E r} {x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀) (h₁ : IsOrthogonalFrame X x₁)
    {x : Frame X.Ψ r} (h : Orth X x) : Orth X (rmul x (pass X.Ψ x₀ x₁)) := by
  intro τ
  rw [mat_rmul, gram_mul, h τ, ← h₀ τ.1 τ.2, ← gram_mul, mat_pass,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₀ τ), h₁ τ.1 τ.2, h₀ τ.1 τ.2]

/- English proof (translation)
The claim follows from `frame_ext fun τ => by rw [mat_rmul, mat_rmul, mat_pass, mat_pass, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₁ τ), Matrix.nonsing_inv_mul _ (isUnit_det_of_x0Orth h₀ τ), Matrix.mul_one]`.
-/
theorem rmul_pass_pass {X : Data E r} {x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀)
    (h₁ : IsOrthogonalFrame X x₁) (x : Frame X.Ψ r) : rmul (rmul x (pass X.Ψ x₀ x₁)) (pass X.Ψ x₁ x₀) = x :=
  frame_ext fun τ => by
    rw [mat_rmul, mat_rmul, mat_pass, mat_pass, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₁ τ),
      Matrix.nonsing_inv_mul _ (isUnit_det_of_x0Orth h₀ τ), Matrix.mul_one]

end Frames

variable {D : D7} {r : ℕ} {Comp : Type}

def moveDict {V : HSp D} {X : Comp → Data D.host.E r} (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : GA D V → Σ k, Frame (X k).Ψ r :=
  fun g => ⟨(dict g).1, rmul (dict g).2 (pass _ x₀ x₁)⟩

/- English proof (translation)
Unfold `moveDict`. Rewrite using `[h]`.
-/
theorem moveDict_eq {V : HSp D} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    (x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) {g : GA D V} {k : Comp} {x : Frame (X k).Ψ r}
    (h : dict g = ⟨k, x⟩) : moveDict dict x₀ x₁ g = ⟨k, rmul x (pass _ x₀ x₁)⟩ := by
  unfold moveDict
  rw [h]

/- English proof (translation)
Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, neg_inj, ← Matrix.transpose_inj]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.
-/
theorem unitary_iff {n : ℕ} (u J : Matrix (Fin n) (Fin n) ℂ) :
    uᵀ * (-Jᵀ) * u.map (starRingEnd ℂ) = -Jᵀ ↔ (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj, ← Matrix.transpose_inj]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[hW.1]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem gm_map {V : HSp D} {X : Data D.host.E V.rank} (hW : ModelW V rfl X) (τ : D.host.E →+* ℂ) :
    X.Gm.map τ = -(V.gram.map τ)ᵀ := by
  rw [hW.1]
  ext a b
  simp

/- English proof (translation)
Substitute `hr` using the available equality. Take `⟨dL, dR, ⟨y, dy, dI⟩, dD, dO, dF⟩` from `hd`. Establish `hy : ∀ c, Orth (X c) (y c)` using `fun c => by`. Take `⟨g, e⟩` from `(dy c).2`. Use `ho g` as an intermediate fact.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hyd : ∀ c τ, IsUnit (mat (y c) τ).det` using `fun c τ => isUnit_iff_ne_zero.2 ((dy c).1 τ).1`. Use `⟨fun γ hγ g => ?_, fun k hk g => ?_, ⟨fun c => rmul (y c) (pass _ x₀ x₁), fun c => ?_, fun g h hh => ?_⟩, fun g => ((ho g).pass (h₀ _) (h₁ _)).dom, fun c x hx => ?_, fun g g' hg => ?_⟩` and prove the remaining obligations. Take `⟨γ', h1, e⟩` from `dL γ hγ g`. Conclude with `⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩`.

Take `⟨γ', h1, e⟩` from `dR k hk g`. Conclude with `⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩`. Take `⟨g, e⟩` from `(dy c).2`. Conclude with `⟨((hy c).pass (h₀ _) (h₁ _)).dom, g, moveDict_eq x₀ x₁ e⟩`. Take `⟨γ', h1, e⟩` from `dI g h hh`.

Use `⟨γ', h1, (moveDict_eq x₀ x₁ e).trans ?_⟩` and prove the remaining obligations. Rewrite using `[rmul_lact]`. Use `congrArg (fun z => (⟨(dict g).1, lact γ' z⟩ : Σ k, Frame (X k).Ψ V.rank)) (frame_ext fun τ => ?_)` and prove the remaining obligations. Establish `hm : IsUnit (mat (pass (X (dict g).1).Ψ x₀ x₁) τ).det`. Rewrite using `[mat_pass, Matrix.det_mul]`.

Conclude with `(Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_x0Orth (h₀ _) τ)).mul (isUnit_det_of_x0Orth (h₁ _) τ)`. Use `show mat (dict g).2 τ * ((mat (y _) τ)⁻¹ * _ * mat (y _) τ) * mat (pass _ x₀ x₁) τ = mat (dict g).2 τ * mat (pass _ x₀ x₁) τ * ((mat (y _) τ * mat (pass _ x₀ x₁) τ)⁻¹ * _ * (mat (y _) τ * mat (pass _ x₀ x₁) τ))`. Rewrite using `[Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hm]`.

Both sides reduce to the same expression. Take `⟨g, γ, hγ, b, hb, e⟩` from `dO c x hx`. Take `⟨-, h4⟩` from `GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (X c).p0 (X c).Ψ (X c).Gm (X c).Gm_herm`. Establish `hz` using `(hy c).pass (h₁ c) (h₀ c)`. Use `choose u hu using fun τ : (X c).Ψ => h4 τ.1 (mat (y c) τ) (mat (rmul (y c) (pass _ x₁ x₀)) τ) (hy c τ) ((hz τ).trans (hy c τ).symm)`.

Take `⟨h, hh, ea⟩` from `((GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X c).Ψ (th c) (X c).cmType (hth c)).2.2.2 u fun τ => (unitary_iff _ _).1 (by rw [← gm_map (hW c)]; exact (hu τ).1)`. Establish `hA : archMat V th rfl y h c = pass _ x₁ x₀` using `frame_ext fun τ => by show (mat (y c) τ)⁻¹ * archM V (th c τ) h * mat (y c) τ = _`. Rewrite using `[ea, Matrix.mul_assoc, ← (hu τ).2, mat_rmul, Matrix.nonsing_inv_mul_cancel_left _ _ (hyd c τ)]`. Establish `hI` using `dI g h hh`. Rewrite `hI` using `[e]`.

Take `⟨γ', h1, e'⟩` from `hI`. Use `⟨g * h, γ' * γ, mul_mem h1 hγ, b, hb, (moveDict_eq x₀ x₁ e').trans ?_⟩` and prove the remaining obligations. Use `show (⟨c, rmul (lact γ' (rmul (rmul (lact γ x) b) (archMat V th rfl y h c))) (pass _ x₀ x₁)⟩ : Σ k, Frame (X k).Ψ V.rank) = _`. Rewrite using `[hA, rmul_lact, rmul_pass_pass (h₁ c) (h₀ c), lact_mul, rmul_lact γ']`. Take `⟨γ', h1, e⟩` from `hg`.

Use `dF g g' ⟨γ', h1, ?_⟩` and prove the remaining obligations. Establish `e1 : moveDict (moveDict dict x₀ x₁) x₁ x₀ g' = dict g'` using `(moveDict_eq x₁ x₀ (moveDict_eq x₀ x₁ (rfl : dict g' = ⟨(dict g').1, (dict g').2⟩))).trans (by rw [rmul_pass_pass (h₀ _) (h₁ _)])`. Rewrite using `[← e1, moveDict_eq x₁ x₀ e, rmul_lact]`. Use `show (⟨(dict g).1, lact γ' (rmul (rmul (dict g).2 (pass _ x₀ x₁)) (pass _ x₁ x₀))⟩ : Σ k, Frame (X k).Ψ V.rank) = _`. Rewrite using `[rmul_pass_pass (h₀ _) (h₁ _)]`.
-/
theorem dictIsUnif_move {V : HSp D} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : DictIsUnif V dict Kf th hr) (hW : ∀ k, ModelW V hr (X k))
    (ho : ∀ g, Orth (X (dict g).1) (dict g).2) {x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (h₀ : ∀ k, IsOrthogonalFrame (X k) x₀) (h₁ : ∀ k, IsOrthogonalFrame (X k) x₁) : DictIsUnif V (moveDict dict x₀ x₁) Kf th hr := by
  subst hr
  obtain ⟨dL, dR, ⟨y, dy, dI⟩, dD, dO, dF⟩ := hd
  have hy : ∀ c, Orth (X c) (y c) := fun c => by
    obtain ⟨g, e⟩ := (dy c).2
    have := ho g
    rwa [e] at this
  have hyd : ∀ c τ, IsUnit (mat (y c) τ).det := fun c τ => isUnit_iff_ne_zero.2 ((dy c).1 τ).1
  refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, ⟨fun c => rmul (y c) (pass _ x₀ x₁), fun c => ?_, fun g h hh => ?_⟩,
    fun g => ((ho g).pass (h₀ _) (h₁ _)).dom, fun c x hx => ?_, fun g g' hg => ?_⟩
  · obtain ⟨γ', h1, e⟩ := dL γ hγ g
    exact ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩
  · obtain ⟨γ', h1, e⟩ := dR k hk g
    exact ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩
  · obtain ⟨g, e⟩ := (dy c).2
    exact ⟨((hy c).pass (h₀ _) (h₁ _)).dom, g, moveDict_eq x₀ x₁ e⟩
  · obtain ⟨γ', h1, e⟩ := dI g h hh
    refine ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans ?_⟩
    rw [rmul_lact]
    refine congrArg (fun z => (⟨(dict g).1, lact γ' z⟩ : Σ k, Frame (X k).Ψ V.rank)) (frame_ext fun τ => ?_)
    have hm : IsUnit (mat (pass (X (dict g).1).Ψ x₀ x₁) τ).det := by
      rw [mat_pass, Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_x0Orth (h₀ _) τ)).mul (isUnit_det_of_x0Orth (h₁ _) τ)
    show mat (dict g).2 τ * ((mat (y _) τ)⁻¹ * _ * mat (y _) τ) * mat (pass _ x₀ x₁) τ =
      mat (dict g).2 τ * mat (pass _ x₀ x₁) τ * ((mat (y _) τ * mat (pass _ x₀ x₁) τ)⁻¹ * _ *
        (mat (y _) τ * mat (pass _ x₀ x₁) τ))
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hm]
    rfl
  · obtain ⟨g, γ, hγ, b, hb, e⟩ := dO c x hx
    obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (X c).p0
      (X c).Ψ (X c).Gm (X c).Gm_herm
    have hz := (hy c).pass (h₁ c) (h₀ c)
    choose u hu using fun τ : (X c).Ψ => h4 τ.1 (mat (y c) τ) (mat (rmul (y c) (pass _ x₁ x₀)) τ) (hy c τ)
      ((hz τ).trans (hy c τ).symm)
    obtain ⟨h, hh, ea⟩ := ((GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X c).Ψ (th c) (X c).cmType (hth c)).2.2.2 u
      fun τ => (unitary_iff _ _).1 (by rw [← gm_map (hW c)]; exact (hu τ).1)
    have hA : archMat V th rfl y h c = pass _ x₁ x₀ := frame_ext fun τ => by
      show (mat (y c) τ)⁻¹ * archM V (th c τ) h * mat (y c) τ = _
      rw [ea, Matrix.mul_assoc, ← (hu τ).2, mat_rmul, Matrix.nonsing_inv_mul_cancel_left _ _ (hyd c τ)]
    have hI := dI g h hh
    rw [e] at hI
    obtain ⟨γ', h1, e'⟩ := hI
    refine ⟨g * h, γ' * γ, mul_mem h1 hγ, b, hb, (moveDict_eq x₀ x₁ e').trans ?_⟩
    show (⟨c, rmul (lact γ' (rmul (rmul (lact γ x) b) (archMat V th rfl y h c))) (pass _ x₀ x₁)⟩ :
      Σ k, Frame (X k).Ψ V.rank) = _
    rw [hA, rmul_lact, rmul_pass_pass (h₁ c) (h₀ c), lact_mul, rmul_lact γ']
  · obtain ⟨γ', h1, e⟩ := hg
    refine dF g g' ⟨γ', h1, ?_⟩
    have e1 : moveDict (moveDict dict x₀ x₁) x₁ x₀ g' = dict g' :=
      (moveDict_eq x₁ x₀ (moveDict_eq x₀ x₁ (rfl : dict g' = ⟨(dict g').1, (dict g').2⟩))).trans
        (by rw [rmul_pass_pass (h₀ _) (h₁ _)])
    rw [← e1, moveDict_eq x₁ x₀ e, rmul_lact]
    show (⟨(dict g).1, lact γ' (rmul (rmul (dict g).2 (pass _ x₀ x₁)) (pass _ x₁ x₀))⟩ :
      Σ k, Frame (X k).Ψ V.rank) = _
    rw [rmul_pass_pass (h₀ _) (h₁ _)]

/- English proof (translation)
Substitute `hr` using the available equality. Introduce `τ`. Rewrite using `[hx, (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.2 τ.1 _ _ ?_]`. Conclude with `h₀ τ.1 τ.2`. Rewrite using `[gm_map hW]`.

Conclude with `(unitary_iff _ _).2 (GlobalTheory.RecDictModel.archM_unitary V (hth τ) g)`.
-/
theorem orth_of_arch {V : HSp D} {hr : V.rank = r} {X : Data D.host.E r} (hW : ModelW V hr X)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀) {x : Frame X.Ψ r} {g : GA D V}
    (hx : ∀ τ, mat x τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th τ) g) * x₀ τ.1) : Orth X x := by
  subst hr
  intro τ
  rw [hx, (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.2 τ.1 _ _ ?_]
  · exact h₀ τ.1 τ.2
  · rw [gm_map hW]
    exact (unitary_iff _ _).2 (GlobalTheory.RecDictModel.archM_unitary V (hth τ) g)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T x₀ hv hJ hC hx`. Establish `ho : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ g, Orth ((T.U j σ).X (T.dict j σ g).1) (T.dict j σ g).2`. Introduce `j hj σ hσ g`. Take `⟨hr, n, e, F, ik, φ, th, -, -, hth, -, hL⟩` from `hJ.adPin j hj σ hσ`. Take `⟨_, hW⟩` from `hJ.modelW j hj σ hσ`.

Take `⟨γ, -, -, -, h3⟩` from `hL g`. Conclude with `orth_of_arch (hr := hr) (hW _) (hth _) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) h3`. Establish `hd : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.Kf j σ) th hr`. Introduce `j hj σ hσ`. Take `⟨th, hr, hth, h⟩` from `hJ.dictU j hj σ hσ`.

Take `⟨_, hW⟩` from `hJ.modelW j hj σ hσ`. Conclude with `⟨th, hr, hth, dictIsUnif_move hth h hW (ho j hj σ hσ) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ) (hx j hj σ hσ)⟩`. Establish `hm : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ)`. Introduce `j hj σ hσ`. Take `⟨h1, h2, h3, -⟩` from `hJ.muUnit j hj σ hσ`.

Conclude with `⟨h1, h2, h3, fun g => ((ho j hj σ hσ g).pass (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) (hx j hj σ hσ _)).unit⟩`. Establish `hA : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdelAut (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ)`. Introduce `j hj σ hσ`. Take `⟨th, hr, hth, h⟩` from `hd j hj σ hσ`. Establish `hK` using `hJ.levelK j hj σ hσ`.

Conclude with `GlobalTheory.OneEmbeddingProbe.adelAut_of_dominant (T.U j σ) (hJ.chiTriv j hj σ hσ) h (hm j hj σ hσ) (hJ.muCont j hj σ hσ) (GlobalTheory.DictLocTest.locClause_of_unif_places h (fun k hk => ((hK k).1 hk).1) (GlobalTheory.LevelOpen.level_mem_nhds D _ _ _ (Nat.mul_pos (D.host.g_prim …`. Establish `hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ)`. Introduce `j hj σ hσ`. Take `⟨th, hr, hth, h⟩` from `hd j hj σ hσ`. Conclude with `cusp_L2_of_measurable hσ (dict_dom_of h) (hm j hj σ hσ) (adelMeas_of_aut _ _ (hA j hj σ hσ))`.

Establish `hM : LawsM (reCore T (fun j σ => moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) T.mu T.chiW x₀ T.cE).toCore` using `{ hJ.toLawsM with dictU := hd muUnit := hm cuspidalL2Subspace := hL l2Def := fun j hj σ hσ => by`. Take `⟨th, hr, hth, h⟩` from `hd j hj σ hσ`. Use `l2Def_of_cusp hσ (hJ.supDef j hj) (aeDom_of (hA j hj σ hσ) (hJ.finVol j hj σ hσ) (volPair_of_tie hv _ ?_) (hm j hj σ hσ) h) (hL j hj σ hσ)` and prove the remaining obligations. Rewrite using `[hJ.spaceW j hj σ hσ]`. Conclude with `D.sp.W_sig j }`.

Use `⟨_, ⟨hM, hJ.cUnit, hJ.muVal, hJ.muConj, hJ.intAll, hJ.modelW, hx, hJ.kfHalf, fun j hj σ hσ => ?_⟩, ⟨hM, hC.cuspMul, hC.latZ, hC.cuNe, hC.expo⟩⟩` and prove the remaining obligations. Take `⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, h4⟩` from `hJ.adPin j hj σ hσ`. Use `⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, k1, k2, k3, k4⟩` from `h4 g`. Use `⟨γ, k1, k2, k3, fun τ => ?_⟩` and prove the remaining obligations.

Use `show mat (T.dict j σ g).2 τ * ((T.x₀ j σ τ.1)⁻¹ * x₀ j σ τ.1) = _`. Rewrite using `[k4 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) τ)]`. Both sides reduce to the same expression.
-/
theorem exists_dict_of_x0Orth : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  intro D T x₀ hv hJ hC hx
  have ho : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ g, Orth ((T.U j σ).X (T.dict j σ g).1) (T.dict j σ g).2 := by
    intro j hj σ hσ g
    obtain ⟨hr, n, e, F, ik, φ, th, -, -, hth, -, hL⟩ := hJ.adPin j hj σ hσ
    obtain ⟨_, hW⟩ := hJ.modelW j hj σ hσ
    obtain ⟨γ, -, -, -, h3⟩ := hL g
    exact orth_of_arch (hr := hr) (hW _) (hth _) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) h3
  have hd : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.Kf j σ) th hr := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hJ.dictU j hj σ hσ
    obtain ⟨_, hW⟩ := hJ.modelW j hj σ hσ
    exact ⟨th, hr, hth, dictIsUnif_move hth h hW (ho j hj σ hσ) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ) (hx j hj σ hσ)⟩
  have hm : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      MuUnit (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨h1, h2, h3, -⟩ := hJ.muUnit j hj σ hσ
    exact ⟨h1, h2, h3, fun g => ((ho j hj σ hσ g).pass (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) (hx j hj σ hσ _)).unit⟩
  have hA : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      AdelAut (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
    have hK := hJ.levelK j hj σ hσ
    exact GlobalTheory.OneEmbeddingProbe.adelAut_of_dominant (T.U j σ) (hJ.chiTriv j hj σ hσ) h (hm j hj σ hσ)
      (hJ.muCont j hj σ hσ) (GlobalTheory.DictLocTest.locClause_of_unif_places h (fun k hk => ((hK k).1 hk).1)
        (GlobalTheory.LevelOpen.level_mem_nhds D _ _ _ (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hK)
        fun k τ => ⟨τ.1, hth k τ⟩)
  have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      CuspL2 (T.U j) σ (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
    exact cusp_L2_of_measurable hσ (dict_dom_of h) (hm j hj σ hσ) (adelMeas_of_aut _ _ (hA j hj σ hσ))
  have hM : LawsM (reCore T (fun j σ => moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) T.mu T.chiW x₀ T.cE).toCore :=
    { hJ.toLawsM with
      dictU := hd
      muUnit := hm
      cuspidalL2Subspace := hL
      l2Def := fun j hj σ hσ => by
        obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
        refine l2Def_of_cusp hσ (hJ.supDef j hj) (aeDom_of (hA j hj σ hσ) (hJ.finVol j hj σ hσ)
          (volPair_of_tie hv _ ?_) (hm j hj σ hσ) h) (hL j hj σ hσ)
        rw [hJ.spaceW j hj σ hσ]
        exact D.sp.W_sig j }
  refine ⟨_, ⟨hM, hJ.cUnit, hJ.muVal, hJ.muConj, hJ.intAll, hJ.modelW, hx, hJ.kfHalf, fun j hj σ hσ => ?_⟩,
    ⟨hM, hC.cuspMul, hC.latZ, hC.cuNe, hC.expo⟩⟩
  obtain ⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, h4⟩ := hJ.adPin j hj σ hσ
  refine ⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, fun g => ?_⟩
  obtain ⟨γ, k1, k2, k3, k4⟩ := h4 g
  refine ⟨γ, k1, k2, k3, fun τ => ?_⟩
  show mat (T.dict j σ g).2 τ * ((T.x₀ j σ τ.1)⁻¹ * x₀ j σ τ.1) = _
  rw [k4 τ, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) τ)]
  rfl

end GlobalTheory.BaseFrameChange
