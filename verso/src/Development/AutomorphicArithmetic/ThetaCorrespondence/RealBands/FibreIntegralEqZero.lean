import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IntegralCoefEqZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsCompactBall
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

open GlobalTheory.FibreAtTau

/- English proof (translation)
Take `⟨C, hC⟩` from `h`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Take `⟨-, hmul, -, -⟩` from `isCompact_ball V.rank (M.ε τ)`. Use `set c : ℝ := 1 + Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) with hc`. Use `⟨c ^ (2 * V.rank ^ 2 + 1) * C, fun u => ?_⟩` and prove the remaining obligations.

Use `set g := (M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ with hg`. Establish `hu : M.fr τ * g * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat u`. Rewrite using `[hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]`. Establish `hJ : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm (M.ε τ)` using `u.2`. Establish `hfg : M.fr τ * g = Formalism.MainNotions.S.umat u * M.fr τ`.

Rewrite using `[hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]`. Establish `hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)` using `by show gᴴ * gramAt D V τ * g = gramAt D V τ`. Rewrite using `[← M.fr_gram τ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (M.fr τ)ᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u) * M.fr τ := by`. Rewrite using `[hfg]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [hJ]`. Establish `h1` using `hC g hmem`.

Establish `he : M.rep τ g = M.σ τ (Formalism.MainNotions.S.umat u)` using `by rw [DSModel.rep, hu]`. Rewrite `h1` using `[he]`. Establish `hn : Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * hsn g * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹)`. Rewrite using `[← hu]`. Conclude with `(hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (Real.sqrt_nonneg _))`.

Establish `h0 : 0 ≤ hsn g` using `Real.sqrt_nonneg _`. Establish `hp : 0 ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹)` using `by positivity`. Establish `h2 : 1 + Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ c * (1 + hsn g)` using `by rw [hc]; nlinarith`. Establish `h3 : wt u ≤ c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)`. Rewrite using `[← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) h2 _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decays_of_decayAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (v a : M.H τ)
    (h : DecayAt M τ v a (2 * V.rank ^ 2 + 1)) : Decays (Formalism.MainNotions.S.coefOn (ε := M.ε τ) (M.σ τ) a v) := by
  obtain ⟨C, hC⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨-, hmul, -, -⟩ := isCompact_ball V.rank (M.ε τ)
  set c : ℝ := 1 + Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) with hc
  refine ⟨c ^ (2 * V.rank ^ 2 + 1) * C, fun u => ?_⟩
  set g := (M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ with hg
  have hu : M.fr τ * g * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat u := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hJ : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm (M.ε τ) := u.2
  have hfg : M.fr τ * g = Formalism.MainNotions.S.umat u * M.fr τ := by
    rw [hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show gᴴ * gramAt D V τ * g = gramAt D V τ
    rw [← M.fr_gram τ]
    calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
        = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u) * M.fr τ := by
          rw [hfg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hJ]
  have h1 := hC g hmem
  have he : M.rep τ g = M.σ τ (Formalism.MainNotions.S.umat u) := by rw [DSModel.rep, hu]
  rw [he] at h1
  have hn : Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤
      Real.sqrt (Formalism.REAL.hs (M.fr τ)) * hsn g * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by
    rw [← hu]
    exact (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (Real.sqrt_nonneg _))
  have h0 : 0 ≤ hsn g := Real.sqrt_nonneg _
  have hp : 0 ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by positivity
  have h2 : 1 + Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ c * (1 + hsn g) := by rw [hc]; nlinarith
  have h3 : wt u ≤ c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 _
  calc _ ≤ ‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = c ^ (2 * V.rank ^ 2 + 1) * (‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/- English proof (translation)
Introduce `D θ hθ V S M K v a hv ha τ r C hC`. Use `⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1, L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩` and prove the remaining obligations. Introduce `ν hν q hq x y`. Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Use `haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩`.

Take `⟨E, hE⟩` from `L_hom θ hθ V S M τ`. Take `⟨W, hW, hemb, hrange⟩` from `L_emb θ hθ V S M τ C hC E hE`. Take `⟨R, hR⟩` from `L_factor θ hθ V S M K v a τ C q hq x y`. Set `ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ)` to `E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)`. Establish `hι : Topology.IsClosedEmbedding ι` using `hemb`.

Establish `hmap` using `isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)`. Establish `hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W`. Rewrite using `[← MonoidHom.range_eq_map, MonoidHom.coe_range]`. Conclude with `hrange`. Rewrite `hmap` using `[hr]`.

Establish `hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ)`. Establish `hDS` using `M.ds τ`. Conclude with `⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩`. Establish `h0` using `integral_coef_eq_zero V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (v τ) (a τ) (decays_of_decayAt M τ _ _ (hv τ)) (decays_of_decayAt M τ _ _ (ha τ)) W hW (ν.map ι) hmap (E x) (E y)`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`.

Establish `key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) = ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R`. Introduce `p`. Rewrite using `[hR p p.2]`. Use `congr 2`. Use `show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)`.

Use `congr 2`. Express the relevant statement in the definitionally equal form `M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)`. Rewrite using `[hE, hE, hE]`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]`. Repeatedly rewrite using `[key]`.

Establish `hint` using `hι.measurableEmbedding.integral_map (μ := ν) (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)`. Rewrite using `[integral_mul_const, ← hint, h0, zero_mul]`.
-/
theorem fibre_integral_eq_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, DecayAt M τ (v τ) (v τ) (2 * V.rank ^ 2 + 1)) → (∀ τ, DecayAt M τ (v τ) (a τ) (2 * V.rank ^ 2 + 1)) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := integral_coef_eq_zero V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (v τ) (a τ)
    (decays_of_decayAt M τ _ _ (hv τ)) (decays_of_decayAt M τ _ _ (ha τ)) W hW (ν.map ι) hmap (E x) (E y)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end UpperTheory.Lit.Cusp
