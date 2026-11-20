import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FdDom

open ReciprocityTheory.ChartRestriction.G.FD

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib, RC …`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations.
-/
theorem gram_neg_transpose (τ : E →+* ℂ) (H : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Hᵀ) x = (-(xᴴ * H.map τ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Unfold `lminor`. Rewrite using `[← Matrix.transpose_submatrix, Matrix.det_transpose]`.
-/
theorem lminor_transpose (A : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : lminor Aᵀ i = lminor A i := by
  unfold lminor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(g.map τ)ᴴ * H.map τ * g.map τ = H.map τ`. Use extensionality with `b a`. Establish `h` using `congrArg τ (hg (Pi.single a 1) (Pi.single b 1))`. Establish `hc : ∀ z : E, τ (ReciprocityTheory.ChartRestriction.G.FD.cc z) = starRingEnd ℂ (τ z)` using `fun z => IsCMField.complexEmbedding_complexConj E τ z`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, hc, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, mul_ite, zero_mul, mul_zer …`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]`. Establish `h2 : (∑ x, ∑ y, if x = a then if y = b then -τ (H y x) else 0 else 0) = -τ (H b a)`. Rewrite using `[Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[← neg_inj, ← h2, ← h]`.

Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations.
-/
theorem map_mem_UH (τ : E →+* ℂ) (H g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) (g.mulVec x) (g.mulVec y) = ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) x y) :
    g.map τ ∈ Formalism.QuantumDeterminants.UH (H.map τ) := by
  change (g.map τ)ᴴ * H.map τ * g.map τ = H.map τ
  ext b a
  have h := congrArg τ (hg (Pi.single a 1) (Pi.single b 1))
  have hc : ∀ z : E, τ (ReciprocityTheory.ChartRestriction.G.FD.cc z) = starRingEnd ℂ (τ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E τ z
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, hc, Matrix.neg_apply,
    Matrix.transpose_apply, map_neg, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
    ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]
  have h2 : (∑ x, ∑ y, if x = a then if y = b then -τ (H y x) else 0 else 0) = -τ (H b a) := by
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← neg_inj, ← h2, ← h]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end

/- English proof (translation)
Introduce `s t h`. Apply `D.eTau.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(D.host.gal).symm.injective` to reduce the goal to its premises. Conclude with `AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)`.
-/
theorem tauE_injective (D : D7) : Function.Injective (tauE D) := by
  intro s t h
  apply D.eTau.injective
  apply Subtype.ext
  apply (D.host.gal).symm.injective
  exact AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)

/- English proof (translation)
Introduce `D θ V S M w r hr Comp X la dict mu c Kf _ hG k`. Substitute `hr` using the available equality. Establish `hΨ` using `hG.base.1 k`. Establish `hp` using `hG.base.2.1 k`. Establish `hGm : (X k).Gm = -V.gramᵀ` using `(hG.model k).1`.

Set `f : D.what₂.Tau → (X k).Ψ` to `fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩`. Establish `hf : Function.Bijective f`. Use `⟨fun s t h => tauE_injective D (congrArg Subtype.val h), fun τ => ?_⟩` and prove the remaining obligations. Take `⟨ρ, hρ⟩` from `(hΨ τ.1).1 τ.2`. Conclude with `⟨ρ, Subtype.ext hρ.symm⟩`.

Use `⟨Equiv.ofBijective f hf, fun _ => rfl, fun x => ?_, fun γ hγ ρ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∀ τ : (X k).Ψ, _) ↔ ∀ ρ, _`. Rewrite using `[← (Equiv.ofBijective f hf).forall_congr_right]`. Use `forall_congr' fun ρ => ?_` and prove the remaining obligations. Simplify using `only [dmin, hGm, gram_neg_transpose, lminor_transpose, hp ρ]`.

Both sides reduce to the same expression. Establish `h` using `((X k).Γ_stab γ hγ).1`. Rewrite `h` using `[hGm]`. Conclude with `map_mem_UH (tauE D ρ) V.gram _ h`.
-/
theorem dom_iff_frDoms : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  intro D θ V S M w r hr Comp X la dict mu c Kf _ hG k
  subst hr
  have hΨ := hG.base.1 k
  have hp := hG.base.2.1 k
  have hGm : (X k).Gm = -V.gramᵀ := (hG.model k).1
  let f : D.what₂.Tau → (X k).Ψ := fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t h => tauE_injective D (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := (hΨ τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext hρ.symm⟩
  refine ⟨Equiv.ofBijective f hf, fun _ => rfl, fun x => ?_, fun γ hγ ρ => ?_⟩
  · change (∀ τ : (X k).Ψ, _) ↔ ∀ ρ, _
    rw [← (Equiv.ofBijective f hf).forall_congr_right]
    refine forall_congr' fun ρ => ?_
    simp only [dmin, hGm, gram_neg_transpose, lminor_transpose, hp ρ]
    rfl
  · have h := ((X k).Γ_stab γ hγ).1
    rw [hGm] at h
    exact map_mem_UH (tauE D ρ) V.gram _ h

end GlobalTheory.HolDict.FdDom
