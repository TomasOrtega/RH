import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section GRpt

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]`. Simplify using `[JJ, Matrix.fromBlocks_multiply]`.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

def invG (M : M2 n) : M2 n := -(JJ n * Mᴴ * JJ n)

/- English proof (translation)
Unfold `invG`. Establish `h : JJ n * Mᴴ * JJ n * M = JJ n * (Mᴴ * JJ n * M)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[neg_mul, h, hM, JJ_mul_JJ, neg_neg]`.
-/
theorem invG_mul {M : M2 n} (hM : InG M) : invG M * M = 1 := by
  unfold invG
  have h : JJ n * Mᴴ * JJ n * M = JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
  rw [neg_mul, h, hM, JJ_mul_JJ, neg_neg]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (invG_mul hM)`.
-/
theorem mul_invG {M : M2 n} (hM : InG M) : M * invG M = 1 := mul_eq_one_comm.1 (invG_mul hM)

def mkG (M : M2 n) (hM : InG M) : GR n := ⟨⟨M, invG M, mul_invG hM, invG_mul hM⟩, hM⟩

def toGR' (M : M2 n) : GR n := if h : InG M then mkG M h else 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mkG (M : M2 n) (hM : InG M) : mR (mkG M hM) = M := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext rfl)`.
-/
theorem mkG_mR (y : GR n) : mkG (mR y) y.2 = y := Subtype.ext (Units.ext rfl)

/- English proof (translation)
The claim follows from `dif_pos hM`.
-/
theorem toGR'_of {M : M2 n} (hM : InG M) : toGR' M = mkG M hM := dif_pos hM

/- English proof (translation)
The claim follows from `(toGR'_of (M := mR y) y.2).trans (mkG_mR y)`.
-/
theorem toGR'_mR (y : GR n) : toGR' (mR y) = y := (toGR'_of (M := mR y) y.2).trans (mkG_mR y)

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mR : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Use `⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Use `show Continuous fun p : {M : M2 n | InG M} => invG p.1`. Unfold `invG`.

Conclude with `((continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const).neg`.
-/
theorem continuous_mkG : Continuous (fun p : {M : M2 n | InG M} => mkG p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  show Continuous fun p : {M : M2 n | InG M} => invG p.1
  unfold invG
  exact ((continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const).neg

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul' (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

end GRpt

/- English proof (translation)
Introduce `z a b`. Set `Fz : d.G → M2 d.n → ℂ` to `fun h M => f (R.ι w (toGR' M) * h)`. Set `Γ : Set (M2 d.n)` to `{M | ∃ y' : GR d.n, M = mR y' ∧ ∃ γ ∈ rat2 σ d.Y, ∃ x : d.G, γ = x * R.ι w y' ∧ ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x}`. Establish `hcont : ∀ h, ContinuousOn (Fz h) {g | InG g}`. Introduce `h`.

Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Establish `e : Set.domRestrict {g | InG g} (Fz h) = fun p : {M : M2 d.n | InG M} => f (R.ι w (mkG p.1 p.2) * h)`. Use function extensionality and compare the values at `p`. Use `show f (R.ι w (toGR' p.1) * h) = _`. Rewrite using `[toGR'_of p.2]`.

Rewrite using `[e]`. Conclude with `hf.comp (((R.cont w).comp continuous_mkG).mul continuous_const)`. Establish `hΓG : ∀ γ ∈ Γ, InG γ`. Introduce and unpack `_ ⟨y', rfl, -⟩`. Conclude with `y'.2`.

Establish `hdense : {g | InG g} ⊆ closure Γ`. Introduce `M hM`. Rewrite using `[mem_closure_iff]`. Introduce `U hU hMU`. Take `⟨γ, hγ, y', hy'O, x, hγx, hx⟩` from `hDW F E σ d R w (mkG M hM) (mR ⁻¹' U) (hU.preimage continuous_mR) hMU`.

Conclude with `⟨mR y', hy'O, y', rfl, γ, hγ, x, hγx, hx⟩`. Establish `hperm : ∀ γ ∈ Γ, ∀ h, ∃ h', ∀ g, InG g → Fz h (γ * g) = Fz h' g`. Introduce and unpack `_ ⟨y', rfl, γ, hγ, x, hγx, hx⟩ h`. Use `⟨x⁻¹ * h, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e1 : mR y' * g = mR (y' * mkG g hg)` using `rfl`.

Establish `hy : R.ι w y' = γ * x⁻¹` using `by rw [hγx, hx y', mul_inv_cancel_right]`. Establish `hc : x⁻¹ * R.ι w (mkG g hg) = R.ι w (mkG g hg) * x⁻¹`. Establish `hc' : Commute x (R.ι w (mkG g hg))` using `hx _`. Conclude with `hc'.inv_left.eq`. Simplify using `only [Fz]`.

Rewrite using `[e1, toGR'_mR, toGR'_of hg, map_mul, hy, mul_assoc, mul_assoc, hinv γ hγ, ← mul_assoc, hc, mul_assoc]`. Establish `hvan : ∀ h g, InG g → ∫ x, Fz h (nU (herm x) * g) * ψ₀ x = 0`. Introduce `h g hg`. Establish `e : ∀ x, Fz h (nU (herm x) * g) = f (R.ι w (nr x) * (R.ι w (mkG g hg) * h))` using `fun x => by`. Establish `e1 : nU (herm x) * g = mR (nr x * mkG g hg)` using `by rw [mR_mul', hnr, mR_mkG]`.

Simplify using `only [Fz]`. Rewrite using `[e1, toGR'_mR, map_mul, mul_assoc]`. Repeatedly rewrite using `[e]`. Conclude with `h0 _`. Establish `key` using `LVs.twoSided d.n d.G Fz Γ hcont hΓG hdense hperm ψ₀ hψc hψs hvan z (mR a) (mR b) a.2 b.2`.

Establish `e : ∀ x, Fz z (mR a * nU (herm x) * mR b) = f (R.ι w (a * nr x * b) * z)` using `fun x => by`. Establish `e1 : mR a * nU (herm x) * mR b = mR (a * nr x * b)` using `by rw [mR_mul', mR_mul', hnr]`. Simplify using `only [Fz]`. Rewrite using `[e1, toGR'_mR]`. Rewrite `key` using `[e]`.

Conclude with `key`.
-/
theorem twoSidedW (hDW : DenseW) (d : SD σ) (R : RD d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    (f : d.G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (h0 : ∀ z, ∫ x, f (R.ι w (nr x) * z) * ψ₀ x = 0) :
    ∀ (z : d.G) (a b : GR d.n), ∫ x, f (R.ι w (a * nr x * b) * z) * ψ₀ x = 0 := by
  intro z a b
  let Fz : d.G → M2 d.n → ℂ := fun h M => f (R.ι w (toGR' M) * h)
  let Γ : Set (M2 d.n) := {M | ∃ y' : GR d.n, M = mR y' ∧ ∃ γ ∈ rat2 σ d.Y, ∃ x : d.G, γ = x * R.ι w y' ∧
    ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x}
  have hcont : ∀ h, ContinuousOn (Fz h) {g | InG g} := by
    intro h
    rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {g | InG g} (Fz h) = fun p : {M : M2 d.n | InG M} => f (R.ι w (mkG p.1 p.2) * h) := by
      funext p
      show f (R.ι w (toGR' p.1) * h) = _
      rw [toGR'_of p.2]
    rw [e]
    exact hf.comp (((R.cont w).comp continuous_mkG).mul continuous_const)
  have hΓG : ∀ γ ∈ Γ, InG γ := by
    rintro _ ⟨y', rfl, -⟩
    exact y'.2
  have hdense : {g | InG g} ⊆ closure Γ := by
    intro M hM
    rw [mem_closure_iff]
    intro U hU hMU
    obtain ⟨γ, hγ, y', hy'O, x, hγx, hx⟩ := hDW F E σ d R w (mkG M hM) (mR ⁻¹' U) (hU.preimage continuous_mR) hMU
    exact ⟨mR y', hy'O, y', rfl, γ, hγ, x, hγx, hx⟩
  have hperm : ∀ γ ∈ Γ, ∀ h, ∃ h', ∀ g, InG g → Fz h (γ * g) = Fz h' g := by
    rintro _ ⟨y', rfl, γ, hγ, x, hγx, hx⟩ h
    refine ⟨x⁻¹ * h, fun g hg => ?_⟩
    have e1 : mR y' * g = mR (y' * mkG g hg) := rfl
    have hy : R.ι w y' = γ * x⁻¹ := by rw [hγx, hx y', mul_inv_cancel_right]
    have hc : x⁻¹ * R.ι w (mkG g hg) = R.ι w (mkG g hg) * x⁻¹ := by
      have hc' : Commute x (R.ι w (mkG g hg)) := hx _
      exact hc'.inv_left.eq
    simp only [Fz]
    rw [e1, toGR'_mR, toGR'_of hg, map_mul, hy, mul_assoc, mul_assoc, hinv γ hγ, ← mul_assoc, hc, mul_assoc]
  have hvan : ∀ h g, InG g → ∫ x, Fz h (nU (herm x) * g) * ψ₀ x = 0 := by
    intro h g hg
    have e : ∀ x, Fz h (nU (herm x) * g) = f (R.ι w (nr x) * (R.ι w (mkG g hg) * h)) := fun x => by
      have e1 : nU (herm x) * g = mR (nr x * mkG g hg) := by rw [mR_mul', hnr, mR_mkG]
      simp only [Fz]
      rw [e1, toGR'_mR, map_mul, mul_assoc]
    simp_rw [e]
    exact h0 _
  have key := LVs.twoSided d.n d.G Fz Γ hcont hΓG hdense hperm ψ₀ hψc hψs hvan z (mR a) (mR b) a.2 b.2
  have e : ∀ x, Fz z (mR a * nU (herm x) * mR b) = f (R.ι w (a * nr x * b) * z) := fun x => by
    have e1 : mR a * nU (herm x) * mR b = mR (a * nr x * b) := by rw [mR_mul', mR_mul', hnr]
    simp only [Fz]
    rw [e1, toGR'_mR]
  simp_rw [e] at key
  exact key

end PositivityTheory.SiegelWeilFormula.KSing

end
