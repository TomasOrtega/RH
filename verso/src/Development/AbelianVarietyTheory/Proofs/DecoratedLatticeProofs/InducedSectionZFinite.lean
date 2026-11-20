import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedKFiniteFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ContDiff

namespace GlobalTheory.EisCont.CentreFinite

open GlobalTheory.WeakHolFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Take `⟨w, τ, Z, hZ, hγ⟩` from `hγ`. Establish `hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1` using `fun x => (archEquiv J h τ x).2`. Establish `h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Establish `h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `u1` using `hu (projArch σ J w a)`. Establish `u2` using `hu (projArch σ J w a)⁻¹`. Use `⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_, fun t => ?_⟩` and prove the remaining obligations. Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *`.

Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *`. Generalize the expression as in `J.map τ.1 = Q at u1 u2 hZ ⊢`. Establish `e1 : M'ᴴ * Q = Q * M` using `by conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `e2 : Q * M' = Mᴴ * Q` using `by conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by`. Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]`.

Take `⟨y, e1, e2⟩` from `hγ t`. Use `⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩` and prove the remaining obligations. Use `show a⁻¹ * γ t * a = _`. Rewrite using `[e1]`. Use `GAd_ext σ J (fun u => ?_) fun v => by simp` and prove the remaining obligations.

Distinguish the cases in `e : u = w`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[projArch_embArch_ne σ J e]`. Rewrite using `[map_mul, map_mul, e2]`.

Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *`. Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *`. Establish `hM : IsUnit M` using `⟨⟨M, M', h2, h1⟩, rfl⟩`. Rewrite using `[← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Introduce `k γ hγ g`. Establish `hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a` using `fun l => by`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]`.

Simplify using `[mul_assoc]`. Establish `e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) = fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod)` using `funext fun t => by`. Rewrite using `[show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by`. Rewrite using `[List.map_ofFn]`. Use the proof step `rfl, hc]`.

Simplify using `[mul_assoc]`. Use `show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)`. Rewrite using `[e]`. Conclude with `hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)`.
-/
theorem isSm_mul_right (h : IsCMExt F E σ) {f : GAd σ J → ℂ} (hf : IsSm σ J f) (a : GAd σ J) :
    IsSm σ J fun x => f (x * a) := by
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)

/- English proof (translation)
The claim follows from `| [], _ => rfl | γ :: l, hl => by rw [List.foldr_cons, List.foldr_cons, foldr_mul_fin hb f l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)] obtain ⟨w, τ, Z, -, hγ⟩ := hl γ List.mem_cons_self have hc : ∀ t, γ t * b = b * γ t := fun t => by obtain ⟨y, hy, -⟩ := hγ t rw [hy] exact (c …`.
-/
theorem foldr_mul_fin {b : GAd σ J} (hb : b ∈ finPts σ J) (f : GAd σ J → ℂ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (fun x => f (x * b)) = fun x => l.foldr lineDer f (x * b)
  | [], _ => rfl
  | γ :: l, hl => by
    rw [List.foldr_cons, List.foldr_cons, foldr_mul_fin hb f l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)]
    obtain ⟨w, τ, Z, -, hγ⟩ := hl γ List.mem_cons_self
    have hc : ∀ t, γ t * b = b * γ t := fun t => by
      obtain ⟨y, hy, -⟩ := hγ t
      rw [hy]
      exact (commute_embArch σ J y (mem_finPts_iff_forall.1 hb w)).eq
    funext x
    simp only [lineDer, mul_assoc, hc]

/- English proof (translation)
Take `⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ infPts σ J, ∃ b ∈ finPts σ J, k = a * b` from `⟨_, mem_infPts.2 (projFin_ofInf _ _ _), _, mem_finPts.2 (projInf_ofFin _ _ _), (ofInf_projInf_mul_ofFin_projFin _ _ k).symm⟩`. Establish `e` using `hz.2 _ (isSm_mul_right h hφ b) a ha g`. Simplify using `only [← mul_assoc]`. Rewrite using `[e]`. Conclude with `Finset.sum_congr rfl fun l hl => by show _ * l.foldr lineDer φ (g * a * b) = _ * l.foldr lineDer (fun x => φ (x * b)) (g * a)`.

Rewrite using `[foldr_mul_fin hb φ l (hz.1 l hl)]`.
-/
theorem dop_mul_right (h : IsCMExt F E σ) {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : IsCentral σ J z) {φ : GAd σ J → ℂ}
    (hφ : IsSm σ J φ) (k g : GAd σ J) : dop z φ (g * k) = dop z (fun x => φ (x * k)) g := by
  obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ infPts σ J, ∃ b ∈ finPts σ J, k = a * b :=
    ⟨_, mem_infPts.2 (projFin_ofInf _ _ _), _, mem_finPts.2 (projInf_ofFin _ _ _),
      (ofInf_projInf_mul_ofFin_projFin _ _ k).symm⟩
  have e := hz.2 _ (isSm_mul_right h hφ b) a ha g
  simp only [← mul_assoc]
  rw [e]
  exact Finset.sum_congr rfl fun l hl => by
    show _ * l.foldr lineDer φ (g * a * b) = _ * l.foldr lineDer (fun x => φ (x * b)) (g * a)
    rw [foldr_mul_fin hb φ l (hz.1 l hl)]

end GlobalTheory.EisCont.CentreFinite
