import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLineLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem initCols_zero {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : initCols X 0 = col X :=
  Matrix.ext fun i j => congrArg (X i) (Fin.ext (Nat.lt_one_iff.1 j.2))

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_frameStab_of_parFlag {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {L : Matrix (Fin s) (Fin n) E} (hL : L * C = 1)
    {d : Fin s → ℕ} {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) : g ∈ frameStab σ J C ⊤ := by
  obtain ⟨⟨B, -, e⟩, B', -, e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  exact ⟨⟨B, B', hBB, mul_eq_one_comm.1 hBB⟩, Subgroup.mem_top _, e⟩

omit [NumberField E] in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities.
-/
theorem unipRad_fix {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, Units.val_one, Matrix.mul_one]⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [e, Subgroup.mem_bot.1 hB, Units.val_one, Matrix.mul_one]

omit [NumberField E] in

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem scales_inv {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x p l) :
    Scales σ J x p⁻¹ l⁻¹ := by
  unfold Scales at *
  have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J p⁻¹).1 * Z)) e
  simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
    Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
  exact this.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem levi_dec_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p l, Scales σ J (col X) p l → ∃ u ∈ unipRad σ J (col X), ∃ m ∈ levi σ J X Y {0}, p = u * m ∧ Scales σ J (col X) m l ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E l = 1 → m ∈ leviOne σ J X Y {0}) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW p l hp
  have sub : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, Formalism.UG.cT (σ : E →+* E) (col A) * J * col B =
      (Formalism.UG.cT (σ : E →+* E) A * J * B).submatrix (fun _ => 0) fun _ => 0 := fun A B => rfl
  have one : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) = 1 :=
    Matrix.ext fun i j => by obtain rfl := Subsingleton.elim i j; simp
  have xy : Formalism.UG.cT (σ : E →+* E) (col X) * J * col Y = 1 := by rw [sub, hW.xy, one]
  have yx' : Formalism.UG.cT (σ : E →+* E) (col Y) * J * col X = 1 := by rw [sub, yx h hJ hW, one]
  have sc : ∀ {g : GAd σ J} {l : (AF F ⊗[F] E)ˣ}, Scales σ J (col X) g l →
      (matHom _ σ J g).1 * adMat F (col X) = adMat F (col X) * (l.1 • (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E))) :=
    fun e => by rw [Matrix.mul_smul, Matrix.mul_one]; exact e
  have hpF : p ∈ GlobalTheory.UAut.parFlag σ J (col X) fun _ => 0 :=
    ⟨⟨_, fun _ _ hlt => absurd hlt (lt_irrefl _), sc hp⟩, _, fun _ _ hlt => absurd hlt (lt_irrefl _), sc (scales_inv hp)⟩
  obtain ⟨u, hu, m, hmF, hpm, hr⟩ := (GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ 1 (col X) (col Y) (fun _ => 0)
    (by rw [sub, hW.xx]; rfl) (by rw [sub, hW.yy]; rfl) xy).1 p hpF
  rw [GlobalTheory.UAut.unipFlag_const] at hu
  have hm : m ∈ levi σ J X Y {0} := by
    simp only [levi, Subgroup.mem_iInf, Finset.mem_singleton]
    rintro k rfl
    rw [initCols_zero, initCols_zero]
    exact ⟨mem_frameStab_of_parFlag yx' hmF.1, mem_frameStab_of_parFlag xy hmF.2⟩
  have hml : Scales σ J (col X) m l := by
    have e : m = u⁻¹ * p := by rw [hpm, inv_mul_cancel_left]
    have hp' : (matHom _ σ J p).1 * adMat F (col X) = l.1 • adMat F (col X) := hp
    unfold Scales
    rw [e, map_mul, Units.val_mul, Matrix.mul_assoc, hp', Matrix.mul_smul, unipRad_fix (inv_mem hu)]
  refine ⟨u, hu, m, hm, hpm, hml, hr, fun hl => Subgroup.mem_inf.2 ⟨hm, ?_⟩⟩
  simp only [Subgroup.mem_iInf, Finset.mem_singleton]
  rintro k rfl
  rw [initCols_zero]
  let B : GL (Fin 1) (AF F ⊗[F] E) := ⟨l.1 • 1, (l⁻¹).1 • 1, by simp [smul_smul], by simp [smul_smul]⟩
  refine ⟨B, ?_, sc hml⟩
  have e : Matrix.GeneralLinearGroup.det B = l := Units.ext (by simp [B])
  exact (congrArg (absE F E) e).trans hl

end GlobalTheory.ResLineLevi
