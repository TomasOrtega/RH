import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealIdeleFlow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueFlow

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

/- English proof (translation)
Use `set S := sigR (AF F) σ with hS`. Use `set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef`. Use `set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef`. Establish `hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹` using `map_inv _ g`. Establish `hMMi : M * Mi = 1`.

Rewrite using `[hMdef, hMidef, hinv]`. Conclude with `Units.mul_inv _`. Establish `hU : cT S M * adMat F J * M = adMat F J` using `g.2`. Establish `hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J`. Rewrite using `[adMat, Matrix.map_mul]`.

Use `congr 1`. Establish `hJM : adMat F J * M = cT S Mi * adMat F J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]`. Use `_ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]`.

Use `_ = cT S Mi * adMat F J := by rw [hU]`. Establish `h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J)`. Rewrite using `[hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]`. Establish `hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1`. Rewrite using `[adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h2 : cT S C = B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2]`.
-/
theorem row_of_stab {X Y : Matrix (Fin n) (Fin r) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {g : GAd σ J} {B C : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hX : (matHom _ σ J g).1 * adMat F X = adMat F X * B) (hY : (matHom _ σ J g⁻¹).1 * adMat F Y = adMat F Y * C) :
    adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 = B * adMat F (cT (σ : E →+* E) Y * J) := by
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J) := by
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : cT S C = B := by
    calc cT S C = cT S C * (adMat F (cT (σ : E →+* E) Y * J) * adMat F X) := by rw [hyx, Matrix.mul_one]
      _ = adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X := by rw [h1, Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [h1, h2]

/- English proof (translation)
Establish `ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} → (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧ ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C`. Introduce `m hm`. Simplify using `only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm`. Take `⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩` from `hm (Fin.last r) (Finset.mem_singleton_self _)`. Conclude with `⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩`.

Use `⟨?_, fun m hm => ?_⟩` and prove the remaining obligations. Simplify using `only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]`. Introduce `k hk`. Use `⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩, ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] …` and prove the remaining obligations. Use extensionality with `i j`.

Use `congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)` as an intermediate fact. Rewrite `this` using `[mul_diagonal]`. Rewrite using `[mul_diagonal]`. Simplify `this` using `[Matrix.mul_apply, initCols]`. Use extensionality with `i j`.

Use `congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)` as an intermediate fact. Rewrite `this` using `[mul_diagonal]`. Rewrite using `[mul_diagonal]`. Simplify `this` using `[Matrix.mul_apply, initCols]`. Take `⟨⟨B, hB⟩, ⟨C, hC⟩⟩` from `ext hm`.

Take `⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩` from `ext (inv_mem hm)`. Establish `rY` using `row_of_stab hCM hJ hW hB hC'`. Establish `rX` using `row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'`. Establish `dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d)` using `fun d Z => by`. Use extensionality with `i j`.

Simplify using `[diagonal_mul, mul_diagonal, mul_comm]`. Establish `c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J) * (mat …`. Rewrite using `[Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]`. Establish `c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F ( …`. Rewrite using `[Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]`.

Apply `matHom_injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, c1, c2]`.
-/
theorem const_centre {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {c : (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun _ => c) a) :
    a ∈ levi σ J X Y {Fin.last r} ∧ ∀ m ∈ levi σ J X Y {Fin.last r}, a * m = m * a := by
  have ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} →
      (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧
      ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C := by
    intro m hm
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm
    obtain ⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩ := hm (Fin.last r) (Finset.mem_singleton_self _)
    exact ⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := ext hm
    obtain ⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩ := ext (inv_mem hm)
    have rY := row_of_stab hCM hJ hW hB hC'
    have rX := row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'
    have dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d) := fun d Z => by
      ext i j; simp [diagonal_mul, mul_diagonal, mul_comm]
    have c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB,
        Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]
    have c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]
    apply matHom_injective
    apply Units.ext
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, c1, c2]

end GlobalTheory.ResidueFlow

open GlobalTheory.IdTorus in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hc hJ hW`. Take `⟨t, htc, ht⟩` from `exists_continuous_isIdTorusElt hc hJ hW`. Take `⟨l, lc, ladd, -, labs⟩` from `exists_real_idele_flow F E σ hc`. Establish `hd : ((r + 1 : ℕ) : ℝ) ≠ 0` using `by positivity`. Establish `cl` using `fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))`.

Use `⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)), htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_, fun s => (cl s).1, fun s => (cl s).2⟩` and prove the remaining obligations. Use `isIdTorusElt_uniq hc hJ hW (ht _) ?_` and prove the remaining obligations. Establish `: (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) = (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ))`. Use function extensionality and compare the values at `k`. Rewrite using `[add_div, ladd]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `isIdTorusElt_mul (ht _) (ht _)`. Use `⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩` and prove the remaining obligations. Establish `: Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) = l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1)`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _`. Rewrite using `[Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]`. Rewrite using `[this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]`.
-/
theorem GlobalTheory.ResidueEisenstein.exists_isFlowJ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  intro F E _ _ _ _ _ σ n J r X Y hc hJ hW
  obtain ⟨t, htc, ht⟩ := exists_continuous_isIdTorusElt hc hJ hW
  obtain ⟨l, lc, ladd, -, labs⟩ := exists_real_idele_flow F E σ hc
  have hd : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have cl := fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))
  refine ⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)),
    htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_,
    fun s => (cl s).1, fun s => (cl s).2⟩
  · refine isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) =
        (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ)) := by
      funext k; rw [add_div, ladd]; rfl
    rw [this]; exact isIdTorusElt_mul (ht _) (ht _)
  · refine ⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩
    have : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) =
        l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by
      apply Units.ext
      change Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

end
