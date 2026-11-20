import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

open Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J v f hQf hff hfc`. Use `set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef`. Establish `hQQ : Q * Q = Q`. Establish `h` using `GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])`. Rewrite `h` using `[← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero]`.

Conclude with `h.symm`. Use `set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef`. Use `set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef`. Establish `hp : p = 1 - q` using `by rw [hpdef, map_sub, map_one]`. Establish `hqq : q * q = q` using `by rw [hqdef, ← map_mul, hQQ]`.

Establish `hqf : q * f = f` using `by rw [hqdef, ← Algebra.smul_def]; exact hQf`. Establish `hcp : cA σ p = p` using `AlgHom.commutes _ _`. Establish `hpp : p * p = p` using `by rw [hp]; linear_combination hqq`. Establish `hpf : p * f = 0` using `by rw [hp]; linear_combination -hqf`. Establish `hpcf : p * cA σ f = 0` using `by rw [← hcp, ← map_mul, hpf, map_zero]`.

Establish `hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N` using `fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm`. Establish `hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1`. Introduce `a`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1) ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef`. Establish `hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1)`. Rewrite using `[hMdef, ← hQdef, hsm]`. Establish `hMM : M * M = 1`.

Rewrite using `[hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Take the linear combination `(1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)`. Take the linear combination `(1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)`.

Take the linear combination `(1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)`. Take the linear combination `(1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)`. Establish `hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J)`. Rewrite using `[hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, smul_smul, smul_neg]`.

Apply the tactic sequence `congr 1 <;> ext i j <;>`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]`. Apply the tactic sequence `all_goals first`. Consider the case `linear_combination incM F J i j * (hpp - hfc + hp)`. Consider the case `linear_combination incM F J i j * (hfc - hpp - hp)`.

Consider the case `linear_combination incM F J i j * (hpcf - hpf)`. Consider the case `linear_combination incM F J i j * (hpf - hpcf)`. Consider the case `linear_combination incM F J i j * (hpcf + hpf)`. Consider the case `linear_combination incM F J i j * (-hpcf - hpf)`. Use `⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩` and prove the remaining obligations.

Introduce `u hu show u • (M - 1) = 0`. Establish `hQu : u * Q = 0`. Establish `h` using `GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu`. Rewrite `h` using `[← hQdef, smul_eq_mul]`. Then use the resulting hypothesis. Use `set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef`.

Establish `huq : ua * q = 0` using `by rw [huadef, hqdef, ← map_mul, hQu, map_zero]`. Establish `huf : ua * f = 0` using `by rw [← hqf]; linear_combination f * huq`. Rewrite using `[← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]`. Apply the tactic sequence `ext (i | i) (j | j) <;>`. Apply the tactic sequence `simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>`.

Use `first`. Consider the case `linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)`. Consider the case `linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)`. Consider the case `linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))`. Consider the case `linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)`.

Consider the case `linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)`. Consider the case `linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)`. Introduce `k hk gd gd' hgd hgd'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M = ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))`. Establish `hK : p • (mat k - 1) = 0`. Rewrite using `[← hsm]`. Conclude with `hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])`. Establish `hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j`.

Introduce `i j`. Establish `h` using `congrFun (congrFun hK i) j`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h`. Take the linear combination `h`. Rewrite using `[hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, smul_smul, smul_zero]`. Apply the tactic sequence `congr 1 <;> ext i j <;>`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Apply the tactic sequence `all_goals first`. Consider the case `linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)`.

Consider the case `linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)`. Consider the case `linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)`.
-/
theorem swap_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  intro F E _ _ _ _ _ σ n J v f hQf hff hfc
  set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef
  have hQQ : Q * Q = Q := by
    have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q)
      (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef
  set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef
  have hp : p = 1 - q := by rw [hpdef, map_sub, map_one]
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQQ]
  have hqf : q * f = f := by rw [hqdef, ← Algebra.smul_def]; exact hQf
  have hcp : cA σ p = p := AlgHom.commutes _ _
  have hpp : p * p = p := by rw [hp]; linear_combination hqq
  have hpf : p * f = 0 := by rw [hp]; linear_combination -hqf
  have hpcf : p * cA σ f = 0 := by rw [← hcp, ← map_mul, hpf, map_zero]
  have hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N :=
    fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm
  have hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1 := by
    intro a; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
      ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef
  have hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1) := by
    rw [hMdef, ← hQdef, hsm]

  have hMM : M * M = 1 := by
    rw [hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
  have hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J) := by
    rw [hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul, smul_neg]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
    all_goals
      first
        | linear_combination incM F J i j * (hpp - hfc + hp)
        | linear_combination incM F J i j * (hfc - hpp - hp)
        | linear_combination incM F J i j * (hpcf - hpf)
        | linear_combination incM F J i j * (hpf - hpcf)
        | linear_combination incM F J i j * (hpcf + hpf)
        | linear_combination incM F J i j * (-hpcf - hpf)

  refine ⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩
  · intro u hu
    show u • (M - 1) = 0
    have hQu : u * Q = 0 := by
      have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
      rwa [← hQdef, smul_eq_mul] at h
    set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef
    have huq : ua * q = 0 := by rw [huadef, hqdef, ← map_mul, hQu, map_zero]
    have huf : ua * f = 0 := by rw [← hqf]; linear_combination f * huq
    rw [← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>
      first
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)
          | linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))
          | linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
  · intro k hk gd gd' hgd hgd'
    apply Subtype.ext
    apply Units.ext
    show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M =
      ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    have hK : p • (mat k - 1) = 0 := by
      rw [← hsm]
      exact hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    have hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
      intro i j
      have h := congrFun (congrFun hK i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h
      linear_combination h
    rw [hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul, smul_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    all_goals
      first
        | linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)
        | linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)
        | linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)

end GlobalTheory.DblDiag
