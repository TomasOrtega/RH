import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviSpan

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Substitute using the available equality. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem span_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z, σ (σ z) = z) → (∀ i j, σ (J j i) = J i j) → n = n₁ + 2 → form σ J x x = 0 → form σ J y y = 0 →
    form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 →
    ∀ z : Fin n → AE F E, ∃ (a b : AE F E) (w : Fin n₁ → AE F E), z = a • incV F x + incM F ι *ᵥ w + b • incV F y := by
  intro F E _ _ _ _ _ σ n n₁ J J₁ x y ι hσ hJ hn hxx hyy hxy hι hG hdet z
  have fadd : ∀ u v w : Fin n → E, form σ J (u + v) w = form σ J u w + form σ J v w := by
    intro u v w; simp [form, add_dotProduct]
  have fsmul : ∀ (c : E) (u w : Fin n → E), form σ J (c • u) w = c * form σ J u w := by
    intro c u w; simp [form, smul_dotProduct]
  have hswap : form σ J y x = σ (form σ J x y) := by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hyx : form σ J y x = 1 := by rw [hswap, hxy, map_one]
  have hinjι : ∀ w : Fin n₁ → E, ι *ᵥ w = 0 → w = 0 := by
    intro w hw
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← hG, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hw]
    simp
  let L : (E × (Fin n₁ → E) × E) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1 • x + ι *ᵥ p.2.1 + p.2.2 • y
      map_add' := by
        intro p q; simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mulVec_add]; abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Matrix.mulVec_smul,
          smul_add, mul_smul] }
  have hL : ∀ p, L p = p.1 • x + ι *ᵥ p.2.1 + p.2.2 • y := fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, w, b⟩ h
    rw [hL] at h
    have h1 := congrArg (fun v => form σ J v y) h
    have h2 := congrArg (fun v => form σ J v x) h
    simp only [fadd, fsmul, hxy, hyy, hxx, hyx, (hι w).1, (hι w).2] at h1 h2
    have hzero : ∀ v : Fin n → E, form σ J 0 v = 0 := by intro v; simp [form]
    rw [hzero] at h1 h2
    simp at h1 h2
    subst h1; subst h2
    simp at h
    simp [hinjι w h]
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · simp [Module.finrank_prod, Module.finrank_fin_fun]; omega
  choose p hp using fun i : Fin n => hsurj (Pi.single i 1)
  set R := inclR (F := F) (E := E) (AF F) with hR
  refine ⟨∑ i, z i * R (p i).1, ∑ i, z i * R (p i).2.2, fun k => ∑ i, z i * R ((p i).2.1 k), ?_⟩
  funext j
  have key : z j = ∑ i, z i * R ((Pi.single i 1 : Fin n → E) j) := by
    simp [Pi.single_apply, Finset.sum_ite_eq', eq_comm]
  rw [key]
  simp only [← hp, hL, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_add, map_mul, map_sum,
    incV, incM, Matrix.map_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k i => R (ι j k) * (z i * R ((p i).2.1 k)))]
  congr 1; congr 1
  all_goals (refine Finset.sum_congr rfl (fun i _ => ?_))
  all_goals (try refine Finset.sum_congr rfl (fun i _ => ?_))
  all_goals ring

end GlobalTheory.LeviSpan
