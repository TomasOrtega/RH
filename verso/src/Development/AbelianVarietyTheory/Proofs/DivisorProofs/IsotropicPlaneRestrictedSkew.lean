import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviRatSkew

open Matrix

section Abstract

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `set A : Matrix (Fin n₁) (Fin n₁) R := (g : Matrix (Fin n₁) (Fin n₁) R) - 1 with hA`. Use `set B : Matrix (Fin n₁) (Fin n₁) R := ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) - 1 with hB`. Establish `hAB : A + B + A * B = 0`. Establish `hgg : (g : Matrix (Fin n₁) (Fin n₁) R) * ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) = 1`. Simplify using the standard rewrite rules.

Establish `: A + B + A * B = (g : Matrix (Fin n₁) (Fin n₁) R) * ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) - 1`. Rewrite using `[hA, hB]`. Use `noncomm_ring`. Rewrite using `[this, hgg, sub_self]`. Use `set M := 1 + ι * A * Q with hM`.

Use `set M' := 1 + ι * B * Q with hM'`. Establish `hMM : M * M' = 1`. Establish `e : M * M' = 1 + ι * (A + B + A * B) * Q`. Establish `: ι * A * Q * (ι * B * Q) = ι * (A * B) * Q`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hM, hM', add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, this, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hAB, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Establish `hKey : Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s = 0`. Establish `hgs : (g : Matrix (Fin n₁) (Fin n₁) R).map s = A.map s + 1`.

Rewrite using `[hA, Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]`. Normalize the expressions using the abelian group laws. Establish `hgt : (g : Matrix (Fin n₁) (Fin n₁) R)ᵀ = Aᵀ + 1`. Rewrite using `[hA, Matrix.transpose_sub, Matrix.transpose_one]`. Normalize the expressions using the abelian group laws.

Rewrite `hg` using `[hgs, hgt]`. Establish `: Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s = (Aᵀ + 1) * J₁ * (A.map s + 1) - J₁` using `by noncomm_ring`. Rewrite using `[this, hg, sub_self]`. Use `⟨⟨M, M', hMM, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hMM⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Mᵀ * J * M.map s = J`.

Establish `hMt : Mᵀ = 1 + Qᵀ * Aᵀ * ιᵀ`. Rewrite using `[hM, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `hMs : M.map s = 1 + ι.map s * A.map s * Q.map s`. Rewrite using `[hM, Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s), Matrix.map_mul, Matrix.map_mul]`. Rewrite using `[hMt, hMs]`.

Establish `e : (1 + Qᵀ * Aᵀ * ιᵀ) * J * (1 + ι.map s * A.map s * Q.map s) = J + Qᵀ * Aᵀ * (ιᵀ * J) + (J * ι.map s) * A.map s * Q.map s + Qᵀ * Aᵀ * (ιᵀ * J * ι.map s) * A.map s * Q.map s`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hg1, h2, h1]`. Establish `e2 : Qᵀ * Aᵀ * (J₁ * Q.map s) + Qᵀ * J₁ * A.map s * Q.map s + Qᵀ * Aᵀ * J₁ * A.map s * Q.map s = Qᵀ * (Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s) * Q.map s`.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]`. Rewrite using `[add_assoc, add_assoc, ← add_assoc (Qᵀ * Aᵀ * (J₁ * Q.map s)), e2, hKey, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Use `show M * ι = ι * (g : Matrix (Fin n₁) (Fin n₁) R)`. Establish `: (g : Matrix (Fin n₁) (Fin n₁) R) = 1 + A` using `by rw [hA]; abel`. Rewrite using `[this, hM, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQι, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]`.

Introduce `v hv show M *ᵥ v = v`. Rewrite using `[hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero]`.
-/
theorem levi_core (s : R →+* R) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) R) (J₁ : Matrix (Fin n₁) (Fin n₁) R)
    (ι : Matrix (Fin n) (Fin n₁) R) (Q : Matrix (Fin n₁) (Fin n) R) (hQι : Q * ι = 1)
    (h1 : J * ι.map s = Qᵀ * J₁) (h2 : ιᵀ * J = J₁ * Q.map s) (hg1 : ιᵀ * J * ι.map s = J₁)
    (g : GL (Fin n₁) R) (hg : (g : Matrix (Fin n₁) (Fin n₁) R)ᵀ * J₁ * (g : Matrix (Fin n₁) (Fin n₁) R).map s = J₁) :
    ∃ m : GL (Fin n) R, (m : Matrix _ _ R)ᵀ * J * (m : Matrix _ _ R).map s = J ∧
      (m : Matrix _ _ R) * ι = ι * (g : Matrix (Fin n₁) (Fin n₁) R) ∧
      ∀ v, Q *ᵥ v = 0 → (m : Matrix _ _ R) *ᵥ v = v := by
  set A : Matrix (Fin n₁) (Fin n₁) R := (g : Matrix (Fin n₁) (Fin n₁) R) - 1 with hA
  set B : Matrix (Fin n₁) (Fin n₁) R := ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) - 1 with hB
  have hAB : A + B + A * B = 0 := by
    have hgg : (g : Matrix (Fin n₁) (Fin n₁) R) * ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) = 1 := by
      simp
    have : A + B + A * B = (g : Matrix (Fin n₁) (Fin n₁) R) * ((g⁻¹ : GL (Fin n₁) R) : Matrix (Fin n₁) (Fin n₁) R) - 1 := by
      rw [hA, hB]; noncomm_ring
    rw [this, hgg, sub_self]
  set M := 1 + ι * A * Q with hM
  set M' := 1 + ι * B * Q with hM'
  have hMM : M * M' = 1 := by
    have e : M * M' = 1 + ι * (A + B + A * B) * Q := by
      have : ι * A * Q * (ι * B * Q) = ι * (A * B) * Q := by
        calc ι * A * Q * (ι * B * Q) = ι * A * (Q * ι) * B * Q := by simp only [Matrix.mul_assoc]
          _ = ι * (A * B) * Q := by rw [hQι, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [hM, hM', add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, this,
        Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
      abel
    rw [e, hAB, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hKey : Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s = 0 := by
    have hgs : (g : Matrix (Fin n₁) (Fin n₁) R).map s = A.map s + 1 := by
      rw [hA, Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]; abel
    have hgt : (g : Matrix (Fin n₁) (Fin n₁) R)ᵀ = Aᵀ + 1 := by
      rw [hA, Matrix.transpose_sub, Matrix.transpose_one]; abel
    rw [hgs, hgt] at hg
    have : Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s = (Aᵀ + 1) * J₁ * (A.map s + 1) - J₁ := by noncomm_ring
    rw [this, hg, sub_self]
  refine ⟨⟨M, M', hMM, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hMM⟩, ?_, ?_, ?_⟩
  · show Mᵀ * J * M.map s = J
    have hMt : Mᵀ = 1 + Qᵀ * Aᵀ * ιᵀ := by
      rw [hM, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    have hMs : M.map s = 1 + ι.map s * A.map s * Q.map s := by
      rw [hM, Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s), Matrix.map_mul, Matrix.map_mul]
    rw [hMt, hMs]
    have e : (1 + Qᵀ * Aᵀ * ιᵀ) * J * (1 + ι.map s * A.map s * Q.map s) =
        J + Qᵀ * Aᵀ * (ιᵀ * J) + (J * ι.map s) * A.map s * Q.map s + Qᵀ * Aᵀ * (ιᵀ * J * ι.map s) * A.map s * Q.map s := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hg1, h2, h1]
    have e2 : Qᵀ * Aᵀ * (J₁ * Q.map s) + Qᵀ * J₁ * A.map s * Q.map s + Qᵀ * Aᵀ * J₁ * A.map s * Q.map s =
        Qᵀ * (Aᵀ * J₁ + J₁ * A.map s + Aᵀ * J₁ * A.map s) * Q.map s := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [add_assoc, add_assoc, ← add_assoc (Qᵀ * Aᵀ * (J₁ * Q.map s)), e2, hKey, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · show M * ι = ι * (g : Matrix (Fin n₁) (Fin n₁) R)
    have : (g : Matrix (Fin n₁) (Fin n₁) R) = 1 + A := by rw [hA]; abel
    rw [this, hM, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQι, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]
  · intro v hv
    show M *ᵥ v = v
    rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero]

end Abstract

end GlobalTheory.LeviRatSkew

namespace GlobalTheory.LeviRatSkew

open Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `e : (A.map (inclR (F` using `F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by`. Use extensionality with `i j`. Simplify using `[cA, inclR]`. Rewrite using `[e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hA]`.
-/
theorem unitary_map' (σ : E →ₐ[F] E) {n : ℕ} (A J : Matrix (Fin n) (Fin n) E) (hA : Aᵀ * J * A.map σ = J) :
    (A.map (inclR (F := F) (AF F)))ᵀ * J.map (inclR (F := F) (AF F)) *
      (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = J.map (inclR (F := F) (AF F)) := by
  have e : (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by
    ext i j; simp [cA, inclR]
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hA]

/- English proof (translation)
Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Establish `e : (A.map (inclR (F` using `F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by`. Use extensionality with `i j`. Simplify using `[cA, inclR]`.

Rewrite `hA` using `[e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `hA`.
-/
theorem unitary_of_map' (σ : E →ₐ[F] E) {n : ℕ} (A J : Matrix (Fin n) (Fin n) E)
    (hA : (A.map (inclR (F := F) (AF F)))ᵀ * J.map (inclR (F := F) (AF F)) *
      (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = J.map (inclR (F := F) (AF F))) :
    Aᵀ * J * A.map σ = J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))
  apply Matrix.map_injective hinj
  have e : (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by
    ext i j; simp [cA, inclR]
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hA
  exact hA

/- English proof (translation)
Simplify using `only [form, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ]`. Simplify using `only [hskew, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem entry_eq (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (hskew : ∀ i j, σ (J j i) = -J i j) (z : Fin n → E) (k : Fin n₁) :
    (((ι.map σ)ᵀ * Jᵀ) *ᵥ z) k = -σ (form σ J (fun i => ι i k) z) := by
  simp only [form, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, hσ]
  simp only [hskew, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n n₁ Y Y₁ H hskew hxx hyy hxy horth hgram hdet γ hγ`. Use `set s : E →+* E := σ.toRingHom with hs`. Establish `hJs : (Y.J.map s)ᵀ = -Y.J` using `by ext i j; simp [hs, hskew]`. Establish `hιss : (H.ι.map s).map s = H.ι` using `by ext i j; simp [hs, hσ]`. Establish `hgram' : H.ιᵀ * Y.J * H.ι.map s = Y₁.J` using `hgram`.

Establish `hJ₁s : (Y₁.J.map s)ᵀ = -Y₁.J`. Rewrite using `[← hgram', Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hιss, hJs, Matrix.transpose_map, Matrix.transpose_transpose]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Establish `hdetT : IsUnit Y₁.Jᵀ.det` using `by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hdet`. Establish `hdet' : IsUnit Y₁.J.det` using `isUnit_iff_ne_zero.2 hdet`.

Use `set Q : Matrix (Fin n₁) (Fin n) E := (Y₁.Jᵀ)⁻¹ * ((H.ι.map s)ᵀ * Y.Jᵀ) with hQ`. Establish `hQι : Q * H.ι = 1`. Establish `: (H.ι.map s)ᵀ * Y.Jᵀ * H.ι = Y₁.Jᵀ`. Rewrite using `[← hgram']`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Rewrite using `[hQ, Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hdetT]`. Establish `h1 : Y.J * H.ι.map s = Qᵀ * Y₁.J`. Rewrite using `[hQ, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_one]`. Establish `h2 : H.ιᵀ * Y.J = Y₁.J * Q.map s`. Establish `e` using `congrArg (fun M => (M.map s)ᵀ) h1`.

Simplify using `only [Matrix.map_mul, Matrix.transpose_mul, hιss, hJs, hJ₁s, Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at e`. Conclude with `e`. Establish `hQv : ∀ z, (∀ u, form σ Y.J (H.ι *ᵥ u) z = 0) → Q *ᵥ z = 0`. Introduce `z hz`. Establish `e0 : ((H.ι.map s)ᵀ * Y.Jᵀ) *ᵥ z = 0`.

Use extensionality with `k`. Establish `e : (((H.ι.map s)ᵀ * Y.Jᵀ) *ᵥ z) k = -σ (form σ Y.J (H.ι *ᵥ Pi.single k 1) z)`. Establish `hcol : H.ι *ᵥ Pi.single k 1 = fun i => H.ι i k`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Rewrite using `[hcol]`. Conclude with `entry_eq σ hσ Y.J H.ι hskew z k`. Rewrite using `[e, hz, map_zero, neg_zero]`. Both sides reduce to the same expression. Rewrite using `[hQ, ← Matrix.mulVec_mulVec, e0, Matrix.mulVec_zero]`.

Establish `hQx : Q *ᵥ H.x = 0` using `hQv _ fun u => (horth u).1`. Establish `hQy : Q *ᵥ H.y = 0` using `hQv _ fun u => (horth u).2`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Take `⟨g, hg⟩` from `Subgroup.mem_subgroupOf.1 hγ`. Establish `hγm : mat γ = (g : Matrix (Fin n₁) (Fin n₁) E).map f`.

Simplify using `only [mat]`. Rewrite using `[← hg]`. Both sides reduce to the same expression. Establish `hγu : (mat γ)ᵀ * incM F Y₁.J * (mat γ).map (cA σ).toRingHom = incM F Y₁.J` using `γ.2`. Rewrite `hγu` using `[hγm]`.

Establish `hgu : (g : Matrix (Fin n₁) (Fin n₁) E)ᵀ * Y₁.J * (g : Matrix (Fin n₁) (Fin n₁) E).map s = Y₁.J` using `unitary_of_map' σ _ _ hγu`. Take `⟨m₀, hu, hι, hfix⟩` from `levi_core s Y.J Y₁.J H.ι Q hQι h1 h2 hgram' g hgu`. Set `h : UA σ Y.J` to `⟨Matrix.GeneralLinearGroup.map f m₀, unitary_map' σ _ _ hu⟩`. Establish `hmv : ∀ v : Fin n → E, mat h *ᵥ incV F v = incV F ((m₀ : Matrix _ _ E) *ᵥ v)` using `fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm`. Use `⟨h, Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmv, hfix _ hQx]`. Simplify using the standard rewrite rules. Rewrite using `[hmv, hfix _ hQy]`. Simplify using the standard rewrite rules. Rewrite using `[hγm]`.

Establish `e : mat h = (m₀ : Matrix (Fin n) (Fin n) E).map f` using `rfl`. Establish `e2 : incM F H.ι = H.ι.map f` using `rfl`. Rewrite using `[e, e2]`. Use `congrArg (fun M => Matrix.map M f) hι` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`.

Rewrite using `[← this]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]`. Simplify using `only [← map_mul, ← map_sum]`. Both sides reduce to the same expression.
-/
theorem exists_rat_isLevi_one_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J →
    Y₁.J.det ≠ 0 → ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m := by
  intro F E _ _ _ _ _ σ hσ n n₁ Y Y₁ H hskew hxx hyy hxy horth hgram hdet γ hγ
  set s : E →+* E := σ.toRingHom with hs
  have hJs : (Y.J.map s)ᵀ = -Y.J := by ext i j; simp [hs, hskew]
  have hιss : (H.ι.map s).map s = H.ι := by ext i j; simp [hs, hσ]
  have hgram' : H.ιᵀ * Y.J * H.ι.map s = Y₁.J := hgram
  have hJ₁s : (Y₁.J.map s)ᵀ = -Y₁.J := by
    rw [← hgram', Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hιss, hJs,
      Matrix.transpose_map, Matrix.transpose_transpose]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hdetT : IsUnit Y₁.Jᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hdet
  have hdet' : IsUnit Y₁.J.det := isUnit_iff_ne_zero.2 hdet
  set Q : Matrix (Fin n₁) (Fin n) E := (Y₁.Jᵀ)⁻¹ * ((H.ι.map s)ᵀ * Y.Jᵀ) with hQ
  have hQι : Q * H.ι = 1 := by
    have : (H.ι.map s)ᵀ * Y.Jᵀ * H.ι = Y₁.Jᵀ := by
      rw [← hgram']; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hdetT]
  have h1 : Y.J * H.ι.map s = Qᵀ * Y₁.J := by
    rw [hQ, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet',
      Matrix.mul_one]
  have h2 : H.ιᵀ * Y.J = Y₁.J * Q.map s := by
    have e := congrArg (fun M => (M.map s)ᵀ) h1
    simp only [Matrix.map_mul, Matrix.transpose_mul, hιss, hJs, hJ₁s, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at e
    exact e
  have hQv : ∀ z, (∀ u, form σ Y.J (H.ι *ᵥ u) z = 0) → Q *ᵥ z = 0 := by
    intro z hz
    have e0 : ((H.ι.map s)ᵀ * Y.Jᵀ) *ᵥ z = 0 := by
      ext k
      have e : (((H.ι.map s)ᵀ * Y.Jᵀ) *ᵥ z) k = -σ (form σ Y.J (H.ι *ᵥ Pi.single k 1) z) := by
        have hcol : H.ι *ᵥ Pi.single k 1 = fun i => H.ι i k := by
          ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
        rw [hcol]
        exact entry_eq σ hσ Y.J H.ι hskew z k
      rw [e, hz, map_zero, neg_zero]; rfl
    rw [hQ, ← Matrix.mulVec_mulVec, e0, Matrix.mulVec_zero]
  have hQx : Q *ᵥ H.x = 0 := hQv _ fun u => (horth u).1
  have hQy : Q *ᵥ H.y = 0 := hQv _ fun u => (horth u).2
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hγ
  have hγm : mat γ = (g : Matrix (Fin n₁) (Fin n₁) E).map f := by
    simp only [mat]; rw [← hg]; rfl
  have hγu : (mat γ)ᵀ * incM F Y₁.J * (mat γ).map (cA σ).toRingHom = incM F Y₁.J := γ.2
  rw [hγm] at hγu
  have hgu : (g : Matrix (Fin n₁) (Fin n₁) E)ᵀ * Y₁.J * (g : Matrix (Fin n₁) (Fin n₁) E).map s = Y₁.J :=
    unitary_of_map' σ _ _ hγu
  obtain ⟨m₀, hu, hι, hfix⟩ := levi_core s Y.J Y₁.J H.ι Q hQι h1 h2 hgram' g hgu
  let h : UA σ Y.J := ⟨Matrix.GeneralLinearGroup.map f m₀, unitary_map' σ _ _ hu⟩
  have hmv : ∀ v : Fin n → E, mat h *ᵥ incV F v = incV F ((m₀ : Matrix _ _ E) *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm
  refine ⟨h, Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩, ?_, ?_, ?_⟩
  · rw [hmv, hfix _ hQx]; simp
  · rw [hmv, hfix _ hQy]; simp
  · rw [hγm]
    have e : mat h = (m₀ : Matrix (Fin n) (Fin n) E).map f := rfl
    have e2 : incM F H.ι = H.ι.map f := rfl
    rw [e, e2]
    have := congrArg (fun M => Matrix.map M f) hι
    simp only [Matrix.map_mul] at this
    rw [← this]
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
    simp only [← map_mul, ← map_sum]
    rfl

end Field

end GlobalTheory.LeviRatSkew

end
