import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.HermCoords

def hermBil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) : LinearMap.BilinForm R (Fin n → S) :=
  LinearMap.mk₂ R (fun b a => Algebra.trace R S (∑ i, ∑ k, b i * J i k * c (a k)))
    (fun b b' a => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun r b a => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun b a a' => by
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun r b a => by
      simp only [Pi.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermBil_apply {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (b a : Fin n → S) :
    hermBil c J b a = Algebra.trace R S (∑ i, ∑ k, b i * J i k * c (a k)) := rfl

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CharZero F]

/- English proof (translation)
Establish `h1 : b ᵥ* J = 0`. Use function extensionality and compare the values at `l`. Use `(traceForm_nondegenerate F E).1 _ fun e => ?_` and prove the remaining obligations. Use `hb (Pi.single l (σ e) : Fin n → E)` as an intermediate fact. Rewrite `this` using `[hermBil_apply]`.

Rewrite using `[Algebra.traceForm_apply, ← this]`. Use `congr 1`. Establish `hs : ∀ j, ∑ l', b j * J j l' * σ ((Pi.single l (σ e) : Fin n → E) l') = b j * J j l * e` using `fun j => by`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using `[hσ]`.

Introduce `l' _ h`. Simplify using `[Pi.single_apply, h]`. Simplify using the standard rewrite rules. Simplify using `only [hs, Matrix.vecMul, dotProduct, Pi.zero_apply, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_hermBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : J.det ≠ 0) (b : Fin n → E) (hb : ∀ a, hermBil σ J b a = 0) : b = 0 := by
  have h1 : b ᵥ* J = 0 := by
    funext l
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    have := hb (Pi.single l (σ e) : Fin n → E)
    rw [hermBil_apply] at this
    rw [Algebra.traceForm_apply, ← this]
    congr 1
    have hs : ∀ j, ∑ l', b j * J j l' * σ ((Pi.single l (σ e) : Fin n → E) l') = b j * J j l * e := fun j => by
      rw [Finset.sum_eq_single l]
      · simp [hσ]
      · intro l' _ h
        simp [Pi.single_apply, h]
      · simp
    simp only [hs, Matrix.vecMul, dotProduct, Pi.zero_apply, Finset.sum_mul]
  calc b = b ᵥ* (J * J⁻¹) := by rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.vecMul_one]
    _ = (b ᵥ* J) ᵥ* J⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

/- English proof (translation)
The claim follows from `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (fun b hb => eq_zero_of_hermBil σ hσ hJ b hb)`.
-/
theorem nondegenerate_hermBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : J.det ≠ 0) : (hermBil σ J).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (fun b hb => eq_zero_of_hermBil σ hσ hJ b hb)

end Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_inclR (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

/- English proof (translation)
Establish `hc : ∀ e : E, cA σ (inclR (F` using `F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl`. Rewrite using `[hermBil_apply, hermBil_apply, ← trace_inclR]`. Simplify using `only [incV, incM, Matrix.map_apply, hc, map_mul, map_sum]`.
-/
theorem hermBil_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    hermBil (cA σ) (incM F J) (incV F v) (incV F w) = algebraMap F (AF F) (hermBil σ J v w) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [hermBil_apply, hermBil_apply, ← trace_inclR]
  simp only [incV, incM, Matrix.map_apply, hc, map_mul, map_sum]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [cA, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.HermCoords

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hσ h2 hJ hdet`. Establish `hrk : Module.finrank F (Fin n → E) = n * 2`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[h2]`. Set `β : Module.Basis (Fin n × Fin 2) F (Fin n → E)` to `(Module.finBasisOfFinrankEq F (Fin n → E) hrk).reindex finProdFinEquiv.symm`.

Set `hnd` to `GlobalTheory.HermCoords.nondegenerate_hermBil σ hσ hdet`. Set `β₂` to `(GlobalTheory.HermCoords.hermBil σ J).dualBasis hnd β`. Set `e` to `TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin n => E)`. Establish `hinc : ∀ v : Fin n → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v` using `fun v => by`. Use function extensionality and compare the values at `i`.

Both sides reduce to the same expression. Set `B₁` to `(β.baseChange (AF F)).map e`. Set `B₂` to `(β₂.baseChange (AF F)).map e`. Establish `hB₁ : ∀ l, B₁ l = incV F (β l)` using `fun l => by`. Simplify using `only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]`.

Establish `hB₂ : ∀ l, B₂ l = incV F (β₂ l)` using `fun l => by`. Simplify using `only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]`. Establish `hk : ∀ k l, GlobalTheory.HermCoords.hermBil (cA σ) (incM F J) (B₂ k) (B₁ l) = if l = k then 1 else 0`. Introduce `k l`. Rewrite using `[hB₁, hB₂, GlobalTheory.HermCoords.hermBil_incV, LinearMap.BilinForm.apply_dualBasis_left]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k))`. Introduce `a b`. Rewrite using `[← GlobalTheory.HermCoords.hermBil_apply]`. Use `conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]`.

Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hcc` using `GlobalTheory.HermCoords.cA_cA σ hσ`. Establish `hJ' : ∀ i k, cA σ (incM F J i k) = incM F J k i` using `fun i k => by show inclR (F := F) (AF F) (σ (J i k)) = inclR (F := F) (AF F) (J k i)`. Rewrite using `[hJ k i]`.

Establish `h2' : ∀ a b : Fin n → AE F E, Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k)) = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, a i * incM F J i k * cA σ (b k))`. Introduce `a b`. Set `eA : AE F E ≃ₐ[AF F] AE F E` to `AlgEquiv.ofBijective (cA σ) (Function.Involutive.bijective hcc)`. Rewrite using `[← Algebra.trace_eq_of_algEquiv eA (∑ i, ∑ k, a i * incM F J i k * cA σ (b k))]`. Use `congr 1`.

Use `show _ = cA σ _`. Simplify using `only [map_sum, map_mul, hcc, hJ']`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hrat : ∀ (b : Module.Basis (Fin n × Fin 2) F (Fin n → E)) (a : Fin n → E), ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k)`. Introduce `b a`. Use function extensionality and compare the values at `k`. Rewrite using `[← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]`. Conclude with `⟨B₂.equivFun, B₁.equivFun, h1, fun a b => (h1 a b).trans (h2' a b), fun a => ⟨_, hrat β₂ a⟩, fun a => ⟨_, hrat β a⟩⟩`.
-/
theorem GlobalTheory.HermCoords.exists_herm_pair_coords : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∃ p q : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin 2 → AF F),
      (∀ a b, p b ⬝ᵥ q a = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k))) ∧
      (∀ a b, p b ⬝ᵥ q a = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, a i * incM F J i k * cA σ (b k))) ∧
      (∀ a : Fin n → E, ∃ y : Fin n × Fin 2 → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin n → E, ∃ y : Fin n × Fin 2 → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  intro F E _ _ _ _ _ σ n J hσ h2 hJ hdet
  classical
  have hrk : Module.finrank F (Fin n → E) = n * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [h2]
  let β : Module.Basis (Fin n × Fin 2) F (Fin n → E) :=
    (Module.finBasisOfFinrankEq F (Fin n → E) hrk).reindex finProdFinEquiv.symm
  let hnd := GlobalTheory.HermCoords.nondegenerate_hermBil σ hσ hdet
  let β₂ := (GlobalTheory.HermCoords.hermBil σ J).dualBasis hnd β
  let e := TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin n => E)
  have hinc : ∀ v : Fin n → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v := fun v => by
    funext i
    rfl
  let B₁ := (β.baseChange (AF F)).map e
  let B₂ := (β₂.baseChange (AF F)).map e
  have hB₁ : ∀ l, B₁ l = incV F (β l) := fun l => by
    simp only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hB₂ : ∀ l, B₂ l = incV F (β₂ l) := fun l => by
    simp only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hk : ∀ k l, GlobalTheory.HermCoords.hermBil (cA σ) (incM F J) (B₂ k) (B₁ l) = if l = k then 1 else 0 := by
    intro k l
    rw [hB₁, hB₂, GlobalTheory.HermCoords.hermBil_incV, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a =
      Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k)) := by
    intro a b
    rw [← GlobalTheory.HermCoords.hermBil_apply]
    conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcc := GlobalTheory.HermCoords.cA_cA σ hσ
  have hJ' : ∀ i k, cA σ (incM F J i k) = incM F J k i := fun i k => by
    show inclR (F := F) (AF F) (σ (J i k)) = inclR (F := F) (AF F) (J k i)
    rw [hJ k i]
  have h2' : ∀ a b : Fin n → AE F E, Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k)) =
      Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, a i * incM F J i k * cA σ (b k)) := by
    intro a b
    let eA : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofBijective (cA σ) (Function.Involutive.bijective hcc)
    rw [← Algebra.trace_eq_of_algEquiv eA (∑ i, ∑ k, a i * incM F J i k * cA σ (b k))]
    congr 1
    show _ = cA σ _
    simp only [map_sum, map_mul, hcc, hJ']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrat : ∀ (b : Module.Basis (Fin n × Fin 2) F (Fin n → E)) (a : Fin n → E),
      ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k) := by
    intro b a
    funext k
    rw [← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  exact ⟨B₂.equivFun, B₁.equivFun, h1, fun a b => (h1 a b).trans (h2' a b),
    fun a => ⟨_, hrat β₂ a⟩, fun a => ⟨_, hrat β a⟩⟩
