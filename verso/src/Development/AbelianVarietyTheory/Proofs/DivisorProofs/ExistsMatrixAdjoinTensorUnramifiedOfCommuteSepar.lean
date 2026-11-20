import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqAevalOfCommute
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyTensorCommutant

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def algK : Algebra K (KQ p K r) := inferInstanceAs (Algebra K (K ⊗[ℚ_[p]] Qr p r))

attribute [local instance] algK

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem inclK_mul (a : K) (x : KQ p K r) : inclK p K r a * x = a • x := by
  rw [Algebra.smul_def]; rfl

def bQ : Module.Basis (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) K (KQ p K r) :=
  Algebra.TensorProduct.basis K (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r))

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.basis_apply _ _`.
-/
theorem bQ_apply (i) : bQ p K r i = inclQ p K r (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r) i) :=
  Algebra.TensorProduct.basis_apply _ _

/- English proof (translation)
Rewrite using `[Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_diagonal]`.
-/
theorem mul_algebraMap_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (KQ p K r)) (c : KQ p K r) (i j : Fin n) :
    (M * algebraMap (KQ p K r) (Matrix (Fin n) (Fin n) (KQ p K r)) c) i j = M i j * c := by
  rw [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.mul_diagonal]

/- English proof (translation)
Introduce `p _ K n r γ _ hsep X hX`. Set `Xc : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → Matrix (Fin n) (Fin n) K` to `fun i => X.map (fun x => (bQ p K r).coord i x)`. Establish `hcomm : ∀ i, Commute (Xc i) γ`. Introduce `i`. Use `Matrix.ext fun a c => ?_` and prove the remaining obligations.

Establish `h` using `congrArg (fun M : Matrix (Fin n) (Fin n) (KQ p K r) => (bQ p K r).coord i (M a c)) hX.eq`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, Xc] at h ⊢`. Simplify using `only [mul_comm (X _ _) (inclK p K r _), inclK_mul, map_smul, smul_eq_mul] at h`. Simplify `h` using `[mul_comm]`. Establish `hmem : ∀ i, Xc i ∈ GlobalTheory.PolyTensor.polySub p K n γ`.

Introduce `i`. Take `⟨q, hq⟩` from `GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n γ (Xc i) hsep (hcomm i)`. Rewrite using `[GlobalTheory.PolyTensor.mem_polySub, hq]`. Conclude with `Polynomial.aeval_mem_adjoin_singleton K γ`. Set `y : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → GlobalTheory.PolyTensor.PolyAlg p K n γ` to `fun i => ⟨Xc i, hmem i⟩`.

Set `e` to `Module.Basis.ofVectorSpace ℚ_[p] (Qr p r)`. Set `s : Finset (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r))` to `Finset.univ.biUnion (fun ac : Fin n × Fin n => ((bQ p K r).repr (X ac.1 ac.2)).support)`. Use `⟨∑ i ∈ s, y i ⊗ₜ e i, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Matrix.ext fun a c => ?_` and prove the remaining obligations.

Simplify using `only [GlobalTheory.PolyTensor.phi_tmul, Matrix.sum_apply, mul_algebraMap_apply, Matrix.map_apply]`. Establish `hv : ∀ i, GlobalTheory.PolyTensor.val p K n γ (y i) = Xc i` using `fun i => rfl`. Simplify using `only [hv, Xc, Matrix.map_apply, inclK_mul, ← bQ_apply]`. Simplify using `only [e, ← bQ_apply, Module.Basis.coord_apply]`. Establish `hsub : ((bQ p K r).repr (X a c)).support ⊆ s` using `fun i hi => Finset.mem_biUnion.2 ⟨(a, c), Finset.mem_univ _, hi⟩`.

Rewrite using `[← Finsupp.sum_of_support_subset _ hsub (fun i k => k • bQ p K r i) (fun i _ => zero_smul _ _), ← Finsupp.linearCombination_apply, Module.Basis.linearCombination_repr]`.
-/
theorem exists_phi_eq : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r),
    Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  intro p _ K n r γ _ hsep X hX
  classical
  let Xc : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → Matrix (Fin n) (Fin n) K :=
    fun i => X.map (fun x => (bQ p K r).coord i x)
  have hcomm : ∀ i, Commute (Xc i) γ := by
    intro i
    refine Matrix.ext fun a c => ?_
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (KQ p K r) => (bQ p K r).coord i (M a c)) hX.eq
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, Xc] at h ⊢
    simp only [mul_comm (X _ _) (inclK p K r _), inclK_mul, map_smul, smul_eq_mul] at h
    simpa [mul_comm] using h
  have hmem : ∀ i, Xc i ∈ GlobalTheory.PolyTensor.polySub p K n γ := by
    intro i
    obtain ⟨q, hq⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n γ (Xc i) hsep (hcomm i)
    rw [GlobalTheory.PolyTensor.mem_polySub, hq]
    exact Polynomial.aeval_mem_adjoin_singleton K γ
  let y : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → GlobalTheory.PolyTensor.PolyAlg p K n γ := fun i => ⟨Xc i, hmem i⟩
  let e := Module.Basis.ofVectorSpace ℚ_[p] (Qr p r)
  let s : Finset (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) :=
    Finset.univ.biUnion (fun ac : Fin n × Fin n => ((bQ p K r).repr (X ac.1 ac.2)).support)
  refine ⟨∑ i ∈ s, y i ⊗ₜ e i, ?_⟩
  rw [map_sum]
  refine Matrix.ext fun a c => ?_
  simp only [GlobalTheory.PolyTensor.phi_tmul, Matrix.sum_apply, mul_algebraMap_apply, Matrix.map_apply]
  have hv : ∀ i, GlobalTheory.PolyTensor.val p K n γ (y i) = Xc i := fun i => rfl
  simp only [hv, Xc, Matrix.map_apply, inclK_mul, ← bQ_apply]
  simp only [e, ← bQ_apply, Module.Basis.coord_apply]
  have hsub : ((bQ p K r).repr (X a c)).support ⊆ s := fun i hi =>
    Finset.mem_biUnion.2 ⟨(a, c), Finset.mem_univ _, hi⟩
  rw [← Finsupp.sum_of_support_subset _ hsub (fun i k => k • bQ p K r i) (fun i _ => zero_smul _ _),
    ← Finsupp.linearCombination_apply, Module.Basis.linearCombination_repr]

end GlobalTheory.PolyTensorCommutant
