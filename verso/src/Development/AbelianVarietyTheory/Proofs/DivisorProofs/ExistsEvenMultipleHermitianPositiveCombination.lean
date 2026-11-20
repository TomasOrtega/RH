import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfAdjointEndoRelatingHermitianFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianEndoMatrixRationalInLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormEqCombinationOfSelfAdjointIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulAevalMemLatticeOfIntRationalMatrixStatement

open Matrix

namespace GlobalTheory.Desc.HermComb

/- English proof (translation)
Use `haveI : IsZLattice ℝ Λ := ⟨hs⟩`. Set `b` to `Module.finBasis ℤ Λ`. Use `⟨_, b.ofZLatticeBasis ℝ Λ, fun x => ⟨fun hx k => ⟨b.repr ⟨x, hx⟩ k, ?_⟩, fun h => ?_⟩⟩` and prove the remaining obligations. Conclude with `b.ofZLatticeBasis_repr_apply ℝ Λ ⟨x, hx⟩ k`. Use `choose m hm using h`.

Establish `hx : x = ∑ k, m k • (b k : Fin g → ℂ)` using `by conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr x]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hm k, Module.Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]`. Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2`.
-/
theorem lat_basis (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
      ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := Module.finBasis ℤ Λ
  refine ⟨_, b.ofZLatticeBasis ℝ Λ, fun x => ⟨fun hx k => ⟨b.repr ⟨x, hx⟩ k, ?_⟩, fun h => ?_⟩⟩
  · exact b.ofZLatticeBasis_repr_apply ℝ Λ ⟨x, hx⟩ k
  · choose m hm using h
    have hx : x = ∑ k, m k • (b k : Fin g → ℂ) := by
      conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hm k, Module.Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Use `⟨k * q.num, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]`.
-/
theorem int_of_den_dvd (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ m : ℤ, (D : ℚ) * q = m := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

/- English proof (translation)
Set `S : Finset ℚ` to `insert c₀ (Finset.univ.image c ∪ Finset.univ.image (fun x : Fin r × Fin n × Fin n => M x.1 x.2.1 x.2.2))`. Establish `hdv : ∀ q ∈ S, q.den ∣ ∏ q ∈ S, q.den` using `fun q hq => Finset.dvd_prod_of_mem _ hq`. Use `⟨∏ q ∈ S, q.den, Finset.prod_pos fun (q : ℚ) _ => q.den_pos, int_of_den_dvd _ _ (hdv _ ?_), fun i => int_of_den_dvd _ _ (hdv _ ?_), fun i k l => int_of_den_dvd _ _ (hdv _ ?_)⟩` and prove the remaining obligations. Simplify using `[S]`. Simplify using `[S]`.

Simplify using `only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]`. Conclude with `Or.inr (Or.inr ⟨(i, k, l), rfl⟩)`.
-/
theorem common_den (n r : ℕ) (c₀ : ℚ) (c : Fin r → ℚ) (M : Fin r → Matrix (Fin n) (Fin n) ℚ) :
    ∃ D : ℕ, 1 ≤ D ∧ (∃ m : ℤ, (D : ℚ) * c₀ = m) ∧ (∀ i, ∃ m : ℤ, (D : ℚ) * c i = m) ∧
      ∀ i k l, ∃ m : ℤ, (D : ℚ) * M i k l = m := by
  classical
  let S : Finset ℚ := insert c₀ (Finset.univ.image c ∪
    Finset.univ.image (fun x : Fin r × Fin n × Fin n => M x.1 x.2.1 x.2.2))
  have hdv : ∀ q ∈ S, q.den ∣ ∏ q ∈ S, q.den := fun q hq => Finset.dvd_prod_of_mem _ hq
  refine ⟨∏ q ∈ S, q.den, Finset.prod_pos fun (q : ℚ) _ => q.den_pos, int_of_den_dvd _ _ (hdv _ ?_),
    fun i => int_of_den_dvd _ _ (hdv _ ?_), fun i k l => int_of_den_dvd _ _ (hdv _ ?_)⟩
  · simp [S]
  · simp [S]
  · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨(i, k, l), rfl⟩)

end GlobalTheory.Desc.HermComb

namespace GlobalTheory.Desc.HermComb

/- English proof (translation)
Introduce `g Λ hd hs H₁ H₂ h₁ h₂ hp₁ hp₂ hi₁ hi₂`. Take `⟨n, e, he⟩` from `lat_basis g Λ hd hs`. Apply the tactic sequence `have hek : ∀ k, e k ∈ Λ := fun k => (he _).2 fun j => ⟨if k = j then 1 else 0, by rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp⟩`. Take `⟨γ, hγ, hsa⟩` from `GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms g H₁ H₂ h₁ h₂ hp₁`. Take `⟨Tq, hT⟩` from `GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis g n e H₁ H₂ hp₁ (fun k l => hi₁ _ (hek k) _ (hek l)) (fun k l => hi₂ _ (hek k) _ (hek l)) γ hγ`.

Take `⟨hB, hBT⟩` from `GlobalTheory.T.posDef_real_gram_pair_hermitian_forms g n e H₁ H₂ h₁ h₂ hp₁ hp₂ γ hγ`. Rewrite `hBT` using `[← hT]`. Take `⟨c₀, r, c, p, hc₀, hc, hid⟩` from `GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint n Tq _ hB hBT`. Establish `hform` using `GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity g H₁ H₂ γ hγ hsa c₀ r c p (GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map g n e γ Tq hT c₀ r c p hid)`. Take `⟨D, hD1, ⟨m₀, hm₀⟩, hci, hM⟩` from `common_den n r c₀ c (fun i => Polynomial.aeval Tq (p i))`.

Use `choose m hm using hci`. Establish `hm₀p : 0 < m₀`. Establish `: (0 : ℚ) < m₀` using `by rw [← hm₀]; exact mul_pos (by exact_mod_cast hD1) hc₀`. Conclude with `this` after adjusting the coercions. Establish `hmp : ∀ i, 0 ≤ m i` using `fun i => by`.

Establish `: (0 : ℚ) ≤ m i` using `by rw [← hm i]; exact (mul_pos (by exact_mod_cast hD1) (hc i)).le`. Conclude with `this` after adjusting the coercions. Use `⟨2 * D ^ 3, 2 * D ^ 2 * m₀.toNat, r, fun i => 2 * (m i).toNat, fun i => D • Polynomial.aeval γ (p i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: 1 ≤ D ^ 3` using `Nat.one_le_pow _ _ hD1`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : 1 ≤ D ^ 2` using `Nat.one_le_pow _ _ hD1`. Establish `h2 : 1 ≤ m₀.toNat` using `by omega`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `even_two_mul _`. Rewrite using `[mul_assoc]`.

Conclude with `even_two_mul _`. Conclude with `fun i => even_two_mul _`. Conclude with `fun i => GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix g n Λ e he γ Tq hT (p i) D (hM i)`. Introduce `z w`. Establish `hm₀' : ((m₀.toNat : ℕ) : ℂ) = (D : ℂ) * (c₀ : ℂ)`.

Establish `: ((m₀.toNat : ℤ) : ℚ) = (D : ℚ) * c₀` using `by rw [Int.toNat_of_nonneg hm₀p.le, hm₀]`. Conclude with `congrArg (fun q : ℚ => (q : ℂ)) this` after adjusting the coercions. Establish `hm' : ∀ i, (((m i).toNat : ℕ) : ℂ) = (D : ℂ) * (c i : ℂ)` using `fun i => by`. Establish `: (((m i).toNat : ℤ) : ℚ) = (D : ℚ) * c i` using `by rw [Int.toNat_of_nonneg (hmp i), hm i]`. Conclude with `congrArg (fun q : ℚ => (q : ℂ)) this` after adjusting the coercions.

Establish `hsc : ∀ a b : Fin g → ℂ, (D • a) ⬝ᵥ H₂.mulVec (star (D • b)) = (D : ℂ) * D * (a ⬝ᵥ H₂.mulVec (star b))`. Introduce `a b`. Rewrite using `[star_nsmul, mulVec_smul, dotProduct_smul, smul_dotProduct, nsmul_eq_mul, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [LinearMap.smul_apply, hsc]`.

Rewrite using `[hform z w]`. Move the coercions through the operations in `[hm₀', hm']`. Rewrite using `[mul_add, Finset.mul_sum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  intro g Λ hd hs H₁ H₂ h₁ h₂ hp₁ hp₂ hi₁ hi₂
  obtain ⟨n, e, he⟩ := lat_basis g Λ hd hs
  have hek : ∀ k, e k ∈ Λ := fun k => (he _).2 fun j =>
    ⟨if k = j then 1 else 0, by rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp⟩
  obtain ⟨γ, hγ, hsa⟩ := GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms g H₁ H₂ h₁ h₂ hp₁
  obtain ⟨Tq, hT⟩ := GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis g n e H₁ H₂ hp₁ (fun k l => hi₁ _ (hek k) _ (hek l))
    (fun k l => hi₂ _ (hek k) _ (hek l)) γ hγ
  obtain ⟨hB, hBT⟩ := GlobalTheory.T.posDef_real_gram_pair_hermitian_forms g n e H₁ H₂ h₁ h₂ hp₁ hp₂ γ hγ
  rw [← hT] at hBT
  obtain ⟨c₀, r, c, p, hc₀, hc, hid⟩ := GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint n Tq _ hB hBT
  have hform := GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity g H₁ H₂ γ hγ hsa c₀ r c p (GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map g n e γ Tq hT c₀ r c p hid)
  obtain ⟨D, hD1, ⟨m₀, hm₀⟩, hci, hM⟩ := common_den n r c₀ c (fun i => Polynomial.aeval Tq (p i))
  choose m hm using hci
  have hm₀p : 0 < m₀ := by
    have : (0 : ℚ) < m₀ := by rw [← hm₀]; exact mul_pos (by exact_mod_cast hD1) hc₀
    exact_mod_cast this
  have hmp : ∀ i, 0 ≤ m i := fun i => by
    have : (0 : ℚ) ≤ m i := by rw [← hm i]; exact (mul_pos (by exact_mod_cast hD1) (hc i)).le
    exact_mod_cast this
  refine ⟨2 * D ^ 3, 2 * D ^ 2 * m₀.toNat, r, fun i => 2 * (m i).toNat,
    fun i => D • Polynomial.aeval γ (p i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD1; omega
  · have h1 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ hD1
    have h2 : 1 ≤ m₀.toNat := by omega
    nlinarith
  · exact even_two_mul _
  · rw [mul_assoc]; exact even_two_mul _
  · exact fun i => even_two_mul _
  · exact fun i => GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix g n Λ e he γ Tq hT (p i) D (hM i)
  · intro z w
    have hm₀' : ((m₀.toNat : ℕ) : ℂ) = (D : ℂ) * (c₀ : ℂ) := by
      have : ((m₀.toNat : ℤ) : ℚ) = (D : ℚ) * c₀ := by rw [Int.toNat_of_nonneg hm₀p.le, hm₀]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hm' : ∀ i, (((m i).toNat : ℕ) : ℂ) = (D : ℂ) * (c i : ℂ) := fun i => by
      have : (((m i).toNat : ℤ) : ℚ) = (D : ℚ) * c i := by rw [Int.toNat_of_nonneg (hmp i), hm i]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hsc : ∀ a b : Fin g → ℂ, (D • a) ⬝ᵥ H₂.mulVec (star (D • b)) = (D : ℂ) * D * (a ⬝ᵥ H₂.mulVec (star b)) := by
      intro a b
      rw [star_nsmul, mulVec_smul, dotProduct_smul, smul_dotProduct, nsmul_eq_mul, nsmul_eq_mul]; ring
    simp only [LinearMap.smul_apply, hsc]
    rw [hform z w]
    push_cast [hm₀', hm']
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring

end GlobalTheory.Desc.HermComb
