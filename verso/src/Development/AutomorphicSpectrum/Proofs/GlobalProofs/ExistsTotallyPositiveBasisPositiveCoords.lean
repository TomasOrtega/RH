import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddingsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrankStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolutionStatement

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast, mul_comm]`.
-/
theorem map_sum_ratSmul {F κ : Type} [Field F] [Fintype κ] (σ : F →+* ℝ) (q : κ → ℚ) (v : κ → F) :
    σ (∑ i, q i • v i) = ∑ i, σ (v i) * (q i : ℝ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

/- English proof (translation)
Introduce `F _ _ _ M`. Take `⟨hfin, hcard⟩` from `GlobalTheory.T.card_real_embeddings_eq_finrank F`. Use `letI : Fintype (F →+* ℝ) := Fintype.ofFinite _`. Take `⟨ε, hε, hW⟩` from `GlobalTheory.T.near_identity_matrix_positive_solution (κ := F →+* ℝ) M`. Establish `hex : ∀ i : F →+* ℝ, ∃ v : F, ∀ σ : F →+* ℝ, |σ v - ((if σ = i then 1 else 0) + ε / 2)| < ε / 2` using `fun i => GlobalTheory.T.totally_real_field_dense_embeddings F (fun σ => (if σ = i then 1 else 0) + ε / 2) (ε / 2) (by positivity)`.

Use `choose v hv using hex`. Establish `hclose : ∀ σ i : F →+* ℝ, |σ (v i) - if σ = i then 1 else 0| < ε`. Introduce `σ i`. Establish `h` using `abs_lt.mp (hv i σ)`. Rewrite using `[abs_lt]`.

Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`. Establish `hpos : ∀ σ i : F →+* ℝ, 0 < σ (v i)`. Introduce `σ i`. Establish `h` using `(abs_lt.mp (hv i σ)).1`. Apply the tactic sequence `split_ifs at h <;> linarith`.

Take `⟨h1, h2⟩` from `hW (fun σ i => σ (v i)) hclose`. Establish `hli : LinearIndependent ℚ v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `q hq i`. Establish `hz : (fun i => (q i : ℝ)) = 0` using `h1 _ fun σ => by`.

Rewrite using `[← map_sum_ratSmul σ q v, hq, map_zero]`. Establish `hi : (q i : ℝ) = 0` using `congrFun hz i`. Conclude with `hi` after adjusting the coercions. Establish `hcardκ : Fintype.card (F →+* ℝ) = Module.finrank ℚ F`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Conclude with `hcard`. Use `haveI : Nonempty (F →+* ℝ) := by`. Apply `Fintype.card_pos_iff.mp` to reduce the goal to its premises. Rewrite using `[hcardκ]`. Conclude with `Module.finrank_pos`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcardκ`. Establish `hb : ∀ i, b i = v i` using `fun i => by`. Simplify using `[b, coe_basisOfLinearIndependentOfCardEqFinrank]`. Use `⟨F →+* ℝ, inferInstance, b, fun i σ => ?_, fun x hx hM i => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`.

Conclude with `hpos σ i`. Establish `hrep : ∀ σ : F →+* ℝ, σ x = ∑ i, σ (v i) * ((b.repr x i : ℚ) : ℝ)`. Introduce `σ`. Rewrite using `[← map_sum_ratSmul σ (fun i => b.repr x i) v]`. Use `congr 1`.

Use `conv_lhs => rw [← b.sum_repr x]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hb]`. Establish `hc` using `h2 (fun i => ((b.repr x i : ℚ) : ℝ)) (fun σ => by rw [← hrep σ]; exact hx σ) (fun σ τ => by rw [← hrep σ, ← hrep τ]; exact hM σ τ) i`. Conclude with `hc` after adjusting the coercions.
-/
theorem exists_totPos_basis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  intro F _ _ _ M
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_real_embeddings_eq_finrank F
  letI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  obtain ⟨ε, hε, hW⟩ := GlobalTheory.T.near_identity_matrix_positive_solution (κ := F →+* ℝ) M
  have hex : ∀ i : F →+* ℝ, ∃ v : F, ∀ σ : F →+* ℝ,
      |σ v - ((if σ = i then 1 else 0) + ε / 2)| < ε / 2 :=
    fun i => GlobalTheory.T.totally_real_field_dense_embeddings F (fun σ => (if σ = i then 1 else 0) + ε / 2) (ε / 2) (by positivity)
  choose v hv using hex
  have hclose : ∀ σ i : F →+* ℝ, |σ (v i) - if σ = i then 1 else 0| < ε := by
    intro σ i
    have h := abs_lt.mp (hv i σ)
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  have hpos : ∀ σ i : F →+* ℝ, 0 < σ (v i) := by
    intro σ i
    have h := (abs_lt.mp (hv i σ)).1
    split_ifs at h <;> linarith
  obtain ⟨h1, h2⟩ := hW (fun σ i => σ (v i)) hclose
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq i
    have hz : (fun i => (q i : ℝ)) = 0 := h1 _ fun σ => by
      rw [← map_sum_ratSmul σ q v, hq, map_zero]
    have hi : (q i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  have hcardκ : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : Nonempty (F →+* ℝ) := by
    apply Fintype.card_pos_iff.mp
    rw [hcardκ]
    exact Module.finrank_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcardκ
  have hb : ∀ i, b i = v i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨F →+* ℝ, inferInstance, b, fun i σ => ?_, fun x hx hM i => ?_⟩
  · rw [hb]; exact hpos σ i
  · have hrep : ∀ σ : F →+* ℝ, σ x = ∑ i, σ (v i) * ((b.repr x i : ℚ) : ℝ) := by
      intro σ
      rw [← map_sum_ratSmul σ (fun i => b.repr x i) v]
      congr 1
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.sum_congr rfl fun j _ => by rw [hb]
    have hc := h2 (fun i => ((b.repr x i : ℚ) : ℝ))
      (fun σ => by rw [← hrep σ]; exact hx σ)
      (fun σ τ => by rw [← hrep σ, ← hrep τ]; exact hM σ τ) i
    exact_mod_cast hc

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens
