import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAnnihilatorIntegerLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactScaledIntoNhdsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual

noncomputable section

open Matrix ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem exists_unif' : ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r, ?_, hr1⟩
  first
    | exact hr0
    | exact (Valuation.ne_zero_iff _).1 hr0
    | simpa using hr0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pi_lt_mem_nhds {n : ℕ} {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < γ}) ∈ nhds (0 : Fin n → k) :=
  set_pi_mem_nhds Set.finite_univ fun _ _ => (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Prove both required implications or components.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ball_isLat {n : ℕ} (s : kˣ) :
    IsCompact (ball n s : Set (Fin n → k)) ∧ IsOpen (ball n s : Set (Fin n → k)) := by
  have hs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  refine ⟨?_, ?_⟩
  · have e : (ball n s : Set (Fin n → k)) =
        Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (s : k)}) := by
      ext x
      exact Iff.intro (fun h i _ => h i) (fun h i => h i (Set.mem_univ i))
    rw [e]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine (ball n s).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hs) ?_)
    intro x hx i
    exact (hx i (Set.mem_univ i)).le

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem exists_ball_n {n : ℕ} {A : AddSubgroup (Fin n → k)} (hA : IsCompact (A : Set (Fin n → k))) :
    ∃ s : kˣ, A ≤ ball n s := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hU : (ball n (1 : kˣ) : Set (Fin n → k)) ∈ nhds (0 : Fin n → k) := by
    refine Filter.mem_of_superset (pi_lt_mem_nhds (n := n) (γ := 1) one_ne_zero) ?_
    intro x hx i
    have h := hx i (Set.mem_univ i)
    simp only [Set.mem_ofPred_eq] at h
    simpa using h.le
  obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k n _ hA _ hU ϖ hϖ1
  have hpl : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  have hne : valuation k (ϖ ^ l) ≠ 0 := (Valuation.ne_zero_iff _).2 hpl
  refine ⟨Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hpl), fun x hx i => ?_⟩
  have h1 := hl x hx i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Units.val_one, map_one] at h1
  simp only [Units.val_mk0]
  calc valuation k (x i) = (valuation k (ϖ ^ l))⁻¹ * (valuation k (ϖ ^ l) * valuation k (x i)) :=
        (inv_mul_cancel_left₀ hne _).symm
    _ ≤ (valuation k (ϖ ^ l))⁻¹ * 1 := by gcongr
    _ = valuation k ((ϖ ^ l)⁻¹) := by rw [mul_one, map_inv₀]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem ann_isLat_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {A : AddSubgroup (Fin n → k)}
    (hA : IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k))) :
    IsCompact (ann ψ A : Set (Fin n → k)) ∧ IsOpen (ann ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hvs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  have hδ : γ / valuation k (s : k) ≠ 0 := div_ne_zero hγ hvs
  refine ⟨?_, ?_⟩
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
    have hAn : (A : Set (Fin n → k)) ∈ nhds 0 := hA.2.mem_nhds A.zero_mem
    obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k n _ (ball_isLat (n := n) 1).1 _ hAn ϖ hϖ1
    have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have hsub : (ann ψ A : Set (Fin n → k)) ⊆
        {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ x)) = 1} := by
      intro η hη
      show ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ η)) = 1
      intro t ht
      have htb : t ∈ ball n 1 := fun j => by
        simpa using (Valuation.mem_integer_iff _ _).mp (ht j)
      have h1 : ψ (η ⬝ᵥ (ϖ ^ l • t)) = 1 := hη _ (hl t htb)
      rw [dotProduct_smul, smul_eq_mul, dotProduct_comm] at h1
      exact h1
    have hcl : IsClosed (ann ψ A : Set (Fin n → k)) := by
      have e : (ann ψ A : Set (Fin n → k)) = ⋂ a ∈ A, {η : Fin n → k | ψ (η ⬝ᵥ a) = 1} := by
        ext η
        simp only [Set.mem_iInter]
        rfl
      rw [e]
      exact isClosed_biInter fun a _ => isClosed_eq (hψ.comp (by unfold dotProduct; fun_prop)) continuous_const
    exact (GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator k ψ hψ hψ1 n _ hb).1.of_isClosed_subset hcl hsub
  · refine (ann ψ A).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hδ) ?_)
    intro η hη a ha
    apply hball
    have hpos : 0 < valuation k (s : k) := zero_lt_iff.mpr hvs
    show valuation k (∑ j, η j * a j) < γ
    refine Valuation.map_sum_lt _ hγ fun j _ => ?_
    have h1 : valuation k (η j) * valuation k (s : k) < γ := (lt_div_iff₀ hpos).1 (hη j (Set.mem_univ j))
    rw [map_mul]
    have h2 := hs ha j
    exact lt_of_le_of_lt (by gcongr) h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_ball_pf {m : ℕ} {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    ∃ s : kˣ, A ≤ ball (m + 1) s ∧ IsLat (ball (m + 1) s) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  exact ⟨s, hs, ball_isLat s⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem exists_big_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} (D : Set (Fin (m + 1) → k))
    (hD : D ∈ nhds (0 : Fin (m + 1) → k)) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ (ann ψ A₁ : Set (Fin (m + 1) → k)) ⊆ D := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hC := ann_isLat_pf hψ hψ1 (ball_isLat (n := m + 1) (1 : kˣ))
  obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k (m + 1) _ hC.1 D hD ϖ hϖ1
  have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  set u : kˣ := Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hb) with hu
  obtain ⟨s₀, hs₀⟩ := exists_ball_n (n := m + 1) hA₀.1
  obtain ⟨s, h1, h2⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      valuation k (u : k) ≤ valuation k (s : k) := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (u : k)) with h | h
    · exact ⟨u, h, le_rfl⟩
    · exact ⟨s₀, le_rfl, h⟩
  refine ⟨ball (m + 1) s, ball_isLat s, fun x hx i => (hs₀ hx i).trans h1, ?_⟩
  intro η hη
  have hη' : (ϖ ^ l)⁻¹ • η ∈ ann ψ (ball (m + 1) 1) := by
    intro a ha
    have hmem : (ϖ ^ l)⁻¹ • a ∈ ball (m + 1) s := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul]
      have ha' : valuation k (a i) ≤ 1 := by simpa using ha i
      calc valuation k (ϖ ^ l)⁻¹ * valuation k (a i) ≤ valuation k (ϖ ^ l)⁻¹ * 1 := by gcongr
        _ = valuation k (u : k) := by simp [hu]
        _ ≤ _ := h2
    have e := hη _ hmem
    rwa [dotProduct_smul, ← smul_dotProduct] at e
  have := hl _ hη'
  rwa [smul_smul, mul_inv_cancel₀ hb, one_smul] at this

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
