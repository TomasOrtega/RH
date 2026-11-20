import Mathlib
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionStStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypothesesStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA

noncomputable section

namespace GlobalTheory.LeviCut

/- English proof (translation)
Unfold `eV`. Rewrite using `[dif_pos ⟨a.2, b.2⟩]`. Both sides reduce to the same expression.
-/
theorem eV_coe {N : ℕ} (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    (eV N ν a b x : MvPolynomial (Fin N × Fin N) ℚ) = LR.der N N a b x := by
  unfold eV
  rw [dif_pos ⟨a.2, b.2⟩]
  rfl

/- English proof (translation)
Take `⟨T, hT1, hT2, hT3, hT4⟩` from `hL p q ν hν c₁ c₂ h₁ h₂`. Take `⟨hrel, hspan, hdom, hst1, hst2⟩` from `hN (p + q) ν hν`. Take `⟨hrel', hbdd'⟩` from `hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan`. Use `set e := eV (p + q) ν with he`. Use `set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀`.

Establish `hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0` using `hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by`. Simplify using `only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]`. Rewrite using `[hT1 c hc d hd hcd, sub_self])`. Set `v : dualWeyl ℚ (p + q) (p + q) ν` to `⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩`. Set `φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ` to `{ toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) map_add' := fun x y => LR.fock_add_right _ _ _ map_smul' := fun c x => LR.fock_smul_right _ _ _ }`.

Establish `hwz : ∀ c : Fin (p + q), wtZ ν c = ν c` using `fun c => by simp [wtZ]`. Establish `hv : IsWt (p + q) e (wtZ ν) v`. Introduce `c hc`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v`.

Establish `h2` using `(LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩`. Establish `h3` using `hwz ⟨c, hc⟩`. Simplify using `only at h1 h3`. Rewrite using `[he, h1, h3]`. Simplify using `using h2`.

Establish `hsc` using `hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by`. Establish `hi : i < p + q` using `hij.trans hj`. Establish `hr` using `LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij`. Establish `h3` using `hwz ⟨i, hi⟩`. Establish `h4` using `hwz ⟨j, hj⟩`.

Simplify using `only at h3 h4`. Use `⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr`. Establish `h1` using `eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x`. Express the relevant statement in the definitionally equal form `fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0`.

Simplify using `only at h1`. Rewrite using `[h1, ← LR.fock_der, hr]`. Simplify using `using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)`. Rewrite using `[h3, h4]`. Conclude with `hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)` after adjusting the coercions.

Rewrite using `[h3, h4]`. Conclude with `hK _ _) hT3` after adjusting the coercions. Use `set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz`. Establish `hone : (z : ℚ) • S₀ = 1`. Use `hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_` and prove the remaining obligations.

Use `hinv c hc d hd` as an intermediate fact. Simplify using `only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this`. Rewrite using `[mul_smul_comm, smul_mul_assoc, ← he, this]`. Express the relevant statement in the definitionally equal form `φ (((z : ℚ) • S₀) v) = _`. Rewrite using `[LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]`.

Conclude with `hT4`. Introduce `x hx`. Set `x' : dualWeyl ℚ (p + q) (p + q) ν` to `⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩`. Establish `hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν)` using `⟨x, hx, rfl⟩`. Establish `h5` using `Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')`.

Rewrite `h5` using `[smul_comm, ← hS₀]`. Establish `h6 : z • S₀ x' = x'`. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]`. Both sides reduce to the same expression. Rewrite `h5` using `[h6]`.

Take `⟨y, hy, hyx⟩` from `h5`. Establish `h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x`. Apply `map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `intQ _ _ y = intQ _ _ _`. Rewrite using `[hyx, map_smul, map_smul]`.

Both sides reduce to the same expression. Conclude with `h7 ▸ hy`.
-/
theorem cut_incl (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ K w Λ : ℕ)
    (h₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)),
      (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (h₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
      (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (hK : ∀ i j, ν i ≤ ν j + K) (hw' : K + (p + q) ≤ w + 1)
    (hΛ : ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) :
    ∀ x ∈ dualWeyl ℤ (p + q) (p + q) ν, ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x ∈ weyl ℤ (p + q) (p + q) le_rfl ν := by
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hL p q ν hν c₁ c₂ h₁ h₂
  obtain ⟨hrel, hspan, hdom, hst1, hst2⟩ := hN (p + q) ν hν
  obtain ⟨hrel', hbdd'⟩ := hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan
  set e := eV (p + q) ν with he
  set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀
  have hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0 :=
    hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hT1 c hc d hd hcd, sub_self])
  let v : dualWeyl ℚ (p + q) (p + q) ν := ⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩
  let φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ :=
    { toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
      map_add' := fun x y => LR.fock_add_right _ _ _
      map_smul' := fun c x => LR.fock_smul_right _ _ _ }
  have hwz : ∀ c : Fin (p + q), wtZ ν c = ν c := fun c => by simp [wtZ]
  have hv : IsWt (p + q) e (wtZ ν) v := by
    intro c hc
    apply Subtype.ext
    have h1 := eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v
    have h2 := (LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩
    have h3 := hwz ⟨c, hc⟩
    simp only at h1 h3
    rw [he, h1, h3]
    simpa using h2
  have hsc := hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by
    have hi : i < p + q := hij.trans hj
    have hr := LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij
    have h3 := hwz ⟨i, hi⟩
    have h4 := hwz ⟨j, hj⟩
    simp only at h3 h4
    refine ⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩
    · exact (eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr
    · have h1 := eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x
      change fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
      simp only at h1
      rw [h1, ← LR.fock_der, hr]
      simpa using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    · rw [h3, h4]; exact_mod_cast hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)
    · rw [h3, h4]; exact_mod_cast hK _ _) hT3
  set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz
  have hone : (z : ℚ) • S₀ = 1 := by
    refine hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_
    · have := hinv c hc d hd
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [mul_smul_comm, smul_mul_assoc, ← he, this]
    · change φ (((z : ℚ) • S₀) v) = _
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]
      exact hT4
  intro x hx
  let x' : dualWeyl ℚ (p + q) (p + q) ν := ⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩
  have hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν) := ⟨x, hx, rfl⟩
  have h5 := Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')
  rw [smul_comm, ← hS₀] at h5
  have h6 : z • S₀ x' = x' := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]; rfl
  rw [h6] at h5
  obtain ⟨y, hy, hyx⟩ := h5
  have h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x := by
    apply map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)
    change intQ _ _ y = intQ _ _ _
    rw [hyx, map_smul, map_smul]
    rfl
  exact h7 ▸ hy

/- English proof (translation)
Introduce `N lam hlam l hl lo w hU a ha`. Take `⟨b, rfl⟩` from `Nat.exists_eq_add_of_le ha`. Establish `hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l = exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l` using `by rintro c rfl; rfl`. Rewrite using `[hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]`. Establish `hA1 : Antitone (LD.res a lam)` using `fun i j hij => hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)`.

Establish `hA2 : Antitone (LD.res b (fun i => lam (a + i)))` using `fun i j hij => hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)`. Take `⟨m₁, hm₁, h₁⟩` from `exact_z_specialization a a le_rfl _ hA1 l hl`. Take `⟨m₂, hm₂, h₂⟩` from `exact_z_specialization b b le_rfl _ hA2 l hl`. Take `⟨m, hm, hden⟩` from `hD l w hl`. Establish `hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i` using `fun i j _ => by`.

Establish `h1` using `(hU i i.2).2`. Establish `h2` using `(hU j j.2).1`. Simplify using `only [UnitNormBounds.UN] at h1 h2`. Use linear arithmetic over natural numbers and integers. Establish `hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b))` using `fun i j => by`.

Establish `hpos : 0 < a + b` using `lt_of_le_of_lt (Nat.zero_le _) i.2`. Establish `h1` using `hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])`. Establish `h2` using `hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])`. Establish `h3` using `hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)`. Simplify using `only [LD.res] at h1 h2 h3 ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1`. Break down `Nat.eq_zero_or_pos (a + b) with h0 | hpos` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])`.

Establish `h2` using `hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])`. Simplify using `only [LD.res] at h1 h2`. Use linear arithmetic over natural numbers and integers. Establish `key` using `cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden`. Use `Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Introduce `h`. Break down `(Nat.Prime.dvd_mul hl).1 h with h | h` into its components or cases. Break down `(Nat.Prime.dvd_mul hl).1 h with h | h` into its components or cases. Conclude with `hm₁ h`. Conclude with `hm₂ h`.

Conclude with `hm (hl.dvd_of_dvd_pow h)`. Use `key x hx using 3` and compare the differences between its conclusion and the goal. Rewrite using `[pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ExCut₂ (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (hD : BetaDen) : Formalism.CohomologicalDescent.E.ExCut := by
  intro N lam hlam l hl lo w hU a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l =
      exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l := by rintro c rfl; rfl
  rw [hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]
  have hA1 : Antitone (LD.res a lam) := fun i j hij =>
    hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)
  have hA2 : Antitone (LD.res b (fun i => lam (a + i))) := fun i j hij =>
    hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)
  obtain ⟨m₁, hm₁, h₁⟩ := exact_z_specialization a a le_rfl _ hA1 l hl
  obtain ⟨m₂, hm₂, h₂⟩ := exact_z_specialization b b le_rfl _ hA2 l hl
  obtain ⟨m, hm, hden⟩ := hD l w hl
  have hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i := fun i j _ => by
    have h1 := (hU i i.2).2
    have h2 := (hU j j.2).1
    simp only [UnitNormBounds.UN] at h1 h2
    omega
  have hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b)) := fun i j => by
    have hpos : 0 < a + b := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
    have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])
    have h3 := hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)
    simp only [LD.res] at h1 h2 h3 ⊢
    omega
  have hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · omega
    · have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
      have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])
      simp only [LD.res] at h1 h2
      omega
  have key := cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden
  refine Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · exact hm₁ h
      · exact hm₂ h
    · exact hm (hl.dvd_of_dvd_pow h)
  · convert key x hx using 3
    rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]
    ring

/- English proof (translation)
The claim follows from `ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two GlobalTheory.T.rank_one_projector_weight_zero_invariance GlobalTheory.T.rank_two_consecutive_projector_invariance) GlobalTheory.T.adjoint_action_endomorphism_weight_bound (GlobalTheory.T.projectorGridScalar_of_projectorScalar …`.
-/
theorem exCut : Formalism.CohomologicalDescent.E.ExCut :=
  ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two GlobalTheory.T.rank_one_projector_weight_zero_invariance GlobalTheory.T.rank_two_consecutive_projector_invariance) GlobalTheory.T.adjoint_action_endomorphism_weight_bound (GlobalTheory.T.projectorGridScalar_of_projectorScalar GlobalTheory.T.projector_value_highest_weight_vector) GlobalTheory.T.projector_grid_denominator_bound
    GlobalTheory.T.dualWeylModuleStructureGl_proof GlobalTheory.T.dualWeylWeightSpreadBound_proof GlobalTheory.T.dualWeyl_schur_endomorphism
    (GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses (GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable) GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal GlobalTheory.T.dualWeyl_restriction_rowOperators) GlobalTheory.T.beta_integral_denominator_bound

end GlobalTheory.LeviCut
