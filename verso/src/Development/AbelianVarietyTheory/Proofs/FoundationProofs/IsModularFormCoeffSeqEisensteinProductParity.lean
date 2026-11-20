import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Use function extensionality and compare the values at `n`. Unfold `Zm`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Use `split_ifs with hp`. Both sides reduce to the same expression.

Use `push_neg at hp`. Rewrite `hx`, `hy` using `[Nat.mem_divisorsAntidiagonal]`. Establish `hx' : ¬ l ∣ x.1` using `fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)`. Establish `hy' : ¬ l ∣ y.2` using `fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)`. Rewrite using `[h _ _ hx' hy']`.
-/
theorem zmf_congr_cop {k l : ℕ} (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hp
  · rfl
  · push_neg at hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    have hx' : ¬ l ∣ x.1 := fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)
    have hy' : ¬ l ∣ y.2 := fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)
    rw [h _ _ hx' hy']

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zmf_sum_smul {ι : Type*} (s : Finset ι) (k l : ℕ) (u v : ℤ → ℂ) (c : ι → ℂ) (G : ι → ℕ → ℕ → ℂ) :
    Zm k l u v (fun x y => ∑ i ∈ s, c i * G i x y) = ∑ i ∈ s, c i • Zm k l u v (G i) := by
  funext n
  simp only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).1`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1`.
-/
theorem zmf_mf_sum {ι : Type*} (s : Finset ι) (k L : ℕ) (χ : ℤ → ℂ) (g : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, MF k L χ (g i)) : MF k L χ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1

/- English proof (translation)
Introduce `k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `set φ : ℂ := ((l ^ m).totient : ℂ) with hφ`. Establish `hφ0 : φ ≠ 0`. Rewrite using `[hφ]`.

Conclude with `(Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'` after adjusting the coercions. Use `set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc`. Establish `hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ), ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹)`. Introduce `ψ u`. Rewrite using `[MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]`.

Establish `hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w`. Introduce `w`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Simplify using `only [Units.val_inj, mul_ite, mul_zero]`.

Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules. Use `_ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by`. Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]`. Use `_ = ∑ ψ, c ψ * ψ w := by`. Simplify using `only [hc, hinv, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν) (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0))`. Apply `zmf_congr_cop` to reduce the goal to its premises. Introduce `x y hx hy`. Establish `cx : Nat.Coprime x (l ^ m)` using `(Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm`.

Establish `cy : Nat.Coprime y (l ^ m)` using `(Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm`. Use `set ux := ZMod.unitOfCoprime x cx`. Use `set uy := ZMod.unitOfCoprime y cy`. Establish `ex : ((x : ℤ) : ZMod (l ^ m)) = ux` using `by simp [ux, ZMod.coe_unitOfCoprime]`. Establish `ey : ((y : ℤ) : ZMod (l ^ m)) = uy` using `by simp [uy, ZMod.coe_unitOfCoprime]`.

Establish `ex' : (x : ZMod (l ^ m)) = ux` using `by simp [ux, ZMod.coe_unitOfCoprime]`. Establish `ey' : (y : ZMod (l ^ m)) = uy` using `by simp [uy, ZMod.coe_unitOfCoprime]`. Simplify using `only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]`. Rewrite using `[ZMod.inv_coe_unit, ← Units.val_mul, hexp]`. Use `Finset.sum_congr rfl fun ψ _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_mul, ← Units.val_mul]`. Rewrite using `[hquo, zmf_sum_smul]`. Apply `zmf_mf_sum` to reduce the goal to its premises. Introduce `ψ _`. Establish `hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1`.

Introduce `M χ`. Rewrite using `[← map_mul, neg_one_mul, neg_neg, map_one]`. Establish `hh` using `(GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ hN`. Distinguish the cases in `hψ : ψ (-1) = θ (-1)`. Establish `h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0)`.

Take `⟨r, rfl⟩` from `hodd`. Rewrite using `[hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num`. Establish `h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1)`. Rewrite using `[hψ, hν, mul_neg, hsq]`. Evaluate the numerical expressions.

Conclude with `((GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).2.2.1 (c ψ) _ (GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1`. Establish `hc0 : c ψ = 0`. Establish `hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1`. Introduce `M χ`. Use `hsq χ` as an intermediate fact.

Establish `h' : (χ (-1) - 1) * (χ (-1) + 1) = 0` using `by linear_combination this`. Break down `mul_eq_zero.1 h' with h | h` into its components or cases. Use `left`. Take the linear combination `h`. Use `right`.

Take the linear combination `h`. Establish `hprod : θ (-1) * ψ⁻¹ (-1) = -1`. Establish `hi : ψ⁻¹ (-1) = ψ (-1)`. Rewrite using `[MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]`. Rewrite using `[hi]`.

Apply the tactic sequence `rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢`. Apply the tactic sequence `all_goals first | exact absurd rfl hψ | norm_num`. Use `set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS`. Establish `hS' : S = - S`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]`. Establish `: S = 0` using `by linear_combination hS' / 2`.

Simplify using `[hc, ← hS, this]`. Rewrite using `[hc0, zero_smul]`. Conclude with `(GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).1`.
-/
theorem zm_fun_mf : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  intro k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set φ : ℂ := ((l ^ m).totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'
  set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc
  have hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ),
      ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹) := by
    intro ψ u; rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w := by
    intro w
    calc f w = φ⁻¹ * (f w * φ) := by field_simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * (if (u : ZMod (l ^ m)) = w then φ else 0) := by
          congr 1
          simp only [Units.val_inj, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']; simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
      _ = ∑ ψ, c ψ * ψ w := by
          simp only [hc, hinv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_
          ring
  have hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν)
      (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0)) := by
    apply zmf_congr_cop
    intro x y hx hy
    have cx : Nat.Coprime x (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm
    have cy : Nat.Coprime y (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm
    set ux := ZMod.unitOfCoprime x cx
    set uy := ZMod.unitOfCoprime y cy
    have ex : ((x : ℤ) : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey : ((y : ℤ) : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    have ex' : (x : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey' : (y : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    simp only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]
    rw [ZMod.inv_coe_unit, ← Units.val_mul, hexp]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← map_mul, ← Units.val_mul]
  rw [hquo, zmf_sum_smul]
  apply zmf_mf_sum
  intro ψ _
  have hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1 := by
    intro M χ; rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hh := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ hN
  by_cases hψ : ψ (-1) = θ (-1)
  · have h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0) := by
      obtain ⟨r, rfl⟩ := hodd
      rw [hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num
    have h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1) := by
      rw [hψ, hν, mul_neg, hsq]; norm_num
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).2.2.1 (c ψ) _
      (GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1
  · have hc0 : c ψ = 0 := by
      have hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1 := by
        intro M χ
        have := hsq χ
        have h' : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.1 h' with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hprod : θ (-1) * ψ⁻¹ (-1) = -1 := by
        have hi : ψ⁻¹ (-1) = ψ (-1) := by
          rw [MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]
        rw [hi]
        rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢
        all_goals first | exact absurd rfl hψ | norm_num
      set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS
      have hS' : S = - S := by
        calc S = ∑ u : (ZMod (l ^ m))ˣ, f ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * ψ⁻¹ ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) :=
              (Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)).symm
          _ = ∑ u : (ZMod (l ^ m))ˣ, (θ (-1) * ψ⁻¹ (-1)) * (f u * ψ⁻¹ u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]
              ring
          _ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]
      have : S = 0 := by linear_combination hS' / 2
      simp [hc, ← hS, this]
    rw [hc0, zero_smul]
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).1

end GlobalTheory.EisM
