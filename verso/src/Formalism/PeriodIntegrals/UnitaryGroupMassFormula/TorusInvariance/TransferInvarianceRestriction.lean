import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.Development
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Simplify using `only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢`. Take `⟨hgU, hgF⟩` from `hg`. Take `⟨hhU, hhF⟩` from `hh`. Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by`.

Simplify using `only [mul_assoc], hgU, hhU]`. Rewrite using `[← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]`.
-/
lemma glev_mul' {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

/- English proof (translation)
Introduce `_ _ _ _ hg _ hh` and use `glev_mul' hg hh`.
-/
theorem transfer_invariance_group_mul : StepGrp := fun _ _ _ _ hg _ hh => glev_mul' hg hh

/- English proof (translation)
Establish `hU : gᴴ * Hpk k r * g = Hpk k r`. Simplify using `only [Glev, UH, Set.mem_setOf_eq] at hg`. Conclude with `hg.1`. Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [mul_assoc], hU, hpk_sq]`.

Rewrite using `[Matrix.inv_eq_left_inv hl]`. Conclude with `⟨mul_eq_one_comm.mp hl, hl⟩`.
-/
lemma glev_unit {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [mul_assoc], hU, hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨mul_eq_one_comm.mp hl, hl⟩

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Rewrite using `[Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]`.
-/
lemma inv_fix {g : Mx k r} (hu : g⁻¹ * g = 1) {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) :
    g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

/- English proof (translation)
Establish `hu` using `glev_unit hg`. Simplify using `only [Glev, UH, Set.mem_setOf_eq] at hg ⊢`. Take `⟨hU, hF⟩` from `hg`. Use `⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := glev_unit hg
  simp only [Glev, UH, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hF⟩ := hg
  refine ⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [hu.1, conjTranspose_one, one_mul, mul_one]

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]`. Establish `h1 : Hpk k r (esI k r a) (eI k r a) = 1`. Simplify using `only [Hpk, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.

Rewrite using `[h1, one_mul]`. Introduce `j _ hj`. Establish `hj' : j.val ≠ a.val` using `fun h => hj (Fin.ext h)`. Establish `hjl` using `j.isLt`. Establish `h0 : Hpk k r (esI k r a) j = 0`.

Simplify using `only [Hpk, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma H_esI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (esI k r a) = w (eI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]`. Establish `h1 : Hpk k r (eI k r a) (esI k r a) = 1`. Simplify using `only [Hpk, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.

Rewrite using `[h1, one_mul]`. Introduce `j _ hj`. Establish `hj' : j.val ≠ 2 * r + k - a.val` using `fun h => hj (Fin.ext h)`. Establish `hjl` using `j.isLt`. Establish `h0 : Hpk k r (eI k r a) j = 0`.

Simplify using `only [Hpk, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma H_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have h1 : Hpk k r (eI k r a) (esI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (eI k r a) j = 0 := by
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hU : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hcol : ∀ l, g l c = bvec c l` using `fun l => by`. Rewrite using `[← congrFun hfix l]`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`. Establish `hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j`.

Introduce `j`. Establish `h1` using `congrFun (congrFun hU c) j`. Rewrite `h1` using `[Matrix.mul_assoc, Matrix.mul_apply]`. Rewrite using `[← h1, Finset.sum_eq_single c]`. Rewrite using `[conjTranspose_apply, hcol]`.

Simplify using `[bvec]`. Introduce `l _ hl`. Rewrite using `[conjTranspose_apply, hcol]`. Simplify using `[bvec, Pi.single_apply, hl]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ c) h`. Establish `key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c`. Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `only [Matrix.mulVec, dotProduct, hrow]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma coord {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hcol : ∀ l, g l c = bvec c l := fun l => by
    rw [← congrFun hfix l]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  have hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j := by
    intro j
    have h1 := congrFun (congrFun hU c) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
    rw [← h1, Finset.sum_eq_single c]
    · rw [conjTranspose_apply, hcol]
      simp [bvec]
    · intro l _ hl
      rw [conjTranspose_apply, hcol]
      simp [bvec, Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  calc (g *ᵥ v) d = (Hpk k r *ᵥ (g *ᵥ v)) c := (hcd _).symm
    _ = (Hpk k r *ᵥ v) c := key
    _ = v d := hcd v

/- English proof (translation)
Establish `hq'` using `q.isLt`. Establish `hi` using `i.isLt`. Distinguish the cases in `h1 : q.val < i.val`. Conclude with `⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩`. Establish `h2 : 2 * r + k - i.val < q.val`.

Assume the negation of the conclusion as `h3`. Conclude with `hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))`. Conclude with `⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩`.
-/
lemma outer {i : Fin (r + 1)} (q : Fin (2 * r + k + 1)) (hq : ∀ c, q ≠ posL k r i c) :
    ∃ a : Fin r, a.val < i.val ∧ (q = eI k r a ∨ q = esI k r a) := by
  have hq' := q.isLt
  have hi := i.isLt
  by_cases h1 : q.val < i.val
  · exact ⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩
  · have h2 : 2 * r + k - i.val < q.val := by
      by_contra h3
      exact hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))
    exact ⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩

/- English proof (translation)
Take `⟨a, ha, hq'⟩` from `outer q hq`. Establish `hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)` using `hg`. Break down `hq' with rfl | rfl` into its components or cases. Conclude with `(hg'.2 a ha).1`. Conclude with `(hg'.2 a ha).2`.
-/
lemma glev_fix_outer {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g *ᵥ bvec q = bvec q := by
  obtain ⟨a, ha, hq'⟩ := outer q hq
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  rcases hq' with rfl | rfl
  · exact (hg'.2 a ha).1
  · exact (hg'.2 a ha).2

/- English proof (translation)
Rewrite using `[← congrFun (glev_fix_outer hg q hq) p]`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`.
-/
lemma glev_col {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (p q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g p q = bvec q p := by
  rw [← congrFun (glev_fix_outer hg q hq) p]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

/- English proof (translation)
Establish `hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)` using `hg`. Take `⟨a, ha, hq'⟩` from `outer q hq`. Break down `hq' with rfl | rfl` into its components or cases. Conclude with `coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v`. Conclude with `coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v`.
-/
lemma glev_row {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) (v : Fin (2 * r + k + 1) → ℂ) : (g *ᵥ v) q = v q := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  obtain ⟨a, ha, hq'⟩ := outer q hq
  rcases hq' with rfl | rfl
  · exact coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v
  · exact coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v

/- English proof (translation)
Rewrite using `[← glev_row hg q hq (bvec p)]`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`.
-/
lemma glev_row' {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q p : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g q p = bvec p q := by
  rw [← glev_row hg q hq (bvec p)]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

/- English proof (translation)
The claim follows from `(Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm`.
-/
lemma sum_posL {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := (Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F
    (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩`.
-/
lemma bvec_posL_outer {i : Fin (r + 1)} (a : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 := ⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩

/- English proof (translation)
Unfold `Nlev at hm`. Simplify using `only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm`. Take `⟨⟨_, hcol, hmid⟩, hG⟩` from `hm`. Unfold `inWb at hz`. Unfold `fvec`.

Use `split_ifs with hi`. Use function extensionality and compare the values at `x`. Rewrite using `[show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]`. Distinguish the cases in `hx : i.val ≤ x.val`.

Rewrite using `[hcol ⟨i.val, hi⟩ x hx]`. Simplify using `[bvec, Pi.single_apply]`. Establish `hout : ∀ c, x ≠ posL k r i c` using `fun c h => hx (by`. Establish `h2` using `congrArg Fin.val h`. Simplify using `only [posL] at h2`.

Use the proof step `omega)`. Rewrite using `[glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : r ≤ x.val`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single x]`. Distinguish the cases in `hxk : x.val ≤ r + k`. Rewrite using `[hmid x x hx hxk hx]`. Simplify using the standard rewrite rules. Rewrite using `[hz x (Or.inr (by omega)), mul_zero]`.

Introduce `j _ hj`. Distinguish the cases in `hjm : r ≤ j.val ∧ j.val ≤ r + k`. Rewrite using `[hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]`. Rewrite using `[hz j (by omega), mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `hout : ∀ c, x ≠ posL k r i c` using `fun c h => hx (by`. Establish `h2` using `congrArg Fin.val h`. Simplify using `only [posL] at h2`. Use the proof step `omega)`.

Conclude with `glev_row hG x hout z`.
-/
lemma n_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} (hz : inWb k r z) {m : Mx k r}
    (hm : m ∈ Nlev k r i) : m *ᵥ fvec k r z i = fvec k r z i := by
  unfold Nlev at hm
  simp only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
  obtain ⟨⟨_, hcol, hmid⟩, hG⟩ := hm
  unfold inWb at hz
  unfold fvec
  split_ifs with hi
  · funext x
    rw [show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]
    by_cases hx : i.val ≤ x.val
    · rw [hcol ⟨i.val, hi⟩ x hx]
      simp [bvec, Pi.single_apply]
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      rw [glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]
  · funext x
    by_cases hx : r ≤ x.val
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hxk : x.val ≤ r + k
        · rw [hmid x x hx hxk hx]
          simp
        · rw [hz x (Or.inr (by omega)), mul_zero]
      · intro j _ hj
        by_cases hjm : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      exact glev_row hG x hout z

/- English proof (translation)
Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Unfold `fvec`. Use `split_ifs with hi`. Conclude with `(hh.2.1 _).1`. Conclude with `hh.2.2`.
-/
lemma h_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {h : Mx k r} (hh : h ∈ UWset k r z) :
    h *ᵥ fvec k r z i = fvec k r z i := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  unfold fvec
  split_ifs with hi
  · exact (hh.2.1 _).1
  · exact hh.2.2

/- English proof (translation)
Introduce `k r z i hz`. Establish `hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i`. Introduce `h hh`. Simplify using `only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢`. Conclude with `⟨hh.1, fun a _ => hh.2.1 a⟩`.

Simplify using `only [Slev, Set.mem_setOf_eq]`. Use `⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩` and prove the remaining obligations. Simplify using `[UWset, UH]`. Simplify using `[Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]`. Introduce and unpack `s ⟨h, hh, m, hm, rfl⟩`.

Establish `hmG : m ∈ Glev k r i`. Unfold `Nlev at hm`. Conclude with `hm.2`. Use `⟨glev_mul' (hUW h hh) hmG, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]`.
-/
theorem transfer_invariance_smooth : StepS := by
  intro k r z i hz
  have hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i := by
    intro h hh
    simp only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢
    exact ⟨hh.1, fun a _ => hh.2.1 a⟩
  simp only [Slev, Set.mem_setOf_eq]
  refine ⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩
  · simp [UWset, UH]
  · simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hmG : m ∈ Glev k r i := by
      unfold Nlev at hm
      exact hm.2
    refine ⟨glev_mul' (hUW h hh) hmG, ?_⟩
    rw [← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]

/- English proof (translation)
Establish `hs' : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Simplify using `only [← Matrix.mul_assoc, hs']`.
-/
lemma herm_uh {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (s *ᵥ v) (s *ᵥ w) = herm (Hpk k r) v w := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [← Matrix.mul_assoc, hs']

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]`. Simplify using `[bvec]`.
-/
lemma herm_col (M : Mx k r) (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ bvec q) w = (star w ᵥ* Hpk k r ᵥ* M) q := by
  unfold herm
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  simp [bvec]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.dotProduct_mulVec]`. Simplify using `[bvec]`.
-/
lemma herm_bv (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = (star w ᵥ* Hpk k r) q := by
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp [bvec]

/- English proof (translation)
Establish `hs' : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma uh_H_inv {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (hu : s * s⁻¹ = 1) :
    Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hs']
    _ = sᴴ * Hpk k r := by rw [mul_assoc (sᴴ * Hpk k r), hu, mul_one]

/- English proof (translation)
Introduce `k r z z' i hz hz'`. Establish `bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) → bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0` using `fun a q hq => bvec_posL_outer a q hq`. Establish `blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t`. Introduce `s t hs`. Use extensionality with `a b`.

Simplify using `only [blk, Matrix.mul_apply]`. Conclude with `sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by show s (posL k r i a) q * t q (posL k r i b) = 0`. Rewrite using `[glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])`. Establish `blk_one : blk i (1 : Mx k r) = 1`. Use extensionality with `a b`.

Simplify using `only [blk, Matrix.one_apply]`. Distinguish the cases in `h : a = b`. Simplify using `[h]`. Rewrite using `[if_neg (fun e => h (posL_inj e)), if_neg h]`. Establish `mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ, (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j)`.

Introduce `s hs v`. Use function extensionality and compare the values at `a`. Simplify using `only [blk, Matrix.mulVec, dotProduct]`. Conclude with `(sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by show s (posL k r i a) q * v q = 0`. Rewrite using `[glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm`.

Establish `vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ, ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j)`. Introduce `t ht x`. Use function extensionality and compare the values at `b`. Simplify using `only [blk, Matrix.vecMul, dotProduct]`. Conclude with `(sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by show x q * t q (posL k r i b) = 0`.

Rewrite using `[glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm`. Establish `hS` using `transfer_invariance_smooth k r z i hz`. Establish `hS'` using `transfer_invariance_smooth k r z' i hz'`. Use `⟨fun s hs g => ?_, fun s' hs' => ?_⟩` and prove the remaining obligations. Take `⟨hsG, hsf⟩` from `hS.2 s hs`.

Establish `hu` using `glev_unit hsG`. Establish `hsU : s ∈ UH (Hpk k r)`. Simplify using `only [Glev, Set.mem_setOf_eq] at hsG`. Conclude with `hsG.1`. Establish `hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i` using `inv_fix hu.2 hsf`.

Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `j`. Simplify using `only [yv]`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]`. Use function extensionality and compare the values at `j`.

Simplify using `only [ybv]`. Use `conv_lhs => rw [← hsf]`. Rewrite using `[← Matrix.mulVec_mulVec, herm_uh hsU]`. Take `⟨hsG, hsf⟩` from `hS'.2 s' hs'`. Establish `hu` using `glev_unit hsG`.

Establish `hiG` using `glev_inv hsG`. Establish `hsU : s' ∈ UH (Hpk k r)`. Establish `h0` using `hsG`. Simplify using `only [Glev, Set.mem_setOf_eq] at h0`. Conclude with `h0.1`.

Use `⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← blk_mul _ _ hsG, hu.1, blk_one]`. Rewrite using `[← blk_mul _ _ hiG, hu.2, blk_one]`. Unfold `xv`. Rewrite using `[mv_blk _ hsG, hsf]`.

Unfold `xbv`. Simplify using `only [herm_bv]`. Rewrite using `[vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]`. Unfold `yv`. Rewrite using `[mv_blk _ hsG]`.

Use function extensionality and compare the values at `j`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]`. Unfold `ybv`. Simplify using `only [herm_col]`. Rewrite using `[vm_blk _ hiG]`.

Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]`.
-/
theorem transfer_invariance_vector : StepVec := by
  intro k r z z' i hz hz'
  have bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) →
      bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 :=
    fun a q hq => bvec_posL_outer a q hq
  have blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t := by
    intro s t hs
    ext a b
    simp only [blk, Matrix.mul_apply]
    exact sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by
      show s (posL k r i a) q * t q (posL k r i b) = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])
  have blk_one : blk i (1 : Mx k r) = 1 := by
    ext a b
    simp only [blk, Matrix.one_apply]
    by_cases h : a = b
    · simp [h]
    · rw [if_neg (fun e => h (posL_inj e)), if_neg h]
  have mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ,
      (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j) := by
    intro s hs v
    funext a
    simp only [blk, Matrix.mulVec, dotProduct]
    exact (sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by
      show s (posL k r i a) q * v q = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm
  have vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ,
      ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j) := by
    intro t ht x
    funext b
    simp only [blk, Matrix.vecMul, dotProduct]
    exact (sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by
      show x q * t q (posL k r i b) = 0
      rw [glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm
  have hS := transfer_invariance_smooth k r z i hz
  have hS' := transfer_invariance_smooth k r z' i hz'
  refine ⟨fun s hs g => ?_, fun s' hs' => ?_⟩
  · obtain ⟨hsG, hsf⟩ := hS.2 s hs
    have hu := glev_unit hsG
    have hsU : s ∈ UH (Hpk k r) := by
      simp only [Glev, Set.mem_setOf_eq] at hsG
      exact hsG.1
    have hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i := inv_fix hu.2 hsf
    constructor
    · funext j
      simp only [yv]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    · funext j
      simp only [ybv]
      conv_lhs => rw [← hsf]
      rw [← Matrix.mulVec_mulVec, herm_uh hsU]
  · obtain ⟨hsG, hsf⟩ := hS'.2 s' hs'
    have hu := glev_unit hsG
    have hiG := glev_inv hsG
    have hsU : s' ∈ UH (Hpk k r) := by
      have h0 := hsG
      simp only [Glev, Set.mem_setOf_eq] at h0
      exact h0.1
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · rw [← blk_mul _ _ hsG, hu.1, blk_one]
    · rw [← blk_mul _ _ hiG, hu.2, blk_one]
    · unfold xv
      rw [mv_blk _ hsG, hsf]
    · unfold xbv
      simp only [herm_bv]
      rw [vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]
    · unfold yv
      rw [mv_blk _ hsG]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]
    · unfold ybv
      simp only [herm_col]
      rw [vm_blk _ hiG]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]

/- English proof (translation)
Introduce `E _ _ k r i D f s' hs' hD hf g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩`. Set `L : Mx k r →L[ℝ] Mx k r` to `LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')`. Establish `hL : ∀ x, L x = x * s'` using `fun _ => rfl`. Use `⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU, hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩` and prove the remaining obligations.

Establish `hx' : x * s' ∈ U` using `by rw [← hL]; exact hx`. Use `show f (x * s') = F (L x)`. Rewrite using `[hL]`. Conclude with `hfF _ hx' (glev_mul' hxG hs')`.
-/
theorem transfer_invariance_restriction : StepRSm := by
  intro E _ _ k r i D f s' hs' hD hf g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩
  let L : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')
  have hL : ∀ x, L x = x * s' := fun _ => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU,
    hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩
  have hx' : x * s' ∈ U := by rw [← hL]; exact hx
  show f (x * s') = F (L x)
  rw [hL]
  exact hfF _ hx' (glev_mul' hxG hs')

end Formalism.FourierDecayAlt.Q.TInvW
