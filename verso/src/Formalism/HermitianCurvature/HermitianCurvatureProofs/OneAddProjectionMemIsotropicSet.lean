import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangularFactorMiddleRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2

variable {k r : ℕ}

/- English proof (translation)
Establish `hb` using `b.isLt`. Use `ext`. Simplify using `only [NFOne.sg, esI, eI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by
  have hb := b.isLt
  ext
  simp only [NFOne.sg, esI, eI]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hb'` using `b.isLt`. Establish `hq : r + k < (esI k r b).val` using `by simp only [esI]; omega`. Establish `hsg : (NFOne.sg k r (esI k r b)).val = b.val` using `by rw [sg_esI]; rfl`. Establish `hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p = (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b)`.

Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]`. Rewrite using `[hcol]`. Distinguish the cases in `hp1 : p.val < r`. Rewrite using `[NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]`. Distinguish the cases in `hp2 : p.val ≤ r + k`.

Rewrite using `[NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]`. Rewrite using `[NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]`. Establish `e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val`. Rewrite using `[Fin.ext_iff]`. Simplify using `only [NFOne.sg, esI]`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h1 : p = esI k r b`. Rewrite using `[if_pos h1, if_pos (e.mp h1)]`. Rewrite using `[if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]`.
-/
theorem pm_col_star (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [if_pos h1, if_pos (e.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]

/- English proof (translation)
Use `⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a, NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]`. Rewrite using `[Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]`.
-/
theorem one_add_projection_mem_isotropic_set (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]

/- English proof (translation)
Take `⟨gU, gX, gz, gW, gS⟩` from `hg`. Take `⟨hU, hX, hz, hW, hS⟩` from `hh`. Establish `col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0`. Introduce `p m hm`. Use `congrFun (gX ⟨m.val, hm⟩) p` as an intermediate fact.

Simplify `this` using `[bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val → ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) → ∀ m, g p m * h m q = if m = q then g p q else 0`. Introduce `p q hp hq m`. Apply the tactic sequence `have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega`. Distinguish the cases in `hm1 : m.val < r`.

Rewrite using `[col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul, if_neg (fun e => by rw [e] at hm1; omega)]`. Establish `tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0`. Introduce `hmq`. Distinguish the cases in `e : m = q`. Substitute `e` using the available equality.

Simplify using `[hmq]`. Simplify using `[hmq, e]`. Distinguish the cases in `hm2 : m.val ≤ r + k`. Break down `hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩` into its components or cases. Conclude with `tail (hW m q hq1 hq2 (by omega))`.

Rewrite using `[gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul, if_neg (fun e => by rw [e] at hm2; omega)]`. Break down `hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩` into its components or cases. Conclude with `tail (hW m q hq1 hq2 (by omega))`. Conclude with `tail (hS m q hq1 (by omega))`. Use `⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Express the relevant statement in the definitionally equal form `gᴴ * Hpk k r * g = Hpk k r at gU`. Express the relevant statement in the definitionally equal form `hᴴ * Hpk k r * h = Hpk k r at hU`. Rewrite using `[Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by`. Simplify using `only [Matrix.mul_assoc], gU, hU]`.

Rewrite using `[← Matrix.mulVec_mulVec, hX, gX]`. Rewrite using `[← Matrix.mulVec_mulVec, hz, gz]`. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`. Conclude with `gW p q hq1 hq2 hp`. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`.

Conclude with `gS p q hq hp`.
-/
private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul,
        if_neg (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul,
            if_neg (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gS p q hq hp

/- English proof (translation)
Conclude with `mul_mem_n0set h1 h2`.
-/
theorem mul_mem_isotropic_unipotent_set (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2

/- English proof (translation)
Establish `hb` using `b.isLt`. Establish `hv : (esI k r b).val = 2 * r + k - b.val` using `rfl`. Establish `hrow : ∀ q : Fin (2 * r + k + 1), Hpk k r (esI k r b) q = if q = eI k r b then 1 else 0`. Introduce `q`. Establish `e : q = eI k r b ↔ q.val = b.val` using `by rw [Fin.ext_iff]; simp only [eI]`.

Distinguish the cases in `h1 : q = eI k r b`. Rewrite using `[if_pos h1]`. Use `e.mp h1` as an intermediate fact. Unfold `Hpk`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`.

Rewrite using `[if_neg h1]`. Use `fun h => h1 (e.mpr h)` as an intermediate fact. Unfold `Hpk`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨-, h2, -⟩; omega)]`. Simplify using `only [herm, bvec, dotProduct, Matrix.mulVec]`.

Rewrite using `[Finset.sum_eq_single (esI k r b)]`. Simplify using `only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul, hrow]`. Simplify using the standard rewrite rules. Introduce `q _ hq`. Simplify using `[Pi.single_apply, hq]`.

Simplify using the standard rewrite rules.
-/
theorem herm_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  have hrow : ∀ q : Fin (2 * r + k + 1), Hpk k r (esI k r b) q = if q = eI k r b then 1 else 0 := by
    intro q
    have e : q = eI k r b ↔ q.val = b.val := by rw [Fin.ext_iff]; simp only [eI]
    by_cases h1 : q = eI k r b
    · rw [if_pos h1]; have := e.mp h1
      unfold Hpk
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]; have := fun h => h1 (e.mpr h)
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨-, h2, -⟩; omega)]
  simp only [herm, bvec, dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul, hrow]
    simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

end N2

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
