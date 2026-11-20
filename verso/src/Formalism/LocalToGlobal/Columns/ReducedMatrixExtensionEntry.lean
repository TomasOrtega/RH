import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nat

/- English proof (translation)
Unfold `LocE.fPos`. Distinguish the cases in `h : p < k₀`. Rewrite using `[if_pos h, if_pos h]`. Rewrite using `[if_neg h, if_neg h, if_pos hp]`.
-/
theorem framePos_of_lt_dim {k₀ c n p : ℕ} (hp : p < n) : LocE.fPos k₀ c n p = if p < k₀ then p else p + c := by
  unfold LocE.fPos
  by_cases h : p < k₀
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_pos hp]

/- English proof (translation)
Rewrite using `[framePos_of_lt_dim hp]`. Unfold `betaExponentOfRanks`. Distinguish the cases in `h1 : p < k₀`. Rewrite using `[if_pos h1, if_pos h1, if_pos (show p < k₀ + 2 * rS + 1 by omega)]`. Unfold `symIdx`.

Rewrite using `[if_pos h1]`. Rewrite using `[if_neg h1, if_neg h1]`. Distinguish the cases in `h2 : p < k₀ + j`. Rewrite using `[if_pos h2, if_pos (show p + c < k₀ + 2 * rS + 1 by omega)]`. Unfold `symIdx`.

Rewrite using `[if_neg (show ¬ p + c < k₀ by omega)]`. Rewrite using `[if_neg h2, if_neg (show ¬ p + c < k₀ + 2 * rS + 1 by omega), show p + c - (k₀ + 2 * rS + 1) = p - (k₀ + j) by omega]`.
-/
theorem beta_framePos_formula {k₀ rS t j c n p : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) :
    betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) =
      if p < k₀ then p + rS else if p < k₀ + j then (if p + c < k₀ + rS then p + c - k₀ else p + c)
        else k₀ + 2 * rS + 1 + (p - (k₀ + j)) / t := by
  rw [framePos_of_lt_dim hp]
  unfold betaExponentOfRanks
  by_cases h1 : p < k₀
  · rw [if_pos h1, if_pos h1, if_pos (show p < k₀ + 2 * rS + 1 by omega)]
    unfold symIdx
    rw [if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p < k₀ + j
    · rw [if_pos h2, if_pos (show p + c < k₀ + 2 * rS + 1 by omega)]
      unfold symIdx
      rw [if_neg (show ¬ p + c < k₀ by omega)]
    · rw [if_neg h2, if_neg (show ¬ p + c < k₀ + 2 * rS + 1 by omega), show p + c - (k₀ + 2 * rS + 1) = p - (k₀ + j) by omega]

/- English proof (translation)
Establish `a1` using `Nat.zero_le ((p - (k₀ + j)) / t)`. Establish `a2` using `Nat.zero_le ((p' - (k₀ + j)) / t)`. Rewrite `h` using `[beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp']`. Unfold `ocbXAllow`. Apply the tactic sequence `split_ifs at h ⊢ <;> omega`.
-/
theorem not_allowed_of_beta_lt {k₀ rS t j c n p p' : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) (hp' : p' < n)
    (h : betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p') < betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) ∨
      (LocE.fPos k₀ c n p < k₀ ∧ LocE.fPos k₀ c n p' = k₀ + rS)) : ¬ ocbXAllow k₀ rS j t p p' := by
  have a1 := Nat.zero_le ((p - (k₀ + j)) / t)
  have a2 := Nat.zero_le ((p' - (k₀ + j)) / t)
  rw [beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp'] at h
  unfold ocbXAllow
  split_ifs at h ⊢ <;> omega

/- English proof (translation)
Establish `a1` using `Nat.zero_le ((p - (k₀ + j)) / t)`. Establish `a2` using `Nat.zero_le ((p' - (k₀ + j)) / t)`. Rewrite using `[beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp']`. Unfold `ocbXAllow at h`. Apply the tactic sequence `split_ifs at h ⊢ <;> omega`.
-/
theorem beta_lt_of_not_allowed {k₀ rS t j c n p p' : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) (hp' : p' < n) (hne : p ≠ p')
    (h : ¬ ocbXAllow k₀ rS j t p p') :
    betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p') < betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) ∨
      (LocE.fPos k₀ c n p < k₀ ∧ LocE.fPos k₀ c n p' = k₀ + rS) := by
  have a1 := Nat.zero_le ((p - (k₀ + j)) / t)
  have a2 := Nat.zero_le ((p' - (k₀ + j)) / t)
  rw [beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp']
  unfold ocbXAllow at h
  split_ifs at h ⊢ <;> omega

end Nat

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Rewrite using `[ciExtM_castAdd]`. Distinguish the cases in `h : y.1 < n`. Rewrite using `[dif_pos h, Finset.sum_eq_single (⟨y.1, h⟩ : Fin n)]`. Rewrite using `[Pi.single_apply, if_pos (show Fin.castAdd c (⟨y.1, h⟩ : Fin n) = y from Fin.ext rfl), mul_one]`. Introduce `b _ hb`.

Rewrite using `[Pi.single_apply, if_neg (fun h' => hb (Fin.ext (by have := congrArg Fin.val h'; simpa using this))), mul_zero]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Rewrite using `[dif_neg h]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.single_apply, if_neg (fun h' => h (by rw [← h']; simp)), mul_zero]`.
-/
theorem extendedMatrix_mulVec_single {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (y : Fin (n + c)) (l : Fin n) :
    (ciExtM c A).mulVec (Pi.single y 1) (Fin.castAdd c l) = if h : y.1 < n then A l ⟨y.1, h⟩ else 0 := by
  rw [ciExtM_castAdd]
  by_cases h : y.1 < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨y.1, h⟩ : Fin n)]
    · rw [Pi.single_apply, if_pos (show Fin.castAdd c (⟨y.1, h⟩ : Fin n) = y from Fin.ext rfl), mul_one]
    · intro b _ hb
      rw [Pi.single_apply, if_neg (fun h' => hb (Fin.ext (by have := congrArg Fin.val h'; simpa using this))), mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.single_apply, if_neg (fun h' => h (by rw [← h']; simp)), mul_zero]

/- English proof (translation)
Unfold `ob2M`. Rewrite using `[hap]`. Proceed by induction on `y using Fin.addCases with`. Consider the case `left l`. Rewrite using `[extendedMatrix_mulVec_single]`.

Simplify using `only [Fin.val_castAdd]`. Distinguish the cases in `h' : y'.1 < n`. Rewrite using `[dif_pos h', dif_pos ⟨l.2, h'⟩, ciScE_lt _ h', ciScE_lt _ l.2, sub_self, zpow_zero, mul_one]`. Rewrite using `[dif_neg h', zero_mul, redP_zero, dif_neg (fun h => h' h.2), if_neg (fun h => h' (by rw [← h]; simp))]`. Consider the case `right jj`.

Rewrite using `[ciExtM_natAdd, dif_neg (fun h => by simp at h), Pi.single_apply]`. Distinguish the cases in `he : Fin.natAdd n jj = y'`. Substitute `he` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, one_mul, sub_self, zpow_zero, redP_one]`. Rewrite using `[if_neg he, if_neg he, zero_mul, redP_zero]`.
-/
theorem reducedMatrix_blockExtension {n c : ℕ} (G : Matrix (Fin n) (Fin n) E) (ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hap : ∀ v, ρ v = (ciExtM c G).mulVec v)
    (y y' : Fin (n + c)) :
    ob2M P q ρ y y' = if h : y.1 < n ∧ y'.1 < n then redP P (G ⟨y.1, h.1⟩ ⟨y'.1, h.2⟩) else if y = y' then 1 else 0 := by
  unfold ob2M
  rw [hap]
  induction y using Fin.addCases with
  | left l =>
    rw [extendedMatrix_mulVec_single]
    simp only [Fin.val_castAdd]
    by_cases h' : y'.1 < n
    · rw [dif_pos h', dif_pos ⟨l.2, h'⟩, ciScE_lt _ h', ciScE_lt _ l.2, sub_self, zpow_zero, mul_one]
    · rw [dif_neg h', zero_mul, redP_zero, dif_neg (fun h => h' h.2), if_neg (fun h => h' (by rw [← h]; simp))]
  | right jj =>
    rw [ciExtM_natAdd, dif_neg (fun h => by simp at h), Pi.single_apply]
    by_cases he : Fin.natAdd n jj = y'
    · subst he
      rw [if_pos rfl, if_pos rfl, one_mul, sub_self, zpow_zero, redP_one]
    · rw [if_neg he, if_neg he, zero_mul, redP_zero]

/- English proof (translation)
Rewrite using `[← ciEN l.2, basisVec_eq_single (show l.1 < n + c by omega)]`. Both sides reduce to the same expression.
-/
theorem inclusion_single_eq_single {n c : ℕ} (l : Fin n) : Loc.inX E n c (Pi.single l 1) = Pi.single (Fin.castAdd c l) 1 := by
  rw [← ciEN l.2, basisVec_eq_single (show l.1 < n + c by omega)]
  rfl

/- English proof (translation)
Unfold `ob2M`. Simplify using `only [Fin.val_castAdd]`. Rewrite using `[ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one, ← inclusion_single_eq_single, hrg, ciInX_castAdd]`.
-/
theorem reducedMatrix_extension_entry {n c : ℕ} {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hrg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) (l l' : Fin n) :
    ob2M P q r (Fin.castAdd c l) (Fin.castAdd c l') = redP P (g (Pi.single l' 1) l) := by
  unfold ob2M
  simp only [Fin.val_castAdd]
  rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one, ← inclusion_single_eq_single, hrg, ciInX_castAdd]

end Ext

section GrpG

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Introduce `hB j hj w hbar`. Take `⟨hk, hr, hrN, -⟩` from `ranks_frame_inequalities R hB.hm hj`. Establish `hq` using `ciQ_mem w.1`. Establish `hu` using `ciQ_notMem_sq hB.hX hB.hPr w.2`. Establish `hq0` using `ciQ_ne_zero hu`.

Establish `hmS : R.m = 2 * R.rS + 2`. Unfold `Ranks.rS`. Take `⟨a, ha⟩` from `R.m_even`. Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hrr : R.r = R.k + 2 * R.rS + 1`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hcj : cOf R j + j = 2 * R.rS + 1`. Use `hB.hm` as an intermediate fact.

Unfold `cOf`. Use linear arithmetic over natural numbers and integers. Establish `hnj : R.k + j ≤ R.N j`. Unfold `Ranks.N`. Establish `e : j * (R.t + 1) = j * R.t + j` using `by ring`.

Rewrite using `[e]`. Use linear arithmetic over natural numbers and integers. Establish `hJat : Jat (Pr` using `Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by`. Unfold `Jat`. Rewrite using `[if_pos w.2, hB.sharp, if_pos rfl]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, ⟨r, hr', hrg⟩, hred⟩`. Establish `hJ : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j)`. Rewrite using `[← hJat]`. Use `hr'.2` as an intermediate fact.

Simplify `this` using `[MulAut.conj_apply]`. Apply the tactic sequence `have hent : ∀ l l' : Fin (R.N j), hbar.1 l l' = ob2M w.1 (qOf w.1) r (Fin.castAdd _ l) (Fin.castAdd _ l') := fun l l' => by rw [ciEntry hred, reducedMatrix_extension_entry hrg]`. Use `⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩` and prove the remaining obligations. Unfold `ocbM`. Rewrite using `[dif_pos ⟨by omega, by omega⟩, hent]`.

Use `reducedMatrix_parahoric_diag_one hq hu hk hr hJ _ ?_` and prove the remaining obligations. Use `show LocE.fPos R.k (cOf R j) (R.N j) p < R.r`. Rewrite using `[framePos_of_lt_dim (by omega), hrr]`. Apply the tactic sequence `split_ifs <;> omega`. Assume the negation of the conclusion as `hna`.

Apply `hnz` to reduce the goal to its premises. Unfold `ocbM`. Rewrite using `[dif_pos ⟨hp, hp'⟩, hent]`. Break down `beta_lt_of_not_allowed (t := R.t) hcj hp hp' hne hna with h | ⟨h1, h2⟩` into its components or cases. Establish `h' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p', hp'⟩ : Fin (R.N j))).1) < betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p, hp⟩ : Fin (R.N j))).1)`.

Rewrite using `[hrr]`. Conclude with `h`. Conclude with `reducedMatrix_parahoric_blockTriangular hq hu hk hr hJ h'`. Conclude with `reducedMatrix_parahoric_corner_zero hq hu hk hr hJ _ _ h1 h2`. Introduce `hpat`.

Take `⟨G, hG⟩ : ∃ G, G = ciLiftM w.1 hbar.1` from `⟨_, rfl⟩`. Establish `hdet : IsUnit G.det` using `isUnit_iff_ne_zero.2 (by rw [hG]; exact ciLiftM_det_ne hbar)`. Establish `hG1 : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv G hdet`. Establish `hG2 : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul G hdet`. Establish `hE1 : ciExtM (cOf R j) G * ciExtM (cOf R j) G⁻¹ = 1` using `by rw [← ciExtM_mul, hG1, ciExtM_one]`.

Establish `hE2 : ciExtM (cOf R j) G⁻¹ * ciExtM (cOf R j) G = 1` using `by rw [← ciExtM_mul, hG2, ciExtM_one]`. Establish `hGi : ∀ i i', IntAt w.1 (G i i')` using `by rw [hG]; exact ciLiftM_int _`. Establish `hGii : ∀ i i', IntAt w.1 (G⁻¹ i i')` using `by rw [hG]; exact ciLiftM_inv_int hbar`. Establish `hGred : ∀ i i', redP w.1 (G i i') = hbar.1 i i'` using `by rw [hG]; exact ciLiftM_red _`. Establish `hap : ∀ v, ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 v = (ciExtM (cOf R j) G).mulVec v` using `fun v => ciEquiv_apply _ _ hE1 hE2 v`.

Establish `he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j), IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1))`. Introduce `A hA l l'`. Rewrite using `[ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]`. Conclude with `hA _ _`. Establish `hS : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1)` using `ciEquiv_stab (fun v hv => ciExtM_maps hq0 G _ (he G hGi) v hv) (fun v hv => ciExtM_maps hq0 G⁻¹ _ (he G⁻¹ hGii) v hv)`.

Establish `hM` using `reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) G _ hap`. Establish `hJ : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j)`. Use `mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_` and prove the remaining obligations. Introduce `y y' hlt`. Rewrite using `[hM]`.

Use `split_ifs with h1 h2`. Rewrite using `[hGred]`. Assume the negation of the conclusion as `hnz`. Establish `hne : y.1 ≠ y'.1` using `fun he' => by`. Establish `hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) < betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1)` using `hlt`.

Rewrite `hlt'` using `[he']`. Conclude with `lt_irrefl _ hlt'`. Establish `hall` using `hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)`. Use `not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall` and prove the remaining obligations. Rewrite using `[← hrr]`.

Conclude with `hlt`. Substitute `h2` using the available equality. Conclude with `absurd hlt (lt_irrefl _)`. Both sides reduce to the same expression. Introduce `y hy`.

Rewrite using `[hM]`. Use `split_ifs with h1 h2`. Rewrite using `[hGred]`. Establish `hyk : y.1 < R.k + j`. Rewrite `hy` using `[framePos_of_lt_dim h1.1, hrr]`.

Apply the tactic sequence `split_ifs at hy <;> omega`. Establish `h3` using `hpat.1 y.1 hyk`. Unfold `ocbM at h3`. Rewrite `h3` using `[dif_pos ⟨h1.1, h1.1⟩]`. Conclude with `h3`.

Both sides reduce to the same expression. Conclude with `absurd rfl h2`. Introduce `y y' hy hy'`. Rewrite using `[hM]`. Use `split_ifs with h1 h2`.

Rewrite using `[hGred]`. Assume the negation of the conclusion as `hnz`. Establish `hne : y.1 ≠ y'.1`. Introduce `he'`. Rewrite `hy` using `[he']`.

Use linear arithmetic over natural numbers and integers. Establish `hall` using `hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)`. Conclude with `not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall`. Substitute `h2` using the available equality. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Use `⟨ciEquiv G G⁻¹ hG1 hG2, ⟨ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2, Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction G G⁻¹ hE1 hE2, Subgroup.mem_comap.2 ?_⟩, fun x => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Simplify `hJ` using `[MulAut.conj_apply, hJat]`. Rewrite using `[hap, ciEquiv_apply, ciExtM_inX]`. Use function extensionality and compare the values at `l`.

Establish `hx'` using `(ciMem_stdAt w.1 x).1 hx`. Simplify using `only [redV, ciEquiv_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[redP_sum _ _ (fun l' _ => (hGi _ _).mul (hx' _))]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[reduction_mul (hGi _ _) (hx' _), hGred]`.
-/
theorem ocbGrpGLoc_holds (m2 : ℕ) : OcbGrpGLoc Ch sel mu cst m2 := by
  intro hB j hj w hbar
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm hj
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr w.2
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hrr : R.r = R.k + 2 * R.rS + 1 := by
    unfold Ranks.r
    omega
  have hcj : cOf R j + j = 2 * R.rS + 1 := by
    have := hB.hm
    unfold cOf
    omega
  have hnj : R.k + j ≤ R.N j := by
    unfold Ranks.N
    have e : j * (R.t + 1) = j * R.t + j := by ring
    rw [e]
    omega
  have hJat : Jat (Pr := Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat
    rw [if_pos w.2, hB.sharp, if_pos rfl]
  constructor
  · rintro ⟨g, ⟨r, hr', hrg⟩, hred⟩
    have hJ : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
      rw [← hJat]
      have := hr'.2
      simpa [MulAut.conj_apply] using this
    have hent : ∀ l l' : Fin (R.N j), hbar.1 l l' = ob2M w.1 (qOf w.1) r (Fin.castAdd _ l) (Fin.castAdd _ l') :=
      fun l l' => by rw [ciEntry hred, reducedMatrix_extension_entry hrg]
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · unfold ocbM
      rw [dif_pos ⟨by omega, by omega⟩, hent]
      refine reducedMatrix_parahoric_diag_one hq hu hk hr hJ _ ?_
      show LocE.fPos R.k (cOf R j) (R.N j) p < R.r
      rw [framePos_of_lt_dim (by omega), hrr]
      split_ifs <;> omega
    · by_contra hna
      apply hnz
      unfold ocbM
      rw [dif_pos ⟨hp, hp'⟩, hent]
      rcases beta_lt_of_not_allowed (t := R.t) hcj hp hp' hne hna with h | ⟨h1, h2⟩
      · have h' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p', hp'⟩ : Fin (R.N j))).1) <
            betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p, hp⟩ : Fin (R.N j))).1) := by
          rw [hrr]
          exact h
        exact reducedMatrix_parahoric_blockTriangular hq hu hk hr hJ h'
      · exact reducedMatrix_parahoric_corner_zero hq hu hk hr hJ _ _ h1 h2
  · intro hpat
    obtain ⟨G, hG⟩ : ∃ G, G = ciLiftM w.1 hbar.1 := ⟨_, rfl⟩
    have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 (by rw [hG]; exact ciLiftM_det_ne hbar)
    have hG1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
    have hG2 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
    have hE1 : ciExtM (cOf R j) G * ciExtM (cOf R j) G⁻¹ = 1 := by rw [← ciExtM_mul, hG1, ciExtM_one]
    have hE2 : ciExtM (cOf R j) G⁻¹ * ciExtM (cOf R j) G = 1 := by rw [← ciExtM_mul, hG2, ciExtM_one]
    have hGi : ∀ i i', IntAt w.1 (G i i') := by rw [hG]; exact ciLiftM_int _
    have hGii : ∀ i i', IntAt w.1 (G⁻¹ i i') := by rw [hG]; exact ciLiftM_inv_int hbar
    have hGred : ∀ i i', redP w.1 (G i i') = hbar.1 i i' := by rw [hG]; exact ciLiftM_red _
    have hap : ∀ v, ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 v = (ciExtM (cOf R j) G).mulVec v :=
      fun v => ciEquiv_apply _ _ hE1 hE2 v
    have he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j),
        IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1)) := by
      intro A hA l l'
      rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
      exact hA _ _
    have hS : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈
        stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) :=
      ciEquiv_stab (fun v hv => ciExtM_maps hq0 G _ (he G hGi) v hv) (fun v hv => ciExtM_maps hq0 G⁻¹ _ (he G⁻¹ hGii) v hv)
    have hM := reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) G _ hap
    have hJ : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈
        LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
      refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_
      · intro y y' hlt
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          by_contra hnz
          have hne : y.1 ≠ y'.1 := fun he' => by
            have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) <
                betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1) := hlt
            rw [he'] at hlt'
            exact lt_irrefl _ hlt'
          have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
          refine not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall
          rw [← hrr]
          exact hlt
        · subst h2
          exact absurd hlt (lt_irrefl _)
        · rfl
      · intro y hy
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          have hyk : y.1 < R.k + j := by
            rw [framePos_of_lt_dim h1.1, hrr] at hy
            split_ifs at hy <;> omega
          have h3 := hpat.1 y.1 hyk
          unfold ocbM at h3
          rw [dif_pos ⟨h1.1, h1.1⟩] at h3
          exact h3
        · rfl
        · exact absurd rfl h2
      · intro y y' hy hy'
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          by_contra hnz
          have hne : y.1 ≠ y'.1 := by
            intro he'
            rw [he'] at hy
            omega
          have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
          exact not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall
        · subst h2
          omega
        · rfl
    refine ⟨ciEquiv G G⁻¹ hG1 hG2, ⟨ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2,
      Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction G G⁻¹ hE1 hE2, Subgroup.mem_comap.2 ?_⟩, fun x => ?_⟩, fun x hx => ?_⟩
    · simpa [MulAut.conj_apply, hJat] using hJ
    · rw [hap, ciEquiv_apply, ciExtM_inX]
    · funext l
      have hx' := (ciMem_stdAt w.1 x).1 hx
      simp only [redV, ciEquiv_apply, Matrix.mulVec, dotProduct]
      rw [redP_sum _ _ (fun l' _ => (hGi _ _).mul (hx' _))]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [reduction_mul (hGi _ _) (hx' _), hGred]

end GrpG

end Formalism.L2.Col
