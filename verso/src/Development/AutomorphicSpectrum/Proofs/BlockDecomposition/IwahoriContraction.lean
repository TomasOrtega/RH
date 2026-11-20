import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open ValuativeRel Matrix Topology MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.IwContract

open PositivityTheory.Rg.Tf.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.mem_iwahori]`. Both sides reduce to the same expression.
-/
theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ↔ g ∈ GlobalTheory.SmGL.iwahori F (Fin n) := by
  rw [GlobalTheory.SmGL.mem_iwahori]; rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `(valuation F).map_sum_le fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_mul]`. Conclude with `mul_le_mul' (hA i k) (hB k j)`.
-/
theorem val_mul_entry {A B : Matrix (Fin n) (Fin n) F} {r s : ValueGroupWithZero F}
    (hA : ∀ i j, valuation F (A i j) ≤ r) (hB : ∀ i j, valuation F (B i j) ≤ s) (i j : Fin n) :
    valuation F ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine (valuation F).map_sum_le fun k _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_mul' (hA i k) (hB k j)

/- English proof (translation)
Establish `hv` using `Valuation.integer.integers (valuation F)`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]`. Conclude with `⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => ne_of_lt h⟩`.
-/
theorem residue_eq_zero_iff (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ valuation F (algebraMap 𝒪[F] F x) < 1 := by
  have hv := Valuation.integer.integers (valuation F)
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    hv.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => ne_of_lt h⟩

/- English proof (translation)
Take `⟨⟨h, rfl⟩, -⟩` from `GlobalTheory.SmGL.mem_iwahori.1 hg`. Conclude with `(h.val i j).2`.
-/
theorem val_entry_le_one {g : GL (Fin n) F} (hg : g ∈ GlobalTheory.SmGL.iwahori F (Fin n)) (i j : Fin n) :
    valuation F (g.val i j) ≤ 1 := by
  obtain ⟨⟨h, rfl⟩, -⟩ := GlobalTheory.SmGL.mem_iwahori.1 hg
  exact (h.val i j).2

/- English proof (translation)
Take `⟨h, hh, rfl⟩` from `hg`. Establish `h1` using `(GeneralLinearGroup.det (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) h)).ne_zero`. Rewrite `h1` using `[GeneralLinearGroup.val_det_apply, det_of_upperTriangular (GlobalTheory.SmGL.mem_borel _ |>.1 hh)]`. Establish `h2 : IsLocalRing.residue 𝒪[F] (h.val i i) ≠ 0` using `Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)`. Rewrite `h2` using `[Ne, residue_eq_zero_iff]`.

Conclude with `le_antisymm (h.val i i).2 (not_lt.1 h2)`.
-/
theorem val_diag {g : GL (Fin n) F} (hg : g ∈ GlobalTheory.SmGL.iwahori F (Fin n)) (i : Fin n) :
    valuation F (g.val i i) = 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 := (GeneralLinearGroup.det (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) h)).ne_zero
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular (GlobalTheory.SmGL.mem_borel _ |>.1 hh)] at h1
  have h2 : IsLocalRing.residue 𝒪[F] (h.val i i) ≠ 0 := Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)
  rw [Ne, residue_eq_zero_iff] at h2
  exact le_antisymm (h.val i i).2 (not_lt.1 h2)

/- English proof (translation)
Set `A : Matrix (Fin n) (Fin n) 𝒪[F]` to `fun i j => ⟨M i j, h1 i j⟩`. Establish `hdet : IsUnit A.det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, det_of_upperTriangular]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_ show IsLocalRing.residue 𝒪[F] (A i i) ≠ 0` and prove the remaining obligations. Rewrite using `[Ne, residue_eq_zero_iff]`.

Conclude with `not_lt.2 (h3 i).ge`. Introduce `i l hl show IsLocalRing.residue 𝒪[F] (A i l) = 0`. Conclude with `(residue_eq_zero_iff _).2 (h2 i l hl)`. Use `⟨GeneralLinearGroup.map (algebraMap 𝒪[F] F) (GeneralLinearGroup.mk'' A hdet), GlobalTheory.SmGL.mem_iwahori.2 ⟨⟨_, rfl⟩, fun i j hij => h2 i j hij⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
theorem exists_mem_iwahori (M : Matrix (Fin n) (Fin n) F) (h1 : ∀ i j, valuation F (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → valuation F (M i j) < 1) (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = M := by
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := fun i j => ⟨M i j, h1 i j⟩
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, det_of_upperTriangular]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      show IsLocalRing.residue 𝒪[F] (A i i) ≠ 0
      rw [Ne, residue_eq_zero_iff]
      exact not_lt.2 (h3 i).ge
    · intro i l hl
      show IsLocalRing.residue 𝒪[F] (A i l) = 0
      exact (residue_eq_zero_iff _).2 (h2 i l hl)
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[F] F) (GeneralLinearGroup.mk'' A hdet),
    GlobalTheory.SmGL.mem_iwahori.2 ⟨⟨_, rfl⟩, fun i j hij => h2 i j hij⟩, ?_⟩
  ext i j
  rfl

/- English proof (translation)
Establish `hr : valuation F (ϖ : F) ^ k ≠ 0` using `pow_ne_zero _ ((valuation F).ne_zero_iff.mpr ϖ.ne_zero)`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x hx`. Simplify using `only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff]`.

Use `⟨Units.mk0 _ hr, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hz`. Simplify using `only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]`. Rewrite using `[(valuation F).map_add_eq_of_lt_left (hz.trans hx)]`.

Conclude with `hx`.
-/
theorem isClosed_val_le_pow (ϖ : Fˣ) (k : ℕ) :
    IsClosed {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k} := by
  have hr : valuation F (ϖ : F) ^ k ≠ 0 := pow_ne_zero _ ((valuation F).ne_zero_iff.mpr ϖ.ne_zero)
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hr, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [(valuation F).map_add_eq_of_lt_left (hz.trans hx)]
  exact hx

def Near (r : ValueGroupWithZero F) (c : GL (Fin n) F) : Prop :=
  c ∈ GlobalTheory.SmGL.iwahori F (Fin n) ∧ ∀ i j, i ≠ j → valuation F (c.val i j) ≤ r

/- English proof (translation)
Establish `hlt : a j < a i` using `ha hij`. Take `⟨k, hk⟩ : ∃ k : ℕ, a i - a j = ((k + 1 : ℕ) : ℤ)` from `⟨(a i - a j - 1).toNat, by omega⟩`. Rewrite using `[hk, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, pow_succ]`. Conclude with `mul_le_of_le_one_left' (pow_le_one' hϖ.le k)`.
-/
theorem val_pw_le {ϖ : Fˣ} (hϖ : valuation F (ϖ : F) < 1) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {i j : Fin n} (hij : i < j) :
    valuation F ((ϖ ^ (a i - a j) : Fˣ) : F) ≤ valuation F (ϖ : F) := by
  have hlt : a j < a i := ha hij
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a i - a j = ((k + 1 : ℕ) : ℤ) := ⟨(a i - a j - 1).toNat, by omega⟩
  rw [hk, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, pow_succ]
  exact mul_le_of_le_one_left' (pow_le_one' hϖ.le k)

/- English proof (translation)
Establish `hq : valuation F (ϖ : F) < 1` using `hϖ.1`. Use `set q := valuation F (ϖ : F) with hqdef`. Use `set D : Fin n → F := fun i => c.val i i with hDdef`. Establish `hD : ∀ i, valuation F (D i) = 1` using `val_diag hc.1`. Establish `hD0 : ∀ i, D i ≠ 0` using `fun i h => by`.

Use `hD i` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Establish `hc1 : ∀ i j, valuation F (c.val i j) ≤ 1` using `val_entry_le_one hc.1`. Establish `hlow : ∀ i j, j < i → valuation F (c.val i j) ≤ q` using `fun i j hij => hϖ.2.2 _ ((GlobalTheory.SmGL.mem_iwahori.1 hc.1).2 i j hij)`.

Set `p : Fin n → Fin n → F` to `fun i j => ((ϖ ^ (a i - a j) : Fˣ) : F)`. Establish `hp : ∀ i j, i < j → valuation F (p i j) ≤ q` using `fun i j hij => val_pw_le hq ha hij`. Set `E : Matrix (Fin n) (Fin n) F` to `fun i j => if i < j then p i j * c.val i j / D j else if j < i then -c.val i j / D i else 0`. Set `E' : Matrix (Fin n) (Fin n) F` to `fun i j => if i < j then c.val i j / D j else if j < i then -(p j i * c.val i j) / D i else 0`. Establish `hEu : ∀ i j, i < j → E i j = p i j * c.val i j / D j` using `fun i j h => if_pos h`.

Establish `hEl : ∀ i j, j < i → E i j = -c.val i j / D i` using `fun i j h => by show (if i < j then _ else _) = _`. Rewrite using `[if_neg h.not_gt, if_pos h]`. Establish `hEd : ∀ i, E i i = 0` using `fun i => by show (if i < i then _ else _) = _`. Rewrite using `[if_neg (lt_irrefl i), if_neg (lt_irrefl i)]`. Establish `hE'u : ∀ i j, i < j → E' i j = c.val i j / D j` using `fun i j h => if_pos h`.

Establish `hE'l : ∀ i j, j < i → E' i j = -(p j i * c.val i j) / D i` using `fun i j h => by show (if i < j then _ else _) = _`. Rewrite using `[if_neg h.not_gt, if_pos h]`. Establish `hE'd : ∀ i, E' i i = 0` using `fun i => by show (if i < i then _ else _) = _`. Rewrite using `[if_neg (lt_irrefl i), if_neg (lt_irrefl i)]`. Establish `hq1 : q ≤ 1` using `hq.le`.

Establish `hE : ∀ i j, valuation F (E i j) ≤ q`. Introduce `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[hEu i j h, map_div₀, hD, div_one, map_mul]`. Conclude with `(mul_le_mul' (hp i j h) (hc1 i j)).trans_eq (mul_one _)`.

Rewrite using `[hEd, map_zero]`. Conclude with `zero_le'`. Rewrite using `[hEl i j h, map_div₀, hD, div_one, Valuation.map_neg]`. Conclude with `hlow i j h`. Establish `hE'1 : ∀ i j, valuation F (E' i j) ≤ 1`.

Introduce `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[hE'u i j h, map_div₀, hD, div_one]`. Conclude with `hc1 i j`. Rewrite using `[hE'd, map_zero]`.

Conclude with `zero_le'`. Rewrite using `[hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]`. Conclude with `(mul_le_mul' ((hp j i h).trans hq1) (hc1 i j)).trans_eq (mul_one _)`. Establish `hE'low : ∀ i j, j < i → valuation F (E' i j) < 1`. Introduce `i j h`.

Rewrite using `[hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]`. Conclude with `lt_of_le_of_lt ((mul_le_mul' (hp j i h) (hc1 i j)).trans_eq (mul_one _)) hq`. Establish `one_add : ∀ (G : Matrix (Fin n) (Fin n) F), (∀ i, G i i = 0) → (∀ i j, valuation F (G i j) ≤ 1) → (∀ i j, j < i → valuation F (G i j) < 1) → ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = 1 + G`. Introduce `G h0 h1 h2`. Use `exists_mem_iwahori _ (fun i j => ?_) (fun i j hij => ?_) fun i => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.add_apply]`. Use `Valuation.map_add_le _ ?_ (h1 i j)` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne h]`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij.ne', zero_add]`. Conclude with `h2 i j hij`. Rewrite using `[Matrix.add_apply, h0, add_zero, Matrix.one_apply_eq, map_one]`. Take `⟨m, hm, hmv⟩` from `one_add E hEd (fun i j => (hE i j).trans hq1) (fun i j h => lt_of_le_of_lt (hE i j) hq)`.

Take `⟨m', hm', hm'v⟩` from `one_add E' hE'd hE'1 hE'low`. Establish `hx : diagPow ϖ a * m' = m * diagPow ϖ a`. Apply `Units.ext` to reduce the goal to its premises. Establish `hxv : (diagPow ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : Fˣ) : F)` using `rfl`. Rewrite using `[Units.val_mul, Units.val_mul, hmv, hm'v, hxv]`.

Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply]`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Establish `e : ((ϖ ^ a i : Fˣ) : F) = p i j * ((ϖ ^ a j : Fˣ) : F)` using `by show _ = ((ϖ ^ (a i - a j) : Fˣ) : F) * _`. Rewrite using `[← Units.val_mul, ← _root_.zpow_add]`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h.ne, zero_add, zero_add, hE'u i j h, hEu i j h, e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE'd, hEd]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : ((ϖ ^ a j : Fˣ) : F) = p j i * ((ϖ ^ a i : Fˣ) : F)` using `by show _ = ((ϖ ^ (a j - a i) : Fˣ) : F) * _`. Rewrite using `[← Units.val_mul, ← _root_.zpow_add]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h.ne', zero_add, zero_add, hE'l i j h, hEl i j h, e]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨m, hm, m'⁻¹ * c * m, ⟨mul_mem (mul_mem (inv_mem hm') hc.1) hm, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Take `⟨Dg, hDg⟩ : ∃ Dg : Matrix (Fin n) (Fin n) F, Dg = Matrix.diagonal D` from `⟨_, rfl⟩`. Take `⟨W, hW⟩ : ∃ W : Matrix (Fin n) (Fin n) F, W = c.val * (1 + E) - (1 + E') * Dg` from `⟨_, rfl⟩`. Establish `hval : (m'⁻¹ * c * m).val = Dg + (m'⁻¹).val * W`.

Establish `h1 : (m'⁻¹).val * (1 + E') = 1`. Rewrite using `[← hm'v, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `h2 : (m'⁻¹ * c * m).val = (m'⁻¹).val * (c.val * (1 + E))`. Rewrite using `[Units.val_mul, Units.val_mul, hmv, mul_assoc]`.

Rewrite using `[h2, hW, mul_sub, ← mul_assoc (m'⁻¹).val (1 + E') Dg, h1, one_mul]`. Normalize the expressions using the abelian group laws. Establish `hinv : ∀ i j, valuation F ((m'⁻¹).val i j) ≤ 1` using `val_entry_le_one (inv_mem hm')`. Establish `hC : ∀ i j, valuation F ((c.val - Dg) i j) ≤ r`. Introduce `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[hDg, Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, map_zero]`. Conclude with `zero_le'`. Rewrite using `[hDg, Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, sub_zero]`.

Conclude with `hc.2 i j h`. Establish `hWeq : W = (c.val - Dg) * E + ((c.val - Dg) + Dg * E - E' * Dg)`. Rewrite using `[hW]`. Simplify using `only [mul_add, add_mul, mul_one, one_mul, sub_mul]`. Normalize the expressions using the abelian group laws.

Establish `hWb : ∀ i j, valuation F (W i j) ≤ r * q`. Introduce `i j`. Rewrite using `[hWeq, Matrix.add_apply]`. Apply the tactic sequence `refine Valuation.map_add_le _ (val_mul_entry hC hE i j) ?_`. Rewrite using `[Matrix.sub_apply, Matrix.add_apply, hDg, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Establish `e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j = D i * (p i j * c.val i j / D j)`. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne, sub_zero, hEu i j h, hE'u i j h, div_mul_cancel₀ _ (hD0 j)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul, hD, one_mul, map_div₀, hD, div_one, map_mul, mul_comm r]`.

Conclude with `mul_le_mul' (hp i j h) (hc.2 i j h.ne)`. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_eq, hEd, hE'd]`. Simplify using `[hDdef]`. Establish `e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j = p j i * c.val i j * D j / D i`. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne', sub_zero, hEl i j h, hE'l i j h, mul_div_cancel₀ _ (hD0 i)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_div₀, hD, div_one, map_mul, map_mul, hD, mul_one, mul_comm r]`. Conclude with `mul_le_mul' (hp j i h) (hc.2 i j h.ne')`. Apply the tactic sequence `have hfin := val_mul_entry hinv hWb i j`. Rewrite using `[hval, Matrix.add_apply, hDg, Matrix.diagonal_apply_ne _ hij, zero_add]`.

Simplify using `using hfin`. Rewrite using `[← mul_assoc m, ← hx] group`.
-/
theorem step {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {r : ValueGroupWithZero F} {c : GL (Fin n) F} (hc : Near r c) :
    ∃ m ∈ GlobalTheory.SmGL.iwahori F (Fin n), ∃ c' : GL (Fin n) F, Near (r * valuation F (ϖ : F)) c' ∧
      (diagPow ϖ a * c) * m = m * (diagPow ϖ a * c') := by
  classical
  have hq : valuation F (ϖ : F) < 1 := hϖ.1
  set q := valuation F (ϖ : F) with hqdef
  set D : Fin n → F := fun i => c.val i i with hDdef
  have hD : ∀ i, valuation F (D i) = 1 := val_diag hc.1
  have hD0 : ∀ i, D i ≠ 0 := fun i h => by
    have := hD i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hc1 : ∀ i j, valuation F (c.val i j) ≤ 1 := val_entry_le_one hc.1
  have hlow : ∀ i j, j < i → valuation F (c.val i j) ≤ q := fun i j hij =>
    hϖ.2.2 _ ((GlobalTheory.SmGL.mem_iwahori.1 hc.1).2 i j hij)
  let p : Fin n → Fin n → F := fun i j => ((ϖ ^ (a i - a j) : Fˣ) : F)
  have hp : ∀ i j, i < j → valuation F (p i j) ≤ q := fun i j hij => val_pw_le hq ha hij
  let E : Matrix (Fin n) (Fin n) F := fun i j =>
    if i < j then p i j * c.val i j / D j else if j < i then -c.val i j / D i else 0
  let E' : Matrix (Fin n) (Fin n) F := fun i j =>
    if i < j then c.val i j / D j else if j < i then -(p j i * c.val i j) / D i else 0
  have hEu : ∀ i j, i < j → E i j = p i j * c.val i j / D j := fun i j h => if_pos h
  have hEl : ∀ i j, j < i → E i j = -c.val i j / D i := fun i j h => by
    show (if i < j then _ else _) = _
    rw [if_neg h.not_gt, if_pos h]
  have hEd : ∀ i, E i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hE'u : ∀ i j, i < j → E' i j = c.val i j / D j := fun i j h => if_pos h
  have hE'l : ∀ i j, j < i → E' i j = -(p j i * c.val i j) / D i := fun i j h => by
    show (if i < j then _ else _) = _
    rw [if_neg h.not_gt, if_pos h]
  have hE'd : ∀ i, E' i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hq1 : q ≤ 1 := hq.le
  have hE : ∀ i j, valuation F (E i j) ≤ q := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hEu i j h, map_div₀, hD, div_one, map_mul]
      exact (mul_le_mul' (hp i j h) (hc1 i j)).trans_eq (mul_one _)
    · rw [hEd, map_zero]; exact zero_le'
    · rw [hEl i j h, map_div₀, hD, div_one, Valuation.map_neg]
      exact hlow i j h
  have hE'1 : ∀ i j, valuation F (E' i j) ≤ 1 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hE'u i j h, map_div₀, hD, div_one]
      exact hc1 i j
    · rw [hE'd, map_zero]; exact zero_le'
    · rw [hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]
      exact (mul_le_mul' ((hp j i h).trans hq1) (hc1 i j)).trans_eq (mul_one _)
  have hE'low : ∀ i j, j < i → valuation F (E' i j) < 1 := by
    intro i j h
    rw [hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]
    exact lt_of_le_of_lt ((mul_le_mul' (hp j i h) (hc1 i j)).trans_eq (mul_one _)) hq
  have one_add : ∀ (G : Matrix (Fin n) (Fin n) F), (∀ i, G i i = 0) → (∀ i j, valuation F (G i j) ≤ 1) →
      (∀ i j, j < i → valuation F (G i j) < 1) →
      ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = 1 + G := by
    intro G h0 h1 h2
    refine exists_mem_iwahori _ (fun i j => ?_) (fun i j hij => ?_) fun i => ?_
    · rw [Matrix.add_apply]
      refine Valuation.map_add_le _ ?_ (h1 i j)
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', zero_add]
      exact h2 i j hij
    · rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_eq, map_one]
  obtain ⟨m, hm, hmv⟩ := one_add E hEd (fun i j => (hE i j).trans hq1)
    (fun i j h => lt_of_le_of_lt (hE i j) hq)
  obtain ⟨m', hm', hm'v⟩ := one_add E' hE'd hE'1 hE'low
  have hx : diagPow ϖ a * m' = m * diagPow ϖ a := by
    apply Units.ext
    have hxv : (diagPow ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, hmv, hm'v, hxv]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · have e : ((ϖ ^ a i : Fˣ) : F) = p i j * ((ϖ ^ a j : Fˣ) : F) := by
        show _ = ((ϖ ^ (a i - a j) : Fˣ) : F) * _
        rw [← Units.val_mul, ← _root_.zpow_add]
        simp
      rw [Matrix.one_apply_ne h.ne, zero_add, zero_add, hE'u i j h, hEu i j h, e]
      ring
    · rw [hE'd, hEd]
      ring
    · have e : ((ϖ ^ a j : Fˣ) : F) = p j i * ((ϖ ^ a i : Fˣ) : F) := by
        show _ = ((ϖ ^ (a j - a i) : Fˣ) : F) * _
        rw [← Units.val_mul, ← _root_.zpow_add]
        simp
      rw [Matrix.one_apply_ne h.ne', zero_add, zero_add, hE'l i j h, hEl i j h, e]
      ring
  refine ⟨m, hm, m'⁻¹ * c * m, ⟨mul_mem (mul_mem (inv_mem hm') hc.1) hm, ?_⟩, ?_⟩
  · intro i j hij
    obtain ⟨Dg, hDg⟩ : ∃ Dg : Matrix (Fin n) (Fin n) F, Dg = Matrix.diagonal D := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin n) (Fin n) F, W = c.val * (1 + E) - (1 + E') * Dg := ⟨_, rfl⟩
    have hval : (m'⁻¹ * c * m).val = Dg + (m'⁻¹).val * W := by
      have h1 : (m'⁻¹).val * (1 + E') = 1 := by
        rw [← hm'v, ← Units.val_mul]
        simp
      have h2 : (m'⁻¹ * c * m).val = (m'⁻¹).val * (c.val * (1 + E)) := by
        rw [Units.val_mul, Units.val_mul, hmv, mul_assoc]
      rw [h2, hW, mul_sub, ← mul_assoc (m'⁻¹).val (1 + E') Dg, h1, one_mul]
      abel
    have hinv : ∀ i j, valuation F ((m'⁻¹).val i j) ≤ 1 := val_entry_le_one (inv_mem hm')
    have hC : ∀ i j, valuation F ((c.val - Dg) i j) ≤ r := by
      intro i j
      by_cases h : i = j
      · subst h
        rw [hDg, Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, map_zero]
        exact zero_le'
      · rw [hDg, Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, sub_zero]
        exact hc.2 i j h
    have hWeq : W = (c.val - Dg) * E + ((c.val - Dg) + Dg * E - E' * Dg) := by
      rw [hW]
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul]
      abel
    have hWb : ∀ i j, valuation F (W i j) ≤ r * q := by
      intro i j
      rw [hWeq, Matrix.add_apply]
      refine Valuation.map_add_le _ (val_mul_entry hC hE i j) ?_
      rw [Matrix.sub_apply, Matrix.add_apply, hDg, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rcases lt_trichotomy i j with h | rfl | h
      · have e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j =
            D i * (p i j * c.val i j / D j) := by
          rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne, sub_zero, hEu i j h, hE'u i j h,
            div_mul_cancel₀ _ (hD0 j)]
          ring
        rw [e, map_mul, hD, one_mul, map_div₀, hD, div_one, map_mul, mul_comm r]
        exact mul_le_mul' (hp i j h) (hc.2 i j h.ne)
      · rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, hEd, hE'd]
        simp [hDdef]
      · have e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j =
            p j i * c.val i j * D j / D i := by
          rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne', sub_zero, hEl i j h, hE'l i j h,
            mul_div_cancel₀ _ (hD0 i)]
          ring
        rw [e, map_div₀, hD, div_one, map_mul, map_mul, hD, mul_one, mul_comm r]
        exact mul_le_mul' (hp j i h) (hc.2 i j h.ne')
    have hfin := val_mul_entry hinv hWb i j
    rw [hval, Matrix.add_apply, hDg, Matrix.diagonal_apply_ne _ hij, zero_add]
    simpa using hfin
  · rw [← mul_assoc m, ← hx]
    group

/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x, x = diagPow ϖ a` from `⟨_, rfl⟩`. Rewrite `hγ`, the goal using `[← hx]`. Take `⟨u, hu, w, hw, hγe⟩` from `hγ`. Establish `hu'` using `mem_iwahori_iff.1 hu`. Establish `hw'` using `mem_iwahori_iff.1 hw`.

Establish `hq : valuation F (ϖ : F) < 1` using `hϖ.1`. Take `⟨φ, hφ⟩ : ∃ φ : GL (Fin n) F → GL (Fin n) F, φ = fun m => x⁻¹ * (m⁻¹ * γ * m)` from `⟨_, rfl⟩`. Establish `hφc : Continuous φ`. Rewrite using `[hφ]`. Use `fun_prop`.

Set `S : ℕ → Set (GL (Fin n) F)` to `fun k => {m | m ∈ GlobalTheory.SmGL.iwahori F (Fin n) ∧ Near (valuation F (ϖ : F) ^ k) (φ m)}`. Establish `hdec : ∀ k, S (k + 1) ⊆ S k` using `fun k m hm => ⟨hm.1, hm.2.1, fun i j hij => (hm.2.2 i j hij).trans (pow_le_pow_right_of_le_one' hq.le (Nat.le_succ k))⟩`. Establish `hne : ∀ k, (S k).Nonempty`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Establish `e : φ u = w * u`. Rewrite using `[hφ, hγe]`. Use `group`. Use `⟨u, hu', ?_, fun i j _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `mul_mem hw' hu'`. Rewrite using `[e, pow_zero]`. Conclude with `val_entry_le_one (mul_mem hw' hu') i j`. Consider the case `succ k ih`.

Take `⟨m, hm, hN⟩` from `ih`. Take `⟨m₁, hm₁, c', hc', he⟩` from `step hϖ ha hN`. Rewrite `he` using `[← hx]`. Establish `h0 : x * φ m = m⁻¹ * γ * m`. Rewrite using `[hφ]`.

Use `group`. Establish `e : φ (m * m₁) = c'`. Establish `h1 : (m * m₁)⁻¹ * γ * (m * m₁) = m₁⁻¹ * ((x * φ m) * m₁)`. Rewrite using `[h0]`. Use `group`.

Rewrite using `[hφ]`. Use `show x⁻¹ * ((m * m₁)⁻¹ * γ * (m * m₁)) = c'`. Rewrite using `[h1, he]`. Use `group`. Use `⟨m * m₁, mul_mem hm hm₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, pow_succ]`. Conclude with `hc'`. Establish `hIcl : IsClosed (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F))` using `Subgroup.isClosed_of_isOpen _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori F (Fin n))`. Establish `hcl : ∀ k, IsClosed (S k)`. Introduce `k`.

Establish `e : S k = (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩ (φ ⁻¹' (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩ ⋂ i, ⋂ j, ⋂ _ : i ≠ j, (fun m => (φ m).val i j) ⁻¹' {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k})`. Use extensionality with `m`. Simplify using `only [S, Near, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]`. Rewrite using `[e]`. Use `hIcl.inter ((hIcl.preimage hφc).inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => (isClosed_val_le_pow ϖ k).preimage ?_))` and prove the remaining obligations.

Conclude with `(Units.continuous_val.matrix_elem i j).comp hφc`. Establish `hcomp : IsCompact (S 0)` using `(GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori F (Fin n)).of_isClosed_subset (hcl 0) fun m hm => hm.1`. Take `⟨m, hm⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne hcomp hcl`. Establish `hm' : ∀ k, m ∈ S k` using `Set.mem_iInter.1 hm`. Establish `hoff : ∀ i j, i ≠ j → (φ m).val i j = 0`.

Introduce `i j hij`. Assume the negation of the conclusion as `hne0`. Establish `hv : valuation F ((φ m).val i j) ≠ 0` using `(Valuation.ne_zero_iff _).2 hne0`. Establish `: MulArchimedean (ValueGroupWithZero F)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨k, hk⟩` from `exists_pow_lt₀ hq (Units.mk0 _ hv)`.

Conclude with `absurd ((hm' k).2.2 i j hij) (not_le.2 hk)`. Use `⟨m, mem_iwahori_iff.2 (hm' 0).1, φ m, ⟨(mem_iwahori_iff.2 (hm' 0).2.1).1, hoff⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Use `group`.
-/
theorem contraction {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    (γ : GL (Fin n) F) (hγ : γ ∈ iwDouble F (diagPow ϖ a)) :
    ∃ m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F, ∃ t ∈ torusO F, m⁻¹ * γ * m = diagPow ϖ a * t := by
  obtain ⟨x, hx⟩ : ∃ x, x = diagPow ϖ a := ⟨_, rfl⟩
  rw [← hx] at hγ ⊢
  obtain ⟨u, hu, w, hw, hγe⟩ := hγ
  have hu' := mem_iwahori_iff.1 hu
  have hw' := mem_iwahori_iff.1 hw
  have hq : valuation F (ϖ : F) < 1 := hϖ.1
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin n) F → GL (Fin n) F, φ = fun m => x⁻¹ * (m⁻¹ * γ * m) := ⟨_, rfl⟩
  have hφc : Continuous φ := by
    rw [hφ]
    fun_prop
  let S : ℕ → Set (GL (Fin n) F) := fun k =>
    {m | m ∈ GlobalTheory.SmGL.iwahori F (Fin n) ∧ Near (valuation F (ϖ : F) ^ k) (φ m)}
  have hdec : ∀ k, S (k + 1) ⊆ S k := fun k m hm =>
    ⟨hm.1, hm.2.1, fun i j hij => (hm.2.2 i j hij).trans (pow_le_pow_right_of_le_one' hq.le (Nat.le_succ k))⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      have e : φ u = w * u := by
        rw [hφ, hγe]
        group
      refine ⟨u, hu', ?_, fun i j _ => ?_⟩
      · rw [e]
        exact mul_mem hw' hu'
      · rw [e, pow_zero]
        exact val_entry_le_one (mul_mem hw' hu') i j
    | succ k ih =>
      obtain ⟨m, hm, hN⟩ := ih
      obtain ⟨m₁, hm₁, c', hc', he⟩ := step hϖ ha hN
      rw [← hx] at he
      have h0 : x * φ m = m⁻¹ * γ * m := by
        rw [hφ]
        group
      have e : φ (m * m₁) = c' := by
        have h1 : (m * m₁)⁻¹ * γ * (m * m₁) = m₁⁻¹ * ((x * φ m) * m₁) := by
          rw [h0]
          group
        rw [hφ]
        show x⁻¹ * ((m * m₁)⁻¹ * γ * (m * m₁)) = c'
        rw [h1, he]
        group
      refine ⟨m * m₁, mul_mem hm hm₁, ?_⟩
      rw [e, pow_succ]
      exact hc'
  have hIcl : IsClosed (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) :=
    Subgroup.isClosed_of_isOpen _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori F (Fin n))
  have hcl : ∀ k, IsClosed (S k) := by
    intro k
    have e : S k = (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩
        (φ ⁻¹' (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩
          ⋂ i, ⋂ j, ⋂ _ : i ≠ j, (fun m => (φ m).val i j) ⁻¹'
            {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k}) := by
      ext m
      simp only [S, Near, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
        SetLike.mem_coe]
    rw [e]
    refine hIcl.inter ((hIcl.preimage hφc).inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (isClosed_val_le_pow ϖ k).preimage ?_))
    exact (Units.continuous_val.matrix_elem i j).comp hφc
  have hcomp : IsCompact (S 0) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori F (Fin n)).of_isClosed_subset (hcl 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne hcomp hcl
  have hm' : ∀ k, m ∈ S k := Set.mem_iInter.1 hm
  have hoff : ∀ i j, i ≠ j → (φ m).val i j = 0 := by
    intro i j hij
    by_contra hne0
    have hv : valuation F ((φ m).val i j) ≠ 0 := (Valuation.ne_zero_iff _).2 hne0
    have : MulArchimedean (ValueGroupWithZero F) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨k, hk⟩ := exists_pow_lt₀ hq (Units.mk0 _ hv)
    exact absurd ((hm' k).2.2 i j hij) (not_le.2 hk)
  refine ⟨m, mem_iwahori_iff.2 (hm' 0).1, φ m, ⟨(mem_iwahori_iff.2 (hm' 0).2.1).1, hoff⟩, ?_⟩
  rw [hφ]
  group

/- English proof (translation)
Introduce `F _ _ _ _ n ϖ hϖ a ha γ hγ`. Conclude with `contraction hϖ ha γ hγ`.
-/
theorem e1 : PositivityTheory.Rg.Tf.Loc.E1 := by
  intro F _ _ _ _ n ϖ hϖ a ha γ hγ
  exact contraction hϖ ha γ hγ

end GlobalTheory.CompanionTheory.IwContract
