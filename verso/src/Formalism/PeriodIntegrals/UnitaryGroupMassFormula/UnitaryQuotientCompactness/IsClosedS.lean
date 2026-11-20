import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Establish `hc : Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => gᴴ * Hpk k r * g` using `((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `isClosed_eq hc continuous_const`.
-/
lemma isClosed_UH : IsClosed (UH (Hpk k r)) := by
  have hc : Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => gᴴ * Hpk k r * g :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

/- English proof (translation)
Establish `e : Nset k r = UH (Hpk k r) ∩ ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1), {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0}`. Use extensionality with `g`. Rewrite using `[mem_Nset_iff]`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Use `isClosed_UH.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : j.val ≤ r + k ∧ min j.val r ≤ i.val`. Establish `: {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} = {g | g i j = if i = j then 1 else 0}`. Use extensionality with `g`.

Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨fun h => h hp.1 hp.2, fun h _ _ => h⟩`. Rewrite using `[this]`. Conclude with `isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const`. Establish `: {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} = Set.univ`.

Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Introduce `h1 h2`. Conclude with `absurd ⟨h1, h2⟩ hp`. Rewrite using `[this]`.

Conclude with `isClosed_univ`.
-/
lemma isClosed_N : IsClosed (Nset k r) := by
  have e : Nset k r = UH (Hpk k r) ∩ ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
      {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} := by
    ext g
    rw [mem_Nset_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_UH.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  by_cases hp : j.val ≤ r + k ∧ min j.val r ≤ i.val
  · have : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        {g | g i j = if i = j then 1 else 0} := by
      ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hp.1 hp.2, fun h _ _ => h⟩
    rw [this]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} = Set.univ := by
      ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hp
    rw [this]; exact isClosed_univ

/- English proof (translation)
Take `⟨h, hh, n, hn, rfl⟩` from `hg`. Conclude with `mul_mem_UH hh.1 hn.1`.
-/
lemma S_sub_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Sset k r z) :
    g ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, n, hn, rfl⟩ := hg
  exact mul_mem_UH hh.1 hn.1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, n, hn, rfl⟩`. Use `⟨h, hh, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]`. Conclude with `hn`.

Introduce and unpack `⟨h, hh, hn⟩`. Use `⟨h, hh, _, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]`.
-/
lemma mem_S_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, Hpk k r * hᴴ * Hpk k r * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, n, hn, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]; exact hn
  · rintro ⟨h, hh, hn⟩
    refine ⟨h, hh, _, hn, ?_⟩
    rw [← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]

/- English proof (translation)
Use `haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK`. Use `set C : Set (UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := {p | Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2 ∈ Nset k r}`. Establish `hC : IsClosed C`. Establish `hc : Continuous fun p : UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2` using `((continuous_const.matrix_mul ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose)).matrix_mul continuous_const).matrix_mul continuous_snd`. Conclude with `isClosed_N.preimage hc`.

Establish `e : Sset k r z = Prod.snd '' C`. Use extensionality with `g`. Rewrite using `[mem_S_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, hn⟩`.

Conclude with `⟨(⟨h, hh⟩, g), hn, rfl⟩`. Introduce and unpack `⟨⟨h, g'⟩, hn, rfl⟩`. Conclude with `⟨h.1, h.2, hn⟩`. Rewrite using `[e]`. Conclude with `isClosedMap_snd_of_compactSpace C hC`.
-/
lemma isClosed_S (hK : IsCompact (UWset k r z)) : IsClosed (Sset k r z) := by
  haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
  set C : Set (UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    {p | Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2 ∈ Nset k r}
  have hC : IsClosed C := by
    have hc : Continuous fun p : UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2 :=
      ((continuous_const.matrix_mul
        ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose)).matrix_mul continuous_const).matrix_mul
        continuous_snd
    exact isClosed_N.preimage hc
  have e : Sset k r z = Prod.snd '' C := by
    ext g
    rw [mem_S_iff]
    constructor
    · rintro ⟨h, hh, hn⟩; exact ⟨(⟨h, hh⟩, g), hn, rfl⟩
    · rintro ⟨⟨h, g'⟩, hn, rfl⟩; exact ⟨h.1, h.2, hn⟩
  rw [e]
  exact isClosedMap_snd_of_compactSpace C hC

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_mem_UW, 1, (nilpotent_subgroup k r).1, (Matrix.one_mul 1).symm⟩`.
-/
lemma one_mem_S : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z :=
  ⟨1, one_mem_UW, 1, (nilpotent_subgroup k r).1, (Matrix.one_mul 1).symm⟩

/- English proof (translation)
Take `⟨h1, hh1, n1, hn1, rfl⟩` from `ha`. Take `⟨h2, hh2, n2, hn2, rfl⟩` from `hb`. Establish `hi2` using `inv_mem_UW hh2`. Establish `hc : h2⁻¹ * n1 * h2 ∈ Nset k r`. Use `uw_conj_N hi2 hn1` as an intermediate fact.

Rewrite `this` using `[inv_inv_UH hh2.1]`. Then use the resulting hypothesis. Use `⟨h1 * h2, mul_mem_UW hh1 hh2, h2⁻¹ * n1 * h2 * n2, (nilpotent_subgroup k r).2.1 _ hc _ hn2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_UH hh2.1, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = h1 * h2 * (h2⁻¹ * n1 * h2 * n2) := by simp only [Matrix.mul_assoc]`.
-/
lemma mul_mem_S {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) : a * b ∈ Sset k r z := by
  obtain ⟨h1, hh1, n1, hn1, rfl⟩ := ha
  obtain ⟨h2, hh2, n2, hn2, rfl⟩ := hb
  have hi2 := inv_mem_UW hh2
  have hc : h2⁻¹ * n1 * h2 ∈ Nset k r := by
    have := uw_conj_N hi2 hn1; rwa [inv_inv_UH hh2.1] at this
  refine ⟨h1 * h2, mul_mem_UW hh1 hh2, h2⁻¹ * n1 * h2 * n2, (nilpotent_subgroup k r).2.1 _ hc _ hn2, ?_⟩
  calc h1 * n1 * (h2 * n2) = h1 * (h2 * h2⁻¹) * n1 * h2 * n2 := by
        rw [mul_inv_UH hh2.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = h1 * h2 * (h2⁻¹ * n1 * h2 * n2) := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Use `⟨?_, mul_inv_UH (S_sub_UH ha)⟩` and prove the remaining obligations. Take `⟨h, hh, n, hn, rfl⟩` from `ha`. Establish `hi` using `inv_mem_UW hh`. Establish `hni : n⁻¹ ∈ Nset k r` using `(nilpotent_subgroup k r).2.2 _ hn`. Use `⟨h⁻¹, hi, h * n⁻¹ * h⁻¹, uw_conj_N hh hni, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inv_mem_S {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z ∧ a * a⁻¹ = 1 := by
  refine ⟨?_, mul_inv_UH (S_sub_UH ha)⟩
  obtain ⟨h, hh, n, hn, rfl⟩ := ha
  have hi := inv_mem_UW hh
  have hni : n⁻¹ ∈ Nset k r := (nilpotent_subgroup k r).2.2 _ hn
  refine ⟨h⁻¹, hi, h * n⁻¹ * h⁻¹, uw_conj_N hh hni, ?_⟩
  rw [Matrix.mul_inv_rev]
  calc n⁻¹ * h⁻¹ = (h⁻¹ * h) * n⁻¹ * h⁻¹ := by rw [inv_mul_UH' hh.1, Matrix.one_mul]
    _ = h⁻¹ * (h * n⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `k r z hz hT`. Conclude with `⟨isClosed_S (hUW k r z hz hT), one_mem_S, fun a ha b hb => mul_mem_S ha hb, fun a ha => inv_mem_S ha⟩`.
-/
theorem sGroup_of (hUW : UWCompact) : SsetGroup := by
  intro k r z hz hT
  exact ⟨isClosed_S (hUW k r z hz hT), one_mem_S, fun a ha b hb => mul_mem_S ha hb,
    fun a ha => inv_mem_S ha⟩

end PI.QuotSetU.UnitaryGroupMassFormula.SW
