import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc

open Mdl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
The claim follows from `(hR a).2 ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simpa using ha⟩`.
-/
theorem mem_of_isLocAt {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) {a : Ω} (ha : a ∈ A) : a ∈ R :=
  (hR a).2 ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simpa using ha⟩

/- English proof (translation)
Establish `h0 : (a : Ω) ≠ 0` using `fun h => ha (by`. Establish `e : a = 0` using `Subtype.ext h`. Rewrite using `[e]`. Conclude with `q.zero_mem)`. Conclude with `⟨h0, (hR _).2 ⟨a, ha, by rw [mul_inv_cancel₀ h0]; exact A.one_mem⟩⟩`.
-/
theorem unit_of_not_mem {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {a : A} (ha : a ∉ q) : (a : Ω) ≠ 0 ∧ (a : Ω)⁻¹ ∈ R := by
  have h0 : (a : Ω) ≠ 0 := fun h => ha (by
    have e : a = 0 := Subtype.ext h
    rw [e]
    exact q.zero_mem)
  exact ⟨h0, (hR _).2 ⟨a, ha, by rw [mul_inv_cancel₀ h0]; exact A.one_mem⟩⟩

/- English proof (translation)
Take `⟨s, hs, hsb⟩` from `(hR _).1 hi`. Introduce `hb`. Apply `hs` to reduce the goal to its premises. Establish `e : s = ⟨_, hsb⟩ * b` using `Subtype.ext (by`. Rewrite using `[Subalgebra.coe_mul]`.

Conclude with `(inv_mul_cancel_right₀ h0 _).symm)`. Rewrite using `[e]`. Conclude with `q.mul_mem_left _ hb`.
-/
theorem not_mem_of_unit {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {b : A} (h0 : (b : Ω) ≠ 0) (hi : (b : Ω)⁻¹ ∈ R) : b ∉ q := by
  obtain ⟨s, hs, hsb⟩ := (hR _).1 hi
  intro hb
  apply hs
  have e : s = ⟨_, hsb⟩ * b := Subtype.ext (by
    rw [Subalgebra.coe_mul]
    exact (inv_mul_cancel_right₀ h0 _).symm)
  rw [e]
  exact q.mul_mem_left _ hb

/- English proof (translation)
The claim follows from `Algebra.adjoin_le (by rintro x (rfl | hx) · exact hh · exact hA hx)`.
-/
theorem invAdj_le_of {A C : Subalgebra ℚ Ω} {h : Ω} (hA : A ≤ C) (hh : h⁻¹ ∈ C) : invAdj A h ≤ C :=
  Algebra.adjoin_le (by
    rintro x (rfl | hx)
    · exact hh
    · exact hA hx)

/- English proof (translation)
Use `invAdj_le_of (le_invAdj _ _) ?_` and prove the remaining obligations. Establish `hs0 : s ≠ 0` using `right_ne_zero_of_mul h0`. Establish `hg0 : g ≠ 0` using `left_ne_zero_of_mul h0`. Establish `e : g⁻¹ = s * (g * s)⁻¹` using `by field_simp`. Rewrite using `[e]`.

Conclude with `Subalgebra.mul_mem _ (le_invAdj _ _ hs) (inv_mem_invAdj _ _)`.
-/
theorem invAdj_le_mul {A : Subalgebra ℚ Ω} {g s : Ω} (hs : s ∈ A) (h0 : g * s ≠ 0) :
    invAdj A g ≤ invAdj A (g * s) := by
  refine invAdj_le_of (le_invAdj _ _) ?_
  have hs0 : s ≠ 0 := right_ne_zero_of_mul h0
  have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
  have e : g⁻¹ = s * (g * s)⁻¹ := by field_simp
  rw [e]
  exact Subalgebra.mul_mem _ (le_invAdj _ _ hs) (inv_mem_invAdj _ _)

/- English proof (translation)
Establish `key : ∀ T : Finset Ω, (∀ b ∈ T, b ∈ R) → ∃ g : A, g ∉ q ∧ ∀ b ∈ T, b ∈ invAdj A g`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩`. Consider the case `insert b T _ ih`.

Introduce `hT`. Take `⟨g₁, hg₁, hg₁T⟩` from `ih fun x hx => hT x (Finset.mem_insert_of_mem hx)`. Take `⟨s, hs, hsb⟩` from `(hR b).1 (hT b (Finset.mem_insert_self _ _))`. Establish `hmul : g₁ * s ∉ q` using `fun h => (hq.mem_or_mem h).elim hg₁ hs`. Establish `h0 : (g₁ : Ω) * s ≠ 0` using `(unit_of_not_mem hR hmul).1`.

Establish `hs0 : (s : Ω) ≠ 0` using `right_ne_zero_of_mul h0`. Establish `hg0 : (g₁ : Ω) ≠ 0` using `left_ne_zero_of_mul h0`. Use `⟨g₁ * s, hmul, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_mul]`. Introduce `x hx`.

Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Establish `e : x = ((s : Ω) * x) * g₁ * ((g₁ : Ω) * s)⁻¹` using `by field_simp`. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (le_invAdj _ _ hsb) (le_invAdj _ _ g₁.2)) (inv_mem_invAdj _ _)`. Conclude with `invAdj_le_mul s.2 h0 (hg₁T x hx)`.

Take `⟨S, rfl⟩` from `hB`. Take `⟨g, hg, hgS⟩` from `key S fun b hb => hBR b (Algebra.subset_adjoin hb)`. Conclude with `⟨g, hg, Algebra.adjoin_le fun b hb => hgS b hb⟩`.
-/
theorem exists_den {A B : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) (hB : B.FG) (hBR : ∀ b ∈ B, b ∈ R) : ∃ g : A, g ∉ q ∧ B ≤ invAdj A g := by
  classical
  have key : ∀ T : Finset Ω, (∀ b ∈ T, b ∈ R) → ∃ g : A, g ∉ q ∧ ∀ b ∈ T, b ∈ invAdj A g := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
    | insert b T _ ih =>
      intro hT
      obtain ⟨g₁, hg₁, hg₁T⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨s, hs, hsb⟩ := (hR b).1 (hT b (Finset.mem_insert_self _ _))
      have hmul : g₁ * s ∉ q := fun h => (hq.mem_or_mem h).elim hg₁ hs
      have h0 : (g₁ : Ω) * s ≠ 0 := (unit_of_not_mem hR hmul).1
      have hs0 : (s : Ω) ≠ 0 := right_ne_zero_of_mul h0
      have hg0 : (g₁ : Ω) ≠ 0 := left_ne_zero_of_mul h0
      refine ⟨g₁ * s, hmul, ?_⟩
      rw [Subalgebra.coe_mul]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : x = ((s : Ω) * x) * g₁ * ((g₁ : Ω) * s)⁻¹ := by field_simp
        rw [e]
        exact Subalgebra.mul_mem _
          (Subalgebra.mul_mem _ (le_invAdj _ _ hsb) (le_invAdj _ _ g₁.2)) (inv_mem_invAdj _ _)
      · exact invAdj_le_mul s.2 h0 (hg₁T x hx)
  obtain ⟨S, rfl⟩ := hB
  obtain ⟨g, hg, hgS⟩ := key S fun b hb => hBR b (Algebra.subset_adjoin hb)
  exact ⟨g, hg, Algebra.adjoin_le fun b hb => hgS b hb⟩

/- English proof (translation)
Take `⟨gn, gi⟩` from `unit_of_not_mem hR hg`. Take `⟨hn, hi⟩` from `unit_of_not_mem hR' hh`. Take `⟨m, hm⟩` from `exists_mul_pow_mem h.2 hn hgh`. Use `⟨⟨_, hm⟩, m, not_mem_of_unit hR' (mul_ne_zero gn (pow_ne_zero _ hn)) ?_, rfl⟩` and prove the remaining obligations. Use `show ((g : Ω) * (h : Ω) ^ m)⁻¹ ∈ R`.

Rewrite using `[mul_inv, ← inv_pow]`. Conclude with `R.mul_mem gi (R.pow_mem hi _)`.
-/
theorem exists_clear {A B : Subalgebra ℚ Ω} {q : Ideal A} {q' : Ideal B} {R : Subring Ω}
    (hR : IsLocAt A q R) (hR' : IsLocAt B q' R) {g : A} {h : B} (hg : g ∉ q) (hh : h ∉ q')
    (hgh : (g : Ω) ∈ invAdj B h) : ∃ (a : B) (m : ℕ), a ∉ q' ∧ (a : Ω) = g * (h : Ω) ^ m := by
  obtain ⟨gn, gi⟩ := unit_of_not_mem hR hg
  obtain ⟨hn, hi⟩ := unit_of_not_mem hR' hh
  obtain ⟨m, hm⟩ := exists_mul_pow_mem h.2 hn hgh
  refine ⟨⟨_, hm⟩, m, not_mem_of_unit hR' (mul_ne_zero gn (pow_ne_zero _ hn)) ?_, rfl⟩
  show ((g : Ω) * (h : Ω) ^ m)⁻¹ ∈ R
  rw [mul_inv, ← inv_pow]
  exact R.mul_mem gi (R.pow_mem hi _)

/- English proof (translation)
Introduce `Ω _ _ A B q q' R hA hB hq hq' hR hR'`. Take `⟨g₀, hg₀, hBg⟩` from `exists_den hq hR hB fun b hb => mem_of_isLocAt hq' hR' hb`. Take `⟨h₀, hh₀, hAh⟩` from `exists_den hq' hR' hA fun b hb => mem_of_isLocAt hq hR hb`. Take `⟨a, m, ha, ea⟩` from `exists_clear hR hR' hg₀ hh₀ (hAh g₀.2)`. Take `⟨h, hh, eh⟩ : ∃ h : B, h ∉ q' ∧ (h : Ω) = h₀ * a` from `⟨h₀ * a, fun hm => (hq'.mem_or_mem hm).elim hh₀ ha, rfl⟩`.

Take `⟨a', l, ha', ea'⟩` from `exists_clear hR' hR hh hg₀ (hBg h.2)`. Take `⟨g, hg, eg⟩ : ∃ g : A, g ∉ q ∧ (g : Ω) = g₀ * a'` from `⟨g₀ * a', fun hm => (hq.mem_or_mem hm).elim hg₀ ha', rfl⟩`. Establish `g0n` using `(unit_of_not_mem hR hg₀).1`. Establish `h0n` using `(unit_of_not_mem hR' hh₀).1`. Establish `gn` using `(unit_of_not_mem hR hg).1`.

Establish `hn` using `(unit_of_not_mem hR' hh).1`. Establish `an` using `(unit_of_not_mem hR' ha).1`. Establish `an'` using `(unit_of_not_mem hR ha').1`. Use `⟨g, h, hg, hh, ?_⟩` and prove the remaining obligations. Establish `hAh' : invAdj B (h₀ : Ω) ≤ invAdj B h`.

Rewrite using `[eh]`. Conclude with `invAdj_le_mul a.2 (eh ▸ hn)`. Establish `hBg' : invAdj A (g₀ : Ω) ≤ invAdj A g`. Rewrite using `[eg]`. Conclude with `invAdj_le_mul a'.2 (eg ▸ gn)`.

Establish `g0inv : (g₀ : Ω)⁻¹ ∈ invAdj B h`. Establish `e : (g₀ : Ω)⁻¹ = (h₀ : Ω) ^ m * h₀ * (h : Ω)⁻¹`. Rewrite using `[eh, ea]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (le_invAdj _ _ (B.pow_mem h₀.2 _)) (le_invAdj _ _ h₀.2)) (inv_mem_invAdj _ _)`. Establish `C1 : invAdj A (g₀ : Ω) ≤ invAdj B h` using `invAdj_le_of (hAh.trans hAh') g0inv`. Establish `hinv : (h : Ω)⁻¹ ∈ invAdj A g`. Establish `e : (h : Ω)⁻¹ = (g₀ : Ω) ^ l * g₀ * (g : Ω)⁻¹`. Rewrite using `[eg, ea']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (le_invAdj _ _ (A.pow_mem g₀.2 _)) (le_invAdj _ _ g₀.2)) (inv_mem_invAdj _ _)`. Establish `ginv : (g : Ω)⁻¹ ∈ invAdj B h`. Establish `e : (g : Ω)⁻¹ = (g₀ : Ω)⁻¹ * ((h : Ω)⁻¹ * ((g₀ : Ω)⁻¹) ^ l)`.

Rewrite using `[eg, ea', mul_inv, mul_inv, inv_pow]`. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ g0inv (Subalgebra.mul_mem _ (inv_mem_invAdj _ _) (Subalgebra.pow_mem _ g0inv _))`. Conclude with `le_antisymm (invAdj_le_of ((le_invAdj A _).trans C1) ginv) (invAdj_le_of (hBg.trans hBg') hinv)`.
-/
theorem exists_common_loc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A B : Subalgebra ℚ Ω) (q : Ideal A) (q' : Ideal B)
    (R : Subring Ω), A.FG → B.FG → q.IsPrime → q'.IsPrime → IsLocAt A q R → IsLocAt B q' R →
    ∃ (g : A) (h : B), g ∉ q ∧ h ∉ q' ∧ Mdl.invAdj A g = Mdl.invAdj B h := by
  intro Ω _ _ A B q q' R hA hB hq hq' hR hR'
  obtain ⟨g₀, hg₀, hBg⟩ := exists_den hq hR hB fun b hb => mem_of_isLocAt hq' hR' hb
  obtain ⟨h₀, hh₀, hAh⟩ := exists_den hq' hR' hA fun b hb => mem_of_isLocAt hq hR hb
  obtain ⟨a, m, ha, ea⟩ := exists_clear hR hR' hg₀ hh₀ (hAh g₀.2)
  obtain ⟨h, hh, eh⟩ : ∃ h : B, h ∉ q' ∧ (h : Ω) = h₀ * a :=
    ⟨h₀ * a, fun hm => (hq'.mem_or_mem hm).elim hh₀ ha, rfl⟩
  obtain ⟨a', l, ha', ea'⟩ := exists_clear hR' hR hh hg₀ (hBg h.2)
  obtain ⟨g, hg, eg⟩ : ∃ g : A, g ∉ q ∧ (g : Ω) = g₀ * a' :=
    ⟨g₀ * a', fun hm => (hq.mem_or_mem hm).elim hg₀ ha', rfl⟩
  have g0n := (unit_of_not_mem hR hg₀).1
  have h0n := (unit_of_not_mem hR' hh₀).1
  have gn := (unit_of_not_mem hR hg).1
  have hn := (unit_of_not_mem hR' hh).1
  have an := (unit_of_not_mem hR' ha).1
  have an' := (unit_of_not_mem hR ha').1
  refine ⟨g, h, hg, hh, ?_⟩

  have hAh' : invAdj B (h₀ : Ω) ≤ invAdj B h := by
    rw [eh]
    exact invAdj_le_mul a.2 (eh ▸ hn)
  have hBg' : invAdj A (g₀ : Ω) ≤ invAdj A g := by
    rw [eg]
    exact invAdj_le_mul a'.2 (eg ▸ gn)
  have g0inv : (g₀ : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g₀ : Ω)⁻¹ = (h₀ : Ω) ^ m * h₀ * (h : Ω)⁻¹ := by
      rw [eh, ea]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (B.pow_mem h₀.2 _)) (le_invAdj _ _ h₀.2)) (inv_mem_invAdj _ _)
  have C1 : invAdj A (g₀ : Ω) ≤ invAdj B h := invAdj_le_of (hAh.trans hAh') g0inv
  have hinv : (h : Ω)⁻¹ ∈ invAdj A g := by
    have e : (h : Ω)⁻¹ = (g₀ : Ω) ^ l * g₀ * (g : Ω)⁻¹ := by
      rw [eg, ea']
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (A.pow_mem g₀.2 _)) (le_invAdj _ _ g₀.2)) (inv_mem_invAdj _ _)
  have ginv : (g : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g : Ω)⁻¹ = (g₀ : Ω)⁻¹ * ((h : Ω)⁻¹ * ((g₀ : Ω)⁻¹) ^ l) := by
      rw [eg, ea', mul_inv, mul_inv, inv_pow]
    rw [e]
    exact Subalgebra.mul_mem _ g0inv
      (Subalgebra.mul_mem _ (inv_mem_invAdj _ _) (Subalgebra.pow_mem _ g0inv _))
  exact le_antisymm (invAdj_le_of ((le_invAdj A _).trans C1) ginv)
    (invAdj_le_of (hBg.trans hBg') hinv)

end GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc
