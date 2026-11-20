import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.HTOsmulRight

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

section Prime

variable (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
  (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
  (hloc : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))

include hU hint hind he hloc in
/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal`. Set `mk` to `Ideal.Quotient.mk P.asIdeal`. Set `U : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal)` to `{ carrier := {φ | ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧ ∀ i, φ i = mk (o i)} zero_mem' := ⟨0, Λ.zero_mem, 0, fun i => by simp, fun i => by simp⟩ add_mem' := by`. Introduce and unpack `φ ψ ⟨y, hy, o, ho, hφ⟩ ⟨y', hy', o', ho', hψ⟩`.

Use `⟨y + y', Λ.add_mem hy hy', o + o', fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[map_add, ho, ho']`. Simplify using `[hφ, hψ]`. Use the proof step `smul_mem' := by`. Introduce and unpack `κ φ ⟨y, hy, o, ho, hφ⟩`.

Take `⟨κ', rfl⟩` from `Ideal.Quotient.mk_surjective κ`. Use `⟨cj κ' • y, Λ.smul_mem _ hy, fun i => κ' * o i, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hT_cj_left, ho]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hφ, mk] }`. Establish `hUtop : U = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hfU⟩` from `Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hne)`. Set `α : Fin r → 𝓞 E ⧸ P.asIdeal` to `fun i => f (fun j => if i = j then 1 else 0)`.

Establish `hfα : ∀ φ, f φ = ∑ i, φ i * α i`. Introduce `φ`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f φ]`. Simplify using `[α, smul_eq_mul]`. Establish `hα0 : ∃ i, α i ≠ 0`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun φ => ?_` and prove the remaining obligations. Rewrite using `[hfα, LinearMap.zero_apply]`.

Conclude with `Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]`. Use `choose α' hα' using fun i => Ideal.Quotient.mk_surjective (α i)`. Establish `hmem` using `coeff_mem_P Λ hU e hind P hloc α' (by`. Introduce `y hy`. Use `choose o ho using fun i => hint y hy (e i) (he i)`.

Establish `hφ : (fun i => mk (o i)) ∈ U` using `⟨y, hy, o, ho, fun i => rfl⟩`. Establish `hz : f (fun i => mk (o i)) = 0` using `hfU hφ`. Rewrite `hz` using `[hfα]`. Use `⟨∑ i, o i * α' i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Simplify `hz` using `[map_sum, map_mul, hα', mk]`. Rewrite using `[map_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hT_osmul_right, ho]`.

Use the proof step `ring)`. Take `⟨i, hi⟩` from `hα0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← hα' i]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)`.

Establish `hc : (fun i => if i = c then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ U` using `by rw [hUtop]; trivial`. Take `⟨y, hy, o, ho, hφ⟩` from `hc`. Use `⟨y, hy, o, ho, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Use `hφ i` as an intermediate fact.

Simplify using `only at this`. Distinguish the cases in `hic : i = c`. Simplify using `only [hic, if_true] at this ⊢`. Rewrite using `[map_one]`. Conclude with `this.symm`.

Simplify using `only [hic, if_false] at this ⊢`. Rewrite using `[map_zero]`. Conclude with `this.symm`.
-/
theorem residue_onto (c : Fin r) :
    ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧
      ∀ i, (o i - if i = c then 1 else 0) ∈ P.asIdeal := by
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let mk := Ideal.Quotient.mk P.asIdeal
  let U : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal) :=
    { carrier := {φ | ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧ ∀ i, φ i = mk (o i)}
      zero_mem' := ⟨0, Λ.zero_mem, 0, fun i => by simp, fun i => by simp⟩
      add_mem' := by
        rintro φ ψ ⟨y, hy, o, ho, hφ⟩ ⟨y', hy', o', ho', hψ⟩
        refine ⟨y + y', Λ.add_mem hy hy', o + o', fun i => ?_, fun i => ?_⟩
        · simp [map_add, ho, ho']
        · simp [hφ, hψ]
      smul_mem' := by
        rintro κ φ ⟨y, hy, o, ho, hφ⟩
        obtain ⟨κ', rfl⟩ := Ideal.Quotient.mk_surjective κ
        refine ⟨cj κ' • y, Λ.smul_mem _ hy, fun i => κ' * o i, fun i => ?_, fun i => ?_⟩
        · rw [hT_cj_left, ho]; push_cast; ring
        · simp [hφ, mk] }
  have hUtop : U = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hne)
    let α : Fin r → 𝓞 E ⧸ P.asIdeal := fun i => f (fun j => if i = j then 1 else 0)
    have hfα : ∀ φ, f φ = ∑ i, φ i * α i := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ f φ]
      simp [α, smul_eq_mul]
    have hα0 : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      apply hf0
      refine LinearMap.ext fun φ => ?_
      rw [hfα, LinearMap.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
    choose α' hα' using fun i => Ideal.Quotient.mk_surjective (α i)
    have hmem := coeff_mem_P Λ hU e hind P hloc α' (by
      intro y hy
      choose o ho using fun i => hint y hy (e i) (he i)
      have hφ : (fun i => mk (o i)) ∈ U := ⟨y, hy, o, ho, fun i => rfl⟩
      have hz : f (fun i => mk (o i)) = 0 := hfU hφ
      rw [hfα] at hz
      refine ⟨∑ i, o i * α' i, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [map_sum, map_mul, hα', mk] using hz
      · rw [map_sum]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hT_osmul_right, ho]; ring)
    obtain ⟨i, hi⟩ := hα0
    apply hi
    rw [← hα' i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
  have hc : (fun i => if i = c then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ U := by rw [hUtop]; trivial
  obtain ⟨y, hy, o, ho, hφ⟩ := hc
  refine ⟨y, hy, o, ho, fun i => ?_⟩
  rw [← Ideal.Quotient.eq]
  have := hφ i
  simp only at this
  by_cases hic : i = c
  · simp only [hic, if_true] at this ⊢; rw [map_one]; exact this.symm
  · simp only [hic, if_false] at this ⊢; rw [map_zero]; exact this.symm

include hU hint hind he hloc in
/- English proof (translation)
Use `choose y hy o ho hP using fun j => residue_onto Λ hU hint e hind he P hloc j`. Set `G : Matrix (Fin r) (Fin r) (𝓞 E)` to `fun j i => o j i`. Establish `hdet : G.det ∉ P.asIdeal`. Introduce `hmem`. Establish `h1 : (Ideal.Quotient.mk P.asIdeal).mapMatrix G = 1`.

Use extensionality with `j i`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]`. Use `Ideal.Quotient.eq.mpr (hP j i)` as an intermediate fact. Rewrite using `[this]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij]`. Use `RingHom.map_det (Ideal.Quotient.mk P.asIdeal) G` as an intermediate fact. Rewrite `this` using `[h1, Matrix.det_one, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]`.

Conclude with `zero_ne_one this`. Establish `key : ∀ i, S.hT (∑ j, cj (G.adjugate c j) • y j) (e i) = ((G.adjugate * G) c i : E)`. Introduce `i`. Rewrite using `[map_sum, LinearMap.sum_apply, Matrix.mul_apply]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hT_cj_left, ho]`. Rewrite `key` using `[Matrix.adjugate_mul]`. Use `⟨∑ j, cj (G.adjugate c j) • y j, Λ.sum_mem fun j _ => Λ.smul_mem _ (hy j), fun i hi => ?_, G.det, ?_, hdet⟩` and prove the remaining obligations. Rewrite using `[key, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hi)]`.

Simplify using the standard rewrite rules. Rewrite using `[key, Matrix.smul_apply, Matrix.one_apply_eq]`. Simplify using the standard rewrite rules.
-/
theorem exact_dual (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ o : 𝓞 E, S.hT y (e c) = (o : E) ∧ o ∉ P.asIdeal := by
  choose y hy o ho hP using fun j => residue_onto Λ hU hint e hind he P hloc j
  let G : Matrix (Fin r) (Fin r) (𝓞 E) := fun j i => o j i
  have hdet : G.det ∉ P.asIdeal := by
    intro hmem
    have h1 : (Ideal.Quotient.mk P.asIdeal).mapMatrix G = 1 := by
      ext j i
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have := Ideal.Quotient.eq.mpr (hP j i)
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have := RingHom.map_det (Ideal.Quotient.mk P.asIdeal) G
    rw [h1, Matrix.det_one, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at this
    exact zero_ne_one this
  have key : ∀ i, S.hT (∑ j, cj (G.adjugate c j) • y j) (e i) = ((G.adjugate * G) c i : E) := by
    intro i
    rw [map_sum, LinearMap.sum_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT_cj_left, ho]
  rw [Matrix.adjugate_mul] at key
  refine ⟨∑ j, cj (G.adjugate c j) • y j, Λ.sum_mem fun j _ => Λ.smul_mem _ (hy j), fun i hi => ?_,
    G.det, ?_, hdet⟩
  · rw [key, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hi)]; simp
  · rw [key, Matrix.smul_apply, Matrix.one_apply_eq]; simp

end Prime

end PI.NRL
