import Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.CompPf
open LateralTheory.E.t_E3Cut

section
variable {R D : Type} [CommRing R] [CommRing D] (h : R →+* D)

/- English proof (translation)
Rewrite using `[eval₂_map]`. Both sides reduce to the same expression.
-/
theorem eval_map_rr (p : R[X]) (x : D) :
    (p.map h.rangeRestrict).eval₂ h.range.subtype x = p.eval₂ h x := by
  rw [eval₂_map]; rfl

/- English proof (translation)
Use `letI : Algebra h.range D := h.range.subtype.toAlgebra`. Use `⟨p.map h.rangeRestrict, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hn` to reduce the goal to its premises. Establish `h1` using `congrArg (fun q => ((q.coeff n : h.range) : D)) h0`.

Simplify using `using h1`. Rewrite using `[aeval_def]`. Conclude with `(eval_map_rr h p x).trans hp`.
-/
theorem alg_of (x : D) (p : R[X]) (n : ℕ) (hn : h (p.coeff n) ≠ 0) (hp : p.eval₂ h x = 0) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra
    IsAlgebraic h.range x := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  refine ⟨p.map h.rangeRestrict, ?_, ?_⟩
  · intro h0
    apply hn
    have h1 := congrArg (fun q => ((q.coeff n : h.range) : D)) h0
    simpa using h1
  · rw [aeval_def]; exact (eval_map_rr h p x).trans hp

/- English proof (translation)
Use `letI : Algebra h.range D := h.range.subtype.toAlgebra`. Introduce and unpack `⟨q, hq0, hq⟩`. Take `⟨p, rfl⟩` from `Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q`. Use `⟨p, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc push_neg at hc`.

Apply `hq0` to reduce the goal to its premises. Use extensionality with `n`. Simplify using `only [coeff_map, coeff_zero]`. Simplify using `using hc n`. Rewrite `hq` using `[aeval_def]`.

Conclude with `(eval_map_rr h p x).symm.trans hq`.
-/
theorem of_alg (x : D) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra
    IsAlgebraic h.range x → ∃ p : R[X], (∃ n, h (p.coeff n) ≠ 0) ∧ p.eval₂ h x = 0 := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  rintro ⟨q, hq0, hq⟩
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simpa using hc n
  · rw [aeval_def] at hq; exact (eval_map_rr h p x).symm.trans hq
end

/- English proof (translation)
Introduce `A B C f g hf hg Q hQ c`. Use `haveI := hQ`. Set `gB : B →+* C ⧸ Q` to `(Ideal.Quotient.mk Q).comp g.hom`. Set `fA : A →+* C ⧸ Q` to `gB.comp f.hom`. Establish `hle : fA.range ≤ gB.range` using `by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩`.

Use `letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra`. Use `letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra`. Use `letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra`. Use `haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by`.

Introduce and unpack `⟨_, b, rfl⟩`. Take `⟨p, ⟨n, hn⟩, hp⟩` from `hf (Q.comap g.hom) (hQ.comap _) b`. Establish `hb` using `alg_of fA (gB b) p n (by`. Introduce `h0`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[Ideal.mem_comap]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h0)`. Use the proof step `(by`. Establish `h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hp`. Rewrite `h5` using `[hom_eval₂, hom_eval₂]`.

Conclude with `h5)`. Conclude with `(isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩`. Use `haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by`. Introduce `x`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Take `⟨p, ⟨n, hn⟩, hp⟩` from `hg Q hQ c'`. Conclude with `alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0)) (by`. Establish `h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hp`. Rewrite `h5` using `[hom_eval₂]`. Conclude with `h5)⟩`.

Establish `h3` using `(Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)`. Take `⟨p, ⟨n, hn⟩, hp⟩` from `of_alg fA _ h3`. Use `⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩` and prove the remaining obligations. Apply `Ideal.Quotient.eq_zero_iff_mem.mp` to reduce the goal to its premises. Rewrite using `[hom_eval₂]`.

Conclude with `hp`.
-/
theorem Comp_of : LateralTheory.E.AlgResPropsPf.Comp := by
  intro A B C f g hf hg Q hQ c
  haveI := hQ
  let gB : B →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g.hom
  let fA : A →+* C ⧸ Q := gB.comp f.hom
  have hle : fA.range ≤ gB.range := by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩
  letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra
  letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra
  letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by
    rintro ⟨_, b, rfl⟩
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap g.hom) (hQ.comap _) b
    have hb := alg_of fA (gB b) p n (by
        intro h0; apply hn; rw [Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h0)
      (by
        have h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂, hom_eval₂] at h5; exact h5)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩
  haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by
    intro x
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hg Q hQ c'
    exact alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (by
        have h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂] at h5; exact h5)⟩
  have h3 := (Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := of_alg fA _ h3
  refine ⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]; exact hp

end LateralTheory.E.CompPf
