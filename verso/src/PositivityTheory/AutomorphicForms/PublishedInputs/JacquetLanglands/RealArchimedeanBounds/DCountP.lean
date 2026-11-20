import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

/- English proof (translation)
Introduce `hM hB hO F _ _ _ c hc χ`. Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `hKH : Kc c ≤ Hc c` using `le_sup_left`. Establish `hzH : ∀ z, zc F z ∈ Hc c` using `fun z => Subgroup.mem_sup_right ⟨z, rfl⟩`. Take `⟨-, -, hKK, hHd, -⟩` from `hM F`.

Use `show Countable (GF F ⧸ Hc c) ∧ ∀ a : GF F, {ω : GF F ⧸ Hc c | ∃ h ∈ Hc c, ω = ((h * a : GF F) : GF F ⧸ Hc c)}.Finite`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨S, hS⟩` from `hB F c hc`. Establish `: Countable (Matrix (Fin 2) (Fin 2) F)` using `inferInstanceAs (Countable (Fin 2 → Fin 2 → F))`. Establish `: Countable (GL (Fin 2) F)` using `(show Function.Injective (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) from fun _ _ h => Units.ext h).countable`.

Use `Function.Surjective.countable (f := fun p : GL (Fin 2) F × S => ((jF F p.1 * p.2.1 : GF F) : GF F ⧸ Hc c)) ?_` and prove the remaining obligations. Introduce `ω`. Proceed by induction on `ω using QuotientGroup.induction_on with`. Consider the case `H x`. Take `⟨b, -, x', hx', h, hh, e⟩` from `hS x`.

Use `⟨(b⁻¹, ⟨x', hx'⟩), QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Establish `hx : x = jF F b⁻¹ * x' * h` using `by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]`. Use `show (jF F b⁻¹ * x')⁻¹ * x ∈ Hc c`. Rewrite using `[hx, inv_mul_cancel_left]`. Conclude with `hKH hh`.

Take `⟨S, hS⟩` from `hO F c hc a`. Use `(S.finite_toSet.image (fun x : GF F => (x : GF F ⧸ Hc c))).subset ?_` and prove the remaining obligations. Introduce and unpack `ω ⟨h, hh, rfl⟩`. Take `⟨k, hk, z, rfl⟩` from `(hHd c h).1 hh`. Take `⟨x', hx', h', hh', e⟩` from `hS k (hKK c hk)`.

Use `⟨x', hx', QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Establish `he : k * zc F z * a = x' * (h' * zc F z)`. Rewrite using `[mul_assoc, ← Subgroup.mem_center_iff.1 (zc_center z) a, ← mul_assoc, e, mul_assoc]`. Rewrite using `[he, inv_mul_cancel_left]`. Conclude with `mul_mem (hKH hh') (hzH z)`.
-/
theorem dCount : AMem → ABnfH → AOrb → DCount := by
  intro hM hB hO F _ _ _ c hc χ
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hKH : Kc c ≤ Hc c := le_sup_left
  have hzH : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  obtain ⟨-, -, hKK, hHd, -⟩ := hM F
  show Countable (GF F ⧸ Hc c) ∧ ∀ a : GF F,
    {ω : GF F ⧸ Hc c | ∃ h ∈ Hc c, ω = ((h * a : GF F) : GF F ⧸ Hc c)}.Finite
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨S, hS⟩ := hB F c hc
    have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    have : Countable (GL (Fin 2) F) :=
      (show Function.Injective (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) from
        fun _ _ h => Units.ext h).countable
    refine Function.Surjective.countable
      (f := fun p : GL (Fin 2) F × S => ((jF F p.1 * p.2.1 : GF F) : GF F ⧸ Hc c)) ?_
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
      refine ⟨(b⁻¹, ⟨x', hx'⟩), QuotientGroup.eq.2 ?_⟩
      have hx : x = jF F b⁻¹ * x' * h := by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]
      show (jF F b⁻¹ * x')⁻¹ * x ∈ Hc c
      rw [hx, inv_mul_cancel_left]
      exact hKH hh
  · obtain ⟨S, hS⟩ := hO F c hc a
    refine (S.finite_toSet.image (fun x : GF F => (x : GF F ⧸ Hc c))).subset ?_
    rintro ω ⟨h, hh, rfl⟩
    obtain ⟨k, hk, z, rfl⟩ := (hHd c h).1 hh
    obtain ⟨x', hx', h', hh', e⟩ := hS k (hKK c hk)
    refine ⟨x', hx', QuotientGroup.eq.2 ?_⟩
    have he : k * zc F z * a = x' * (h' * zc F z) := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zc_center z) a, ← mul_assoc, e, mul_assoc]
    rw [he, inv_mul_cancel_left]
    exact mul_mem (hKH hh') (hzH z)

end UpperTheory.Esk
