import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.HenselSquare

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

/- English proof (translation)
Use `letI := GlobalTheory.LocalData.complRel u`. Use `haveI := GlobalTheory.LocalData.isLocalField u`. Use `haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))`. Establish `hE : (ValuativeRel.valuation (u.adicCompletion F)).IsEquiv (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))` using `ValuativeRel.isEquiv _ _`. Establish `hmem : ∀ x : u.adicCompletion F, x ∈ (ValuativeRel.valuation (u.adicCompletion F)).integer ↔ x ∈ u.adicCompletionIntegers F` using `fun x => by`.

Rewrite using `[mem_adicCompletionIntegers, Valuation.mem_integer_iff]`. Conclude with `hE.le_one_iff_le_one`. Set `e : (ValuativeRel.valuation (u.adicCompletion F)).integer ≃+* u.adicCompletionIntegers F` to `{ toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩ invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl map_add' := fun _ _ => rfl }`. Establish `hm : (maximalIdeal (ValuativeRel.valuation (u.adicCompletion F)).integer).map e = maximalIdeal (u.adicCompletionIntegers F)`. Use extensionality with `y`.

Rewrite using `[← Ideal.comap_symm, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]`. Conclude with `not_congr (isUnit_map_iff e.symm y)`. Rewrite using `[← hm]`. Conclude with `(IsAdicComplete.congr_ringEquiv _ e).2 inferInstance`.
-/
theorem isAdicComplete_integers (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    IsAdicComplete (maximalIdeal (u.adicCompletionIntegers F)) (u.adicCompletionIntegers F) := by
  letI := GlobalTheory.LocalData.complRel u
  haveI := GlobalTheory.LocalData.isLocalField u
  haveI := Valuation.Compatible.ofValuation
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hE : (ValuativeRel.valuation (u.adicCompletion F)).IsEquiv
      (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hmem : ∀ x : u.adicCompletion F,
      x ∈ (ValuativeRel.valuation (u.adicCompletion F)).integer ↔
        x ∈ u.adicCompletionIntegers F := fun x => by
    rw [mem_adicCompletionIntegers, Valuation.mem_integer_iff]
    exact hE.le_one_iff_le_one
  let e : (ValuativeRel.valuation (u.adicCompletion F)).integer ≃+* u.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hm : (maximalIdeal (ValuativeRel.valuation (u.adicCompletion F)).integer).map e =
      maximalIdeal (u.adicCompletionIntegers F) := by
    ext y
    rw [← Ideal.comap_symm, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff e.symm y)
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 inferInstance

/- English proof (translation)
Take `⟨s, hs, -⟩` from `HenselianRing.is_henselian (I := I) (X ^ 2 + X - C z) (by monicity!) 0 (by simpa using hz) (by simp)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `h2 : eval s (X ^ 2 + X - C z) = 0` using `hs`. Simplify using `only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2`. Take the linear combination `h2`.
-/
theorem exists_sq_add_eq {O : Type} [CommRing O] [Nontrivial O] (I : Ideal O) [HenselianRing O I]
    (z : O) (hz : z ∈ I) : ∃ s : O, s ^ 2 + s = z := by
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C z) (by monicity!) 0
    (by simpa using hz) (by simp)
  refine ⟨s, ?_⟩
  have h2 : eval s (X ^ 2 + X - C z) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  linear_combination h2

/- English proof (translation)
Introduce `F _ _ u z hz`. Use `haveI := isAdicComplete_integers F u`. Use `set z' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) z with hz'`. Establish `hcoe : (z' : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F)`. Rewrite using `[hz', algebraMap_adicCompletionIntegers_apply]`.

Both sides reduce to the same expression. Establish `hv : Valued.v (algebraMap F (u.adicCompletion F) (z : F)) < 1`. Establish `h1 : u.valuation F (algebraMap (𝓞 F) F z) < 1`. Rewrite using `[valuation_of_algebraMap]`. Conclude with `(intValuation_lt_one_iff_mem (v := u) z).2 hz`.

Establish `h2 : Valued.v (((z : F) : u.adicCompletion F)) = u.valuation F (z : F)` using `valuedAdicCompletion_eq_valuation' (v := u) (z : F)`. Conclude with `(h2.trans_lt h1 :)`. Establish `hzm : z' ∈ maximalIdeal (u.adicCompletionIntegers F)`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Rewrite using `[show (z'.1 : u.adicCompletion F) = (z' : u.adicCompletion F) from rfl, hcoe]`.

Conclude with `ne_of_lt hv`. Take `⟨s, hs⟩` from `exists_sq_add_eq (maximalIdeal (u.adicCompletionIntegers F)) z' hzm`. Establish `hsK : (s : u.adicCompletion F) ^ 2 + (s : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F)`. Rewrite using `[← hcoe, ← hs]`. Use `norm_cast`.

Establish `hL : algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * algebraMap F (u.adicCompletion F) (z : F)`. Establish `e1 : ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * (z : F)`. Rewrite using `[show (4 : 𝓞 F) = 1 + 1 + 1 + 1 by norm_num]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Simplify using `only [map_add, map_one, map_mul, map_ofNat]`. Use `⟨1 + 2 * (s : u.adicCompletion F), ?_⟩` and prove the remaining obligations. Rewrite using `[hL]`. Take the linear combination `(-4 : u.adicCompletion F) * hsK`.
-/
theorem isSquare_one_add_four_mul : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (z : 𝓞 F), z ∈ u.asIdeal → IsSquare (algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F)) := by
  intro F _ _ u z hz
  haveI := isAdicComplete_integers F u
  set z' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) z with hz'
  have hcoe : (z' : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F) := by
    rw [hz', algebraMap_adicCompletionIntegers_apply]
    rfl
  have hv : Valued.v (algebraMap F (u.adicCompletion F) (z : F)) < 1 := by
    have h1 : u.valuation F (algebraMap (𝓞 F) F z) < 1 := by
      rw [valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem (v := u) z).2 hz
    have h2 : Valued.v (((z : F) : u.adicCompletion F)) = u.valuation F (z : F) :=
      valuedAdicCompletion_eq_valuation' (v := u) (z : F)
    exact (h2.trans_lt h1 :)
  have hzm : z' ∈ maximalIdeal (u.adicCompletionIntegers F) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rw [show (z'.1 : u.adicCompletion F) = (z' : u.adicCompletion F) from rfl, hcoe]
    exact ne_of_lt hv
  obtain ⟨s, hs⟩ := exists_sq_add_eq (maximalIdeal (u.adicCompletionIntegers F)) z' hzm
  have hsK : (s : u.adicCompletion F) ^ 2 + (s : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (z : F) := by
    rw [← hcoe, ← hs]
    norm_cast
  have hL : algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F) =
      1 + 4 * algebraMap F (u.adicCompletion F) (z : F) := by
    have e1 : ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * (z : F) := by
      rw [show (4 : 𝓞 F) = 1 + 1 + 1 + 1 by norm_num]
      push_cast
      ring
    rw [e1]
    simp only [map_add, map_one, map_mul, map_ofNat]
  refine ⟨1 + 2 * (s : u.adicCompletion F), ?_⟩
  rw [hL]
  linear_combination (-4 : u.adicCompletion F) * hsK

end GlobalTheory.HenselSquare
