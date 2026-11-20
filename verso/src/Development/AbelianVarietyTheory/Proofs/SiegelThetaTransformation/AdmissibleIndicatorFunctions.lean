import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

open Classical in

def indFam : Fam E n N := fun Λ x => if ColsIn Λ x then 1 else 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, rfl⟩` from `hy`.

Introduce `a`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `using isIntegral_one`. Simplify using `[hab, isIntegral_zero]`.

Consider the case `zero => intro a`. Conclude with `isIntegral_zero`. Consider the case `add y z _ _ hy hz => intro a`. Conclude with `(hy a).add (hz a)`. Consider the case `smul r y _ hy`.

Introduce `a`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `(RingOfIntegers.isIntegral_coe r).mul (hy a)`. Introduce `hx`. Establish `hsum : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E)`.

Use extensionality with `b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem mem_stdL {x : Fin n → E} : x ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      intro a
      by_cases hab : a = b
      · subst hab
        simpa using isIntegral_one
      · simp [hab, isIntegral_zero]
    | zero => intro a; exact isIntegral_zero
    | add y z _ _ hy hz => intro a; exact (hy a).add (hz a)
    | smul r y _ hy =>
      intro a
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe r).mul (hy a)
  · intro hx
    have hsum : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      ext b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
The claim follows from `map_zero (IsCMField.complexConj E)`.
-/
private theorem cc_zero_siegel_theta_transformation : cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

/- English proof (translation)
The claim follows from `map_one (IsCMField.complexConj E)`.
-/
private theorem cc_one' : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

/- English proof (translation)
The claim follows from `ht.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom`.
-/
private theorem isIntegral_cc' {t : E} (ht : IsIntegral ℤ t) : IsIntegral ℤ (cc t) :=
  ht.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

/- English proof (translation)
Simplify using `[herm, Matrix.one_apply]`.
-/
private theorem herm_one_apply (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), fun x => ?_, ⟨1, one_pos, Nat.coprime_one_left M, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Rewrite using `[herm_one_apply]`. Rewrite `hx`, `hy` using `[mem_stdL]`.

Conclude with `IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc' (hy a))`. Introduce `h`. Rewrite using `[mem_stdL]`. Introduce `a`. Establish `ha` using `h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)`.

Rewrite `ha` using `[herm_one_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc_zero_siegel_theta_transformation]) (by simp)]`. Simplify `ha` using `[cc_one']`.
-/
theorem stdL_mem_Vset (M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_,
    ⟨1, one_pos, Nat.coprime_one_left M, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩
  constructor
  · intro hx y hy
    rw [herm_one_apply]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc' (hy a))
  · intro h
    rw [mem_stdL]
    intro a
    have ha := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc_zero_siegel_theta_transformation])
      (by simp)] at ha
    simpa [cc_one'] using ha

end
end GlobalTheory.SW
