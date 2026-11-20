import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.EigenSubquot

open GlobalTheory.SmGL

/- English proof (translation)
Introduce `G _ V _ _ ρ S θ x hx hθ`. Set `S0 : Submodule ℂ V` to `Submodule.span ℂ (Set.range fun g : G => ρ g x)`. Establish `hS0 : ∀ (g : G) ⦃v : V⦄, v ∈ S0 → ρ g v ∈ S0`. Introduce `g v hv`. Establish `: S0 ≤ S0.comap (ρ g)` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by simp [map_mul]⟩)`. Conclude with `this hv`. Establish `hxS0 : x ∈ S0` using `Submodule.subset_span ⟨1, by simp⟩`. Establish `hgen : ∀ R : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ R → ρ g v ∈ R) → x ∈ R → S0 ≤ R`.

Introduce `R hR hxR`. Conclude with `Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hR h hxR)`. Set `P : Set (Submodule ℂ V)` to `{T | T ≤ S0 ∧ x ∉ T ∧ ∀ (g : G) ⦃v : V⦄, v ∈ T → ρ g v ∈ T}`. Establish `hbot : (⊥ : Submodule ℂ V) ∈ P` using `⟨bot_le, by simpa using hx, fun g v hv => by`. Rewrite using `[(Submodule.mem_bot ℂ).1 hv, map_zero]`.

Conclude with `zero_mem _⟩`. Take `⟨T, -, hT⟩` from `zorn_le_nonempty₀ P (fun c hcP hc y hy => by`. Establish `hne : c.Nonempty` using `⟨y, hy⟩`. Establish `hdir : DirectedOn (· ≤ ·) c` using `hc.directedOn`. Use `⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun hmem => ?_, fun g v hv => ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations.

Take `⟨z, hz, hxz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hmem`. Conclude with `(hcP hz).2.1 hxz`. Take `⟨z, hz, hvz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hv`. Conclude with `(Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcP hz).2.2 g hvz⟩) ⊥ hbot`. Take `⟨hTS, hxT, hTst⟩` from `hT.prop`.

Set `Sr : Subrepresentation ρ` to `⟨S0, hS0⟩`. Set `Tr : Subrepresentation ρ` to `⟨T, hTst⟩`. Establish `hcov : Tr ⋖ Sr`. Use `⟨lt_of_le_of_ne (fun v hv => hTS hv) fun h => hxT ?_, fun R h1 h2 => ?_⟩` and prove the remaining obligations. Establish `: x ∈ Sr` using `hxS0`.

Rewrite `this` using `[← h]`. Conclude with `this`. Distinguish the cases in `hxR : x ∈ R.toSubmodule`. Conclude with `h2.not_ge fun v hv => hgen R.toSubmodule R.apply_mem_toSubmodule hxR hv`. Establish `hRP : R.toSubmodule ∈ P` using `⟨fun v hv => h2.le hv, hxR, R.apply_mem_toSubmodule⟩`.

Establish `hle : T ≤ R.toSubmodule` using `fun v hv => h1.le hv`. Conclude with `h1.not_ge fun v hv => hT.2 hRP hle hv`. Use `⟨_, _, _, subQuot Sr Tr, isIrreducible_subQuot hcov, ⟨Sr, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, Submodule.Quotient.mk ⟨x, hxS0⟩, ?_, fun g hg => ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `(Submodule.Quotient.mk_eq_zero (T.comap S0.subtype) (x := (⟨x, hxS0⟩ : S0))).1 h0`.

Conclude with `hxT h1`. Use `show Submodule.Quotient.mk (Sr.toRepresentation g ⟨x, hxS0⟩) = _`. Rewrite using `[← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (hθ g hg)`.
-/
theorem exists_irreducible_subquotient_eigen : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 →
    (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧
        ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  intro G _ V _ _ ρ S θ x hx hθ
  let S0 : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hS0 : ∀ (g : G) ⦃v : V⦄, v ∈ S0 → ρ g v ∈ S0 := by
    intro g v hv
    have : S0 ≤ S0.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩)
    exact this hv
  have hxS0 : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hgen : ∀ R : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ R → ρ g v ∈ R) → x ∈ R → S0 ≤ R := by
    intro R hR hxR
    exact Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hR h hxR)
  let P : Set (Submodule ℂ V) := {T | T ≤ S0 ∧ x ∉ T ∧ ∀ (g : G) ⦃v : V⦄, v ∈ T → ρ g v ∈ T}
  have hbot : (⊥ : Submodule ℂ V) ∈ P := ⟨bot_le, by simpa using hx, fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun hmem => ?_, fun g v hv => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hmem
      exact (hcP hz).2.1 hxz
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcP hz).2.2 g hvz⟩) ⊥ hbot
  obtain ⟨hTS, hxT, hTst⟩ := hT.prop
  let Sr : Subrepresentation ρ := ⟨S0, hS0⟩
  let Tr : Subrepresentation ρ := ⟨T, hTst⟩
  have hcov : Tr ⋖ Sr := by
    refine ⟨lt_of_le_of_ne (fun v hv => hTS hv) fun h => hxT ?_, fun R h1 h2 => ?_⟩
    · have : x ∈ Sr := hxS0
      rw [← h] at this
      exact this
    by_cases hxR : x ∈ R.toSubmodule
    · exact h2.not_ge fun v hv => hgen R.toSubmodule R.apply_mem_toSubmodule hxR hv
    · have hRP : R.toSubmodule ∈ P := ⟨fun v hv => h2.le hv, hxR, R.apply_mem_toSubmodule⟩
      have hle : T ≤ R.toSubmodule := fun v hv => h1.le hv
      exact h1.not_ge fun v hv => hT.2 hRP hle hv
  refine ⟨_, _, _, subQuot Sr Tr, isIrreducible_subQuot hcov,
    ⟨Sr, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩,
    Submodule.Quotient.mk ⟨x, hxS0⟩, ?_, fun g hg => ?_⟩
  · intro h0
    have h1 := (Submodule.Quotient.mk_eq_zero (T.comap S0.subtype) (x := (⟨x, hxS0⟩ : S0))).1 h0
    exact hxT h1
  · show Submodule.Quotient.mk (Sr.toRepresentation g ⟨x, hxS0⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hθ g hg)

end GlobalTheory.EigenSubquot
