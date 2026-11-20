import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply `Prod.ext` to reduce the goal to its premises. Establish `key : pInf E (a.1.1 i j) = pInf E (b.1.1 i j)`.

Use function extensionality and compare the values at `w`. Establish `h` using `congrArg (fun g : GL (Fin n) ℂ => g.1 i j) (hinf w.embedding)`. Simplify using `only [cEmb, cInf, MonoidHom.comp_apply, GeneralLinearGroup.map, Subgroup.coe_subtype] at h`. Express the relevant statement in the definitionally equal form `coord w.embedding (pInf E (a.1.1 i j)) = coord w.embedding (pInf E (b.1.1 i j)) at h`. Establish `hw : InfinitePlace.mk w.embedding = w` using `InfinitePlace.mk_embedding w`.

Unfold `coord at h`. Rewrite `h` using `[if_pos (by rw [hw])]`. Simplify `h` using `[hw]`. Conclude with `(infEq E).symm.injective key`. Establish `h` using `congrArg (fun g : GL (Fin n) (Af E) => g.1 i j) hfin`.

Conclude with `h`.
-/
theorem UA_ext_cEmb {a b : UA E n}
    (hfin : GeneralLinearGroup.map (pFin E) a.1 = GeneralLinearGroup.map (pFin E) b.1)
    (hinf : ∀ τ : E →+* ℂ, cEmb τ a = cEmb τ b) : a = b := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply Prod.ext
  · have key : pInf E (a.1.1 i j) = pInf E (b.1.1 i j) := by
      funext w
      have h := congrArg (fun g : GL (Fin n) ℂ => g.1 i j) (hinf w.embedding)
      simp only [cEmb, cInf, MonoidHom.comp_apply, GeneralLinearGroup.map, Subgroup.coe_subtype] at h
      change coord w.embedding (pInf E (a.1.1 i j)) = coord w.embedding (pInf E (b.1.1 i j)) at h
      have hw : InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding w
      unfold coord at h
      rw [if_pos (by rw [hw])] at h
      simpa [hw] using h
    exact (infEq E).symm.injective key
  · have h := congrArg (fun g : GL (Fin n) (Af E) => g.1 i j) hfin
    exact h

/- English proof (translation)
Introduce `x hx y hy`. Simplify using `only [embU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx hy`. Take `⟨hxf, hxi⟩` from `hx`. Take `⟨hyf, hyi⟩` from `hy`. Rewrite `hxf`, `hyf` using `[infU, MonoidHom.mem_ker]`.

Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxf hyf`. Apply `UA_ext_cEmb` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, map_mul, hxf, hyf]`. Introduce `σ`. Simplify using `only [map_mul]`.

Distinguish the cases in `h : InfinitePlace.mk σ = InfinitePlace.mk τ`. Establish `: InfinitePlace.mk σ ≠ InfinitePlace.mk τ'` using `h ▸ hne`. Rewrite using `[hyi σ this, one_mul, mul_one]`. Rewrite using `[hxi σ h, one_mul, mul_one]`.
-/
theorem embU_commute (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ)
    (hne : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') : ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  intro x hx y hy
  simp only [embU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx hy
  obtain ⟨hxf, hxi⟩ := hx
  obtain ⟨hyf, hyi⟩ := hy
  rw [infU, MonoidHom.mem_ker] at hxf hyf
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxf hyf
  apply UA_ext_cEmb
  · simp only [Subgroup.coe_mul, map_mul, hxf, hyf]
  · intro σ
    simp only [map_mul]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · have : InfinitePlace.mk σ ≠ InfinitePlace.mk τ' := h ▸ hne
      rw [hyi σ this, one_mul, mul_one]
    · rw [hxi σ h, one_mul, mul_one]

end GlobalTheory.UnitaryBC
