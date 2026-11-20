import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.ZH

/- English proof (translation)
Take `⟨i, hi⟩` from `h.1 (genericPoint M.Z)`. Take `⟨U, hU, hD, hR⟩` from `h.2 i hi.1`. Establish `hne : (U : Set M.Z).Nonempty` using `⟨genericPoint M.Z, by rw [hD]; exact hi⟩`. Set `A : Subalgebra o Ω` to `{ K.toSubring with algebraMap_mem' := hc }`. Establish `hle : M.ringOn U ≤ A`.

Rewrite using `[hR]`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hr i j`. Use `top_unique fun x _ => ?_` and prove the remaining obligations.

Take `⟨a, b, -, rfl⟩` from `RatModel.exists_eq_div hU hne x`. Conclude with `div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩)) (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))`.
-/
theorem RatModel.IsCl.subfield_eq_top_of_ratios {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {M : RatModel o Ω} {J : Type} {t : J → Ω} (h : M.IsCl t) (K : Subfield Ω)
    (hc : ∀ a, algebraMap o Ω a ∈ K) (hr : ∀ i j, t j / t i ∈ K) : K = ⊤ := by
  obtain ⟨i, hi⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, by rw [hD]; exact hi⟩
  let A : Subalgebra o Ω := { K.toSubring with algebraMap_mem' := hc }
  have hle : M.ringOn U ≤ A := by
    rw [hR]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact hr i j
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

/- English proof (translation)
Take `⟨x, hx⟩` from `S.th_ne`. Establish `htop` using `h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ …`. Use `Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[htop]`. Conclude with `Subfield.mem_top y`.
-/
theorem finite_closure_theta_ratios_of_isCl (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) (J : Type) (t : J → Ω) (h : M.IsCl t) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  obtain ⟨x, hx⟩ := S.th_ne
  have htop := h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)}))
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ hx).symm⟩))
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]
  exact Subfield.mem_top y

end GlobalTheory.ZH
