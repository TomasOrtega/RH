import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AssocFin

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

/- English proof (translation)
Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K (h * z.out)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e : (h • z : G ⧸ K) = ((h * z.out : G) : G ⧸ K)` using `by conv_lhs => rw [← QuotientGroup.out_eq' z]`. Both sides reduce to the same expression. Rewrite using `[e, hc]`.
-/
theorem out_smul_out (h : G) (z : G ⧸ K) : ∃ c : K, (h • z : G ⧸ K).out = h * z.out * c := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * z.out)
  refine ⟨c, ?_⟩
  have e : (h • z : G ⧸ K) = ((h * z.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  rw [e, hc]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hA` using `finite_supp_translate (K := K) hK f₁ h₁ 1`. Establish `hB` using `finite_supp_inv (K := K) hK f₃ h₃' g`. Establish `sA : ∀ x : G ⧸ K, x ∉ hA.toFinset → f₁ x.out = 0`. Introduce `x hx`.

Simplify using `using hx`. Establish `sB : ∀ y : G ⧸ K, y ∉ hB.toFinset → f₃ (y.out⁻¹ * g) = 0`. Introduce `y hy`. Simplify using `using hy`. Generalize the expression as in `hA.toFinset = A at sA`.

Generalize the expression as in `hB.toFinset = B at sB`. Establish `key : ∀ x z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) = f₂ (x.out⁻¹ * (x.out • z).out) * f₃ ((x.out • z).out⁻¹ * g)`. Introduce `x z`. Take `⟨c, hc⟩` from `out_smul_out K x.out z`. Rewrite using `[hc]`.

Establish `e2 : x.out⁻¹ * (x.out * z.out * c) = ((1 : K) : G) * z.out * c`. Simplify using `[mul_assoc]`. Establish `e3 : (x.out * z.out * c)⁻¹ * g = ((c⁻¹ : K) : G) * (z.out⁻¹ * (x.out⁻¹ * g)) * ((1 : K) : G)`. Simplify using `[mul_assoc]`. Rewrite using `[e2, e3, h₂, h₃]`.

Establish `inner : ∀ x : G ⧸ K, conv K f₂ f₃ (x.out⁻¹ * g) = ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g)`. Introduce `x`. Combine the equalities or inequalities in the displayed calculation. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `y hy`.

Assume the negation of the conclusion as `h`. Conclude with `(Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])`. Establish `L : conv K (conv K f₁ f₂) f₃ g = ∑ y ∈ B, ∑ x ∈ A, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g)`. Rewrite using `[show conv K (conv K f₁ f₂) f₃ g = ∑ᶠ y : G ⧸ K, (∑ᶠ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * y.out)) * f₃ (y.out⁻¹ * g) from rfl]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := B) ?_]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := A) ?_, Finset.sum_mul]`. Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `(Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])`.

Introduce `y hy`. Assume the negation of the conclusion as `h`. Conclude with `(Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])`. Establish `R : conv K f₁ (conv K f₂ f₃) g = ∑ x ∈ A, ∑ y ∈ B, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g)`. Rewrite using `[show conv K f₁ (conv K f₂ f₃) g = ∑ᶠ x : G ⧸ K, f₁ x.out * conv K f₂ f₃ (x.out⁻¹ * g) from rfl]`.

Rewrite using `[finsum_eq_sum_of_support_subset _ (s := A) ?_]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[inner x, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by ring`. Introduce `x hx`.

Assume the negation of the conclusion as `h`. Conclude with `(Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])`. Rewrite using `[L, R, Finset.sum_comm]`.
-/
theorem conv_assoc (hK : IsCommensurated K) {k : Type} [CommRing k] (f₁ f₂ f₃ : G → k)
    (h₁ : FinDosetSupp K f₁) (h₂ : IsBiInv K f₂) (h₃ : IsBiInv K f₃) (h₃' : FinDosetSupp K f₃) :
    conv K (conv K f₁ f₂) f₃ = conv K f₁ (conv K f₂ f₃) := by
  classical
  funext g
  have hA := finite_supp_translate (K := K) hK f₁ h₁ 1
  have hB := finite_supp_inv (K := K) hK f₃ h₃' g
  have sA : ∀ x : G ⧸ K, x ∉ hA.toFinset → f₁ x.out = 0 := by
    intro x hx
    simpa using hx
  have sB : ∀ y : G ⧸ K, y ∉ hB.toFinset → f₃ (y.out⁻¹ * g) = 0 := by
    intro y hy
    simpa using hy
  generalize hA.toFinset = A at sA
  generalize hB.toFinset = B at sB

  have key : ∀ x z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) =
      f₂ (x.out⁻¹ * (x.out • z).out) * f₃ ((x.out • z).out⁻¹ * g) := by
    intro x z
    obtain ⟨c, hc⟩ := out_smul_out K x.out z
    rw [hc]
    have e2 : x.out⁻¹ * (x.out * z.out * c) = ((1 : K) : G) * z.out * c := by
      simp [mul_assoc]
    have e3 : (x.out * z.out * c)⁻¹ * g =
        ((c⁻¹ : K) : G) * (z.out⁻¹ * (x.out⁻¹ * g)) * ((1 : K) : G) := by
      simp [mul_assoc]
    rw [e2, e3, h₂, h₃]
  have inner : ∀ x : G ⧸ K, conv K f₂ f₃ (x.out⁻¹ * g) =
      ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    intro x
    calc conv K f₂ f₃ (x.out⁻¹ * g)
        = ∑ᶠ z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) := rfl
      _ = ∑ᶠ z : G ⧸ K, (fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
            (MulAction.toPerm x.out z) := finsum_congr (fun z => key x z)
      _ = ∑ᶠ y : G ⧸ K, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) :=
            finsum_comp_equiv (MulAction.toPerm x.out : G ⧸ K ≃ G ⧸ K)
              (f := fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
      _ = ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
        apply finsum_eq_sum_of_support_subset
        intro y hy
        by_contra h
        exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have L : conv K (conv K f₁ f₂) f₃ g =
      ∑ y ∈ B, ∑ x ∈ A, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K (conv K f₁ f₂) f₃ g =
      ∑ᶠ y : G ⧸ K, (∑ᶠ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * y.out)) * f₃ (y.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := B) ?_]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := A) ?_, Finset.sum_mul]
      intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
    · intro y hy
      by_contra h
      exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have R : conv K f₁ (conv K f₂ f₃) g =
      ∑ x ∈ A, ∑ y ∈ B, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K f₁ (conv K f₂ f₃) g = ∑ᶠ x : G ⧸ K, f₁ x.out * conv K f₂ f₃ (x.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := A) ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [inner x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    · intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
  rw [L, R, Finset.sum_comm]

/- English proof (translation)
Introduce `G _ K k _ hK f₁ hf₁ f₂ hf₂ f₃ hf₃`. Conclude with `conv_assoc K hK f₁ f₂ f₃ hf₁.2 hf₂.1 hf₃.1 hf₃.2`.
-/
theorem hecke_assoc : Formalism.UG.HeckeAssoc := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂ f₃ hf₃
  exact conv_assoc K hK f₁ f₂ f₃ hf₁.2 hf₂.1 hf₃.1 hf₃.2

end Formalism.UG.P
