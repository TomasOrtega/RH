import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

/- English proof (translation)
Establish `hs : rStab (fun _ : H => c) = ⊤`. Use extensionality with `k`. Simplify using `[rStab]`. Unfold `avg`. Rewrite using `[hs, Subgroup.index_top]`.

Use `haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top`. Use `haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))`. Rewrite using `[finsum_unique]`. Simplify using the standard rewrite rules.
-/
theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

/- English proof (translation)
Unfold `twOrb`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `q`. Use `set Q : G := Quotient.out q with hQ`. Establish `hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k))) = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q)`.

Use function extensionality and compare the values at `k`. Establish `he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k`. Simplify using `only [MonoidHom.id_apply]`. Use `group`. Rewrite using `[he]`.

Distinguish the cases in `h : Q⁻¹ * γ * Q ∈ K`. Establish `h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K` using `K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2`. Simplify using `[Set.indicator_apply, h, h']`. Establish `h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K`. Introduce `h'`.

Apply `h` to reduce the goal to its premises. Use `K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Simplify using `[Set.indicator_apply, h, h']`. Rewrite using `[hfun, avg_const_fun]`.

Distinguish the cases in `h : Q⁻¹ * γ * Q ∈ K`. Simplify using `[Set.indicator_apply, h]`. Simplify using `[Set.indicator_apply, h]`.
-/
theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
