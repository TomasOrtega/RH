import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[hF.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, _root_.mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun j _ => mul_pow _ _ _`.
-/
theorem eval₂_scale_of_isHomogeneous {o σ S : Type} [CommRing o] [CommRing S] (f : o →+* S)
    (g : σ → S) (u : S) {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ f (fun j => g j * u) F = MvPolynomial.eval₂ f g F * u ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, _root_.mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

/- English proof (translation)
Set `x` to `Ideal.Quotient.mk I (MvPolynomial.X i)`. Set `L` to `Localization.Away x`. Set `g : MvPolynomial σ o →+* L` to `(algebraMap (MvPolynomial σ o ⧸ I) L).comp (Ideal.Quotient.mk I)`. Set `u : L` to `IsLocalization.Away.invSelf x`. Set `ψ : MvPolynomial σ o →+* L` to `MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u)`.

Establish `hg : ∀ F : MvPolynomial σ o, MvPolynomial.eval₂ (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j)) F = g F`. Introduce `F`. Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [MvPolynomial.eval₂_add, hp, hq, map_add]`.

Consider the case `mul_X p j hp => rw [MvPolynomial.eval₂_mul, hp, MvPolynomial.eval₂_X, map_mul]`. Establish `hxu : g (MvPolynomial.X i) * u = 1` using `IsLocalization.Away.mul_invSelf x`. Use `⟨ψ, fun c => by exact MvPolynomial.eval₂Hom_C _ _ c, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Set `J` to `I ⊔ Ideal.span {MvPolynomial.X i - 1}`. Set `q : MvPolynomial σ o ⧸ I →+* MvPolynomial σ o ⧸ J` to `Ideal.Quotient.lift I (Ideal.Quotient.mk J) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_left (a := I) ha))`.

Establish `hq1 : q x = 1`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J (MvPolynomial.X i) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `le_sup_right (a := I) (Ideal.subset_span (Set.mem_singleton _))`. Establish `hunit : IsUnit (q x)` using `by rw [hq1]; exact isUnit_one`.

Set `θ : L →+* MvPolynomial σ o ⧸ J` to `IsLocalization.Away.lift x hunit`. Establish `hθ : ∀ a, θ (algebraMap _ L a) = q a` using `IsLocalization.Away.lift_eq x hunit`. Establish `hθu : θ u = 1`. Establish `h` using `congrArg θ hxu`. Rewrite `h` using `[map_mul, map_one]`.

Establish `h' : θ (g (MvPolynomial.X i)) = 1`. Express the relevant statement in the definitionally equal form `θ (algebraMap _ L x) = 1`. Rewrite using `[hθ, hq1]`. Rewrite `h` using `[h', _root_.one_mul]`. Then use the resulting hypothesis. Establish `hcomp : θ.comp ψ = Ideal.Quotient.mk J`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Rewrite using `[RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.C c)) = _`. Rewrite using `[MvPolynomial.eval₂Hom_C]`.

Express the relevant statement in the definitionally equal form `θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.C c))) = _`. Rewrite using `[hθ]`. Both sides reduce to the same expression. Introduce `j`. Rewrite using `[RingHom.comp_apply]`.

Express the relevant statement in the definitionally equal form `θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X j)) = _`. Rewrite using `[MvPolynomial.eval₂Hom_X', map_mul, hθu, _root_.mul_one]`. Express the relevant statement in the definitionally equal form `θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.X j))) = _`. Rewrite using `[hθ]`. Both sides reduce to the same expression.

Introduce `F hF`. Rewrite `hF` using `[RingHom.mem_ker]`. Establish `h0 : Ideal.Quotient.mk J F = 0`. Rewrite using `[← hcomp, RingHom.comp_apply, hF, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h0`.

Apply `sup_le` to reduce the goal to its premises. Introduce `F hF`. Rewrite using `[RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]`. Use `Finset.sum_eq_zero fun e _ => ?_` and prove the remaining obligations. Establish `h1` using `eval₂_scale_of_isHomogeneous (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j)) u (MvPolynomial.homogeneousComponent_isHomogeneous e F)`.

Rewrite using `[MvPolynomial.coe_eval₂Hom, h1, hg]`. Establish `h2 : Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent e F) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (hI F hF e)`. Express the relevant statement in the definitionally equal form `algebraMap _ L (Ideal.Quotient.mk I _) * _ = 0`. Rewrite using `[h2, map_zero, zero_mul]`. Rewrite using `[Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]`.

Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X i) - 1 = 0`. Rewrite using `[MvPolynomial.eval₂Hom_X', hxu, sub_self]`.
-/
theorem exists_ker_eq_dehomogenisation {o σ : Type} [CommRing o] (I : Ideal (MvPolynomial σ o))
    (i : σ) (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) :
    ∃ ψ : MvPolynomial σ o →+*
        Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)),
      (∀ c, ψ (MvPolynomial.C c) = algebraMap (MvPolynomial σ o ⧸ I) _
        (Ideal.Quotient.mk I (MvPolynomial.C c))) ∧
      RingHom.ker ψ = I ⊔ Ideal.span {MvPolynomial.X i - 1} := by
  classical
  let x := Ideal.Quotient.mk I (MvPolynomial.X i)
  let L := Localization.Away x
  let g : MvPolynomial σ o →+* L :=
    (algebraMap (MvPolynomial σ o ⧸ I) L).comp (Ideal.Quotient.mk I)
  let u : L := IsLocalization.Away.invSelf x
  let ψ : MvPolynomial σ o →+* L :=
    MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u)

  have hg : ∀ F : MvPolynomial σ o,
      MvPolynomial.eval₂ (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j)) F = g F := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [MvPolynomial.eval₂_add, hp, hq, map_add]
    | mul_X p j hp => rw [MvPolynomial.eval₂_mul, hp, MvPolynomial.eval₂_X, map_mul]
  have hxu : g (MvPolynomial.X i) * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨ψ, fun c => by exact MvPolynomial.eval₂Hom_C _ _ c, le_antisymm ?_ ?_⟩
  ·
    let J := I ⊔ Ideal.span {MvPolynomial.X i - 1}
    let q : MvPolynomial σ o ⧸ I →+* MvPolynomial σ o ⧸ J :=
      Ideal.Quotient.lift I (Ideal.Quotient.mk J)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_left (a := I) ha))
    have hq1 : q x = 1 := by
      change Ideal.Quotient.mk J (MvPolynomial.X i) = 1
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_right (a := I) (Ideal.subset_span (Set.mem_singleton _))
    have hunit : IsUnit (q x) := by rw [hq1]; exact isUnit_one
    let θ : L →+* MvPolynomial σ o ⧸ J := IsLocalization.Away.lift x hunit
    have hθ : ∀ a, θ (algebraMap _ L a) = q a := IsLocalization.Away.lift_eq x hunit
    have hθu : θ u = 1 := by
      have h := congrArg θ hxu
      rw [map_mul, map_one] at h
      have h' : θ (g (MvPolynomial.X i)) = 1 := by
        change θ (algebraMap _ L x) = 1
        rw [hθ, hq1]
      rwa [h', _root_.one_mul] at h
    have hcomp : θ.comp ψ = Ideal.Quotient.mk J := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.C c)) = _
        rw [MvPolynomial.eval₂Hom_C]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.C c))) = _
        rw [hθ]
        rfl
      · intro j
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X j)) = _
        rw [MvPolynomial.eval₂Hom_X', map_mul, hθu, _root_.mul_one]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.X j))) = _
        rw [hθ]
        rfl
    intro F hF
    rw [RingHom.mem_ker] at hF
    have h0 : Ideal.Quotient.mk J F = 0 := by
      rw [← hcomp, RingHom.comp_apply, hF, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · apply sup_le
    ·
      intro F hF
      rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      have h1 := eval₂_scale_of_isHomogeneous (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j)) u (MvPolynomial.homogeneousComponent_isHomogeneous e F)
      rw [MvPolynomial.coe_eval₂Hom, h1, hg]
      have h2 : Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent e F) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hI F hF e)
      change algebraMap _ L (Ideal.Quotient.mk I _) * _ = 0
      rw [h2, map_zero, zero_mul]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      change MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X i) - 1 = 0
      rw [MvPolynomial.eval₂Hom_X', hxu, sub_self]

/- English proof (translation)
Introduce `o σ _ I i hI`. Take `⟨ψ, hC, hker⟩` from `exists_ker_eq_dehomogenisation I i hI`. Rewrite using `[← hker]`. Use `⟨fun hrad => ?_, fun htf c F hc hF => ?_⟩` and prove the remaining obligations. Establish `: IsReduced (MvPolynomial σ o ⧸ I)` using `(Ideal.isRadical_iff_quotient_reduced I).mp hrad`.

Introduce and unpack `F ⟨n, hn⟩`. Rewrite `hn`, the goal using `[RingHom.mem_ker]`. Rewrite `hn` using `[map_pow]`. Conclude with `IsReduced.eq_zero _ ⟨n, hn⟩`. Rewrite `hF` using `[RingHom.mem_ker, map_mul]`.

Rewrite using `[RingHom.mem_ker]`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.mk'_surjective (S := Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i))) (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X i))) (ψ F)`. Simplify using `only at hs`. Rewrite `hF` using `[← hs, hC, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨⟨_, k, rfl⟩, hm⟩` from `hF`.

Take `⟨G, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `hIG : MvPolynomial.C c * (MvPolynomial.X i ^ k * G) ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hm]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hG : MvPolynomial.X i ^ k * G ∈ I` using `htf c _ hc hIG`. Rewrite using `[← hs, IsLocalization.mk'_eq_zero_iff]`. Use `⟨⟨_, k, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (MvPolynomial.X i) ^ k * Ideal.Quotient.mk I G = 0`. Rewrite using `[← map_pow, ← map_mul]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hG`.
-/
theorem dehomogenisation_isRadical_and_torsionFree :
    ∀ (o σ : Type) [CommRing o] (I : Ideal (MvPolynomial σ o)) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (I.IsRadical → (I ⊔ Ideal.span {MvPolynomial.X i - 1}).IsRadical) ∧ ((∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1} → F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  intro o σ _ I i hI
  obtain ⟨ψ, hC, hker⟩ := exists_ker_eq_dehomogenisation I i hI
  rw [← hker]
  refine ⟨fun hrad => ?_, fun htf c F hc hF => ?_⟩
  ·
    have : IsReduced (MvPolynomial σ o ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
    rintro F ⟨n, hn⟩
    rw [RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  ·
    rw [RingHom.mem_ker, map_mul] at hF
    rw [RingHom.mem_ker]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective
      (S := Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)))
      (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X i))) (ψ F)
    simp only at hs
    rw [← hs, hC, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hF
    obtain ⟨⟨_, k, rfl⟩, hm⟩ := hF
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hIG : MvPolynomial.C c * (MvPolynomial.X i ^ k * G) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      simp only [map_mul, map_pow]
      ring
    have hG : MvPolynomial.X i ^ k * G ∈ I := htf c _ hc hIG
    rw [← hs, IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.X i) ^ k * Ideal.Quotient.mk I G = 0
    rw [← map_pow, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG

end GlobalTheory
