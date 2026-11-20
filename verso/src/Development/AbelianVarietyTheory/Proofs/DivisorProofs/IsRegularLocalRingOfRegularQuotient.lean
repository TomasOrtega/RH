import Mathlib
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

/- English proof (translation)
Set `P : PrimeSpectrum R` to `⟨p, hp⟩`. Use `haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩`. Establish `h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P`. Use extensionality with `x`. Simplify using `only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]`.

Both sides reduce to the same expression. Establish `h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞)`. Rewrite using `[ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]`. Establish `h3 : p.height = Order.height P` using `PrimeSpectrum.height_eq_orderHeight P`. Rewrite using `[h2, h3, ← WithBot.coe_add]`.

Express the relevant statement in the definitionally equal form `_ ≤ Order.krullDim (PrimeSpectrum R)`. Rewrite using `[Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]`. Conclude with `le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P`.
-/
theorem height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

/- English proof (translation)
Take `⟨s, hs, hsp⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg`. Use `choose g hg using Ideal.Quotient.mk_surjective (I := p)`. Establish `hpm : p ≤ maximalIdeal R` using `le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)`. Establish `hmap : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p)` using `map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h1 : Ideal.map (Ideal.Quotient.mk p) (Ideal.span (g '' s)) = maximalIdeal (R ⧸ p)`.

Rewrite using `[Ideal.map_span, Set.image_image]`. Simplify `hsp` using `[hg]`. Establish `h2 : maximalIdeal R = Ideal.span (((s.image g) ∪ Finset.univ.image f : Finset R) : Set R)`. Establish `h3` using `congrArg (Ideal.comap (Ideal.Quotient.mk p)) (hmap.trans h1.symm)`. Rewrite `h3` using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpm]`.

Rewrite using `[h3, Finset.coe_union, Ideal.span_union, Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← hf]`. Establish `h4` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le ((s.image g) ∪ Finset.univ.image f)`. Rewrite `h4` using `[← h2]`. Establish `h5` using `Finset.card_union_le (s.image g) (Finset.univ.image f)`. Establish `h6 : (s.image g).card ≤ s.card` using `Finset.card_image_le`.

Establish `h7 : (Finset.univ.image f).card ≤ r` using `Finset.card_image_le.trans (by simp)`. Use linear arithmetic over natural numbers and integers.
-/
theorem spanFinrank_maximalIdeal_le {R : Type} [CommRing R] [IsLocalRing R] (p : Ideal R)
    [p.IsPrime] [IsLocalRing (R ⧸ p)] (r : ℕ) (f : Fin r → R) (hf : p = Ideal.span (Set.range f))
    (hfg : (maximalIdeal (R ⧸ p)).FG) :
    (maximalIdeal R).spanFinrank ≤ r + (maximalIdeal (R ⧸ p)).spanFinrank := by
  classical
  obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  choose g hg using Ideal.Quotient.mk_surjective (I := p)
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h1 : Ideal.map (Ideal.Quotient.mk p) (Ideal.span (g '' s)) = maximalIdeal (R ⧸ p) := by
    rw [Ideal.map_span, Set.image_image]
    simpa [hg] using hsp
  have h2 : maximalIdeal R =
      Ideal.span (((s.image g) ∪ Finset.univ.image f : Finset R) : Set R) := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) (hmap.trans h1.symm)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hpm] at h3
    rw [h3, Finset.coe_union, Ideal.span_union, Finset.coe_image, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, ← hf]
  have h4 := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le
    ((s.image g) ∪ Finset.univ.image f)
  rw [← h2] at h4
  have h5 := Finset.card_union_le (s.image g) (Finset.univ.image f)
  have h6 : (s.image g).card ≤ s.card := Finset.card_image_le
  have h7 : (Finset.univ.image f).card ≤ r := Finset.card_image_le.trans (by simp)
  omega

/- English proof (translation)
Introduce `R _ _ _ p _ r f hf hh hreg`. Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises. Establish `hfg : (maximalIdeal (R ⧸ p)).FG` using `IsNoetherian.noetherian _`. Establish `hs` using `spanFinrank_maximalIdeal_le p r f hf hfg`. Establish `hq : ((maximalIdeal (R ⧸ p)).spanFinrank : WithBot ℕ∞) = ringKrullDim (R ⧸ p)` using `IsRegularLocalRing.spanFinrank_maximalIdeal`.

Establish `hd` using `height_add_ringKrullDim_quotient_le p`. Rewrite `hd` using `[hh, ← hq]`. Use `le_trans ?_ hd` and prove the remaining obligations. Establish `: (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) ≤ (((r + (maximalIdeal (R ⧸ p)).spanFinrank : ℕ)) : WithBot ℕ∞)` using `by exact_mod_cast hs`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isRegularLocalRing_of_quotient_prime :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
      (r : ℕ) (f : Fin r → R), p = Ideal.span (Set.range f) → p.height = r →
      IsRegularLocalRing (R ⧸ p) → IsRegularLocalRing R := by
  intro R _ _ _ p _ r f hf hh hreg
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hfg : (maximalIdeal (R ⧸ p)).FG := IsNoetherian.noetherian _
  have hs := spanFinrank_maximalIdeal_le p r f hf hfg
  have hq : ((maximalIdeal (R ⧸ p)).spanFinrank : WithBot ℕ∞) = ringKrullDim (R ⧸ p) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd := height_add_ringKrullDim_quotient_le p
  rw [hh, ← hq] at hd
  refine le_trans ?_ hd
  have : (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) ≤
      (((r + (maximalIdeal (R ⧸ p)).spanFinrank : ℕ)) : WithBot ℕ∞) := by exact_mod_cast hs
  refine this.trans (le_of_eq ?_)
  push_cast
  rfl

end GlobalTheory.RegularAscent
