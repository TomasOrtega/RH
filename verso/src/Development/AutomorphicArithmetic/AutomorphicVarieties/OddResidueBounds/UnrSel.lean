import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ hζE`. Take `⟨ζ₀, hζ₀⟩` from `hζE`. Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Use `haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩`. Establish `hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l` using `hζ₀.map_of_injective (algebraMap E Ω).injective`.

Establish `hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀` using `fun g => g.commutes ζ₀`. Establish `hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧ ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β`. Introduce `φ`. Take `⟨hlc, hadd, -⟩` from `φ.2`. Conclude with `radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])`.

Use `choose β a hβa hgβ using hdata`. Establish `hsel : ∀ φ, a φ ∈ SelK (Above E l) l`. Introduce `φ`. Use `show ∀ v ∉ Above E l, _`. Introduce `v hv`.

Take `⟨A, hA⟩` from `exists_isPlaceOver Ω v`. Use `dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hnot : ¬ A.valuation (l : Ω) < 1` using `fun h => hv (((placeDict E Ω).2.2.2 A v l hA).mp h)`. Establish `h0 : φ.1 g = 0` using `φ.2.2.2 A hnot g hg`.

Rewrite using `[hgβ, h0, ZMod.val_zero, pow_zero, one_mul]`. Use `⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩` and prove the remaining obligations. Rewrite `hfe` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Take `⟨c, hc⟩` from `hfe`. Establish `hc' : a ψ = a φ * c ^ l`.

Establish `h : c ^ l = (a φ)⁻¹ * a ψ` using `by simpa using hc`. Rewrite using `[h, mul_inv_cancel_left]`. Establish `hβne : ∀ φ, β φ ≠ 0`. Introduce `φ h`. Establish `h'` using `hβa φ`.

Rewrite `h'` using `[h, zero_pow (NeZero.ne l)]`. Conclude with `(a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)`. Establish `hcΩ : algebraMap E Ω (c : E) ≠ 0` using `(map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Establish `hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1`. Rewrite using `[div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]`. Conclude with `div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one hγl`. Establish `hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c)`.

Rewrite using `[← hi, map_pow, hgζ]`. Establish `hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0` using `div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)`. Establish `hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) = algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val * (β ψ / (β φ * algebraMap E Ω c))`. Rewrite using `[map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]`. Establish `hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0` using `pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))`.

Establish `hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1`. Apply `mul_right_cancel₀ hγ0` to reduce the goal to its premises. Rewrite using `[one_mul, ← hgγ', hgγ]`. Establish `hpow` using `((div_eq_one_iff_eq hζb).mp hq).symm`. Conclude with `ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)`.
-/
theorem UpperTheory.V.Odd.unrSel :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], (∃ ζ : E, IsPrimitiveRoot ζ l) → ∃ f : UnrHom E Ω l → SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l), Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ hζE
  obtain ⟨ζ₀, hζ₀⟩ := hζE
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
  have hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l := hζ₀.map_of_injective (algebraMap E Ω).injective
  have hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧
      ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β := by
    intro φ
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above E l) l := by
    intro φ
    show ∀ v ∉ Above E l, _
    intro v hv
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_
    intro g hg
    have hnot : ¬ A.valuation (l : Ω) < 1 := fun h => hv (((placeDict E Ω).2.2.2 A v l hA).mp h)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := by
    intro φ h
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)
  have hcΩ : algebraMap E Ω (c : E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) =
      algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap E Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]
  have hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))
  have hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1 := by
    apply mul_right_cancel₀ hγ0
    rw [one_mul, ← hgγ', hgγ]
  have hpow := ((div_eq_one_iff_eq hζb).mp hq).symm
  exact ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
