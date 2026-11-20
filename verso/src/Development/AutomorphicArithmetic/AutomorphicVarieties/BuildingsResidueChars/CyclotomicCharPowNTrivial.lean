import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Establish `hcs` using `UpperTheory.V.Chr.cls_spec (k := ℚ) (Ω := Ω) N s`. Break down `Nat.lt_or_ge 1 N with hN | hN` into its components or cases. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ haveI : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω N`. Establish `h1 : ζ ^ 1 = ζ ^ (UpperTheory.V.Chr.cls ℚ Ω N s : ZMod N).val`.

Rewrite using `[pow_one, ← hcs ζ hζ.pow_eq_one, hs ζ hζ.pow_eq_one]`. Establish `hv` using `hζ.pow_inj hN (ZMod.val_lt _) h1`. Use `haveI : Fact (1 < N) := ⟨hN⟩`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`.

Apply `ZMod.val_injective` to reduce the goal to its premises. Rewrite using `[ZMod.val_one, ← hv]`. Establish `hN1 : N = 1`. Use `NeZero.pos N` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Substitute `hN1` using the available equality. Conclude with `Subsingleton.elim _ _`.
-/
private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (s : G ℚ Ω)
    (hs : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : UpperTheory.V.Chr.cls ℚ Ω N s = 1 := by
  have hcs := UpperTheory.V.Chr.cls_spec (k := ℚ) (Ω := Ω) N s
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
    have h1 : ζ ^ 1 = ζ ^ (UpperTheory.V.Chr.cls ℚ Ω N s : ZMod N).val := by
      rw [pow_one, ← hcs ζ hζ.pow_eq_one, hs ζ hζ.pow_eq_one]
    have hv := hζ.pow_inj hN (ZMod.val_lt _) h1
    haveI : Fact (1 < N) := ⟨hN⟩
    apply Units.ext
    rw [Units.val_one]
    apply ZMod.val_injective
    rw [ZMod.val_one, ← hv]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    exact Subsingleton.elim _ _

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD`. Unfold `Ctx3 at hD`. Take `⟨hg, h, t, e, ψ, hb, he0, het, hX, hIII, hA⟩` from `hD`. Consider the cases of `hA with`. Consider the case `mk he hpsi hS hxi`.

Take `⟨x, ξ', ξ₀, -, -, -, hξ⟩` from `hxi`. Establish `hl2 : l ≠ 2` using `UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good.l_odd hg`. Establish `hlp : Nat.Prime l` using `Fact.out`. Unfold `Host.CaseIII at hIII`. Establish `hne : l ≠ UpperTheory.V.pOne h.chi` using `((UpperTheory.V.HV.bchiFacts h t hb).2.2.2.2 l hlp hl2 hIII.1).2.2.2.2.2.1`.

Establish `hP : Nat.Prime (UpperTheory.V.pOne h.chi)` using `(UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1`. Use `⟨UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ, Nat.mul_pos hP.pos (by positivity), ?_, ?_⟩` and prove the remaining obligations. Introduce `hd`. Break down `(Nat.Prime.dvd_mul hlp).1 hd with h1 | h1` into its components or cases. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq hlp hP).1 h1)`.

Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 (hlp.dvd_of_dvd_pow h1))`. Unfold `KillsMu`. Introduce `s hs`. Establish `key : ∀ (M : ℕ) [NeZero M], M ∣ UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ → UpperTheory.V.Chr.cls ℚ Ω M s = 1`. Introduce `M _ hM`.

Use `cls_one M s (fun ζ hζ => hs ζ ?_)` and prove the remaining obligations. Take `⟨k, hk⟩` from `hM`. Rewrite using `[hk, pow_mul, hζ, one_pow]`. Rewrite using `[hξ, MonoidHom.mul_apply]`. Simplify using `only [UpperTheory.V.Chr.dirG, MonoidHom.comp_apply]`.

Rewrite using `[key _ (dvd_mul_right _ _), key _ (dvd_mul_left _ _), map_one, map_one, mul_one]`.
-/
theorem UpperTheory.cyclotomicChar_pow_N_trivial :
    UpperTheory.V.Sd.S3.KillsN := by
  intro Ω _ _ _ l _ c D hD
  unfold Ctx3 at hD
  obtain ⟨hg, h, t, e, ψ, hb, he0, het, hX, hIII, hA⟩ := hD
  cases hA with
  | mk he hpsi hS hxi =>
  obtain ⟨x, ξ', ξ₀, -, -, -, hξ⟩ := hxi
  have hl2 : l ≠ 2 := UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good.l_odd hg
  have hlp : Nat.Prime l := Fact.out
  unfold Host.CaseIII at hIII
  have hne : l ≠ UpperTheory.V.pOne h.chi :=
    ((UpperTheory.V.HV.bchiFacts h t hb).2.2.2.2 l hlp hl2 hIII.1).2.2.2.2.2.1
  have hP : Nat.Prime (UpperTheory.V.pOne h.chi) := (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1
  refine ⟨UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ, Nat.mul_pos hP.pos (by positivity), ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hlp).1 hd with h1 | h1
    · exact hne ((Nat.prime_dvd_prime_iff_eq hlp hP).1 h1)
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 (hlp.dvd_of_dvd_pow h1))
  · unfold KillsMu
    intro s hs
    have key : ∀ (M : ℕ) [NeZero M], M ∣ UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ →
        UpperTheory.V.Chr.cls ℚ Ω M s = 1 := by
      intro M _ hM
      refine cls_one M s (fun ζ hζ => hs ζ ?_)
      obtain ⟨k, hk⟩ := hM
      rw [hk, pow_mul, hζ, one_pow]
    rw [hξ, MonoidHom.mul_apply]
    simp only [UpperTheory.V.Chr.dirG, MonoidHom.comp_apply]
    rw [key _ (dvd_mul_right _ _), key _ (dvd_mul_left _ _), map_one, map_one, mul_one]
