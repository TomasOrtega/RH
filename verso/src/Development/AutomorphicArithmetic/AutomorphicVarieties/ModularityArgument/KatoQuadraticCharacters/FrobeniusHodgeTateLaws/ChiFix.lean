import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiFixAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers

namespace UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Introduce `l _ ι N χ χd hχ`. Establish `hinj : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) = ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l])) → x = y`. Introduce `x y h`. Conclude with `PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective (ι.injective h))`. Establish `hF1 : ι (algebraMap ℚ_[l] (Qbar l) ((1 : ℤ_[l]) : ℚ_[l])) = 1` using `by simp`.

Establish `hFm : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) ((x * y : ℤ_[l]) : ℚ_[l])) = ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) * ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l]))`. Introduce `x y`. Simplify using the standard rewrite rules. Establish `hFp : ∀ (x : ℤ_[l]) (k : ℕ), ι (algebraMap ℚ_[l] (Qbar l) ((x ^ k : ℤ_[l]) : ℚ_[l])) = ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) ^ k`. Introduce `x k`.

Simplify using the standard rewrite rules. Establish `hcop : ∀ a : ℕ, a.Coprime N ↔ (a % N).Coprime N`. Introduce `a`. Rewrite using `[Nat.Coprime, Nat.Coprime, Nat.gcd_comm a N, Nat.gcd_rec]`. Use `⟨fun d => if d.Coprime N then χd d else 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `d hd dsimp only`. Rewrite using `[if_pos hd]`. Introduce `d hd dsimp only`. Rewrite using `[if_pos hd]`. Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases.

Substitute `hN` using the available equality. Establish `hd1 : d = 1` using `Nat.coprime_zero_right d |>.1 hd`. Substitute `hd1` using the available equality. Establish `h1 : χd 1 = 1` using `hinj _ _ (by rw [hχ 1 hd, hF1]; simp)`. Rewrite using `[h1]`.

Conclude with `isUnit_one`. Establish `hk : (χd d) ^ Nat.totient N = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hFp, hχ d hd, hF1, ← map_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient hd), Nat.cast_one, map_one]`. Conclude with `IsUnit.of_pow_eq_one hk (Nat.totient_pos.2 hN).ne'`.

Introduce `a b dsimp only`. Distinguish the cases in `ha : a.Coprime N`. Distinguish the cases in `hb : b.Coprime N`. Establish `hab : (a * b).Coprime N` using `Nat.Coprime.mul ha hb`. Rewrite using `[if_pos hab, if_pos ha, if_pos hb]`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hFm, hχ _ hab, hχ _ ha, hχ _ hb, Nat.cast_mul, map_mul]`. Establish `hab : ¬ (a * b).Coprime N` using `fun h => hb (Nat.Coprime.coprime_mul_left h)`. Rewrite using `[if_neg hab, if_neg hb, mul_zero]`. Establish `hab : ¬ (a * b).Coprime N` using `fun h => ha (Nat.Coprime.coprime_mul_right h)`.

Rewrite using `[if_neg hab, if_neg ha, zero_mul]`. Introduce `a b hab dsimp only`. Establish `hiff : a.Coprime N ↔ b.Coprime N` using `by rw [hcop a, hcop b, hab]`. Distinguish the cases in `ha : a.Coprime N`. Establish `hb : b.Coprime N` using `hiff.1 ha`.

Rewrite using `[if_pos ha, if_pos hb]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hχ _ ha, hχ _ hb, (ZMod.natCast_eq_natCast_iff' a b N).2 hab]`. Establish `hb : ¬ b.Coprime N` using `fun h => ha (hiff.2 h)`. Rewrite using `[if_neg ha, if_neg hb]`.
-/
theorem chiFix : ChiFix := by
  intro l _ ι N χ χd hχ
  have hinj : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l])) → x = y := by
    intro x y h
    exact PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective (ι.injective h))
  have hF1 : ι (algebraMap ℚ_[l] (Qbar l) ((1 : ℤ_[l]) : ℚ_[l])) = 1 := by simp
  have hFm : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) ((x * y : ℤ_[l]) : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) * ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l])) := by
    intro x y
    simp
  have hFp : ∀ (x : ℤ_[l]) (k : ℕ), ι (algebraMap ℚ_[l] (Qbar l) ((x ^ k : ℤ_[l]) : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) ^ k := by
    intro x k
    simp
  have hcop : ∀ a : ℕ, a.Coprime N ↔ (a % N).Coprime N := by
    intro a
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm a N, Nat.gcd_rec]
  refine ⟨fun d => if d.Coprime N then χd d else 0, ?_, ?_, ?_, ?_⟩
  · intro d hd
    dsimp only
    rw [if_pos hd]
  · intro d hd
    dsimp only
    rw [if_pos hd]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hd1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
      subst hd1
      have h1 : χd 1 = 1 := hinj _ _ (by rw [hχ 1 hd, hF1]; simp)
      rw [h1]
      exact isUnit_one
    · have hk : (χd d) ^ Nat.totient N = 1 := by
        apply hinj
        rw [hFp, hχ d hd, hF1, ← map_pow, ← Nat.cast_pow,
          (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient hd), Nat.cast_one, map_one]
      exact IsUnit.of_pow_eq_one hk (Nat.totient_pos.2 hN).ne'
  · intro a b
    dsimp only
    by_cases ha : a.Coprime N
    · by_cases hb : b.Coprime N
      · have hab : (a * b).Coprime N := Nat.Coprime.mul ha hb
        rw [if_pos hab, if_pos ha, if_pos hb]
        apply hinj
        rw [hFm, hχ _ hab, hχ _ ha, hχ _ hb, Nat.cast_mul, map_mul]
      · have hab : ¬ (a * b).Coprime N := fun h => hb (Nat.Coprime.coprime_mul_left h)
        rw [if_neg hab, if_neg hb, mul_zero]
    · have hab : ¬ (a * b).Coprime N := fun h => ha (Nat.Coprime.coprime_mul_right h)
      rw [if_neg hab, if_neg ha, zero_mul]
  · intro a b hab
    dsimp only
    have hiff : a.Coprime N ↔ b.Coprime N := by rw [hcop a, hcop b, hab]
    by_cases ha : a.Coprime N
    · have hb : b.Coprime N := hiff.1 ha
      rw [if_pos ha, if_pos hb]
      apply hinj
      rw [hχ _ ha, hχ _ hb, (ZMod.natCast_eq_natCast_iff' a b N).2 hab]
    · have hb : ¬ b.Coprime N := fun h => ha (hiff.2 h)
      rw [if_neg ha, if_neg hb]

end UpperTheory.V.Z.Kato.Joint

end
