import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CapTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ClTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

/- English proof (translation)
Use `haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩`. Take `⟨h, hc, hn⟩` from `clTwist N k χ ψ⁻¹ g.f g.char`. Establish `h0 : h ≠ 0`. Introduce and unpack `rfl`. Use `hn 1` as an intermediate fact.

Rewrite `this` using `[g.one, Nat.cast_one, map_one, mul_one]`. Simplify using `[coef, UpperHalfPlane.qExpansion_zero] at this`. Take `⟨g', hg'⟩` from `eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p`. Use `⟨_, g', fun p hp hd => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (p : ZMod (N * N))` using `(ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)`.

Establish `hu' : IsUnit (p : ZMod N)` using `(ZMod.isUnit_prime_iff_not_dvd hp).2 hd`. Establish `e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) = χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2`. Use `DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)]`. Rewrite using `[this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]`.

Establish `e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1`. Rewrite using `[← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hg' p hp fun n h1 => ?_]`. Take the linear combination `g.a p * e1`.

Use `g.eig p hp n h1` as an intermediate fact. Rewrite using `[e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]`. Distinguish the cases in `hpn : p ∣ n`. Take `⟨m, rfl⟩` from `hpn`. Rewrite `this`, the goal using `[if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos]`.

Rewrite using `[hn, Nat.cast_mul, map_mul]`. Take the linear combination `ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this`. Rewrite `this`, the goal using `[if_neg hpn]`. Take the linear combination `ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this`. Rewrite using `[e]`.

Take the linear combination `χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1`.
-/
private theorem untwist (k N : ℕ) [NeZero N] (hk : 1 ≤ k) (χ ψ : DirichletCharacter ℂ N) (g : Eigenform k N χ) :
    ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'), ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      g'.a p * ψ (p : ZMod N) = g.a p ∧ χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
  have h0 : h ≠ 0 := by
    rintro rfl
    have := hn 1
    rw [g.one, Nat.cast_one, map_one, mul_one] at this
    simp [coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨g', hg'⟩ := eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
  refine ⟨_, g', fun p hp hd => ?_⟩
  have hu : IsUnit (p : ZMod (N * N)) :=
    (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
  have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
      χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
  constructor
  · rw [hg' p hp fun n h1 => ?_]
    · linear_combination g.a p * e1
    have := g.eig p hp n h1
    rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
      rw [hn, Nat.cast_mul, map_mul]
      linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
    · rw [if_neg hpn] at this ⊢
      linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
  · rw [e]
    linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `hf ((finDim N k).2 f fun n hn => (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))`.
-/
private theorem eig_unique {k N p : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} (hf : f ≠ 0)
    {a b : ℂ} (ha : IsEigAt k χ f p a) (hb : IsEigAt k χ f p b) : a = b := by
  by_contra h
  exact hf ((finDim N k).2 f fun n hn =>
    (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))

/- English proof (translation)
Use extensionality with `g`. Use `⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩` and prove the remaining obligations. Use `haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)`. Conclude with `Subsingleton.elim _ _`.
-/
private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    K1 w 0 = GlobalTheory.LFun.KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

/- English proof (translation)
Establish `hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1`. Simplify using `only [TR.lieS_apply, ← map_sum]`. Conclude with `congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm`. Establish `h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i` using `fun i => by`. Rewrite using `[TR.Eop_eq]`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`. Simplify using the standard rewrite rules. Rewrite using `[hX, Fin.sum_univ_two, h1, h1]`.

Conclude with `h _`.
-/
private theorem lie_one (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) : TR.lie ℚ 2 (TR.oneL ℚ 2) φ = 0 := by
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by
    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1]
  exact h _

/- English proof (translation)
Establish `h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0` using `by simpa using h`. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `not_not.1 hw`. Use `Ideal.dvd_span_singleton.2 ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, (places w).2.1]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
