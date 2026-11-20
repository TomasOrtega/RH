import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ClTwist

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

/- English proof (translation)
Rewrite `h`, the goal using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Conclude with `(Int.natCast_dvd_natCast.2 hd).trans h`.
-/
private theorem zmod_cast_eq_of_dvd_of_cast_eq {N L : ℕ} (hd : N ∣ L) {a b : ℤ} (h : (a : ZMod L) = b) : (a : ZMod N) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  exact (Int.natCast_dvd_natCast.2 hd).trans h

/- English proof (translation)
Introduce `A hA`. Rewrite `hA`, the goal using `[Gamma1_mem]`. Take `⟨h1, h2, h3⟩` from `hA`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `zmod_cast_eq_of_dvd_of_cast_eq (b := 1) hd (by exact_mod_cast h1)` after adjusting the coercions.

Conclude with `zmod_cast_eq_of_dvd_of_cast_eq (b := 1) hd (by exact_mod_cast h2)` after adjusting the coercions. Conclude with `zmod_cast_eq_of_dvd_of_cast_eq (b := 0) hd (by exact_mod_cast h3)` after adjusting the coercions.
-/
private theorem gamma1_le_of_dvd' {N L : ℕ} (hd : N ∣ L) : Gamma1 L ≤ Gamma1 N := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast zmod_cast_eq_of_dvd_of_cast_eq (b := 1) hd (by exact_mod_cast h1)
  · exact_mod_cast zmod_cast_eq_of_dvd_of_cast_eq (b := 1) hd (by exact_mod_cast h2)
  · exact_mod_cast zmod_cast_eq_of_dvd_of_cast_eq (b := 0) hd (by exact_mod_cast h3)

/- English proof (translation)
Rewrite `hA`, the goal using `[Gamma0_mem]`. Conclude with `zmod_cast_eq_of_dvd_of_cast_eq (b := 0) hd (by exact_mod_cast hA)` after adjusting the coercions.
-/
private theorem mem_gamma0_of_dvd_of_mem {N L : ℕ} (hd : N ∣ L) {A : SL(2, ℤ)} (hA : A ∈ Gamma0 L) : A ∈ Gamma0 N := by
  rw [Gamma0_mem] at hA ⊢
  exact_mod_cast zmod_cast_eq_of_dvd_of_cast_eq (b := 0) hd (by exact_mod_cast hA)

/- English proof (translation)
Rewrite `hA` using `[Gamma0_mem]`. Establish `hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1`. Use `A.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `h : ((A 0 0 : ℤ) : ZMod L) * ((A 1 1 : ℤ) : ZMod L) = 1`.

Use `congrArg (fun z : ℤ => (z : ZMod L)) hdet` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite `this` using `[hA, mul_zero, sub_zero]`. Conclude with `this`. Conclude with `⟨⟨_, _, by rw [mul_comm]; exact h, h⟩, rfl⟩`.
-/
private theorem isUnit_lower_right_of_mem_gamma0 {L : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 L) : IsUnit ((A 1 1 : ℤ) : ZMod L) := by
  rw [Gamma0_mem] at hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rwa [Matrix.det_fin_two] at this
  have h : ((A 0 0 : ℤ) : ZMod L) * ((A 1 1 : ℤ) : ZMod L) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod L)) hdet
    push_cast at this
    rw [hA, mul_zero, sub_zero] at this
    exact this
  exact ⟨⟨_, _, by rw [mul_comm]; exact h, h⟩, rfl⟩

/- English proof (translation)
Establish `hle : (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) ≤ Gamma1 N` using `Subgroup.map_mono (gamma1_le_of_dvd' hd)`. Use `⟨{ toFun := f slash_action_eq' := fun γ hγ => f.slash_action_eq' γ (hle hγ) holo' := f.holo' zero_at_cusps' := fun hc => f.zero_at_cusps' (hc.mono hle) }, rfl, ?_⟩` and prove the remaining obligations. Introduce `γ hγ`. Establish `h` using `hf γ (mem_gamma0_of_dvd_of_mem hd hγ)`. Express the relevant statement in the definitionally equal form `(f : ℍ → ℂ) ∣[(k : ℤ)] γ = _ • (f : ℍ → ℂ)`.

Rewrite using `[h]`. Use `congr 1`. Take `⟨u, hu⟩` from `isUnit_lower_right_of_mem_gamma0 hγ`. Rewrite using `[← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_intCast hd]`.
-/
private theorem raise (k N L : ℕ) [NeZero N] [NeZero L] (hd : N ∣ L) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (hf : HasChar k χ f) :
    ∃ g : CuspForm (Gamma1 L) (k : ℤ), (g : ℍ → ℂ) = f ∧ HasChar k (DirichletCharacter.changeLevel hd χ) g := by
  have hle : (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) ≤ Gamma1 N := Subgroup.map_mono (gamma1_le_of_dvd' hd)
  refine ⟨{ toFun := f
            slash_action_eq' := fun γ hγ => f.slash_action_eq' γ (hle hγ)
            holo' := f.holo'
            zero_at_cusps' := fun hc => f.zero_at_cusps' (hc.mono hle) }, rfl, ?_⟩
  intro γ hγ
  have h := hf γ (mem_gamma0_of_dvd_of_mem hd hγ)
  change (f : ℍ → ℂ) ∣[(k : ℤ)] γ = _ • (f : ℍ → ℂ)
  rw [h]
  congr 1
  obtain ⟨u, hu⟩ := isUnit_lower_right_of_mem_gamma0 hγ
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_intCast hd]

/- English proof (translation)
Take `⟨u, hu'⟩` from `hu`. Rewrite using `[← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, hu', ZMod.cast_natCast hd]`.
-/
private theorem chg {N L p : ℕ} (hd : N ∣ L) (χ : DirichletCharacter ℂ N) (hu : IsUnit (p : ZMod L)) :
    DirichletCharacter.changeLevel hd χ (p : ZMod L) = χ (p : ZMod N) := by
  obtain ⟨u, hu'⟩ := hu
  rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, hu', ZMod.cast_natCast hd]

/- English proof (translation)
Introduce `k N L _ _ hk hd χ g`. Take `⟨f1, hf1, hc1⟩` from `raise k N L hd χ g.f g.char`. Take `⟨h, hh, hcoef⟩` from `UpperTheory.V.Br.clTwist L k (DirichletCharacter.changeLevel hd χ) 1 f1 hc1`. Establish `hψu : ∀ m : ℕ, ¬ m.Coprime L → (1 : DirichletCharacter ℂ L) (m : ZMod L) = 0` using `fun m hm => MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])`. Establish `hψ1 : ∀ m : ℕ, m.Coprime L → (1 : DirichletCharacter ℂ L) (m : ZMod L) = 1` using `fun m hm => MulChar.one_apply ((ZMod.isUnit_iff_coprime m L).2 hm)`.

Establish `hc : ∀ n, coef h n = (1 : DirichletCharacter ℂ L) (n : ZMod L) * coef g.f n`. Introduce `n`. Rewrite using `[hcoef, hf1]`. Establish `hmul : ∀ a b : ℕ, (1 : DirichletCharacter ℂ L) ((a * b : ℕ) : ZMod L) = (1 : DirichletCharacter ℂ L) (a : ZMod L) * (1 : DirichletCharacter ℂ L) (b : ZMod L)` using `fun a b => by rw [Nat.cast_mul, map_mul]`. Establish `hχ' : ∀ p : ℕ, p.Coprime L → DirichletCharacter.changeLevel (dvd_mul_right L L) (DirichletCharacter.changeLevel hd χ * 1 ^ 2) (p : ZMod (L * L)) = χ (p : ZMod N)`.

Introduce `p hp`. Rewrite using `[chg _ _ ((ZMod.isUnit_iff_coprime p (L * L)).2 (Nat.Coprime.mul_right hp hp)), one_pow, mul_one, chg _ _ ((ZMod.isUnit_iff_coprime p L).2 hp)]`. Establish `hχ0 : ∀ p : ℕ, ¬ p.Coprime L → DirichletCharacter.changeLevel (dvd_mul_right L L) (DirichletCharacter.changeLevel hd χ * 1 ^ 2) (p : ZMod (L * L)) = 0`. Introduce `p hp`. Apply `MulChar.map_nonunit` to reduce the goal to its premises.

Rewrite using `[ZMod.isUnit_iff_coprime]`. Conclude with `fun hc' => hp (Nat.coprime_mul_iff_right.1 hc').1`. Use `⟨_, ⟨h, hh, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hψ1 1 (Nat.coprime_one_left L), one_mul]`. Conclude with `g.one`.

Introduce `p hp n hn`. Establish `gE` using `g.eig p hp n hn`. Distinguish the cases in `hpL : p.Coprime L`. Simplify using `only [hc, hχ' p hpL, hψ1 p hpL, hmul, one_mul] split_ifs at gE ⊢ with hpn`. Take `⟨m, rfl⟩` from `hpn`.

Rewrite `gE`, the goal using `[Nat.mul_div_cancel_left _ hp.pos]`. Simplify using `only [hmul, hψ1 p hpL, one_mul]`. Take the linear combination `(1 : DirichletCharacter ℂ L) (m : ZMod L) * gE`. Take the linear combination `(1 : DirichletCharacter ℂ L) (n : ZMod L) * gE`. Simplify using `only [hc, hχ0 p hpL, hψu p hpL, hmul, zero_mul, mul_zero, zero_add]`.

Introduce `p hp`. Use `⟨fun hpL => ?_, fun hpL => ?_⟩` and prove the remaining obligations. Establish `hcop : p.Coprime L` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hpL`. Use `⟨hχ' p hcop, ?_⟩` and prove the remaining obligations. Use `show coef h p = coef g.f p`.

Rewrite using `[hc, hψ1 p hcop, one_mul]`. Establish `hcop : ¬ p.Coprime L` using `fun hcop => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpL) show coef h p = 0`. Rewrite using `[hc, hψu p hcop, zero_mul]`.
-/
theorem UpperTheory.V.Af.Rs.deplete :
    UpperTheory.V.Af.Rs.Deplete := by
  intro k N L _ _ hk hd χ g
  obtain ⟨f1, hf1, hc1⟩ := raise k N L hd χ g.f g.char
  obtain ⟨h, hh, hcoef⟩ := UpperTheory.V.Br.clTwist L k (DirichletCharacter.changeLevel hd χ) 1 f1 hc1
  have hψu : ∀ m : ℕ, ¬ m.Coprime L → (1 : DirichletCharacter ℂ L) (m : ZMod L) = 0 := fun m hm =>
    MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  have hψ1 : ∀ m : ℕ, m.Coprime L → (1 : DirichletCharacter ℂ L) (m : ZMod L) = 1 := fun m hm =>
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m L).2 hm)
  have hc : ∀ n, coef h n = (1 : DirichletCharacter ℂ L) (n : ZMod L) * coef g.f n := by
    intro n
    rw [hcoef, hf1]
  have hmul : ∀ a b : ℕ, (1 : DirichletCharacter ℂ L) ((a * b : ℕ) : ZMod L)
      = (1 : DirichletCharacter ℂ L) (a : ZMod L) * (1 : DirichletCharacter ℂ L) (b : ZMod L) :=
    fun a b => by rw [Nat.cast_mul, map_mul]
  have hχ' : ∀ p : ℕ, p.Coprime L → DirichletCharacter.changeLevel (dvd_mul_right L L)
      (DirichletCharacter.changeLevel hd χ * 1 ^ 2) (p : ZMod (L * L)) = χ (p : ZMod N) := by
    intro p hp
    rw [chg _ _ ((ZMod.isUnit_iff_coprime p (L * L)).2 (Nat.Coprime.mul_right hp hp)), one_pow, mul_one,
      chg _ _ ((ZMod.isUnit_iff_coprime p L).2 hp)]
  have hχ0 : ∀ p : ℕ, ¬ p.Coprime L → DirichletCharacter.changeLevel (dvd_mul_right L L)
      (DirichletCharacter.changeLevel hd χ * 1 ^ 2) (p : ZMod (L * L)) = 0 := by
    intro p hp
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact fun hc' => hp (Nat.coprime_mul_iff_right.1 hc').1
  refine ⟨_, ⟨h, hh, ?_, ?_⟩, ?_⟩
  · rw [hc, hψ1 1 (Nat.coprime_one_left L), one_mul]
    exact g.one
  · intro p hp n hn
    have gE := g.eig p hp n hn
    by_cases hpL : p.Coprime L
    · simp only [hc, hχ' p hpL, hψ1 p hpL, hmul, one_mul]
      split_ifs at gE ⊢ with hpn
      · obtain ⟨m, rfl⟩ := hpn
        rw [Nat.mul_div_cancel_left _ hp.pos] at gE ⊢
        simp only [hmul, hψ1 p hpL, one_mul]
        linear_combination (1 : DirichletCharacter ℂ L) (m : ZMod L) * gE
      · linear_combination (1 : DirichletCharacter ℂ L) (n : ZMod L) * gE
    · simp only [hc, hχ0 p hpL, hψu p hpL, hmul, zero_mul, mul_zero, zero_add]
  · intro p hp
    refine ⟨fun hpL => ?_, fun hpL => ?_⟩
    · have hcop : p.Coprime L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
      refine ⟨hχ' p hcop, ?_⟩
      show coef h p = coef g.f p
      rw [hc, hψ1 p hcop, one_mul]
    · have hcop : ¬ p.Coprime L := fun hcop => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpL)
      show coef h p = 0
      rw [hc, hψu p hcop, zero_mul]
