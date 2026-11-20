import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycCompat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨1, Units.ext ?_⟩` and prove the remaining obligations. Establish `: Subsingleton (ZMod (l ^ 0))`. Rewrite using `[pow_zero]`.

Use `infer_instance`. Conclude with `Subsingleton.elim _ _`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩ set k := (b : ZMod (l ^ n)).val with hkdef`. Establish `hcop : Nat.Coprime k (l ^ n)` using `ZMod.val_coe_unit_coprime b`. Establish `hk : ¬ (l : ℤ) ∣ (k : ℤ)`.

Rewrite using `[Int.natCast_dvd_natCast]`. Introduce `hd`. Establish `hc : Nat.Coprime l k` using `Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (dvd_pow_self l hn.ne') hcop)`. Establish `hg` using `Nat.dvd_gcd (dvd_refl l) hd`. Rewrite `hg` using `[Nat.Coprime.gcd_eq_one hc]`.

Conclude with `hl.ne_one (Nat.eq_one_of_dvd_one hg)`. Establish `hu : IsUnit ((k : ℤ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd _).mp h))`. Use `⟨hu.unit, Units.ext ?_⟩` and prove the remaining obligations.

Simplify using `only [KStar.TotallyRealRoots.redPow, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, map_intCast, Int.cast_natCast]`. Rewrite using `[hkdef]`. Conclude with `(map_natCast (PadicInt.toZModPow n) _).trans (ZMod.natCast_zmod_val _)`.
-/
private theorem cycIne_red_surj (l : ℕ) [Fact l.Prime] (n : ℕ) (b : (ZMod (l ^ n))ˣ) :
    ∃ u : ℤ_[l]ˣ, KStar.TotallyRealRoots.redPow l n u = b := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, Units.ext ?_⟩
    have : Subsingleton (ZMod (l ^ 0)) := by
      rw [pow_zero]
      infer_instance
    exact Subsingleton.elim _ _
  · haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    set k := (b : ZMod (l ^ n)).val with hkdef
    have hcop : Nat.Coprime k (l ^ n) := ZMod.val_coe_unit_coprime b
    have hk : ¬ (l : ℤ) ∣ (k : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      intro hd
      have hc : Nat.Coprime l k :=
        Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (dvd_pow_self l hn.ne') hcop)
      have hg := Nat.dvd_gcd (dvd_refl l) hd
      rw [Nat.Coprime.gcd_eq_one hc] at hg
      exact hl.ne_one (Nat.eq_one_of_dvd_one hg)
    have hu : IsUnit ((k : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _)
        (not_lt.mp fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd _).mp h))
    refine ⟨hu.unit, Units.ext ?_⟩
    simp only [KStar.TotallyRealRoots.redPow, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, map_intCast,
      Int.cast_natCast]
    rw [hkdef]
    exact (map_natCast (PadicInt.toZModPow n) _).trans (ZMod.natCast_zmod_val _)

/- English proof (translation)
Introduce `Ω _ _ _ N _ p _ B hB`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hp : p.Prime` using `Fact.out`. Establish `hN0 : N ≠ 0` using `NeZero.ne N`.

Use `set M := N / p ^ N.factorization p with hM`. Use `haveI : NeZero M := ⟨(Nat.ordCompl_pos p hN0).ne'⟩`. Establish `hMcop : M.Coprime p` using `(Nat.coprime_ordCompl hp hN0).symm`. Establish `hone : ∀ ζ : Ω, ζ ^ M = 1 → ζ = ζ ^ (1 % M)`. Introduce `ζ hζ`.

Break down `Nat.lt_or_ge 1 M with h | h` into its components or cases. Rewrite using `[Nat.mod_eq_of_lt h, pow_one]`. Establish `hM1 : M = 1` using `le_antisymm h (Nat.pos_of_ne_zero (NeZero.ne M))`. Rewrite using `[hM1, Nat.mod_self, pow_zero]`. Rewrite `hζ` using `[hM1, pow_one]`.

Conclude with `hζ`. Establish `hfixM : ∀ g ∈ Ine (F` using `ℚ) B, ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ := fun g hg ζ hζ => (UpperTheory.V.LDataCardLeFinrank.ineFixRoots ℚ Ω p B hB M hMcop ζ hζ).2 g hg`. Establish `hcycM : ∀ g ∈ Ine (F` using `ℚ) B, cycN ℚ Ω M g = 1 := by`. Introduce `g hg`. Rewrite using `[cycN_eq_iff]`.

Introduce `ζ hζ`. Rewrite using `[hfixM g hg ζ hζ, Units.val_one, ZMod.val_one_eq_one_mod]`. Conclude with `hone ζ hζ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `h hh`.

Take `⟨g, hg, rfl⟩` from `Subgroup.mem_map.mp hh`. Use `show cycN ℚ Ω N g ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker`. Rewrite using `[MonoidHom.mem_ker, (cycCompat ℚ Ω N).2.1 M (Nat.ordCompl_dvd N p) g]`. Conclude with `hcycM g hg`. Introduce `h hh`.

Establish `hh' : ZMod.unitsMap (Nat.ordCompl_dvd N p) h = 1` using `hh`. Take `⟨u, hu⟩` from `cycIne_red_surj p (N.factorization p) (ZMod.unitsMap (Nat.ordProj_dvd N p) h)`. Take `⟨σ, hσ, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω p B hB u`. Use `Subgroup.mem_map.mpr ⟨σ, hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[cycN_eq_iff]`.

Use `(UpperTheory.V.LDataCardLeFinrank.classIff Ω p N (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) h).mpr ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `ζ hζ`. Rewrite using `[hh', Units.val_one, ZMod.val_one_eq_one_mod]`. Use `show σ ζ = _`. Rewrite using `[hfixM σ hσ ζ hζ]`.

Conclude with `hone ζ hζ`. Rewrite using `[← hu, ← hσu]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.B1.cycIne :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (B : ValuationSubring Ω), B.valuation (p : Ω) < 1 →
    (Ine (F := ℚ) B).map (cycN ℚ Ω N) = B3.pPart N p := by
  intro Ω _ _ _ N _ p _ B hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  set M := N / p ^ N.factorization p with hM
  haveI : NeZero M := ⟨(Nat.ordCompl_pos p hN0).ne'⟩
  have hMcop : M.Coprime p := (Nat.coprime_ordCompl hp hN0).symm
  have hone : ∀ ζ : Ω, ζ ^ M = 1 → ζ = ζ ^ (1 % M) := by
    intro ζ hζ
    rcases Nat.lt_or_ge 1 M with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have hM1 : M = 1 := le_antisymm h (Nat.pos_of_ne_zero (NeZero.ne M))
      rw [hM1, Nat.mod_self, pow_zero]
      rw [hM1, pow_one] at hζ
      exact hζ
  have hfixM : ∀ g ∈ Ine (F := ℚ) B, ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ := fun g hg ζ hζ =>
    (UpperTheory.V.LDataCardLeFinrank.ineFixRoots ℚ Ω p B hB M hMcop ζ hζ).2 g hg
  have hcycM : ∀ g ∈ Ine (F := ℚ) B, cycN ℚ Ω M g = 1 := by
    intro g hg
    rw [cycN_eq_iff]
    intro ζ hζ
    rw [hfixM g hg ζ hζ, Units.val_one, ZMod.val_one_eq_one_mod]
    exact hone ζ hζ
  apply le_antisymm
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    show cycN ℚ Ω N g ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker
    rw [MonoidHom.mem_ker, (cycCompat ℚ Ω N).2.1 M (Nat.ordCompl_dvd N p) g]
    exact hcycM g hg
  · intro h hh
    have hh' : ZMod.unitsMap (Nat.ordCompl_dvd N p) h = 1 := hh
    obtain ⟨u, hu⟩ := cycIne_red_surj p (N.factorization p) (ZMod.unitsMap (Nat.ordProj_dvd N p) h)
    obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω p B hB u
    refine Subgroup.mem_map.mpr ⟨σ, hσ, ?_⟩
    rw [cycN_eq_iff]
    refine (UpperTheory.V.LDataCardLeFinrank.classIff Ω p N (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) h).mpr ⟨?_, ?_⟩
    · intro ζ hζ
      rw [hh', Units.val_one, ZMod.val_one_eq_one_mod]
      show σ ζ = _
      rw [hfixM σ hσ ζ hζ]
      exact hone ζ hζ
    · rw [← hu, ← hσu]
      rfl
