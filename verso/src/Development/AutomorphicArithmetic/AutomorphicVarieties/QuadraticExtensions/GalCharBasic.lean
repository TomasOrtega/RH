import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Establish `hs` using `galChar_spec m g ζ hζ.pow_eq_one`. Rewrite `hs` using `[h]`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero (NeZero.ne m)`. Establish `hmod : a ≡ (galChar Ω m g : ZMod m).val [MOD m]`. Establish `e1 : ζ ^ a = ζ ^ (a % m)` using `by conv_lhs => rw [← Nat.div_add_mod a m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]`.

Establish `e2 : ζ ^ (galChar Ω m g : ZMod m).val = ζ ^ ((galChar Ω m g : ZMod m).val % m)` using `by conv_lhs => rw [← Nat.div_add_mod (galChar Ω m g : ZMod m).val m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]`. Conclude with `hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) (by rw [← e1, ← e2, hs])`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod` as an intermediate fact. Rewrite `this` using `[ZMod.natCast_zmod_val]`. Conclude with `this.symm`.
-/
private theorem gcb_key (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m]
    (g : G ℚ Ω) (a : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) (h : g ζ = ζ ^ a) : (galChar Ω m g : ZMod m) = a := by
  have hs := galChar_spec m g ζ hζ.pow_eq_one
  rw [h] at hs
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmod : a ≡ (galChar Ω m g : ZMod m).val [MOD m] := by
    have e1 : ζ ^ a = ζ ^ (a % m) := by
      conv_lhs => rw [← Nat.div_add_mod a m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    have e2 : ζ ^ (galChar Ω m g : ZMod m).val = ζ ^ ((galChar Ω m g : ZMod m).val % m) := by
      conv_lhs => rw [← Nat.div_add_mod (galChar Ω m g : ZMod m).val m, pow_add, pow_mul,
        hζ.pow_eq_one, one_pow, one_mul]
    exact hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) (by rw [← e1, ← e2, hs])
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [ZMod.natCast_zmod_val] at this
  exact this.symm

/- English proof (translation)
Introduce `Ω _ _ _ m _`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `prim : ∀ k : ℕ, k ≠ 0 → ∃ z : Ω, IsPrimitiveRoot z k`. Introduce `k hk`.

Use `haveI : NeZero k := ⟨hk⟩`. Use `haveI : NeZero ((k : ℕ) : Ω) := ⟨by exact_mod_cast hk⟩`. Conclude with `HasEnoughRootsOfUnity.prim`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero (NeZero.ne m)`. Take `⟨ζ, hζ⟩` from `prim m (NeZero.ne m)`.

Use `⟨?_, ?_, fun g a z hz hg => gcb_key Ω m g a z hz hg, ?_⟩` and prove the remaining obligations. Introduce `u haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Establish `hy : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m` using `hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)`. Establish `hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ`. Establish `h1` using `Polynomial.cyclotomic_eq_minpoly_rat hy hm`.

Establish `h2` using `Polynomial.cyclotomic_eq_minpoly_rat hζ hm`. Apply the tactic sequence `convert h1.symm.trans h2 using 2 <;> exact Subsingleton.elim _ _`. Take `⟨g, hg⟩` from `(Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin`. Use `⟨g, Units.ext ?_⟩` and prove the remaining obligations. Establish `key` using `gcb_key Ω m g _ ζ hζ hg`.

Rewrite using `[key, ZMod.natCast_zmod_val]`. Apply `Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup)` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[MonoidHom.mem_ker]`. Apply `Units.ext` to reduce the goal to its premises.

Establish `hfix : g ζ = ζ ^ 1`. Rewrite using `[pow_one]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)`. Rewrite using `[gcb_key Ω m g 1 ζ hζ hfix]`. Simplify using the standard rewrite rules.

Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hm).tower_top`. Conclude with `IntermediateField.fixingSubgroup_isOpen _`. Introduce `n _ h g`. Establish `hn : n ≠ 0` using `NeZero.ne n`. Take `⟨ω, hω⟩` from `prim n hn`.

Establish `hd : n / m ∣ n` using `Nat.div_dvd_of_dvd h`. Establish `hdm : n / m ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) hm).ne'`. Establish `hω' : IsPrimitiveRoot (ω ^ (n / m)) m`. Use `hω.pow_of_dvd hdm hd` as an intermediate fact. Rewrite `this` using `[Nat.div_div_self h hn]`. Then use the resulting hypothesis.

Establish `hg : g (ω ^ (n / m)) = (ω ^ (n / m)) ^ (galChar Ω n g : ZMod n).val`. Rewrite using `[map_pow, galChar_spec n g ω hω.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]`. Establish `key` using `gcb_key Ω m g _ _ hω' hg`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[key, ZMod.unitsMap, Units.coe_map]`.

Simplify using `only [MonoidHom.coe_coe, ZMod.castHom_apply]`. Conclude with `ZMod.cast_eq_val _`.
-/
theorem UpperTheory.V.Two.galCharBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m], Function.Surjective (galChar Ω m) ∧ IsOpen ((galChar Ω m).ker : Set (G ℚ Ω)) ∧
      (∀ (g : G ℚ Ω) (a : ℕ) (ζ : Ω), IsPrimitiveRoot ζ m → g ζ = ζ ^ a → (galChar Ω m g : ZMod m) = a) ∧
      ∀ (n : ℕ) [NeZero n] (h : m ∣ n) (g : G ℚ Ω), ZMod.unitsMap h (galChar Ω n g) = galChar Ω m g := by
  intro Ω _ _ _ m _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have prim : ∀ k : ℕ, k ≠ 0 → ∃ z : Ω, IsPrimitiveRoot z k := by
    intro k hk
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero ((k : ℕ) : Ω) := ⟨by exact_mod_cast hk⟩
    exact HasEnoughRootsOfUnity.prim
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨ζ, hζ⟩ := prim m (NeZero.ne m)
  refine ⟨?_, ?_, fun g a z hz hg => gcb_key Ω m g a z hz hg, ?_⟩
  · intro u
    haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
    have hy : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m :=
      hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)
    have hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ := by
      have h1 := Polynomial.cyclotomic_eq_minpoly_rat hy hm
      have h2 := Polynomial.cyclotomic_eq_minpoly_rat hζ hm
      convert h1.symm.trans h2 using 2 <;> exact Subsingleton.elim _ _
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin
    refine ⟨g, Units.ext ?_⟩
    have key := gcb_key Ω m g _ ζ hζ hg
    rw [key, ZMod.natCast_zmod_val]
  · apply Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup)
    · intro g hg
      rw [MonoidHom.mem_ker]
      apply Units.ext
      have hfix : g ζ = ζ ^ 1 := by
        rw [pow_one]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
          (IntermediateField.mem_adjoin_simple_self ℚ ζ)
      rw [gcb_key Ω m g 1 ζ hζ hfix]
      simp
    · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
        IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hm).tower_top
      exact IntermediateField.fixingSubgroup_isOpen _
  · intro n _ h g
    have hn : n ≠ 0 := NeZero.ne n
    obtain ⟨ω, hω⟩ := prim n hn
    have hd : n / m ∣ n := Nat.div_dvd_of_dvd h
    have hdm : n / m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) hm).ne'
    have hω' : IsPrimitiveRoot (ω ^ (n / m)) m := by
      have := hω.pow_of_dvd hdm hd
      rwa [Nat.div_div_self h hn] at this
    have hg : g (ω ^ (n / m)) = (ω ^ (n / m)) ^ (galChar Ω n g : ZMod n).val := by
      rw [map_pow, galChar_spec n g ω hω.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]
    have key := gcb_key Ω m g _ _ hω' hg
    apply Units.ext
    rw [key, ZMod.unitsMap, Units.coe_map]
    simp only [MonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_eq_val _
