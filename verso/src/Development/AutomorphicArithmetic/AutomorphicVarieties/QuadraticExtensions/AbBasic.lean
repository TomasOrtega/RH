import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GalCharBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem ker_congr (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m n : ℕ) [NeZero m] [NeZero n]
    (h : m = n) : (galChar Ω m).ker = (galChar Ω n).ker := by
  subst h
  rfl

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω) (Polynomial.degree_cyclotomic_pos m Ω (NeZero.pos m)).ne'`. Conclude with `⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩`.
-/
private theorem prim_lemma (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω)
    (Polynomial.degree_cyclotomic_pos m Ω (NeZero.pos m)).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/- English proof (translation)
Establish `h1` using `galChar_spec m g ζ hζ.pow_eq_one`. Rewrite `h1` using `[hk]`. Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.mpr ⟨m, NeZero.pos m, hζ.pow_eq_one⟩`. Establish `h2` using `hfin.pow_eq_pow_iff_modEq.mp h1`. Rewrite `h2` using `[← hζ.eq_orderOf]`.

Rewrite using `[← ZMod.natCast_zmod_val (galChar Ω m g : ZMod m)]`. Conclude with `((ZMod.natCast_eq_natCast_iff _ _ _).mpr h2).symm`.
-/
private theorem galChar_eq_of_apply_primitiveRoot_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m]
    (g : G ℚ Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) (k : ℕ) (hk : g ζ = ζ ^ k) :
    (galChar Ω m g : ZMod m) = k := by
  have h1 := galChar_spec m g ζ hζ.pow_eq_one
  rw [hk] at h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, NeZero.pos m, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.mp h1
  rw [← hζ.eq_orderOf] at h2
  rw [← ZMod.natCast_zmod_val (galChar Ω m g : ZMod m)]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h2).symm

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `prim_lemma Ω N`. Take `⟨d, hd⟩` from `h`. Establish `hμ : IsPrimitiveRoot (ζ ^ d) m` using `hζ.pow (NeZero.pos N) (by rw [hd, mul_comm])`. Use `(galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g (ζ ^ d) hμ _ ?_).symm` and prove the remaining obligations. Rewrite using `[map_pow, galChar_spec N g ζ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem galChar_val_cast_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    (((galChar Ω N g : ZMod N).val : ℕ) : ZMod m) = (galChar Ω m g : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω N
  obtain ⟨d, hd⟩ := h
  have hμ : IsPrimitiveRoot (ζ ^ d) m := hζ.pow (NeZero.pos N) (by rw [hd, mul_comm])
  refine (galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g (ζ ^ d) hμ _ ?_).symm
  rw [map_pow, galChar_spec N g ζ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Use `ext`. Rewrite using `[← galChar_val_cast_eq_galChar_of_dvd Ω m N h g, ← ZMod.cast_eq_val]`. Both sides reduce to the same expression.
-/
private theorem unitsMap_galChar_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    ZMod.unitsMap h (galChar Ω N g) = galChar Ω m g := by
  ext
  rw [← galChar_val_cast_eq_galChar_of_dvd Ω m N h g, ← ZMod.cast_eq_val]
  rfl

/- English proof (translation)
Introduce `u`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `⟨ζ, hζ⟩` from `prim_lemma Ω m`. Establish `hcop : Nat.Coprime (u : ZMod m).val m` using `ZMod.val_coe_unit_coprime u`. Establish `hμ : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m` using `hζ.pow_of_coprime _ hcop`.

Establish `hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ`. Establish `e1` using `Polynomial.cyclotomic_eq_minpoly_rat hμ (NeZero.pos m)`. Establish `e2` using `Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)`. Apply the tactic sequence `convert e1.symm.trans e2 <;> exact Subsingleton.elim _ _`. Take `⟨g, hg⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin`.

Establish `hg' : g ζ = ζ ^ (u : ZMod m).val` using `(AlgEquiv.smul_def g ζ).symm.trans hg`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ _ hg', ZMod.natCast_zmod_val]`.
-/
private theorem galChar_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    Function.Surjective (galChar Ω m) := by
  intro u
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  have hcop : Nat.Coprime (u : ZMod m).val m := ZMod.val_coe_unit_coprime u
  have hμ : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m := hζ.pow_of_coprime _ hcop
  have hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ := by
    have e1 := Polynomial.cyclotomic_eq_minpoly_rat hμ (NeZero.pos m)
    have e2 := Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)
    convert e1.symm.trans e2 <;> exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  have hg' : g ζ = ζ ^ (u : ZMod m).val := (AlgEquiv.smul_def g ζ).symm.trans hg
  refine ⟨g, ?_⟩
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ _ hg', ZMod.natCast_zmod_val]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `prim_lemma Ω m`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top`. Use `Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)` and prove the remaining obligations. Introduce `g hg`.

Establish `hfix : g ζ = ζ ^ 1`. Rewrite using `[pow_one]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))`. Rewrite using `[MonoidHom.mem_ker]`. Use `ext`.

Rewrite using `[galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ 1 hfix]`. Simplify using the standard rewrite rules.
-/
private theorem isOpen_galChar_ker (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    IsOpen ((galChar Ω m).ker : Set (G ℚ Ω)) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro g hg
  have hfix : g ζ = ζ ^ 1 := by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
      (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))
  rw [MonoidHom.mem_ker]
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ 1 hfix]
  simp

/- English proof (translation)
Introduce `Ω _ _ _`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `A B`. Use extensionality with `g`. Rewrite using `[Subgroup.mem_inf]`.

Use `show ZMod.unitsMap (dvd_mul_right A.m B.m) (galChar Ω (A.m * B.m) g) ∈ A.H ∧ ZMod.unitsMap (dvd_mul_left B.m A.m) (galChar Ω (A.m * B.m) g) ∈ B.H ↔ galChar Ω A.m g ∈ A.H ∧ galChar Ω B.m g ∈ B.H`. Rewrite using `[unitsMap_galChar_eq_galChar_of_dvd Ω A.m (A.m * B.m) (dvd_mul_right _ _) g, unitsMap_galChar_eq_galChar_of_dvd Ω B.m (A.m * B.m) (dvd_mul_left _ _) g]`. Introduce `A`. Use `⟨Subgroup.index_comap_of_surjective _ (galChar_surjective Ω A.m), Subgroup.index_ne_zero_of_finite, ?_, ?_⟩` and prove the remaining obligations. Use `Subgroup.isOpen_mono ?_ (isOpen_galChar_ker Ω A.m)` and prove the remaining obligations.

Introduce `g hg`. Simplify using `[abU, MonoidHom.mem_ker.mp hg, one_mem]`. Introduce `g hg`. Simplify using `[abU, MonoidHom.mem_ker.mp hg, one_mem]`. Introduce `A N _ hN g`.

Simplify using `only [abU, Subgroup.mem_comap, AbF.ker]`. Rewrite using `[galChar_val_cast_eq_galChar_of_dvd Ω A.m N hN g]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, rfl⟩`.

Introduce and unpack `⟨u, hu, hEq⟩`. Rewrite using `[← Units.ext hEq]` and apply the resulting hypothesis. Introduce `m _`. Establish `hm : (AbF.cyc m).m = m` using `max_eq_left NeZero.one_le`. Use `show Subgroup.comap _ ⊥ = _`.

Rewrite using `[MonoidHom.comap_bot]`. Conclude with `ker_congr Ω _ _ hm`.
-/
theorem UpperTheory.V.Two.abBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], (∀ A B : AbF, abU Ω (A.sup B) = abU Ω A ⊓ abU Ω B) ∧ (∀ A : AbF, (abU Ω A).index = A.deg ∧ A.deg ≠ 0 ∧ IsOpen (abU Ω A : Set (G ℚ Ω)) ∧ (galChar Ω A.m).ker ≤ abU Ω A) ∧
      (∀ (A : AbF) (N : ℕ) [NeZero N], A.m ∣ N → ∀ g, g ∈ abU Ω A ↔ A.ker (galChar Ω N g : ZMod N).val) ∧ ∀ (m : ℕ) [NeZero m], abU Ω (AbF.cyc m) = (galChar Ω m).ker := by
  intro Ω _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    ext g
    rw [Subgroup.mem_inf]
    show ZMod.unitsMap (dvd_mul_right A.m B.m) (galChar Ω (A.m * B.m) g) ∈ A.H ∧
        ZMod.unitsMap (dvd_mul_left B.m A.m) (galChar Ω (A.m * B.m) g) ∈ B.H ↔
      galChar Ω A.m g ∈ A.H ∧ galChar Ω B.m g ∈ B.H
    rw [unitsMap_galChar_eq_galChar_of_dvd Ω A.m (A.m * B.m) (dvd_mul_right _ _) g,
      unitsMap_galChar_eq_galChar_of_dvd Ω B.m (A.m * B.m) (dvd_mul_left _ _) g]
  · intro A
    refine ⟨Subgroup.index_comap_of_surjective _ (galChar_surjective Ω A.m), Subgroup.index_ne_zero_of_finite, ?_, ?_⟩
    · refine Subgroup.isOpen_mono ?_ (isOpen_galChar_ker Ω A.m)
      intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
    · intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
  · intro A N _ hN g
    simp only [abU, Subgroup.mem_comap, AbF.ker]
    rw [galChar_val_cast_eq_galChar_of_dvd Ω A.m N hN g]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, hEq⟩
      rwa [← Units.ext hEq]
  · intro m _
    have hm : (AbF.cyc m).m = m := max_eq_left NeZero.one_le
    show Subgroup.comap _ ⊥ = _
    rw [MonoidHom.comap_bot]
    exact ker_congr Ω _ _ hm
