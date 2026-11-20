import Mathlib
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
Establish `: Module.Finite R N` using `Module.Finite.trans B N`. Establish `: IsNoetherian R N` using `isNoetherian_of_isNoetherianRing_of_finite R N`. Set `P : Submodule R N` to `{ carrier := Set.range φ add_mem' := by`. Introduce and unpack `_ _ ⟨x, rfl⟩ ⟨y, rfl⟩`. Conclude with `⟨x + y, map_add φ x y⟩`.

Use the proof step `zero_mem' := ⟨0, map_zero φ⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `r _ ⟨x, rfl⟩`. Take `⟨b, rfl⟩` from `hσ r`. Conclude with `⟨b • x, hφσ b x⟩ }`.

Take `⟨s, hs⟩` from `(IsNoetherian.noetherian P : P.FG)`. Establish `hsP : ∀ n ∈ s, ∃ m, φ m = n` using `fun n hn => by`. Establish `: n ∈ P` using `hs ▸ Submodule.subset_span hn`. Conclude with `this`. Use `choose! g hg using hsP`.

Use `⟨⟨s.image g, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `m -`. Set `Q : Submodule B M` to `Submodule.span B (s.image g : Set M)`. Set `Q' : Submodule R N` to `{ carrier := φ '' Q add_mem' := by`.

Introduce and unpack `_ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩`. Conclude with `⟨x + y, Q.add_mem hx hy, map_add φ x y⟩`. Use the proof step `zero_mem' := ⟨0, Q.zero_mem, map_zero φ⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `r _ ⟨x, hx, rfl⟩`.

Take `⟨b, rfl⟩` from `hσ r`. Conclude with `⟨b • x, Q.smul_mem b hx, hφσ b x⟩ }`. Establish `hsQ' : (s : Set N) ⊆ Q'`. Introduce `n hn`. Use `⟨g n, Submodule.subset_span ?_, hg n hn⟩` and prove the remaining obligations.

Conclude with `Finset.mem_coe.mpr (Finset.mem_image_of_mem g hn)`. Establish `hPQ : P ≤ Q'` using `hs ▸ Submodule.span_le.mpr hsQ'`. Take `⟨m', hm', he⟩` from `hPQ (⟨m, rfl⟩ : φ m ∈ P)`. Conclude with `hφ he ▸ hm'`.
-/
theorem module_finite_of_semilinear {B R M N : Type*} [CommRing B] [CommRing R] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B] [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module R N] [IsScalarTower R B N] [Module.Finite B N]
    (σ : B →+* R) (hσ : Function.Surjective σ) (φ : M →+ N) (hφ : Function.Injective φ)
    (hφσ : ∀ (b : B) (m : M), φ (b • m) = σ b • φ m) : Module.Finite B M := by
  have : Module.Finite R N := Module.Finite.trans B N
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  let P : Submodule R N :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add φ x y⟩
      zero_mem' := ⟨0, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, hφσ b x⟩ }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  have hsP : ∀ n ∈ s, ∃ m, φ m = n := fun n hn => by
    have : n ∈ P := hs ▸ Submodule.subset_span hn
    exact this
  choose! g hg using hsP
  classical
  refine ⟨⟨s.image g, ?_⟩⟩
  rw [eq_top_iff]
  rintro m -
  let Q : Submodule B M := Submodule.span B (s.image g : Set M)
  let Q' : Submodule R N :=
    { carrier := φ '' Q
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, Q.add_mem hx hy, map_add φ x y⟩
      zero_mem' := ⟨0, Q.zero_mem, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, Q.smul_mem b hx, hφσ b x⟩ }
  have hsQ' : (s : Set N) ⊆ Q' := by
    intro n hn
    refine ⟨g n, Submodule.subset_span ?_, hg n hn⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem g hn)
  have hPQ : P ≤ Q' := hs ▸ Submodule.span_le.mpr hsQ'
  obtain ⟨m', hm', he⟩ := hPQ (⟨m, rfl⟩ : φ m ∈ P)
  exact hφ he ▸ hm'

/- English proof (translation)
Use `set B := MvPolynomial (Fin s) (ZMod p)`. Use `set R := (iterateFrobenius B p e).range`. Establish `hpow : ∀ x : B, x ^ p ^ e ∈ R` using `fun x => ⟨x, by rw [iterateFrobenius_def]⟩`. Establish `hint : Algebra.IsIntegral R B` using `⟨fun x => by`. Use `IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero e (Fact.out : p.Prime).ne_zero)) ?_` and prove the remaining obligations.

Establish `: x ^ p ^ e = algebraMap R B ⟨x ^ p ^ e, hpow x⟩` using `rfl`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap⟩`. Establish `hft : Algebra.FiniteType R B`. Use `⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce and unpack `f -`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: MvPolynomial.C a = algebraMap R B ⟨MvPolynomial.C a, ⟨MvPolynomial.C a, by`.

Rewrite using `[iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]⟩⟩ := rfl`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add f g hf hg => exact Subalgebra.add_mem _ hf hg`. Consider the case `mul_X f i hf`.

Use `Subalgebra.mul_mem _ hf (Algebra.subset_adjoin ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem mvPolynomial_finite_frobenius_range (p : ℕ) [Fact p.Prime] (s e : ℕ) :
    Module.Finite (iterateFrobenius (MvPolynomial (Fin s) (ZMod p)) p e).range
      (MvPolynomial (Fin s) (ZMod p)) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  set R := (iterateFrobenius B p e).range
  have hpow : ∀ x : B, x ^ p ^ e ∈ R := fun x => ⟨x, by rw [iterateFrobenius_def]⟩
  have hint : Algebra.IsIntegral R B := ⟨fun x => by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero e (Fact.out : p.Prime).ne_zero)) ?_
    have : x ^ p ^ e = algebraMap R B ⟨x ^ p ^ e, hpow x⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap⟩
  have hft : Algebra.FiniteType R B := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    rw [eq_top_iff]
    rintro f -
    induction f using MvPolynomial.induction_on with
    | C a =>
      have : MvPolynomial.C a = algebraMap R B ⟨MvPolynomial.C a, ⟨MvPolynomial.C a, by
        rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]⟩⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add f g hf hg => exact Subalgebra.add_mem _ hf hg
    | mul_X f i hf =>
      refine Subalgebra.mul_mem _ hf (Algebra.subset_adjoin ?_)
      simp
  exact Algebra.IsIntegral.finite

/- English proof (translation)
Use `set B := MvPolynomial (Fin s) (ZMod p)`. Establish `hp : p.Prime` using `Fact.out`. Establish `hinjBL : Function.Injective (algebraMap B L)`. Rewrite using `[IsScalarTower.algebraMap_eq B F L]`. Conclude with `(algebraMap F L).injective.comp (IsFractionRing.injective B F)`.

Establish `: CharP L p` using `charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C) (hinjBL.comp (MvPolynomial.C_injective (Fin s) (ZMod p))) p`. Use `set Ls := separableClosure F L`. Establish `: ExpChar Ls p` using `ExpChar.prime hp`. Establish `: IsScalarTower B Ls L` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply B F L, IsScalarTower.algebraMap_apply B F Ls, IsScalarTower.algebraMap_apply F Ls L]`.

Establish `: IsPurelyInseparable Ls L` using `separableClosure.isPurelyInseparable F L`. Use `set e := IsPurelyInseparable.exponent Ls L`. Set `fr : L →+* Ls` to `IsPurelyInseparable.iterateFrobenius Ls L p (le_refl e)`. Establish `hfr : ∀ y, algebraMap Ls L (fr y) = y ^ p ^ e` using `fun y => IsPurelyInseparable.algebraMap_iterateFrobenius Ls p (le_refl e) y`. Establish `hinjLs : Function.Injective (algebraMap Ls L)` using `(algebraMap Ls L).injective`.

Establish `: Algebra.IsSeparable F Ls` using `separableClosure.isSeparable F L`. Establish `: Module.Finite B (integralClosure B Ls)` using `IsIntegralClosure.finite B F Ls (integralClosure B Ls)`. Use `mvPolynomial_finite_frobenius_range p s e` as an intermediate fact. Establish `hint : ∀ y : integralClosure B L, IsIntegral B (fr y)` using `fun y => (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ls L) hinjLs).mp (by`. Rewrite using `[IsScalarTower.toAlgHom_apply, hfr]`.

Conclude with `y.2.pow _)`. Set `φ : integralClosure B L →+ integralClosure B Ls` to `{ toFun := fun y => ⟨fr y, hint y⟩ map_zero' := by ext; simp map_add' := fun y z => by ext; simp }`. Use `module_finite_of_semilinear (iterateFrobenius B p e).rangeRestrict (iterateFrobenius B p e).rangeRestrict_surjective φ ?_ ?_` and prove the remaining obligations. Introduce `y z h`. Establish `h' : fr y = fr z` using `congrArg Subtype.val h`.

Conclude with `Subtype.ext (fr.injective h')`. Introduce `b y`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinjLs` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap Ls L (fr (b • (y : L))) = algebraMap Ls L (((iterateFrobenius B p e b : B) • fr y))`.

Rewrite using `[hfr, Algebra.smul_def, Algebra.smul_def, map_mul, hfr, iterateFrobenius_def, mul_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]`.
-/
theorem finite_integralClosure_mvPolynomial (p : ℕ) [Fact p.Prime] (s : ℕ)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin s) (ZMod p)) F]
    [IsFractionRing (MvPolynomial (Fin s) (ZMod p)) F]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra (MvPolynomial (Fin s) (ZMod p)) L]
    [IsScalarTower (MvPolynomial (Fin s) (ZMod p)) F L] :
    Module.Finite (MvPolynomial (Fin s) (ZMod p))
      (integralClosure (MvPolynomial (Fin s) (ZMod p)) L) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p :=
    charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
      (hinjBL.comp (MvPolynomial.C_injective (Fin s) (ZMod p))) p
  set Ls := separableClosure F L
  have : ExpChar Ls p := ExpChar.prime hp
  have : IsScalarTower B Ls L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B F L, IsScalarTower.algebraMap_apply B F Ls,
      IsScalarTower.algebraMap_apply F Ls L]
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent Ls L
  let fr : L →+* Ls := IsPurelyInseparable.iterateFrobenius Ls L p (le_refl e)
  have hfr : ∀ y, algebraMap Ls L (fr y) = y ^ p ^ e := fun y =>
    IsPurelyInseparable.algebraMap_iterateFrobenius Ls p (le_refl e) y
  have hinjLs : Function.Injective (algebraMap Ls L) := (algebraMap Ls L).injective
  have : Algebra.IsSeparable F Ls := separableClosure.isSeparable F L
  have : Module.Finite B (integralClosure B Ls) :=
    IsIntegralClosure.finite B F Ls (integralClosure B Ls)
  have := mvPolynomial_finite_frobenius_range p s e
  have hint : ∀ y : integralClosure B L, IsIntegral B (fr y) := fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ls L) hinjLs).mp (by
      rw [IsScalarTower.toAlgHom_apply, hfr]
      exact y.2.pow _)
  let φ : integralClosure B L →+ integralClosure B Ls :=
    { toFun := fun y => ⟨fr y, hint y⟩
      map_zero' := by ext; simp
      map_add' := fun y z => by ext; simp }
  refine module_finite_of_semilinear (iterateFrobenius B p e).rangeRestrict
    (iterateFrobenius B p e).rangeRestrict_surjective φ ?_ ?_
  · intro y z h
    have h' : fr y = fr z := congrArg Subtype.val h
    exact Subtype.ext (fr.injective h')
  · intro b y
    apply Subtype.ext
    apply hinjLs
    change algebraMap Ls L (fr (b • (y : L))) =
      algebraMap Ls L (((iterateFrobenius B p e b : B) • fr y))
    rw [hfr, Algebra.smul_def, Algebra.smul_def, map_mul, hfr, iterateFrobenius_def, mul_pow,
      ← map_pow, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Set `: Algebra (ZMod p) A` to `ZMod.algebra A p`. Establish `: Algebra.FiniteType (ZMod p) A` using `Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A`. Take `⟨s, g, hginj, hgfin⟩` from `exists_finite_inj_algHom_of_fg (ZMod p) A`. Use `set B := MvPolynomial (Fin s) (ZMod p)`. Set `: Algebra B A` to `g.toRingHom.toAlgebra`.

Establish `: Module.Finite B A` using `hgfin`. Set `: Algebra B K` to `((algebraMap A K).comp (algebraMap B A)).toAlgebra`. Set `: Algebra B L` to `((algebraMap A L).comp (algebraMap B A)).toAlgebra`. Establish `: IsScalarTower B A K` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower B A L` using `IsScalarTower.of_algebraMap_eq' rfl`.

Establish `: IsScalarTower B K L` using `IsScalarTower.of_algebraMap_eq fun x => by`. Express the relevant statement in the definitionally equal form `algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))`. Conclude with `IsScalarTower.algebraMap_apply A K L _`. Establish `hinjBK : Function.Injective (algebraMap B K)` using `(IsFractionRing.injective A K).comp hginj`. Establish `: FaithfulSMul B K` using `(faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK`.

Set `: Algebra (FractionRing B) K` to `FractionRing.liftAlgebra B K`. Set `: Algebra (FractionRing B) L` to `((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra`. Establish `: IsScalarTower (FractionRing B) K L` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower B (FractionRing B) L` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply (FractionRing B) K L, ← IsScalarTower.algebraMap_apply B (FractionRing B) K, ← IsScalarTower.algebraMap_apply B K L]`.

Establish `: Algebra.IsIntegral B A` using `Algebra.IsIntegral.of_finite B A`. Establish `: FiniteDimensional (FractionRing B) K`. Take `⟨t, ht⟩` from `(Module.Finite.fg_top : (⊤ : Submodule B A).FG)`. Set `T : Set K` to `algebraMap A K '' t`. Establish `hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x`.

Introduce and unpack `_ ⟨a, -, rfl⟩`. Establish `: IsIntegral B (algebraMap A K a)` using `(Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)`. Conclude with `this.tower_top`. Establish `: Finite T` using `(t.finite_toSet.image _).to_subtype`. Establish `hfd` using `IntermediateField.finiteDimensional_adjoin hTint`.

Establish `htop : IntermediateField.adjoin (FractionRing B) T = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T`. Introduce `a`.

Establish `ha : a ∈ Submodule.span B (t : Set A)` using `ht ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `add_mem hy hz`. Consider the case `smul b y _ hy`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B (FractionRing B) K]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) hy`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`.

Conclude with `div_mem (hA a) (hA b)`. Rewrite `hfd` using `[htop]`. Conclude with `(IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional`. Establish `: FiniteDimensional (FractionRing B) L` using `Module.Finite.trans K L`. Establish `hB` using `finite_integralClosure_mvPolynomial p s (FractionRing B) L`.

Establish `hle : (integralClosure A L).toSubmodule.restrictScalars B ≤ (integralClosure B L).toSubmodule` using `fun y hy => isIntegral_trans (R := B) (A := A) y hy`. Establish `: IsNoetherian B (integralClosure B L).toSubmodule` using `isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)`. Establish `: IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B)` using `isNoetherian_of_le hle`. Establish `: Module.Finite B (integralClosure A L)` using `Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)`. Conclude with `Module.Finite.of_restrictScalars_finite B A (integralClosure A L)`.
-/
theorem finite_integralClosure_of_charP (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [CharP A p]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  have : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  set B := MvPolynomial (Fin s) (ZMod p)
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := finite_integralClosure_mvPolynomial p s (FractionRing B) L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

end GroundTheory.Heights₂.Heights.Model
