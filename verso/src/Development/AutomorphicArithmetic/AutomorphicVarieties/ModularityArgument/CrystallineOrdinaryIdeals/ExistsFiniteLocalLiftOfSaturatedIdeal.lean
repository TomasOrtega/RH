import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsLeMemPowOfMulMemPowOfNonZeroDivisorStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ModuleFiniteQuotientMaximalPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.ThickenSaturated

/- English proof (translation)
Establish `hne : m ^ k ≠ ⊤` using `fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))`. Use `haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne`. Take `⟨M0, hM0⟩` from `Ideal.exists_maximal (A ⧸ m ^ k)`. Establish `key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m`. Introduce `M hM`.

Establish `h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k))`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]`. Conclude with `M.zero_mem`.

Establish `h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k))` using `h1.isPrime.le_of_pow_le h2`. Conclude with `(hm.eq_of_le h1.ne_top h3).symm`. Conclude with `IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM => Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ((key M hM).trans (key M0 hM0).symm)⟩`.
-/
theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

/- English proof (translation)
Use `set mB := IsLocalRing.maximalIdeal B with hmB`. Use `set m : Ideal A := mB.comap (g : A →+* B) with hm`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite K B`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : IsNilpotent mB := by`. Use `IsArtinianRing.isNilpotent_jacobson_bot (R := B)` as an intermediate fact.

Rewrite `this` using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Then use the resulting hypothesis. Establish `hj : m ^ (n + 1) ≤ RingHom.ker g`. Introduce `x hx`. Establish `h1 : x ∈ (mB ^ (n + 1)).comap (g : A →+* B)` using `Ideal.le_comap_pow _ _ hx`. Rewrite `h1` using `[pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot]`.

Conclude with `RingHom.mem_ker.2 h1`. Take `⟨k, hjk, hk⟩` from `GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor m δ hδ (n + 1)`. Use `haveI : m.IsPrime := Ideal.comap_isPrime _ _`. Establish `hinj : Function.Injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB)` using `Ideal.quotientMap_injective`. Use `haveI : Module.Finite K (B ⧸ mB) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K mB).toLinearMap Ideal.Quotient.mk_surjective`.

Use `haveI hfin : Module.Finite K (A ⧸ m) := Module.Finite.of_injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB).toLinearMap hinj`. Use `haveI : IsArtinianRing (A ⧸ m) := IsArtinianRing.of_finite K (A ⧸ m)`. Use `haveI : m.IsMaximal := Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)`. Use `⟨m ^ k, isLocalRing_quot_pow m k (by omega), GlobalTheory.T.module_finite_quotient_maximal_pow m hfin k, (Ideal.pow_le_pow_right hjk).trans hj, fun a ha => ?_⟩` and prove the remaining obligations. Conclude with `RingHom.mem_ker.1 (hj (hk a ha))`.
-/
theorem core {K : Type} [Field K] {A : Type} [CommRing A] [IsNoetherianRing A] [Algebra K A]
    (δ : A) (hδ : ∀ a, δ * a = 0 → a = 0)
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra K B] [Module.Finite K B] (g : A →ₐ[K] B) :
    ∃ I : Ideal A, IsLocalRing (A ⧸ I) ∧ Module.Finite K (A ⧸ I) ∧ I ≤ RingHom.ker g ∧
      ∀ a, δ * a ∈ I → g a = 0 := by
  set mB := IsLocalRing.maximalIdeal B with hmB
  set m : Ideal A := mB.comap (g : A →+* B) with hm
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn⟩ : IsNilpotent mB := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hj : m ^ (n + 1) ≤ RingHom.ker g := by
    intro x hx
    have h1 : x ∈ (mB ^ (n + 1)).comap (g : A →+* B) := Ideal.le_comap_pow _ _ hx
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at h1
    exact RingHom.mem_ker.2 h1
  obtain ⟨k, hjk, hk⟩ := GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor m δ hδ (n + 1)
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hinj : Function.Injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB) :=
    Ideal.quotientMap_injective
  haveI : Module.Finite K (B ⧸ mB) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K mB).toLinearMap Ideal.Quotient.mk_surjective
  haveI hfin : Module.Finite K (A ⧸ m) := Module.Finite.of_injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB).toLinearMap hinj
  haveI : IsArtinianRing (A ⧸ m) := IsArtinianRing.of_finite K (A ⧸ m)
  haveI : m.IsMaximal := Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  refine ⟨m ^ k, isLocalRing_quot_pow m k (by omega), GlobalTheory.T.module_finite_quotient_maximal_pow m hfin k,
    (Ideal.pow_le_pow_right hjk).trans hj, fun a ha => ?_⟩
  exact RingHom.mem_ker.1 (hj (hk a ha))

/- English proof (translation)
Introduce `l hl O _ _ R _ _ _ J d _ hdJ B _ _ _ _ _ _ _ _ f hJf`. Set `x : R ⧸ J` to `Ideal.Quotient.mk J (l : R)`. Set `A` to `Localization.Away x`. Use `haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers x) A inferInstance`. Establish `hlA : IsUnit ((l : ℕ) : A)`.

Use `IsLocalization.Away.algebraMap_isUnit (S := A) x` as an intermediate fact. Simplify `this` using `[x, map_natCast]`. Set `ψ₀ : ℤ_[l] →+* A` to `(algebraMap O A).comp (algebraMap ℤ_[l] O)`. Establish `hψ₀ : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ₀ y)`. Introduce and unpack `⟨y, hy⟩`.

Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Use `show IsUnit (ψ₀ y)`. Rewrite using `[PadicInt.unitCoeff_spec hy0, map_mul, map_pow, map_natCast]`. Conclude with `((Units.isUnit _).map ψ₀).mul (hlA.pow _)`. Set `ψ : ℚ_[l] →+* A` to `IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) hψ₀`.

Use `letI algQA : Algebra ℚ_[l] A := ψ.toAlgebra`. Set `g₀ : R ⧸ J →+* B` to `Ideal.Quotient.lift J f.toRingHom (fun a ha => RingHom.mem_ker.1 (hJf ha))`. Establish `hu : IsUnit (g₀ x)`. Establish `h1 : g₀ x = algebraMap ℚ_[l] B (l : ℚ_[l])`. Simplify using `[g₀, x, map_natCast]`.

Rewrite using `[h1]`. Conclude with `(isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)).map _`. Set `g : A →+* B` to `IsLocalization.Away.lift x hu`. Establish `hg : ∀ w, g (algebraMap (R ⧸ J) A w) = g₀ w` using `fun w => IsLocalization.Away.lift_eq x hu w`. Establish `hgO : ∀ z : O, g (algebraMap O A z) = algebraMap O B z`.

Introduce `z`. Rewrite using `[IsScalarTower.algebraMap_apply O (R ⧸ J) A, hg]`. Conclude with `f.commutes z`. Establish `hgψ : g.comp ψ = algebraMap ℚ_[l] B`. Use `IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) ?_` and prove the remaining obligations.

Use extensionality with `y`. Simplify using `only [RingHom.comp_apply, ψ, IsLocalization.lift_eq, ψ₀, hgO]`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Set `gK : A →ₐ[ℚ_[l]] B` to `{ g with commutes' := fun r => RingHom.congr_fun hgψ r }`. Set `δ : A` to `algebraMap (R ⧸ J) A (Ideal.Quotient.mk J d)`.

Establish `hδ : ∀ a, δ * a = 0 → a = 0`. Introduce `a ha`. Take `⟨⟨w, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers x) a`. Express the relevant statement in the definitionally equal form `δ * IsLocalization.mk' A w s = 0 at ha`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' A w s = 0`.

Establish `e : δ = IsLocalization.mk' A (Ideal.Quotient.mk J d) (1 : Submonoid.powers x)` using `(IsLocalization.mk'_one A _).symm`. Rewrite `ha` using `[e, ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨c, hc⟩` from `ha`. Rewrite using `[IsLocalization.mk'_eq_zero_iff]`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Take `⟨w', rfl⟩` from `Ideal.Quotient.mk_surjective w`. Take `⟨c', hc'⟩` from `Ideal.Quotient.mk_surjective (c : R ⧸ J)`. Rewrite `hc` using `[← hc', ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Apply `hdJ` to reduce the goal to its premises.

Simplify `hc` using `[mul_comm, mul_left_comm, mul_assoc]`. Take `⟨I, hloc, hfin, hIker, hI⟩` from `core δ hδ gK`. Use `letI algZ : Algebra ℤ_[l] (A ⧸ I) := ((algebraMap ℚ_[l] (A ⧸ I)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra`. Establish `tZO : IsScalarTower ℤ_[l] O (A ⧸ I)` using `IsScalarTower.of_algebraMap_eq fun y => by show Ideal.Quotient.mk I (ψ (algebraMap ℤ_[l] ℚ_[l] y)) = Ideal.Quotient.mk I (algebraMap O A (algebraMap ℤ_[l] O y))`. Rewrite using `[IsLocalization.lift_eq]`.

Both sides reduce to the same expression. Establish `tZQ : IsScalarTower ℤ_[l] ℚ_[l] (A ⧸ I)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `f' : R →ₐ[O] A ⧸ I` to `(Ideal.Quotient.mkₐ O I).comp ((IsScalarTower.toAlgHom O (R ⧸ J) A).comp (Ideal.Quotient.mkₐ O J))`. Establish `hf' : ∀ a, f' a = Ideal.Quotient.mk I (algebraMap (R ⧸ J) A (Ideal.Quotient.mk J a))` using `fun _ => rfl`. Set `q : A ⧸ I →ₐ[ℚ_[l]] B` to `Ideal.Quotient.liftₐ I gK (fun a ha => RingHom.mem_ker.1 (hIker ha))`.

Establish `hq : ∀ a, q (Ideal.Quotient.mk I a) = g a` using `fun _ => rfl`. Use `⟨A ⧸ I, inferInstance, hloc, inferInstance, hfin, inferInstance, algZ, tZO, tZQ, f', q, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[RingHom.mem_ker, hf', Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]`. Introduce `a`.

Rewrite using `[hf', hq, hg]`. Both sides reduce to the same expression. Introduce `b hb`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `hb` using `[hf', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`.

Rewrite using `[hq]`. Conclude with `hI a hb`.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l hl O _ _ R _ _ _ J d _ hdJ B _ _ _ _ _ _ _ _ f hJf
  let x : R ⧸ J := Ideal.Quotient.mk J (l : R)
  let A := Localization.Away x
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers x) A inferInstance
  have hlA : IsUnit ((l : ℕ) : A) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A) x
    simpa [x, map_natCast] using this
  let ψ₀ : ℤ_[l] →+* A := (algebraMap O A).comp (algebraMap ℤ_[l] O)
  have hψ₀ : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ₀ y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    show IsUnit (ψ₀ y)
    rw [PadicInt.unitCoeff_spec hy0, map_mul, map_pow, map_natCast]
    exact ((Units.isUnit _).map ψ₀).mul (hlA.pow _)
  let ψ : ℚ_[l] →+* A := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) hψ₀
  letI algQA : Algebra ℚ_[l] A := ψ.toAlgebra
  let g₀ : R ⧸ J →+* B := Ideal.Quotient.lift J f.toRingHom (fun a ha => RingHom.mem_ker.1 (hJf ha))
  have hu : IsUnit (g₀ x) := by
    have h1 : g₀ x = algebraMap ℚ_[l] B (l : ℚ_[l]) := by
      simp [g₀, x, map_natCast]
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)).map _
  let g : A →+* B := IsLocalization.Away.lift x hu
  have hg : ∀ w, g (algebraMap (R ⧸ J) A w) = g₀ w := fun w => IsLocalization.Away.lift_eq x hu w
  have hgO : ∀ z : O, g (algebraMap O A z) = algebraMap O B z := by
    intro z
    rw [IsScalarTower.algebraMap_apply O (R ⧸ J) A, hg]
    exact f.commutes z
  have hgψ : g.comp ψ = algebraMap ℚ_[l] B := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) ?_
    ext y
    simp only [RingHom.comp_apply, ψ, IsLocalization.lift_eq, ψ₀, hgO]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let gK : A →ₐ[ℚ_[l]] B := { g with commutes' := fun r => RingHom.congr_fun hgψ r }
  let δ : A := algebraMap (R ⧸ J) A (Ideal.Quotient.mk J d)
  have hδ : ∀ a, δ * a = 0 → a = 0 := by
    intro a ha
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) a
    change δ * IsLocalization.mk' A w s = 0 at ha
    change IsLocalization.mk' A w s = 0
    have e : δ = IsLocalization.mk' A (Ideal.Quotient.mk J d) (1 : Submonoid.powers x) :=
      (IsLocalization.mk'_one A _).symm
    rw [e, ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff] at ha
    obtain ⟨c, hc⟩ := ha
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, ?_⟩
    obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (c : R ⧸ J)
    rw [← hc', ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hc
    rw [← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply hdJ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  obtain ⟨I, hloc, hfin, hIker, hI⟩ := core δ hδ gK
  letI algZ : Algebra ℤ_[l] (A ⧸ I) := ((algebraMap ℚ_[l] (A ⧸ I)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have tZO : IsScalarTower ℤ_[l] O (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun y => by
    show Ideal.Quotient.mk I (ψ (algebraMap ℤ_[l] ℚ_[l] y)) = Ideal.Quotient.mk I (algebraMap O A (algebraMap ℤ_[l] O y))
    rw [IsLocalization.lift_eq]
    rfl
  have tZQ : IsScalarTower ℤ_[l] ℚ_[l] (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f' : R →ₐ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).comp
    ((IsScalarTower.toAlgHom O (R ⧸ J) A).comp (Ideal.Quotient.mkₐ O J))
  have hf' : ∀ a, f' a = Ideal.Quotient.mk I (algebraMap (R ⧸ J) A (Ideal.Quotient.mk J a)) := fun _ => rfl
  let q : A ⧸ I →ₐ[ℚ_[l]] B := Ideal.Quotient.liftₐ I gK (fun a ha => RingHom.mem_ker.1 (hIker ha))
  have hq : ∀ a, q (Ideal.Quotient.mk I a) = g a := fun _ => rfl
  refine ⟨A ⧸ I, inferInstance, hloc, inferInstance, hfin, inferInstance, algZ, tZO, tZQ, f', q, ?_, ?_, ?_⟩
  · intro a ha
    rw [RingHom.mem_ker, hf', Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro a
    rw [hf', hq, hg]
    rfl
  · intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hf', ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb
    rw [hq]
    exact hI a hb

end GlobalTheory.ThickenSaturated
