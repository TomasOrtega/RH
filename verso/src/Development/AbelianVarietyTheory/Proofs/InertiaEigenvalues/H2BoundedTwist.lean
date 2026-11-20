import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.CyclotomicH2Bound

open GlobalTheory.ShapeNeg

/- English proof (translation)
Establish `hsp` using `cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n) (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one`. Establish `h1 : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ` using `rfl`. Rewrite `hsp` using `[h1, ha]`. Establish `h3 : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p])` using `rfl`. Rewrite using `[h3]`.

Use `set b := ((PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]))`. Establish `hne : ζ ≠ 0` using `hζ.ne_zero (NeZero.ne _)`. Establish `hz : ζ ^ ((a : ℤ) - (b.val : ℤ)) = 1`. Rewrite using `[zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]`. Establish `hd` using `(hζ.zpow_eq_one_iff_dvd _).1 hz`.

Establish `h0 : (((a : ℤ) - (b.val : ℤ) : ℤ) : ZMod (p ^ n)) = 0`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `hd` after adjusting the coercions. Move the coercions through the operations in `at h0`. Rewrite `h0` using `[ZMod.natCast_zmod_val]`.

Conclude with `(sub_eq_zero.1 h0).symm`.
-/
theorem cycK_eq_of_prim {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (n : ℕ)
    (g : Formalism.GaloisCohomology.GK p K) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) (a : ℕ)
    (ha : g ζ = ζ ^ a) : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (a : ZMod (p ^ n)) := by
  have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have h1 : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [h1, ha] at hsp
  have h3 : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) =
      (PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]) := rfl
  rw [h3]
  set b := ((PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]))
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hz : ζ ^ ((a : ℤ) - (b.val : ℤ)) = 1 := by
    rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
  have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
  have h0 : (((a : ℤ) - (b.val : ℤ) : ℤ) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hd
  push_cast at h0
  rw [ZMod.natCast_zmod_val] at h0
  exact (sub_eq_zero.1 h0).symm

/- English proof (translation)
The claim follows from `HasEnoughRootsOfUnity.exists_primitiveRoot _ _`.
-/
theorem exists_prim (p : ℕ) [Fact p.Prime] (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hI : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O` using `((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm`. Use `haveI : Finite (O ⧸ Ideal.span {ϖ}) := by`. Rewrite using `[hI]`. Conclude with `(inferInstance : Finite (IsLocalRing.ResidueField O))`. Rewrite using `[← Ideal.span_singleton_pow]`.

Conclude with `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k`.
-/
theorem finite_quot [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ k}) := by
  have hI : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm
  haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
    rw [hI]; exact (inferInstance : Finite (IsLocalRing.ResidueField O))
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

/- English proof (translation)
Establish `hϖ0 : (algebraMap O (FractionRing O) ϖ) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hϖ.ne_zero`. Set `z₀ : FractionRing O` to `(algebraMap O (FractionRing O) ϖ ^ n)⁻¹`. Establish `hk : (ϖ ^ n) • eM.symm (Submodule.Quotient.mk z₀) = 0`.

Rewrite using `[← map_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, map_pow, mul_inv_cancel₀ (pow_ne_zero _ hϖ0)]`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).2 (Submodule.one_le.1 le_rfl), map_zero]`. Use `⟨Lev.mk _ hk, fun y => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (eM y.val)`. Establish `hy` using `y.smul_val`.

Establish `hm : (ϖ ^ n) • (Submodule.Quotient.mk z : Formalism.NG.KO O) = 0`. Rewrite using `[hz, ← map_smul, hy, map_zero]`. Rewrite `hm` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Take `⟨t, ht⟩` from `hm`. Use `⟨t, Lev.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[Lev.val_smul, Lev.val_mk, ← eM.symm_apply_apply y.val, ← hz, ← map_smul, ← Submodule.Quotient.mk_smul]`. Use `congr 2`. Rewrite using `[Algebra.smul_def, ht, Algebra.smul_def, map_pow, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_mul]`.
-/
theorem lev_cyclic {M : Type} [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] Formalism.NG.KO O)
    {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ x₀ : Lev M (ϖ ^ n), ∀ y : Lev M (ϖ ^ n), ∃ t : O, y = t • x₀ := by
  have hϖ0 : (algebraMap O (FractionRing O) ϖ) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖ.ne_zero
  let z₀ : FractionRing O := (algebraMap O (FractionRing O) ϖ ^ n)⁻¹
  have hk : (ϖ ^ n) • eM.symm (Submodule.Quotient.mk z₀) = 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, map_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hϖ0)]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.one_le.1 le_rfl), map_zero]
  refine ⟨Lev.mk _ hk, fun y => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (eM y.val)
  have hy := y.smul_val
  have hm : (ϖ ^ n) • (Submodule.Quotient.mk z : Formalism.NG.KO O) = 0 := by
    rw [hz, ← map_smul, hy, map_zero]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, Lev.ext ?_⟩
  rw [Lev.val_smul, Lev.val_mk, ← eM.symm_apply_apply y.val, ← hz, ← map_smul,
    ← Submodule.Quotient.mk_smul]
  congr 2
  rw [Algebra.smul_def, ht, Algebra.smul_def, map_pow, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_mul]

/- English proof (translation)
The claim follows from `map_nsmul (show M →ₗ[R] R from φ) k y`.
-/
theorem td_nsmul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M) (k : ℕ)
    (y : M) : φ (k • y) = k • φ y := map_nsmul (show M →ₗ[R] R from φ) k y
/- English proof (translation)
The claim follows from `(show M →ₗ[R] R from φ).map_sub x y`.
-/
theorem td_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x - y) = φ x - φ y := (show M →ₗ[R] R from φ).map_sub x y
/- English proof (translation)
The claim follows from `(show M →ₗ[R] R from φ).map_add x y`.
-/
theorem td_add {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x + y) = φ x + φ y := (show M →ₗ[R] R from φ).map_add x y

/- English proof (translation)
Establish `h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out = Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t` using `Ideal.Quotient.mk_out _`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)`. Rewrite using `[← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hz, smul_zero]`.
-/
theorem out_smul {N : Type} [AddCommGroup N] [Module O N] {ϖ : O} (k : ℕ) {z : N}
    (hz : (ϖ ^ k) • z = 0) (t : O) : (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out • z = t • z := by
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t := Ideal.Quotient.mk_out _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
  rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hz, smul_zero]

/- English proof (translation)
Introduce `hLTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ ε hε e M _ _ eM ρ hρ σ₀ hσ hcont`. Establish `hw : ((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1 ≠ 0`. Introduce `h0`. Apply `hσ` to reduce the goal to its premises. Use `ext`.

Rewrite using `[Units.val_one]`. Conclude with `sub_eq_zero.1 h0`. Take `⟨c, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 hpϖ`. Use `haveI hQ := finite_quot hϖ c`.

Use `⟨(p ^ c) ^ ((p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})), fun n hn h => ?_⟩` and prove the remaining obligations. Use `letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h`. Take `⟨x₀, hx₀⟩` from `lev_cyclic eM hϖ n`. Establish `hkn : ∀ y : Lev M (ϖ ^ n), (ϖ ^ n) • y = 0` using `fun y => Lev.ext (by`. Rewrite using `[Lev.val_smul, Lev.smul_val, Lev.val_zero])`.

Use `haveI : Finite (Lev M (ϖ ^ n)) := by haveI := finite_quot hϖ n`. Use `Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) (fun y => ?_)` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hx₀ y`. Conclude with `⟨Ideal.Quotient.mk _ t, out_smul n (hkn x₀) t⟩`. Take `⟨⟨eB⟩, -, -, -, hcup, -⟩` from `hLTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)`.

Establish `hpn : ∀ y : Lev M (ϖ ^ n), ((p : O) ^ n) • y = 0`. Introduce `y`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[← hr, mul_smul, hkn, smul_zero]`. Take `⟨ζ, hζ⟩` from `exists_prim p n`.

Take `⟨a₀, ha₀, hdiff⟩` from `hε σ₀ n ζ hζ.pow_eq_one`. Establish `hcyc` using `cycK_eq_of_prim n σ₀ hζ a₀ ha₀`. Establish `hεy : ∀ y : Lev M (ϖ ^ n), ((ε σ₀ : Oˣ) : O) • y = (a₀ : O) • y`. Introduce `y`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hdiff`.

Rewrite using `[← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hpn, smul_zero]`. Establish `hεk : ∀ (k : ℕ) (y : Lev M (ϖ ^ n)), ((ε σ₀ : Oˣ) : O) ^ k • y = (a₀ ^ k : ℕ) • y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y`.

Simplify using the standard rewrite rules. Consider the case `succ k ih => intro y`. Rewrite using `[pow_succ, mul_smul, hεy, ih, ← Nat.cast_smul_eq_nsmul O (a₀ ^ k), ← Nat.cast_smul_eq_nsmul O (a₀ ^ (k + 1)), smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_succ]`. Establish `hinv : ∀ y : Lev M (ϖ ^ n), levRepZ p n h ρ σ₀⁻¹ y = ((ε σ₀ : Oˣ) : O) ^ e • y`. Introduce `y`.

Apply `Lev.ext` to reduce the goal to its premises. Rewrite using `[levRepZ_apply, levRep_val, hρ, Lev.val_smul, map_inv, inv_pow, inv_inv, Units.val_pow_eq_pow_val]`. Set `A` to `H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id _))`. Establish `hfix : ∀ (a : A) (y : Lev M (ϖ ^ n)), (((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n))) * (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y = (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y`. Introduce `a y`.

Establish `h1` using `DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 a.2 σ₀) y`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at h1`. Rewrite `h1` using `[hinv, hεk, td_nsmul, nsmul_eq_mul, hcyc, ← mul_assoc]`. Establish `h2 : ((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n)) = (a₀ : ZMod (p ^ n)) * ((a₀ ^ e : ℕ) : ZMod (p ^ n))` using `by push_cast; ring`. Rewrite using `[h2]`.

Conclude with `h1`. Establish `hkill : ∀ (a : A) (y : Lev M (ϖ ^ n)), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((ϖ ^ c) • y) = 0`. Introduce `a y`. Establish `hy : (ϖ ^ c) • y = (((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1) • (((u⁻¹ : Oˣ) : O) • y)`. Rewrite using `[hu, smul_smul, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]`.

Rewrite using `[hy, sub_smul, one_smul, Units.val_pow_eq_pow_val, hεk, td_sub, td_nsmul, nsmul_eq_mul, hfix, sub_self]`. Establish `hkillp : ∀ (a : A) (y : Lev M (ϖ ^ n)), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((p ^ c : ℕ) • y) = 0`. Introduce `a y`. Establish `hy : (p ^ c : ℕ) • y = (ϖ ^ c) • ((s ^ c) • y)`. Rewrite using `[← Nat.cast_smul_eq_nsmul O, smul_smul, ← mul_pow, mul_comm ϖ s, hs, Nat.cast_pow]`.

Rewrite using `[hy, hkill]`. Establish `hA : ∀ a : A, (p ^ c : ℕ) • a = 0`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `TDual.ext` to reduce the goal to its premises.

Introduce `y`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), Submodule.coe_smul, TDual.smul_apply, ← nsmul_eq_mul, ← td_nsmul, hkillp]`. Both sides reduce to the same expression. Set `T` to `{x : ZMod (p ^ n) // (p ^ c) • x = 0}`. Establish `hT : Nat.card T ≤ p ^ c` using `by classical`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Conclude with `IsAddCyclic.card_nsmul_eq_zero_le (pow_pos (Fact.out : p.Prime).pos c)`. Establish `hq : ∀ (a : A) (t : O), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀) = (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (t • x₀)`. Introduce `a t`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t)))`.

Establish `h1 : (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀ = t • x₀ + (ϖ ^ c) • (r • x₀)`. Rewrite using `[smul_smul, mul_comm (ϖ ^ c) r, hr, sub_smul, add_sub_cancel]`. Rewrite using `[h1, td_add, hkill, add_zero]`. Set `G : A → (O ⧸ Ideal.span {ϖ ^ c} → T)` to `fun a q => ⟨(a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (q.out • x₀), by rw [← td_nsmul, hkillp]⟩`. Establish `hGinj : Function.Injective G`.

Introduce `a a' hG`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `TDual.ext` to reduce the goal to its premises. Introduce `y`. Take `⟨t, rfl⟩` from `hx₀ y`.

Establish `h1` using `congrArg Subtype.val (congrFun hG (Ideal.Quotient.mk _ t))`. Simplify using `only [G] at h1`. Rewrite `h1` using `[hq a t, hq a' t]`. Then use the resulting hypothesis. Use `haveI : Finite A := Finite.of_injective G hGinj`. Establish `hAcard : Nat.card A ≤ (p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})` using `(Nat.card_le_card_of_injective G hGinj).trans (by rw [Nat.card_fun]; exact Nat.pow_le_pow_left hT _)`.

Set `F : H2 ((levRepZ p n h ρ).comp (MonoidHom.id _)) → (A → T)` to `fun f a => ⟨eB (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) f a), by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ← LinearEquiv.map_smul, ← LinearMap.map_smul, Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), hA a, LinearMap.map_zero, LinearEquiv.map_zero]⟩`. Establish `hFinj : Function.Injective F`. Introduce `f f' hF`. Apply `hcup` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `a`. Apply `eB.injective` to reduce the goal to its premises. Conclude with `congrArg Subtype.val (congrFun hF a)`. Use `show Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id _))) ≤ _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem h2_bounded_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hLTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ ε hε e M _ _ eM ρ hρ σ₀ hσ hcont
  have hw : ((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1 ≠ 0 := by
    intro h0; apply hσ; ext; rw [Units.val_one]; exact sub_eq_zero.1 h0
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hpϖ
  haveI hQ := finite_quot hϖ c
  refine ⟨(p ^ c) ^ ((p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})), fun n hn h => ?_⟩
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hkn : ∀ y : Lev M (ϖ ^ n), (ϖ ^ n) • y = 0 := fun y => Lev.ext (by
    rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  haveI : Finite (Lev M (ϖ ^ n)) := by
    haveI := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) (fun y => ?_)
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n (hkn x₀) t⟩
  obtain ⟨⟨eB⟩, -, -, -, hcup, -⟩ := hLTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)
  have hpn : ∀ y : Lev M (ϖ ^ n), ((p : O) ^ n) • y = 0 := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hr, mul_smul, hkn, smul_zero]
  obtain ⟨ζ, hζ⟩ := exists_prim p n
  obtain ⟨a₀, ha₀, hdiff⟩ := hε σ₀ n ζ hζ.pow_eq_one
  have hcyc := cycK_eq_of_prim n σ₀ hζ a₀ ha₀
  have hεy : ∀ y : Lev M (ϖ ^ n), ((ε σ₀ : Oˣ) : O) • y = (a₀ : O) • y := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hdiff
    rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hpn, smul_zero]
  have hεk : ∀ (k : ℕ) (y : Lev M (ϖ ^ n)), ((ε σ₀ : Oˣ) : O) ^ k • y = (a₀ ^ k : ℕ) • y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, mul_smul, hεy, ih, ← Nat.cast_smul_eq_nsmul O (a₀ ^ k),
        ← Nat.cast_smul_eq_nsmul O (a₀ ^ (k + 1)), smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_succ]
  have hinv : ∀ y : Lev M (ϖ ^ n), levRepZ p n h ρ σ₀⁻¹ y = ((ε σ₀ : Oˣ) : O) ^ e • y := by
    intro y; apply Lev.ext
    rw [levRepZ_apply, levRep_val, hρ, Lev.val_smul, map_inv, inv_pow, inv_inv, Units.val_pow_eq_pow_val]
  let A := H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id _))
  have hfix : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n))) * (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y := by
    intro a y
    have h1 := DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 a.2 σ₀) y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at h1
    rw [hinv, hεk, td_nsmul, nsmul_eq_mul, hcyc, ← mul_assoc] at h1
    have h2 : ((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n)) = (a₀ : ZMod (p ^ n)) * ((a₀ ^ e : ℕ) : ZMod (p ^ n)) := by
      push_cast; ring
    rw [h2]; exact h1
  have hkill : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((ϖ ^ c) • y) = 0 := by
    intro a y
    have hy : (ϖ ^ c) • y = (((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1) • (((u⁻¹ : Oˣ) : O) • y) := by
      rw [hu, smul_smul, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]
    rw [hy, sub_smul, one_smul, Units.val_pow_eq_pow_val, hεk, td_sub, td_nsmul, nsmul_eq_mul, hfix,
      sub_self]
  have hkillp : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((p ^ c : ℕ) • y) = 0 := by
    intro a y
    have hy : (p ^ c : ℕ) • y = (ϖ ^ c) • ((s ^ c) • y) := by
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← mul_pow, mul_comm ϖ s, hs, Nat.cast_pow]
    rw [hy, hkill]
  have hA : ∀ a : A, (p ^ c : ℕ) • a = 0 := by
    intro a; apply Subtype.ext; apply TDual.ext; intro y
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), Submodule.coe_smul, TDual.smul_apply,
      ← nsmul_eq_mul, ← td_nsmul, hkillp]; rfl
  let T := {x : ZMod (p ^ n) // (p ^ c) • x = 0}
  have hT : Nat.card T ≤ p ^ c := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsAddCyclic.card_nsmul_eq_zero_le (pow_pos (Fact.out : p.Prime).pos c)
  have hq : ∀ (a : A) (t : O), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n)))
      ((Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀) =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (t • x₀) := by
    intro a t
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t)))
    have h1 : (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀ = t • x₀ + (ϖ ^ c) • (r • x₀) := by
      rw [smul_smul, mul_comm (ϖ ^ c) r, hr, sub_smul, add_sub_cancel]
    rw [h1, td_add, hkill, add_zero]
  let G : A → (O ⧸ Ideal.span {ϖ ^ c} → T) := fun a q =>
    ⟨(a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (q.out • x₀), by rw [← td_nsmul, hkillp]⟩
  have hGinj : Function.Injective G := by
    intro a a' hG; apply Subtype.ext; apply TDual.ext; intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    have h1 := congrArg Subtype.val (congrFun hG (Ideal.Quotient.mk _ t))
    simp only [G] at h1
    rwa [hq a t, hq a' t] at h1
  haveI : Finite A := Finite.of_injective G hGinj
  have hAcard : Nat.card A ≤ (p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c}) :=
    (Nat.card_le_card_of_injective G hGinj).trans (by rw [Nat.card_fun]; exact Nat.pow_le_pow_left hT _)
  let F : H2 ((levRepZ p n h ρ).comp (MonoidHom.id _)) → (A → T) := fun f a =>
    ⟨eB (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) f a), by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ← LinearEquiv.map_smul, ← LinearMap.map_smul,
        Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), hA a, LinearMap.map_zero, LinearEquiv.map_zero]⟩
  have hFinj : Function.Injective F := by
    intro f f' hF; apply hcup; apply LinearMap.ext; intro a; apply eB.injective
    exact congrArg Subtype.val (congrFun hF a)
  show Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id _))) ≤ _
  calc _ ≤ Nat.card (A → T) := Nat.card_le_card_of_injective F hFinj
    _ = Nat.card T ^ Nat.card A := Nat.card_fun
    _ ≤ (p ^ c) ^ Nat.card A := Nat.pow_le_pow_left hT _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos c) hAcard

end GlobalTheory.CyclotomicH2Bound
