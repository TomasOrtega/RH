import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.UnrUnipChar

/- English proof (translation)
Take `⟨k, hk⟩` from `ha`. Establish `h2 : a ^ (k + 1 + 1) = 0` using `pow_eq_zero_of_le (by omega) hk`. Use `⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩` and prove the remaining obligations. Rewrite using `[IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]`. Establish `: ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1) = a ^ 2 * ((((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i)` using `fun i _ => by`.

Rewrite using `[mul_smul_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl this]`. Simplify using `only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one, pow_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_eq_one_add_add_sq {A : Type} [CommRing A] [Algebra ℚ A] {a : A} (ha : IsNilpotent a) :
    ∃ s, IsNilpotent.exp a = 1 + a + a ^ 2 * s := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ (k + 1 + 1) = 0 := pow_eq_zero_of_le (by omega) hk
  refine ⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1)
      = a ^ 2 * ((((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i) := fun i _ => by
    rw [mul_smul_comm]; congr 1; ring
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one,
    pow_zero]
  ring

end GlobalTheory.UnrUnipChar

open GlobalTheory.UnrUnipChar in

/- English proof (translation)
Introduce `l _ B _ _ _ x hx σ hσ`. Use `letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra`. Use `letI : TopologicalSpace B := moduleTopology ℚ_[l] B`. Use `haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B`.

Use `haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B`. Take `⟨c, ⟨hc, hcI, hcσ⟩, -⟩` from `existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (A := ℚ_[l]) (V := ℚ_[l]) (1 : Representation ℚ_[l] (GQ l) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1`. Establish `hadd : ∀ g h, c (g * h) = c g + c h` using `fun g h => hc.2 g h`. Establish `hcc : Continuous c` using `hc.1`. Establish `hc1 : c 1 = 0` using `hcI 1 (one_mem _)`.

Establish `hcpow : ∀ m : ℕ, c (σ ^ m) = m`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp [hc1]`. Consider the case `succ m ih => rw [pow_succ, hadd, ih, hcσ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `f : GQ l →* B` to `{ toFun := fun g => IsNilpotent.exp (c g • x) map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero] map_mul' := fun g h => by`. Rewrite using `[hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }`. Establish `hf : Continuous f`.

Take `⟨k, hk⟩` from `hx`. Establish `: (f : GQ l → B) = fun g => ∑ i ∈ Finset.range k, ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `IsNilpotent.exp (c g • x) = _`. Rewrite using `[IsNilpotent.exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, Rat.cast_smul_eq_qsmul, _root_.smul_pow]`. Rewrite using `[this]`. Use `fun_prop`. Establish `hfI : ∀ g ∈ Iq l, f g = 1` using `fun g hg => by`.

Express the relevant statement in the definitionally equal form `IsNilpotent.exp (c g • x) = 1`. Rewrite using `[hcI g hg, zero_smul, IsNilpotent.exp_zero]`. Use `⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_, 1, fun m => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsNilpotent (IsNilpotent.exp (c g • x) - 1)`. Take `⟨s, hs⟩` from `exp_eq_one_add_add_sq (hx.smul (c g))`.

Rewrite using `[hs, show 1 + c g • x + (c g • x) ^ 2 * s - 1 = (c g • x) * (1 + (c g • x) * s) by ring]`. Use `first`. Consider the case `exact (Commute.all _ _).isNilpotent_mul_right (hx.smul (c g))`. Consider the case `exact (Commute.all _ _).isNilpotent_mul_left (hx.smul (c g))`. Express the relevant statement in the definitionally equal form `∃ b, IsNilpotent.exp (c (σ ^ m) • x) - 1 = x * ((m : B) * ((1 : Bˣ) : B) + x * b)`.

Rewrite using `[hcpow m]`. Take `⟨s, hs⟩` from `exp_eq_one_add_add_sq (hx.smul ((m : ℚ_[l])))`. Use `⟨(m : B) ^ 2 * s, ?_⟩` and prove the remaining obligations. Establish `e : ((m : ℚ_[l]) • x) = (m : B) * x` using `by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`. Rewrite using `[hs, e, Units.val_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.unr_unip_char_frob :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (t : B),
      IsNilpotent t → ∀ σ : GQ l, UpperTheory.V.Loc.IsFrob σ → ∃ u : GQ l →* Bˣ, QCont l (fun g => (u g : B)) ∧
        (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : B) - 1)) ∧
        ∃ v : Bˣ, ∀ m : ℕ, ∃ b : B, (u (σ ^ m) : B) - 1 = t * ((m : B) * v + t * b) := by
  intro l _ B _ _ _ x hx σ hσ
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ l) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  have hcpow : ∀ m : ℕ, c (σ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hc1]
    | succ m ih => rw [pow_succ, hadd, ih, hcσ]; push_cast; ring
  let f : GQ l →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ l → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, _root_.smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq l, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_, 1, fun m => ?_⟩
  · change IsNilpotent (IsNilpotent.exp (c g • x) - 1)
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul (c g))
    rw [hs, show 1 + c g • x + (c g • x) ^ 2 * s - 1 = (c g • x) * (1 + (c g • x) * s) by ring]
    first
      | exact (Commute.all _ _).isNilpotent_mul_right (hx.smul (c g))
      | exact (Commute.all _ _).isNilpotent_mul_left (hx.smul (c g))
  · change ∃ b, IsNilpotent.exp (c (σ ^ m) • x) - 1 = x * ((m : B) * ((1 : Bˣ) : B) + x * b)
    rw [hcpow m]
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul ((m : ℚ_[l])))
    refine ⟨(m : B) ^ 2 * s, ?_⟩
    have e : ((m : ℚ_[l]) • x) = (m : B) * x := by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [hs, e, Units.val_one]
    ring
