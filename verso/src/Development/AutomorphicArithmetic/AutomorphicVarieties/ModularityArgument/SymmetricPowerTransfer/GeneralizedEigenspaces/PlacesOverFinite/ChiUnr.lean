import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `fun h0 => hn (h0 ▸ dvd_zero l)`. Establish `hnorm : ‖x‖ = 1`. Establish `h1 : ‖x‖ ^ n = 1` using `by rw [← norm_pow, hx, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg x) hn0).1 h1`. Establish `hpow : ∀ i : ℕ, ‖x ^ i - 1‖ < 1`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simpa using zero_lt_one`. Consider the case `succ i ih`. Establish `e : x ^ (i + 1) - 1 = x ^ i * (x - 1) + (x ^ i - 1)` using `by ring`.

Rewrite using `[e]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ih)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, hnorm, one_pow, one_mul]`. Conclude with `h`. Establish `hnn : ‖(n : Qbar l)‖ = 1`.

Establish `h1 : ‖(n : ℚ_[l])‖ = 1` using `Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)`. Establish `h2 : ((n : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l])` using `by simp`. Rewrite using `[h2, PadicAlgCl.norm_extends, h1]`. Establish `hS : ∑ i ∈ Finset.range n, x ^ i ≠ 0`. Introduce `h0`.

Establish `e : (n : Qbar l) = -∑ i ∈ Finset.range n, (x ^ i - 1)`. Rewrite using `[Finset.sum_sub_distrib, h0]`. Simplify using the standard rewrite rules. Establish `hlt : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (x ^ i - 1)‖ < 1`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.sum_range_succ]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ih (hpow m))`.

Rewrite `hnn` using `[e, norm_neg]`. Conclude with `(hlt n).ne hnn`. Establish `: (x - 1) * ∑ i ∈ Finset.range n, x ^ i = 0`. Rewrite using `[mul_geom_sum, hx, sub_self]`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hS)`.
-/
private theorem root_one {l : ℕ} [Fact l.Prime] {x : Qbar l} {n : ℕ} (hn : ¬ l ∣ n) (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero l)
  have hnorm : ‖x‖ = 1 := by
    have h1 : ‖x‖ ^ n = 1 := by rw [← norm_pow, hx, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hn0).1 h1
  have hpow : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simpa using zero_lt_one
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x ^ i * (x - 1) + (x ^ i - 1) := by ring
      rw [e]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ih)
      rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]
      exact h
  have hnn : ‖(n : Qbar l)‖ = 1 := by
    have h1 : ‖(n : ℚ_[l])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)
    have h2 : ((n : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by simp
    rw [h2, PadicAlgCl.norm_extends, h1]
  have hS : ∑ i ∈ Finset.range n, x ^ i ≠ 0 := by
    intro h0
    have e : (n : Qbar l) = -∑ i ∈ Finset.range n, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib, h0]; simp
    have hlt : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (x ^ i - 1)‖ < 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ih (hpow m))
    rw [e, norm_neg] at hnn
    exact (hlt n).ne hnn
  have : (x - 1) * ∑ i ∈ Finset.range n, x ^ i = 0 := by
    rw [mul_geom_sum, hx, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hS)

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩`. Use `show cyclotomicCharacter Ω l σ.toRingEquiv = 1`. Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`.

Establish `: NeZero (l ^ n)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `e1` using `cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one`. Establish `hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1`. Rewrite using `[Nat.cast_pow, map_pow, not_lt]`. Conclude with `one_le_pow₀ (not_lt.1 hA)`.

Establish `e2` using `Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one`. Rewrite `e2` using `[show Chr.cls ℚ Ω (l ^ n) σ = 1 from (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ]`. Establish `e3` using `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (e1.symm.trans e2)`. Rewrite using `[ZMod.val_injective _ e3]`. Simplify using the standard rewrite rules.
-/
private theorem cyc_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e1 := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have e2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [show Chr.cls ℚ Ω (l ^ n) σ = 1 from (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ] at e2
  have e3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (e1.symm.trans e2)
  rw [ZMod.val_injective _ e3]
  simp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c N _ e ψ χ' j hord hcong M hM L _ _ _ A hA s hs`. Establish `hv : ¬ A.valuation (l : Ω) < 1 ∧ ¬ A.valuation (N : Ω) < 1`. Take `⟨k, rfl⟩` from `hM`. Establish `hn : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1` using `fun n => (A.valuation_le_one_iff _).2 (natCast_mem A n)`. Rewrite `hA` using `[Nat.cast_mul, Nat.cast_mul, map_mul, map_mul]`.

Use `⟨fun h => hA ?_, fun h => hA ?_⟩` and prove the remaining obligations. Conclude with `mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le h (hn N)) (hn k)`. Conclude with `mul_lt_one_of_lt_of_le (lt_of_le_of_lt (mul_le_of_le_one_left' (hn l)) h) (hn k)`. Establish `hσ : galEmb ℚ L Ω s ∈ Ine (F` using `ℚ) A := ⟨hs.1, fun x hx => hs.2 x hx⟩`. Use `set σ := galEmb ℚ L Ω s with hσdef`.

Establish `hz : cycZ ℚ Ω l σ = 1` using `cyc_one Ω l A hv.1 hσ`. Establish `hcyc : cycBar ℚ Ω l σ = 1` using `by simp [cycBar, hz]`. Establish `hchi : UpperTheory.V.Base.chiO ℚ Ω l c.O σ = 1` using `by simp [UpperTheory.V.Base.chiO, hz]`. Establish `hdir : Chr.dirG ℚ Ω ψ σ = 1`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, show Chr.cls ℚ Ω N σ = 1 from (Chr.clsFacts ℚ Ω N).2.2.2.2 A hv.2 hσ, map_one]`.

Establish `hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1`. Rewrite using `[Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, hchi, hdir, one_zpow, one_mul]`. Establish `h` using `hcong σ`. Rewrite `h` using `[MonoidHom.mul_apply, MonoidHom.pow_apply, hcyc, one_pow, one_mul, hP]`. Establish `h' : ‖((χ' σ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1` using `h`.

Establish `ho : ((χ' σ : (Qbar l)ˣ) : Qbar l) ^ orderOf χ' = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply, Units.val_one]`. Conclude with `Units.ext (root_one hord ho h')`.
-/
theorem chiUnr : ChiUnr := by
  intro Ω _ _ _ l _ c N _ e ψ χ' j hord hcong M hM L _ _ _ A hA s hs
  have hv : ¬ A.valuation (l : Ω) < 1 ∧ ¬ A.valuation (N : Ω) < 1 := by
    obtain ⟨k, rfl⟩ := hM
    have hn : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).2 (natCast_mem A n)
    rw [Nat.cast_mul, Nat.cast_mul, map_mul, map_mul] at hA
    refine ⟨fun h => hA ?_, fun h => hA ?_⟩
    · exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le h (hn N)) (hn k)
    · exact mul_lt_one_of_lt_of_le (lt_of_le_of_lt (mul_le_of_le_one_left' (hn l)) h) (hn k)
  have hσ : galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := ⟨hs.1, fun x hx => hs.2 x hx⟩
  set σ := galEmb ℚ L Ω s with hσdef
  have hz : cycZ ℚ Ω l σ = 1 := cyc_one Ω l A hv.1 hσ
  have hcyc : cycBar ℚ Ω l σ = 1 := by simp [cycBar, hz]
  have hchi : UpperTheory.V.Base.chiO ℚ Ω l c.O σ = 1 := by simp [UpperTheory.V.Base.chiO, hz]
  have hdir : Chr.dirG ℚ Ω ψ σ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply,
      show Chr.cls ℚ Ω N σ = 1 from (Chr.clsFacts ℚ Ω N).2.2.2.2 A hv.2 hσ, map_one]
  have hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    rw [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, hchi, hdir, one_zpow, one_mul]
  have h := hcong σ
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hcyc, one_pow, one_mul, hP] at h
  have h' : ‖((χ' σ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := h
  have ho : ((χ' σ : (Qbar l)ˣ) : Qbar l) ^ orderOf χ' = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply, Units.val_one]
  exact Units.ext (root_one hord ho h')

end UpperTheory.V.Z.Sym.Pl
