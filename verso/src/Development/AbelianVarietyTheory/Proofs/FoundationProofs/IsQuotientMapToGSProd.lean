import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

variable {l : ℕ} [Fact l.Prime] (c : Coef l)

abbrev Ix : Type := Module.Free.ChooseBasisIndex ℤ_[l] c.O

def bas : Module.Basis (Ix c) ℤ_[l] c.O := Module.Free.chooseBasis ℤ_[l] c.O

open Classical in

def crd (n : ℕ) (i : Ix c) (x : Qbar l) : ZMod (l ^ n) :=
  if h : x ∈ c.O then PadicInt.toZModPow n ((bas c).repr ⟨x, h⟩ i) else 0

def lft (n : ℕ) (a : Ix c → ZMod (l ^ n)) : Qbar l :=
  (((bas c).equivFun.symm fun i => (((a i).val : ℕ) : ℤ_[l]) : c.O) : Qbar l)

variable {c}

/- English proof (translation)
Unfold `crd`. Rewrite using `[dif_pos hx]`.
-/
theorem crd_of_mem {n : ℕ} (i : Ix c) {x : Qbar l} (hx : x ∈ c.O) :
    crd c n i x = PadicInt.toZModPow n ((bas c).repr ⟨x, hx⟩ i) := by
  unfold crd; rw [dif_pos hx]

/- English proof (translation)
Rewrite using `[crd_of_mem i hx, crd_of_mem i hy, crd_of_mem i (c.O.add_mem hx hy), ← map_add]`. Use `congr 1`. Establish `: (⟨x + y, c.O.add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`. Rewrite using `[this, map_add]`. Both sides reduce to the same expression.
-/
theorem crd_add {n : ℕ} (i : Ix c) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    crd c n i (x + y) = crd c n i x + crd c n i y := by
  rw [crd_of_mem i hx, crd_of_mem i hy, crd_of_mem i (c.O.add_mem hx hy), ← map_add]
  congr 1
  have : (⟨x + y, c.O.add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add]; rfl

/- English proof (translation)
Rewrite using `[crd_of_mem i hx, crd_of_mem i hy, crd_of_mem i (c.O.sub_mem hx hy), ← map_sub]`. Use `congr 1`. Establish `: (⟨x - y, c.O.sub_mem hx hy⟩ : c.O) = ⟨x, hx⟩ - ⟨y, hy⟩` using `rfl`. Rewrite using `[this, map_sub]`. Both sides reduce to the same expression.
-/
theorem crd_sub {n : ℕ} (i : Ix c) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    crd c n i (x - y) = crd c n i x - crd c n i y := by
  rw [crd_of_mem i hx, crd_of_mem i hy, crd_of_mem i (c.O.sub_mem hx hy), ← map_sub]
  congr 1
  have : (⟨x - y, c.O.sub_mem hx hy⟩ : c.O) = ⟨x, hx⟩ - ⟨y, hy⟩ := rfl
  rw [this, map_sub]; rfl

/- English proof (translation)
The claim follows from `c.O.mul_mem (c.O.algebraMap_mem a) hx`.
-/
theorem algebraMap_mul_mem (a : ℤ_[l]) {x : Qbar l} (hx : x ∈ c.O) :
    algebraMap ℤ_[l] (Qbar l) a * x ∈ c.O :=
  c.O.mul_mem (c.O.algebraMap_mem a) hx

/- English proof (translation)
Rewrite using `[crd_of_mem i hx, crd_of_mem i (algebraMap_mul_mem a hx), ← map_mul]`. Use `congr 1`. Establish `: (⟨algebraMap ℤ_[l] (Qbar l) a * x, algebraMap_mul_mem a hx⟩ : c.O) = a • ⟨x, hx⟩` using `by ext; simp [Algebra.smul_def]`. Rewrite using `[this, map_smul]`. Both sides reduce to the same expression.
-/
theorem crd_algebraMap_mul {n : ℕ} (i : Ix c) (a : ℤ_[l]) {x : Qbar l} (hx : x ∈ c.O) :
    crd c n i (algebraMap ℤ_[l] (Qbar l) a * x) = PadicInt.toZModPow n a * crd c n i x := by
  rw [crd_of_mem i hx, crd_of_mem i (algebraMap_mul_mem a hx), ← map_mul]
  congr 1
  have : (⟨algebraMap ℤ_[l] (Qbar l) a * x, algebraMap_mul_mem a hx⟩ : c.O) = a • ⟨x, hx⟩ := by
    ext; simp [Algebra.smul_def]
  rw [this, map_smul]; rfl

/- English proof (translation)
The claim follows from `SetLike.coe_mem _`.
-/
theorem lft_mem (n : ℕ) (a : Ix c → ZMod (l ^ n)) : lft c n a ∈ c.O := SetLike.coe_mem _

/- English proof (translation)
Rewrite using `[crd_of_mem i (lft_mem n a)]`. Establish `: (⟨lft c n a, lft_mem n a⟩ : c.O) = (bas c).equivFun.symm fun i => (((a i).val : ℕ) : ℤ_[l])` using `rfl`. Rewrite using `[this]`. Establish `h2` using `congrFun ((bas c).equivFun.apply_symm_apply fun i => (((a i).val : ℕ) : ℤ_[l])) i`. Rewrite `h2` using `[Module.Basis.equivFun_apply]`.

Rewrite using `[h2, map_natCast, ZMod.natCast_zmod_val]`.
-/
theorem crd_lft {n : ℕ} (a : Ix c → ZMod (l ^ n)) (i : Ix c) : crd c n i (lft c n a) = a i := by
  rw [crd_of_mem i (lft_mem n a)]
  have : (⟨lft c n a, lft_mem n a⟩ : c.O) = (bas c).equivFun.symm fun i => (((a i).val : ℕ) : ℤ_[l]) := rfl
  rw [this]
  have h2 := congrFun ((bas c).equivFun.apply_symm_apply fun i => (((a i).val : ℕ) : ℤ_[l])) i
  rw [Module.Basis.equivFun_apply] at h2
  rw [h2, map_natCast, ZMod.natCast_zmod_val]

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']`. Conclude with `r.2`.
-/
theorem norm_algebraMap_padicInt_le_one (r : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) r‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact r.2

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral (R := ℤ_[l]) norm_algebraMap_padicInt_le_one x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)`.
-/
theorem norm_le_one_of_mem {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral (R := ℤ_[l]) norm_algebraMap_padicInt_le_one x
    ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

/- English proof (translation)
Establish `h1 : ‖((u : c.O) : Qbar l)‖ * ‖(((u⁻¹ : (c.O)ˣ) : c.O) : Qbar l)‖ = 1`. Rewrite using `[← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules. Establish `h2` using `norm_le_one_of_mem (c := c) (u : c.O).2`. Establish `h3` using `norm_le_one_of_mem (c := c) ((u⁻¹ : (c.O)ˣ) : c.O).2`.

Establish `h4` using `norm_nonneg ((u : c.O) : Qbar l)`. Establish `h5` using `norm_nonneg (((u⁻¹ : (c.O)ˣ) : c.O) : Qbar l)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_unit_eq_one (u : (c.O)ˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 : ‖((u : c.O) : Qbar l)‖ * ‖(((u⁻¹ : (c.O)ˣ) : c.O) : Qbar l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem (c := c) (u : c.O).2
  have h3 := norm_le_one_of_mem (c := c) ((u⁻¹ : (c.O)ˣ) : c.O).2
  have h4 := norm_nonneg ((u : c.O) : Qbar l)
  have h5 := norm_nonneg (((u⁻¹ : (c.O)ˣ) : c.O) : Qbar l)
  nlinarith

/- English proof (translation)
Establish `: ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_natCast_l : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hlO : ((l : c.O) : Qbar l) = ((l : ℕ) : Qbar l)` using `by simp`. Establish `hl0 : (l : c.O) ≠ 0`. Introduce `h0`.

Establish `: ((l : ℕ) : Qbar l) = 0` using `by rw [← hlO, h0]; rfl`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `key : ∀ (a : c.O) (k : ℕ) (u : (c.O)ˣ), a = u * ϖ ^ k → ‖(a : Qbar l)‖ = ‖(ϖ : Qbar l)‖ ^ k`. Introduce `a k u e`. Rewrite using `[e]`.

Simplify using `[norm_unit_eq_one]`. Take `⟨k, u, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Establish `hn` using `key _ _ _ hk`.

Rewrite `hn` using `[hlO, norm_natCast_l, pow_zero]`. Establish `: (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hϖ1 : ‖(ϖ : Qbar l)‖ < 1`. Establish `hn` using `key _ _ _ hk`.

Rewrite `hn` using `[hlO, norm_natCast_l]`. Establish `hle` using `norm_le_one_of_mem (c := c) ϖ.2`. Break down `hle.lt_or_eq with h' | h'` into its components or cases. Conclude with `h'`. Rewrite `hn` using `[h', one_pow]`.

Establish `: (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hϖ0 : 0 < ‖(ϖ : Qbar l)‖`. Rewrite using `[norm_pos_iff]`. Introduce `h0`.

Conclude with `hϖ.ne_zero (Subtype.ext h0)`. Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, c.O.zero_mem, by rw [hx0, mul_zero]⟩`. Establish `hy0 : (⟨x, hx⟩ : c.O) ≠ 0` using `fun h0 => hx0 (congrArg Subtype.val h0)`. Take `⟨a, v, ha⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ`.

Establish `hln : ((l : c.O) ^ n) ≠ 0` using `pow_ne_zero _ hl0`. Take `⟨b, v', hb⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hln hϖ`. Establish `e1` using `key _ _ _ ha`. Establish `e2` using `key _ _ _ hb`. Establish `hxn : ‖x‖ = ‖(ϖ : Qbar l)‖ ^ a` using `e1`.

Establish `hln' : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖(ϖ : Qbar l)‖ ^ b`. Rewrite using `[← e2]`. Simplify using the standard rewrite rules. Rewrite `h` using `[hxn, hln']`. Establish `hba : b ≤ a` using `(pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖ1).1 h`.

Use `⟨(((v * v'⁻¹ : (c.O)ˣ) : c.O) * ϖ ^ (a - b) : c.O), SetLike.coe_mem _, ?_⟩` and prove the remaining obligations. Establish `e3 : (⟨x, hx⟩ : c.O) = (l : c.O) ^ n * (((v * v'⁻¹ : (c.O)ˣ) : c.O) * ϖ ^ (a - b))`. Rewrite using `[ha, hb]`. Establish `: ϖ ^ a = ϖ ^ b * ϖ ^ (a - b)` using `by rw [← pow_add, Nat.add_sub_cancel' hba]`. Rewrite using `[this, Units.val_mul]`.

Establish `hv : ((v' : c.O) * ((v'⁻¹ : (c.O)ˣ) : c.O)) = 1` using `Units.mul_inv v'`. Take the linear combination `(-(↑v * ϖ ^ b * ϖ ^ (a - b))) * hv`. Establish `e4` using `congrArg Subtype.val e3`. Simplify using `using e4`.
-/
theorem exists_eq_pow_mul_of_norm_le {n : ℕ} {x : Qbar l} (hx : x ∈ c.O)
    (h : ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) : ∃ w ∈ c.O, x = ((l : ℕ) : Qbar l) ^ n * w := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlO : ((l : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by simp
  have hl0 : (l : c.O) ≠ 0 := by
    intro h0
    have : ((l : ℕ) : Qbar l) = 0 := by rw [← hlO, h0]; rfl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have key : ∀ (a : c.O) (k : ℕ) (u : (c.O)ˣ), a = u * ϖ ^ k → ‖(a : Qbar l)‖ = ‖(ϖ : Qbar l)‖ ^ k := by
    intro a k u e
    rw [e]; simp [norm_unit_eq_one]

  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hn := key _ _ _ hk
    rw [hlO, norm_natCast_l, pow_zero] at hn
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    linarith
  have hϖ1 : ‖(ϖ : Qbar l)‖ < 1 := by
    have hn := key _ _ _ hk
    rw [hlO, norm_natCast_l] at hn
    have hle := norm_le_one_of_mem (c := c) ϖ.2
    rcases hle.lt_or_eq with h' | h'
    · exact h'
    · rw [h', one_pow] at hn
      have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
      linarith
  have hϖ0 : 0 < ‖(ϖ : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hϖ.ne_zero (Subtype.ext h0)
  by_cases hx0 : x = 0
  · exact ⟨0, c.O.zero_mem, by rw [hx0, mul_zero]⟩
  have hy0 : (⟨x, hx⟩ : c.O) ≠ 0 := fun h0 => hx0 (congrArg Subtype.val h0)
  obtain ⟨a, v, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hln : ((l : c.O) ^ n) ≠ 0 := pow_ne_zero _ hl0
  obtain ⟨b, v', hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hln hϖ
  have e1 := key _ _ _ ha
  have e2 := key _ _ _ hb
  have hxn : ‖x‖ = ‖(ϖ : Qbar l)‖ ^ a := e1
  have hln' : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖(ϖ : Qbar l)‖ ^ b := by
    rw [← e2]; simp
  rw [hxn, hln'] at h
  have hba : b ≤ a := (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖ1).1 h
  refine ⟨(((v * v'⁻¹ : (c.O)ˣ) : c.O) * ϖ ^ (a - b) : c.O), SetLike.coe_mem _, ?_⟩
  have e3 : (⟨x, hx⟩ : c.O) = (l : c.O) ^ n * (((v * v'⁻¹ : (c.O)ˣ) : c.O) * ϖ ^ (a - b)) := by
    rw [ha, hb]
    have : ϖ ^ a = ϖ ^ b * ϖ ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hba]
    rw [this, Units.val_mul]
    have hv : ((v' : c.O) * ((v'⁻¹ : (c.O)ˣ) : c.O)) = 1 := Units.mul_inv v'
    linear_combination (-(↑v * ϖ ^ b * ϖ ^ (a - b))) * hv
  have e4 := congrArg Subtype.val e3
  simpa using e4

/- English proof (translation)
Establish `hmap : algebraMap ℤ_[l] (Qbar l) ((l : ℤ_[l]) ^ n) = ((l : ℕ) : Qbar l) ^ n` using `by simp`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Take `⟨w, hw, rfl⟩` from `exists_eq_pow_mul_of_norm_le hx h`. Rewrite using `[← hmap, crd_algebraMap_mul i _ hw, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]`.

Introduce `h set y : c.O := ⟨x, hx⟩ with hy`. Establish `hr : ∀ i, ∃ a : ℤ_[l], (bas c).repr y i = (l : ℤ_[l]) ^ n * a`. Introduce `i`. Establish `h0` using `h i`. Rewrite `h0` using `[crd_of_mem i hx]`.

Establish `hm : (bas c).repr y i ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n))` using `h0`. Rewrite `hm` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `hm`. Conclude with `⟨a, by rw [← ha, mul_comm]⟩`. Use `choose a ha using hr`.

Establish `hsum : y = ((l : ℤ_[l]) ^ n) • ∑ i, a i • bas c i` using `by conv_lhs => rw [← (bas c).sum_repr y]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ha i, smul_smul]`. Establish `hx' : x = algebraMap ℤ_[l] (Qbar l) ((l : ℤ_[l]) ^ n) * ((∑ i, a i • bas c i : c.O) : Qbar l)`.

Use `congrArg Subtype.val hsum` as an intermediate fact. Rewrite `this` using `[Subalgebra.coe_smul, Algebra.smul_def]`. Conclude with `this`. Rewrite using `[hx', hmap, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_iff_crd_eq_zero {n : ℕ} {x : Qbar l} (hx : x ∈ c.O) :
    ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ∀ i, crd c n i x = 0 := by
  have hmap : algebraMap ℤ_[l] (Qbar l) ((l : ℤ_[l]) ^ n) = ((l : ℕ) : Qbar l) ^ n := by simp
  constructor
  · intro h i
    obtain ⟨w, hw, rfl⟩ := exists_eq_pow_mul_of_norm_le hx h
    rw [← hmap, crd_algebraMap_mul i _ hw, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  · intro h
    set y : c.O := ⟨x, hx⟩ with hy
    have hr : ∀ i, ∃ a : ℤ_[l], (bas c).repr y i = (l : ℤ_[l]) ^ n * a := by
      intro i
      have h0 := h i
      rw [crd_of_mem i hx] at h0
      have hm : (bas c).repr y i ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := h0
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hm
      obtain ⟨a, ha⟩ := hm
      exact ⟨a, by rw [← ha, mul_comm]⟩
    choose a ha using hr
    have hsum : y = ((l : ℤ_[l]) ^ n) • ∑ i, a i • bas c i := by
      conv_lhs => rw [← (bas c).sum_repr y]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, smul_smul]
    have hx' : x = algebraMap ℤ_[l] (Qbar l) ((l : ℤ_[l]) ^ n) * ((∑ i, a i • bas c i : c.O) : Qbar l) := by
      have := congrArg Subtype.val hsum
      rw [Subalgebra.coe_smul, Algebra.smul_def] at this
      exact this
    rw [hx', hmap, norm_mul]
    calc ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((∑ i, a i • bas c i : c.O) : Qbar l)‖
        ≤ ‖((l : ℕ) : Qbar l) ^ n‖ * 1 := by
          gcongr; exact norm_le_one_of_mem (SetLike.coe_mem _)
      _ = _ := mul_one _

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

/- English proof (translation)
Unfold `Cg`. Rewrite using `[norm_le_iff_crd_eq_zero (c.O.sub_mem hx hy)]`. Simplify using `only [crd_sub _ hx hy, sub_eq_zero]`.
-/
theorem cg_iff {n : ℕ} {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    Cg n x y ↔ ∀ i, crd c n i x = crd c n i y := by
  unfold Cg
  rw [norm_le_iff_crd_eq_zero (c.O.sub_mem hx hy)]
  simp only [crd_sub _ hx hy, sub_eq_zero]

/- English proof (translation)
Rewrite using `[continuous_discrete_rng]`. Introduce `b`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `hpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖` using `norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))`.

Use `filter_upwards [hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f x) hpos)] with y hy`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢`. Rewrite using `[← hx]`. Rewrite `hy` using `[Set.mem_preimage, Metric.mem_ball, dist_eq_norm]`. Conclude with `(cg_iff (hO y) (hO x)).1 hy.le i`.
-/
theorem continuous_crd {X : Type*} [TopologicalSpace X] {f : X → Qbar l} (hf : Continuous f)
    (hO : ∀ x, f x ∈ c.O) (n : ℕ) (i : Ix c) : Continuous fun x => crd c n i (f x) := by
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  filter_upwards [hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f x) hpos)] with y hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [← hx]
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
  exact (cg_iff (hO y) (hO x)).1 hy.le i

section Glob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

variable (c n S ξ) in

def zc (i : Ix c) (p : GS Ω (S : Set Pl) × GS Ω (S : Set Pl)) : ZMod (l ^ n) :=
  crd c n i (ξ (Quotient.out p.1) (Quotient.out p.2))

/- English proof (translation)
Establish `hk : ∀ s : G ℚ Ω, s⁻¹ * Quotient.out (s : GS Ω (S : Set Pl)) ∈ (toGS Ω (S : Set Pl)).ker`. Introduce `s`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv]`. Establish `: toGS Ω (S : Set Pl) (Quotient.out (s : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) s` using `Quotient.out_eq _`. Rewrite using `[this, inv_mul_cancel]`.

Establish `h` using `hξ.unr s t _ (hk s) _ (hk t)`. Rewrite `h` using `[mul_inv_cancel_left, mul_inv_cancel_left]`. Conclude with `(cg_iff (hξ.int _ _) (hξ.int _ _)).1 h i`.
-/
theorem zc_mk (hξ : Coc2 c n S ξ) (i : Ix c) (s t : G ℚ Ω) :
    zc c n S ξ i ((s : GS Ω (S : Set Pl)), (t : GS Ω (S : Set Pl))) = crd c n i (ξ s t) := by
  have hk : ∀ s : G ℚ Ω, s⁻¹ * Quotient.out (s : GS Ω (S : Set Pl)) ∈ (toGS Ω (S : Set Pl)).ker := by
    intro s
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : toGS Ω (S : Set Pl) (Quotient.out (s : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) s :=
      Quotient.out_eq _
    rw [this, inv_mul_cancel]
  have h := hξ.unr s t _ (hk s) _ (hk t)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
  exact (cg_iff (hξ.int _ _) (hξ.int _ _)).1 h i

/- English proof (translation)
The claim follows from `(IsOpenMap.prodMap QuotientGroup.isOpenMap_coe QuotientGroup.isOpenMap_coe).isQuotientMap ((continuous_toGS Ω _).prodMap (continuous_toGS Ω _)) (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)`.
-/
theorem isQuotientMap_toGS_prod :
    Topology.IsQuotientMap (Prod.map (toGS Ω (S : Set Pl)) (toGS Ω (S : Set Pl))) :=
  (IsOpenMap.prodMap QuotientGroup.isOpenMap_coe QuotientGroup.isOpenMap_coe).isQuotientMap
    ((continuous_toGS Ω _).prodMap (continuous_toGS Ω _))
    (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isQuotientMap_toGS_prod.continuous_iff]`. Establish `: (zc c n S ξ i ∘ Prod.map (toGS Ω (S : Set Pl)) (toGS Ω (S : Set Pl))) = fun p : G ℚ Ω × G ℚ Ω => crd c n i (ξ p.1 p.2)` using `funext fun p => zc_mk hξ i p.1 p.2`. Rewrite using `[this]`. Conclude with `continuous_crd hξ.cont (fun p => hξ.int _ _) n i`.

Introduce `g h k`. Take `⟨r, rfl⟩` from `QuotientGroup.mk_surjective g`. Take `⟨s, rfl⟩` from `QuotientGroup.mk_surjective h`. Take `⟨t, rfl⟩` from `QuotientGroup.mk_surjective k`. Rewrite using `[charRep_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, zc_mk hξ, zc_mk hξ, zc_mk hξ, zc_mk hξ]`.

Establish `hμr : ((μ (r : GS Ω (S : Set Pl)) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l r : ℤ_[l])`. Use `DFunLike.congr_fun hμ r` as an intermediate fact. Conclude with `congrArg Units.val this`. Rewrite using `[hμr]`. Establish `hc` using `(cg_iff (c.O.add_mem (algebraMap_mul_mem _ (hξ.int s t)) (hξ.int r (s * t))) (c.O.add_mem (hξ.int _ _) (hξ.int _ _))).1 (hξ.coc r s t) i`.

Rewrite `hc` using `[crd_add i (algebraMap_mul_mem _ (hξ.int s t)) (hξ.int r (s * t)), crd_add i (hξ.int _ _) (hξ.int _ _), crd_algebraMap_mul i _ (hξ.int s t)]`. Take the linear combination `hc`.
-/
theorem zc_mem {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : zc c n S ξ i ∈ Z2 (charRep μ) := by
  refine ⟨?_, ?_⟩
  · rw [isQuotientMap_toGS_prod.continuous_iff]
    have : (zc c n S ξ i ∘ Prod.map (toGS Ω (S : Set Pl)) (toGS Ω (S : Set Pl))) =
        fun p : G ℚ Ω × G ℚ Ω => crd c n i (ξ p.1 p.2) := funext fun p => zc_mk hξ i p.1 p.2
    rw [this]
    exact continuous_crd hξ.cont (fun p => hξ.int _ _) n i
  · intro g h k
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective k
    rw [charRep_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, zc_mk hξ, zc_mk hξ, zc_mk hξ,
      zc_mk hξ]
    have hμr : ((μ (r : GS Ω (S : Set Pl)) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l r : ℤ_[l]) := by
      have := DFunLike.congr_fun hμ r
      exact congrArg Units.val this
    rw [hμr]
    have hc := (cg_iff (c.O.add_mem (algebraMap_mul_mem _ (hξ.int s t)) (hξ.int r (s * t)))
      (c.O.add_mem (hξ.int _ _) (hξ.int _ _))).1 (hξ.coc r s t) i
    rw [crd_add i (algebraMap_mul_mem _ (hξ.int s t)) (hξ.int r (s * t)),
      crd_add i (hξ.int _ _) (hξ.int _ _), crd_algebraMap_mul i _ (hξ.int s t)] at hc
    linear_combination hc

end Glob

end GlobalTheory.Ord2.Rec
