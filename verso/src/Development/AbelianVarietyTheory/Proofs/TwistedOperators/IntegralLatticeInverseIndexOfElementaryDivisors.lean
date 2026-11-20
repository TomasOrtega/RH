import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Set `φ : (AddSubgroup.pi Set.univ I) →+ ∀ a, (I a ⧸ (J a).addSubgroupOf (I a))` to `{ toFun := fun x a => QuotientAddGroup.mk (⟨(x : ι → G) a, x.2 a (Set.mem_univ a)⟩ : I a) map_zero' := by funext a; rfl map_add' := fun x y => by funext a; rfl }`. Establish `hsurj : Function.Surjective φ`. Introduce `c`. Use `choose y hy using fun a => QuotientAddGroup.mk_surjective (c a)`. Use `⟨⟨fun a => (y a : G), fun a _ => (y a).2⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Use `show QuotientAddGroup.mk (⟨(y a : G), _⟩ : I a) = c a`. Rewrite using `[← hy a]`. Establish `hker : φ.ker = (AddSubgroup.pi Set.univ J).addSubgroupOf (AddSubgroup.pi Set.univ I)`. Use extensionality with `x`.

Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce `h a _`. Use `congrFun h a` as an intermediate fact. Simplify using `only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this`.

Conclude with `this`. Introduce `h`. Use function extensionality and compare the values at `a`. Simplify using `only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Conclude with `h a (Set.mem_univ a)`.

Unfold `AddSubgroup.relIndex AddSubgroup.index`. Rewrite using `[← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, Nat.card_pi]`.
-/
theorem relIndex_pi_univ {ι : Type} [Fintype ι] {G : Type} [AddCommGroup G] (I J : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ J).relIndex (AddSubgroup.pi Set.univ I) = ∏ a, (J a).relIndex (I a) := by
  classical
  let φ : (AddSubgroup.pi Set.univ I) →+ ∀ a, (I a ⧸ (J a).addSubgroupOf (I a)) :=
    { toFun := fun x a => QuotientAddGroup.mk (⟨(x : ι → G) a, x.2 a (Set.mem_univ a)⟩ : I a)
      map_zero' := by funext a; rfl
      map_add' := fun x y => by funext a; rfl }
  have hsurj : Function.Surjective φ := by
    intro c
    choose y hy using fun a => QuotientAddGroup.mk_surjective (c a)
    refine ⟨⟨fun a => (y a : G), fun a _ => (y a).2⟩, ?_⟩
    funext a
    show QuotientAddGroup.mk (⟨(y a : G), _⟩ : I a) = c a
    rw [← hy a]
  have hker : φ.ker = (AddSubgroup.pi Set.univ J).addSubgroupOf (AddSubgroup.pi Set.univ I) := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h a _
      have := congrFun h a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf] at this
      exact this
    · intro h
      funext a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact h a (Set.mem_univ a)
  unfold AddSubgroup.relIndex AddSubgroup.index
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, Nat.card_pi]

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def scaledInt (c : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scaledInt {c x : L} : x ∈ scaledInt c ↔ c * x ∈ intL L := Iff.rfl

/- English proof (translation)
Introduce `y` and use `⟨c⁻¹ * y, by simp [AddMonoidHom.mulLeft, mul_inv_cancel_left₀ hc]⟩`.
-/
theorem mulLeft_surjective {c : L} (hc : c ≠ 0) : Function.Surjective (AddMonoidHom.mulLeft c) :=
  fun y => ⟨c⁻¹ * y, by simp [AddMonoidHom.mulLeft, mul_inv_cancel_left₀ hc]⟩

/- English proof (translation)
Introduce `x y h` and use `mul_left_cancel₀ hc h`.
-/
theorem mulLeft_injective {c : L} (hc : c ≠ 0) : Function.Injective (AddMonoidHom.mulLeft c) :=
  fun x y h => mul_left_cancel₀ hc h

/- English proof (translation)
Establish `hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hU.2.2.2.1`. Establish `h0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hv` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hv.symm`.

Establish `hϖ : ϖ ∈ intL L` using `by show Valued.v ϖ ≤ 1`. Rewrite using `[hv, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2`. Establish `hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup` using `AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _`.

Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]`. Conclude with `intIndex L ϖ σ q hU`. Proceed by induction on `d with`. Consider the case `zero`. Establish `: scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup`.

Use extensionality with `x`. Simplify using `[mem_scaledInt]`. Rewrite using `[this, AddSubgroup.relIndex_self]`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Establish `hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d)` using `fun x hx => mul_mem (pow_mem hϖ d) hx`. Establish `hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1))` using `fun x hx => by`. Rewrite `hx`, the goal using `[mem_scaledInt]`. Rewrite using `[pow_succ, mul_comm _ ϖ, mul_assoc]`. Conclude with `mul_mem hϖ hx`.

Establish `hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d))`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_comap, mem_scaledInt]`. Rewrite using `[pow_succ, mul_comm _ ϖ, mul_assoc]`. Conclude with `Iff.rfl`.

Establish `hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2`. Rewrite using `[hc, scaledInt, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relIndex_scaledInt {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : ℕ) :
    (intL L).toAddSubgroup.relIndex (scaledInt (ϖ ^ d)) = q ^ (2 * d) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2 := by
    have hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup :=
      AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]
    exact intIndex L ϖ σ q hU
  induction d with
  | zero =>
    have : scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup := by
      ext x; simp [mem_scaledInt]
    rw [this, AddSubgroup.relIndex_self]; simp
  | succ d ih =>
    have hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d) := fun x hx =>
      mul_mem (pow_mem hϖ d) hx
    have hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1)) := fun x hx => by
      rw [mem_scaledInt] at hx ⊢
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact mul_mem hϖ hx
    have hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d)) := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_scaledInt]
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact Iff.rfl
    have hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2 := by
      rw [hc, scaledInt, AddSubgroup.relIndex_comap,
        AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]
    ring

end

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Rewrite `hr`, the goal using `[mem_intV]`. Introduce `j`. Simplify using `only [Matrix.vecMul, dotProduct]`. Conclude with `Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)`.
-/
theorem intV_vecMul {r : Fin n → L} {M : Matrix (Fin n) (Fin n) L} (hr : r ∈ intV L n) (hM : IsInt M) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  simp only [Matrix.vecMul, dotProduct]
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[mem_preLat, AddSubgroup.mem_pi]`. Simplify using `only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]`.
-/
theorem preLat_diagonal (ϖ : L) (d : Fin n → ℕ) :
    preLat (Matrix.diagonal fun i => ϖ ^ d i) = AddSubgroup.pi Set.univ fun i => scaledInt (ϖ ^ d i) := by
  ext r
  rw [mem_preLat, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]

/- English proof (translation)
Rewrite using `[preLat_diagonal, intV, relIndex_pi_univ]`. Simplify using `only [relIndex_scaledInt hU, Finset.mul_sum, Finset.prod_pow_eq_pow_sum]`.
-/
theorem latIndex_diagonal {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : Fin n → ℕ) :
    (intV L n).relIndex (preLat (Matrix.diagonal fun i => ϖ ^ d i)) = q ^ (2 * ∑ i, d i) := by
  rw [preLat_diagonal, intV, relIndex_pi_univ]
  simp only [relIndex_scaledInt hU, Finset.mul_sum, Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Establish `ea2 : a * a' = 1` using `mul_eq_one_comm.1 ea`. Set `f : (Fin n → L) →+ (Fin n → L)` to `a.vecMulLinear.toAddMonoidHom`. Establish `hf : ∀ r, f r = r ᵥ* a` using `fun r => rfl`. Establish `hsurj : Function.Surjective f` using `fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩`. Establish `h1 : preLat A = (preLat D).comap f`.

Use extensionality with `r`. Rewrite using `[AddSubgroup.mem_comap, hf]`. Conclude with `hpre r`. Establish `h2 : intV L n = (intV L n).comap f`. Use extensionality with `r`.

Rewrite using `[AddSubgroup.mem_comap, hf]`. Use `⟨fun h => intV_vecMul h ha, fun h => ?_⟩` and prove the remaining obligations. Use `intV_vecMul h ha'` as an intermediate fact. Rewrite `this` using `[Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one]`. Then use the resulting hypothesis. Rewrite using `[h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]`.
-/
theorem relIndex_preLat_mul {A D a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (ea : a' * a = 1)
    (hpre : ∀ r, r ∈ preLat A ↔ r ᵥ* a ∈ preLat D) :
    (intV L n).relIndex (preLat A) = (intV L n).relIndex (preLat D) := by
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hf : ∀ r, f r = r ᵥ* a := fun r => rfl
  have hsurj : Function.Surjective f := fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : preLat A = (preLat D).comap f := by
    ext r; rw [AddSubgroup.mem_comap, hf]; exact hpre r
  have h2 : intV L n = (intV L n).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hf]
    refine ⟨fun h => intV_vecMul h ha, fun h => ?_⟩
    have := intV_vecMul h ha'
    rwa [Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one] at this
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]

end

/- English proof (translation)
Introduce `hS L _ _ ϖ σ q n hU A k hA hdet`. Establish `hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hU.2.2.2.1`. Establish `h0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hv` using `[map_zero]`.

Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hA0 : A.det ≠ 0` using `fun h => by`. Rewrite `hdet` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hdet.symm`. Take `⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩` from `hS L ϖ n hv A hA0`.

Use `set D := Matrix.diagonal fun i => ϖ ^ d i with hD`. Establish `ea2 : a * a' = 1` using `mul_eq_one_comm.1 ea`. Establish `eb2 : b' * b = 1` using `mul_eq_one_comm.1 eb`. Establish `hDint : IsInt D`. Establish `: D = a' * (a * D * b) * b'`.

Rewrite using `[show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[this]`. Conclude with `(ha'.mul hA).mul hb'`. Establish `hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z)` using `fun z => by`. Rewrite using `[map_zpow₀, hv, ← WithZero.exp_zsmul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `hd : ∀ i, 0 ≤ d i` using `fun i => by`. Establish `h` using `hDint i i`. Rewrite `h` using `[hD, Matrix.diagonal_apply_eq]`.

Establish `h' : Valued.v (ϖ ^ d i) ≤ 1` using `h`. Rewrite `h'` using `[hvz, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Use `set e : Fin n → ℕ := fun i => (d i).toNat with he`. Establish `hde : ∀ i, d i = (e i : ℤ)` using `fun i => (Int.toNat_of_nonneg (hd i)).symm`.

Establish `hDe : D = Matrix.diagonal fun i => ϖ ^ e i`. Rewrite using `[hD]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[hde i, zpow_natCast]`.

Establish `hk : k = ∑ i, e i`. Establish `hva : Valued.v a.det = 1` using `v_det_eq_one ha ha' ea2`. Establish `hvb : Valued.v b.det = 1` using `v_det_eq_one hb hb' eb`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj]`. Conclude with `(neg_inj.1 hdet).symm` after adjusting the coercions.

Establish `hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D` using `fun r => by show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n`. Rewrite using `[← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]`. Use `⟨fun h => ?_, fun h => intV_vecMul h hb⟩` and prove the remaining obligations. Use `intV_vecMul h hb'` as an intermediate fact. Rewrite `this` using `[Matrix.vecMul_vecMul, eb, Matrix.vecMul_one]`. Then use the resulting hypothesis.

Rewrite using `[relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]`.
-/
theorem latIndex_of_smith : Smith → LatIndex := by
  intro hS L _ _ ϖ σ q n hU A k hA hdet
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hA0 : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdet; exact WithZero.exp_ne_zero hdet.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hv A hA0
  set D := Matrix.diagonal fun i => ϖ ^ d i with hD
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb2 : b' * b = 1 := mul_eq_one_comm.1 eb

  have hDint : IsInt D := by
    have : D = a' * (a * D * b) * b' := by
      rw [show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb,
        Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (ha'.mul hA).mul hb'
  have hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z) := fun z => by
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]; congr 1; simp
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hDint i i
    rw [hD, Matrix.diagonal_apply_eq] at h
    have h' : Valued.v (ϖ ^ d i) ≤ 1 := h
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at h'
    omega
  set e : Fin n → ℕ := fun i => (d i).toNat with he
  have hde : ∀ i, d i = (e i : ℤ) := fun i => (Int.toNat_of_nonneg (hd i)).symm
  have hDe : D = Matrix.diagonal fun i => ϖ ^ e i := by
    rw [hD]; congr 1; funext i; rw [hde i, zpow_natCast]

  have hk : k = ∑ i, e i := by
    have hva : Valued.v a.det = 1 := v_det_eq_one ha ha' ea2
    have hvb : Valued.v b.det = 1 := v_det_eq_one hb hb' eb
    rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj] at hdet
    exact_mod_cast (neg_inj.1 hdet).symm

  have hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D := fun r => by
    show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    refine ⟨fun h => ?_, fun h => intV_vecMul h hb⟩
    have := intV_vecMul h hb'
    rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this
  rw [relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]

end GlobalTheory.InertZeta
