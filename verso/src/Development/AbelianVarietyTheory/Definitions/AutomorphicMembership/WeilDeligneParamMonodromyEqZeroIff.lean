import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

def IsTameChar (t : Ine (F := E) A →* Multiplicative ℤ_[l]) : Prop :=
  Continuous t ∧ Function.Surjective t

def tval (t : Ine (F := E) A →* Multiplicative ℤ_[l]) (σ : Ine (F := E) A) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((t σ).toAdd : ℚ_[l])

section Tame

variable {t t' : Ine (F := E) A →* Multiplicative ℤ_[l]}

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Simplify using `[tval]`.
-/
@[simp] theorem tval_mul (σ τ : Ine (F := E) A) : tval t (σ * τ) = tval t σ + tval t τ := by
  simp [tval]

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Simplify using `[tval]`.
-/
@[simp] theorem tval_one : tval t 1 = 0 := by simp [tval]

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Simplify using `[tval]`.
-/
@[simp] theorem tval_pow (σ : Ine (F := E) A) (k : ℕ) : tval t (σ ^ k) = k * tval t σ := by
  simp [tval]

/- English proof (translation)
Take `⟨σ, hσ, hx⟩` from `GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne E Ω A w h l Fact.out (unif w) unif_mem unif_notMem (rootOf Ω l (unifUnit w : E) 1) (by`. Use `rootOf_pow (Ω := Ω) l (unifUnit w : E) 1` as an intermediate fact. Rewrite using `[pow_one] at this)` and apply the resulting hypothesis. Conclude with `⟨continuous_kummerChar h hl _, surjective_kummerChar h hl _ hσ hx⟩`.
-/
theorem isTameChar_tameL (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) :
    IsTameChar (tameL h hl) := by
  obtain ⟨σ, hσ, hx⟩ := GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne E Ω A w h l Fact.out (unif w) unif_mem unif_notMem
    (rootOf Ω l (unifUnit w : E) 1) (by
      have := rootOf_pow (Ω := Ω) l (unifUnit w : E) 1
      rwa [pow_one] at this)
  exact ⟨continuous_kummerChar h hl _, surjective_kummerChar h hl _ hσ hx⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.TameCharUnique.exists_eq_mul E Ω A w h l hl t t' ht.1 ht'.1 ht'.2`. Use `⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => by simp [tval, hc]⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `ht.2 (Multiplicative.ofAdd 1)`. Use `hc σ` as an intermediate fact. Rewrite `this` using `[hσ]`.

Introduce `h0`. Rewrite `h0` using `[map_eq_zero, PadicInt.coe_eq_zero]`. Simplify using `[h0] at this`.
-/
theorem IsTameChar.exists_mul (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t σ = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul E Ω A w h l hl t t' ht.1 ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => by simp [tval, hc]⟩
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  have := hc σ
  rw [hσ] at this
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  simp [h0] at this

/- English proof (translation)
Take `⟨c, -, hc⟩` from `ht.exists_mul h hl (isTameChar_tameL h hl)`. Rewrite using `[hc, hc, mul_left_comm, tval, tameL, kummerChar_ineConj, map_mul, map_zpow₀, map_natCast]`. Both sides reduce to the same expression.
-/
theorem IsTameChar.tval_ineConj (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (g : Weil h) (σ : Ine (F := E) A) :
    tval t (ineConj g σ) = ((normV w : ℕ) : Qbar l) ^ deg g * tval t σ := by
  obtain ⟨c, -, hc⟩ := ht.exists_mul h hl (isTameChar_tameL h hl)
  rw [hc, hc, mul_left_comm, tval, tameL, kummerChar_ineConj, map_mul, map_zpow₀, map_natCast]
  rfl

/- English proof (translation)
Use `compactSpace_Ine (E := E) A` as an intermediate fact. Establish `: Finite (Ine (F` using `E) A ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hU`. Take `⟨σ, hσ⟩` from `ht.2 (Multiplicative.ofAdd 1)`. Take `⟨d, hd, -, hσd⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) σ`. Conclude with `⟨σ ^ d, hσd, by simpa [tval, hσ] using hd.ne'⟩`.
-/
theorem IsTameChar.exists_tval_ne_zero (ht : IsTameChar t) {U : Subgroup (Ine (F := E) A)}
    (hU : IsOpen (U : Set (Ine (F := E) A))) : ∃ σ ∈ U, tval t σ ≠ 0 := by
  have := compactSpace_Ine (E := E) A
  have : Finite (Ine (F := E) A ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hU
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  obtain ⟨d, hd, -, hσd⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := U)) σ
  exact ⟨σ ^ d, hσd, by simpa [tval, hσ] using hd.ne'⟩

end Tame

def IsMonodromy (t : Ine (F := E) A →* Multiplicative ℤ_[l]) (r : G E Ω →* GL n (Qbar l))
    (N : Matrix n n (Qbar l)) : Prop :=
  IsNilpotent N ∧ ∃ U : Subgroup (Ine (F := E) A), IsOpen (U : Set (Ine (F := E) A)) ∧
    ∀ σ ∈ U, (r σ : Matrix n n (Qbar l)) = exp (tval t σ • N)

def inePart {φ : Weil h} (hφ : deg φ = 1) (g : Weil h) : Ine (F := E) A :=
  ⟨((φ ^ deg g)⁻¹ * g : Weil h), deg_eq_zero_iff.mp (by simp [hφ])⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ineIncl_inePart {φ : Weil h} (hφ : deg φ = 1) (g : Weil h) :
    ineIncl h (inePart hφ g) = (φ ^ deg g)⁻¹ * g := rfl

/- English proof (translation)
The claim follows from `Subgroup.inclusion_injective (Ine_le_Weil h) (by show ineIncl h _ = ineIncl h _ simp [hφ])`.
-/
@[simp] theorem inePart_zpow_mul {φ : Weil h} (hφ : deg φ = 1) (k : ℤ) (σ : Ine (F := E) A) :
    inePart hφ (φ ^ k * ineIncl h σ) = σ :=
  Subgroup.inclusion_injective (Ine_le_Weil h) (by
    show ineIncl h _ = ineIncl h _
    simp [hφ])

/- English proof (translation)
Simplify using `using inePart_zpow_mul hφ 0 σ`.
-/
@[simp] theorem inePart_ineIncl {φ : Weil h} (hφ : deg φ = 1) (σ : Ine (F := E) A) :
    inePart hφ (ineIncl h σ) = σ := by
  simpa using inePart_zpow_mul hφ 0 σ

/- English proof (translation)
The claim follows from `Subgroup.inclusion_injective (Ine_le_Weil h) (by show ineIncl h _ = ineIncl h _ simp [zpow_add, mul_assoc])`.
-/
theorem inePart_mul {φ : Weil h} (hφ : deg φ = 1) (g g' : Weil h) :
    inePart hφ (g * g') = ineConj (φ ^ deg g')⁻¹ (inePart hφ g) * inePart hφ g' :=
  Subgroup.inclusion_injective (Ine_le_Weil h) (by
    show ineIncl h _ = ineIncl h _
    simp [zpow_add, mul_assoc])

def wdMat (t : Ine (F := E) A →* Multiplicative ℤ_[l]) {φ : Weil h} (hφ : deg φ = 1)
    (r : G E Ω →* GL n (Qbar l)) (N : Matrix n n (Qbar l)) (g : Weil h) : Matrix n n (Qbar l) :=
  (r g : Matrix n n (Qbar l)) * exp ((-tval t (inePart hφ g)) • N)

def toEndC (ι : Qbar l ≃+* ℂ) : Matrix n n (Qbar l) →+* End ℂ (n → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] End ℂ (n → ℂ)) :
    Matrix n n ℂ →+* End ℂ (n → ℂ)).comp ι.toRingHom.mapMatrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toEndC_apply (ι : Qbar l ≃+* ℂ) (M : Matrix n n (Qbar l)) :
    toEndC ι M = Matrix.toLin' (M.map ι) := rfl

/- English proof (translation)
Rewrite using `[toEndC_apply, toEndC_apply, ← map_smul]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem toEndC_smul (ι : Qbar l ≃+* ℂ) (c : Qbar l) (M : Matrix n n (Qbar l)) :
    toEndC ι (c • M) = ι c • toEndC ι M := by
  rw [toEndC_apply, toEndC_apply, ← map_smul]
  congr 1
  ext; simp

/- English proof (translation)
The claim follows from `Matrix.toLin'.injective.comp (Matrix.map_injective ι.injective)`.
-/
theorem toEndC_injective (ι : Qbar l ≃+* ℂ) : Function.Injective (toEndC (n := n) ι) :=
  Matrix.toLin'.injective.comp (Matrix.map_injective ι.injective)

/- English proof (translation)
Rewrite using `[toEndC_apply, Matrix.charpoly_toLin']`. Conclude with `Matrix.charpoly_map M ι.toRingHom`.
-/
theorem charpoly_toEndC (ι : Qbar l ≃+* ℂ) (M : Matrix n n (Qbar l)) :
    (toEndC ι M).charpoly = M.charpoly.map ι.toRingHom := by
  rw [toEndC_apply, Matrix.charpoly_toLin']
  exact Matrix.charpoly_map M ι.toRingHom

section Monodromy

variable {t t' : Ine (F := E) A →* Multiplicative ℤ_[l]} {r : G E Ω →* GL n (Qbar l)}
  {N N' : Matrix n n (Qbar l)} {φ φ' : Weil h}

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Set `e : Ine (F` to `E) A →* Matrix n n (Qbar l) := { toFun := fun σ => exp (tval t σ • N) map_one' := by simp map_mul' := fun σ τ => by rw [tval_mul, exp_add_smul hN] }`. Use `⟨hN, (r.comp (Ine (F := E) A).subtype).eqLocus e.toHomUnits, Subgroup.isOpen_of_mem_nhds _ (g := 1) (hr.mono fun σ hσ => Units.ext hσ), fun σ hσ => congrArg Units.val hσ⟩` and prove the remaining obligations.
-/
theorem IsMonodromy.of_nhds (hN : IsNilpotent N)
    (hr : ∀ᶠ σ : Ine (F := E) A in nhds 1, (r σ : Matrix n n (Qbar l)) = exp (tval t σ • N)) :
    IsMonodromy t r N := by
  let e : Ine (F := E) A →* Matrix n n (Qbar l) :=
    { toFun := fun σ => exp (tval t σ • N)
      map_one' := by simp
      map_mul' := fun σ τ => by rw [tval_mul, exp_add_smul hN] }
  refine ⟨hN, (r.comp (Ine (F := E) A).subtype).eqLocus e.toHomUnits,
    Subgroup.isOpen_of_mem_nhds _ (g := 1) (hr.mono fun σ hσ => Units.ext hσ),
    fun σ hσ => congrArg Units.val hσ⟩

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, U, hU, H⟩`. Conclude with `.of_open hU U.one_mem fun σ hσ => Units.ext (by simpa using H σ hσ)`. Introduce `H`. Use `.of_nhds IsNilpotent.zero ?_` and prove the remaining obligations.

Use `filter_upwards [H.mem_nhds (show (1 : Ine (F := E) A) ∈ _ by simp)] with σ hσ`. Simplify using `using congrArg Units.val hσ`.
-/
theorem isMonodromy_zero_iff : IsMonodromy t r 0 ↔ IsSmooth (r.comp (Weil h).subtype) := by
  constructor
  · rintro ⟨-, U, hU, H⟩
    exact .of_open hU U.one_mem fun σ hσ => Units.ext (by simpa using H σ hσ)
  · intro H
    refine .of_nhds IsNilpotent.zero ?_
    filter_upwards [H.mem_nhds (show (1 : Ine (F := E) A) ∈ _ by simp)] with σ hσ
    simpa using congrArg Units.val hσ

/- English proof (translation)
Take `⟨h1, U, hU, H⟩` from `hN`. Take `⟨h1', U', hU', H'⟩` from `hN'`. Take `⟨σ, hσ, h0⟩` from `ht.exists_tval_ne_zero (U := U ⊓ U') (hU.inter hU')`. Use `eq_of_exp_smul_eq h1 h1' h0 fun k => ?_` and prove the remaining obligations. Rewrite using `[← tval_pow, ← H _ (pow_mem hσ.1 k), ← H' _ (pow_mem hσ.2 k)]`.
-/
theorem IsMonodromy.unique (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hN' : IsMonodromy t r N') : N = N' := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨h1', U', hU', H'⟩ := hN'
  obtain ⟨σ, hσ, h0⟩ := ht.exists_tval_ne_zero (U := U ⊓ U') (hU.inter hU')
  refine eq_of_exp_smul_eq h1 h1' h0 fun k => ?_
  rw [← tval_pow, ← H _ (pow_mem hσ.1 k), ← H' _ (pow_mem hσ.2 k)]

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Take `⟨h1, U, hU, H⟩` from `hN`. Conclude with `⟨h1.smul c, U, hU, fun σ hσ => by rw [H σ hσ, hc, smul_smul, mul_comm]⟩`.
-/
theorem IsMonodromy.smul {c : Qbar l} (hc : ∀ σ, tval t σ = c * tval t' σ)
    (hN : IsMonodromy t r N) : IsMonodromy t' r (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  exact ⟨h1.smul c, U, hU, fun σ hσ => by rw [H σ hσ, hc, smul_smul, mul_comm]⟩

/- English proof (translation)
Establish `hq : ((normV w : ℕ) : Qbar l) ^ deg g ≠ 0` using `zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)`. Use `set M : Matrix n n (Qbar l) := (r g).val * N * (r g)⁻¹.val with hM`. Establish `hM' : (r g : Matrix n n (Qbar l)) * N = M * r g` using `by rw [hM, Units.inv_mul_cancel_right]`. Establish `hMn : IsNilpotent M`. Take `⟨k, hk⟩` from `hN.1`.

Conclude with `⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩`. Establish `h2 : IsMonodromy t r ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ • M)`. Take `⟨h1, U, hU, H⟩` from `hN`. Use `.of_nhds (hMn.smul _) ?_` and prove the remaining obligations. Establish `h0 : ineConj g⁻¹ (1 : Ine (F` using `E) A) = 1 := Subtype.ext (by simp)`.

Use `filter_upwards [(hU.preimage (continuous_ineConj g⁻¹)).mem_nhds (show ineConj g⁻¹ 1 ∈ U by rw [h0]; exact U.one_mem)] with σ hσ`. Establish `h3` using `H _ hσ`. Rewrite `h3` using `[ht.tval_ineConj hl, deg_inv, zpow_neg]`. Establish `h4` using `semiconj_exp (x := (r g : Matrix n n (Qbar l))) (h1.smul ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ * tval t σ)) (hMn.smul ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ * tval t σ)) (by rw [mul_smul_comm, smul_mul_assoc, hM'])`. Rewrite `h4` using `[← h3, ← Units.val_mul, ← map_mul]`.

Rewrite using `[smul_smul, mul_comm (tval t σ), ← Units.mul_left_inj (r g), ← h4, ← Units.val_mul, ← map_mul]`. Simplify using `[← mul_assoc]`. Rewrite using `[hM', ← smul_mul_assoc]`. Use `congr 1`. Rewrite using `[hN.unique ht h2, smul_inv_smul₀ hq]`.
-/
theorem IsMonodromy.comm (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (g : Weil h) :
    (r g : Matrix n n (Qbar l)) * N = ((normV w : ℕ) : Qbar l) ^ deg g • (N * r g) := by
  have hq : ((normV w : ℕ) : Qbar l) ^ deg g ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
  set M : Matrix n n (Qbar l) := (r g).val * N * (r g)⁻¹.val with hM
  have hM' : (r g : Matrix n n (Qbar l)) * N = M * r g := by rw [hM, Units.inv_mul_cancel_right]
  have hMn : IsNilpotent M := by
    obtain ⟨k, hk⟩ := hN.1
    exact ⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩
  have h2 : IsMonodromy t r ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ • M) := by
    obtain ⟨h1, U, hU, H⟩ := hN
    refine .of_nhds (hMn.smul _) ?_
    have h0 : ineConj g⁻¹ (1 : Ine (F := E) A) = 1 := Subtype.ext (by simp)
    filter_upwards [(hU.preimage (continuous_ineConj g⁻¹)).mem_nhds
      (show ineConj g⁻¹ 1 ∈ U by rw [h0]; exact U.one_mem)] with σ hσ
    have h3 := H _ hσ
    rw [ht.tval_ineConj hl, deg_inv, zpow_neg] at h3
    have h4 := semiconj_exp (x := (r g : Matrix n n (Qbar l)))
      (h1.smul ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ * tval t σ))
      (hMn.smul ((((normV w : ℕ) : Qbar l) ^ deg g)⁻¹ * tval t σ))
      (by rw [mul_smul_comm, smul_mul_assoc, hM'])
    rw [← h3, ← Units.val_mul, ← map_mul] at h4
    rw [smul_smul, mul_comm (tval t σ), ← Units.mul_left_inj (r g), ← h4, ← Units.val_mul,
      ← map_mul]
    simp [← mul_assoc]
  rw [hM', ← smul_mul_assoc]
  congr 1
  rw [hN.unique ht h2, smul_inv_smul₀ hq]

/- English proof (translation)
The claim follows from `semiconj_exp (hN.1.smul _) (hN.1.smul _) (by rw [mul_smul_comm, hN.comm hl ht, smul_mul_assoc, smul_smul, mul_comm])`.
-/
theorem IsMonodromy.mul_exp (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (g : Weil h) (s : Qbar l) :
    (r g : Matrix n n (Qbar l)) * exp (s • N) =
      exp ((((normV w : ℕ) : Qbar l) ^ deg g * s) • N) * r g :=
  semiconj_exp (hN.1.smul _) (hN.1.smul _) (by
    rw [mul_smul_comm, hN.comm hl ht, smul_mul_assoc, smul_smul, mul_comm])

/- English proof (translation)
Rewrite using `[inePart_mul, tval_mul, ht.tval_ineConj hl]`. Simplify using `[hφ]`.
-/
theorem IsTameChar.tval_inePart_mul (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hφ : deg φ = 1) (g g' : Weil h) :
    tval t (inePart hφ (g * g')) = (((normV w : ℕ) : Qbar l) ^ deg g')⁻¹ * tval t (inePart hφ g) +
      tval t (inePart hφ g') := by
  rw [inePart_mul, tval_mul, ht.tval_ineConj hl]
  simp [hφ]

/- English proof (translation)
Rewrite using `[wdMat, inePart_zpow_mul]`. Both sides reduce to the same expression.
-/
theorem wdMat_zpow_mul (hφ : deg φ = 1) (k : ℤ) (σ : Ine (F := E) A) :
    wdMat t hφ r N (φ ^ k * ineIncl h σ) =
      (r ((φ : G E Ω) ^ k * σ) : Matrix n n (Qbar l)) * exp ((-tval t σ) • N) := by
  rw [wdMat, inePart_zpow_mul]; rfl

/- English proof (translation)
Rewrite using `[wdMat, inePart_ineIncl]`. Both sides reduce to the same expression.
-/
theorem wdMat_ineIncl (hφ : deg φ = 1) (σ : Ine (F := E) A) :
    wdMat t hφ r N (ineIncl h σ) = (r σ : Matrix n n (Qbar l)) * exp ((-tval t σ) • N) := by
  rw [wdMat, inePart_ineIncl]; rfl

/- English proof (translation)
Simplify using `[wdMat]`.
-/
@[simp] theorem wdMat_zero (hφ : deg φ = 1) (g : Weil h) :
    wdMat t hφ r 0 g = (r g : Matrix n n (Qbar l)) := by simp [wdMat]

/- English proof (translation)
Simplify using `using wdMat_ineIncl (t := t) (r := r) (N := N) hφ 1`.
-/
theorem wdMat_one (hφ : deg φ = 1) : wdMat t hφ r N 1 = 1 := by
  simpa using wdMat_ineIncl (t := t) (r := r) (N := N) hφ 1

/- English proof (translation)
Establish `hq : ((normV w : ℕ) : Qbar l) ^ deg g' ≠ 0` using `zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)`. Rewrite using `[wdMat, wdMat, wdMat, ht.tval_inePart_mul hl, neg_add, exp_add_smul hN.1, Subgroup.coe_mul, map_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc (r g' : Matrix n n (Qbar l)), hN.mul_exp hl ht, mul_neg, mul_inv_cancel_left₀ hq, mul_assoc]`.
-/
theorem IsMonodromy.wdMat_mul (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (g g' : Weil h) :
    wdMat t hφ r N (g * g') = wdMat t hφ r N g * wdMat t hφ r N g' := by
  have hq : ((normV w : ℕ) : Qbar l) ^ deg g' ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
  rw [wdMat, wdMat, wdMat, ht.tval_inePart_mul hl, neg_add, exp_add_smul hN.1, Subgroup.coe_mul,
    map_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc (r g' : Matrix n n (Qbar l)),
    hN.mul_exp hl ht, mul_neg, mul_inv_cancel_left₀ hq, mul_assoc]

/- English proof (translation)
Rewrite using `[wdMat, mul_assoc, exp_smul_mul hN.1, ← mul_assoc, hN.comm hl ht, smul_mul_assoc, mul_assoc]`.
-/
theorem IsMonodromy.wdMat_comm (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (g : Weil h) :
    wdMat t hφ r N g * N = ((normV w : ℕ) : Qbar l) ^ deg g • (N * wdMat t hφ r N g) := by
  rw [wdMat, mul_assoc, exp_smul_mul hN.1, ← mul_assoc, hN.comm hl ht, smul_mul_assoc, mul_assoc]

/- English proof (translation)
Use `set q : Qbar l := ((normV w : ℕ) : Qbar l) with hq`. Establish `hq0 : q ≠ 0` using `Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot`. Establish `hq1 : 1 - q⁻¹ ≠ 0`. Rewrite using `[sub_ne_zero, ne_comm, Ne, inv_eq_one]`. Conclude with `Nat.cast_ne_one.mpr (one_lt_normV w).ne'`.

Set `D : Weil h → Qbar l` to `fun g => tval t (inePart hφ' g) - tval t (inePart hφ g)`. Establish `hD : ∀ g g', D (g * g') = (q ^ deg g')⁻¹ * D g + D g'` using `fun g g' => by`. Simplify using `only [D, ht.tval_inePart_mul hl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : ∀ g, deg g = 0 → D g = 0` using `fun g hg => by`.

Establish `e : g = ineIncl h ⟨g, deg_eq_zero_iff.mp hg⟩` using `rfl`. Rewrite using `[e]`. Simplify using `[D]`. Establish `key : ∀ g, D g = (1 - (q ^ deg g)⁻¹) * (D φ / (1 - q⁻¹))` using `fun g => by`. Establish `h1` using `hD (φ * g) ((φ * g)⁻¹ * (g * φ))`.

Establish `h0 : deg ((φ * g)⁻¹ * (g * φ)) = 0` using `by simp only [deg_mul, deg_inv]; ring`. Rewrite `h1` using `[mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ, zpow_one, zpow_zero, inv_one, one_mul, add_zero]`. Rewrite using `[← mul_div_assoc, eq_div_iff hq1]`. Take the linear combination `-h1`. Use `⟨D φ / (1 - q⁻¹), fun g => ?_⟩` and prove the remaining obligations.

Establish `h2` using `hN.mul_exp hl ht g ((q ^ deg g)⁻¹ * (D φ / (1 - q⁻¹)))`. Rewrite `h2` using `[mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)]`. Rewrite using `[wdMat, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]`. Use `congr 3`. Use `key g` as an intermediate fact.

Simplify using `only [D] at this ⊢`. Take the linear combination `this`.
-/
theorem IsMonodromy.exists_conj (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (hφ' : deg φ' = 1) :
    ∃ b : Qbar l, ∀ g, exp (b • N) * wdMat t hφ r N g = wdMat t hφ' r N g * exp (b • N) := by
  set q : Qbar l := ((normV w : ℕ) : Qbar l) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq1 : 1 - q⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    exact Nat.cast_ne_one.mpr (one_lt_normV w).ne'
  let D : Weil h → Qbar l := fun g => tval t (inePart hφ' g) - tval t (inePart hφ g)
  have hD : ∀ g g', D (g * g') = (q ^ deg g')⁻¹ * D g + D g' := fun g g' => by
    simp only [D, ht.tval_inePart_mul hl]; ring
  have hD0 : ∀ g, deg g = 0 → D g = 0 := fun g hg => by
    have e : g = ineIncl h ⟨g, deg_eq_zero_iff.mp hg⟩ := rfl
    rw [e]; simp [D]
  have key : ∀ g, D g = (1 - (q ^ deg g)⁻¹) * (D φ / (1 - q⁻¹)) := fun g => by
    have h1 := hD (φ * g) ((φ * g)⁻¹ * (g * φ))
    have h0 : deg ((φ * g)⁻¹ * (g * φ)) = 0 := by simp only [deg_mul, deg_inv]; ring
    rw [mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ, zpow_one, zpow_zero, inv_one, one_mul,
      add_zero] at h1
    rw [← mul_div_assoc, eq_div_iff hq1]
    linear_combination -h1
  refine ⟨D φ / (1 - q⁻¹), fun g => ?_⟩
  have h2 := hN.mul_exp hl ht g ((q ^ deg g)⁻¹ * (D φ / (1 - q⁻¹)))
  rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)] at h2
  rw [wdMat, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1,
    ← exp_add_smul hN.1]
  congr 3
  have := key g
  simp only [D] at this ⊢
  linear_combination this

/- English proof (translation)
Use `set q : Qbar l := ((normV w : ℕ) : Qbar l) with hq`. Use `set s := -tval t (inePart hφ g)`. Establish `h2` using `hN.mul_exp hl ht g`. Distinguish the cases in `hg : deg g = 0`. Establish `hc : Commute (r g : Matrix n n (Qbar l)) (exp (s • N))`.

Use `h2 s` as an intermediate fact. Rewrite `this` using `[hg, zpow_zero, one_mul]`. Then use the resulting hypothesis. Use `charpoly_eq_of_isNilpotent_sub (f := Matrix.toLinAlgEquiv' (r g : Matrix n n (Qbar l))) (g := Matrix.toLinAlgEquiv' (wdMat t hφ r N g)) (((Commute.refl _).mul_right hc).map _) (by` as an intermediate fact. Rewrite using `[← map_sub, wdMat, ← mul_sub_one]`. Conclude with `((hc.sub_right (Commute.one_right _)).isNilpotent_mul_left (isNilpotent_exp_sub_one (hN.1.smul s))).map _)`.

Conclude with `((Matrix.charpoly_toLin' _).symm.trans this.symm).trans (Matrix.charpoly_toLin' _)`. Establish `hq1 : 1 - q ^ deg g ≠ 0`. Rewrite using `[sub_ne_zero, ne_comm]`. Introduce `h1`. Establish `h3 : (((normV w : ℕ) : ℚ) ^ deg g : ℚ) = 1`.

Rewrite using `[← Rat.cast_inj (α := Qbar l)]`. Use `push_cast`. Conclude with `h1`. Conclude with `hg ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _) (Nat.cast_ne_one.mpr (one_lt_normV w).ne')).mp h3)`. Establish `e : s = s / (1 - q ^ deg g) + -(q ^ deg g * (s / (1 - q ^ deg g)))` using `by field_simp; ring`.

Rewrite using `[wdMat]`. Express the relevant statement in the definitionally equal form `(_ * exp (s • N)).charpoly = _`. Rewrite using `[e]`. Generalize the expression as in `s / (1 - q ^ deg g) = b`. Rewrite using `[exp_add_smul hN.1, ← mul_assoc, h2, Matrix.charpoly_mul_comm, ← mul_assoc, ← exp_add_smul hN.1]`.

Simplify using `[← hq]`.
-/
theorem IsMonodromy.charpoly_wdMat (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (g : Weil h) :
    (wdMat t hφ r N g).charpoly = (r g : Matrix n n (Qbar l)).charpoly := by
  set q : Qbar l := ((normV w : ℕ) : Qbar l) with hq
  set s := -tval t (inePart hφ g)
  have h2 := hN.mul_exp hl ht g
  by_cases hg : deg g = 0
  · have hc : Commute (r g : Matrix n n (Qbar l)) (exp (s • N)) := by
      have := h2 s
      rwa [hg, zpow_zero, one_mul] at this
    have := charpoly_eq_of_isNilpotent_sub
      (f := Matrix.toLinAlgEquiv' (r g : Matrix n n (Qbar l)))
      (g := Matrix.toLinAlgEquiv' (wdMat t hφ r N g))
      (((Commute.refl _).mul_right hc).map _) (by
        rw [← map_sub, wdMat, ← mul_sub_one]
        exact ((hc.sub_right (Commute.one_right _)).isNilpotent_mul_left
          (isNilpotent_exp_sub_one (hN.1.smul s))).map _)
    exact ((Matrix.charpoly_toLin' _).symm.trans this.symm).trans (Matrix.charpoly_toLin' _)
  · have hq1 : 1 - q ^ deg g ≠ 0 := by
      rw [sub_ne_zero, ne_comm]
      intro h1
      have h3 : (((normV w : ℕ) : ℚ) ^ deg g : ℚ) = 1 := by
        rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
      exact hg ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
        (Nat.cast_ne_one.mpr (one_lt_normV w).ne')).mp h3)
    have e : s = s / (1 - q ^ deg g) + -(q ^ deg g * (s / (1 - q ^ deg g))) := by
      field_simp; ring
    rw [wdMat]
    change (_ * exp (s • N)).charpoly = _
    rw [e]
    generalize s / (1 - q ^ deg g) = b
    rw [exp_add_smul hN.1, ← mul_assoc, h2, Matrix.charpoly_mul_comm, ← mul_assoc,
      ← exp_add_smul hN.1]
    simp [← hq]

def IsMonodromy.rep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (ι : Qbar l ≃+* ℂ) :
    Representation ℂ (Weil h) (n → ℂ) where
  toFun g := toEndC ι (wdMat t hφ r N g)
  map_one' := by rw [wdMat_one, map_one]
  map_mul' g g' := by rw [hN.wdMat_mul hl ht, map_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem IsMonodromy.rep_apply (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (ι : Qbar l ≃+* ℂ) (g : Weil h) :
    hN.rep hl ht hφ ι g = toEndC ι (wdMat t hφ r N g) := rfl

/- English proof (translation)
Take `⟨U, hU, H⟩` from `hN.2`. Use `.of_open hU U.one_mem fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[hN.rep_apply, wdMat_ineIncl, H σ hσ, ← exp_add_smul hN.1]`. Simplify using the standard rewrite rules.
-/
theorem IsMonodromy.isSmooth_rep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (ι : Qbar l ≃+* ℂ) :
    IsSmooth (hN.rep hl ht hφ ι) := by
  obtain ⟨U, hU, H⟩ := hN.2
  refine .of_open hU U.one_mem fun σ hσ => ?_
  rw [hN.rep_apply, wdMat_ineIncl, H σ hσ, ← exp_add_smul hN.1]
  simp

/- English proof (translation)
Rewrite using `[hN.rep_apply, ← map_mul, hN.wdMat_comm hl ht, toEndC_smul, map_mul, map_zpow₀, map_natCast]`.
-/
theorem IsMonodromy.rep_comm (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ht : IsTameChar t)
    (hN : IsMonodromy t r N) (hφ : deg φ = 1) (ι : Qbar l ≃+* ℂ) (g : Weil h) :
    hN.rep hl ht hφ ι g * toEndC ι N =
      ((normV w : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN.rep hl ht hφ ι g) := by
  rw [hN.rep_apply, ← map_mul, hN.wdMat_comm hl ht, toEndC_smul, map_mul, map_zpow₀, map_natCast]

end Monodromy

def IsWDOfWith (t : Ine (F := E) A →* Multiplicative ℤ_[l]) {φ : Weil h} (hφ : deg φ = 1)
    (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) (x : WD h) : Prop :=
  ∃ (N : Matrix n n (Qbar l)) (a : WDRep h (n → ℂ)), IsMonodromy t r N ∧
    IsFrobSS (fun g => toEndC ι (wdMat t hφ r N g)) (toEndC ι N) a ∧ WD.mk a = x

def IsWDOf (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) (x : WD h) : Prop :=
  ∃ t : Ine (F := E) A →* Multiplicative ℤ_[l], IsTameChar t ∧
    ∃ (φ : Weil h) (hφ : deg φ = 1), IsWDOfWith t hφ ι r x

variable (h) in
open Classical in

def wdOf (_hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) :
    WD h :=
  if H : ∃ x : WD h, IsWDOf ι r x then H.choose else WD.mk (WDRep.diag h fun _ : n => 1)

section Param

variable {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {r : G E Ω →* GL n (Qbar l)}
  {N : Matrix n n (Qbar l)} {φ : Weil h} {ι : Qbar l ≃+* ℂ}
  (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)

include hl in

/- English proof (translation)
The claim follows from `WeilDeligne.exists_isFrobSS (hN.rep hl ht hφ ι) _ (hN.isSmooth_rep hl ht hφ ι) (hN.1.map _) (hN.rep_comm hl ht hφ ι)`.
-/
theorem IsMonodromy.exists_isFrobSS (ht : IsTameChar t) (hN : IsMonodromy t r N) (hφ : deg φ = 1)
    (ι : Qbar l ≃+* ℂ) : ∃ a : WDRep h (n → ℂ),
      IsFrobSS (fun g => toEndC ι (wdMat t hφ r N g)) (toEndC ι N) a :=
  WeilDeligne.exists_isFrobSS (hN.rep hl ht hφ ι) _ (hN.isSmooth_rep hl ht hφ ι) (hN.1.map _)
    (hN.rep_comm hl ht hφ ι)

include hl in

/- English proof (translation)
Take `⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩` from `hx`. Take `⟨t', ht', φ', hφ', N', b, hN', hb, rfl⟩` from `hy`. Take `⟨c, hc0, hc⟩` from `ht.exists_mul h hl ht'`. Take `rfl : N' = c • N` from `hN'.unique ht' (hN.smul hc)`. Take `⟨a', ha'⟩` from `hN.exists_isFrobSS hl ht hφ' ι`.

Take `⟨s, hs⟩` from `hN.exists_conj hl ht hφ hφ'`. Take `⟨u, hu⟩` from `(isUnit_exp (hN.1.smul s)).map (toEndC ι)`. Establish `h1 : a.Iso a'` using `ha.iso ha' (LinearMap.GeneralLinearGroup.toLinearEquiv u) (fun g v => by show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N g)) v = (toEndC ι (wdMat t hφ' r N g) * (u : End ℂ (n → ℂ))) v`. Rewrite using `[hu, ← map_mul, hs, map_mul])`. Use the proof step `(fun v => by show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v`.

Rewrite using `[hu, ← map_mul, exp_smul_mul hN.1, map_mul])`. Establish `e : ∀ g, wdMat t' hφ' r (c • N) g = wdMat t hφ' r N g` using `fun g => by`. Rewrite using `[wdMat, wdMat, hc, smul_smul, neg_mul, mul_comm c]`. Simplify using `only [e, toEndC_smul] at hb`. Conclude with `WD.sound (h1.trans (ha'.iso_of_smul ((map_ne_zero ι).mpr hc0) hb))`.
-/
theorem IsWDOf.unique {x y : WD h} (hx : IsWDOf ι r x) (hy : IsWDOf ι r y) : x = y := by
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx
  obtain ⟨t', ht', φ', hφ', N', b, hN', hb, rfl⟩ := hy
  obtain ⟨c, hc0, hc⟩ := ht.exists_mul h hl ht'
  obtain rfl : N' = c • N := hN'.unique ht' (hN.smul hc)
  obtain ⟨a', ha'⟩ := hN.exists_isFrobSS hl ht hφ' ι
  obtain ⟨s, hs⟩ := hN.exists_conj hl ht hφ hφ'
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul s)).map (toEndC ι)
  have h1 : a.Iso a' := ha.iso ha' (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N g)) v =
        (toEndC ι (wdMat t hφ' r N g) * (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, hs, map_mul])
    (fun v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have e : ∀ g, wdMat t' hφ' r (c • N) g = wdMat t hφ' r N g := fun g => by
    rw [wdMat, wdMat, hc, smul_smul, neg_mul, mul_comm c]
  simp only [e, toEndC_smul] at hb
  exact WD.sound (h1.trans (ha'.iso_of_smul ((map_ne_zero ι).mpr hc0) hb))

/- English proof (translation)
Rewrite using `[wdOf, dif_pos ⟨x, hx⟩]`. Conclude with `(Exists.choose_spec (⟨x, hx⟩ : ∃ x : WD h, IsWDOf ι r x)).unique hl hx`.
-/
theorem IsWDOf.wdOf_eq {x : WD h} (hx : IsWDOf ι r x) : wdOf h hl ι r = x := by
  rw [wdOf, dif_pos ⟨x, hx⟩]
  exact (Exists.choose_spec (⟨x, hx⟩ : ∃ x : WD h, IsWDOf ι r x)).unique hl hx

include hl in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, t', ht', φ, hφ, N, a, hN, -⟩`. Take `⟨c, -, hc⟩` from `ht'.exists_mul h hl ht`. Conclude with `⟨_, hN.smul hc⟩`. Introduce and unpack `⟨N, hN⟩`.

Take `⟨a, ha⟩` from `hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι`. Conclude with `⟨_, t, ht, _, deg_frob, N, a, hN, ha, rfl⟩`.
-/
theorem exists_isWDOf_iff (ht : IsTameChar t) :
    (∃ x : WD h, IsWDOf ι r x) ↔ ∃ N, IsMonodromy t r N := by
  constructor
  · rintro ⟨x, t', ht', φ, hφ, N, a, hN, -⟩
    obtain ⟨c, -, hc⟩ := ht'.exists_mul h hl ht
    exact ⟨_, hN.smul hc⟩
  · rintro ⟨N, hN⟩
    obtain ⟨a, ha⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
    exact ⟨_, t, ht, _, deg_frob, N, a, hN, ha, rfl⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hN.exists_isFrobSS hl ht hφ ι`. Conclude with `⟨a, ha, IsWDOf.wdOf_eq hl ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩⟩`.
-/
theorem IsMonodromy.wdOf_spec (ht : IsTameChar t) (hN : IsMonodromy t r N) (hφ : deg φ = 1)
    (ι : Qbar l ≃+* ℂ) : ∃ a : WDRep h (n → ℂ),
      IsFrobSS (hN.rep hl ht hφ ι) (toEndC ι N) a ∧ wdOf h hl ι r = WD.mk a := by
  obtain ⟨a, ha⟩ := hN.exists_isFrobSS hl ht hφ ι
  exact ⟨a, ha, IsWDOf.wdOf_eq hl ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩⟩

/- English proof (translation)
The claim follows from `dif_neg H`.
-/
theorem wdOf_of_not (H : ¬ ∃ x : WD h, IsWDOf ι r x) :
    wdOf h hl ι r = WD.mk (WDRep.diag h fun _ : n => 1) := dif_neg H

/- English proof (translation)
Distinguish the cases in `H : ∃ x : WD h, IsWDOf ι r x`. Take `⟨x, hx⟩` from `H`. Rewrite using `[hx.wdOf_eq hl]`. Take `⟨-, -, -, -, -, a, -, -, rfl⟩` from `hx`. Simplify using the standard rewrite rules.

Simplify using `[wdOf_of_not hl H]`.
-/
theorem lpDim_wdOf (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) :
    (wdOf h hl ι r).lpDim = Fintype.card n := by
  by_cases H : ∃ x : WD h, IsWDOf ι r x
  · obtain ⟨x, hx⟩ := H
    rw [hx.wdOf_eq hl]
    obtain ⟨-, -, -, -, -, a, -, -, rfl⟩ := hx
    simp
  · simp [wdOf_of_not hl H]

/- English proof (translation)
Take `⟨a, ha, e⟩` from `hN.wdOf_spec hl ht (deg_frob (h := h)) ι`. Rewrite using `[e, WD.charPol_mk, ha.charpoly_eq, hN.rep_apply, charpoly_toEndC, hN.charpoly_wdMat hl ht]`.
-/
theorem IsMonodromy.charPol_wdOf (ht : IsTameChar t) (hN : IsMonodromy t r N) (ι : Qbar l ≃+* ℂ)
    (g : Weil h) : (wdOf h hl ι r).charPol g =
      (r g : Matrix n n (Qbar l)).charpoly.map ι.toRingHom := by
  obtain ⟨a, ha, e⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [e, WD.charPol_mk, ha.charpoly_eq, hN.rep_apply, charpoly_toEndC, hN.charpoly_wdMat hl ht]

/- English proof (translation)
Take `⟨a, ha, e⟩` from `hN.wdOf_spec hl ht (deg_frob (h := h)) ι`. Rewrite using `[e, WD.monodromyZero_ofWeilDeligneRepClass_iff, ha.1, map_eq_zero_iff _ (toEndC_injective ι)]`.
-/
theorem IsMonodromy.weilDeligneParam_monodromy_eq_zero_iff (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (ι : Qbar l ≃+* ℂ) : (wdOf h hl ι r).mono0 ↔ N = 0 := by
  obtain ⟨a, ha, e⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [e, WD.monodromyZero_ofWeilDeligneRepClass_iff, ha.1, map_eq_zero_iff _ (toEndC_injective ι)]

/- English proof (translation)
Take `⟨a, ha, e⟩` from `hN.wdOf_spec hl ht (deg_frob (h := h)) ι`. Establish `key : N = 0 → ∀ σ : Ine (F` using `E) A, a.ρ (ineIncl h σ) = 1 ↔ r σ = 1 := by`. Introduce and unpack `rfl σ`. Rewrite using `[ha.ρ_ineIncl (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, map_eq_one_iff _ (toEndC_injective ι), Units.val_eq_one, coe_ineIncl]`. Rewrite using `[e, WD.unr_mk, WDRep.Unr, ha.1, map_eq_zero_iff _ (toEndC_injective ι)]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun H σ hσ => (key H.1 ⟨σ, hσ⟩).mp (H.2 _)`. Introduce `H`. Establish `h0 : N = 0` using `hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => H σ σ.2))`. Conclude with `⟨h0, fun σ => (key h0 σ).mpr (H σ σ.2)⟩`.
-/
theorem IsMonodromy.unr_wdOf_iff (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (ι : Qbar l ≃+* ℂ) : (wdOf h hl ι r).unr ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1 := by
  obtain ⟨a, ha, e⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  have key : N = 0 → ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) = 1 ↔ r σ = 1 := by
    rintro rfl σ
    rw [ha.ρ_ineIncl (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero,
      map_eq_one_iff _ (toEndC_injective ι), Units.val_eq_one, coe_ineIncl]
  rw [e, WD.unr_mk, WDRep.Unr, ha.1, map_eq_zero_iff _ (toEndC_injective ι)]
  constructor
  · exact fun H σ hσ => (key H.1 ⟨σ, hσ⟩).mp (H.2 _)
  · intro H
    have h0 : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr
      (.of_trivial fun σ => H σ σ.2))
    exact ⟨h0, fun σ => (key h0 σ).mpr (H σ σ.2)⟩

/- English proof (translation)
Use `IsWDOf.wdOf_eq hl ⟨_, isTameChar_tameL h hl, _, deg_frob, 0, a, (isMonodromy_zero_iff (h := h)).mpr (a.smooth.of_le fun g hg => ?_), ?_, rfl⟩` and prove the remaining obligations. Conclude with `Units.val_eq_one.mp ((map_eq_one_iff _ (toEndC_injective ι)).mp ((hr g).trans hg))`. Simplify using `only [wdMat_zero, hr, map_zero, ← ha]`. Conclude with `isFrobSS_self a`.
-/
theorem wdOf_eq_mk (a : WDRep h (n → ℂ)) (ha : a.N = 0)
    (hr : ∀ g : Weil h, toEndC ι (r g : Matrix n n (Qbar l)) = a.ρ g) :
    wdOf h hl ι r = WD.mk a := by
  refine IsWDOf.wdOf_eq hl ⟨_, isTameChar_tameL h hl, _, deg_frob, 0, a,
    (isMonodromy_zero_iff (h := h)).mpr (a.smooth.of_le fun g hg => ?_), ?_, rfl⟩
  · exact Units.val_eq_one.mp ((map_eq_one_iff _ (toEndC_injective ι)).mp ((hr g).trans hg))
  · simp only [wdMat_zero, hr, map_zero, ← ha]
    exact isFrobSS_self a

include hl in

/- English proof (translation)
Take `⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩` from `hx`. Use `set M : Matrix n n (Qbar l) := P.val * N * P⁻¹.val with hM`. Establish `hM' : P.val * N = M * P.val` using `by rw [hM, Units.inv_mul_cancel_right]`. Establish `hMn : IsNilpotent M`. Take `⟨k, hk⟩` from `hN.1`.

Conclude with `⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩`. Establish `he : ∀ s : Qbar l, P.val * exp (s • N) = exp (s • M) * P.val` using `fun s => semiconj_exp (hN.1.smul s) (hMn.smul s) (by rw [mul_smul_comm, smul_mul_assoc, hM'])`. Establish `hP' : ∀ g : Weil h, P.val * (r g).val = (r' g).val * P.val` using `fun g => congrArg Units.val (hP g)`. Establish `hN' : IsMonodromy t r' M`. Take `⟨U, hU, H⟩` from `hN.2`.

Use `⟨hMn, U, hU, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.mul_left_inj P, ← he, ← H σ hσ]`. Conclude with `(hP' (ineIncl h σ)).symm`. Take `⟨b, hb⟩` from `hN'.exists_isFrobSS hl ht hφ ι`. Take `⟨u, hu⟩` from `P.isUnit.map (toEndC ι)`.

Use `⟨t, ht, φ, hφ, M, b, hN', hb, WD.sound (WDRep.Iso.symm (ha.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u) (fun g v => ?_) fun v => ?_))⟩` and prove the remaining obligations. Use `show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N g)) v = (toEndC ι (wdMat t hφ r' M g) * (u : End ℂ (n → ℂ))) v`. Rewrite using `[hu, ← map_mul, ← map_mul, wdMat, wdMat, ← mul_assoc, hP', mul_assoc, he, mul_assoc]`. Use `show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι M * (u : End ℂ (n → ℂ))) v`. Rewrite using `[hu, ← map_mul, hM', map_mul]`.
-/
theorem IsWDOf.of_conj {r' : G E Ω →* GL n (Qbar l)} (P : GL n (Qbar l))
    (hP : ∀ g : Weil h, P * r g = r' g * P) {x : WD h} (hx : IsWDOf ι r x) : IsWDOf ι r' x := by
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx
  set M : Matrix n n (Qbar l) := P.val * N * P⁻¹.val with hM
  have hM' : P.val * N = M * P.val := by rw [hM, Units.inv_mul_cancel_right]
  have hMn : IsNilpotent M := by
    obtain ⟨k, hk⟩ := hN.1
    exact ⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩
  have he : ∀ s : Qbar l, P.val * exp (s • N) = exp (s • M) * P.val := fun s =>
    semiconj_exp (hN.1.smul s) (hMn.smul s) (by rw [mul_smul_comm, smul_mul_assoc, hM'])
  have hP' : ∀ g : Weil h, P.val * (r g).val = (r' g).val * P.val := fun g =>
    congrArg Units.val (hP g)
  have hN' : IsMonodromy t r' M := by
    obtain ⟨U, hU, H⟩ := hN.2
    refine ⟨hMn, U, hU, fun σ hσ => ?_⟩
    rw [← Units.mul_left_inj P, ← he, ← H σ hσ]
    exact (hP' (ineIncl h σ)).symm
  obtain ⟨b, hb⟩ := hN'.exists_isFrobSS hl ht hφ ι
  obtain ⟨u, hu⟩ := P.isUnit.map (toEndC ι)
  refine ⟨t, ht, φ, hφ, M, b, hN', hb, WD.sound (WDRep.Iso.symm
    (ha.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u) (fun g v => ?_) fun v => ?_))⟩
  · show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N g)) v =
      (toEndC ι (wdMat t hφ r' M g) * (u : End ℂ (n → ℂ))) v
    rw [hu, ← map_mul, ← map_mul, wdMat, wdMat, ← mul_assoc, hP', mul_assoc, he, mul_assoc]
  · show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι M * (u : End ℂ (n → ℂ))) v
    rw [hu, ← map_mul, hM', map_mul]

/- English proof (translation)
Distinguish the cases in `H : ∃ x : WD h, IsWDOf ι r x`. Take `⟨x, hx⟩` from `H`. Rewrite using `[hx.wdOf_eq hl, (hx.of_conj hl P hP).wdOf_eq hl]`. Rewrite using `[wdOf_of_not hl H, wdOf_of_not hl]`. Introduce and unpack `⟨x, hx⟩`.

Conclude with `H ⟨x, hx.of_conj hl P⁻¹ fun g => by`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, hP, mul_inv_cancel_right]⟩`.
-/
theorem wdOf_eq_of_conj {r' : G E Ω →* GL n (Qbar l)} (P : GL n (Qbar l))
    (hP : ∀ g : Weil h, P * r g = r' g * P) : wdOf h hl ι r = wdOf h hl ι r' := by
  by_cases H : ∃ x : WD h, IsWDOf ι r x
  · obtain ⟨x, hx⟩ := H
    rw [hx.wdOf_eq hl, (hx.of_conj hl P hP).wdOf_eq hl]
  · rw [wdOf_of_not hl H, wdOf_of_not hl]
    rintro ⟨x, hx⟩
    exact H ⟨x, hx.of_conj hl P⁻¹ fun g => by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hP, mul_inv_cancel_right]⟩

end Param

section Examples

variable (l) in

def kummerRep (a : Eˣ) : G E Ω →* GL (Fin 2) (Qbar l) :=
  MonoidHom.toHomUnits
    { toFun := fun σ => !![algebraMap ℚ_[l] (Qbar l) ((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]),
        algebraMap ℚ_[l] (Qbar l) (kummer l a σ); 0, 1]
      map_one' := by simp [Matrix.one_fin_two]
      map_mul' := fun σ τ => by
        simp [kummer_mul, add_comm]
        simp [Algebra.smul_def] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_kummerRep (a : Eˣ) (σ : G E Ω) :
    (kummerRep l a σ : Matrix (Fin 2) (Fin 2) (Qbar l)) =
      !![algebraMap ℚ_[l] (Qbar l) ((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]),
        algebraMap ℚ_[l] (Qbar l) (kummer l a σ); 0, 1] := rfl

/- English proof (translation)
Establish `h1 : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])` using `(continuous_algebraMap _ _).comp continuous_subtype_val`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1.comp (Units.continuous_val.comp (continuous_cycZ E Ω l))`. Conclude with `h1.comp (continuous_kummer l a)`.

Conclude with `continuous_const`. Conclude with `continuous_const`.
-/
theorem continuous_kummerRep (a : Eˣ) :
    Continuous fun σ : G E Ω => (kummerRep l a σ : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
  have h1 : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    (continuous_algebraMap _ _).comp continuous_subtype_val
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h1.comp (Units.continuous_val.comp (continuous_cycZ E Ω l))
  · exact h1.comp (continuous_kummer l a)
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Use `⟨⟨2, by simp [pow_two, ← Matrix.ext_iff]⟩, ⊤, isOpen_univ, fun σ _ => ?_⟩` and prove the remaining obligations. Rewrite using `[exp_eq_sum (k := 2) (by simp [pow_two, ← Matrix.ext_iff]), coe_kummerRep, cycZ_of_mem_Ine h hl σ.2]`. Simplify using `[Finset.sum_range_succ, Matrix.one_fin_two, tval, tameL]`. Simplify using `[Algebra.smul_def]`.
-/
theorem isMonodromy_kummerRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) :
    IsMonodromy (tameL h hl) (kummerRep l (unifUnit w)) !![0, 1; 0, 0] := by
  refine ⟨⟨2, by simp [pow_two, ← Matrix.ext_iff]⟩, ⊤, isOpen_univ, fun σ _ => ?_⟩
  rw [exp_eq_sum (k := 2) (by simp [pow_two, ← Matrix.ext_iff]), coe_kummerRep,
    cycZ_of_mem_Ine h hl σ.2]
  simp [Finset.sum_range_succ, Matrix.one_fin_two, tval, tameL]
  simp [Algebra.smul_def]

/- English proof (translation)
Use `⟨by simp [lpDim_wdOf], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(isMonodromy_kummerRep hl).weilDeligneParam_monodromy_eq_zero_iff hl (isTameChar_tameL h hl)]`. Simplify using `[← Matrix.ext_iff]`. Rewrite using `[(isMonodromy_kummerRep hl).charPol_wdOf hl (isTameChar_tameL h hl), coe_kummerRep, cycZ_of_isFrob hl h isFrob_frob, Matrix.charpoly_fin_two]`. Simplify using `[Matrix.det_fin_two]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wdOf_kummerRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) :
    (wdOf h hl ι (kummerRep l (unifUnit w))).lpDim = 2 ∧
      ¬ (wdOf h hl ι (kummerRep l (unifUnit w))).mono0 ∧
      (wdOf h hl ι (kummerRep l (unifUnit w))).charPol (frob h) =
        (X - C ((normV w : ℕ) : ℂ)) * (X - 1) := by
  refine ⟨by simp [lpDim_wdOf], ?_, ?_⟩
  · rw [(isMonodromy_kummerRep hl).weilDeligneParam_monodromy_eq_zero_iff hl (isTameChar_tameL h hl)]
    simp [← Matrix.ext_iff]
  · rw [(isMonodromy_kummerRep hl).charPol_wdOf hl (isTameChar_tameL h hl), coe_kummerRep,
      cycZ_of_isFrob hl h isFrob_frob, Matrix.charpoly_fin_two]
    simp [Matrix.det_fin_two]
    ring

/- English proof (translation)
Rewrite using `[WD.lpTw_mk]`. Use `wdOf_eq_mk hl _ rfl fun g => ?_` and prove the remaining obligations. Establish `e : ((cyc E Ω l g : (Qbar l)ˣ) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg g`. Use `congrArg (algebraMap ℚ_[l] (Qbar l)) (cycZ_weil hl g)` as an intermediate fact. Rewrite `this` using `[map_zpow₀, map_natCast]`.

Conclude with `this`. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[toEndC_apply, e, Matrix.mulVec, dotProduct]`.
-/
theorem wdOf_cyc (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) :
    wdOf h hl ι ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l)) =
      (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)).lpTw 1 := by
  rw [WD.lpTw_mk]
  refine wdOf_eq_mk hl _ rfl fun g => ?_
  have e : ((cyc E Ω l g : (Qbar l)ˣ) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg g := by
    have := congrArg (algebraMap ℚ_[l] (Qbar l)) (cycZ_weil hl g)
    rw [map_zpow₀, map_natCast] at this
    exact this
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Subsingleton.elim i 0]
  simp [toEndC_apply, e, Matrix.mulVec, dotProduct]

/- English proof (translation)
The claim follows from `wdOf_eq_mk hl _ rfl fun g => LinearMap.ext fun v => funext fun i => by simp`.
-/
example (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) :
    wdOf h hl ι (1 : G E Ω →* GL n (Qbar l)) = WD.mk (WDRep.diag h fun _ : n => 1) :=
  wdOf_eq_mk hl _ rfl fun g => LinearMap.ext fun v => funext fun i => by simp

end Examples

end GlobalTheory.WeilDeligne
