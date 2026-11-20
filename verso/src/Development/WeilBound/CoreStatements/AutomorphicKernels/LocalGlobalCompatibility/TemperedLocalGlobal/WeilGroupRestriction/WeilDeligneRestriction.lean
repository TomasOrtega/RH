import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
open GlobalTheory.WeilDeligne PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilDeligneRestriction

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω}

/- English proof (translation)
Establish `h1 : resG E σ • A = A` using `hσ`. Use `show σ • A = A`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Use `conv_rhs => rw [← h1]`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem mem_Dec_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Dec (F := E) A) : σ ∈ Dec (F := E') A := by
  have h1 : resG E σ • A = A := hσ
  show σ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_Dec_of_resG hσ.1, fun x hx => hσ.2 x hx⟩`.
-/
theorem mem_Ine_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Ine (F := E) A) : σ ∈ Ine (F := E') A :=
  ⟨mem_Dec_of_resG hσ.1, fun x hx => hσ.2 x hx⟩

variable (E A) in

def resIne : Ine (F := E') A →* Ine (F := E) A where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_resIne (σ : Ine (F := E') A) : ((resIne E A σ : Ine (F := E) A) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

/- English proof (translation)
Use `show Continuous fun σ : Ine (F := E') A => (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : Ine (F := E) A)`. Conclude with `((continuous_resG (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val).subtype_mk _`.
-/
theorem continuous_resIne : Continuous (resIne E A : Ine (F := E') A → Ine (F := E) A) := by
  show Continuous fun σ : Ine (F := E') A => (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : Ine (F := E) A)
  exact ((continuous_resG (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val).subtype_mk _

/- English proof (translation)
Set `bQ` to `Module.finBasis ℚ E'`. Set `K : IntermediateField E Ω` to `IntermediateField.adjoin E (Set.range fun i => algebraMap E' Ω (bQ i))`. Establish `: Algebra.IsAlgebraic E Ω` using `IsAlgClosure.isAlgebraic`. Establish `: FiniteDimensional E K` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Set `U : Subgroup (Ine (F` to `E) A) := K.fixingSubgroup.comap (Ine (F := E) A).subtype`.

Establish `hU : IsOpen (U : Set (Ine (F` using `E) A)) := (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val`. Take `⟨σ, hσ, hne⟩` from `ht.exists_tval_ne_zero hU`. Establish `hσ' : (σ : G E Ω) ∈ K.fixingSubgroup` using `hσ`. Establish `hb : ∀ i, (σ : G E Ω) (algebraMap E' Ω (bQ i)) = algebraMap E' Ω (bQ i)` using `fun i => (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`. Establish `: CharZero Ω` using `(RingHom.charZero_iff (algebraMap E Ω).injective).mp inferInstance`.

Establish `hfix : ∀ y : E', (σ : G E Ω) (algebraMap E' Ω y) = algebraMap E' Ω y`. Introduce `y`. Rewrite using `[← bQ.sum_repr y, map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_rat_smul, map_rat_smul, hb]`. Set `τ : G E' Ω` to `{ (σ : G E Ω).toRingEquiv with commutes' := hfix }`.

Establish `hτ : resG E τ = (σ : G E Ω)` using `AlgEquiv.ext fun _ => rfl`. Establish `hτI : τ ∈ Ine (F` using `E') A := mem_Ine_of_resG (by rw [hτ]; exact σ.2)`. Use `⟨⟨τ, hτI⟩, ?_⟩` and prove the remaining obligations. Establish `e : resIne E A ⟨τ, hτI⟩ = σ` using `Subtype.ext hτ`. Rewrite using `[e]`.

Conclude with `hne`.
-/
theorem exists_tval_resIne_ne {l : ℕ} [Fact l.Prime] {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t) :
    ∃ σ : Ine (F := E') A, tval t (resIne E A σ) ≠ 0 := by
  classical
  let bQ := Module.finBasis ℚ E'
  let K : IntermediateField E Ω := IntermediateField.adjoin E (Set.range fun i => algebraMap E' Ω (bQ i))
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let U : Subgroup (Ine (F := E) A) := K.fixingSubgroup.comap (Ine (F := E) A).subtype
  have hU : IsOpen (U : Set (Ine (F := E) A)) :=
    (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val
  obtain ⟨σ, hσ, hne⟩ := ht.exists_tval_ne_zero hU
  have hσ' : (σ : G E Ω) ∈ K.fixingSubgroup := hσ
  have hb : ∀ i, (σ : G E Ω) (algebraMap E' Ω (bQ i)) = algebraMap E' Ω (bQ i) := fun i =>
    (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have : CharZero Ω := (RingHom.charZero_iff (algebraMap E Ω).injective).mp inferInstance
  have hfix : ∀ y : E', (σ : G E Ω) (algebraMap E' Ω y) = algebraMap E' Ω y := by
    intro y
    rw [← bQ.sum_repr y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_rat_smul, map_rat_smul, hb]
  let τ : G E' Ω := { (σ : G E Ω).toRingEquiv with commutes' := hfix }
  have hτ : resG E τ = (σ : G E Ω) := AlgEquiv.ext fun _ => rfl
  have hτI : τ ∈ Ine (F := E') A := mem_Ine_of_resG (by rw [hτ]; exact σ.2)
  refine ⟨⟨τ, hτI⟩, ?_⟩
  have e : resIne E A ⟨τ, hτI⟩ = σ := Subtype.ext hτ
  rw [e]
  exact hne

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

include h h' in

/- English proof (translation)
Introduce `H`. Apply `hl` to reduce the goal to its premises. Rewrite using `[← h]`. Use `(h' _).mpr H` as an intermediate fact. Simplify using `using this`.
-/
theorem notMem_of_place (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal := by
  intro H
  apply hl
  rw [← h]
  have := (h' _).mpr H
  simpa using this

/- English proof (translation)
Establish `hpow : ∀ g : Weil h', ((normV w : ℕ) : Qbar l) ^ deg (resW h h' g) = ((normV w' : ℕ) : Qbar l) ^ deg g` using `fun g => by rw [deg_resW, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow_resF h h']`. Establish `hq0 : ((normV w : ℕ) : Qbar l) ≠ 0` using `Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot`. Establish `hq1 : 1 - ((normV w' : ℕ) : Qbar l)⁻¹ ≠ 0`. Rewrite using `[sub_ne_zero, ne_comm, Ne, inv_eq_one]`. Conclude with `Nat.cast_ne_one.mpr (one_lt_normV w').ne'`.

Set `D : Weil h' → Qbar l` to `fun g => c' * tval t' (inePart hφ' g) - tval t (inePart hφ (resW h h' g))`. Establish `hD : ∀ g g', D (g * g') = (((normV w' : ℕ) : Qbar l) ^ deg g')⁻¹ * D g + D g'` using `fun g g' => by`. Simplify using `only [D, map_mul, ht'.tval_inePart_mul hl' hφ', ht.tval_inePart_mul hl hφ, hpow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : ∀ g, deg g = 0 → D g = 0` using `fun g hg => by`.

Establish `e : g = ineIncl h' ⟨g, deg_eq_zero_iff.mp hg⟩` using `rfl`. Establish `e2 : ∀ σ : Ine (F` using `E') A, resW h h' (ineIncl h' σ) = ineIncl h (resIne E A σ) := fun σ => Subtype.ext rfl`. Rewrite using `[e]`. Simplify using `only [D, e2, inePart_ineIncl, hct, sub_self]`. Take `⟨b, hb⟩ : ∃ b : Qbar l, b = D φ' / (1 - ((normV w' : ℕ) : Qbar l)⁻¹)` from `⟨_, rfl⟩`.

Establish `key : ∀ g, D g = (1 - (((normV w' : ℕ) : Qbar l) ^ deg g)⁻¹) * b` using `fun g => by`. Establish `h1` using `hD (φ' * g) ((φ' * g)⁻¹ * (g * φ'))`. Establish `h0 : deg ((φ' * g)⁻¹ * (g * φ')) = 0` using `by simp only [deg_mul, deg_inv]; ring`. Rewrite `h1` using `[mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ', zpow_one, zpow_zero, inv_one, one_mul, add_zero]`. Rewrite using `[hb, ← mul_div_assoc, eq_div_iff hq1]`.

Take the linear combination `-h1`. Use `⟨b, fun g => ?_⟩` and prove the remaining obligations. Establish `h2` using `hN.mul_exp hl ht (resW h h' g) ((((normV w : ℕ) : Qbar l) ^ deg (resW h h' g))⁻¹ * b)`. Rewrite `h2` using `[mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)]`. Establish `hw : wdMat t' hφ' (r.comp (resG E (E'` using `E') (Ω := Ω))) (c' • N) g = (r (resW h h' g) : Matrix n n (Qbar l)) * exp ((-(c' * tval t' (inePart hφ' g))) • N) := by`.

Rewrite using `[wdMat, smul_smul, show -tval t' (inePart hφ' g) * c' = -(c' * tval t' (inePart hφ' g)) by ring]`. Both sides reduce to the same expression. Rewrite using `[hw, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]`. Use `congr 3`. Establish `k` using `key g`.

Simplify using `only [D] at k`. Rewrite using `[hpow]`. Take the linear combination `k`.
-/
theorem exists_conj_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hl' : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {t' : Ine (F := E') A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') {r : G E Ω →* GL n (Qbar l)} {N : Matrix n n (Qbar l)}
    (hN : IsMonodromy t r N) {φ : Weil h} (hφ : deg φ = 1) {φ' : Weil h'} (hφ' : deg φ' = 1) {c' : Qbar l}
    (hct : ∀ σ, tval t (resIne E A σ) = c' * tval t' σ) :
    ∃ b : Qbar l, ∀ g, exp (b • N) * wdMat t hφ r N (resW h h' g) =
      wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g * exp (b • N) := by
  have hpow : ∀ g : Weil h', ((normV w : ℕ) : Qbar l) ^ deg (resW h h' g) = ((normV w' : ℕ) : Qbar l) ^ deg g :=
    fun g => by rw [deg_resW, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow_resF h h']
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq1 : 1 - ((normV w' : ℕ) : Qbar l)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    exact Nat.cast_ne_one.mpr (one_lt_normV w').ne'
  let D : Weil h' → Qbar l := fun g => c' * tval t' (inePart hφ' g) - tval t (inePart hφ (resW h h' g))
  have hD : ∀ g g', D (g * g') = (((normV w' : ℕ) : Qbar l) ^ deg g')⁻¹ * D g + D g' := fun g g' => by
    simp only [D, map_mul, ht'.tval_inePart_mul hl' hφ', ht.tval_inePart_mul hl hφ, hpow]
    ring
  have hD0 : ∀ g, deg g = 0 → D g = 0 := fun g hg => by
    have e : g = ineIncl h' ⟨g, deg_eq_zero_iff.mp hg⟩ := rfl
    have e2 : ∀ σ : Ine (F := E') A, resW h h' (ineIncl h' σ) = ineIncl h (resIne E A σ) := fun σ => Subtype.ext rfl
    rw [e]
    simp only [D, e2, inePart_ineIncl, hct, sub_self]
  obtain ⟨b, hb⟩ : ∃ b : Qbar l, b = D φ' / (1 - ((normV w' : ℕ) : Qbar l)⁻¹) := ⟨_, rfl⟩
  have key : ∀ g, D g = (1 - (((normV w' : ℕ) : Qbar l) ^ deg g)⁻¹) * b := fun g => by
    have h1 := hD (φ' * g) ((φ' * g)⁻¹ * (g * φ'))
    have h0 : deg ((φ' * g)⁻¹ * (g * φ')) = 0 := by simp only [deg_mul, deg_inv]; ring
    rw [mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ', zpow_one, zpow_zero, inv_one, one_mul,
      add_zero] at h1
    rw [hb, ← mul_div_assoc, eq_div_iff hq1]
    linear_combination -h1
  refine ⟨b, fun g => ?_⟩
  have h2 := hN.mul_exp hl ht (resW h h' g) ((((normV w : ℕ) : Qbar l) ^ deg (resW h h' g))⁻¹ * b)
  rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)] at h2
  have hw : wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g =
      (r (resW h h' g) : Matrix n n (Qbar l)) * exp ((-(c' * tval t' (inePart hφ' g))) • N) := by
    rw [wdMat, smul_smul, show -tval t' (inePart hφ' g) * c' = -(c' * tval t' (inePart hφ' g)) by ring]
    rfl
  rw [hw, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have k := key g
  simp only [D] at k
  rw [hpow]
  linear_combination k

/- English proof (translation)
Take `⟨t, ht, φ, hφ, N, a0, hN, ha, rfl⟩` from `hx`. Establish `hl'` using `notMem_of_place h h' hl`. Establish `ht'` using `isTameChar_tameL h' hl'`. Take `⟨c, hc⟩` from `GlobalTheory.TameCharUnique.exists_eq_mul E' Ω A w' h' l hl' (t.comp (resIne E A)) (tameL h' hl') (ht.1.comp continuous_resIne) ht'.1 ht'.2`. Establish `hct : ∀ σ, tval t (resIne E A σ) = algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) * tval (tameL h' hl') σ` using `fun σ => by`.

Establish `e : (t (resIne E A σ)).toAdd = c * ((tameL h' hl') σ).toAdd` using `hc σ`. Simplify using `only [tval, e, PadicInt.coe_mul, map_mul]`. Generalize the expression as in `algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) = c' at hct`. Establish `hc0 : c' ≠ 0`. Introduce `h0`.

Take `⟨σ, hσ⟩` from `exists_tval_resIne_ne (E' := E') ht`. Conclude with `hσ (by rw [hct, h0, zero_mul])`. Establish `hN' : IsMonodromy (tameL h' hl') (r.comp (resG E (E'` using `E') (Ω := Ω))) (c' • N) := by`. Take `⟨U, hU, H⟩` from `hN.2`. Use `⟨hN.1.smul c', U.comap (resIne E A), hU.preimage continuous_resIne, fun σ hσ => ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul, mul_comm (tval _ σ), ← hct]`. Conclude with `H _ hσ`. Establish `hφ' : deg (frob h') = 1` using `deg_frob`. Take `⟨bb, hbb⟩` from `exists_conj_res h h' hl hl' ht ht' hN hφ hφ' hct`. Take `⟨b', hb'⟩` from `hN'.exists_isFrobSS hl' ht' hφ' ι`.

Use `⟨tameL h' hl', ht', frob h', hφ', c' • N, b', hN', hb', ?_⟩` and prove the remaining obligations. Rewrite using `[WD.res_mk]`. Take `⟨u, hu⟩` from `(isUnit_exp (hN.1.smul bb)).map (toEndC ι)`. Establish `ha2 : IsFrobSS (fun g => toEndC ι (wdMat t hφ r N (resW h h' g))) (toEndC ι N) (resRep h h' a0)` using `⟨ha.1, fun g => ha.2 (resW h h' g)⟩`. Establish `hcomm : ∀ g, (hN'.rep hl' ht' hφ' ι) g * toEndC ι N = ((normV w' : ℕ) : ℂ) ^ deg g • (toEndC ι N * (hN'.rep hl' ht' hφ' ι) g)` using `fun g => by`.

Establish `H` using `hN'.rep_comm hl' ht' hφ' ι g`. Rewrite `H` using `[toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm]`. Conclude with `smul_right_injective _ ((map_ne_zero ι).mpr hc0) H`. Take `⟨b1, hb1⟩` from `exists_isFrobSS (hN'.rep hl' ht' hφ' ι) (toEndC ι N) (hN'.isSmooth_rep hl' ht' hφ' ι) (hN.1.map (toEndC ι)) hcomm`. Establish `i1 : (resRep h h' a0).Iso b1` using `ha2.iso hb1 (LinearMap.GeneralLinearGroup.toLinearEquiv u) (fun g v => by show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N (resW h h' g))) v = (toEndC ι (wdMat (tameL h' hl') hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g) * (u : End ℂ (n → ℂ))) v`.

Rewrite using `[hu, ← map_mul, hbb, map_mul])`. Use the proof step `(fun v => by show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v`. Rewrite using `[hu, ← map_mul, exp_smul_mul hN.1, map_mul])`. Establish `i2 : b1.Iso b'` using `IsFrobSS.iso_of_smul ((map_ne_zero ι).mpr hc0) hb1 (by rw [← toEndC_smul]; exact hb')`. Conclude with `WD.sound (i1.trans i2).symm`.
-/
theorem isWDOf_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) {x : WD h}
    (hx : IsWDOf ι r x) : IsWDOf ι (r.comp (resG E (E' := E') (Ω := Ω))) (WD.res h h' x) := by
  obtain ⟨t, ht, φ, hφ, N, a0, hN, ha, rfl⟩ := hx
  have hl' := notMem_of_place h h' hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul E' Ω A w' h' l hl' (t.comp (resIne E A)) (tameL h' hl')
    (ht.1.comp continuous_resIne) ht'.1 ht'.2
  have hct : ∀ σ, tval t (resIne E A σ) = algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) * tval (tameL h' hl') σ := fun σ => by
    have e : (t (resIne E A σ)).toAdd = c * ((tameL h' hl') σ).toAdd := hc σ
    simp only [tval, e, PadicInt.coe_mul, map_mul]
  generalize algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) = c' at hct
  have hc0 : c' ≠ 0 := by
    intro h0
    obtain ⟨σ, hσ⟩ := exists_tval_resIne_ne (E' := E') ht
    exact hσ (by rw [hct, h0, zero_mul])
  have hN' : IsMonodromy (tameL h' hl') (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) := by
    obtain ⟨U, hU, H⟩ := hN.2
    refine ⟨hN.1.smul c', U.comap (resIne E A), hU.preimage continuous_resIne, fun σ hσ => ?_⟩
    rw [smul_smul, mul_comm (tval _ σ), ← hct]
    exact H _ hσ
  have hφ' : deg (frob h') = 1 := deg_frob
  obtain ⟨bb, hbb⟩ := exists_conj_res h h' hl hl' ht ht' hN hφ hφ' hct
  obtain ⟨b', hb'⟩ := hN'.exists_isFrobSS hl' ht' hφ' ι
  refine ⟨tameL h' hl', ht', frob h', hφ', c' • N, b', hN', hb', ?_⟩
  rw [WD.res_mk]
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul bb)).map (toEndC ι)
  have ha2 : IsFrobSS (fun g => toEndC ι (wdMat t hφ r N (resW h h' g))) (toEndC ι N) (resRep h h' a0) :=
    ⟨ha.1, fun g => ha.2 (resW h h' g)⟩
  have hcomm : ∀ g, (hN'.rep hl' ht' hφ' ι) g * toEndC ι N =
      ((normV w' : ℕ) : ℂ) ^ deg g • (toEndC ι N * (hN'.rep hl' ht' hφ' ι) g) := fun g => by
    have H := hN'.rep_comm hl' ht' hφ' ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at H
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) H
  obtain ⟨b1, hb1⟩ := exists_isFrobSS (hN'.rep hl' ht' hφ' ι) (toEndC ι N) (hN'.isSmooth_rep hl' ht' hφ' ι)
    (hN.1.map (toEndC ι)) hcomm
  have i1 : (resRep h h' a0).Iso b1 := ha2.iso hb1 (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N (resW h h' g))) v =
        (toEndC ι (wdMat (tameL h' hl') hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g) *
          (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, hbb, map_mul])
    (fun v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : b1.Iso b' := IsFrobSS.iso_of_smul ((map_ne_zero ι).mpr hc0) hb1 (by rw [← toEndC_smul]; exact hb')
  exact WD.sound (i1.trans i2).symm

end

end WeilDeligneRestriction

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ X l a _ ι r _ A w h w' h' hl x hx`. Conclude with `WeilDeligneRestriction.isWDOf_res h h' hl ι r hx`.
-/
theorem weil_deligne_restriction_away : K5 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ A w h w' h' hl x hx
  exact WeilDeligneRestriction.isWDOf_res h h' hl ι r hx

end PositivityTheory.Pf1.CLGD.K

end
