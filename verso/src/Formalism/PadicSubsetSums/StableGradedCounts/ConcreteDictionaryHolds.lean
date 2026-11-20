import Formalism.PadicSubsetSums.CentralIdempotents.GL2UnipotentBruhatDecomposition

namespace Formalism.IrreducibleCountingLemmas.WindowSums

namespace ConcreteDictionaryLemmas
open PowerSeries

section ode
variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/- English proof (translation)
Establish `h` using `congrArg (coeff n) hf`. Rewrite `h` using `[add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]`. Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [coeff_zero_X_mul, add_zero] at h`.

Simplify using `only [Nat.cast_zero, zero_add, sub_zero, one_mul] at h ⊢`. Simplify using `using h`. Consider the case `succ m`. Rewrite `h` using `[coeff_succ_X_mul, coeff_derivative]`. Move the coercions through the operations in `at h ⊢`.

Take the linear combination `h`.
-/
theorem ode_coeff (c : R) (f : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f) (n : ℕ) :
    ((n : R) + 1) * coeff (n + 1) f = (c - n) * coeff n f := by
  have h := congrArg (coeff n) hf
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at h
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, add_zero] at h
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at h ⊢
    simpa using h
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

/- English proof (translation)
Use extensionality with `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using h0`. Consider the case `succ n ih`. Establish `h1` using `ode_coeff c f hf n`.

Establish `h2` using `ode_coeff c g hg n`. Rewrite `h1` using `[ih, ← h2]`. Establish `h3 : (n + 1) • coeff (n + 1) f = (n + 1) • coeff (n + 1) g`. Simplify `h1` using `[nsmul_eq_mul]`. Conclude with `nsmul_right_injective (Nat.succ_ne_zero n) h3`.
-/
theorem ode_unique (c : R) (f g : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f)
    (hg : (1 + X) * d⁄dX R g = C c * g) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := ode_coeff c f hf n
    have h2 := ode_coeff c g hg n
    rw [ih, ← h2] at h1
    have h3 : (n + 1) • coeff (n + 1) f = (n + 1) • coeff (n + 1) g := by
      simpa [nsmul_eq_mul] using h1
    exact nsmul_right_injective (Nat.succ_ne_zero n) h3

end ode

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use extensionality with `n`. Establish `key : ∀ n : ℕ, ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = Ring.choose c n * (c - n)`. Introduce `n`. Use `Ring.choose_smul_choose c (Nat.le_succ n)` as an intermediate fact. Simplify using `only [Nat.succ_eq_add_one, Nat.choose_succ_self_right, add_tsub_cancel_left, Ring.choose_one_right, nsmul_eq_mul] at this`.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]`. Simplify using `only [binomialSeries_coeff, smul_eq_mul, mul_one]`. Consider the cases of `n with`.

Consider the case `zero`. Use `key 0` as an intermediate fact. Simplify using `only [coeff_zero_X_mul, add_zero]`. Simplify using `only [Nat.cast_zero, zero_add, sub_zero, one_mul] at this ⊢`. Rewrite using `[mul_one, this, mul_comm]`.

Consider the case `succ m`. Rewrite using `[coeff_succ_X_mul, coeff_derivative]`. Simplify using `only [binomialSeries_coeff, smul_eq_mul, mul_one]`. Use `key (m + 1)` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Take the linear combination `this`.
-/
theorem bin_ode (c : ℤ_[l]) :
    (1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c) = C c * binomialSeries ℤ_[l] c := by
  ext n
  have key : ∀ n : ℕ, ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = Ring.choose c n * (c - n) := by
    intro n
    have := Ring.choose_smul_choose c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one, Nat.choose_succ_self_right, add_tsub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul] at this
    push_cast at this
    exact this
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  cases n with
  | zero =>
    have := key 0
    simp only [coeff_zero_X_mul, add_zero]
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at this ⊢
    rw [mul_one, this, mul_comm]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
    have := key (m + 1)
    push_cast at this ⊢
    linear_combination this

/- English proof (translation)
Simplify using `[brk]`.
-/
theorem brk_const (a : ℤ_[l]) : constantCoeff (brk l a) = 0 := by
  simp [brk]

/- English proof (translation)
The claim follows from `HasSubst.of_constantCoeff_zero' (brk_const a)`.
-/
theorem brk_hasSubst (a : ℤ_[l]) : HasSubst (brk l a) :=
  HasSubst.of_constantCoeff_zero' (brk_const a)

/- English proof (translation)
Establish `hs : HasSubst h` using `HasSubst.of_constantCoeff_zero' hh`. Establish `h1 : f = C (constantCoeff f) + (f - C (constantCoeff f))` using `by ring`. Use `conv_lhs => rw [h1]`. Rewrite using `[subst_add hs, map_add]`. Establish `h2 : constantCoeff (subst h (f - C (constantCoeff f))) = 0` using `constantCoeff_subst_eq_zero hh _ (by simp)`.

Rewrite using `[h2, add_zero, subst_C]`. Conclude with `constantCoeff_C _`.
-/
theorem const_subst (h f : PowerSeries ℤ_[l]) (hh : constantCoeff h = 0) :
    constantCoeff (subst h f) = constantCoeff f := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have h1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add]
  have h2 : constantCoeff (subst h (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero hh _ (by simp)
  rw [h2, add_zero, subst_C]
  exact constantCoeff_C _

/- English proof (translation)
Establish `hs` using `brk_hasSubst b`. Apply `ode_unique (a * b) _ _ _ (bin_ode _)` to reduce the goal to its premises. Rewrite using `[const_subst _ _ (brk_const b)]`. Simplify using the standard rewrite rules. Rewrite using `[derivative_subst hs]`.

Establish `h1 : d⁄dX ℤ_[l] (brk l b) = d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b)`. Simplify using `[brk]`. Establish `h2 : (1 + X : PowerSeries ℤ_[l]).subst (brk l b) = binomialSeries ℤ_[l] b`. Rewrite using `[subst_add hs, subst_X hs, ← map_one C, subst_C]`. Simplify using `[brk]`.

Establish `h3` using `congrArg (subst (brk l b)) (bin_ode a)`. Rewrite `h3` using `[subst_mul hs, subst_mul hs, h2, subst_C]`. Establish `h4` using `bin_ode b`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.

Substitute `(brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a))) := by rw [h4]; ring` using the available equality. Use `_ = _ := by`. Rewrite using `[h3, map_mul]`. Establish `: (MvPowerSeries.C a : MvPowerSeries Unit ℤ_[l]) = (C a : PowerSeries ℤ_[l])` using `rfl`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bin_comp (a b : ℤ_[l]) :
    subst (brk l b) (binomialSeries ℤ_[l] a) = binomialSeries ℤ_[l] (a * b) := by
  have hs := brk_hasSubst b
  apply ode_unique (a * b) _ _ _ (bin_ode _)
  · rw [const_subst _ _ (brk_const b)]; simp
  · rw [derivative_subst hs]
    have h1 : d⁄dX ℤ_[l] (brk l b) = d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b) := by
      simp [brk]
    have h2 : (1 + X : PowerSeries ℤ_[l]).subst (brk l b) = binomialSeries ℤ_[l] b := by
      rw [subst_add hs, subst_X hs, ← map_one C, subst_C]
      simp [brk]
    have h3 := congrArg (subst (brk l b)) (bin_ode a)
    rw [subst_mul hs, subst_mul hs, h2, subst_C] at h3
    have h4 := bin_ode b
    rw [h1]
    calc (1 + X) * (subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b))
        = subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            ((1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b)) := by ring
      _ = C b * (binomialSeries ℤ_[l] b *
            subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a))) := by rw [h4]; ring
      _ = _ := by
        rw [h3, map_mul]
        have : (MvPowerSeries.C a : MvPowerSeries Unit ℤ_[l]) = (C a : PowerSeries ℤ_[l]) := rfl
        rw [this]; ring

/- English proof (translation)
Establish `hs` using `brk_hasSubst b`. Express the relevant statement in the definitionally equal form `subst (brk l b) (binomialSeries ℤ_[l] a - 1) = _`. Rewrite using `[subst_sub hs, bin_comp, ← map_one C, subst_C]`. Simplify using `[brk]`.
-/
theorem brk_comp (a b : ℤ_[l]) : subst (brk l b) (brk l a) = brk l (a * b) := by
  have hs := brk_hasSubst b
  change subst (brk l b) (binomialSeries ℤ_[l] a - 1) = _
  rw [subst_sub hs, bin_comp, ← map_one C, subst_C]
  simp [brk]

/- English proof (translation)
Use `⟨PowerSeries.mk fun n => coeff (n + 1) (brk l a), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Consider the cases of `n with`. Consider the case `zero => simp [brk_const]`. Consider the case `succ m => rw [coeff_succ_X_mul, coeff_mk]`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mk]`. Simplify using `[brk, binomialSeries_coeff, coeff_one]`.
-/
theorem brk_factor (a : ℤ_[l]) :
    ∃ g : PowerSeries ℤ_[l], brk l a = X * g ∧ constantCoeff g = a := by
  refine ⟨PowerSeries.mk fun n => coeff (n + 1) (brk l a), ?_, ?_⟩
  · ext n
    cases n with
    | zero => simp [brk_const]
    | succ m => rw [coeff_succ_X_mul, coeff_mk]
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp [brk, binomialSeries_coeff, coeff_one]

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod l) (l - 1)`. Establish `inj : Function.Injective (WittVector.teichmuller l : ZMod l →* WittVector l (ZMod l))`. Introduce `x y hxy`. Use `congrArg (fun w => WittVector.coeff w 0) hxy` as an intermediate fact.

Simplify `this` using `[WittVector.teichmuller_coeff_zero]`. Establish `h1` using `hζ.map_of_injective inj`. Establish `h2` using `h1.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective`. Conclude with `⟨_, h2.pow (by omega) h.symm⟩`.
-/
theorem exists_prim (e s : ℕ) (h : e * s = l - 1) : ∃ ω : ℤ_[l], IsPrimitiveRoot ω s := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod l) (l - 1)
  have inj : Function.Injective (WittVector.teichmuller l : ZMod l →* WittVector l (ZMod l)) := by
    intro x y hxy
    have := congrArg (fun w => WittVector.coeff w 0) hxy
    simpa [WittVector.teichmuller_coeff_zero] using this
  have h1 := hζ.map_of_injective inj
  have h2 := h1.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective
  exact ⟨_, h2.pow (by omega) h.symm⟩

/- English proof (translation)
Establish `hs` using `brk_hasSubst ω`. Take `⟨Dd, hDd⟩ : ∃ Dd, Dd = T - C (constantCoeff T)` from `⟨_, rfl⟩`. Establish `hD : subst (brk l ω) Dd = Dd`. Rewrite using `[hDd, subst_sub hs, hT, subst_C]`. Both sides reduce to the same expression.

Rewrite using `[← hDd, X_pow_dvd_iff]`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `hk`.

Establish `hdiv : X ^ k ∣ Dd` using `X_pow_dvd_iff.mpr (fun m hm => ih m hm (hm.trans hk))`. Take `⟨D', hD'⟩` from `hdiv`. Establish `hck : coeff k Dd = constantCoeff D'`. Use `coeff_X_pow_mul D' k 0` as an intermediate fact. Rewrite using `[hD']`.

Simplify using `using this`. Break down `Nat.eq_zero_or_pos k with rfl | hkpos` into its components or cases. Simplify using `[hDd]`. Take `⟨g, hg, hg0⟩` from `brk_factor ω`. Establish `e1 : X ^ k * D' = X ^ k * (g ^ k * subst (brk l ω) D')`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : D' = g ^ k * subst (brk l ω) D'` using `mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) e1`. Establish `e3` using `congrArg constantCoeff e2`. Rewrite `e3` using `[map_mul, map_pow, hg0, const_subst _ _ (brk_const ω)]`. Establish `e4 : (ω ^ k - 1) * constantCoeff D' = 0` using `by linear_combination -e3`.

Break down `mul_eq_zero.mp e4 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h) (hω.pow_ne_one_of_pos_of_lt hkpos.ne' hk)`. Rewrite using `[hck, h]`.
-/
theorem inv_lemma (s : ℕ) (ω : ℤ_[l]) (hω : IsPrimitiveRoot ω s) (T : PowerSeries ℤ_[l])
    (hT : subst (brk l ω) T = T) : X ^ s ∣ T - C (constantCoeff T) := by
  have hs := brk_hasSubst ω
  obtain ⟨Dd, hDd⟩ : ∃ Dd, Dd = T - C (constantCoeff T) := ⟨_, rfl⟩
  have hD : subst (brk l ω) Dd = Dd := by
    rw [hDd, subst_sub hs, hT, subst_C]; rfl
  rw [← hDd, X_pow_dvd_iff]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hdiv : X ^ k ∣ Dd := X_pow_dvd_iff.mpr (fun m hm => ih m hm (hm.trans hk))
    obtain ⟨D', hD'⟩ := hdiv
    have hck : coeff k Dd = constantCoeff D' := by
      have := coeff_X_pow_mul D' k 0
      rw [hD']; simpa using this
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [hDd]
    obtain ⟨g, hg, hg0⟩ := brk_factor ω
    have e1 : X ^ k * D' = X ^ k * (g ^ k * subst (brk l ω) D') := by
      calc X ^ k * D' = Dd := hD'.symm
        _ = subst (brk l ω) Dd := hD.symm
        _ = subst (brk l ω) (X ^ k * D') := congrArg _ hD'
        _ = (brk l ω) ^ k * subst (brk l ω) D' := by rw [subst_mul hs, subst_pow hs, subst_X hs]
        _ = _ := by rw [hg]; ring
    have e2 : D' = g ^ k * subst (brk l ω) D' := mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) e1
    have e3 := congrArg constantCoeff e2
    rw [map_mul, map_pow, hg0, const_subst _ _ (brk_const ω)] at e3
    have e4 : (ω ^ k - 1) * constantCoeff D' = 0 := by linear_combination -e3
    rcases mul_eq_zero.mp e4 with h | h
    · exact absurd (sub_eq_zero.mp h) (hω.pow_ne_one_of_pos_of_lt hkpos.ne' hk)
    · rw [hck, h]

/- English proof (translation)
Rewrite using `[← coe_substAlgHom hs, map_prod]`.
-/
theorem subst_prod {ι : Type*} (h : PowerSeries ℤ_[l]) (hs : HasSubst h) (t : Finset ι)
    (f : ι → PowerSeries ℤ_[l]) : subst h (∏ i ∈ t, f i) = ∏ i ∈ t, subst h (f i) := by
  rw [← coe_substAlgHom hs, map_prod]

end ConcreteDictionaryLemmas

open PowerSeries ConcreteDictionaryLemmas

/- English proof (translation)
Introduce `l _ e s hes u q hq`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hs1 : 0 < s`. Break down `Nat.eq_zero_or_pos s with rfl | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Take `⟨ω₀, hω₀⟩` from `exists_prim (l := l) e s hes`. Establish `hcard` using `hω₀.card_nthRootsFinset`. Establish `hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1` using `fun ω => Polynomial.mem_nthRootsFinset hs1 1`. Use `choose g hg hg0 using (brk_factor (l := l))`.

Establish `hb : ∃ ε : (PowerSeries ℤ_[l])ˣ, piP l s = (ε : PowerSeries ℤ_[l]) * X ^ s`. Establish `hu : IsUnit (∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), g ω)`. Rewrite using `[isUnit_iff_constantCoeff, map_prod]`. Use `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_` and prove the remaining obligations. Introduce `ω hω`.

Rewrite using `[hg0]`. Conclude with `IsUnit.of_pow_eq_one ((hμ ω).mp hω) hs1.ne'`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, piP, Finset.prod_congr rfl (fun ω _ => hg ω), Finset.prod_mul_distrib, Finset.prod_const, hcard, mul_comm]`. Take `⟨ε, hε⟩` from `hb`.

Establish `hXs : X ^ s = ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * piP l s`. Rewrite using `[hε, ← mul_assoc, Units.inv_mul, one_mul]`. Use `⟨hcard, ⟨ε, hε⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hs` using `brk_hasSubst (l : ℤ_[l])`. Establish `hu1 : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l]))`.

Rewrite using `[isUnit_iff_constantCoeff, const_subst _ _ (brk_const _), ← isUnit_iff_constantCoeff]`. Conclude with `ε.isUnit`. Establish `hu : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l]) * ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]))` using `hu1.mul (ε⁻¹).isUnit`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`.

Use `conv_lhs => rw [hε]`. Rewrite using `[subst_mul hs, subst_pow hs, subst_X hs, ← hq, mul_pow, hXs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsu` using `brk_hasSubst u`. Choose the witnesses or unpack the hypotheses as in `⟨T, hTdef⟩ : ∃ T, T = ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]),`.

Substitute `(brk l ω) (g u) := ⟨_, rfl⟩` using the available equality. Establish `h1 : subst (brk l u) (piP l s) = piP l s * T`. Rewrite using `[piP, subst_prod _ hsu, hTdef, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun ω _ => ?_` and prove the remaining obligations. Establish `hsω` using `brk_hasSubst ω`.

Rewrite using `[brk_comp, mul_comm ω u, ← brk_comp u ω]`. Use `conv_lhs => rw [hg u]`. Rewrite using `[subst_mul hsω, subst_X hsω]`. Establish `hT0 : constantCoeff T = u ^ s`. Rewrite using `[hTdef, map_prod, Finset.prod_congr rfl (fun ω _ => (const_subst _ _ (brk_const ω)).trans (hg0 u)), Finset.prod_const, hcard]`.

Establish `hTinv : subst (brk l ω₀) T = T`. Establish `hs0` using `brk_hasSubst ω₀`. Rewrite using `[hTdef, subst_prod _ hs0]`. Establish `hstep : ∀ ω, subst (brk l ω₀) (subst (brk l ω) (g u)) =`. Substitute `(brk l (ω * ω₀)) (g u) := by` using the available equality.

Introduce `ω`. Rewrite using `[subst_comp_subst_apply (brk_hasSubst ω) hs0, brk_comp]`. Rewrite using `[Finset.prod_congr rfl (fun ω _ => hstep ω)]`. Establish `h01 : ω₀ ^ s = 1` using `hω₀.pow_eq_one`. Establish `h02 : ω₀ * ω₀ ^ (s - 1) = 1`.

Rewrite using `[← pow_succ', Nat.sub_add_cancel hs1, h01]`. Use `Finset.prod_nbij' (fun ω => ω * ω₀) (fun ω => ω * ω₀ ^ (s - 1)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `ω hω`. Rewrite `hω`, the goal using `[hμ]`. Rewrite using `[mul_pow, hω, h01, one_mul]`.

Introduce `ω hω`. Rewrite `hω`, the goal using `[hμ]`. Rewrite using `[mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, h01, one_pow, one_mul]`. Introduce `ω _`. Simplify using `only [mul_assoc, h02, mul_one]`.

Introduce `ω _`. Simplify using `only [mul_assoc, mul_comm (ω₀ ^ (s - 1)) ω₀, h02, mul_one]`. Introduce `ω _`. Both sides reduce to the same expression. Take `⟨w, hw⟩` from `inv_lemma s ω₀ hω₀ T hTinv`.

Rewrite `hw` using `[hT0]`. Use `⟨((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * w, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem concrete_dictionary_holds : DictConcrete := by
  intro l _ e s hes u q hq
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hs1 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · omega
    · exact h
  obtain ⟨ω₀, hω₀⟩ := exists_prim (l := l) e s hes
  have hcard := hω₀.card_nthRootsFinset
  have hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1 :=
    fun ω => Polynomial.mem_nthRootsFinset hs1 1
  choose g hg hg0 using (brk_factor (l := l))

  have hb : ∃ ε : (PowerSeries ℤ_[l])ˣ, piP l s = (ε : PowerSeries ℤ_[l]) * X ^ s := by
    have hu : IsUnit (∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), g ω) := by
      rw [isUnit_iff_constantCoeff, map_prod]
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_
      intro ω hω
      rw [hg0]
      exact IsUnit.of_pow_eq_one ((hμ ω).mp hω) hs1.ne'
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, piP, Finset.prod_congr rfl (fun ω _ => hg ω), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, mul_comm]
  obtain ⟨ε, hε⟩ := hb
  have hXs : X ^ s = ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * piP l s := by
    rw [hε, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨hcard, ⟨ε, hε⟩, ?_, ?_⟩
  ·
    have hs := brk_hasSubst (l : ℤ_[l])
    have hu1 : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l])) := by
      rw [isUnit_iff_constantCoeff, const_subst _ _ (brk_const _), ← isUnit_iff_constantCoeff]
      exact ε.isUnit
    have hu : IsUnit (subst (brk l (l : ℤ_[l])) (ε : PowerSeries ℤ_[l]) *
        ((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l])) := hu1.mul (ε⁻¹).isUnit
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec]
    conv_lhs => rw [hε]
    rw [subst_mul hs, subst_pow hs, subst_X hs, ← hq, mul_pow, hXs]
    ring
  ·
    have hsu := brk_hasSubst u
    obtain ⟨T, hTdef⟩ : ∃ T, T = ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]),
      subst (brk l ω) (g u) := ⟨_, rfl⟩
    have h1 : subst (brk l u) (piP l s) = piP l s * T := by
      rw [piP, subst_prod _ hsu, hTdef, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ω _ => ?_
      have hsω := brk_hasSubst ω
      rw [brk_comp, mul_comm ω u, ← brk_comp u ω]
      conv_lhs => rw [hg u]
      rw [subst_mul hsω, subst_X hsω]
    have hT0 : constantCoeff T = u ^ s := by
      rw [hTdef, map_prod, Finset.prod_congr rfl
        (fun ω _ => (const_subst _ _ (brk_const ω)).trans (hg0 u)), Finset.prod_const, hcard]
    have hTinv : subst (brk l ω₀) T = T := by
      have hs0 := brk_hasSubst ω₀
      rw [hTdef, subst_prod _ hs0]
      have hstep : ∀ ω, subst (brk l ω₀) (subst (brk l ω) (g u)) =
          subst (brk l (ω * ω₀)) (g u) := by
        intro ω
        rw [subst_comp_subst_apply (brk_hasSubst ω) hs0, brk_comp]
      rw [Finset.prod_congr rfl (fun ω _ => hstep ω)]
      have h01 : ω₀ ^ s = 1 := hω₀.pow_eq_one
      have h02 : ω₀ * ω₀ ^ (s - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hs1, h01]
      refine Finset.prod_nbij' (fun ω => ω * ω₀) (fun ω => ω * ω₀ ^ (s - 1)) ?_ ?_ ?_ ?_ ?_
      · intro ω hω
        rw [hμ] at hω ⊢
        rw [mul_pow, hω, h01, one_mul]
      · intro ω hω
        rw [hμ] at hω ⊢
        rw [mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, h01, one_pow, one_mul]
      · intro ω _
        simp only [mul_assoc, h02, mul_one]
      · intro ω _
        simp only [mul_assoc, mul_comm (ω₀ ^ (s - 1)) ω₀, h02, mul_one]
      · intro ω _
        rfl
    obtain ⟨w, hw⟩ := inv_lemma s ω₀ hω₀ T hTinv
    rw [hT0] at hw
    refine ⟨((ε⁻¹ : (PowerSeries ℤ_[l])ˣ) : PowerSeries ℤ_[l]) * w, ?_⟩
    rw [h1]
    calc piP l s * T - C (u ^ s) * piP l s = piP l s * (T - C (u ^ s)) := by ring
      _ = piP l s * (X ^ s * w) := by rw [hw]
      _ = _ := by rw [hXs]; ring

end Formalism.IrreducibleCountingLemmas.WindowSums
