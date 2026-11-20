import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CondConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.EntInMulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfPowLe

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.MP

section Tsz

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

/- English proof (translation)
The claim follows from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] exact isUnit_or_isUnit_one_sub_self _`.
-/
private theorem tsz_local [IsLocalRing O] : IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

/- English proof (translation)
Simplify using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`.
-/
private theorem tsz_mem_max [IsLocalRing O] [IsLocalRing (TrivSqZeroExt O M)] (x : TrivSqZeroExt O M) :
    x ∈ maximalIdeal (TrivSqZeroExt O M) ↔ x.fst ∈ maximalIdeal O := by
  simp [TrivSqZeroExt.isUnit_iff_isUnit_fst]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le hJ he`.
-/
private theorem precomplete_of_pow_le {A : Type} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A :=
  _root_.UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le hJ he

/- English proof (translation)
Establish `h1 : IsLocalRing (TrivSqZeroExt O M)` using `tsz_local`. Establish `h2 : Module.Finite O (TrivSqZeroExt O M)` using `inferInstanceAs (Module.Finite O (O × M))`. Establish `h3` using `IsNoetherianRing.of_finite O (TrivSqZeroExt O M)`. Establish `h4` using `GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) (TrivSqZeroExt O M)`. Establish `hJ : (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M)) ≤ maximalIdeal _`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, tsz_mem_max]`. Conclude with `hx`. Establish `he : maximalIdeal (TrivSqZeroExt O M) ^ 2 ≤ (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M))`.

Rewrite using `[pow_two, Ideal.mul_le]`. Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[tsz_mem_max]`. Establish `: x * y = algebraMap O _ x.fst * y + algebraMap O _ y.fst * TrivSqZeroExt.inr x.snd`. Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`.

Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy))`. Establish `h5` using `precomplete_of_pow_le hJ he`. Conclude with `{ complete := ⟨⟩ isLocalHom := ⟨fun a ha => by simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.algebraMap_eq_inl] using ha⟩ res_surj := fun x => ⟨x.fst, by rw [tsz_mem_max]; simp [TrivSqZeroExt.algebraMap_eq_inl]⟩ }`.
-/
private theorem tsz_isCO [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [Module.Finite O M] : IsCO O (TrivSqZeroExt O M) := by
  have h1 : IsLocalRing (TrivSqZeroExt O M) := tsz_local
  have h2 : Module.Finite O (TrivSqZeroExt O M) := inferInstanceAs (Module.Finite O (O × M))
  have h3 := IsNoetherianRing.of_finite O (TrivSqZeroExt O M)
  have h4 := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) (TrivSqZeroExt O M)
  have hJ : (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M)) ≤ maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, tsz_mem_max]
    exact hx
  have he : maximalIdeal (TrivSqZeroExt O M) ^ 2 ≤ (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M)) := by
    rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    rw [tsz_mem_max] at hx hy
    have : x * y = algebraMap O _ x.fst * y + algebraMap O _ y.fst * TrivSqZeroExt.inr x.snd := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy))
  have h5 := precomplete_of_pow_le hJ he
  exact { complete := ⟨⟩
          isLocalHom := ⟨fun a ha => by simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.algebraMap_eq_inl] using ha⟩
          res_surj := fun x => ⟨x.fst, by rw [tsz_mem_max]; simp [TrivSqZeroExt.algebraMap_eq_inl]⟩ }

end Tsz

section PS

variable {O A σ : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]

/- English proof (translation)
Establish `hc : ∀ n : σ →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0` using `fun n hn => by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hn (Finsupp.ext h)`. Use `choose c hc using hc`.

Set `q : σ → MvPowerSeries σ O` to `fun i n => if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0`. Establish `hq : ∀ i n, MvPowerSeries.coeff n (q i) = if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0` using `fun _ _ => rfl`. Establish `hs : p = ∑ i, q i`. Use extensionality with `n`. Rewrite using `[map_sum]`.

Simplify using `only [hq]`. Distinguish the cases in `h : n ≠ 0`. Simplify using `[dif_pos h]`. Simplify using `only [dif_neg h, Finset.sum_const_zero] push Not at h`. Substitute `h` using the available equality.

Simplify using `using hp`. Establish `hd : ∀ i, MvPowerSeries.X i ∣ q i` using `fun i => by`. Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `m hm`. Rewrite using `[hq]`.

Use `split_ifs with h1 h2`. Conclude with `absurd (h2 ▸ hm) (hc m h1)`. Both sides reduce to the same expression. Both sides reduce to the same expression. Use `choose r hr using hd`.

Conclude with `⟨r, hs.trans (Finset.sum_congr rfl fun i _ => hr i)⟩`.
-/
private theorem exists_sum_X_mul (p : MvPowerSeries σ O) (hp : MvPowerSeries.constantCoeff p = 0) :
    ∃ r : σ → MvPowerSeries σ O, p = ∑ i, MvPowerSeries.X i * r i := by
  classical
  have hc : ∀ n : σ →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0 := fun n hn => by
    by_contra h
    push Not at h
    exact hn (Finsupp.ext h)
  choose c hc using hc
  let q : σ → MvPowerSeries σ O := fun i n =>
    if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0
  have hq : ∀ i n, MvPowerSeries.coeff n (q i) =
      if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0 := fun _ _ => rfl
  have hs : p = ∑ i, q i := by
    ext n
    rw [map_sum]
    simp only [hq]
    by_cases h : n ≠ 0
    · simp [dif_pos h]
    · simp only [dif_neg h, Finset.sum_const_zero]
      push Not at h
      subst h
      simpa using hp
  have hd : ∀ i, MvPowerSeries.X i ∣ q i := fun i => by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hq]
    split_ifs with h1 h2
    · exact absurd (h2 ▸ hm) (hc m h1)
    · rfl
    · rfl
  choose r hr using hd
  exact ⟨r, hs.trans (Finset.sum_congr rfl fun i _ => hr i)⟩

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Use `MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single i 1) (n := 0) (φ := r) (1 : O)` as an intermediate fact. Simplify `this` using `[MvPowerSeries.X_def]`. Conclude with `MvPowerSeries.X_dvd_iff.1 (dvd_mul_right _ _) _ (Finsupp.single_eq_of_ne h)`.
-/
private theorem coeff_X_mul (i j : σ) (r : MvPowerSeries σ O) [DecidableEq σ] :
    MvPowerSeries.coeff (Finsupp.single j 1) (MvPowerSeries.X i * r) =
      if i = j then MvPowerSeries.constantCoeff r else 0 := by
  split_ifs with h
  · subst h
    have := MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single i 1) (n := 0) (φ := r) (1 : O)
    simpa [MvPowerSeries.X_def] using this
  · exact MvPowerSeries.X_dvd_iff.1 (dvd_mul_right _ _) _ (Finsupp.single_eq_of_ne h)

/- English proof (translation)
Establish `h0 : ∀ p : MvPowerSeries σ O, ∃ r : σ → MvPowerSeries σ O, p = algebraMap O _ (MvPowerSeries.constantCoeff p) + ∑ i, MvPowerSeries.X i * r i` using `fun p => by`. Take `⟨r, hr⟩` from `exists_sum_X_mul (p - algebraMap O _ (MvPowerSeries.constantCoeff p)) (by simp [MvPowerSeries.algebraMap_apply])`. Conclude with `⟨r, by rw [← hr]; ring⟩`. Establish `h1 : ∀ i (r : MvPowerSeries σ O), φ (MvPowerSeries.X i * r) = MvPowerSeries.constantCoeff r • φ (MvPowerSeries.X i)` using `fun i r => by`. Take `⟨s, hs⟩` from `h0 r`.

Use `conv_lhs => rw [hs]`. Simplify using `only [map_mul, map_add, map_sum, AlgHom.commutes, mul_add, Finset.mul_sum, ← mul_assoc, hφ, zero_mul, Finset.sum_const_zero, add_zero, Algebra.smul_def]`. Conclude with `mul_comm _ _`. Take `⟨r, hr⟩` from `h0 p`. Establish `h2 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) p = MvPowerSeries.constantCoeff (r j)` using `fun j => by conv_lhs => rw [hr]`.

Simplify using `[coeff_X_mul, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]`. Use `conv_lhs => rw [hr]`. Simplify using `only [map_add, map_sum, AlgHom.commutes, h1, h2]`.
-/
private theorem map_lin (φ : MvPowerSeries σ O →ₐ[O] A)
    (hφ : ∀ i j, φ (MvPowerSeries.X i) * φ (MvPowerSeries.X j) = 0) (p : MvPowerSeries σ O) :
    φ p = algebraMap O A (MvPowerSeries.constantCoeff p) +
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p • φ (MvPowerSeries.X i) := by
  classical
  have h0 : ∀ p : MvPowerSeries σ O, ∃ r : σ → MvPowerSeries σ O,
      p = algebraMap O _ (MvPowerSeries.constantCoeff p) + ∑ i, MvPowerSeries.X i * r i := fun p => by
    obtain ⟨r, hr⟩ := exists_sum_X_mul (p - algebraMap O _ (MvPowerSeries.constantCoeff p))
      (by simp [MvPowerSeries.algebraMap_apply])
    exact ⟨r, by rw [← hr]; ring⟩
  have h1 : ∀ i (r : MvPowerSeries σ O), φ (MvPowerSeries.X i * r) =
      MvPowerSeries.constantCoeff r • φ (MvPowerSeries.X i) := fun i r => by
    obtain ⟨s, hs⟩ := h0 r
    conv_lhs => rw [hs]
    simp only [map_mul, map_add, map_sum, AlgHom.commutes, mul_add, Finset.mul_sum, ← mul_assoc, hφ, zero_mul,
      Finset.sum_const_zero, add_zero, Algebra.smul_def]
    exact mul_comm _ _
  obtain ⟨r, hr⟩ := h0 p
  have h2 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) p = MvPowerSeries.constantCoeff (r j) := fun j => by
    conv_lhs => rw [hr]
    simp [coeff_X_mul, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  conv_lhs => rw [hr]
  simp only [map_add, map_sum, AlgHom.commutes, h1, h2]

end PS

section Point

private def Tm (C : Type) [CommRing C] : Matrix (Fin 3) (Fin 3) C := !![0, 0, 0; 1, 0, 0; 0, -1, 0]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | rfl | exact absurd rfl h`.
-/
private theorem Tm_wt (C : Type) [CommRing C] (a b : Fin 3) (h : wt a b ≠ -1) : Tm C a b = 0 := by
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd rfl h

/- English proof (translation)
The claim follows from `MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ((h' g).2.trans (h'' g).2.symm)) ((h' g).1.trans (h'' g).1.symm)`.
-/
private theorem deform_eq {D C : Type} [Group D] [CommRing C] {r r' r'' : D →* GG 3 C}
    {γ : D → Matrix (Fin 3) (Fin 3) C} (h' : IsDeform r γ r') (h'' : IsDeform r γ r'') : r' = r'' :=
  MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ((h' g).2.trans (h'' g).2.symm))
    ((h' g).1.trans (h'' g).1.symm)

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι)
  (C : Type) [CommRing C] [Algebra O C]

/- English proof (translation)
Use `MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl` and prove the remaining obligations. Use `show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = (tor C _ : GL (Fin 3) C)`. Rewrite using `[tor_val, tor_val, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O C).toMonoidHom)]`. Both sides reduce to the same expression.
-/
private theorem rz_eq : F.rz C = r0 F.η ((Units.map (algebraMap O C).toMonoidHom).comp F.Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = (tor C _ : GL (Fin 3) C)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  rw [MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O C).toMonoidHom)]
  rfl

/- English proof (translation)
Use `show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = _`. Rewrite using `[tor_val, Matrix.diagonal_map (map_zero _)]`. Both sides reduce to the same expression.
-/
private theorem rz_mat (g : Γ) : (F.rz C g).mat = Matrix.diagonal fun i => algebraMap O C (psi F.Ψ i g) := by
  show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

/- English proof (translation)
Rewrite using `[rz_eq]`. Use extensionality with `a b`. Rewrite using `[adRep_baseLift_apply]`. Establish `h : (if F.η g = 1 then (x • Tm C) a b else -(x • Tm C) b.rev a.rev) = x * Tm C a b` using `by split_ifs`. Both sides reduce to the same expression.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Tm, Fin.rev]`. Rewrite using `[h]`. Distinguish the cases in `hw : wt a b = -1`. Rewrite using `[hw, _root_.zpow_neg_one, MonoidHom.comp_apply, ← map_inv, Matrix.smul_apply, smul_eq_mul, mul_assoc]`. Both sides reduce to the same expression.

Simplify using `[Tm_wt C a b hw]`.
-/
private theorem ad_Tm (g : Γ) (x : C) :
    adRep (F.rz C) g (x • Tm C) = (algebraMap O C ((F.Ψ g)⁻¹ : Oˣ) * x) • Tm C := by
  rw [rz_eq]
  ext a b
  rw [adRep_baseLift_apply]
  have h : (if F.η g = 1 then (x • Tm C) a b else -(x • Tm C) b.rev a.rev) = x * Tm C a b := by
    split_ifs
    · rfl
    · fin_cases a <;> fin_cases b <;> simp [Tm, Fin.rev]
  rw [h]
  by_cases hw : wt a b = -1
  · rw [hw, _root_.zpow_neg_one, MonoidHom.comp_apply, ← map_inv, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    rfl
  · simp [Tm_wt C a b hw]

end Point

/- English proof (translation)
Establish `h0` using `isPt_rz F hF g₁ (R := C)`. Establish `hent : ∀ x ∈ I, EntIn I (x • Tm C)` using `fun x hx a b => I.mul_mem_right _ hx`. Take `⟨r, hr⟩` from `exists_isDeform I (F.rz C) (fun g => ζ g • Tm C) hI (fun g => hent _ (hζ g)) (fun g h => by simp only [ad_Tm, hcoc, add_smul])`. Establish `hr2 : ∀ g, (r g).mat = (1 + ζ g • Tm C) * (F.rz C g).mat` using `fun g => (hr g).2`. Apply the tactic sequence `have hT' : ∀ a b, algebraMap O C (Tm O a b) = Tm C a b := fun a b => by fin_cases a <;> fin_cases b <;> simp [Tm]`.

Establish `hm : ∀ g a b, (r g).mat a b = (F.rz C g).mat a b + algebraMap O C (Tm O a b * psi F.Ψ b g) * ζ g`. Introduce `g a b`. Rewrite using `[hr2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, rz_mat, Matrix.mul_diagonal, map_mul, hT', Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : ζ F.c = 0`.

Establish `h1 : ζ 1 = 0` using `by simpa using hcoc 1 1`. Establish `h2` using `hcoc F.c F.c`. Rewrite `h2` using `[hF.csq, h1, hF.Ψc]`. Establish `h3 : algebraMap O C 2 * ζ F.c = 0`. Rewrite using `[map_ofNat, two_mul]`.

Simplify using `using h2.symm`. Conclude with `(hF.two.map (algebraMap O C)).mul_right_eq_zero.1 h3`. Use `⟨r, ⟨⟨⟨⟨fun g => (hr g).1, fun g a b => ?_⟩, fun v => ?_⟩, ⟨?_, ?_, ?_⟩⟩, fun n => ?_⟩, hm⟩` and prove the remaining obligations. Use `h0.red g a b` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.sub_apply]`.

Rewrite using `[hm, add_sub_right_comm]`. Conclude with `add_mem this (Ideal.mul_mem_left _ _ (hIm (hζ g)))`. Distinguish the cases in `hv : v ∈ F.Tb`. Take `⟨m, hmI, hmv⟩` from `hT v hv`. Take `⟨h, hh, hd⟩` from `isDeform_cob I ((F.rz C).comp (F.loc v)) ((-m) • Tm C) hI (hent _ (neg_mem hmI))`.

Establish `e : r.comp (F.loc v) = conjBy h ((F.rz C).comp (F.loc v))`. Use `deform_eq (fun g => ?_) hd` and prove the remaining obligations. Establish `e1 : cob ((F.rz C).comp (F.loc v)) ((-m) • Tm C) g = ζ (F.loc v g) • Tm C` using `by show (-m) • Tm C - adRep (F.rz C) (F.loc v g) ((-m) • Tm C) = _`. Rewrite using `[ad_Tm, hmv, ← sub_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `hr (F.loc v g)`. Rewrite using `[e]`. Use `(cond_conj F h fun a b => ?_).1 v _ (h0.loc v)` and prove the remaining obligations.

Rewrite using `[hh, add_sub_cancel_left]`. Conclude with `hIm (hent _ (neg_mem hmI) a b)`. Use `⟨fun e => absurd (e ▸ Set.mem_insert _ _) hv, fun e => absurd (Set.mem_insert_of_mem _ e) hv, fun _ s hs => ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ ((h0.loc v).2.2 hv s hs)` and prove the remaining obligations. Use `SemidirectProduct.ext (Units.ext ?_) (hr _).1` and prove the remaining obligations.

Use `hr2 (F.loc v s)` as an intermediate fact. Rewrite `this` using `[hU v hv s hs, zero_smul, add_zero, Matrix.one_mul]`. Conclude with `this`. Rewrite using `[hr2, hc, zero_smul, add_zero, Matrix.one_mul, h0.norm.atc]`. Use `h0.norm.z12` as an intermediate fact.

Simplify using `only [zmat, Matrix.sub_apply] at this ⊢`. Rewrite using `[hm, hm]`. Simplify `this` using `[Tm]`. Use `h0.norm.z21` as an intermediate fact. Simplify using `only [zmat, Matrix.sub_apply] at this ⊢`.

Rewrite using `[hm, hm]`. Establish `e : ∀ g, Tm O 1 0 * psi F.Ψ 0 g = F.Ψ g` using `fun g => by simp [Tm, psi, wt1]`. Rewrite using `[e, e, hN, add_sub_add_right_eq_sub, this]`. Establish `e : (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n))) = fun g => (1 + ζ g • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n)) * (F.rz C g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n))`. Use function extensionality and compare the values at `g`.

Rewrite using `[hr2, Matrix.map_mul]`. Rewrite using `[e]`. Conclude with `(hlc.comp fun x => (1 + x • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n))).mul (h0.cont n)`.
-/
private theorem exists_pt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) {C : Type} [CommRing C] [IsLocalRing C] [Algebra O C]
    [IsLocalHom (algebraMap O C)] (I : Ideal C) (hI : I * I = ⊥) (hIm : I ≤ maximalIdeal C) (ζ : Γ → C)
    (hζ : ∀ g, ζ g ∈ I) (hlc : IsLocallyConstant ζ)
    (hcoc : ∀ g h, ζ (g * h) = ζ g + algebraMap O C ((F.Ψ g)⁻¹ : Oˣ) * ζ h)
    (hU : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, ζ (F.loc v s) = 0)
    (hT : ∀ v ∈ F.Tb, ∃ m ∈ I, ∀ g : F.D v, ζ (F.loc v g) = algebraMap O C ((F.Ψ (F.loc v g))⁻¹ : Oˣ) * m - m)
    (hN : algebraMap O C (F.Ψ g₁) * ζ g₁ = algebraMap O C (F.Ψ (gstar F.c g₁)) * ζ (gstar F.c g₁)) :
    ∃ r : Γ →* GG 3 C, F.IsPt g₁ r ∧
      ∀ g a b, (r g).mat a b = (F.rz C g).mat a b + algebraMap O C (Tm O a b * psi F.Ψ b g) * ζ g := by
  have h0 := isPt_rz F hF g₁ (R := C)
  have hent : ∀ x ∈ I, EntIn I (x • Tm C) := fun x hx a b => I.mul_mem_right _ hx
  obtain ⟨r, hr⟩ := exists_isDeform I (F.rz C) (fun g => ζ g • Tm C) hI (fun g => hent _ (hζ g))
    (fun g h => by simp only [ad_Tm, hcoc, add_smul])
  have hr2 : ∀ g, (r g).mat = (1 + ζ g • Tm C) * (F.rz C g).mat := fun g => (hr g).2
  have hT' : ∀ a b, algebraMap O C (Tm O a b) = Tm C a b := fun a b => by
    fin_cases a <;> fin_cases b <;> simp [Tm]
  have hm : ∀ g a b, (r g).mat a b = (F.rz C g).mat a b + algebraMap O C (Tm O a b * psi F.Ψ b g) * ζ g := by
    intro g a b
    rw [hr2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, rz_mat, Matrix.mul_diagonal, map_mul, hT',
      Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : ζ F.c = 0 := by
    have h1 : ζ 1 = 0 := by simpa using hcoc 1 1
    have h2 := hcoc F.c F.c
    rw [hF.csq, h1, hF.Ψc] at h2
    have h3 : algebraMap O C 2 * ζ F.c = 0 := by
      rw [map_ofNat, two_mul]; simpa using h2.symm
    exact (hF.two.map (algebraMap O C)).mul_right_eq_zero.1 h3
  refine ⟨r, ⟨⟨⟨⟨fun g => (hr g).1, fun g a b => ?_⟩, fun v => ?_⟩, ⟨?_, ?_, ?_⟩⟩, fun n => ?_⟩, hm⟩
  · have := h0.red g a b
    rw [Matrix.sub_apply] at this ⊢
    rw [hm, add_sub_right_comm]
    exact add_mem this (Ideal.mul_mem_left _ _ (hIm (hζ g)))
  · by_cases hv : v ∈ F.Tb
    · obtain ⟨m, hmI, hmv⟩ := hT v hv
      obtain ⟨h, hh, hd⟩ := isDeform_cob I ((F.rz C).comp (F.loc v)) ((-m) • Tm C) hI (hent _ (neg_mem hmI))
      have e : r.comp (F.loc v) = conjBy h ((F.rz C).comp (F.loc v)) := by
        refine deform_eq (fun g => ?_) hd
        have e1 : cob ((F.rz C).comp (F.loc v)) ((-m) • Tm C) g = ζ (F.loc v g) • Tm C := by
          show (-m) • Tm C - adRep (F.rz C) (F.loc v g) ((-m) • Tm C) = _
          rw [ad_Tm, hmv, ← sub_smul]
          congr 1
          ring
        rw [e1]
        exact hr (F.loc v g)
      rw [e]
      refine (cond_conj F h fun a b => ?_).1 v _ (h0.loc v)
      rw [hh, add_sub_cancel_left]
      exact hIm (hent _ (neg_mem hmI) a b)
    · refine ⟨fun e => absurd (e ▸ Set.mem_insert _ _) hv, fun e => absurd (Set.mem_insert_of_mem _ e) hv,
        fun _ s hs => ?_⟩
      refine Eq.trans ?_ ((h0.loc v).2.2 hv s hs)
      refine SemidirectProduct.ext (Units.ext ?_) (hr _).1
      have := hr2 (F.loc v s)
      rw [hU v hv s hs, zero_smul, add_zero, Matrix.one_mul] at this
      exact this
  · rw [hr2, hc, zero_smul, add_zero, Matrix.one_mul, h0.norm.atc]
  · have := h0.norm.z12
    simp only [zmat, Matrix.sub_apply] at this ⊢
    rw [hm, hm]
    simpa [Tm] using this
  · have := h0.norm.z21
    simp only [zmat, Matrix.sub_apply] at this ⊢
    rw [hm, hm]
    have e : ∀ g, Tm O 1 0 * psi F.Ψ 0 g = F.Ψ g := fun g => by simp [Tm, psi, wt1]
    rw [e, e, hN, add_sub_add_right_eq_sub, this]
  · have e : (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n))) = fun g =>
        (1 + ζ g • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n)) *
          (F.rz C g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n)) := by
      funext g
      rw [hr2, Matrix.map_mul]
    rw [e]
    exact (hlc.comp fun x => (1 + x • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n))).mul (h0.cont n)

/- English proof (translation)
Use `letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)`. Use `haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩`. Use `haveI : IsCO O (TrivSqZeroExt O M) := tsz_isCO`. Establish `hmul : ∀ (c : O) (m : M), algebraMap O (TrivSqZeroExt O M) c * TrivSqZeroExt.inr m = TrivSqZeroExt.inr (c • m)` using `fun c m => TrivSqZeroExt.inl_mul_inr c m`. Set `I : Ideal (TrivSqZeroExt O M)` to `RingHom.ker (TrivSqZeroExt.fstHom O O M)`.

Establish `hI : ∀ x, x ∈ I ↔ x.fst = 0` using `fun x => Iff.rfl`. Take `⟨r, hr, hm⟩` from `exists_pt F hF g₁ I (by`. Rewrite using `[eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[hI]`.

Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [hx, hy])`. Use the proof step `(fun x hx => by rw [tsz_mem_max, (hI x).1 hx]; exact zero_mem _)`. Use the proof step `(fun g => TrivSqZeroExt.inr (n g)) (fun g => rfl) (hlc.comp _)`. Use the proof step `(fun g h => by rw [hmul, hcoc, TrivSqZeroExt.inr_add])`.

Use the proof step `(fun v hv s hs => by rw [hU v hv s hs, TrivSqZeroExt.inr_zero])`. Use the proof step `(fun v hv => by`. Take `⟨m, hm⟩` from `hT v hv`. Conclude with `⟨TrivSqZeroExt.inr m, rfl, fun g => by rw [hmul, hm, TrivSqZeroExt.inr_sub]⟩)`. Use the proof step `(by rw [hmul, hmul, hN])`.

Simplify using `only [hmul] at hm`. Take `⟨f, hf, -⟩` from `hu.univ _ r hr`. Establish `e1 : ∀ g a b, f ((u g).mat a b) = (r g).mat a b` using `fun g a b => congrArg (fun r : Γ →* GG 3 (TrivSqZeroExt O M) => (r g).mat a b) hf`. Establish `hX : ∀ i, (f.comp W.π) (MvPowerSeries.X i) = TrivSqZeroExt.inr ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i))` using `fun i => by`. Establish `e2 : f ((F.rz R (g i)).mat (a i) (b i)) = (F.rz _ (g i)).mat (a i) (b i)` using `f.commutes _`.

Use `show f (W.z i) = _`. Rewrite using `[hz, map_sub, e1, e2, hm, add_sub_cancel_left]`. Establish `key : ∀ p, (f (W.π p)).snd = ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p • ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i))` using `fun p => by`. Use `map_lin (f.comp W.π) (fun i j => by rw [hX, hX, TrivSqZeroExt.inr_mul_inr]) p` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply]`.

Rewrite using `[this]`. Simplify using `only [hX, TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_inr]`. Use `⟨fun p hp => by rw [← key, hp, map_zero, TrivSqZeroExt.snd_zero], fun h => funext fun s => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `W.surj ((u s).mat 1 0)`. Establish `h1` using `key p`.

Simplify using `only [h, smul_zero, Finset.sum_const_zero] at h1`. Rewrite `h1` using `[hp, e1, hm, rz_mat]`. Establish `h2 : (F.Ψ s : O) • n s = 0` using `by simpa [Tm, psi, wt1] using h1`. Conclude with `((F.Ψ s).isUnit.smul_eq_zero).1 h2`.
-/
private theorem coord
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R) (hu : F.IsUniv g₁ u)
    (W : WPres O ℤ R) (g : W.σ → Γ) (a b : W.σ → Fin 3)
    (hz : ∀ i, W.z i = (u (g i)).mat (a i) (b i) - (F.rz R (g i)).mat (a i) (b i))
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] (n : Γ → M) (hlc : IsLocallyConstant n)
    (hcoc : ∀ g h, n (g * h) = n g + (((F.Ψ g)⁻¹ : Oˣ) : O) • n h)
    (hU : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, n (F.loc v s) = 0)
    (hT : ∀ v ∈ F.Tb, ∃ m, ∀ g : F.D v, n (F.loc v g) = (((F.Ψ (F.loc v g))⁻¹ : Oˣ) : O) • m - m)
    (hN : (F.Ψ g₁ : O) • n g₁ = (F.Ψ (gstar F.c g₁) : O) • n (gstar F.c g₁)) :
    (∀ p, W.π p = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p •
      ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) = 0) ∧
    ((∀ i, (Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i) = 0) → n = 0) := by
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  haveI : IsCO O (TrivSqZeroExt O M) := tsz_isCO
  have hmul : ∀ (c : O) (m : M), algebraMap O (TrivSqZeroExt O M) c * TrivSqZeroExt.inr m =
      TrivSqZeroExt.inr (c • m) := fun c m => TrivSqZeroExt.inl_mul_inr c m
  let I : Ideal (TrivSqZeroExt O M) := RingHom.ker (TrivSqZeroExt.fstHom O O M)
  have hI : ∀ x, x ∈ I ↔ x.fst = 0 := fun x => Iff.rfl
  obtain ⟨r, hr, hm⟩ := exists_pt F hF g₁ I
    (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [hI] at hx hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx, hy])
    (fun x hx => by rw [tsz_mem_max, (hI x).1 hx]; exact zero_mem _)
    (fun g => TrivSqZeroExt.inr (n g)) (fun g => rfl) (hlc.comp _)
    (fun g h => by rw [hmul, hcoc, TrivSqZeroExt.inr_add])
    (fun v hv s hs => by rw [hU v hv s hs, TrivSqZeroExt.inr_zero])
    (fun v hv => by
      obtain ⟨m, hm⟩ := hT v hv
      exact ⟨TrivSqZeroExt.inr m, rfl, fun g => by rw [hmul, hm, TrivSqZeroExt.inr_sub]⟩)
    (by rw [hmul, hmul, hN])
  simp only [hmul] at hm
  obtain ⟨f, hf, -⟩ := hu.univ _ r hr
  have e1 : ∀ g a b, f ((u g).mat a b) = (r g).mat a b := fun g a b =>
    congrArg (fun r : Γ →* GG 3 (TrivSqZeroExt O M) => (r g).mat a b) hf
  have hX : ∀ i, (f.comp W.π) (MvPowerSeries.X i) =
      TrivSqZeroExt.inr ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) := fun i => by
    have e2 : f ((F.rz R (g i)).mat (a i) (b i)) = (F.rz _ (g i)).mat (a i) (b i) := f.commutes _
    show f (W.z i) = _
    rw [hz, map_sub, e1, e2, hm, add_sub_cancel_left]
  have key : ∀ p, (f (W.π p)).snd = ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p •
      ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) := fun p => by
    have := map_lin (f.comp W.π) (fun i j => by rw [hX, hX, TrivSqZeroExt.inr_mul_inr]) p
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp only [hX, TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, zero_add,
      TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_inr]
  refine ⟨fun p hp => by rw [← key, hp, map_zero, TrivSqZeroExt.snd_zero], fun h => funext fun s => ?_⟩
  obtain ⟨p, hp⟩ := W.surj ((u s).mat 1 0)
  have h1 := key p
  simp only [h, smul_zero, Finset.sum_const_zero] at h1
  rw [hp, e1, hm, rz_mat] at h1
  have h2 : (F.Ψ s : O) • n s = 0 := by simpa [Tm, psi, wt1] using h1
  exact ((F.Ψ s).isUnit.smul_eq_zero).1 h2

/- English proof (translation)
Establish `hρ : ∀ g (m : OQ a), oqRep Ψ⁻¹ a g m = (((Ψ g)⁻¹ : Oˣ) : O) • m` using `fun _ _ => rfl`. Set `l : (Γ → OQ a) →ₗ[O] OQ a` to `(Ψ g₁ : O) • LinearMap.proj g₁ - (Ψ (gstar c g₁) : O) • LinearMap.proj (gstar c g₁)`. Establish `hl : ∀ y, l y = (Ψ g₁ : O) • y g₁ - (Ψ (gstar c g₁) : O) • y (gstar c g₁)` using `fun _ => rfl`. Establish `hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹` using `by simp [gstar, hc]`. Establish `hw : IsUnit ((((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁)`.

Establish `: (((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁ = -(((Ψ g₁)⁻¹ : Oˣ) : O) * ((Ψ g₁ : O) ^ 2 - 1)`. Take the linear combination `(Ψ g₁ : O) * (Ψ g₁).inv_mul`. Rewrite using `[this]`. Conclude with `(Units.isUnit _).neg.mul hg`. Take `⟨w, hw⟩` from `hw`.

Establish `hld : ∀ m, l (d0 (oqRep Ψ⁻¹ a) m) = (w : O) • m` using `fun m => by`. Rewrite using `[hl, amitsur_d0_apply, amitsur_d0_apply, hρ, hρ, smul_sub, smul_sub, smul_smul, smul_smul, Units.mul_inv, Units.mul_inv, hs, hw, sub_smul]`. Normalize the expressions using the abelian group laws. Set `N₀ : (Γ → OQ a) →ₗ[O] (Γ → OQ a)` to `LinearMap.id - (d0 (oqRep Ψ⁻¹ a)).comp (((w⁻¹ : Oˣ) : O) • l)`. Establish `hN₀ : ∀ y, N₀ y = y - d0 (oqRep Ψ⁻¹ a) (((w⁻¹ : Oˣ) : O) • l y)` using `fun _ => rfl`.

Use `⟨Submodule.liftQ _ (N₀.comp (Z1 (oqRep Ψ⁻¹ a)).subtype) ?_, fun z => ⟨_, hN₀ z.1⟩, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨m, hm⟩ show N₀ z.1 = 0`. Establish `hm' : z.1 = d0 (oqRep Ψ⁻¹ a) m` using `hm.symm`. Rewrite using `[hN₀, hm', hld, smul_smul, Units.inv_mul, one_smul, sub_self]`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite using `[← sub_eq_zero, ← hl]`. Use `show l (N₀ z.1) = 0`. Rewrite using `[hN₀, map_sub, hld, smul_smul, Units.mul_inv, one_smul, sub_self]`.
-/
private theorem exists_norm {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ) (a : O)
    (c g₁ : Γ) (hc : Ψ c = 1) (hg : IsUnit ((Ψ g₁ : O) ^ 2 - 1)) :
    ∃ N : H1 (oqRep Ψ⁻¹ a) →ₗ[O] (Γ → OQ a),
      (∀ z : Z1 (oqRep Ψ⁻¹ a), ∃ m, N (Submodule.Quotient.mk z) = z.1 - d0 (oqRep Ψ⁻¹ a) m) ∧
      ∀ x, (Ψ g₁ : O) • N x g₁ = (Ψ (gstar c g₁) : O) • N x (gstar c g₁) := by
  have hρ : ∀ g (m : OQ a), oqRep Ψ⁻¹ a g m = (((Ψ g)⁻¹ : Oˣ) : O) • m := fun _ _ => rfl
  let l : (Γ → OQ a) →ₗ[O] OQ a :=
    (Ψ g₁ : O) • LinearMap.proj g₁ - (Ψ (gstar c g₁) : O) • LinearMap.proj (gstar c g₁)
  have hl : ∀ y, l y = (Ψ g₁ : O) • y g₁ - (Ψ (gstar c g₁) : O) • y (gstar c g₁) := fun _ => rfl
  have hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by simp [gstar, hc]
  have hw : IsUnit ((((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁) := by
    have : (((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁ = -(((Ψ g₁)⁻¹ : Oˣ) : O) * ((Ψ g₁ : O) ^ 2 - 1) := by
      linear_combination (Ψ g₁ : O) * (Ψ g₁).inv_mul
    rw [this]
    exact (Units.isUnit _).neg.mul hg
  obtain ⟨w, hw⟩ := hw
  have hld : ∀ m, l (d0 (oqRep Ψ⁻¹ a) m) = (w : O) • m := fun m => by
    rw [hl, amitsur_d0_apply, amitsur_d0_apply, hρ, hρ, smul_sub, smul_sub, smul_smul, smul_smul, Units.mul_inv, Units.mul_inv,
      hs, hw, sub_smul]
    abel
  let N₀ : (Γ → OQ a) →ₗ[O] (Γ → OQ a) := LinearMap.id - (d0 (oqRep Ψ⁻¹ a)).comp (((w⁻¹ : Oˣ) : O) • l)
  have hN₀ : ∀ y, N₀ y = y - d0 (oqRep Ψ⁻¹ a) (((w⁻¹ : Oˣ) : O) • l y) := fun _ => rfl
  refine ⟨Submodule.liftQ _ (N₀.comp (Z1 (oqRep Ψ⁻¹ a)).subtype) ?_, fun z => ⟨_, hN₀ z.1⟩, fun x => ?_⟩
  · rintro z ⟨m, hm⟩
    show N₀ z.1 = 0
    have hm' : z.1 = d0 (oqRep Ψ⁻¹ a) m := hm.symm
    rw [hN₀, hm', hld, smul_smul, Units.inv_mul, one_smul, sub_self]
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← sub_eq_zero, ← hl]
    show l (N₀ z.1) = 0
    rw [hN₀, map_sub, hld, smul_smul, Units.mul_inv, one_smul, sub_self]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact h`. Consider the case `zero => exact ⟨0, rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨0, fun _ => by simp⟩⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨z, rfl, h1, h2⟩` from `hx`.

Take `⟨z', rfl, h1', h2'⟩` from `hy`. Use `⟨z + z', rfl, fun v hv s hs => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_add, Pi.add_apply, h1 v hv s hs, h1' v hv s hs, add_zero]`. Take `⟨m, hm⟩` from `h2 v hv`. Take `⟨m', hm'⟩` from `h2' v hv`.

Conclude with `⟨m + m', fun g => by rw [Submodule.coe_add, Pi.add_apply, hm, hm', map_add]; abel⟩`. Consider the case `smul c x _ hx`. Take `⟨z, rfl, h1, h2⟩` from `hx`. Use `⟨c • z, rfl, fun v hv s hs => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Pi.smul_apply, h1 v hv s hs, smul_zero]`.

Take `⟨m, hm⟩` from `h2 v hv`. Conclude with `⟨c • m, fun g => by rw [Submodule.coe_smul, Pi.smul_apply, hm, map_smul, smul_sub]⟩`.
-/
private theorem exists_rep {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    [TopologicalSpace Γ] (F : Frame O G Γ ι) (a : O) (x : H1 (oqRep F.Ψ⁻¹ a)) (hx : x ∈ F.ShaO a) :
    ∃ z : Z1 (oqRep F.Ψ⁻¹ a), x = Submodule.Quotient.mk z ∧
      (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z.1 (F.loc v s) = 0) ∧
      ∀ v ∈ F.Tb, ∃ m, ∀ g : F.D v, z.1 (F.loc v g) = oqRep F.Ψ⁻¹ a (F.loc v g) m - m := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨0, fun _ => by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl, h1, h2⟩ := hx
    obtain ⟨z', rfl, h1', h2'⟩ := hy
    refine ⟨z + z', rfl, fun v hv s hs => ?_, fun v hv => ?_⟩
    · rw [Submodule.coe_add, Pi.add_apply, h1 v hv s hs, h1' v hv s hs, add_zero]
    · obtain ⟨m, hm⟩ := h2 v hv
      obtain ⟨m', hm'⟩ := h2' v hv
      exact ⟨m + m', fun g => by rw [Submodule.coe_add, Pi.add_apply, hm, hm', map_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨z, rfl, h1, h2⟩ := hx
    refine ⟨c • z, rfl, fun v hv s hs => ?_, fun v hv => ?_⟩
    · rw [Submodule.coe_smul, Pi.smul_apply, h1 v hv s hs, smul_zero]
    · obtain ⟨m, hm⟩ := h2 v hv
      exact ⟨c • m, fun g => by rw [Submodule.coe_smul, Pi.smul_apply, hm, map_smul, smul_sub]⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ha hϖ`. Establish `hle : maximalIdeal O ^ n ≤ Ideal.span {a}`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]`. Conclude with `hn.dvd`.

Use `(hf n).comp fun y => (show OQ a from Ideal.Quotient.factor hle y) * m` as an intermediate fact. Use `(congrArg IsLocallyConstant (funext fun g => ?_)).mp this` and prove the remaining obligations. Conclude with `(Algebra.smul_def (f g) m).symm`.
-/
private theorem lc_smul {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace Γ]
    (f : Γ → O) (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (f g))
    (a : O) (ha : a ≠ 0) (m : OQ a) : IsLocallyConstant fun g => f g • m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hle : maximalIdeal O ^ n ≤ Ideal.span {a} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact hn.dvd
  have := (hf n).comp fun y => (show OQ a from Ideal.Quotient.factor hle y) * m
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp this
  exact (Algebra.smul_def (f g) m).symm

end UpperTheory.V.UnitaryThreeInertia.MP

open UpperTheory.V.UnitaryThreeInertia.MP in
/- English proof (translation)
Introduce `O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu W hW a ha`. Use `choose g p q _ hwt hz using hW.var`. Take `⟨N, hN1, hN2⟩` from `exists_norm F.Ψ a F.c g₁ hF.Ψc hg.2`. Use `haveI : Module.Finite O (OQ a) := inferInstanceAs (Module.Finite O (O ⧸ Ideal.span {a}))`. Establish `hρ : ∀ g (m : OQ a), oqRep F.Ψ⁻¹ a g m = (((F.Ψ g)⁻¹ : Oˣ) : O) • m` using `fun _ _ => rfl`.

Set `d : F.ShaO a →+ (W.σ → OQ a)` to `{ toFun := fun x i => (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i) map_zero' := funext fun i => by simp map_add' := fun x y => funext fun i => by simp }`. Establish `key : ∀ x : F.ShaO a, (∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f • d x i = 0) ∧ ((∀ i, d x i = 0) → N x.1 = 0)` using `fun x => by`. Take `⟨z, hxz, h1, h2⟩` from `exists_rep F a x.1 x.2`. Take `⟨m, hm⟩` from `hN1 z`. Rewrite `hm` using `[← hxz]`.

Establish `hn : ∀ s, N x.1 s = z.1 s - ((((F.Ψ s)⁻¹ : Oˣ) : O) • m - m)` using `fun s => congrFun hm s`. Use `coord F hF g₁ u hu W g p q hz (N x.1) ?_ (fun s t => ?_) (fun v hv s hs => ?_) (fun v hv => ?_) (hN2 _)` and prove the remaining obligations. Rewrite using `[show N x.1 = _ from funext hn]`. Establish `hΨ : IsLocallyConstant fun s => (((F.Ψ s)⁻¹ : Oˣ) : O) • m` using `lc_smul _ (fun n => by simpa only [Function.comp_def, map_inv] using (hF.Ψ_cont n).comp_continuous continuous_inv) a ha m`. Conclude with `((IsLocallyConstant.iff_continuous _).2 z.2.1).sub (hΨ.sub (IsLocallyConstant.const m))`.

Rewrite using `[hn, hn, hn, z.2.2, hρ, map_mul, mul_inv, Units.val_mul, mul_smul, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `: F.Ψ (F.loc v s) = 1` using `hF.teich v hv s hs`. Rewrite using `[hn, h1 v hv s hs, this]`. Simplify using the standard rewrite rules.

Take `⟨m', hm'⟩` from `h2 v hv`. Conclude with `⟨m' - m, fun s => by rw [hn, hm', hρ, smul_sub]; abel⟩`. Use `⟨d, (injective_iff_map_eq_zero d).2 fun x hx => ?_, fun x i hi => ?_, fun x => (key x).1⟩` and prove the remaining obligations. Establish `h0` using `(key x).2 fun i => congrFun hx i`. Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ x.1`.

Take `⟨m, hm⟩` from `hN1 z`. Rewrite `hm` using `[hz, h0, eq_comm, sub_eq_zero]`. Conclude with `Subtype.ext (hz.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨m, hm.symm⟩))`. Use `show (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i) = 0`. Rewrite using `[Tm_wt O _ _ (hwt i ▸ hi), zero_mul, zero_smul]`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.mprime_coord :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∀ a : O, a ≠ 0 → ∃ d : F.ShaO a →+ (W.σ → O ⧸ Ideal.span {a}), Function.Injective d ∧
      (∀ x i, W.wt i ≠ -1 → d x i = 0) ∧ ∀ x f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f • d x i = 0 := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu W hW a ha
  choose g p q _ hwt hz using hW.var
  obtain ⟨N, hN1, hN2⟩ := exists_norm F.Ψ a F.c g₁ hF.Ψc hg.2
  haveI : Module.Finite O (OQ a) := inferInstanceAs (Module.Finite O (O ⧸ Ideal.span {a}))
  have hρ : ∀ g (m : OQ a), oqRep F.Ψ⁻¹ a g m = (((F.Ψ g)⁻¹ : Oˣ) : O) • m := fun _ _ => rfl
  let d : F.ShaO a →+ (W.σ → OQ a) :=
    { toFun := fun x i => (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i)
      map_zero' := funext fun i => by simp
      map_add' := fun x y => funext fun i => by simp }
  have key : ∀ x : F.ShaO a, (∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f • d x i = 0) ∧
      ((∀ i, d x i = 0) → N x.1 = 0) := fun x => by
    obtain ⟨z, hxz, h1, h2⟩ := exists_rep F a x.1 x.2
    obtain ⟨m, hm⟩ := hN1 z
    rw [← hxz] at hm
    have hn : ∀ s, N x.1 s = z.1 s - ((((F.Ψ s)⁻¹ : Oˣ) : O) • m - m) := fun s => congrFun hm s
    refine coord F hF g₁ u hu W g p q hz (N x.1) ?_ (fun s t => ?_) (fun v hv s hs => ?_) (fun v hv => ?_) (hN2 _)
    · rw [show N x.1 = _ from funext hn]
      have hΨ : IsLocallyConstant fun s => (((F.Ψ s)⁻¹ : Oˣ) : O) • m :=
        lc_smul _ (fun n => by simpa only [Function.comp_def, map_inv] using (hF.Ψ_cont n).comp_continuous continuous_inv) a ha m
      exact ((IsLocallyConstant.iff_continuous _).2 z.2.1).sub (hΨ.sub (IsLocallyConstant.const m))
    · rw [hn, hn, hn, z.2.2, hρ, map_mul, mul_inv, Units.val_mul, mul_smul, smul_sub, smul_sub]
      abel
    · have : F.Ψ (F.loc v s) = 1 := hF.teich v hv s hs
      rw [hn, h1 v hv s hs, this]
      simp
    · obtain ⟨m', hm'⟩ := h2 v hv
      exact ⟨m' - m, fun s => by rw [hn, hm', hρ, smul_sub]; abel⟩
  refine ⟨d, (injective_iff_map_eq_zero d).2 fun x hx => ?_, fun x i hi => ?_, fun x => (key x).1⟩
  · have h0 := (key x).2 fun i => congrFun hx i
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    obtain ⟨m, hm⟩ := hN1 z
    rw [hz, h0, eq_comm, sub_eq_zero] at hm
    exact Subtype.ext (hz.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨m, hm.symm⟩))
  · show (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i) = 0
    rw [Tm_wt O _ _ (hwt i ▸ hi), zero_mul, zero_smul]
