import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Establish `hs : σ ∈ MulAction.stabilizer (G F Ω) z` using `h`. Conclude with `(MulAction.stabilizer (G F Ω) z).zpow_mem hs n`.
-/
private theorem zpow_mem_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ z = z) (n : ℤ) : (σ ^ n) z = z := by
  have hs : σ ∈ MulAction.stabilizer (G F Ω) z := h
  exact (MulAction.stabilizer (G F Ω) z).zpow_mem hs n

/- English proof (translation)
Establish `e : φ ^ (2 : ℤ) = φ * φ` using `zpow_two φ`. Rewrite using `[e, AlgEquiv.mul_apply]`. Break down `h with h | h` into its components or cases. Rewrite using `[h, h]`. Rewrite using `[h, map_neg, h, neg_neg]`.
-/
private theorem sq_apply_of_pm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (φ : G F Ω) (z : Ω)
    (h : φ z = z ∨ φ z = -z) : (φ ^ (2 : ℤ)) z = z := by
  have e : φ ^ (2 : ℤ) = φ * φ := zpow_two φ
  rw [e, AlgEquiv.mul_apply]
  rcases h with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

/- English proof (translation)
Break down `Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩` into its components or cases. Rewrite using `[hj, ← two_mul, zpow_mul]`. Conclude with `zpow_mem_fix _ x (sq_apply_of_pm φ x hφx) j`. It suffices to derive a contradiction. Establish `hφe' : φ e = -e`.

Break down `hφe with h | h` into its components or cases. Conclude with `absurd (zpow_mem_fix φ e h k) hk`. Conclude with `h`. Rewrite `hm` using `[hj, zpow_add, zpow_one, zpow_mul, AlgEquiv.mul_apply, hφe', map_neg, zpow_mem_fix _ e (sq_apply_of_pm φ e hφe) j]`. Establish `h2 : (2 : Ω) * e = 0` using `by linear_combination -hm`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `two_ne_zero h`. Conclude with `he0 h`.
-/
private theorem fix_of_parity {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω] (φ : G F Ω) (e x : Ω)
    (he0 : e ≠ 0) (hφe : φ e = e ∨ φ e = -e) (hφx : φ x = x ∨ φ x = -x) (k m : ℤ)
    (hk : (φ ^ k) e ≠ e) (hm : (φ ^ m) e = e) : (φ ^ m) x = x := by
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, zpow_mul]
    exact zpow_mem_fix _ x (sq_apply_of_pm φ x hφx) j
  · exfalso
    have hφe' : φ e = -e := by
      rcases hφe with h | h
      · exact absurd (zpow_mem_fix φ e h k) hk
      · exact h
    rw [hj, zpow_add, zpow_one, zpow_mul, AlgEquiv.mul_apply, hφe', map_neg,
      zpow_mem_fix _ e (sq_apply_of_pm φ e hφe) j] at hm
    have h2 : (2 : Ω) * e = 0 := by linear_combination -hm
    rcases mul_eq_zero.1 h2 with h | h
    · exact two_ne_zero h
    · exact he0 h

/- English proof (translation)
Rewrite `h` using `[map_pow]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.1 h`.
-/
private theorem pm_of_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ (z ^ 2) = z ^ 2) : σ z = z ∨ σ z = -z := by
  rw [map_pow] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

/- English proof (translation)
Introduce `y`. Establish `h2 : (2 : Y) ≠ 0` using `two_ne_zero`. Take `⟨a, haa⟩ : ∃ a : Y, a = (y + IsCMField.complexConj Y y) / 2` from `⟨_, rfl⟩`. Take `⟨b, hbb⟩ : ∃ b : Y, b = (y - IsCMField.complexConj Y y) / (2 * e)` from `⟨_, rfl⟩`. Establish `ha : IsCMField.complexConj Y a = a`.

Rewrite using `[haa, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]`. Establish `hb : IsCMField.complexConj Y b = b`. Rewrite using `[hbb, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hce]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hy : y = a + e * b`. Rewrite using `[haa, hbb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hfa : g (algebraMap Y Ω a) = algebraMap Y Ω a` using `g.commutes ⟨a, (IsCMField.complexConj_eq_self_iff Y a).1 ha⟩`.

Establish `hfb : g (algebraMap Y Ω b) = algebraMap Y Ω b` using `g.commutes ⟨b, (IsCMField.complexConj_eq_self_iff Y b).1 hb⟩`. Rewrite using `[hy, map_add, map_mul, map_add, map_mul, hfa, hfb, hg]`.
-/
private theorem fixes_of_imag {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω]
    (e : Y) (he : e ≠ 0) (hce : IsCMField.complexConj Y e = -e) (g : G (maximalRealSubfield Y) Ω)
    (hg : g (algebraMap Y Ω e) = algebraMap Y Ω e) : Fixes Y g := by
  intro y
  have h2 : (2 : Y) ≠ 0 := two_ne_zero
  obtain ⟨a, haa⟩ : ∃ a : Y, a = (y + IsCMField.complexConj Y y) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : Y, b = (y - IsCMField.complexConj Y y) / (2 * e) := ⟨_, rfl⟩
  have ha : IsCMField.complexConj Y a = a := by
    rw [haa, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
  have hb : IsCMField.complexConj Y b = b := by
    rw [hbb, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hce]
    field_simp
    ring
  have hy : y = a + e * b := by
    rw [haa, hbb]
    field_simp
    ring
  have hfa : g (algebraMap Y Ω a) = algebraMap Y Ω a :=
    g.commutes ⟨a, (IsCMField.complexConj_eq_self_iff Y a).1 ha⟩
  have hfb : g (algebraMap Y Ω b) = algebraMap Y Ω b :=
    g.commutes ⟨b, (IsCMField.complexConj_eq_self_iff Y b).1 hb⟩
  rw [hy, map_add, map_mul, map_add, map_mul, hfa, hfb, hg]

/- English proof (translation)
Introduce `hD Y Ω _ _ _ _ _ _ A u hu x a hx hI hg h hh`. Take `⟨g, hgD, hgY⟩` from `hg`. Use `haveI : IsAlgClosure (maximalRealSubfield Y) Ω := IsAlgClosure.ofAlgebraic _ Y Ω`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield Y)), IsPlaceOver A v := by`.

Use `⟨⟨u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y)), Ideal.IsPrime.comap _, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `hb`. Conclude with `u.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)`. Introduce `z`. Conclude with `hu (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y) z)`.

Take `⟨φ, hφ⟩` from `exists_isFrob hv`. Choose the witnesses or unpack the hypotheses as in `⟨e, he0, hce⟩ : ∃ e : Y, e ≠ 0 ∧ IsCMField.complexConj Y e = -e := by`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : Y, IsCMField.complexConj Y y ≠ y := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `IsCMField.complexConj_ne_one Y (AlgEquiv.ext hc)`. Use `⟨y - IsCMField.complexConj Y y, sub_ne_zero.2 (Ne.symm hy), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, IsCMField.complexConj_apply_apply, neg_sub]`. Establish `hXf : ({x, algebraMap Y Ω e} : Set Ω).Finite` using `Set.toFinite _`. Establish `hIX : ∀ τ ∈ (Ine A : Subgroup (G (maximalRealSubfield Y) Ω)), ∀ y ∈ ({x, algebraMap Y Ω e} : Set Ω), τ y = y`.

Introduce `τ hτ y hy`. Break down `hy with rfl | rfl` into its components or cases. Conclude with `(hI τ hτ).2`. Conclude with `(hI τ hτ).1 e`. Set `h' : G (maximalRealSubfield Y) Ω` to `AlgEquiv.restrictScalars _ h`.

Establish `hh' : h' ∈ Dec A` using `(GlobalTheory.AboveL.mem_dec_congr A h' h (fun _ => rfl)).2 hh`. Take `⟨k, hk⟩` from `hD _ Ω A v hv φ hφ _ hXf hIX g hgD`. Take `⟨m, hm⟩` from `hD _ Ω A v hv φ hφ _ hXf hIX h' hh'`. Establish `hE0 : algebraMap Y Ω e ≠ 0` using `(map_ne_zero _).2 he0`. Establish `hpmE : φ (algebraMap Y Ω e) = algebraMap Y Ω e ∨ φ (algebraMap Y Ω e) = -algebraMap Y Ω e`.

Apply `pm_of_sq` to reduce the goal to its premises. Establish `hs : e ^ 2 ∈ maximalRealSubfield Y`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_pow, hce, neg_sq]`. Rewrite using `[← map_pow]`. Conclude with `φ.commutes (⟨e ^ 2, hs⟩ : maximalRealSubfield Y)`.

Establish `hpmx : φ x = x ∨ φ x = -x`. Apply `pm_of_sq` to reduce the goal to its premises. Rewrite using `[hx, map_intCast]`. Establish `hkE : (φ ^ k) (algebraMap Y Ω e) ≠ algebraMap Y Ω e`. Rewrite using `[← hk _ (by simp)]`.

Introduce `hgE`. Conclude with `hgY (fixes_of_imag e he0 hce g hgE)`. Establish `hmE : (φ ^ m) (algebraMap Y Ω e) = algebraMap Y Ω e`. Rewrite using `[← hm _ (by simp)]`. Conclude with `h.commutes e`.

Establish `hfx` using `fix_of_parity φ _ x hE0 hpmE hpmx k m hkE hmE`. Rewrite `hfx` using `[← hm x (by simp)]`. Conclude with `hfx`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.inertSplit :
    DecGen → InertSplit := by
  intro hD Y Ω _ _ _ _ _ _ A u hu x a hx hI hg h hh
  obtain ⟨g, hgD, hgY⟩ := hg
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω := IsAlgClosure.ofAlgebraic _ Y Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield Y)), IsPlaceOver A v := by
    refine ⟨⟨u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y)), Ideal.IsPrime.comap _, ?_⟩, ?_⟩
    · intro hb
      exact u.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    · intro z
      exact hu (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y) z)
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  obtain ⟨e, he0, hce⟩ : ∃ e : Y, e ≠ 0 ∧ IsCMField.complexConj Y e = -e := by
    obtain ⟨y, hy⟩ : ∃ y : Y, IsCMField.complexConj Y y ≠ y := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one Y (AlgEquiv.ext hc)
    refine ⟨y - IsCMField.complexConj Y y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hXf : ({x, algebraMap Y Ω e} : Set Ω).Finite := Set.toFinite _
  have hIX : ∀ τ ∈ (Ine A : Subgroup (G (maximalRealSubfield Y) Ω)),
      ∀ y ∈ ({x, algebraMap Y Ω e} : Set Ω), τ y = y := by
    intro τ hτ y hy
    rcases hy with rfl | rfl
    · exact (hI τ hτ).2
    · exact (hI τ hτ).1 e
  let h' : G (maximalRealSubfield Y) Ω := AlgEquiv.restrictScalars _ h
  have hh' : h' ∈ Dec A := (GlobalTheory.AboveL.mem_dec_congr A h' h (fun _ => rfl)).2 hh
  obtain ⟨k, hk⟩ := hD _ Ω A v hv φ hφ _ hXf hIX g hgD
  obtain ⟨m, hm⟩ := hD _ Ω A v hv φ hφ _ hXf hIX h' hh'
  have hE0 : algebraMap Y Ω e ≠ 0 := (map_ne_zero _).2 he0
  have hpmE : φ (algebraMap Y Ω e) = algebraMap Y Ω e ∨ φ (algebraMap Y Ω e) = -algebraMap Y Ω e := by
    apply pm_of_sq
    have hs : e ^ 2 ∈ maximalRealSubfield Y := by
      rw [← IsCMField.complexConj_eq_self_iff, map_pow, hce, neg_sq]
    rw [← map_pow]
    exact φ.commutes (⟨e ^ 2, hs⟩ : maximalRealSubfield Y)
  have hpmx : φ x = x ∨ φ x = -x := by
    apply pm_of_sq
    rw [hx, map_intCast]
  have hkE : (φ ^ k) (algebraMap Y Ω e) ≠ algebraMap Y Ω e := by
    rw [← hk _ (by simp)]
    intro hgE
    exact hgY (fixes_of_imag e he0 hce g hgE)
  have hmE : (φ ^ m) (algebraMap Y Ω e) = algebraMap Y Ω e := by
    rw [← hm _ (by simp)]
    exact h.commutes e
  have hfx := fix_of_parity φ _ x hE0 hpmE hpmx k m hkE hmE
  rw [← hm x (by simp)] at hfx
  exact hfx
