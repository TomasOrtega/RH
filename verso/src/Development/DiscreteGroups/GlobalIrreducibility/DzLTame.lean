import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
import Development.DiscreteGroups.GlobalIrreducibility.EigTranslate
import Development.DiscreteGroups.GlobalIrreducibility.DzTame
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
import Development.DiscreteGroups.GlobalIrreducibility.ContinuousResI
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `choose e he using hex`. Establish `hne : ∀ s, e s ≠ 0` using `fun s h0 => DzCliff.rho_ne_zero ρ (f s) hu (by rw [he s, h0, zero_smul])`. Use `⟨{ toFun := fun s => Units.mk0 (e s) (hne s), map_one' := ?_, map_mul' := ?_ }, fun s => he s⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [Units.val_mk0, Units.val_one]`.

Conclude with `DzCliff.eig_unique hu (he 1) (by rw [map_one, map_one, Module.End.one_apply, one_smul])`. Introduce `s t`. Use `ext`. Simplify using `only [Units.val_mk0, Units.val_mul]`. Conclude with `DzCliff.eig_unique hu (he (s * t)) (by rw [map_mul, map_mul, Module.End.mul_apply, he t, map_smul, he s, smul_smul, mul_comm])`.
-/
theorem exists_eigenChar {H W V : Type*} [Group H] [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ W V) (f : H →* W) {u : V} (hu : u ≠ 0) (hex : ∀ s, ∃ e : ℂ, ρ (f s) u = e • u) :
    ∃ χ : H →* ℂˣ, ∀ s, ρ (f s) u = ((χ s : ℂˣ) : ℂ) • u := by
  choose e he using hex
  have hne : ∀ s, e s ≠ 0 := fun s h0 => DzCliff.rho_ne_zero ρ (f s) hu (by rw [he s, h0, zero_smul])
  refine ⟨{ toFun := fun s => Units.mk0 (e s) (hne s), map_one' := ?_, map_mul' := ?_ }, fun s => he s⟩
  · ext
    simp only [Units.val_mk0, Units.val_one]
    exact DzCliff.eig_unique hu (he 1) (by rw [map_one, map_one, Module.End.one_apply, one_smul])
  · intro s t
    ext
    simp only [Units.val_mk0, Units.val_mul]
    exact DzCliff.eig_unique hu (he (s * t))
      (by rw [map_mul, map_mul, Module.End.mul_apply, he t, map_smul, he s, smul_smul, mul_comm])

/- English proof (translation)
Introduce `E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn hg hN a' ha' K _ _ red hr hk y hirr htame hdim`. Establish `hq : normV w = g` using `normV_eq_of_padic w g i hi`. Establish `hq' : normV w' = normV w ^ n` using `by rw [hq, hN]`. Take `⟨m, a, hya, hirr_a⟩` from `hirr`. Take `⟨m2, a2, hya2, htame2⟩` from `htame`.

Establish `hiso : a2.Iso a` using `WD.mk_eq_mk.mp (hya2.trans hya.symm)`. Establish `htame_a : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1` using `fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)`. Establish `hdim_a : finrank ℂ (Fin m → ℂ) = n` using `by rw [← hdim, ← hya, WD.lpDim_mk]`. Set `I : Subgroup (Weil h)` to `(Ine (F := E) A).comap (Weil h).subtype`. Use `haveI hInorm : I.Normal := ⟨fun t ht g0 => by show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A`.

Conclude with `conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩`. Establish `hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t` using `fun σ => by`. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) σ`. Conclude with `⟨deg σ, ineIncl h τ, τ.2, hτ⟩`. Establish `hcomm : ∀ s ∈ I, ∀ t ∈ I, a.ρ s * a.ρ t = a.ρ t * a.ρ s`.

Introduce `s hs t ht`. Set `s' : Ine (F` to `E) A := ⟨s, hs⟩`. Set `t' : Ine (F` to `E) A := ⟨t, ht⟩`. Establish `h1 : a.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1` using `htame_a _ (isWild_commutator s' t')`. Establish `h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹` using `Subtype.ext rfl`.

Rewrite `h1` using `[h2]`. Establish `e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s)` using `by group`. Rewrite using `[← map_mul, ← map_mul, e, map_mul, h1, one_mul]`. Establish `hfrob : ∀ t ∈ I, a.ρ (frob h * t * (frob h)⁻¹) = a.ρ t ^ normV w`. Introduce `t ht`.

Set `t' : Ine (F` to `E) A := ⟨t, ht⟩`. Set `c' : Ine (F` to `E) A := ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩`. Establish `h1 : a.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1` using `htame_a _ (isWild_frob (isFrob_frob (h := h)) t')`. Establish `h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹` using `Subtype.ext rfl`. Rewrite `h1` using `[h2]`.

Establish `e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w` using `by group`. Rewrite using `[e, map_mul, h1, one_mul, map_pow]`. Take `⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩` from `DzCliff.clifford a.ρ hirr_a I (frob h) (normV w) n hdim_a hn hgen hcomm hfrob`. Establish `hc0 : c ≠ 0` using `fun h0 => DzCliff.rho_ne_zero a.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])`. Establish `hcinv : a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u`.

Establish `h1` using `DzCliff.rho_inv_apply a.ρ (frob h ^ n) u`. Rewrite `h1` using `[hφn, map_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Use `_ = c⁻¹ • u := by rw [h1]`.

Establish `hz : ∀ k : ℤ, a.ρ ((frob h ^ n) ^ k) u = c ^ k • u`. Introduce `k`. Proceed by induction on `k using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]`. Consider the case `pred k ih`. Rewrite using `[zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0, mul_comm]`. Establish `hex : ∀ σ : Weil h', ∃ e : ℂ, a.ρ (resW h h' hq' σ) u = e • u`. Introduce `σ`.

Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) (resW h h' hq' σ)`. Rewrite using `[hτ, deg_resW, map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul, show frob h ^ ((n : ℤ) * deg σ) = (frob h ^ n) ^ deg σ by rw [zpow_mul, zpow_natCast], hz, smul_smul]`. Conclude with `⟨_, rfl⟩`. Take `⟨η', hη'⟩` from `exists_eigenChar a.ρ (resW h h' hq') hu hex`. Establish `hval : ∀ t : Ine (F` using `E') A, ((η' (ineIncl h' t) : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t => DzCliff.eig_unique hu (hη' _) (by rw [resW_ineIncl]; exact huI (ineIncl h (resI t)) (resI t).2)`.

Establish `hsm : IsSmooth η'`. Use `IsSmooth.of_open (U := resI ⁻¹' {s : Ine (F := E) A | a.ρ (ineIncl h s) = 1}) (IsOpen.preimage continuous_resI a.smooth) (by simp) ?_` and prove the remaining obligations. Introduce `t ht`. Establish `h1 : a.ρ (resW h h' hq' (ineIncl h' t)) u = (1 : ℂ) • u`. Rewrite using `[resW_ineIncl, ht, Module.End.one_apply, one_smul]`.

Conclude with `Units.ext (DzCliff.eig_unique hu (hη' _) h1)`. Establish `hηN : ∀ t : Ine (F` using `E') A, η' (ineIncl h' t) ^ (g ^ n - 1) = 1 := by`. Introduce `t`. Establish `hp` using `hper (ineIncl h (resI t)) (resI t).2`. Rewrite `hp` using `[hq]`.

Establish `hs0 : η (ineIncl h (resI t)) ≠ 0` using `by rw [← hval]; exact Units.ne_zero _`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, hval, Units.val_one]`. Establish `h1 : η (ineIncl h (resI t)) ^ (g ^ n - 1) * η (ineIncl h (resI t)) = 1 * η (ineIncl h (resI t))`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), hp, one_mul]`.

Conclude with `mul_right_cancel₀ hs0 h1`. Take `⟨ξ, hξ⟩` from `exists_resChar g A w' h' n hn hN a' ha' K red hr hk η' hsm hηN`. Use `⟨ξ, ?_, ?_⟩` and prove the remaining obligations. Introduce `i0 j0 hi0 hj0 hij`. Assume the negation of the conclusion as `hne`.

Use `wlog hlt : i0 < j0 generalizing i0 j0`. Conclude with `this j0 i0 hj0 hi0 hij.symm (Ne.symm hne) (by omega)`. Take `⟨s, hsI, hs⟩` from `hmin (j0 - i0) (by omega) (by omega)`. Take `⟨t0, ht0, hres⟩` from `ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI`. Set `t : Ine (F` to `E') A := ⟨t0, ht0⟩`.

Establish `hts : ineIncl h (resI t) = s` using `Subtype.ext hres`. Establish `hunit : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1`. Establish `h1` using `ha'.ord_eq (ineIncl h' t)`. Rewrite `h1` using `[GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl]`. Establish `hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0`.

Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `Units.ne_zero _`. Establish `hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0`. Simplify using `using h1`. Rewrite using `[← WithZero.exp_log hv0, hl, WithZero.exp_zero]`.

Take `⟨x, hx⟩` from `exists_int_approx_compl w' _ hunit.le`. Establish `hxw : red x ≠ 0`. Introduce `h0`. Establish `hxm : x ∈ w'.asIdeal` using `by rw [← hk, RingHom.mem_ker]; exact h0`. Establish `hvx : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1`.

Establish `e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E')` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')`. Rewrite using `[e]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hxm`. Establish `hlt1 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1`. Establish `e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E')` using `by ring`.

Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ hx hvx`. Rewrite `hlt1` using `[hunit]`. Conclude with `lt_irrefl _ hlt1`. Establish `hξz` using `hξ t x (Units.mk0 (red x) hxw) rfl hx`.

Establish `h1 : (ξ (Units.mk0 (red x) hxw)) ^ g ^ i0 = (ξ (Units.mk0 (red x) hxw)) ^ g ^ j0`. Use `congrArg (fun χ : Kˣ →* ℂˣ => χ (Units.mk0 (red x) hxw)) hij` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[hξz]`. Establish `h2 : ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ i0 = ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ j0`.

Use `congrArg Units.val h1` as an intermediate fact. Simplify `this` using `only [Units.val_pow_eq_pow_val]`. Rewrite `h2` using `[hval, hts]`. Establish `hp` using `hper s hsI`. Rewrite `hp`, `hs` using `[hq]`.

Apply `hs` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Use `_ = (η s ^ g ^ j0) ^ g ^ (n - i0) := by rw [pow_mul]`. Use `_ = (η s ^ g ^ i0) ^ g ^ (n - i0) := by rw [h2]`. Use `_ = η s ^ (g ^ i0 * g ^ (n - i0)) := by rw [← pow_mul]`. Use `_ = η s ^ g ^ n := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi0)]`. Use `_ = η s := hp`.

Introduce `t x z hxz hv`. Establish `hξz` using `hξ t x z hxz hv`. Rewrite using `[WD.inePol_of_mem_Ine y (res_mem_Ine t.2), ← hya, WD.charPol_mk]`. Rewrite using `[show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl, hchar (ineIncl h (resI t)) (resI t).2, hq]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow ξ, Units.val_pow_eq_pow_val, hξz, hval]`.
-/
theorem lTame : LTame := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn hg hN a' ha' K _ _ red hr hk y hirr htame hdim
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  obtain ⟨m, a, hya, hirr_a⟩ := hirr
  obtain ⟨m2, a2, hya2, htame2⟩ := htame
  have hiso : a2.Iso a := WD.mk_eq_mk.mp (hya2.trans hya.symm)
  have htame_a : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 :=
    fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)
  have hdim_a : finrank ℂ (Fin m → ℂ) = n := by rw [← hdim, ← hya, WD.lpDim_mk]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, a.ρ s * a.ρ t = a.ρ t * a.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : a.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame_a _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, a.ρ (frob h * t * (frob h)⁻¹) = a.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : a.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame_a _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford a.ρ hirr_a I (frob h) (normV w) n hdim_a hn hgen hcomm hfrob
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero a.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply a.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • a.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, a.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have hex : ∀ σ : Weil h', ∃ e : ℂ, a.ρ (resW h h' hq' σ) u = e • u := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (resW h h' hq' σ)
    rw [hτ, deg_resW, map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * deg σ) = (frob h ^ n) ^ deg σ by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ := exists_eigenChar a.ρ (resW h h' hq') hu hex
  have hval : ∀ t : Ine (F := E') A, ((η' (ineIncl h' t) : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hη' _) (by rw [resW_ineIncl]; exact huI (ineIncl h (resI t)) (resI t).2)
  have hsm : IsSmooth η' := by
    refine IsSmooth.of_open (U := resI ⁻¹' {s : Ine (F := E) A | a.ρ (ineIncl h s) = 1})
      (IsOpen.preimage continuous_resI a.smooth) (by simp) ?_
    intro t ht
    have h1 : a.ρ (resW h h' hq' (ineIncl h' t)) u = (1 : ℂ) • u := by
      rw [resW_ineIncl, ht, Module.End.one_apply, one_smul]
    exact Units.ext (DzCliff.eig_unique hu (hη' _) h1)
  have hηN : ∀ t : Ine (F := E') A, η' (ineIncl h' t) ^ (g ^ n - 1) = 1 := by
    intro t
    have hp := hper (ineIncl h (resI t)) (resI t).2
    rw [hq] at hp
    have hs0 : η (ineIncl h (resI t)) ≠ 0 := by rw [← hval]; exact Units.ne_zero _
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hval, Units.val_one]
    have h1 : η (ineIncl h (resI t)) ^ (g ^ n - 1) * η (ineIncl h (resI t)) = 1 * η (ineIncl h (resI t)) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), hp, one_mul]
    exact mul_right_cancel₀ hs0 h1
  obtain ⟨ξ, hξ⟩ := exists_resChar g A w' h' n hn hN a' ha' K red hr hk η' hsm hηN
  refine ⟨ξ, ?_, ?_⟩
  · intro i0 j0 hi0 hj0 hij
    by_contra hne
    wlog hlt : i0 < j0 generalizing i0 j0
    · exact this j0 i0 hj0 hi0 hij.symm (Ne.symm hne) (by omega)
    obtain ⟨s, hsI, hs⟩ := hmin (j0 - i0) (by omega) (by omega)
    obtain ⟨t0, ht0, hres⟩ := ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI
    let t : Ine (F := E') A := ⟨t0, ht0⟩
    have hts : ineIncl h (resI t) = s := Subtype.ext hres
    have hunit : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
      have h1 := ha'.ord_eq (ineIncl h' t)
      rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
      have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
        rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
      have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
        simpa using h1
      rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ hunit.le
    have hxw : red x ≠ 0 := by
      intro h0
      have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
      have hvx : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
        have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
        rw [e]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hxm
      have hlt1 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
        have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
            (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
              algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
        rw [e]
        exact Valuation.map_add_lt _ hx hvx
      rw [hunit] at hlt1
      exact lt_irrefl _ hlt1
    have hξz := hξ t x (Units.mk0 (red x) hxw) rfl hx
    have h1 : (ξ (Units.mk0 (red x) hxw)) ^ g ^ i0 = (ξ (Units.mk0 (red x) hxw)) ^ g ^ j0 := by
      have := congrArg (fun χ : Kˣ →* ℂˣ => χ (Units.mk0 (red x) hxw)) hij
      simpa using this
    rw [hξz] at h1
    have h2 : ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ i0 = ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ j0 := by
      have := congrArg Units.val h1
      simpa only [Units.val_pow_eq_pow_val] using this
    rw [hval, hts] at h2
    have hp := hper s hsI
    rw [hq] at hp hs
    apply hs
    calc η s ^ g ^ (j0 - i0) = (η s ^ g ^ n) ^ g ^ (j0 - i0) := by rw [hp]
      _ = η s ^ (g ^ n * g ^ (j0 - i0)) := by rw [← pow_mul]
      _ = η s ^ (g ^ j0 * g ^ (n - i0)) := by
          rw [← pow_add, ← pow_add]; congr 2; omega
      _ = (η s ^ g ^ j0) ^ g ^ (n - i0) := by rw [pow_mul]
      _ = (η s ^ g ^ i0) ^ g ^ (n - i0) := by rw [h2]
      _ = η s ^ (g ^ i0 * g ^ (n - i0)) := by rw [← pow_mul]
      _ = η s ^ g ^ n := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi0)]
      _ = η s := hp
  · intro t x z hxz hv
    have hξz := hξ t x z hxz hv
    rw [WD.inePol_of_mem_Ine y (res_mem_Ine t.2), ← hya, WD.charPol_mk]
    rw [show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar (ineIncl h (resI t)) (resI t).2, hq]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow ξ, Units.val_pow_eq_pow_val, hξz, hval]

end DiscreteGroups.sglob.DzType

end
