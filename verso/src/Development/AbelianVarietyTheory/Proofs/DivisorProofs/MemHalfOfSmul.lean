import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CoverTransform

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

/- English proof (translation)
The claim follows from `(Submodule.Quotient.eq _).1 (GlobalTheory.HalfPairing.qRep_mk _)`.
-/
theorem qRep_sub_mem {K : Submodule (𝓞 E) Dw.La} (a : Dw.La) :
    qRep (Submodule.Quotient.mk a : Dw.La ⧸ K) - a ∈ K :=
  (Submodule.Quotient.eq _).1 (GlobalTheory.HalfPairing.qRep_mk _)

/- English proof (translation)
Establish `h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[GlobalTheory.LevelCoverDatum.half_mul_conj d h]`. Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `Ideal.mul_le_right h1`.
-/
theorem pd_mem_half (d : DeltaDat Xo c n) (h : d.IsLev) :
    (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [GlobalTheory.LevelCoverDatum.half_mul_conj d h]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mul_le_right h1

/- English proof (translation)
Unfold `Mfr`. Rewrite using `[h.2.2.2.1, Ideal.map_mul]`.
-/
theorem mfr_cover (d : DeltaDat Xo c n) (h : d.IsLev) :
    Mfr d.l₂ = Mfr l * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold Mfr; rw [h.2.2.2.1, Ideal.map_mul]

/- English proof (translation)
Establish `hp` using `GlobalTheory.LevelCoverDatum.pd_pos d h`. Establish `hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥`. Introduce `e`. Use `pd_mem_half d h` as an intermediate fact. Rewrite `this` using `[e, Ideal.mem_bot]`.

Conclude with `hp.ne' (by exact_mod_cast this)`. Use `(d.I.map (H.bar : 𝓞 E →+* 𝓞 E)).finiteQuotientOfFreeOfNeBot hb` as an intermediate fact. Use `Dw.fin` as an intermediate fact. Conclude with `Submodule.finite_quotient_smul _ (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top`.
-/
theorem finite_laJ (d : DeltaDat Xo c n) (h : d.IsLev) : Finite (LaJ Xo c d) := by
  have hp := GlobalTheory.LevelCoverDatum.pd_pos d h
  have hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro e
    have := pd_mem_half d h
    rw [e, Ideal.mem_bot] at this
    exact hp.ne' (by exact_mod_cast this)
  have := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)).finiteQuotientOfFreeOfNeBot hb
  have := Dw.fin
  exact Submodule.finite_quotient_smul _ (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

/- English proof (translation)
The claim follows from `Nat.Coprime.cast (R := 𝓞 E) h.2.2.1`.
-/
theorem exists_bezout (d : DeltaDat Xo c n) (h : d.IsLev) :
    ∃ α β : 𝓞 E, α * d.pd + β * l.M = 1 := Nat.Coprime.cast (R := 𝓞 E) h.2.2.1

/- English proof (translation)
Take `⟨α, β, e⟩` from `exists_bezout d h`. Establish `h1 : l.M • u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)` using `Submodule.smul_mono_left (by rw [mfr_cover d h]; exact Ideal.mul_le_right) hu`. Establish `h2 : u = (α * d.pd) • u + β • l.M • u`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, ← add_smul, e, one_smul]`. Rewrite using `[h2]`.

Conclude with `add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) trivial) (Submodule.smul_mem _ _ h1)`.
-/
theorem mem_half_of_smul (d : DeltaDat Xo c n) (h : d.IsLev) {u : Dw.La}
    (hu : l.M • u ∈ (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) :
    u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  have h1 : l.M • u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mono_left (by rw [mfr_cover d h]; exact Ideal.mul_le_right) hu
  have h2 : u = (α * d.pd) • u + β • l.M • u := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, ← add_smul, e, one_smul]
  rw [h2]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) trivial) (Submodule.smul_mem _ _ h1)

/- English proof (translation)
Take `⟨α, β, e⟩` from `exists_bezout d h`. Use `⟨Submodule.Quotient.mk (β • (u - d.pd • x)), (Submodule.Quotient.eq _).2 ?_⟩` and prove the remaining obligations. Establish `h1` using `qRep_sub_mem (K := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) (β • (u - d.pd • x))`. Generalize the expression as in `qRep (Submodule.Quotient.mk (β • (u - d.pd • x)) : LaJ Xo c d) = r at h1 ⊢`. Establish `h2 : d.pd • x + l.M • r - u = (l.M : 𝓞 E) • (r - β • (u - d.pd • x)) - (α * d.pd) • (u - d.pd • x)`.

Establish `e' : α * (d.pd : 𝓞 E) = 1 - l.M * β` using `by linear_combination e`. Rewrite using `[e', ← Nat.cast_smul_eq_nsmul (𝓞 E) l.M]`. Generalize the expression as in `d.pd • x = v`. Use `module`. Rewrite using `[h2, mfr_cover d h]`.

Use `sub_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul (GlobalTheory.Dict.CoverFourier.natCast_mem l).2 h1`. Rewrite using `[mul_comm (Mfr l), Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) hu`.
-/
theorem exists_class (d : DeltaDat Xo c n) (h : d.IsLev) {x u : Dw.La}
    (hu : u - d.pd • x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ z : LaJ Xo c d, (Submodule.Quotient.mk (d.pd • x + l.M • qRep z) : LevQc Dw d.l₂) = Submodule.Quotient.mk u := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  refine ⟨Submodule.Quotient.mk (β • (u - d.pd • x)), (Submodule.Quotient.eq _).2 ?_⟩
  have h1 := qRep_sub_mem (K := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) (β • (u - d.pd • x))
  generalize qRep (Submodule.Quotient.mk (β • (u - d.pd • x)) : LaJ Xo c d) = r at h1 ⊢
  have h2 : d.pd • x + l.M • r - u =
      (l.M : 𝓞 E) • (r - β • (u - d.pd • x)) - (α * d.pd) • (u - d.pd • x) := by
    have e' : α * (d.pd : 𝓞 E) = 1 - l.M * β := by linear_combination e
    rw [e', ← Nat.cast_smul_eq_nsmul (𝓞 E) l.M]
    generalize d.pd • x = v
    module
  rw [h2, mfr_cover d h]
  refine sub_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul (GlobalTheory.Dict.CoverFourier.natCast_mem l).2 h1
  · rw [mul_comm (Mfr l), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) hu

/- English proof (translation)
Establish `h1` using `GlobalTheory.LevelPairing.dvd_left (l := d.l₂) y (qRep_sub_mem (K := (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) (d.pd • x + l.M • z))`. Take `⟨a1, a2⟩` from `GlobalTheory.LevelPairing.cSep_spec d.l₂`. Take `⟨b1, b2⟩` from `GlobalTheory.LevelPairing.cSep_spec l`. Establish `h2 : (l.M : ℤ) ∣ Dw.EF x ((cSep d.l₂ - cSep l) • y)`. Use `GlobalTheory.HalfPairing.dvd_of_mem _ _ _ ?_` and prove the remaining obligations.

Rewrite using `[← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]`. Use `⟨?_, sub_mem ?_ b1⟩` and prove the remaining obligations. Simplify using `using sub_mem (h.1.2.1 a2) b2`. Rewrite `a1` using `[mfr_cover d h]`. Conclude with `Ideal.mul_le_left a1`.

Establish `h3` using `GlobalTheory.Dict.CoverFourier.pd_dvd d h (by rw [mfr_cover d h]; exact Ideal.mul_le_right) z (a := y) (a' := y) (by rw [sub_self]; exact zero_mem _)`. Establish `hM : (d.l₂.M : ℤ) = l.M * d.pd` using `by rw [h.2.1]; push_cast; rfl`. Establish `h4 : (d.l₂.M : ℤ) ∣ _` using `hM ▸ mul_dvd_mul_right h2 (d.pd : ℤ)`. Establish `h5 : (d.l₂.M : ℤ) ∣ _` using `hM ▸ mul_dvd_mul_left (l.M : ℤ) h3`. Establish `h6` using `dvd_add (dvd_add h1 h4) h5`.

Simplify using `only [map_sub, map_add, map_nsmul, sub_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at h6`. Use `h6.trans (dvd_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvd_pairing (d : DeltaDat Xo c n) (h : d.IsLev) (x z y : Dw.La) :
    (d.l₂.M : ℤ) ∣ Dw.EF (qRep (Submodule.Quotient.mk (d.pd • x + l.M • z) : LevQc Dw d.l₂)) (cSep d.l₂ • y) -
      (d.pd * Dw.EF x (cSep l • y) + l.M * Dw.EF z (cHalf H d.I • y)) := by
  have h1 := GlobalTheory.LevelPairing.dvd_left (l := d.l₂) y
    (qRep_sub_mem (K := (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) (d.pd • x + l.M • z))
  obtain ⟨a1, a2⟩ := GlobalTheory.LevelPairing.cSep_spec d.l₂
  obtain ⟨b1, b2⟩ := GlobalTheory.LevelPairing.cSep_spec l
  have h2 : (l.M : ℤ) ∣ Dw.EF x ((cSep d.l₂ - cSep l) • y) := by
    refine GlobalTheory.HalfPairing.dvd_of_mem _ _ _ ?_
    rw [← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]
    refine ⟨?_, sub_mem ?_ b1⟩
    · simpa using sub_mem (h.1.2.1 a2) b2
    · rw [mfr_cover d h] at a1
      exact Ideal.mul_le_left a1
  have h3 := GlobalTheory.Dict.CoverFourier.pd_dvd d h (by rw [mfr_cover d h]; exact Ideal.mul_le_right) z
    (a := y) (a' := y) (by rw [sub_self]; exact zero_mem _)
  have hM : (d.l₂.M : ℤ) = l.M * d.pd := by rw [h.2.1]; push_cast; rfl
  have h4 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_right h2 (d.pd : ℤ)
  have h5 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_left (l.M : ℤ) h3
  have h6 := dvd_add (dvd_add h1 h4) h5
  simp only [map_sub, map_add, map_nsmul, sub_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at h6
  refine h6.trans (dvd_of_eq ?_)
  ring

end

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin x₀ ζ φc hval hsupp`. Use function extensionality and compare the values at `q`. Use `haveI := finite_laJ d hd`. Use `haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw d.l₂`. Use `haveI := Fintype.ofFinite (Fin n → LaJ Xo c d)`.

Use `haveI := Fintype.ofFinite (Fin n → LevQc Dw d.l₂)`. Establish `hM₂ : d.l₂.M ≠ 0` using `by have := d.l₂.three_le; omega`. Establish `he : zeta d.l₂.M ^ d.l₂.M = 1` using `(Complex.isPrimitiveRoot_exp _ hM₂).pow_eq_one`. Establish `he0 : zeta d.l₂.M ≠ 0` using `Complex.exp_ne_zero _`. Establish `hz : d.c₂.F.val (zetaM d.c₂) = zeta d.l₂.M` using `GlobalTheory.LevelPairing.zetaM_coe d.c₂`.

Establish `hz1 : c.F.val (zetaM c) = zeta d.l₂.M ^ d.pd`. Rewrite using `[← hz, ← map_pow, GlobalTheory.LevelCoverDatum.zetaM_cover d hd.2.1]`. Both sides reduce to the same expression. Establish `hφ : c.F.val (d.φδ q) = ∑ z : Fin n → LaJ Xo c d, ((ph z : c.F) : ℂ) * (zeta d.l₂.M ^ l.M) ^ (∑ b, Dw.EF (qRep (z b)) (cHalf H d.I • levRep (q b)))`. Express the relevant statement in the definitionally equal form `d.c₂.F.val (d.eF (d.φδ q)) = _`.

Rewrite using `[hpin.2.2.2.2.2 q, finsum_eq_sum_of_fintype, map_sum]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_zpow₀, ← GlobalTheory.Dict.CoverFourier.zetaM_pow d hd, map_pow, hz]`. Both sides reduce to the same expression. Rewrite using `[DeltaDat.w, AlgEquiv.symm_apply_apply]`.

Express the relevant statement in the definitionally equal form `_ = ζ * c.F.val (zetaM c ^ pairL (l := l) x₀ (fun b => levRep (q b)) * d.φδ q)`. Rewrite using `[map_mul, map_zpow₀, hz1, hφ, Finset.mul_sum, Finset.mul_sum, GlobalTheory.AdTh.hatC, finsum_eq_sum_of_fintype]`. Use `symm`. Use `Fintype.sum_of_injective (fun (z : Fin n → LaJ Xo c d) b => (Submodule.Quotient.mk (d.pd • x₀ b + l.M • qRep (z b)) : LevQc Dw d.l₂)) (fun z z' e => funext fun b => ?_) _ _ (fun x hx => ?_) (fun z => ?_)` and prove the remaining obligations. Establish `h1` using `(Submodule.Quotient.eq _).1 (congrFun e b)`.

Rewrite `h1` using `[add_sub_add_left_eq_sub, ← smul_sub]`. Rewrite using `[← GlobalTheory.HalfPairing.qRep_mk (z b), ← GlobalTheory.HalfPairing.qRep_mk (z' b)]`. Conclude with `(Submodule.Quotient.eq _).2 (mem_half_of_smul d hd h1)`. Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hx' : (fun b => (Submodule.Quotient.mk (qRep (x b)) : LevQc Dw d.l₂)) = x`. Use function extensionality and compare the values at `fun b => GlobalTheory.HalfPairing.qRep_mk _`. Use `choose z hz' using fun b => exists_class d hd (hsupp (fun b => qRep (x b)) (by rwa [hx']) b)`. Conclude with `hx ⟨z, (funext hz').trans hx'⟩`. Establish `hz' : (fun b => (Submodule.Quotient.mk (qRep (z b)) : LaJ Xo c d)) = z`.

Use function extensionality and compare the values at `fun b => GlobalTheory.HalfPairing.qRep_mk _`. Rewrite using `[hval (fun b => qRep (z b)), hz', mul_left_comm, ← mul_assoc ζ, mul_left_comm]`. Use `congr 1`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ he0]`. Use `symm`.

Use `GlobalTheory.Dict.CoverFourier.zpow_congr' hM₂ he ?_` and prove the remaining obligations. Rewrite using `[pairL, pairL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Conclude with `Finset.dvd_sum fun b _ => dvd_pairing d hd _ _ _`.
-/
theorem hatC_eq_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (x₀ : Fin n → Dw.La) (ζ : ℂ) (φc : (Fin n → LevQc Dw d.l₂) → ℂ), (∀ z : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (d.pd • x₀ b + l.M • z b)) = ζ * ((ph (fun b => Submodule.Quotient.mk (z b)) : c.F) : ℂ)) → (∀ x : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (x b)) ≠ 0 → ∀ b, x b - d.pd • x₀ b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) → GlobalTheory.AdTh.hatC d.l₂ φc = fun q => ζ * ((d.eF.symm (d.w x₀ q) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin x₀ ζ φc hval hsupp
  funext q
  haveI := finite_laJ d hd
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw d.l₂
  haveI := Fintype.ofFinite (Fin n → LaJ Xo c d)
  haveI := Fintype.ofFinite (Fin n → LevQc Dw d.l₂)
  have hM₂ : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have he : zeta d.l₂.M ^ d.l₂.M = 1 := (Complex.isPrimitiveRoot_exp _ hM₂).pow_eq_one
  have he0 : zeta d.l₂.M ≠ 0 := Complex.exp_ne_zero _
  have hz : d.c₂.F.val (zetaM d.c₂) = zeta d.l₂.M := GlobalTheory.LevelPairing.zetaM_coe d.c₂
  have hz1 : c.F.val (zetaM c) = zeta d.l₂.M ^ d.pd := by
    rw [← hz, ← map_pow, GlobalTheory.LevelCoverDatum.zetaM_cover d hd.2.1]; rfl
  have hφ : c.F.val (d.φδ q) = ∑ z : Fin n → LaJ Xo c d, ((ph z : c.F) : ℂ) * (zeta d.l₂.M ^ l.M) ^
      (∑ b, Dw.EF (qRep (z b)) (cHalf H d.I • levRep (q b))) := by
    change d.c₂.F.val (d.eF (d.φδ q)) = _
    rw [hpin.2.2.2.2.2 q, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, map_zpow₀, ← GlobalTheory.Dict.CoverFourier.zetaM_pow d hd, map_pow, hz]
    rfl
  rw [DeltaDat.w, AlgEquiv.symm_apply_apply]
  change _ = ζ * c.F.val (zetaM c ^ pairL (l := l) x₀ (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_zpow₀, hz1, hφ, Finset.mul_sum, Finset.mul_sum, GlobalTheory.AdTh.hatC, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective
    (fun (z : Fin n → LaJ Xo c d) b => (Submodule.Quotient.mk (d.pd • x₀ b + l.M • qRep (z b)) : LevQc Dw d.l₂))
    (fun z z' e => funext fun b => ?_) _ _ (fun x hx => ?_) (fun z => ?_)
  · have h1 := (Submodule.Quotient.eq _).1 (congrFun e b)
    rw [add_sub_add_left_eq_sub, ← smul_sub] at h1
    rw [← GlobalTheory.HalfPairing.qRep_mk (z b), ← GlobalTheory.HalfPairing.qRep_mk (z' b)]
    exact (Submodule.Quotient.eq _).2 (mem_half_of_smul d hd h1)
  · refine mul_eq_zero_of_left ?_ _
    by_contra hne
    have hx' : (fun b => (Submodule.Quotient.mk (qRep (x b)) : LevQc Dw d.l₂)) = x :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    choose z hz' using fun b => exists_class d hd (hsupp (fun b => qRep (x b)) (by rwa [hx']) b)
    exact hx ⟨z, (funext hz').trans hx'⟩
  · have hz' : (fun b => (Submodule.Quotient.mk (qRep (z b)) : LaJ Xo c d)) = z :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    rw [hval (fun b => qRep (z b)), hz', mul_left_comm, ← mul_assoc ζ, mul_left_comm]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ he0]
    symm
    refine GlobalTheory.Dict.CoverFourier.zpow_congr' hM₂ he ?_
    rw [pairL, pairL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun b _ => dvd_pairing d hd _ _ _

end GlobalTheory.CoverTransform
