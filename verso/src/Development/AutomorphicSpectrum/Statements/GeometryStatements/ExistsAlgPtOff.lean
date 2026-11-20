import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ReadsRootsFinZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest

open MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec ramOverZ)
open GlobalTheory.CompanionTheory.Ar.Ref (pjSys UnifAll)

section Pts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[Subsingleton.elim A B]`.
-/
theorem aeval_inst {σ R : Type} [CommRing R] (A B : Algebra ℤ R) (x : σ → R) (f : MvPolynomial σ ℤ) :
    (letI := A; aeval x f) = (letI := B; aeval x f) := by
  rw [Subsingleton.elim A B]

/- English proof (translation)
Establish `h` using `aeval_blockScale hg (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))`. Establish `h2 : ∀ f : MRing ι, eval₂ (Int.castRingHom _) (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => rw [eval₂_C]`.

Simplify using the standard rewrite rules. Consider the case `add f f' h h' => rw [eval₂_add, h, h', map_add, map_add]`. Consider the case `mul_X f p h => rw [eval₂_mul, h, eval₂_X, map_mul, map_mul, aeval_X]`. Rewrite using `[← h2]`. Use `Eq.trans ?_ (h.trans ?_)` and prove the remaining obligations.

Unfold `mConeMap`. Simplify using `only [mul_comm]`. Conclude with `aeval_inst _ _ _ _`. Both sides reduce to the same expression.
-/
theorem mConeMap_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = (∏ k, X k ^ d k) * C (aeval y g) := by
  have h := aeval_blockScale hg (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))
  have h2 : ∀ f : MRing ι, eval₂ (Int.castRingHom _) (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => rw [eval₂_C]; simp
    | add f f' h h' => rw [eval₂_add, h, h', map_add, map_add]
    | mul_X f p h => rw [eval₂_mul, h, eval₂_X, map_mul, map_mul, aeval_X]
  rw [← h2]
  refine Eq.trans ?_ (h.trans ?_)
  · unfold mConeMap
    simp only [mul_comm]
    exact aeval_inst _ _ _ _
  · rfl

/- English proof (translation)
Take `⟨dg, dh, g, h, hg, hh, hd, e, hz0, ez⟩` from `h`. Take `⟨dg', dh', g', h', hg', hh', hd', e', hz0', ez'⟩` from `h'`. Establish `hm : g * h' - g' * h ∈ mCoordIdeal y` using `by show mConeMap y _ = 0`. Rewrite using `[map_sub, map_mul, map_mul, mConeMap_form y hg, mConeMap_form y hh, mConeMap_form y hg', mConeMap_form y hh', e, e']`. Establish `: (∏ k, (X k : MvPolynomial K Ω) ^ dg k) * ∏ k, X k ^ dh' k = (∏ k, X k ^ dg' k) * ∏ k, X k ^ dh k`.

Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Use `hd k` as an intermediate fact.

Use `hd' k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul]`. Take the linear combination `(C s * C (aeval y h) * C (aeval y h')) * this`. Use `hz.2 _ hm` as an intermediate fact.

Rewrite `this` using `[map_sub, map_mul, map_mul, ez, ez']`. Establish `h3 : (w - w') * (aeval z h * aeval z h') = 0` using `by linear_combination this`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right (mul_ne_zero hz0 hz0'))`.
-/
theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e', hz0', ez'⟩ := h'
  have hm : g * h' - g' * h ∈ mCoordIdeal y := by
    show mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, mConeMap_form y hg, mConeMap_form y hh, mConeMap_form y hg',
      mConeMap_form y hh', e, e']
    have : (∏ k, (X k : MvPolynomial K Ω) ^ dg k) * ∏ k, X k ^ dh' k = (∏ k, X k ^ dg' k) * ∏ k, X k ^ dh k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_add, ← pow_add]
      congr 1
      have := hd k; have := hd' k; omega
    simp only [map_mul]
    linear_combination (C s * C (aeval y h) * C (aeval y h')) * this
  have := hz.2 _ hm
  rw [map_sub, map_mul, map_mul, ez, ez'] at this
  have h3 : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination this
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right (mul_ne_zero hz0 hz0'))

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Use `letI := Ideal.Quotient.field m`. Use `haveI : Module.Finite ℚ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ m)`. Set `j : (B ⧸ m) →ₐ[ℚ] PadicAlgCl p` to `IsAlgClosed.lift`. Conclude with `⟨j.comp (Ideal.Quotient.mkₐ ℚ m), fun b => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (Ideal.Quotient.mkₐ ℚ m b)).algHom j⟩`.
-/
theorem exists_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℚ B] [Algebra.FiniteType ℚ B] (p : ℕ)
    [Fact p.Prime] : ∃ ψ : B →ₐ[ℚ] PadicAlgCl p, ∀ b, IsAlgebraic ℚ (ψ b) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℚ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ m)
  let j : (B ⧸ m) →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  exact ⟨j.comp (Ideal.Quotient.mkₐ ℚ m), fun b =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (Ideal.Quotient.mkₐ ℚ m b)).algHom j⟩

/- English proof (translation)
Use `choose i hi using hy`. Set `F` to `FractionRing (MvPolynomial K Ω)`. Set `φ : MRing ι →+* F` to `(algebraMap (MvPolynomial K Ω) F).comp (mConeMap y).toRingHom`. Establish `hφ : ∀ f, φ f = 0 ↔ f ∈ mCoordIdeal y` using `fun f => map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial K Ω) F)`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K Ω) F)`.

Set `v : MRing ι` to `u * ∏ k, X ⟨k, i k⟩`. Establish `hv : φ v ≠ 0`. Rewrite using `[map_mul, map_prod]`. Conclude with `mul_ne_zero (fun h => hu ((hφ _).1 h)) (Finset.prod_ne_zero_iff.2 fun k _ h => hi k ((hφ _).1 h))`. Set `s : Finset F` to `insert (φ v)⁻¹ (Finset.univ.image fun q => φ (X q))`.

Set `B` to `Algebra.adjoin ℚ (s : Set F)`. Use `haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)`. Establish `hX : ∀ q, φ (X q) ∈ B` using `fun q => Algebra.subset_adjoin (by simp [s])`. Establish `hvi : (φ v)⁻¹ ∈ B` using `Algebra.subset_adjoin (by simp [s])`. Take `⟨ψ, hψ⟩` from `exists_algHom B p`.

Set `χ : MRing ι →ₐ[ℤ] B` to `aeval fun q => ⟨φ (X q), hX q⟩`. Establish `hχ : ∀ f, (χ f : F) = φ f` using `fun f => by`. Establish `: (B.val.toRingHom.comp χ.toRingHom) = φ`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `[χ]`. Conclude with `DFunLike.congr_fun this f`. Set `z : (Σ k, ι k) → PadicAlgCl p` to `fun q => ψ ⟨φ (X q), hX q⟩`. Establish `hz : ∀ f, aeval z f = ψ (χ f)` using `fun f => by`. Establish `: (aeval z : MRing ι →ₐ[ℤ] PadicAlgCl p).toRingHom = ψ.toRingHom.comp χ.toRingHom`.

Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[χ, z]`. Conclude with `DFunLike.congr_fun this f`. Establish `hzv : aeval z v ≠ 0`.

Rewrite using `[hz]`. Establish `: χ v * ⟨_, hvi⟩ = 1` using `Subtype.ext (by simpa [hχ] using mul_inv_cancel₀ hv)`. Conclude with `left_ne_zero_of_mul_eq_one (by rw [← map_mul, this, map_one])`. Rewrite `hzv` using `[map_mul, map_prod]`. Use `⟨z, ⟨⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩, fun q => ?_⟩, left_ne_zero_of_mul hzv⟩` and prove the remaining obligations.

Simplify using `using Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hzv) k (Finset.mem_univ _)`. Use `(aeval_inst _ _ z f).trans ((hz f).trans ?_)` and prove the remaining obligations. Rewrite using `[show χ f = 0 from Subtype.ext (by rw [hχ]; exact (hφ f).2 hf), map_zero]`. Conclude with `hψ _`.
-/
theorem exists_algPt [CharZero Ω] (y : (Σ k, ι k) → Ω) (hy : IsRelevant (mCoordIdeal y)) {u : MRing ι}
    (hu : u ∉ mCoordIdeal y) (p : ℕ) [Fact p.Prime] : ∃ z ∈ algPts p (mCoordIdeal y), aeval z u ≠ 0 := by
  classical
  choose i hi using hy
  let F := FractionRing (MvPolynomial K Ω)
  let φ : MRing ι →+* F := (algebraMap (MvPolynomial K Ω) F).comp (mConeMap y).toRingHom
  have hφ : ∀ f, φ f = 0 ↔ f ∈ mCoordIdeal y := fun f =>
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial K Ω) F)
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K Ω) F)
  let v : MRing ι := u * ∏ k, X ⟨k, i k⟩
  have hv : φ v ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (fun h => hu ((hφ _).1 h)) (Finset.prod_ne_zero_iff.2 fun k _ h => hi k ((hφ _).1 h))
  let s : Finset F := insert (φ v)⁻¹ (Finset.univ.image fun q => φ (X q))
  let B := Algebra.adjoin ℚ (s : Set F)
  haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  have hX : ∀ q, φ (X q) ∈ B := fun q => Algebra.subset_adjoin (by simp [s])
  have hvi : (φ v)⁻¹ ∈ B := Algebra.subset_adjoin (by simp [s])
  obtain ⟨ψ, hψ⟩ := exists_algHom B p
  let χ : MRing ι →ₐ[ℤ] B := aeval fun q => ⟨φ (X q), hX q⟩
  have hχ : ∀ f, (χ f : F) = φ f := fun f => by
    have : (B.val.toRingHom.comp χ.toRingHom) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
      · simp
      · simp [χ]
    exact DFunLike.congr_fun this f
  let z : (Σ k, ι k) → PadicAlgCl p := fun q => ψ ⟨φ (X q), hX q⟩
  have hz : ∀ f, aeval z f = ψ (χ f) := fun f => by
    have : (aeval z : MRing ι →ₐ[ℤ] PadicAlgCl p).toRingHom = ψ.toRingHom.comp χ.toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
      · simp
      · simp [χ, z]
    exact DFunLike.congr_fun this f
  have hzv : aeval z v ≠ 0 := by
    rw [hz]
    have : χ v * ⟨_, hvi⟩ = 1 := Subtype.ext (by simpa [hχ] using mul_inv_cancel₀ hv)
    exact left_ne_zero_of_mul_eq_one (by rw [← map_mul, this, map_one])
  rw [map_mul, map_prod] at hzv
  refine ⟨z, ⟨⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩, fun q => ?_⟩, left_ne_zero_of_mul hzv⟩
  · simpa using Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hzv) k (Finset.mem_univ _)
  · refine (aeval_inst _ _ z f).trans ((hz f).trans ?_)
    rw [show χ f = 0 from Subtype.ext (by rw [hχ]; exact (hφ f).2 hf), map_zero]
  · exact hψ _

end Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

/- English proof (translation)
The claim follows from `haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective exists_algPt RM.y RM.arith.2.1.2.2 hu.2 p`.
-/
theorem exists_algPt_off (Or : RootOrigin Y S RM Fx) {u : MRing RM.ι} (hu : IsFormOff (mCoordIdeal RM.y) u)
    (p : ℕ) [Fact p.Prime] : ∃ z ∈ algPts p (mCoordIdeal RM.y), aeval z u ≠ 0 :=
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  exists_algPt RM.y RM.arith.2.1.2.2 hu.2 p

set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Apply the tactic sequence `have h3 : ∀ j, ex D 0 0 j = 0 := fun j => by cases j <;> rfl`. Establish `h1 : (1 : Rul Xo c) ∈ sec Xo c 0 0` using `⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun _ _ _ _ _ => by simp [Formalism.L2.Pj.wchar, h3]⟩`. Take `⟨v', hv', hn⟩` from `h 0 0 (a • 1) (Submodule.smul_mem _ a h1)`. Rewrite `hv'` using `[Fr.rd_smul, Fr.rd_one, mul_one]`. Rewrite using `[hasVal_unique hz.1 hv hv']`.

Rewrite `hn` using `[(pjSys Xo c).val_smul x _ _ ha, pjSys_val_one, add_zero]`. Simplify using `only [h3, pow_zero, Finset.prod_const_one] at hn`. Simplify using `using (isNormOfVal_coe hp.out.one_le he _ zero_le_one _).1 hn`.
-/
theorem norm_const {Or : RootOrigin Y S RM Fx} (Fr : GenFrame Or) {p : ℕ} [hp : Fact p.Prime]
    {z : (Σ k, RM.ι k) → PadicAlgCl p} (hz : z ∈ algPts p (mCoordIdeal RM.y)) {la : HeightOneSpectrum (𝓞 c.F)}
    (he : 0 < ramOverZ la) {x : (pjSys Xo c).Pt la} {t : Ix D → ℝ} (h : ReadsSecFin Fr z x t) {a : c.F} (ha : a ≠ 0)
    {v : PadicAlgCl p} (hv : HasVal RM.y 0 (Or.𝔐.cst a) z v) :
    ‖v‖ = (p : ℝ) ^ (-((Ref.vl la a : ℝ) / ramOverZ la)) := by
  have h3 : ∀ j, ex D 0 0 j = 0 := fun j => by cases j <;> rfl
  have h1 : (1 : Rul Xo c) ∈ sec Xo c 0 0 :=
    ⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun _ _ _ _ _ => by simp [Formalism.L2.Pj.wchar, h3]⟩
  obtain ⟨v', hv', hn⟩ := h 0 0 (a • 1) (Submodule.smul_mem _ a h1)
  rw [Fr.rd_smul, Fr.rd_one, mul_one] at hv'
  rw [hasVal_unique hz.1 hv hv']
  rw [(pjSys Xo c).val_smul x _ _ ha, pjSys_val_one, add_zero] at hn
  simp only [h3, pow_zero, Finset.prod_const_one] at hn
  simpa using (isNormOfVal_coe hp.out.one_le he _ zero_le_one _).1 hn

/- English proof (translation)
Take `⟨he, h⟩` from `Or.lines ρ`. Establish `h1` using `h q (Set.mem_univ _) ch hq`. Establish `h2 : s ^ HodgeCpt.rootSgn D ρ ∈ Or.Fl.rootLat ρ q` using `Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩`. Rewrite `h2` using `[h1, Submodule.mem_span_singleton]`. Take `⟨r, hr⟩` from `h2`.

Establish `hy : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)`. Establish `hr' : (r : RM.Ω) * ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) = s ^ HodgeCpt.rootSgn D ρ` using `hr`. Establish `hs0 : s ^ HodgeCpt.rootSgn D ρ ≠ 0` using `zpow_ne_zero _ hs.1`. Use `⟨r, r.2, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_zpow, ← hr']`.

Establish `hr0 : (r : RM.Ω) ≠ 0` using `fun h0 => hs0 (by rw [← hr', h0, zero_mul])`. Clear the denominators using the available nonvanishing facts.
-/
theorem root_sign (Or : RootOrigin Y S RM Fx) (ρ : RootIx D) (q : Cpt Or.𝔐.ξ) (ch : ∀ k, RM.ι k)
    (hq : InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q) {s : RM.Ω}
    (hs : ((Or.𝔐.V (HodgeCpt.rootIdx D ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx D ρ).1)
      (HodgeCpt.rootIdx D ρ).2).IsGenAt q s) :
    ∃ r ∈ regAt Or.𝔐.ξ q,
      (s⁻¹ ^ HodgeCpt.rootSgn D ρ) * r = (Or.e ρ)⁻¹ / ∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k := by
  obtain ⟨he, h⟩ := Or.lines ρ
  have h1 := h q (Set.mem_univ _) ch hq
  have h2 : s ^ HodgeCpt.rootSgn D ρ ∈ Or.Fl.rootLat ρ q :=
    Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩
  rw [h1, Submodule.mem_span_singleton] at h2
  obtain ⟨r, hr⟩ := h2
  have hy : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)
  have hr' : (r : RM.Ω) * ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) = s ^ HodgeCpt.rootSgn D ρ := hr
  have hs0 : s ^ HodgeCpt.rootSgn D ρ ≠ 0 := zpow_ne_zero _ hs.1
  refine ⟨r, r.2, ?_⟩
  rw [inv_zpow, ← hr']
  have hr0 : (r : RM.Ω) ≠ 0 := fun h0 => hs0 (by rw [← hr', h0, zero_mul])
  field_simp

end GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest
