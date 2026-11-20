import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Rewrite using `[← T.val, (valuation T.Fp).vle_iff_le]`.
-/
theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

/- English proof (translation)
Establish `h` using `val_le_iff T x 1`. Simplify using `only [map_one] at h`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem mem_int_iff (T : LocAt F E sig p) (x : F) :
    T.ιF x ∈ 𝒪[T.Fp] ↔ p.valuation F x ≤ 1 := by
  have h := val_le_iff T x 1
  simp only [map_one] at h
  rw [← h]; rfl

/- English proof (translation)
Establish `h` using `val_le_iff T 1 x`. Simplify using `only [map_one] at h`. Rewrite using `[← not_le, ← not_le, h]`.
-/
theorem val_lt_one_iff (T : LocAt F E sig p) (x : F) :
    valuation T.Fp (T.ιF x) < 1 ↔ p.valuation F x < 1 := by
  have h := val_le_iff T 1 x
  simp only [map_one] at h
  rw [← not_le, ← not_le, h]

/- English proof (translation)
Use `haveI := T.lf`. Establish `hm : ∀ z : 𝒪[T.Fp], z ∈ Ideal.span {ϖ} ↔ valuation T.Fp (z : T.Fp) < 1`. Introduce `z`. Rewrite using `[← h.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Set `φ : 𝓞 F →+* 𝒪[T.Fp]` to `(T.ιF.comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => (mem_int_iff T _).2 (p.valuation_le_one a))`.

Establish `hφ : ∀ a, ((φ a : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a)` using `fun a => rfl`. Set `ψ : 𝓞 F →+* 𝒪[T.Fp] ⧸ Ideal.span {ϖ}` to `(Ideal.Quotient.mk _).comp φ`. Establish `hker : RingHom.ker ψ = p.asIdeal`. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker]`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (φ a) = 0 ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hm, hφ, val_lt_one_iff]`. Conclude with `p.valuation_lt_one_iff_mem (K := F) a`. Establish `hsurj : Function.Surjective ψ`. Introduce `w`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Establish `hn : {z : T.Fp | valuation T.Fp (z - y) < 1} ∈ nhds (y : T.Fp)` using `IsValuativeTopology.mem_nhds_iff'.2 ⟨1, fun z hz => by simpa using hz⟩`. Take `⟨x, hx⟩` from `T.dense.mem_nhds hn`. Establish `hx' : valuation T.Fp (T.ιF x - y) < 1` using `hx`. Establish `hy : valuation T.Fp (y : T.Fp) ≤ 1` using `y.2`.

Establish `hx1 : valuation T.Fp (T.ιF x) ≤ 1`. Establish `: T.ιF x = (T.ιF x - y) + y` using `by ring`. Rewrite using `[this]`. Conclude with `(valuation T.Fp).map_add_le hx'.le hy`. Take `⟨a, ha⟩` from `p.exists_valuation_sub_lt_of_integer ((mem_int_iff T x).1 hx1) 1`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (φ a) = _`. Rewrite using `[Ideal.Quotient.eq, hm]`. Establish `ha'` using `(val_lt_one_iff T _).2 (by simpa using ha : p.valuation F (algebraMap (𝓞 F) F a - x) < 1)`. Establish `: ((φ a - y : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - y)`.

Rewrite using `[map_sub, ← hφ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(valuation T.Fp).map_add_lt ha' hx'`.

Rewrite using `[resQ, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]`. Conclude with `(Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm`.
-/
theorem resQ_eq_absNorm (T : LocAt F E sig p) (ϖ : 𝒪[T.Fp]) (h : Irreducible ϖ) :
    resQ ϖ = Ideal.absNorm p.asIdeal := by
  haveI := T.lf
  have hm : ∀ z : 𝒪[T.Fp], z ∈ Ideal.span {ϖ} ↔ valuation T.Fp (z : T.Fp) < 1 := by
    intro z
    rw [← h.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  let φ : 𝓞 F →+* 𝒪[T.Fp] := (T.ιF.comp (algebraMap (𝓞 F) F)).codRestrict _
    (fun a => (mem_int_iff T _).2 (p.valuation_le_one a))
  have hφ : ∀ a, ((φ a : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a) := fun a => rfl
  let ψ : 𝓞 F →+* 𝒪[T.Fp] ⧸ Ideal.span {ϖ} := (Ideal.Quotient.mk _).comp φ
  have hker : RingHom.ker ψ = p.asIdeal := by
    ext a
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (φ a) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hm, hφ, val_lt_one_iff]
    exact p.valuation_lt_one_iff_mem (K := F) a
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hn : {z : T.Fp | valuation T.Fp (z - y) < 1} ∈ nhds (y : T.Fp) :=
      IsValuativeTopology.mem_nhds_iff'.2 ⟨1, fun z hz => by simpa using hz⟩
    obtain ⟨x, hx⟩ := T.dense.mem_nhds hn
    have hx' : valuation T.Fp (T.ιF x - y) < 1 := hx
    have hy : valuation T.Fp (y : T.Fp) ≤ 1 := y.2
    have hx1 : valuation T.Fp (T.ιF x) ≤ 1 := by
      have : T.ιF x = (T.ιF x - y) + y := by ring
      rw [this]
      exact (valuation T.Fp).map_add_le hx'.le hy
    obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer ((mem_int_iff T x).1 hx1) 1
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (φ a) = _
    rw [Ideal.Quotient.eq, hm]
    have ha' := (val_lt_one_iff T _).2 (by simpa using ha : p.valuation F (algebraMap (𝓞 F) F a - x) < 1)
    have : ((φ a - y : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - y) := by
      rw [map_sub, ← hφ]; push_cast; ring
    rw [this]
    exact (valuation T.Fp).map_add_lt ha' hx'
  rw [resQ, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

/- English proof (translation)
The claim follows from `Module.nontrivial_of_finrank_pos (R := T.Fp) (by rw [T.rank]; norm_num)`.
-/
theorem nontrivial_Ep (T : LocAt F E sig p) : Nontrivial T.Ep :=
  Module.nontrivial_of_finrank_pos (R := T.Fp) (by rw [T.rank]; norm_num)

/- English proof (translation)
Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `p : HeightOneSpectrum (𝓞 F)` to `⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩`. Use `haveI := nontrivial_Ep (A.loc p)`. Establish `hss : ∀ y, sig (sig y) = y`. Introduce `y`.

Apply `(A.loc p).ιE.injective` to reduce the goal to its premises. Rewrite using `[← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]`. Establish `hfix : ∀ y, sig y = y → ∃ a, algebraMap F E a = y` using `by haveI := Subalgebra.isSimpleOrder_of_finrank A.quad`. Break down `eq_bot_or_eq_top (AlgHom.equalizer sig (AlgHom.id F E)) with h | h` into its components or cases. Introduce `y hy`.

Establish `: y ∈ AlgHom.equalizer sig (AlgHom.id F E)` using `hy`. Rewrite `this` using `[h, Algebra.mem_bot]`. Conclude with `this`. It suffices to derive a contradiction. Establish `h1 : ∀ y, sig y = y` using `fun y => by`.

Establish `: y ∈ AlgHom.equalizer sig (AlgHom.id F E)` using `by rw [h]; trivial`. Conclude with `this`. Establish `h2 : ∀ z, (A.loc p).cj z = z`. Introduce `z`. Establish `hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE)`.

Rewrite using `[(A.loc p).span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨y, rfl⟩ := hz`. Rewrite using `[(A.loc p).cj_ιE, h1]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `smul c a _ ha => rw [map_smul, ha]`. Establish `h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep)`. Introduce `z`.

Conclude with `((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)`. Establish `h4` using `LinearMap.finrank_le_finrank_of_surjective h3`. Rewrite `h4` using `[(A.loc p).rank, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers. Take `⟨t, ht⟩` from `hfix (x + sig x) (by rw [map_add, hss, add_comm])`.

Take `⟨n, hn⟩` from `hfix (x * sig x) (by rw [map_mul, hss, mul_comm])`. Conclude with `⟨t, n, ht, hn⟩`.
-/
theorem exists_trace_norm (A : Places F E sig) (x : E) :
    ∃ t n : F, algebraMap F E t = x + sig x ∧ algebraMap F E n = x * sig x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := nontrivial_Ep (A.loc p)
  have hss : ∀ y, sig (sig y) = y := by
    intro y
    apply (A.loc p).ιE.injective
    rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]
  have hfix : ∀ y, sig y = y → ∃ a, algebraMap F E a = y := by
    haveI := Subalgebra.isSimpleOrder_of_finrank A.quad
    rcases eq_bot_or_eq_top (AlgHom.equalizer sig (AlgHom.id F E)) with h | h
    · intro y hy
      have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := hy
      rw [h, Algebra.mem_bot] at this
      exact this
    · exfalso
      have h1 : ∀ y, sig y = y := fun y => by
        have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := by rw [h]; trivial
        exact this
      have h2 : ∀ z, (A.loc p).cj z = z := by
        intro z
        have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
          rw [(A.loc p).span]; trivial
        induction hz using Submodule.span_induction with
        | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, h1]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, ha, hb]
        | smul c a _ ha => rw [map_smul, ha]
      have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
        intro z
        exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
      have h4 := LinearMap.finrank_le_finrank_of_surjective h3
      rw [(A.loc p).rank, Module.finrank_self] at h4
      omega
  obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add, hss, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hss, mul_comm])
  exact ⟨t, n, ht, hn⟩

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ht, hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isIntegral_of_quad {R S : Type} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    (x y : S) (t n : R) (ht : algebraMap R S t = x + y) (hn : algebraMap R S n = x * y) :
    IsIntegral R x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ht, hn]
    ring

/- English proof (translation)
Use `haveI := (A.loc p).lf`. Use `haveI := (A.loc p).char0`. Use `haveI := nontrivial_Ep (A.loc p)`. Establish `ht' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF t) = (A.loc p).ιE x + (A.L p).cj ((A.loc p).ιE x)`. Rewrite using `[← (A.loc p).compat, ht, map_add, A.L_cj, (A.loc p).cj_ιE]`.

Establish `hn' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF n) = (A.loc p).ιE x * (A.L p).cj ((A.loc p).ιE x)`. Rewrite using `[← (A.loc p).compat, hn, map_mul, A.L_cj, (A.loc p).cj_ιE]`. Rewrite using `[← mem_int_iff (A.loc p), ← mem_int_iff (A.loc p)]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[(A.loc p).Fp]`. Take `⟨-, ⟨c, hc⟩, d, hd⟩` from `(GlobalTheory.UnramOrder.order_facts (A.L p) ϖ hϖ).2.1 _ hx`. Establish `hinj` using `(algebraMap (A.loc p).Fp (A.loc p).Ep).injective`. Rewrite using `[hinj (ht'.trans hc), hinj (hn'.trans hd)]`. Conclude with `⟨c.2, d.2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Rewrite using `[(A.L p).O_def]`. Conclude with `isIntegral_of_quad (R := 𝒪[(A.loc p).Fp]) _ _ ⟨_, h1⟩ ⟨_, h2⟩ ht' hn'`.
-/
theorem mem_O_iff (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) (t n : F)
    (ht : algebraMap F E t = x + sig x) (hn : algebraMap F E n = x * sig x) :
    (A.loc p).ιE x ∈ (A.L p).O ↔ p.valuation F t ≤ 1 ∧ p.valuation F n ≤ 1 := by
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI := nontrivial_Ep (A.loc p)
  have ht' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF t)
      = (A.loc p).ιE x + (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, ht, map_add, A.L_cj, (A.loc p).cj_ιE]
  have hn' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF n)
      = (A.loc p).ιE x * (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, hn, map_mul, A.L_cj, (A.loc p).cj_ιE]
  rw [← mem_int_iff (A.loc p), ← mem_int_iff (A.loc p)]
  constructor
  · intro hx
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[(A.loc p).Fp]
    obtain ⟨-, ⟨c, hc⟩, d, hd⟩ := (GlobalTheory.UnramOrder.order_facts (A.L p) ϖ hϖ).2.1 _ hx
    have hinj := (algebraMap (A.loc p).Fp (A.loc p).Ep).injective
    rw [hinj (ht'.trans hc), hinj (hn'.trans hd)]
    exact ⟨c.2, d.2⟩
  · rintro ⟨h1, h2⟩
    rw [(A.L p).O_def]
    exact isIntegral_of_quad (R := 𝒪[(A.loc p).Fp]) _ _ ⟨_, h1⟩ ⟨_, h2⟩ ht' hn'

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A`. Use `⟨fun x => ⟨fun hx => ?_, ?_⟩, fun x => ?_, fun x p => mem_int_iff _ x, fun p ϖ h => resQ_eq_absNorm _ ϖ h⟩` and prove the remaining obligations. Take `⟨t, n, ht, hn⟩` from `exists_trace_norm A x`. Establish `h` using `fun p => (mem_O_iff A p x t n ht hn).1 (hx p)`. Take `⟨t', ht'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t (fun p => (h p).1)`.

Take `⟨n', hn'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F n (fun p => (h p).2)`. Establish `hi : IsIntegral (𝓞 F) x` using `isIntegral_of_quad x (sig x) t' n' (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ht', ht]) (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hn', hn])`. Conclude with `⟨⟨x, isIntegral_trans (R := ℤ) x hi⟩, rfl⟩`. Introduce and unpack `⟨o, rfl⟩ p`. Rewrite using `[(A.L p).O_def]`.

Establish `h : IsIntegral ℤ ((A.loc p).ιE (o : E))` using `map_isIntegral_int (A.loc p).ιE o.isIntegral_coe`. Conclude with `h.tower_top`. Take `⟨t, n, ht, hn⟩` from `exists_trace_norm A x`. Use `((HeightOneSpectrum.Support.finite (𝓞 F) t).union (HeightOneSpectrum.Support.finite (𝓞 F) n)).subset fun p hp => ?_` and prove the remaining obligations. Establish `hp' : ¬ ((A.loc p).ιE x ∈ (A.L p).O)` using `hp`.

Rewrite `hp'` using `[mem_O_iff A p x t n ht hn, not_and_or, not_le, not_le]`. Conclude with `hp'`.
-/
theorem integers_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), (∀ x : E, (∀ p, (A.loc p).ιE x ∈ (A.L p).O) ↔ ∃ o : 𝓞 E, (o : E) = x) ∧ (∀ x : E, {p | (A.loc p).ιE x ∉ (A.L p).O}.Finite) ∧ (∀ (x : F) p, (A.loc p).ιF x ∈ 𝒪[(A.loc p).Fp] ↔ p.valuation F x ≤ 1) ∧ ∀ p (ϖ : 𝒪[(A.loc p).Fp]), Irreducible ϖ → resQ ϖ = Ideal.absNorm p.asIdeal := by
  intro F E _ _ _ _ _ sig A
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun x => ?_, fun x p => mem_int_iff _ x,
    fun p ϖ h => resQ_eq_absNorm _ ϖ h⟩
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    have h := fun p => (mem_O_iff A p x t n ht hn).1 (hx p)
    obtain ⟨t', ht'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t
      (fun p => (h p).1)
    obtain ⟨n', hn'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F n
      (fun p => (h p).2)
    have hi : IsIntegral (𝓞 F) x := isIntegral_of_quad x (sig x) t' n'
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ht', ht])
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hn', hn])
    exact ⟨⟨x, isIntegral_trans (R := ℤ) x hi⟩, rfl⟩
  · rintro ⟨o, rfl⟩ p
    rw [(A.L p).O_def]
    have h : IsIntegral ℤ ((A.loc p).ιE (o : E)) :=
      map_isIntegral_int (A.loc p).ιE o.isIntegral_coe
    exact h.tower_top
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    refine ((HeightOneSpectrum.Support.finite (𝓞 F) t).union
      (HeightOneSpectrum.Support.finite (𝓞 F) n)).subset fun p hp => ?_
    have hp' : ¬ ((A.loc p).ιE x ∈ (A.L p).O) := hp
    rw [mem_O_iff A p x t n ht hn, not_and_or, not_le, not_le] at hp'
    exact hp'

end GlobalTheory.HL.PlacesInt
