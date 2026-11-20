import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

/- English proof (translation)
Establish `hopen : IsOpen {x : v.adicCompletion F | (x - a) * c⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion F))}` using `(Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage ((continuous_sub_right _).mul continuous_const)`. Take `⟨y, hy⟩` from `(v.denseRange_algebraMap (K := F)).exists_mem_open hopen ⟨a, by simp⟩`. Establish `hvc : Valued.v c ≠ 0` using `(Valuation.ne_zero_iff _).2 hc0`. Establish `hy' : Valued.v (algebraMap F (v.adicCompletion F) y - a) ≤ Valued.v c`. Establish `h1 : Valued.v ((algebraMap F (v.adicCompletion F) y - a) * c⁻¹) ≤ 1` using `(Valuation.mem_valuationSubring_iff _ _).1 hy`.

Rewrite `h1` using `[map_mul, map_inv₀]`. Establish `h2` using `mul_le_mul' h1 (le_refl (Valued.v c))`. Rewrite `h2` using `[mul_assoc, inv_mul_cancel₀ hvc, mul_one, one_mul]`. Then use the resulting hypothesis. Establish `ha1 : Valued.v a ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha`. Establish `e2 : ∀ z : F, Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z` using `fun z => v.valuedAdicCompletion_eq_valuation' z`.

Establish `hy1 : v.valuation F y ≤ 1`. Rewrite using `[← e2]`. Establish `e : algebraMap F (v.adicCompletion F) y = (algebraMap F (v.adicCompletion F) y - a) + a` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ (hy'.trans hc) ha1`.

Take `⟨r, hr⟩` from `v.exists_valuation_sub_lt_of_integer hy1 (Units.mk0 (Valued.v c) hvc)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hr' : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) ≤ Valued.v c`. Rewrite using `[← map_sub, e2]`. Conclude with `hr.le`.

Establish `e : a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) = -(algebraMap F (v.adicCompletion F) y - a) - (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y)` using `by ring`. Rewrite using `[e]`. Use `le_trans (Valuation.map_sub _ _ _) (max_le ?_ hr')` and prove the remaining obligations. Rewrite using `[Valuation.map_neg]`. Conclude with `hy'`.
-/
theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) (c : v.adicCompletion F) (hc0 : c ≠ 0) (hc : Valued.v c ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) ≤ Valued.v c := by
  have hopen : IsOpen {x : v.adicCompletion F |
      (x - a) * c⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion F))} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      ((continuous_sub_right _).mul continuous_const)
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hopen ⟨a, by simp⟩
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  have hy' : Valued.v (algebraMap F (v.adicCompletion F) y - a) ≤ Valued.v c := by
    have h1 : Valued.v ((algebraMap F (v.adicCompletion F) y - a) * c⁻¹) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).1 hy
    rw [map_mul, map_inv₀] at h1
    have h2 := mul_le_mul' h1 (le_refl (Valued.v c))
    rwa [mul_assoc, inv_mul_cancel₀ hvc, mul_one, one_mul] at h2
  have ha1 : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha
  have e2 : ∀ z : F, Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z := fun z =>
    v.valuedAdicCompletion_eq_valuation' z
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← e2]
    have e : algebraMap F (v.adicCompletion F) y = (algebraMap F (v.adicCompletion F) y - a) + a := by ring
    rw [e]
    exact Valuation.map_add_le _ (hy'.trans hc) ha1
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hy1 (Units.mk0 (Valued.v c) hvc)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) ≤ Valued.v c := by
    rw [← map_sub, e2]
    exact hr.le
  have e : a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      -(algebraMap F (v.adicCompletion F) y - a) - (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hr')
  rw [Valuation.map_neg]; exact hy'

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

/- English proof (translation)
Establish `h1 : inclE (F` using `F) ((A.pl v).1.adicCompletion F) (algebraMap F E f) = (1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f := by`. Express the relevant statement in the definitionally equal form `algebraMap F E f ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F) = _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]`. Simplify using `only [LocAt.iw, LocAt.phE, LocAt.ph, RingHom.comp_apply, h1]`. Rewrite using `[show (A.spl v).toRingHom ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) = A.spl v ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) from rfl, hA v]`.

Both sides reduce to the same expression.
-/
theorem iw_algebraMap (A : LocAt F E n G) (hA : SplAlg A) (v : Fin G.P.nV) (f : F) :
    A.iw v (algebraMap F E f) = (A.eQ v).symm (algebraMap F ((A.pl v).1.adicCompletion F) f) := by
  have h1 : inclE (F := F) ((A.pl v).1.adicCompletion F) (algebraMap F E f) =
      (1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f := by
    change algebraMap F E f ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  simp only [LocAt.iw, LocAt.phE, LocAt.ph, RingHom.comp_apply, h1]
  rw [show (A.spl v).toRingHom ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) =
    A.spl v ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) from rfl, hA v]
  rfl

/- English proof (translation)
Use `haveI := (G.P.setting v).frac_alt`. Establish `h1 : IsIntegral ℤ (A.iw v (x : E))` using `x.2.map (A.iw v).toIntAlgHom`. Establish `h2 : IsIntegral (G.P.W v) (A.iw v (x : E))` using `h1.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Conclude with `⟨y, hy⟩`.
-/
theorem iw_int (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    A.iw v (x : E) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have h1 : IsIntegral ℤ (A.iw v (x : E)) := x.2.map (A.iw v).toIntAlgHom
  have h2 : IsIntegral (G.P.W v) (A.iw v (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def toW (A : LocAt F E n G) (v : Fin G.P.nV) : 𝓞 E →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  (RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩).symm.toRingHom.comp
    (((A.iw v).comp (algebraMap (𝓞 E) E)).codRestrict _ (fun x => iw_int A v x))

/- English proof (translation)
Use `haveI := (G.P.setting v).frac_alt`. Use `set e := RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h), (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩ with he`. Establish `h : (e (toW A v x) : G.P.Qq v) = A.iw v (x : E)`. Simplify using `only [toW, he, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]`. Rewrite using `[← h]`.

Both sides reduce to the same expression.
-/
theorem toW_spec (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    algebraMap (G.P.W v) (G.P.Qq v) (toW A v x) = A.iw v (x : E) := by
  haveI := (G.P.setting v).frac_alt
  set e := RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩ with he
  have h : (e (toW A v x) : G.P.Qq v) = A.iw v (x : E) := by
    simp only [toW, he, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]
  rw [← h]
  rfl

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

/- English proof (translation)
The claim follows from `(G.P.setting v).p_unif`.
-/
theorem p_irr (v : Fin G.P.nV) : Irreducible ((p : ℕ) : G.P.W v) := (G.P.setting v).p_unif

def primeAt (A : LocAt F E n G) (v : Fin G.P.nV) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)})
  isPrime := by
    haveI : (Ideal.span {((p : ℕ) : G.P.W v)}).IsPrime :=
      (Ideal.span_singleton_prime (p_irr (G := G) v).ne_zero).2 (p_irr (G := G) v).prime
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hm : ((p : ℕ) : 𝓞 E) ∈ Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)}) := by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _
    rw [h, Ideal.mem_bot] at hm
    have hp0 : ((p : ℕ) : G.P.W v) = 0 := by
      have := congrArg (toW A v) hm; rwa [map_natCast, map_zero] at this
    exact (p_irr (G := G) v).ne_zero hp0

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ Ideal.comap (toW A v) _ ↔ _`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`.
-/
theorem mem_primeAt (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    x ∈ (primeAt A v).asIdeal ↔ ((p : ℕ) : G.P.W v) ∣ toW A v x := by
  change x ∈ Ideal.comap (toW A v) _ ↔ _
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]

/- English proof (translation)
Introduce `F E _ _ _ _ _ n p _ G A hW hA v`. Use `⟨primeAt A v, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `⟨toW A v x, (toW_spec A v x).symm, mem_primeAt A v x⟩`. Introduce `y k set K := (A.pl v).1.adicCompletion F`.

Establish `ha : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y) ∈ (A.pl v).1.adicCompletionIntegers F` using `(hW v _).1 ⟨y, rfl⟩`. Establish `hpK : ((p : ℕ) : K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F K)]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)`. Establish `hc0 : ((p : ℕ) : K) ^ k ≠ 0` using `pow_ne_zero _ hpK`.

Establish `hp1 : Valued.v ((p : ℕ) : K) ≤ 1`. Establish `e2 : Valued.v (algebraMap F K ((p : ℕ) : F)) = (A.pl v).1.valuation F ((p : ℕ) : F)` using `(A.pl v).1.valuedAdicCompletion_eq_valuation' _`. Rewrite using `[← map_natCast (algebraMap F K), e2, ← map_natCast (algebraMap (𝓞 F) F)]`. Conclude with `(A.pl v).1.valuation_le_one _`. Establish `hc : Valued.v (((p : ℕ) : K) ^ k) ≤ 1`.

Rewrite using `[map_pow]`. Conclude with `pow_le_one₀ zero_le' hp1`. Take `⟨r, hr⟩` from `exists_int_near (A.pl v).1 _ ha _ hc0 hc`. Use `set a := A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y)`. Use `set d := a - algebraMap F K (algebraMap (𝓞 F) F r)`.

Establish `hdq : d * (((p : ℕ) : K) ^ k)⁻¹ ∈ (A.pl v).1.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]`. Establish `hv0 : Valued.v (((p : ℕ) : K) ^ k) ≠ 0` using `(Valuation.ne_zero_iff _).2 hc0`. Combine the equalities or inequalities in the displayed calculation. Take `⟨z', hz'⟩` from `(hW v ((A.eQ v).symm (d * (((p : ℕ) : K) ^ k)⁻¹))).2 (by rwa [RingEquiv.apply_symm_apply])`.

Use `⟨algebraMap (𝓞 F) (𝓞 E) r, -z', ?_⟩` and prove the remaining obligations. Establish `hx : ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F r)`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]`. Rewrite using `[hx, iw_algebraMap A hA v]`.

Establish `e1 : algebraMap F K (algebraMap (𝓞 F) F r) = a - (((p : ℕ) : K) ^ k) * (d * (((p : ℕ) : K) ^ k)⁻¹)`. Rewrite using `[mul_comm d, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`. Simplify using `[d]`. Rewrite using `[e1, map_sub, map_mul, map_pow, map_natCast, ← hz', RingEquiv.symm_apply_apply]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mem_primeAt, map_natCast]`. Introduce `h`. Establish `h1 : toW A v ((p : ℕ) : 𝓞 E) ∈ Ideal.map (toW A v) ((primeAt A v).asIdeal ^ 2)` using `Ideal.mem_map_of_mem _ h`. Rewrite `h1` using `[Ideal.map_pow, map_natCast]`.

Establish `h2 : Ideal.map (toW A v) (primeAt A v).asIdeal ^ 2 ≤ (Ideal.span {((p : ℕ) : G.P.W v)}) ^ 2` using `Ideal.pow_right_mono (Ideal.map_comap_le) 2`. Establish `h3` using `h2 h1`. Rewrite `h3` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `hi` using `p_irr (G := G) v`. Take `⟨c, hc⟩` from `h3`.

Establish `: ((p : ℕ) : G.P.W v) * (((p : ℕ) : G.P.W v) * c) = ((p : ℕ) : G.P.W v) * 1` using `by rw [mul_one, ← mul_assoc, ← sq, ← hc]`. Establish `hu` using `mul_left_cancel₀ hi.ne_zero this`. Conclude with `hi.not_isUnit ⟨⟨_, c, hu, by rw [mul_comm]; exact hu⟩, rfl⟩`.
-/
theorem exists_primeOf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ)
    [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E),
    PrimeOf p (G.P.W v) (A.iw v) P ∧
    (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧
    ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro F E _ _ _ _ _ n p _ G A hW hA v
  refine ⟨primeAt A v, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨toW A v x, (toW_spec A v x).symm, mem_primeAt A v x⟩
  · intro y k
    set K := (A.pl v).1.adicCompletion F
    have ha : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y) ∈ (A.pl v).1.adicCompletionIntegers F :=
      (hW v _).1 ⟨y, rfl⟩
    have hpK : ((p : ℕ) : K) ≠ 0 := by
      rw [← map_natCast (algebraMap F K)]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have hc0 : ((p : ℕ) : K) ^ k ≠ 0 := pow_ne_zero _ hpK
    have hp1 : Valued.v ((p : ℕ) : K) ≤ 1 := by
      have e2 : Valued.v (algebraMap F K ((p : ℕ) : F)) = (A.pl v).1.valuation F ((p : ℕ) : F) :=
        (A.pl v).1.valuedAdicCompletion_eq_valuation' _
      rw [← map_natCast (algebraMap F K), e2, ← map_natCast (algebraMap (𝓞 F) F)]
      exact (A.pl v).1.valuation_le_one _
    have hc : Valued.v (((p : ℕ) : K) ^ k) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le' hp1
    obtain ⟨r, hr⟩ := exists_int_near (A.pl v).1 _ ha _ hc0 hc
    set a := A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y)
    set d := a - algebraMap F K (algebraMap (𝓞 F) F r)
    have hdq : d * (((p : ℕ) : K) ^ k)⁻¹ ∈ (A.pl v).1.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      have hv0 : Valued.v (((p : ℕ) : K) ^ k) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
      calc Valued.v d * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ ≤ Valued.v (((p : ℕ) : K) ^ k) * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ :=
            mul_le_mul' hr le_rfl
        _ = 1 := mul_inv_cancel₀ hv0
    obtain ⟨z', hz'⟩ := (hW v ((A.eQ v).symm (d * (((p : ℕ) : K) ^ k)⁻¹))).2 (by rwa [RingEquiv.apply_symm_apply])
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, -z', ?_⟩
    have hx : ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F r) := by
      change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [hx, iw_algebraMap A hA v]
    have e1 : algebraMap F K (algebraMap (𝓞 F) F r) = a - (((p : ℕ) : K) ^ k) * (d * (((p : ℕ) : K) ^ k)⁻¹) := by
      rw [mul_comm d, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; simp [d]
    rw [e1, map_sub, map_mul, map_pow, map_natCast, ← hz', RingEquiv.symm_apply_apply]
    simp only [map_add, map_mul, map_pow, map_natCast, map_neg]
    ring
  · rw [mem_primeAt, map_natCast]
  · intro h
    have h1 : toW A v ((p : ℕ) : 𝓞 E) ∈ Ideal.map (toW A v) ((primeAt A v).asIdeal ^ 2) := Ideal.mem_map_of_mem _ h
    rw [Ideal.map_pow, map_natCast] at h1
    have h2 : Ideal.map (toW A v) (primeAt A v).asIdeal ^ 2 ≤ (Ideal.span {((p : ℕ) : G.P.W v)}) ^ 2 :=
      Ideal.pow_right_mono (Ideal.map_comap_le) 2
    have h3 := h2 h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    have hi := p_irr (G := G) v
    obtain ⟨c, hc⟩ := h3
    have : ((p : ℕ) : G.P.W v) * (((p : ℕ) : G.P.W v) * c) = ((p : ℕ) : G.P.W v) * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
    have hu := mul_left_cancel₀ hi.ne_zero this
    exact hi.not_isUnit ⟨⟨_, c, hu, by rw [mul_comm]; exact hu⟩, rfl⟩

end GlobalTheory.TwV.Xc.PrimeAt

end
