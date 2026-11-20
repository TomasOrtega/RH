import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr GlobalTheory.AntiLAdic
open scoped Pointwise

namespace GlobalTheory.GalToHecke

section Tame

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.
-/
theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

/- English proof (translation)
Establish `hx0 : v.valuation L (x : L) ≠ 0` using `by simp`. Establish `hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k` using `fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k`. Establish `h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ)`. Establish `: ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]`.

Rewrite using `[this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]`. Conclude with `hxy`. Establish `h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1`. Use `Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Establish `h3 : χ.locK v (y * x⁻¹) = 1`. Use `h (atFin v (y * x⁻¹)) ?_ ?_` and prove the remaining obligations. Conclude with `(hval _).trans h2`. Establish `: ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1)`. Rewrite using `[map_sub, map_one]`.

Both sides reduce to the same expression. Rewrite using `[this, hval]`. Simplify using `using h1`. Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : v.valuation L (x : L) ≠ 0 := by simp
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hxy
  have h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1 := by
    have := Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)
    rwa [add_sub_cancel] at this
  have h3 : χ.locK v (y * x⁻¹) = 1 := by
    refine h (atFin v (y * x⁻¹)) ?_ ?_
    · exact (hval _).trans h2
    · have : ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
          algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, hval]
      simpa using h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h3

/- English proof (translation)
Establish `hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ))` using `fun v => ⟨_, v.intValuation_if_neg (ht v)⟩`. Use `choose n hn using hn`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1) (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)`. Use `⟨y, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `(v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)`.

Establish `e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v)`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := L)]`. Simplify using the standard rewrite rules. Establish `e2 : v.valuation L (t v : L) = v.intValuation (t v)` using `HeightOneSpectrum.valuation_of_algebraMap (K := L) v _`. Rewrite using `[e1, e2, hn, ← WithZero.exp_add]`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

end Tame

section Basic

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}

def IsHeckeOf (art : Ideles E →* Gab E Ω) (r : G E Ω →* ℂˣ) (χ : HChar E) : Prop :=
  ∀ (x : Ideles E) (σ : G E Ω), art x = toAb E Ω σ → χ.1 x = r σ

def heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) : HChar E :=
  ⟨(liftAb r (continuous_of_isOpen_ker' r hr)).comp art,
    (continuous_liftAb r (continuous_of_isOpen_ker' r hr)).comp ha.quot.continuous, fun k => by
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]⟩

/- English proof (translation)
Introduce `x σ h` and use `by show liftAb r (continuous_of_isOpen_ker' r hr) (art x) = r σ rw [h, liftAb_toAb]`.
-/
theorem isHeckeOf_heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) :
    IsHeckeOf art r (heckeOf ha r hr) := fun x σ h => by
  show liftAb r (continuous_of_isOpen_ker' r hr) (art x) = r σ
  rw [h, liftAb_toAb]

variable {r : G E Ω →* ℂˣ} {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

/- English proof (translation)
The claim follows from `Subtype.ext (MonoidHom.ext fun x => by obtain ⟨σ, hσ⟩ := toAb_surjective (art x) rw [h x σ hσ.symm, h' x σ hσ.symm])`.
-/
theorem IsHeckeOf.unique (h : IsHeckeOf art r χ) {χ' : HChar E} (h' : IsHeckeOf art r χ') : χ = χ' :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    rw [h x σ hσ.symm, h' x σ hσ.symm])

/- English proof (translation)
The claim follows from `Subtype.ext (MonoidHom.ext fun x => by obtain ⟨σ, hσ⟩ := toAb_surjective (art x) show χ.1 x ^ m = 1 rw [h x σ hσ.symm, hm])`.
-/
theorem IsHeckeOf.orderDvd (h : IsHeckeOf art r χ) {m : ℕ} (hm : ∀ σ, r σ ^ m = 1) : χ.OrderDvd m :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    show χ.1 x ^ m = 1
    rw [h x σ hσ.symm, hm])

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H σ hσ`. Take `⟨x, hx, e⟩` from `(ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩`. Rewrite using `[← h _ σ e]`. Conclude with `H x hx`.

Introduce `H x hx`. Take `⟨σ, hσ, e⟩` from `(ha.ine v A hA _).1 ⟨x, hx, rfl⟩`. Conclude with `(h _ σ e.symm).trans (H σ hσ)`.
-/
theorem IsHeckeOf.unr_iff (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v) :
    χ.UnrAt v ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1 := by
  constructor
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩
    rw [← h _ σ e]
    exact H x hx
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    exact (h _ σ e.symm).trans (H σ hσ)

/- English proof (translation)
Take `⟨x, hx, e⟩` from `(ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩`. Rewrite using `[← χ.val_eq hu x hx, ← map_inv]`. Conclude with `h _ _ e`.
-/
theorem IsHeckeOf.val_eq (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hu : χ.UnrAt v) (hA : IsPlaceOver A v)
    {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) : χ.val v = (r σ)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  rw [← χ.val_eq hu x hx, ← map_inv]
  exact h _ _ e

/- English proof (translation)
Establish `hm : art (localIdele E v x) ∈ (Dec (F` using `E) A).map (toAb E Ω) := by`. Rewrite using `[← ha.dec v A hA]`. Conclude with `Subgroup.le_topologicalClosure _ ⟨x, rfl⟩`. Take `⟨σ, hσ, e⟩` from `hm`. Conclude with `(h _ σ e.symm).trans (H σ hσ)`.
-/
theorem IsHeckeOf.loc_eq_one (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v)
    (H : ∀ σ ∈ Dec (F := E) A, r σ = 1) (x : (v.adicCompletion E)ˣ) : χ.loc v x = 1 := by
  have hm : art (localIdele E v x) ∈ (Dec (F := E) A).map (toAb E Ω) := by
    rw [← ha.dec v A hA]
    exact Subgroup.le_topologicalClosure _ ⟨x, rfl⟩
  obtain ⟨σ, hσ, e⟩ := hm
  exact (h _ σ e.symm).trans (H σ hσ)

/- English proof (translation)
Introduce `x _ hx`. Establish `h1 : ∀ y, χ.1 y ^ (l ^ k) = 1` using `fun y => congrArg (fun ξ : HChar E => ξ.1 y) h`. Establish `ho` using `isOpen_ker_of_pow χ.1 χ.2.1 (pow_pos hl.pos k) h1`. Set `θ : (v.adicCompletion E)ˣ →* rootsOfUnity (l ^ k) ℂ` to `(χ.loc v).codRestrict _ fun y => h1 _`. Use `GlobalTheory.RingCls.tame hl (B := rootsOfUnity (l ^ k) ℂ) (fun z => ⟨k, Subtype.ext z.2⟩) hv θ (by` as an intermediate fact.

Use `ho.preimage (Determ.continuous_localIdele v) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Conclude with `Subtype.ext_iff) x (hx.trans_lt (by simpa using exp_neg_one_lt_one))`. Conclude with `congrArg Subtype.val this`.
-/
theorem tameAt_of_orderDvd {l k : ℕ} (hl : l.Prime) (h : χ.OrderDvd (l ^ k)) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    χ.TameAt v := by
  intro x _ hx
  have h1 : ∀ y, χ.1 y ^ (l ^ k) = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  have ho := isOpen_ker_of_pow χ.1 χ.2.1 (pow_pos hl.pos k) h1
  let θ : (v.adicCompletion E)ˣ →* rootsOfUnity (l ^ k) ℂ := (χ.loc v).codRestrict _ fun y => h1 _
  have := GlobalTheory.RingCls.tame hl (B := rootsOfUnity (l ^ k) ℂ) (fun z => ⟨k, Subtype.ext z.2⟩) hv θ (by
    convert ho.preimage (Determ.continuous_localIdele v) using 1
    ext y
    exact Subtype.ext_iff) x (hx.trans_lt (by simpa using exp_neg_one_lt_one))
  exact congrArg Subtype.val this

/- English proof (translation)
Establish `h1 : ∀ y, χ.1 y ^ m = 1` using `fun y => congrArg (fun ξ : HChar E => ξ.1 y) h`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (e y) hm`. Establish `hy : e.symm z ^ m = y` using `e.injective (by rw [map_pow, e.apply_symm_apply, hz])`. Establish `h0 : e.symm z ≠ 0`.

Introduce `h0`. Rewrite `hy` using `[h0, zero_pow hm.ne']`. Conclude with `y.ne_zero hy.symm`. Establish `e1 : y = Units.mk0 _ h0 ^ m` using `Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)`. Rewrite using `[e1, map_pow]`.

Conclude with `h1 _`.
-/
theorem locInf_eq_one [IsTotallyComplex E] {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) (w : InfinitePlace E)
    (y : (w.Completion)ˣ) : χ.locInf w y = 1 := by
  have h1 : ∀ y, χ.1 y ^ m = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e y) hm
  have hy : e.symm z ^ m = y := e.injective (by rw [map_pow, e.apply_symm_apply, hz])
  have h0 : e.symm z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hy
    exact y.ne_zero hy.symm
  have e1 : y = Units.mk0 _ h0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
  rw [e1, map_pow]
  exact h1 _

end Basic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[aboveF]`.
-/
theorem mem_aboveF {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `h` using `hr P (Units.mk0 x hx)`. Unfold `ordF at h`. Establish `h1 : P.valuation E (algebraMap F E x) ≠ 0` using `by simpa using hx`.

Establish `h2 : (P.under (𝓞 F)).valuation F x ≠ 0` using `by simpa using hx`. Rewrite using `[← WithZero.exp_log h1, ← WithZero.exp_log h2]`. Conclude with `congrArg WithZero.exp (neg_injective h)`.
-/
theorem valuation_up (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    P.valuation E (algebraMap F E x) = (P.under (𝓞 F)).valuation F x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hr P (Units.mk0 x hx)
  unfold ordF at h
  have h1 : P.valuation E (algebraMap F E x) ≠ 0 := by simpa using hx
  have h2 : (P.under (𝓞 F)).valuation F x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2]
  exact congrArg WithZero.exp (neg_injective h)

/- English proof (translation)
Rewrite using `[HChar.resFin, MonoidHom.finsetProd_apply]`. Both sides reduce to the same expression.
-/
theorem resFin_eq (χ : HChar E) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := E) F v, χ.locK P (upF F k) := by
  rw [HChar.resFin, MonoidHom.finsetProd_apply]
  rfl

/- English proof (translation)
Establish `h0 : ∀ v, v ∉ T → ∀ k, χ.resFin v k = 1` using `fun v hvT k => by`. Rewrite using `[resFin_eq, Finset.prod_congr rfl (g := fun P => χ.val P ^ ordF v k) fun P hP => by`. Establish `e` using `mem_aboveF.1 hP`. Rewrite using `[GlobalTheory.HeckeProduct.locK_unr χ (hu P (e ▸ hvT)), hr, e], Finset.prod_zpow, hv v hvT, one_zpow]`. Establish `h1 : ∀ k : Fˣ, ∏ v ∈ T, χ.resFin v k = 1` using `fun k => by`.

Set `T'` to `T ∪ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset`. Establish `hS : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ T'.biUnion (aboveF (L` using `E) F) ↔ P.under (𝓞 F) ∈ T' := fun P => by`. Simplify using `[Finset.mem_biUnion, mem_aboveF, -Finset.mem_union]`. Establish `h` using `GlobalTheory.HeckeProduct.productRule χ (T'.biUnion (aboveF (L := E) F)) (fun P hP => hu P fun hm => hP ((hS P).2 (Finset.mem_union_left _ hm))) (upF F k)`. Establish `hi : χ.inf (upF F k) = 1` using `by show χ.1 (infDiag _) = 1`.

Rewrite using `[infDiag, MonoidHom.finsetProd_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => hinf w _`. Establish `hf : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ T'.biUnion (aboveF (L` using `E) F)), χ.val P ^ ordF P (upF F k)) = 1 := by`. Use `finprod_eq_one_of_forall_eq_one fun P => ?_` and prove the remaining obligations. Distinguish the cases in `hP : P ∈ T'.biUnion (aboveF (L := E) F)`.

Conclude with `finprod_eq_if.trans (if_neg (not_not.2 hP))`. Rewrite using `[finprod_eq_if, if_pos hP]`. Establish `: ordF (P.under (𝓞 F)) k = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hP ((hS P).2 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hne)))`.

Rewrite using `[hr, this, zpow_zero]`. Rewrite `h` using `[hi, hf, one_mul, mul_one, Finset.prod_biUnion (fun v _ v' _ hne => Finset.disjoint_left.2 fun P h1 h2 => hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2)))]`. Rewrite using `[← h]`. Simplify using `only [← resFin_eq]`. Conclude with `Finset.prod_subset Finset.subset_union_left fun v _ hvT => h0 v hvT k`.

Establish `h2 : ∀ v (x y : Fˣ), v.valuation F ((y : F) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation F (x : F) → χ.resFin v y = χ.resFin v x` using `fun v x y hxy => by`. Rewrite using `[resFin_eq, resFin_eq]`. Use `Finset.prod_congr rfl fun P hP => locK_eq_of_tame χ (htame P) _ _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.valuation E (algebraMap F E y - algebraMap F E x) ≤ _ * P.valuation E (algebraMap F E x)`. Rewrite using `[← map_sub, valuation_up hr, valuation_up hr, mem_aboveF.1 hP]`.

Conclude with `hxy`. Use `⟨fun v k => ?_, fun w k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hvT : v ∈ T swap`. Conclude with `h0 v hvT k`. Establish `key : ∀ (a : 𝓞 F) (ha : (a : F) ≠ 0), χ.resFin v (Units.mk0 (a : F) ha) = 1`.

Introduce `a ha`. Establish `ha' : a ≠ 0` using `fun h => ha (by simp [h])`. Take `⟨y, hy⟩` from `exists_approx T (fun u => if u = v then a else 1) (fun u => by split_ifs; exacts [ha', one_ne_zero])`. Establish `hP` using `hy v hvT`. Simplify using `only [if_true] at hP`.

Establish `hy0 : (y : F) ≠ 0`. Introduce `h0`. Rewrite `hP` using `[h0, zero_sub, Valuation.map_neg]`. Establish `hpos : 0 < v.valuation F (a : F)` using `zero_lt_iff.2 (by simpa using ha')`. Use `mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Conclude with `absurd hP (not_le.2 this)`. Rewrite using `[← h2 v (Units.mk0 (a : F) ha) (Units.mk0 (y : F) hy0) hP, ← h1 (Units.mk0 (y : F) hy0)]`. Use `symm`. Use `Finset.prod_eq_single_of_mem v hvT fun u hu hne => ?_` and prove the remaining obligations.

Establish `h3` using `hy u hu`. Simplify using `only [if_neg hne] at h3`. Rewrite using `[h2 u 1 _ (by simpa using h3), map_one]`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (𝓞 F) (k : F)`. Establish `hb0 : (b : F) ≠ 0` using `by simpa using nonZeroDivisors.ne_zero hb`.

Establish `ha0 : (a : F) ≠ 0`. Introduce `h`. Apply `k.ne_zero` to reduce the goal to its premises. Rewrite using `[← hab]`. Express the relevant statement in the definitionally equal form `(a : F) / _ = 0`.

Rewrite using `[h, zero_div]`. Establish `hx : k = Units.mk0 (a : F) ha0 * (Units.mk0 (b : F) hb0)⁻¹`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]`. Both sides reduce to the same expression.

Rewrite using `[hx, map_mul, map_inv, key, key, inv_one, mul_one]`. Rewrite using `[HChar.resInf, MonoidHom.finsetProd_apply]`. Conclude with `Finset.prod_eq_one fun w' _ => hinf w' _`.
-/
theorem trivOn_of_cofinite (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (χ : HChar E) (htame : ∀ P, χ.TameAt P) (hinf : ∀ w y, χ.locInf w y = 1) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ T → χ.UnrAt P)
    (hv : ∀ v, v ∉ T → ∏ P ∈ aboveF (L := E) F v, χ.val P = 1) : χ.TrivOn F := by
  classical
  have h0 : ∀ v, v ∉ T → ∀ k, χ.resFin v k = 1 := fun v hvT k => by
    rw [resFin_eq, Finset.prod_congr rfl (g := fun P => χ.val P ^ ordF v k) fun P hP => by
      have e := mem_aboveF.1 hP
      rw [GlobalTheory.HeckeProduct.locK_unr χ (hu P (e ▸ hvT)), hr, e], Finset.prod_zpow, hv v hvT, one_zpow]
  have h1 : ∀ k : Fˣ, ∏ v ∈ T, χ.resFin v k = 1 := fun k => by
    let T' := T ∪ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
    have hS : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ T'.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ T' := fun P => by
      simp [Finset.mem_biUnion, mem_aboveF, -Finset.mem_union]
    have h := GlobalTheory.HeckeProduct.productRule χ (T'.biUnion (aboveF (L := E) F))
      (fun P hP => hu P fun hm => hP ((hS P).2 (Finset.mem_union_left _ hm))) (upF F k)
    have hi : χ.inf (upF F k) = 1 := by
      show χ.1 (infDiag _) = 1
      rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
      exact Finset.prod_eq_one fun w _ => hinf w _
    have hf : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ T'.biUnion (aboveF (L := E) F)),
        χ.val P ^ ordF P (upF F k)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun P => ?_
      by_cases hP : P ∈ T'.biUnion (aboveF (L := E) F)
      · exact finprod_eq_if.trans (if_neg (not_not.2 hP))
      rw [finprod_eq_if, if_pos hP]
      have : ordF (P.under (𝓞 F)) k = 0 := by
        by_contra hne
        exact hP ((hS P).2 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hne)))
      rw [hr, this, zpow_zero]
    rw [hi, hf, one_mul, mul_one, Finset.prod_biUnion (fun v _ v' _ hne => Finset.disjoint_left.2 fun P h1 h2 =>
      hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2)))] at h
    rw [← h]
    simp only [← resFin_eq]
    exact Finset.prod_subset Finset.subset_union_left fun v _ hvT => h0 v hvT k
  have h2 : ∀ v (x y : Fˣ), v.valuation F ((y : F) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation F (x : F) →
      χ.resFin v y = χ.resFin v x := fun v x y hxy => by
    rw [resFin_eq, resFin_eq]
    refine Finset.prod_congr rfl fun P hP => locK_eq_of_tame χ (htame P) _ _ ?_
    change P.valuation E (algebraMap F E y - algebraMap F E x) ≤ _ * P.valuation E (algebraMap F E x)
    rw [← map_sub, valuation_up hr, valuation_up hr, mem_aboveF.1 hP]
    exact hxy
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · by_cases hvT : v ∈ T
    swap
    · exact h0 v hvT k
    have key : ∀ (a : 𝓞 F) (ha : (a : F) ≠ 0), χ.resFin v (Units.mk0 (a : F) ha) = 1 := by
      intro a ha
      have ha' : a ≠ 0 := fun h => ha (by simp [h])
      obtain ⟨y, hy⟩ := exists_approx T (fun u => if u = v then a else 1)
        (fun u => by split_ifs; exacts [ha', one_ne_zero])
      have hP := hy v hvT
      simp only [if_true] at hP
      have hy0 : (y : F) ≠ 0 := by
        intro h0
        rw [h0, zero_sub, Valuation.map_neg] at hP
        have hpos : 0 < v.valuation F (a : F) := zero_lt_iff.2 (by simpa using ha')
        have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
        rw [one_mul] at this
        exact absurd hP (not_le.2 this)
      rw [← h2 v (Units.mk0 (a : F) ha) (Units.mk0 (y : F) hy0) hP, ← h1 (Units.mk0 (y : F) hy0)]
      symm
      refine Finset.prod_eq_single_of_mem v hvT fun u hu hne => ?_
      have h3 := hy u hu
      simp only [if_neg hne] at h3
      rw [h2 u 1 _ (by simpa using h3), map_one]
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (k : F)
    have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
    have ha0 : (a : F) ≠ 0 := by
      intro h
      apply k.ne_zero
      rw [← hab]
      change (a : F) / _ = 0
      rw [h, zero_div]
    have hx : k = Units.mk0 (a : F) ha0 * (Units.mk0 (b : F) hb0)⁻¹ := by
      apply Units.ext
      rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
    rw [hx, map_mul, map_inv, key, key, inv_one, mul_one]
  · rw [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun w' _ => hinf w' _

end Adelic

section Galois

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field Ω] [Algebra E Ω]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normV_eq (v : HeightOneSpectrum (𝓞 E)) : normV v = Ideal.absNorm v.asIdeal := rfl

/- English proof (translation)
Use `set v := P.under (𝓞 F) with hv`. Use `P.isPrime` as an intermediate fact. Use `v.isMaximal` as an intermediate fact. Establish `: P.asIdeal.LiesOver v.asIdeal` using `⟨rfl⟩`. Establish `he : v.asIdeal.ramificationIdx' P.asIdeal = 1`.

Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `h` using `HeightOneSpectrum.valuation_liesOver E v P π`. Rewrite `h` using `[valuation_up hr, ← hv, hπ, ← WithZero.exp_nsmul, WithZero.exp_inj]`. Simplify using `using h`. Establish `hs` using `Ideal.sum_ramification_inertia (𝓞 E) F E v.ne_bot`.

Establish `hset : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {P.asIdeal}`. Use extensionality with `Q`. Rewrite using `[← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset v.ne_bot, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hQ, hl⟩`.

Conclude with `congrArg HeightOneSpectrum.asIdeal (hP ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩ (HeightOneSpectrum.ext hl.over.symm))`. Introduce and unpack `rfl`. Conclude with `⟨inferInstance, inferInstance⟩`. Rewrite `hs` using `[hset, Finset.sum_singleton, he, one_mul, h2]`. Rewrite using `[normV_eq, normV_eq, ← hs]`.

Conclude with `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot`.
-/
theorem normV_inert (h2 : Module.finrank F E = 2)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P) :
    normV P = normV (P.under (𝓞 F)) ^ 2 := by
  set v := P.under (𝓞 F) with hv
  have := P.isPrime
  have := v.isMaximal
  have : P.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have h := HeightOneSpectrum.valuation_liesOver E v P π
    rw [valuation_up hr, ← hv, hπ, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
    simpa using h
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E v.ne_bot
  have hset : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {P.asIdeal} := by
    ext Q
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset v.ne_bot, Finset.mem_singleton]
    constructor
    · rintro ⟨hQ, hl⟩
      exact congrArg HeightOneSpectrum.asIdeal
        (hP ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩ (HeightOneSpectrum.ext hl.over.symm))
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  rw [hset, Finset.sum_singleton, he, one_mul, h2] at hs
  rw [normV_eq, normV_eq, ← hs]
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot

/- English proof (translation)
Introduce `h`. Use `P.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field P.asIdeal`. Establish `hfin : Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)`.

Establish `hc : Fintype.card (𝓞 E ⧸ P.asIdeal) = q ^ 2` using `by rw [← hq, ← Nat.card_eq_fintype_card]; rfl`. Establish `h1 : 1 < q`. Establish `: 1 < q ^ 2` using `hc ▸ Fintype.one_lt_card`. Conclude with `(Nat.one_lt_pow_iff two_ne_zero).1 this`. Establish `h3` using `Polynomial.card_le_degree_of_subset_roots (p := (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P.asIdeal))) (Z := Finset.univ) (fun z _ => by`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h1)]`. Simplify using `using Ideal.Quotient.eq_zero_iff_mem.2 (h x))`. Rewrite `h3` using `[FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, Finset.card_univ, hc]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem not_forall_pow_sub_mem {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : normV P = q ^ 2) :
    ¬ ∀ x : 𝓞 E, x ^ q - x ∈ P.asIdeal := by
  intro h
  classical
  have := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have hc : Fintype.card (𝓞 E ⧸ P.asIdeal) = q ^ 2 := by rw [← hq, ← Nat.card_eq_fintype_card]; rfl
  have h1 : 1 < q := by
    have : 1 < q ^ 2 := hc ▸ Fintype.one_lt_card
    exact (Nat.one_lt_pow_iff two_ne_zero).1 this
  have h3 := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P.asIdeal))) (Z := Finset.univ) (fun z _ => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h1)]
      simpa using Ideal.Quotient.eq_zero_iff_mem.2 (h x))
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, Finset.card_univ, hc] at h3
  nlinarith

/- English proof (translation)
Rewrite `ha`, `hb` using `[A.valuation_le_one_iff]`. Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ q`. Establish `e : a ^ q - b ^ q = (a - b) * c` using `congrArg Subtype.val hc`. Rewrite using `[e, map_mul]`. Conclude with `(mul_le_of_le_one_right' (A.valuation_le_one c)).trans_lt h`.
-/
theorem valuation_pow_sub_pow_lt (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1)
    (h : A.valuation (a - b) < 1) (q : ℕ) : A.valuation (a ^ q - b ^ q) < 1 := by
  rw [A.valuation_le_one_iff] at ha hb
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ q
  have e : a ^ q - b ^ q = (a - b) * c := congrArg Subtype.val hc
  rw [e, map_mul]
  exact (mul_le_of_le_one_right' (A.valuation_le_one c)).trans_lt h

/- English proof (translation)
Use `letI : Algebra F Ω := ((algebraMap E Ω).comp (algebraMap F E)).toAlgebra`. Use `haveI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩`. Establish `: Algebra.IsQuadraticExtension F E` using `{ finrank_eq_two' := h2 }`. Establish `: IsGalois F E` using `inferInstance`.

Establish `hall : ∀ σ : E ≃ₐ[F] E, σ = 1 ∨ σ = c`. Introduce `σ`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`. Distinguish the cases in `h : σ = 1`.

Conclude with `Or.inl h`. Conclude with `Or.inr ((hy σ h).trans (hy c hne).symm)`. Establish `hAv : IsPlaceOver A (P.under (𝓞 F))` using `fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)`. Take `⟨τ, hτ⟩` from `exists_isFrob hAv`. Establish `hq` using `normV_inert h2 hr hP`.

Use `set q := normV (P.under (𝓞 F))`. Establish `hτd : τ ∈ Dec (F` using `F) A := hτ.1`. Establish `hres : ∀ x : E, τ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormal τ E x)` using `fun x => (AlgEquiv.restrictNormal_commutes τ E x).symm`. Break down `hall (AlgEquiv.restrictNormal τ E) with h | h` into its components or cases. It suffices to derive a contradiction.

Use `not_forall_pow_sub_mem hq fun x => (hA _).1 ?_` and prove the remaining obligations. Establish `hx : A.valuation (algebraMap E Ω (x : E)) ≤ 1`. Conclude with `Valuation.Integers.mem_of_integral (Valuation.valuationSubring.integers A.valuation) (((RingOfIntegers.isIntegral_coe x).map (algebraMap E Ω).toIntAlgHom).tower_top)`. Establish `h1` using `hτ.2 _ hx`. Rewrite `h1` using `[hres, h, ← Valuation.map_neg, neg_sub]`.

Simplify using `using h1`. Establish `hs : ∀ x, cc.symm x = cc x` using `fun x => by rw [RingEquiv.symm_apply_eq, hcc2]`. Set `g : G E Ω` to `{ cc.trans (τ : Ω ≃+* Ω) with commutes' := fun x => by show τ (cc (algebraMap E Ω x)) = _`. Rewrite using `[hcc, hres, h, hinv] }`. Set `g' : G E Ω` to `{ (τ : Ω ≃+* Ω).trans cc with commutes' := fun x => by show cc (τ (algebraMap E Ω x)) = _`.

Rewrite using `[hres, h, hcc, hinv] }`. Establish `e : ∀ x, (g * g') x = τ (τ x)` using `fun x => by show τ (cc (cc (τ x))) = _`. Rewrite using `[hcc2]`. Use `⟨g, g', fun x => ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `show cc (τ x) = cc (τ (cc (cc.symm x)))`.

Rewrite using `[cc.apply_symm_apply]`. Use `show g * g' ∈ Dec (F := E) A`. Rewrite using `[mem_Dec]`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`.

Take `⟨z, rfl⟩` from `(g * g').surjective x`. Establish `h1 : ((g * g')⁻¹ : G E Ω) ((g * g') z) = z` using `(g * g').symm_apply_apply z`. Rewrite using `[h1, e, apply_mem_iff_of_mem_Dec hτd, apply_mem_iff_of_mem_Dec hτd]`. Establish `hx' : A.valuation (τ x) ≤ 1`. Rewrite `hx`, the goal using `[A.valuation_le_one_iff]`.

Conclude with `(apply_mem_iff_of_mem_Dec hτd x).2 hx`. Establish `e2 : (g * g') x - x ^ normV P = (τ (τ x) - τ x ^ q) + (τ x ^ q - (x ^ q) ^ q)`. Rewrite using `[e, hq, sq, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `Valuation.map_add_lt _ (hτ.2 _ hx') (valuation_pow_sub_pow_lt A hx' (by rw [map_pow]; exact pow_le_one' hx q) (hτ.2 x hx) q)`.
-/
theorem exists_frob_inert [IsAlgClosure E Ω] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A P) :
    ∃ g g' : G E Ω, (∀ x, g' x = cc (g (cc.symm x))) ∧ IsFrob (F := E) A (normV P) (g * g') := by
  letI : Algebra F Ω := ((algebraMap E Ω).comp (algebraMap F E)).toAlgebra
  haveI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have : IsGalois F E := inferInstance
  have hall : ∀ σ : E ≃ₐ[F] E, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hne).symm)
  have hAv : IsPlaceOver A (P.under (𝓞 F)) := fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨τ, hτ⟩ := exists_isFrob hAv
  have hq := normV_inert h2 hr hP
  set q := normV (P.under (𝓞 F))
  have hτd : τ ∈ Dec (F := F) A := hτ.1
  have hres : ∀ x : E, τ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormal τ E x) := fun x =>
    (AlgEquiv.restrictNormal_commutes τ E x).symm
  rcases hall (AlgEquiv.restrictNormal τ E) with h | h
  · exfalso
    refine not_forall_pow_sub_mem hq fun x => (hA _).1 ?_
    have hx : A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
      exact Valuation.Integers.mem_of_integral (Valuation.valuationSubring.integers A.valuation)
        (((RingOfIntegers.isIntegral_coe x).map (algebraMap E Ω).toIntAlgHom).tower_top)
    have h1 := hτ.2 _ hx
    rw [hres, h, ← Valuation.map_neg, neg_sub] at h1
    simpa using h1
  · have hs : ∀ x, cc.symm x = cc x := fun x => by rw [RingEquiv.symm_apply_eq, hcc2]
    let g : G E Ω := { cc.trans (τ : Ω ≃+* Ω) with
      commutes' := fun x => by
        show τ (cc (algebraMap E Ω x)) = _
        rw [hcc, hres, h, hinv] }
    let g' : G E Ω := { (τ : Ω ≃+* Ω).trans cc with
      commutes' := fun x => by
        show cc (τ (algebraMap E Ω x)) = _
        rw [hres, h, hcc, hinv] }
    have e : ∀ x, (g * g') x = τ (τ x) := fun x => by
      show τ (cc (cc (τ x))) = _
      rw [hcc2]
    refine ⟨g, g', fun x => ?_, ?_, fun x hx => ?_⟩
    · show cc (τ x) = cc (τ (cc (cc.symm x)))
      rw [cc.apply_symm_apply]
    · show g * g' ∈ Dec (F := E) A
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
      obtain ⟨z, rfl⟩ := (g * g').surjective x
      have h1 : ((g * g')⁻¹ : G E Ω) ((g * g') z) = z := (g * g').symm_apply_apply z
      rw [h1, e, apply_mem_iff_of_mem_Dec hτd, apply_mem_iff_of_mem_Dec hτd]
    · have hx' : A.valuation (τ x) ≤ 1 := by
        rw [A.valuation_le_one_iff] at hx ⊢
        exact (apply_mem_iff_of_mem_Dec hτd x).2 hx
      have e2 : (g * g') x - x ^ normV P = (τ (τ x) - τ x ^ q) + (τ x ^ q - (x ^ q) ^ q) := by
        rw [e, hq, sq, pow_mul]; ring
      rw [e2]
      exact Valuation.map_add_lt _ (hτ.2 _ hx')
        (valuation_pow_sub_pow_lt A hx' (by rw [map_pow]; exact pow_le_one' hx q) (hτ.2 x hx) q)

/- English proof (translation)
Establish `hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y` using `fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, hcc, hinv]⟩`. Establish `hu : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset.image (fun P => P.under (𝓞 F)) → χ.UnrAt P`. Introduce `P hP`. Assume the negation of the conclusion as `hn`. Conclude with `hP (Finset.mem_image.2 ⟨P, by simpa using hn, rfl⟩)`.

Use `trivOn_of_cofinite hr χ htame (locInf_eq_one hm ho) _ hu fun v hv => ?_` and prove the remaining obligations. Break down `(aboveF (L := E) F v).eq_empty_or_nonempty with h0 | ⟨P, hP⟩` into its components or cases. Rewrite using `[h0, Finset.prod_empty]`. Take `rfl` from `mem_aboveF.1 hP`. Take `⟨P', hP'⟩` from `(existsUnique_conjPl c.toRingEquiv P).exists`.

Establish `hs : aboveF (L` using `E) F (P.under (𝓞 F)) = {P, P'} := by`. Use extensionality with `Q`. Rewrite using `[mem_aboveF, under_eq_iff_conjPl c h2 hne P Q, Finset.mem_insert, Finset.mem_singleton]`. Use `or_congr Iff.rfl ⟨fun h' => (existsUnique_conjPl _ P).unique h' hP', ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hP'`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω P`. Distinguish the cases in `e : P = P'`. Substitute `e` using the available equality. Rewrite `hs` using `[Finset.pair_eq_singleton]`.

Take `⟨g, g', hg, hσ⟩` from `exists_frob_inert c h2 hne hinv hr cc hcc hcc2 (fun Q hQ => Finset.mem_singleton.1 (hs ▸ mem_aboveF.2 hQ)) hA`. Rewrite using `[hs, Finset.prod_singleton, h.val_eq ha (hu P hv) hA hσ, map_mul, hanti g g' hg, mul_inv_cancel, inv_one]`. Take `⟨σ, hσ⟩` from `exists_isFrob hA`. Establish `hA'` using `isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) hcc hP' hA`. Establish `hσ'` using `isFrob_conjHom cc hc hσ`.

Rewrite `hσ'` using `[← normV_conjPl hP']`. Establish `hu' : χ.UnrAt P'` using `hu P' (by`. Rewrite using `[mem_aboveF.1 (hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self P') : P' ∈ aboveF F (P.under (𝓞 F)))])` and apply the resulting hypothesis. Rewrite using `[hs, Finset.prod_pair e, h.val_eq ha (hu P hv) hA hσ, h.val_eq ha hu' hA' hσ', hanti σ _ (conjHom_apply cc hc σ), inv_inv, inv_mul_cancel]`.
-/
theorem IsHeckeOf.trivOn [IsAlgClosure E Ω] [IsTotallyComplex E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : HChar E} (h : IsHeckeOf art r χ)
    (hanti : AntiHom cc r) {m : ℕ} (hm : 0 < m) (ho : χ.OrderDvd m) (htame : ∀ P, χ.TameAt P) : χ.TrivOn F := by
  classical
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x =>
    ⟨c x, by rw [RingEquiv.symm_apply_eq, hcc, hinv]⟩
  have hu : ∀ P : HeightOneSpectrum (𝓞 E),
      P.under (𝓞 F) ∉ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset.image (fun P => P.under (𝓞 F)) → χ.UnrAt P := by
    intro P hP
    by_contra hn
    exact hP (Finset.mem_image.2 ⟨P, by simpa using hn, rfl⟩)
  refine trivOn_of_cofinite hr χ htame (locInf_eq_one hm ho) _ hu fun v hv => ?_
  rcases (aboveF (L := E) F v).eq_empty_or_nonempty with h0 | ⟨P, hP⟩
  · rw [h0, Finset.prod_empty]
  obtain rfl := mem_aboveF.1 hP
  obtain ⟨P', hP'⟩ := (existsUnique_conjPl c.toRingEquiv P).exists
  have hs : aboveF (L := E) F (P.under (𝓞 F)) = {P, P'} := by
    ext Q
    rw [mem_aboveF, under_eq_iff_conjPl c h2 hne P Q, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h' => (existsUnique_conjPl _ P).unique h' hP', ?_⟩
    rintro rfl
    exact hP'
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω P
  by_cases e : P = P'
  · subst e
    rw [Finset.pair_eq_singleton] at hs
    obtain ⟨g, g', hg, hσ⟩ := exists_frob_inert c h2 hne hinv hr cc hcc hcc2
      (fun Q hQ => Finset.mem_singleton.1 (hs ▸ mem_aboveF.2 hQ)) hA
    rw [hs, Finset.prod_singleton, h.val_eq ha (hu P hv) hA hσ, map_mul, hanti g g' hg, mul_inv_cancel, inv_one]
  · obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have hA' := isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) hcc hP' hA
    have hσ' := isFrob_conjHom cc hc hσ
    rw [← normV_conjPl hP'] at hσ'
    have hu' : χ.UnrAt P' := hu P' (by
      rwa [mem_aboveF.1 (hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self P') : P' ∈ aboveF F (P.under (𝓞 F)))])
    rw [hs, Finset.prod_pair e, h.val_eq ha (hu P hv) hA hσ, h.val_eq ha hu' hA' hσ',
      hanti σ _ (conjHom_apply cc hc σ), inv_inv, inv_mul_cancel]

end Galois

end GlobalTheory.GalToHecke

end
