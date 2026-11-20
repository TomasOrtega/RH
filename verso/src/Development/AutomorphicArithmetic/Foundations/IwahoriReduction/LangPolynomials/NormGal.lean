import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumTriv
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)`.
-/
private theorem ng_add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ r) (fun _ _ => ng_add_le) (by simpa using hr) h`.
-/
private theorem ng_sum_le {l : ℕ} [Fact l.Prime] {ι : Type} (F : Finset ι) (f : ι → Qbar l) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i ∈ F, ‖f i‖ ≤ r) : ‖∑ i ∈ F, f i‖ ≤ r :=
  Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ r) (fun _ _ => ng_add_le) (by simpa using hr) h

/- English proof (translation)
Establish `h1` using `((pBasEx l c).2 β).1`. Establish `e : x = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨x, hx⟩ i)`. Use `congrArg (fun y : c.O => (y : PadicAlgCl l)) (β.e.sum_repr ⟨x, hx⟩)` as an intermediate fact. Simplify using `only [AddSubmonoidClass.coe_finset_sum] at this`. Use `this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[mul_comm, ← Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `ng_sum_le _ _ zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `mul_le_one₀ (h1 i) (norm_nonneg _) ?_` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Conclude with `PadicInt.norm_le_one _`.
-/
private theorem ng_O {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  have h1 := ((pBasEx l c).2 β).1
  have e : x = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨x, hx⟩ i) := by
    have := congrArg (fun y : c.O => (y : PadicAlgCl l)) (β.e.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finset_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [mul_comm, ← Algebra.smul_def]
    rfl
  rw [e]
  refine ng_sum_le _ _ zero_le_one fun i _ => ?_
  rw [norm_mul]
  refine mul_le_one₀ (h1 i) (norm_nonneg _) ?_
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact PadicInt.norm_le_one _

/- English proof (translation)
Use `haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩`. Establish `h` using `congrArg Units.val hx`. Simplify using `only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one] at h`. Rewrite `h` using `[ZMod.cast_eq_val]`. Establish `: (((((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) - 1 : ℤ) : ZMod (l ^ m)) = 0`.

Rewrite using `[Int.cast_sub, Int.cast_natCast, h, Int.cast_one, sub_self]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this` after adjusting the coercions.
-/
private theorem ng_dvd {l m : ℕ} [Fact l.Prime] (x : (ZMod (l ^ (m + 1)))ˣ) (hx : red l m x = 1) :
    ((l : ℤ) ^ m) ∣ (((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) - 1 := by
  haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  have h := congrArg Units.val hx
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one] at h
  rw [ZMod.cast_eq_val] at h
  have : (((((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) - 1 : ℤ) : ZMod (l ^ m)) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, h, Int.cast_one, sub_self]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/- English proof (translation)
Use `haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩`. Establish `h1` using `ng_dvd x hx`. Establish `h2 : ((l : ℕ) : ℤ) ∣ (((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) - 1` using `(dvd_pow_self _ (by omega)).trans h1`. Establish `h3` using `mul_dvd_mul (dvd_geom_sum₂_self h2) h1`. Rewrite `h3` using `[Commute.geom_sum₂_mul (Commute.all _ _), one_pow, ← pow_succ']`.

Establish `h4 : ((((((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) ^ l - 1 : ℤ)) : ZMod (l ^ (m + 1))) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ (m + 1))).2 (by exact_mod_cast h3)`. Use `ext`. Rewrite `h4` using `[Int.cast_sub, Int.cast_pow, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one, sub_eq_zero]`. Simplify using `using h4`.
-/
private theorem ng_pow {l m : ℕ} [Fact l.Prime] (hm : 1 ≤ m) (x : (ZMod (l ^ (m + 1)))ˣ) (hx : red l m x = 1) :
    x ^ l = 1 := by
  haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  have h1 := ng_dvd x hx
  have h2 : ((l : ℕ) : ℤ) ∣ (((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) - 1 := (dvd_pow_self _ (by omega)).trans h1
  have h3 := mul_dvd_mul (dvd_geom_sum₂_self h2) h1
  rw [Commute.geom_sum₂_mul (Commute.all _ _), one_pow, ← pow_succ'] at h3
  have h4 : ((((((x : ZMod (l ^ (m + 1))).val : ℕ) : ℤ) ^ l - 1 : ℤ)) : ZMod (l ^ (m + 1))) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ (m + 1))).2 (by exact_mod_cast h3)
  ext
  rw [Int.cast_sub, Int.cast_pow, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one, sub_eq_zero] at h4
  simpa using h4

/- English proof (translation)
Establish `h` using `ZMod.val_coe_unit_coprime x`. Introduce `hd`. Use `Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd h) (dvd_pow_self l (by omega))` as an intermediate fact. Conclude with `(Fact.out : l.Prime).one_lt.ne' this`.
-/
private theorem ng_ndvd {l m : ℕ} [Fact l.Prime] (x : (ZMod (l ^ (m + 1)))ˣ) : ¬ l ∣ (x : ZMod (l ^ (m + 1))).val := by
  have h := ZMod.val_coe_unit_coprime x
  intro hd
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd h) (dvd_pow_self l (by omega))
  exact (Fact.out : l.Prime).one_lt.ne' this

/- English proof (translation)
Use `haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩`. Use `ext`. Simplify using `[un]`.
-/
private theorem ng_un {l m : ℕ} [Fact l.Prime] (x : (ZMod (l ^ (m + 1)))ˣ) : un _ (ng_ndvd x) (m + 1) = x := by
  haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  ext
  simp [un]

/- English proof (translation)
Unfold `pv`. Rewrite using `[Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow]`.
-/
private theorem ng_expand {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (b : ℕ) (z : Ω) :
    pv (Polynomial.expand (R0 A) b P) z = pv P (z ^ b) := by
  unfold pv
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow]

/- English proof (translation)
Unfold `pv`. Use `Polynomial.hom_eval₂ P (R0 A).subtype (s : Ω →+* Ω) z` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `x`.

Conclude with `x.2.2 s hs`.
-/
private theorem ng_map {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A) : s (pv P z) = pv P (s z) := by
  unfold pv
  have := Polynomial.hom_eval₂ P (R0 A).subtype (s : Ω →+* Ω) z
  refine this.trans ?_
  congr 1
  ext x
  exact x.2.2 s hs

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Rewrite `h1`, `h3` using `[← A.valuation_le_one_iff]`. Rewrite `h3` using `[map_inv₀, inv_le_one₀ (by simpa [zero_lt_iff] using h2)]`. Conclude with `le_antisymm h1 h3`.

Introduce `h`. Use `⟨(A.valuation_le_one_iff _).1 h.le, ?_, (A.valuation_le_one_iff _).1 (by simp [h])⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at h`.
-/
private theorem ng_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (u : Ω) :
    (u ∈ A ∧ u ≠ 0 ∧ u⁻¹ ∈ A) ↔ A.valuation u = 1 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [← A.valuation_le_one_iff] at h1 h3
    rw [map_inv₀, inv_le_one₀ (by simpa [zero_lt_iff] using h2)] at h3
    exact le_antisymm h1 h3
  · intro h
    refine ⟨(A.valuation_le_one_iff _).1 h.le, ?_, (A.valuation_le_one_iff _).1 (by simp [h])⟩
    rintro rfl
    simp at h

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos (Fact.out : l.Prime).pos i).ne'⟩`. Use `infer_instance`.
-/
private theorem ng_enough (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (i : ℕ) :
    HasEnoughRootsOfUnity Ω (l ^ i) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos (Fact.out : l.Prime).pos i).ne'⟩
  infer_instance

/- English proof (translation)
Take `⟨η, hη⟩ : ∃ η, η = s v / v` from `⟨_, rfl⟩`. Establish `he : s v = η * v` using `by rw [hη]; field_simp`. Establish `h1 : η ^ N = 1` using `by rw [hη, div_pow, ← map_pow, hq, div_self (pow_ne_zero _ hv)]`. Establish `h2 : s η = η` using `hfix η h1`. Establish `h3 : ∀ k : ℕ, (s ^ k) v = η ^ k * v`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, h2, he, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4 : η ^ l = 1`. Use `h3 l` as an intermediate fact. Rewrite `this` using `[hl]`. Conclude with `mul_right_cancel₀ hv (by rw [one_mul]; exact this.symm)`. Rewrite using `[map_pow, he, mul_pow, h4, one_mul]`.
-/
private theorem ng_root {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N l : ℕ} (s : G ℚ Ω) (v : Ω) (hv : v ≠ 0)
    (hq : s (v ^ N) = v ^ N) (hfix : ∀ t : Ω, t ^ N = 1 → s t = t) (hl : (s ^ l) v = v) : s (v ^ l) = v ^ l := by
  obtain ⟨η, hη⟩ : ∃ η, η = s v / v := ⟨_, rfl⟩
  have he : s v = η * v := by rw [hη]; field_simp
  have h1 : η ^ N = 1 := by rw [hη, div_pow, ← map_pow, hq, div_self (pow_ne_zero _ hv)]
  have h2 : s η = η := hfix η h1
  have h3 : ∀ k : ℕ, (s ^ k) v = η ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, h2, he, pow_succ]; ring
  have h4 : η ^ l = 1 := by
    have := h3 l
    rw [hl] at this
    exact mul_right_cancel₀ hv (by rw [one_mul]; exact this.symm)
  rw [map_pow, he, mul_pow, h4, one_mul]

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos hlp.pos _).ne'⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩`.

Establish `hz : ζ (m + 1) ^ l ^ (m + 1) = 1` using `(hζ (m + 1)).1.pow_eq_one`. Take `⟨y, hyd⟩ : ∃ y, y = cycMod ℚ Ω l (m + 1) s` from `⟨_, rfl⟩`. Establish `hy : red l m y = 1`. Rewrite using `[hyd]`. Conclude with `(IwC.map_cycMod_succ (Ω := Ω) (l := l) m s).trans hs.2`.

Establish `hsz : s (ζ (m + 1)) = ζ (m + 1) ^ (y : ZMod (l ^ (m + 1))).val`. Rewrite using `[hyd]`. Conclude with `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (ζ (m + 1)) hz`. Rewrite using `[map_prod]`. Use `Finset.prod_equiv (Equiv.mulLeft y) ?_ ?_` and prove the remaining obligations.

Introduce `x`. Simplify using `[hy]`. Introduce `x _`. Rewrite using `[ng_map _ _ s hs.1, map_pow, hsz, ← pow_mul]`. Simplify using `only [Equiv.coe_mulLeft, Units.val_mul]`.

Rewrite using `[ZMod.val_mul, ← pow_eq_pow_mod _ hz]`.
-/
private theorem ng_fix {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {A : ValuationSubring Ω} {ζ : ℕ → Ω} (hζ : Roots l ζ) (m : ℕ) (Pi : Polynomial (R0 A))
    (s : G ℚ Ω) (hs : s ∈ Hm l A m) :
    s (∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv Pi (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) =
      ∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv Pi (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos hlp.pos _).ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩
  have hz : ζ (m + 1) ^ l ^ (m + 1) = 1 := (hζ (m + 1)).1.pow_eq_one
  obtain ⟨y, hyd⟩ : ∃ y, y = cycMod ℚ Ω l (m + 1) s := ⟨_, rfl⟩
  have hy : red l m y = 1 := by
    rw [hyd]
    exact (IwC.map_cycMod_succ (Ω := Ω) (l := l) m s).trans hs.2
  have hsz : s (ζ (m + 1)) = ζ (m + 1) ^ (y : ZMod (l ^ (m + 1))).val := by
    rw [hyd]
    exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (ζ (m + 1)) hz
  rw [map_prod]
  refine Finset.prod_equiv (Equiv.mulLeft y) ?_ ?_
  · intro x
    simp [hy]
  · intro x _
    rw [ng_map _ _ s hs.1, map_pow, hsz, ← pow_mul]
    simp only [Equiv.coe_mulLeft, Units.val_mul]
    rw [ZMod.val_mul, ← pow_eq_pow_mod _ hz]

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Use `haveI := ng_enough l Ω`. Use `haveI : NeZero (l ^ n) := ⟨(pow_pos hlp.pos _).ne'⟩`. Use `haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos hlp.pos _).ne'⟩`. Take `⟨hsI, hsc⟩` from `hs`.

Establish `hc1 : cycMod ℚ Ω l (m + 1) s = 1` using `hsc`. Establish `hc0 : cycMod ℚ Ω l m s = 1`. Rewrite using `[← IwC.map_cycMod_succ (Ω := Ω) (l := l) m s, hc1, map_one]`. Establish `hzn : s (ζ n) = ζ n` using `fix_of_cycMod (by omega) hc1 (hζ n).1.pow_eq_one`. Establish `H : ∀ x : (ZMod (l ^ (m + 1)))ˣ, ∃ k : Fin β.d → ZMod (l ^ n), (∀ i, KumVal (l` using `l) n (ζ n) (pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) s (k i)) ∧ Cg n ((((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) * Z (m + 1) s x) (∑ i, β.val i * (((k i).val : ℕ) : Qbar l)) := by`.

Introduce `x`. Establish `h` using `pPresTr l hl Ω A hA c β ζ hζ Z hZ _ (ng_ndvd x) (m + 1) n P hP`. Take `⟨k, hk, hcg⟩` from `h.2.2.2.2 s hsI hc1 hzn`. Use `⟨k, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `hk i` as an intermediate fact.

Simplify `this` using `only [ng_expand]`. Simplify using `only [tr, one_mul, ng_un] at hcg`. Conclude with `hcg`. Use `choose k hk hcg using H`. Take `⟨k', hk', hcg'⟩` from `hP'.2.2.2.2 s hsI hc0 hzn`.

Establish `kalg` using `(pKumAlg l hl Ω A hA ζ hζ (m + 1) n (by omega) s ⟨hsI, hsc⟩).1`. Establish `hprod : ∀ (F : Finset (ZMod (l ^ (m + 1)))ˣ) (i : Fin β.d), KumVal (l` using `l) n (ζ n) (∏ x ∈ F, pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) s (∑ x ∈ F, k x i) := by`. Introduce `F i`. Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => simpa using kumVal_one (l := l) n (ζ n) s`.

Consider the case `insert a F ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(kalg _ _ _ _ (hk a i) ih).1`. Establish `heq : ∀ i, ∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), k x i = k' i`. Introduce `i`.

Take `⟨xs, hxs⟩ : ∃ xs : Fin β.d → ℤ_[l], xs = fun i => ((∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), (k x i).val : ℕ) : ℤ_[l]) - (((k' i).val : ℕ) : ℤ_[l])` from `⟨_, rfl⟩`. Establish `hS : ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (xs i) = ∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), (∑ i, β.val i * (((k x i).val : ℕ) : Qbar l) - (((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) * Z (m + 1) s x) + ∑ x ∈ (Finset.univ.filter fun x …`. Rewrite using `[hZ.nrm m s hsI 1, hxs]`. Simplify using `only [map_sub, map_sum, map_natCast, Nat.cast_sum, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, one_mul]`. Rewrite using `[Finset.sum_comm]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hC : Cg n (∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (xs i)) 0`. Unfold `Cg`. Rewrite using `[sub_zero, hS]`. Use `ng_add_le (ng_add_le (ng_sum_le _ _ (norm_nonneg _) fun x _ => ?_) (ng_sum_le _ _ (norm_nonneg _) fun x hx => ?_)) hcg'` and prove the remaining obligations.

Rewrite using `[norm_sub_rev]`. Conclude with `hcg x`. Take `⟨t, ht⟩` from `ng_dvd x (Finset.mem_filter.1 hx).2`. Establish `e : (((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) - 1 = ((l : ℕ) : Qbar l) ^ n * (((l : ℕ) : Qbar l) ^ (m - n) * (t : Qbar l))`. Use `congrArg (Int.cast : ℤ → Qbar l) ht` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite using `[this, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]`. Establish `b1 : ‖((l : ℕ) : Qbar l) ^ (m - n)‖ ≤ 1`. Conclude with `IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) (l ^ (m - n))` after adjusting the coercions. Establish `b2 : ‖(t : Qbar l)‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) t`.

Establish `b3 : ‖Z (m + 1) s x‖ ≤ 1` using `ng_O β _ (hZ.int (m + 1) s hsI x)`. Rewrite using `[e, norm_mul, norm_mul, norm_mul, mul_assoc]`. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Conclude with `mul_le_one₀ (mul_le_one₀ b1 (norm_nonneg _) b2) (norm_nonneg _) b3`. Take `⟨y, hy⟩` from `((pBasEx l c).2 β).2.1 n xs hC i`.

Establish `h2` using `congrArg (PadicInt.toZModPow (p := l) n) hy`. Establish `e0 : (PadicInt.toZModPow (p` using `l) n) ((l : ℤ_[l]) ^ n) = 0 := by`. Rewrite using `[← Nat.cast_pow, map_natCast]`. Conclude with `ZMod.natCast_self (l ^ n)`. Rewrite `h2` using `[map_mul, e0, zero_mul, hxs]`.

Simplify using `only [map_sub, map_sum, map_natCast, Nat.cast_sum, ZMod.natCast_zmod_val] at h2`. Conclude with `sub_eq_zero.1 h2`. Establish `h3` using `(kalg _ _ _ _ (hprod (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1) i) (kalg _ _ _ _ (hk' i) (hk' i)).2.1).1`. Rewrite `h3` using `[heq i, add_neg_cancel]`. Conclude with `h3`.
-/
private theorem ng_kum {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {A : ValuationSubring Ω} (hA : OverL l A) {c : Coef l} (β : Bas c) {ζ : ℕ → Ω} (hζ : Roots l ζ) {Z : Sy Ω l}
    (hZ : IwI c A Z) {m n : ℕ} (hnm : n ≤ m) {P P' : Fin β.d → Polynomial (R0 A)}
    (hP : BPres β A ζ Z (m + 1) n P) (hP' : BPres β A ζ Z m n P') (i : Fin β.d)
    (s : G ℚ Ω) (hs : s ∈ Hm l A (m + 1)) :
    KumVal (l := l) n (ζ n)
      ((∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) *
        (pv (P' i) (ζ m))⁻¹) s 0 := by
  have hlp : l.Prime := Fact.out
  haveI := ng_enough l Ω
  haveI : NeZero (l ^ n) := ⟨(pow_pos hlp.pos _).ne'⟩
  haveI : NeZero (l ^ (m + 1)) := ⟨(pow_pos hlp.pos _).ne'⟩
  obtain ⟨hsI, hsc⟩ := hs
  have hc1 : cycMod ℚ Ω l (m + 1) s = 1 := hsc
  have hc0 : cycMod ℚ Ω l m s = 1 := by
    rw [← IwC.map_cycMod_succ (Ω := Ω) (l := l) m s, hc1, map_one]
  have hzn : s (ζ n) = ζ n := fix_of_cycMod (by omega) hc1 (hζ n).1.pow_eq_one
  have H : ∀ x : (ZMod (l ^ (m + 1)))ˣ, ∃ k : Fin β.d → ZMod (l ^ n),
      (∀ i, KumVal (l := l) n (ζ n) (pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) s (k i)) ∧
      Cg n ((((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) * Z (m + 1) s x) (∑ i, β.val i * (((k i).val : ℕ) : Qbar l)) := by
    intro x
    have h := pPresTr l hl Ω A hA c β ζ hζ Z hZ _ (ng_ndvd x) (m + 1) n P hP
    obtain ⟨k, hk, hcg⟩ := h.2.2.2.2 s hsI hc1 hzn
    refine ⟨k, fun i => ?_, ?_⟩
    · have := hk i
      simpa only [ng_expand] using this
    · simp only [tr, one_mul, ng_un] at hcg
      exact hcg
  choose k hk hcg using H
  obtain ⟨k', hk', hcg'⟩ := hP'.2.2.2.2 s hsI hc0 hzn
  have kalg := (pKumAlg l hl Ω A hA ζ hζ (m + 1) n (by omega) s ⟨hsI, hsc⟩).1
  have hprod : ∀ (F : Finset (ZMod (l ^ (m + 1)))ˣ) (i : Fin β.d),
      KumVal (l := l) n (ζ n) (∏ x ∈ F, pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)) s (∑ x ∈ F, k x i) := by
    intro F i
    classical
    induction F using Finset.induction_on with
    | empty => simpa using kumVal_one (l := l) n (ζ n) s
    | insert a F ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (kalg _ _ _ _ (hk a i) ih).1
  have heq : ∀ i, ∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), k x i = k' i := by
    intro i
    obtain ⟨xs, hxs⟩ : ∃ xs : Fin β.d → ℤ_[l], xs = fun i =>
      ((∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), (k x i).val : ℕ) : ℤ_[l]) -
        (((k' i).val : ℕ) : ℤ_[l]) := ⟨_, rfl⟩
    have hS : ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (xs i) =
        ∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1),
          (∑ i, β.val i * (((k x i).val : ℕ) : Qbar l) - (((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) * Z (m + 1) s x) +
        ∑ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1),
          ((((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) - 1) * Z (m + 1) s x +
        (Z m s 1 - ∑ i, β.val i * (((k' i).val : ℕ) : Qbar l)) := by
      rw [hZ.nrm m s hsI 1, hxs]
      simp only [map_sub, map_sum, map_natCast, Nat.cast_sum, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, one_mul]
      rw [Finset.sum_comm]
      ring
    have hC : Cg n (∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (xs i)) 0 := by
      unfold Cg
      rw [sub_zero, hS]
      refine ng_add_le (ng_add_le (ng_sum_le _ _ (norm_nonneg _) fun x _ => ?_) (ng_sum_le _ _ (norm_nonneg _) fun x hx => ?_)) hcg'
      · rw [norm_sub_rev]
        exact hcg x
      · obtain ⟨t, ht⟩ := ng_dvd x (Finset.mem_filter.1 hx).2
        have e : (((x : ZMod (l ^ (m + 1))).val : ℕ) : Qbar l) - 1 = ((l : ℕ) : Qbar l) ^ n * (((l : ℕ) : Qbar l) ^ (m - n) * (t : Qbar l)) := by
          have := congrArg (Int.cast : ℤ → Qbar l) ht
          push_cast at this
          rw [this, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]
        have b1 : ‖((l : ℕ) : Qbar l) ^ (m - n)‖ ≤ 1 := by
          exact_mod_cast IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) (l ^ (m - n))
        have b2 : ‖(t : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) t
        have b3 : ‖Z (m + 1) s x‖ ≤ 1 := ng_O β _ (hZ.int (m + 1) s hsI x)
        rw [e, norm_mul, norm_mul, norm_mul, mul_assoc]
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact mul_le_one₀ (mul_le_one₀ b1 (norm_nonneg _) b2) (norm_nonneg _) b3
    obtain ⟨y, hy⟩ := ((pBasEx l c).2 β).2.1 n xs hC i
    have h2 := congrArg (PadicInt.toZModPow (p := l) n) hy
    have e0 : (PadicInt.toZModPow (p := l) n) ((l : ℤ_[l]) ^ n) = 0 := by
      rw [← Nat.cast_pow, map_natCast]
      exact ZMod.natCast_self (l ^ n)
    rw [map_mul, e0, zero_mul, hxs] at h2
    simp only [map_sub, map_sum, map_natCast, Nat.cast_sum, ZMod.natCast_zmod_val] at h2
    exact sub_eq_zero.1 h2
  have h3 := (kalg _ _ _ _ (hprod (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1) i) (kalg _ _ _ _ (hk' i) (hk' i)).2.1).1
  rw [heq i, add_neg_cancel] at h3
  exact h3

/- English proof (translation)
Introduce `l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ m n hn1 hnm P P' hP hP' i`. Establish `hlp : l.Prime` using `Fact.out`. Use `haveI := ng_enough l Ω`. Establish `hm : 1 ≤ m` using `hn1.trans hnm`. Take `⟨U, hU⟩ : ∃ U, U = ∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val)` from `⟨_, rfl⟩`.

Rewrite using `[← hU]`. Establish `hV` using `(ng_unit A _).1 (hP'.2.2.1 i)`. Establish `hV0 : pv (P' i) (ζ m) ≠ 0` using `(hP'.2.2.1 i).2.1`. Establish `hUv : A.valuation U = 1`. Rewrite using `[hU, map_prod]`.

Use `Finset.prod_eq_one fun x _ => ?_` and prove the remaining obligations. Establish `h` using `(pPresTr l hl Ω A hA c β ζ hζ Z hZ _ (ng_ndvd x) (m + 1) n P hP).2.2.1 i`. Establish `h'` using `(ng_unit A _).1 h`. Simplify `h'` using `only [ng_expand]`. Establish `hU0 : U ≠ 0` using `((ng_unit A U).2 hUv).2.1`.

Establish `hq0 : U * (pv (P' i) (ζ m))⁻¹ ≠ 0` using `mul_ne_zero hU0 (inv_ne_zero hV0)`. Take `⟨v, hv, hvfix⟩` from `pKumTriv l hl Ω A hA ζ hζ (m + 1) n (by omega) (U * (pv (P' i) (ζ m))⁻¹) hq0 (fun s hs => by rw [hU]; exact ng_kum hl hA β hζ hZ hnm hP hP' i s hs)`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Rewrite `hv` using `[zero_pow (pow_pos hlp.pos n).ne']`.

Conclude with `hq0 hv.symm`. Establish `hwfix : ∀ s ∈ Hm l A m, s (v ^ l) = v ^ l`. Introduce `s hs`. Establish `hsV : s (pv (P' i) (ζ m)) = pv (P' i) (ζ m)`. Rewrite using `[ng_map _ _ s hs.1, fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one]`.

Use `ng_root (N := l ^ n) s v hv0 ?_ (fun t ht => fix_of_cycMod hnm hs.2 ht) ?_` and prove the remaining obligations. Rewrite using `[hv, map_mul, map_inv₀, hsV, hU, ng_fix hζ m (P i) s hs]`. Use `hvfix (s ^ l) ⟨pow_mem hs.1 l, ?_⟩` and prove the remaining obligations. Establish `hy : red l m (cycMod ℚ Ω l (m + 1) s) = 1` using `(IwC.map_cycMod_succ (Ω := Ω) (l := l) m s).trans hs.2`. Express the relevant statement in the definitionally equal form `cycMod ℚ Ω l (m + 1) (s ^ l) = 1`.

Rewrite using `[map_pow, ng_pow hm _ hy]`. Establish `hpow : (v ^ l) ^ l ^ (n - 1) = U * (pv (P' i) (ζ m))⁻¹`. Rewrite using `[← pow_mul, ← pow_succ', Nat.sub_add_cancel hn1, hv]`. Establish `hwv : A.valuation (v ^ l) = 1`. Establish `h1 : A.valuation (v ^ l) ^ l ^ (n - 1) = 1`.

Rewrite using `[← map_pow, hpow, map_mul, map_inv₀, hUv, hV, inv_one, one_mul]`. Conclude with `(pow_eq_one_iff_left (pow_pos hlp.pos _).ne').1 h1`. Take `⟨Q, hQ⟩` from `pPolyEx l hl Ω A hA ζ hζ m (v ^ l) ((ng_unit A _).2 hwv).1 hwfix`. Use `⟨Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ]`.

Conclude with `(ng_unit A _).2 hwv`. Rewrite using `[hQ, hpow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.Kd.C7.pNormGal :
    UpperTheory.Kd.C7.SNormGal := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ m n hn1 hnm P P' hP hP' i
  have hlp : l.Prime := Fact.out
  haveI := ng_enough l Ω
  have hm : 1 ≤ m := hn1.trans hnm
  obtain ⟨U, hU⟩ : ∃ U, U = ∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val) := ⟨_, rfl⟩
  rw [← hU]
  have hV := (ng_unit A _).1 (hP'.2.2.1 i)
  have hV0 : pv (P' i) (ζ m) ≠ 0 := (hP'.2.2.1 i).2.1
  have hUv : A.valuation U = 1 := by
    rw [hU, map_prod]
    refine Finset.prod_eq_one fun x _ => ?_
    have h := (pPresTr l hl Ω A hA c β ζ hζ Z hZ _ (ng_ndvd x) (m + 1) n P hP).2.2.1 i
    have h' := (ng_unit A _).1 h
    simpa only [ng_expand] using h'
  have hU0 : U ≠ 0 := ((ng_unit A U).2 hUv).2.1
  have hq0 : U * (pv (P' i) (ζ m))⁻¹ ≠ 0 := mul_ne_zero hU0 (inv_ne_zero hV0)
  obtain ⟨v, hv, hvfix⟩ := pKumTriv l hl Ω A hA ζ hζ (m + 1) n (by omega) (U * (pv (P' i) (ζ m))⁻¹) hq0
    (fun s hs => by rw [hU]; exact ng_kum hl hA β hζ hZ hnm hP hP' i s hs)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_pos hlp.pos n).ne'] at hv
    exact hq0 hv.symm
  have hwfix : ∀ s ∈ Hm l A m, s (v ^ l) = v ^ l := by
    intro s hs
    have hsV : s (pv (P' i) (ζ m)) = pv (P' i) (ζ m) := by
      rw [ng_map _ _ s hs.1, fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one]
    refine ng_root (N := l ^ n) s v hv0 ?_ (fun t ht => fix_of_cycMod hnm hs.2 ht) ?_
    · rw [hv, map_mul, map_inv₀, hsV, hU, ng_fix hζ m (P i) s hs]
    · refine hvfix (s ^ l) ⟨pow_mem hs.1 l, ?_⟩
      have hy : red l m (cycMod ℚ Ω l (m + 1) s) = 1 :=
        (IwC.map_cycMod_succ (Ω := Ω) (l := l) m s).trans hs.2
      change cycMod ℚ Ω l (m + 1) (s ^ l) = 1
      rw [map_pow, ng_pow hm _ hy]
  have hpow : (v ^ l) ^ l ^ (n - 1) = U * (pv (P' i) (ζ m))⁻¹ := by
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn1, hv]
  have hwv : A.valuation (v ^ l) = 1 := by
    have h1 : A.valuation (v ^ l) ^ l ^ (n - 1) = 1 := by
      rw [← map_pow, hpow, map_mul, map_inv₀, hUv, hV, inv_one, one_mul]
    exact (pow_eq_one_iff_left (pow_pos hlp.pos _).ne').1 h1
  obtain ⟨Q, hQ⟩ := pPolyEx l hl Ω A hA ζ hζ m (v ^ l) ((ng_unit A _).2 hwv).1 hwfix
  refine ⟨Q, ?_, ?_⟩
  · rw [hQ]
    exact (ng_unit A _).2 hwv
  · rw [hQ, hpow]
    field_simp
