import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Establish `hfin : ∃ N : ℕ, (t ^ (N + 1)) u = u`. Establish `hint : IsIntegral ℚ u` using `Algebra.IsIntegral.isIntegral u`. Establish `hf : ((minpoly ℚ u).rootSet Ω).Finite` using `Polynomial.rootSet_finite _ _`. Establish `hm : ∀ k : ℕ, (t ^ k) u ∈ (minpoly ℚ u).rootSet Ω` using `fun k => by`. Rewrite using `[Polynomial.mem_rootSet]`.

Use `⟨minpoly.ne_zero hint, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algEquiv]`. Simplify using the standard rewrite rules. Take `⟨i, j, hij, he⟩` from `hf.exists_lt_map_eq_of_forall_mem hm`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hij`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite `he` using `[add_assoc, pow_add, AlgEquiv.mul_apply]`. Conclude with `((t ^ i).injective he).symm`. Take `⟨N, hN⟩` from `hfin`. Establish `hne : ∀ k : ℕ, (t ^ k) u ≠ 0` using `fun k => (map_ne_zero _).2 hu`.

Establish `htu : t u ≠ 0` using `(map_ne_zero _).2 hu`. Establish `hs : ∀ k : ℕ, (t ^ (k + 1)) u = t ((t ^ k) u)` using `fun k => by rw [pow_succ', AlgEquiv.mul_apply]`. Break down `A.mem_or_inv_mem (t u / u) with h | h` into its components or cases. Establish `key : ∀ k : ℕ, (t ^ k) u / u ∈ A`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp [hu, A.one_mem]`. Consider the case `succ k ih`. Use `A.mul_mem _ _ (ht _ ih) h` as an intermediate fact. Rewrite `this` using `[map_div₀, div_mul_div_cancel₀ htu, ← hs]`. Then use the resulting hypothesis.

Use `ht _ (key N)` as an intermediate fact. Rewrite `this` using `[map_div₀, ← hs, hN]`. Conclude with `⟨this, h⟩`. Rewrite `h` using `[inv_div]`. Establish `key : ∀ k : ℕ, u / (t ^ k) u ∈ A`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hu, A.one_mem]`. Consider the case `succ k ih`. Use `A.mul_mem _ _ h (ht _ ih)` as an intermediate fact.

Rewrite `this` using `[map_div₀, div_mul_div_cancel₀ htu, ← hs]`. Then use the resulting hypothesis. Use `ht _ (key N)` as an intermediate fact. Rewrite `this` using `[map_div₀, ← hs, hN]`. Conclude with `⟨h, this⟩`.
-/
private theorem div_mem_of {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω)
    (t : G ℚ Ω) (ht : ∀ x ∈ A, t x ∈ A) (u : Ω) (hu : u ≠ 0) : u / t u ∈ A ∧ t u / u ∈ A := by
  have hfin : ∃ N : ℕ, (t ^ (N + 1)) u = u := by
    have hint : IsIntegral ℚ u := Algebra.IsIntegral.isIntegral u
    have hf : ((minpoly ℚ u).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
    have hm : ∀ k : ℕ, (t ^ k) u ∈ (minpoly ℚ u).rootSet Ω := fun k => by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp
    obtain ⟨i, j, hij, he⟩ := hf.exists_lt_map_eq_of_forall_mem hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨d, ?_⟩
    rw [add_assoc, pow_add, AlgEquiv.mul_apply] at he
    exact ((t ^ i).injective he).symm
  obtain ⟨N, hN⟩ := hfin
  have hne : ∀ k : ℕ, (t ^ k) u ≠ 0 := fun k => (map_ne_zero _).2 hu
  have htu : t u ≠ 0 := (map_ne_zero _).2 hu
  have hs : ∀ k : ℕ, (t ^ (k + 1)) u = t ((t ^ k) u) := fun k => by rw [pow_succ', AlgEquiv.mul_apply]
  rcases A.mem_or_inv_mem (t u / u) with h | h
  · have key : ∀ k : ℕ, (t ^ k) u / u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ (ht _ ih) h
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨this, h⟩
  · rw [inv_div] at h
    have key : ∀ k : ℕ, u / (t ^ k) u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ h (ht _ ih)
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨h, this⟩

/- English proof (translation)
Establish `h1` using `((pBasEx l c).2 β).1`. Establish `hw : (w : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr w i)` using `by conv_lhs => rw [← β.e.sum_repr w]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl`. Unfold `Cg`.

Rewrite using `[hw, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Establish `h2 : β.e.repr w i - ((PadicInt.toZModPow m (β.e.repr w i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m}`. Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker]`. Simplify using the standard rewrite rules.

Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 h2`. Establish `h3` using `congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he`. Rewrite `h3` using `[map_sub, map_natCast, map_mul, map_pow, map_natCast]`. Rewrite using `[← mul_sub, ← h3, norm_mul, norm_mul]`. Establish `h4 : ‖algebraMap ℤ_[l] (PadicAlgCl l) e‖ ≤ 1`.

Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Conclude with `e.2`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem cg_coord {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (m : ℕ) (w : c.O) :
    Cg m (w : PadicAlgCl l) (∑ i, β.val i * ((PadicInt.toZModPow m (β.e.repr w i)).val : Qbar l)) := by
  have h1 := ((pBasEx l c).2 β).1
  have hw : (w : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr w i) := by
    conv_lhs => rw [← β.e.sum_repr w]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  unfold Cg
  rw [hw, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  have h2 : β.e.repr w i - ((PadicInt.toZModPow m (β.e.repr w i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h3
  rw [← mul_sub, ← h3, norm_mul, norm_mul]
  have h4 : ‖algebraMap ℤ_[l] (PadicAlgCl l) e‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact e.2
  calc _ ≤ 1 * (1 * ‖((l : ℕ) : Qbar l) ^ m‖) := by gcongr; exact h1 i
    _ = _ := by ring

/- English proof (translation)
Establish `hu : IsUnit (b : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb)`. Take `⟨τ, hτ, he⟩` from `(pFrobEx l hl Ω A hA).2.2 hu.unit`. Use `⟨τ, hτ, Units.ext ?_⟩` and prove the remaining obligations.

Establish `: ((cycMod ℚ Ω l m τ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = PadicInt.toZModPow m ((cycZ ℚ Ω l τ : ℤ_[l]ˣ) : ℤ_[l])` using `rfl`. Rewrite using `[this, he]`. Simplify using `[un]`.
-/
private theorem exists_tau (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (b : ℕ) (hb : ¬ l ∣ b) (m : ℕ) :
    ∃ τ ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m τ = un b hb m := by
  have hu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb)
  obtain ⟨τ, hτ, he⟩ := (pFrobEx l hl Ω A hA).2.2 hu.unit
  refine ⟨τ, hτ, Units.ext ?_⟩
  have : ((cycMod ℚ Ω l m τ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = PadicInt.toZModPow m ((cycZ ℚ Ω l τ : ℤ_[l]ˣ) : ℤ_[l]) := rfl
  rw [this, he]
  simp [un]

/- English proof (translation)
Introduce `l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ hC b hb`. Use `⟨0, 0, fun m _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.sub_zero]`. Use `haveI : NeZero (l : Ω) := by haveI : CharZero Ω := algebraRat.charZero Ω`. Conclude with `⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩`.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨τ, hτ, hτb⟩` from `exists_tau l hl Ω A hA b hb m`. Take `⟨U, hU, hUZ⟩` from `hC m m`. Set `w : G ℚ Ω → c.O` to `fun s => if h : s ∈ Ine (F := ℚ) A then ⟨Z m s 1, hZ.int m s h 1⟩ else 0`. Establish `hw : ∀ s ∈ Ine (F` using `ℚ) A, (w s : PadicAlgCl l) = Z m s 1 := fun s hs => by simp only [w, dif_pos hs]`.

Set `χ : Fin β.d → G ℚ Ω → ZMod (l ^ m)` to `fun i s => PadicInt.toZModPow m (β.e.repr (w s) i)`. Establish `hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ Hm l A m, s u = u) ∧ ∀ s ∈ Hm l A m, KumVal (l` using `l) m (ζ m) u s (χ i s) := by`. Introduce `i`. Use `GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup l Ω m (Hm l A m) (GlobalTheory.T.isClosed_inertia_cyclotomic_kernel l Ω A m) (ζ m) (hζ m).1 (fun s hs => fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one) (χ i) (fun s hs t ht => ?_) U hU (fun s hs hsU => ?_)` and prove the remaining obligations. Establish `e : w (s * t) = w s + w t`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : cycMod ℚ Ω l m s = 1` using `hs.2`. Rewrite using `[Subalgebra.coe_add, hw _ (mul_mem hs.1 ht.1), hw _ hs.1, hw _ ht.1, hZ.coc m s hs.1 t ht.1, h1, inv_one, mul_one]`. Simplify using `only [χ, e, map_add, Finsupp.add_apply]`. Take `⟨y, hy⟩` from `((pBasEx l c).2 β).2.2.1 m (w s) (by rw [hw s hs.1]; exact hUZ s hsU hs.1 1)`.

Establish `e : w s = ((l : ℤ_[l]) ^ m) • y` using `by rw [hy, Algebra.smul_def, map_pow, map_natCast]`. Simplify using `only [χ, e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]`. Rewrite using `[← Nat.cast_pow, ZMod.natCast_self, zero_mul]`. Use `choose u hu0 hufix huk using hex`. Establish `hconj` using `fun s hs => pConj l hl Ω A hA c Z hZ m s hs τ⁻¹ (inv_mem hτ)`.

Simplify using `only [inv_inv] at hconj`. Establish `hun` using `fun i => div_mem_of A τ (fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hτ) x).2 hx) (u i) (hu0 i)`. Establish `hP : ∀ i, ∃ P : Polynomial (R0 A), pv P (ζ m) = u i / τ (u i)`. Introduce `i`. Use `pPolyEx l hl Ω A hA ζ hζ m _ (hun i).1 fun s hs => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg τ (hufix i _ (hconj s hs).1)`. Rewrite `h1` using `[← AlgEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply]`. Rewrite using `[map_div₀, h1, hufix i s hs]`. Use `choose P hP using hP`. Use `⟨P, (hζ m).1, le_rfl, fun i => ?_, ((pBasEx l c).2 β).1, fun s hs hc _ => ?_⟩` and prove the remaining obligations.

Simplify using `only [hP, inv_div]`. Conclude with `⟨(hun i).1, div_ne_zero (hu0 i) ((map_ne_zero _).2 (hu0 i)), (hun i).2⟩`. Establish `hH : s ∈ Hm l A m` using `⟨hs, hc⟩`. Take `⟨hs', hZ'⟩` from `hconj s hH`. Use `⟨fun i => PadicInt.toZModPow m (β.e.repr (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ)) i), fun i => ?_, ?_⟩` and prove the remaining obligations.

Establish `k1` using `(pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hs').2.2 (τ (u i)) (χ i (τ⁻¹ * s * τ)) τ (by`. Rewrite using `[← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Conclude with `huk i _ hs')`. Rewrite `k1` using `[show τ * (τ⁻¹ * s * τ) * τ⁻¹ = s by group, hτb]`. Establish `a1` using `(pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hH).1`.

Establish `k2` using `(a1 _ _ _ _ (huk i s hH) (a1 _ _ _ _ k1 k1).2.1).1`. Simplify using `only [hP, div_eq_mul_inv]`. Use `k2 using 1` and compare the differences between its conclusion and the goal. Simplify using `[χ, un, sub_eq_add_neg]`. Use `cg_coord β m (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Subalgebra.coe_sub, Subalgebra.coe_smul, hw s hs, hw _ hs'.1, hZ', map_inv, inv_inv, hτb, Algebra.smul_def, map_natCast]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Kd.C7.pKumEx :
    UpperTheory.Kd.C7.SKumEx := by
  classical
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ hC b hb
  refine ⟨0, 0, fun m _ => ?_⟩
  rw [Nat.sub_zero]
  haveI : NeZero (l : Ω) := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨τ, hτ, hτb⟩ := exists_tau l hl Ω A hA b hb m
  obtain ⟨U, hU, hUZ⟩ := hC m m
  let w : G ℚ Ω → c.O := fun s => if h : s ∈ Ine (F := ℚ) A then ⟨Z m s 1, hZ.int m s h 1⟩ else 0
  have hw : ∀ s ∈ Ine (F := ℚ) A, (w s : PadicAlgCl l) = Z m s 1 := fun s hs => by simp only [w, dif_pos hs]
  let χ : Fin β.d → G ℚ Ω → ZMod (l ^ m) := fun i s => PadicInt.toZModPow m (β.e.repr (w s) i)
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ Hm l A m, s u = u) ∧
      ∀ s ∈ Hm l A m, KumVal (l := l) m (ζ m) u s (χ i s) := by
    intro i
    refine GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup l Ω m (Hm l A m) (GlobalTheory.T.isClosed_inertia_cyclotomic_kernel l Ω A m) (ζ m) (hζ m).1
      (fun s hs => fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one) (χ i) (fun s hs t ht => ?_) U hU (fun s hs hsU => ?_)
    · have e : w (s * t) = w s + w t := by
        apply Subtype.ext
        have h1 : cycMod ℚ Ω l m s = 1 := hs.2
        rw [Subalgebra.coe_add, hw _ (mul_mem hs.1 ht.1), hw _ hs.1, hw _ ht.1, hZ.coc m s hs.1 t ht.1, h1, inv_one, mul_one]
      simp only [χ, e, map_add, Finsupp.add_apply]
    · obtain ⟨y, hy⟩ := ((pBasEx l c).2 β).2.2.1 m (w s) (by rw [hw s hs.1]; exact hUZ s hsU hs.1 1)
      have e : w s = ((l : ℤ_[l]) ^ m) • y := by rw [hy, Algebra.smul_def, map_pow, map_natCast]
      simp only [χ, e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  choose u hu0 hufix huk using hex
  have hconj := fun s hs => pConj l hl Ω A hA c Z hZ m s hs τ⁻¹ (inv_mem hτ)
  simp only [inv_inv] at hconj
  have hun := fun i => div_mem_of A τ (fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hτ) x).2 hx) (u i) (hu0 i)
  have hP : ∀ i, ∃ P : Polynomial (R0 A), pv P (ζ m) = u i / τ (u i) := by
    intro i
    refine pPolyEx l hl Ω A hA ζ hζ m _ (hun i).1 fun s hs => ?_
    have h1 := congrArg τ (hufix i _ (hconj s hs).1)
    rw [← AlgEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply] at h1
    rw [map_div₀, h1, hufix i s hs]
  choose P hP using hP
  refine ⟨P, (hζ m).1, le_rfl, fun i => ?_, ((pBasEx l c).2 β).1, fun s hs hc _ => ?_⟩
  · simp only [hP, inv_div]
    exact ⟨(hun i).1, div_ne_zero (hu0 i) ((map_ne_zero _).2 (hu0 i)), (hun i).2⟩
  · have hH : s ∈ Hm l A m := ⟨hs, hc⟩
    obtain ⟨hs', hZ'⟩ := hconj s hH
    refine ⟨fun i => PadicInt.toZModPow m (β.e.repr (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ)) i), fun i => ?_, ?_⟩
    · have k1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hs').2.2 (τ (u i)) (χ i (τ⁻¹ * s * τ)) τ (by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]; exact huk i _ hs')
      rw [show τ * (τ⁻¹ * s * τ) * τ⁻¹ = s by group, hτb] at k1
      have a1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hH).1
      have k2 := (a1 _ _ _ _ (huk i s hH) (a1 _ _ _ _ k1 k1).2.1).1
      simp only [hP, div_eq_mul_inv]
      convert k2 using 1
      simp [χ, un, sub_eq_add_neg]
    · have := cg_coord β m (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ))
      convert this using 1
      rw [Subalgebra.coe_sub, Subalgebra.coe_smul, hw s hs, hw _ hs'.1, hZ', map_inv, inv_inv, hτb, Algebra.smul_def,
        map_natCast]
      rfl
