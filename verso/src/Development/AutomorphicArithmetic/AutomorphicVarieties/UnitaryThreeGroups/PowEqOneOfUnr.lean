import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private def ball {F : Type} [NormedField F] [IsUltrametricDist F] (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < ε}
  one_mem' := by simpa using h0
  mul_mem' {a b} ha hb := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    have hb' : ‖(b : F) - 1‖ < ε := hb
    show ‖((a * b : Fˣ) : F) - 1‖ < ε
    have e : ((a * b : Fˣ) : F) - 1 = ((a : F) - 1) * ((b : F) - 1) + (((a : F) - 1) + ((b : F) - 1)) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')))
    rw [norm_mul]
    nlinarith [norm_nonneg ((a : F) - 1), norm_nonneg ((b : F) - 1)]
  inv_mem' {a} ha := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    show ‖((a⁻¹ : Fˣ) : F) - 1‖ < ε
    have hn : ‖(a : F)‖ = 1 := by
      have h2 : ‖(a : F) - 1‖ < ‖(1 : F)‖ := by rw [norm_one]; exact ha'.trans_le h1
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne
      rw [sub_add_cancel, max_eq_right h2.le, norm_one] at this
      exact this
    have e : (a : F) * (((a⁻¹ : Fˣ) : F) - 1) = -((a : F) - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, hn, one_mul, norm_neg] at this
    rwa [this]

/- English proof (translation)
Establish `hn : ‖x‖ ≤ 1`. Use `IsUltrametricDist.norm_add_le_max (x - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le hx.le le_rfl)`. Establish `h1 : ∀ n : ℕ, ‖x ^ n - 1‖ < 1`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1)` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use polynomial arithmetic with `[norm_nonneg x, norm_nonneg (x ^ n - 1)]`. Establish `h2 : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, x ^ i - n‖ < 1`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : ∑ i ∈ Finset.range (n + 1), x ^ i - ((n + 1 : ℕ) : F) = (∑ i ∈ Finset.range n, x ^ i - n) + (x ^ n - 1)`.

Rewrite using `[Finset.sum_range_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 n))`.

Establish `h3` using `geom_sum_mul x h`. Rewrite `h3` using `[e, sub_self, mul_eq_zero]`. Break down `h3 with h3 | h3` into its components or cases. Use `h2 h` as an intermediate fact. Rewrite `this` using `[h3, zero_sub, norm_neg, hh]`.

Conclude with `absurd this (lt_irrefl _)`. Conclude with `sub_eq_zero.1 h3`.
-/
private theorem eq_one_of_pow {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : ‖x - 1‖ < 1) (h : ℕ)
    (hh : ‖(h : F)‖ = 1) (e : x ^ h = 1) : x = 1 := by
  have hn : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hx.le le_rfl)
  have h1 : ∀ n : ℕ, ‖x ^ n - 1‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)
      rw [norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg (x ^ n - 1)]
  have h2 : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, x ^ i - n‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ Finset.range (n + 1), x ^ i - ((n + 1 : ℕ) : F) =
          (∑ i ∈ Finset.range n, x ^ i - n) + (x ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 n))
  have h3 := geom_sum_mul x h
  rw [e, sub_self, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · have := h2 h
    rw [h3, zero_sub, norm_neg, hh] at this
    exact absurd this (lt_irrefl _)
  · exact sub_eq_zero.1 h3

/- English proof (translation)
Establish `key : ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1), ‖(κ g : F) ^ classNumber K - 1‖ < ε`. Introduce `ε h0 h1`. Set `χ` to `(QuotientGroup.mk' (ball (F := F) ε h0 h1)).comp κ`. Establish `hχ : ∀ x, x ∈ χ.ker ↔ ‖(κ x : F) - 1‖ < ε` using `fun x => QuotientGroup.eq_one_iff (κ x)`. Establish `hle` using `Kum.artKer K Ω _ χ ?_ ?_ ?_`.

Establish `hg : g ^ classNumber K ∈ (Kum.artCl K Ω).ker`. Rewrite using `[MonoidHom.mem_ker, map_pow, classNumber]`. Conclude with `pow_card_eq_one`. Use `(hχ _).1 (hle hg)` as an intermediate fact. Rewrite `this` using `[map_pow, Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis.

Establish `: (χ.ker : Set (G K Ω)) = {x | ‖(κ x : F) - 1‖ < ε}` using `Set.ext hχ`. Rewrite using `[this]`. Conclude with `isOpen_lt (hc.sub continuous_const).norm continuous_const`. Introduce `A x hx`. Rewrite using `[hχ, hI A x hx]`.

Simplify using `using h0`. Introduce and unpack `c ⟨j, hj⟩`. It suffices to derive a contradiction. Establish `hE : ComplexEmbedding.IsReal (j.comp (algebraMap K Ω))`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `y`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `(hj (algebraMap K Ω y)).symm.trans (congrArg j (c.commutes y))`. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal _ hE`. Rewrite using `[← sub_eq_zero, ← norm_le_zero_iff]`.

Assume the negation of the conclusion as `hne`. Establish `hpos` using `not_le.1 hne`. Conclude with `absurd (key _ (lt_min hpos one_pos) (min_le_right _ _)) (not_lt.2 (min_le_left _ _))`.
-/
private theorem pow_eq_one_of_unr {K Ω F : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsTotallyComplex K] [NormedField F] [IsUltrametricDist F] (κ : G K Ω →* Fˣ) (hc : Continuous fun g => (κ g : F))
    (hI : ∀ (A : ValuationSubring Ω), ∀ g ∈ Ine (F := K) A, κ g = 1) (g : G K Ω) : (κ g : F) ^ classNumber K = 1 := by
  have key : ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1), ‖(κ g : F) ^ classNumber K - 1‖ < ε := by
    intro ε h0 h1
    let χ := (QuotientGroup.mk' (ball (F := F) ε h0 h1)).comp κ
    have hχ : ∀ x, x ∈ χ.ker ↔ ‖(κ x : F) - 1‖ < ε := fun x => QuotientGroup.eq_one_iff (κ x)
    have hle := Kum.artKer K Ω _ χ ?_ ?_ ?_
    · have hg : g ^ classNumber K ∈ (Kum.artCl K Ω).ker := by
        rw [MonoidHom.mem_ker, map_pow, classNumber]
        exact pow_card_eq_one
      have := (hχ _).1 (hle hg)
      rwa [map_pow, Units.val_pow_eq_pow_val] at this
    · have : (χ.ker : Set (G K Ω)) = {x | ‖(κ x : F) - 1‖ < ε} := Set.ext hχ
      rw [this]
      exact isOpen_lt (hc.sub continuous_const).norm continuous_const
    · intro A x hx
      rw [hχ, hI A x hx]
      simpa using h0
    · rintro c ⟨j, hj⟩
      exfalso
      have hE : ComplexEmbedding.IsReal (j.comp (algebraMap K Ω)) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact (hj (algebraMap K Ω y)).symm.trans (congrArg j (c.commutes y))
      exact IsTotallyComplex.complexEmbedding_not_isReal _ hE
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  by_contra hne
  have hpos := not_le.1 hne
  exact absurd (key _ (lt_min hpos one_pos) (min_le_right _ _)) (not_lt.2 (min_le_left _ _))

/- English proof (translation)
Introduce `Ω _ _ _ K _ _ _ l _ c N _ e ψ D κ hc h1 hI`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Use `haveI := D.gd.imag`. Set `ι : G K Ω →* D.η.ker` to `(galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s`. Establish `hι : Continuous ι` using `(galEmbTop ℚ K Ω).1.continuous.subtype_mk _`.

Establish `hp` using `pow_eq_one_of_unr (κ.comp ι) (hc.comp hι) fun A g hg => hI A (ι g) (by`. Rewrite `hg` using `[← ((galEmbFam ℚ K Ω l).1 A).2]`. Conclude with `hg)`. Establish `hh : ‖((classNumber K : ℕ) : PadicAlgCl l)‖ = 1`. Establish `hnd : ¬ l ∣ classNumber K` using `fun h => D.gd.l_cop (h.mul_left _)`.

Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Establish `hg : g.1 ∈ (galEmb ℚ K Ω).range`. Rewrite using `[range_galEmb, ← D.η_ker]`.

Conclude with `g.2`. Take `⟨s, hs⟩` from `hg`. Establish `e : ι s = g` using `Subtype.ext hs`. Use `hp s` as an intermediate fact. Rewrite `this` using `[MonoidHom.comp_apply, e]`.

Conclude with `Units.ext (eq_one_of_pow _ (h1 g) _ hh this)`.
-/
theorem UpperTheory.V.U3.char_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (κ : D.η.ker →* (PadicAlgCl l)ˣ),
      Continuous (fun g => (κ g : PadicAlgCl l)) → (∀ g, ‖(κ g : PadicAlgCl l) - 1‖ < 1) →
      (∀ (A : ValuationSubring Ω) (g : D.η.ker), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → κ g = 1) → κ = 1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D κ hc h1 hI
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI := D.gd.imag
  let ι : G K Ω →* D.η.ker := (galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hι : Continuous ι := (galEmbTop ℚ K Ω).1.continuous.subtype_mk _
  have hp := pow_eq_one_of_unr (κ.comp ι) (hc.comp hι) fun A g hg =>
    hI A (ι g) (by
      rw [← ((galEmbFam ℚ K Ω l).1 A).2] at hg
      exact hg)
  have hh : ‖((classNumber K : ℕ) : PadicAlgCl l)‖ = 1 := by
    have hnd : ¬ l ∣ classNumber K := fun h => D.gd.l_cop (h.mul_left _)
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd
  refine MonoidHom.ext fun g => ?_
  have hg : g.1 ∈ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact g.2
  obtain ⟨s, hs⟩ := hg
  have e : ι s = g := Subtype.ext hs
  have := hp s
  rw [MonoidHom.comp_apply, e] at this
  exact Units.ext (eq_one_of_pow _ (h1 g) _ hh this)
