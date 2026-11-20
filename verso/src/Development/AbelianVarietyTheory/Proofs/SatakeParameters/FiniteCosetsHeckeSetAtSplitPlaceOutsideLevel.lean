import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDoubleCosetAdicCompletionInvMulIntegralStatement

open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.TSetFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime L s`.
-/
theorem exists_sep (s : SplitPlace L) : ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
    Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime L s

/- English proof (translation)
The claim follows from `GlobalTheory.T.cmField_adele_split_place_support_integral L s e he he' z hz h1 h2`.
-/
theorem mem_ALint_of_local (s : SplitPlace L) (e : 𝓞 L) (he : Valued.v (s.i (e : L)) = 1)
    (he' : Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1) (z : AL L)
    (hz : ∀ w, w ≠ s.v → compAt L w z = 0) (h1 : Valued.v (s.proj z) ≤ 1)
    (h2 : Valued.v (s.proj (conjAL L z)) ≤ 1) : z ∈ ALint L := GlobalTheory.T.cmField_adele_split_place_support_integral L s e he he' z hz h1 h2

/- English proof (translation)
The claim follows from `GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral F v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hc hg hg'`.
-/
theorem local_int {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (a a' b b' g g' : GL (Fin n) (v.adicCompletion F))
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hc : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hg' : (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 :=
  GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral F v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hc hg hg'

/- English proof (translation)
Introduce `w hw`. Establish `: ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))` using `rfl`. Rewrite using `[this, Matrix.map_mul, hx w hw, hy w hw, mul_one]`.
-/
theorem triv_mul {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GA L n} (hx : TrivOutside T x)
    (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

/- English proof (translation)
Introduce `w hw`. Establish `h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (fun M => M.map (compAt L w)) h1`.

Simplify using `only [Matrix.map_mul, hx w hw, mul_one] at h2`. Rewrite using `[h2, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem triv_inv {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GA L n} (hx : TrivOutside T x) :
    TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Take `⟨e, he, he'⟩` from `exists_sep s`. Introduce `i j`. Establish `hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i`. Establish `hm` using `x.2`. Simplify using `only [GA, UGroup, Subgroup.mem_mk] at hm`.

Establish `h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1` using `Units.inv_eq_of_mul_eq_one_right hm`. Simplify using `only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]`. Establish `hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L`. Apply `mem_ALint_of_local s e he he'` to reduce the goal to its premises. Introduce `w hw`.

Use `congrFun (congrFun (hx w (by simpa using hw)) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[map_sub, this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j` using `rfl`.

Rewrite using `[map_sub, e1]`. Use `(Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) = ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i` using `rfl`. Rewrite using `[map_sub, map_sub, hconj, e1]`.

Use `(Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Use `add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by` as an intermediate fact. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])`. Simplify using `using this`.
-/
theorem mem_Umax_of_loc {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by
  obtain ⟨e, he, he'⟩ := exists_sep s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

/- English proof (translation)
Take `⟨g, rfl⟩` from `ha`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2`. Rewrite using `[← map_inv]`. Conclude with `(((g⁻¹ : GL (Fin n) (v.adicCompletionIntegers F).toSubring) : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2`.
-/
theorem glint_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {a : GL (Fin n) (v.adicCompletion F)} (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring) :
    (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2
  · rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) (v.adicCompletionIntegers F).toSubring) : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2

/- English proof (translation)
Use `⟨fun y => if h : Valued.v y ≤ 1 then Ideal.Quotient.mk _ (adic_exists_approx v y h).choose else 0, ?_⟩` and prove the remaining obligations. Introduce `y y' hy hy' hc`. Simplify using `only [dif_pos hy, dif_pos hy'] at hc`. Establish `ha` using `(adic_exists_approx v y hy).choose_spec`. Establish `ha'` using `(adic_exists_approx v y' hy').choose_spec`.

Use `set a := (adic_exists_approx v y hy).choose`. Use `set a' := (adic_exists_approx v y' hy').choose`. Rewrite `hc` using `[Ideal.Quotient.eq]`. Establish `h3 : Valued.v (algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a')) < 1` using `by show Valued.v (algebraMap L⁺ (v.adicCompletion L⁺) (algebraMap (𝓞 L⁺) L⁺ (a - a'))) < 1`. Rewrite using `[adic_valued_algebraMap]`.

Conclude with `(v.valuation_lt_one_iff_mem (K := L⁺) _).2 hc`. Establish `e : y - y' = (y - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a) - (y' - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a') + algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a')`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha ha')) h3)`.
-/
theorem approx_class (v : HeightOneSpectrum (𝓞 L⁺)) :
    ∃ c : v.adicCompletion L⁺ → 𝓞 L⁺ ⧸ v.asIdeal, ∀ y y' : v.adicCompletion L⁺, Valued.v y ≤ 1 → Valued.v y' ≤ 1 →
      c y = c y' → Valued.v (y - y') < 1 := by
  classical
  refine ⟨fun y => if h : Valued.v y ≤ 1 then Ideal.Quotient.mk _ (adic_exists_approx v y h).choose else 0, ?_⟩
  intro y y' hy hy' hc
  simp only [dif_pos hy, dif_pos hy'] at hc
  have ha := (adic_exists_approx v y hy).choose_spec
  have ha' := (adic_exists_approx v y' hy').choose_spec
  set a := (adic_exists_approx v y hy).choose
  set a' := (adic_exists_approx v y' hy').choose
  rw [Ideal.Quotient.eq] at hc
  have h3 : Valued.v (algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a')) < 1 := by
    show Valued.v (algebraMap L⁺ (v.adicCompletion L⁺) (algebraMap (𝓞 L⁺) L⁺ (a - a'))) < 1
    rw [adic_valued_algebraMap]
    exact (v.valuation_lt_one_iff_mem (K := L⁺) _).2 hc
  have e : y - y' = (y - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a) -
      (y' - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a') + algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a') := by
    rw [map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha ha')) h3)

/- English proof (translation)
Introduce `L _ _ _ n J χ B hJ s ϖ k hB hϖ`. Take `⟨c, hc⟩` from `approx_class s.v`. Use `haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot`. Set `κ : Formalism.AUTREP.GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal)` to `fun x => if h : x ∈ Formalism.AUTREP.tSet L n s ϖ k then fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) else 0`. Establish `key : ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, ∀ x' ∈ Formalism.AUTREP.tSet L n s ϖ k, κ x = κ x' → (x : Formalism.AUTREP.GAf L n ⧸ J) = x'`.

Introduce `x hx x' hx' hκ`. Simplify using `only [κ, dif_pos hx, dif_pos hx'] at hκ`. Take `⟨ha, b, hb, hg⟩` from `hx.2.choose_spec`. Take `⟨ha', b', hb', hg'⟩` from `hx'.2.choose_spec`. Use `set a := hx.2.choose`.

Use `set a' := hx'.2.choose`. Establish `ia` using `glint_int ha`. Establish `ia'` using `glint_int ha'`. Establish `ib` using `glint_int hb`. Establish `ib'` using `glint_int hb'`.

Establish `hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j - (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1` using `fun i j => hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)`. Establish `hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j - (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1` using `fun i j => by`. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hcl i j`. Establish `hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`.

Establish `h1` using `local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'`. Establish `h2` using `local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg`. Rewrite using `[QuotientGroup.eq]`. Establish `htriv : TrivOutside {s.v} (x⁻¹ * x')` using `triv_mul (triv_inv hx.1) hx'.1`. Use `((hJ _ ?_).1).2 ?_` and prove the remaining obligations.

Introduce `w hw`. Use `htriv w ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hB (by simpa using hw)`. Use `mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv]`. Conclude with `h1 i j`. Rewrite using `[mul_inv_rev, inv_inv, map_mul, map_inv]`. Conclude with `h2 i j`. Set `g : Formalism.AUTREP.GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal)` to `fun q => if h : ∃ x ∈ Formalism.AUTREP.tSet L n s ϖ k, (x : Formalism.AUTREP.GAf L n ⧸ J) = q then κ h.choose else 0`.

Use `Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg`. Establish `h : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x` using `⟨x, hx, rfl⟩`. Establish `h' : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x'` using `⟨x', hx', rfl⟩`. Simplify using `only [g, dif_pos h, dif_pos h'] at hgg`.

Use `show (x : Formalism.AUTREP.GAf L n ⧸ J) = x'`. Rewrite using `[← h.choose_spec.2, ← h'.choose_spec.2]`. Conclude with `key _ h.choose_spec.1 _ h'.choose_spec.1 hgg`.
-/
theorem finite_image_tSet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
    s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ →
    ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  intro L _ _ _ n J χ B hJ s ϖ k hB hϖ
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : Formalism.AUTREP.GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ Formalism.AUTREP.tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, ∀ x' ∈ Formalism.AUTREP.tSet L n s ϖ k, κ x = κ x' →
      (x : Formalism.AUTREP.GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine ((hJ _ ?_).1).2 ?_
    · intro w hw
      refine htriv w ?_
      rintro rfl
      exact hB (by simpa using hw)
    · refine mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)
      · rw [map_mul, map_inv]; exact h1 i j
      · rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j
  let g : Formalism.AUTREP.GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ Formalism.AUTREP.tSet L n s ϖ k, (x : Formalism.AUTREP.GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : Formalism.AUTREP.GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFin
