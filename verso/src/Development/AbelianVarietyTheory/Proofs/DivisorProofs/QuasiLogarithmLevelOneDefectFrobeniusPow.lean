import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPowDefect

/- English proof (translation)
Establish `key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔ x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A)`. Introduce `n x`. Rewrite using `[GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]`. Simplify using `[Algebra.smul_def]`. Conclude with `{ haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n => SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n))) prec' := fun f hf => by`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn => SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))`. Conclude with `⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }`.
-/
theorem adicComplete_ring {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

/- English proof (translation)
Use `set I : Ideal B := Ideal.span {(p : B)}`. Use `haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)`. Use `haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out`. Establish `hw : map (Ideal.Quotient.mk I) (map t w) = map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w)`. Use extensionality with `n`.

Simplify using `only [coeff_map, frobenius_def]`. Rewrite using `[← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `ht _`. Establish `key : map (Ideal.Quotient.mk I) (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0`. Rewrite using `[map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]`.

Use `congrArg (coeff α) key` as an intermediate fact. Rewrite `this` using `[coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis.
-/
theorem pow_sub_expand_mem (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (t : B →+* B)
    (ht : ∀ b, (p : B) ∣ t b - b ^ p) (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B)
    (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

/- English proof (translation)
Establish `h : ∀ α, ∃ b, coeff α w = (p : B) * b` using `fun α => Ideal.mem_span_singleton'.1 (hw α) |>.imp fun b hb => by rw [← hb, mul_comm]`. Use `choose e he using h`. Set `w' : MvPowerSeries τ B` to `e`. Use `⟨w', ?_⟩` and prove the remaining obligations. Use extensionality with `α`.

Rewrite using `[← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]`. Conclude with `he α`.
-/
theorem exists_eq_p_mul {B : Type} [CommRing B] (p : ℕ) {τ : Type} (w : MvPowerSeries τ B)
    (hw : ∀ α, coeff α w ∈ Ideal.span {(p : B)}) :
    ∃ w' : MvPowerSeries τ B, w = (p : MvPowerSeries τ B) * w' := by
  have h : ∀ α, ∃ b, coeff α w = (p : B) * b := fun α => Ideal.mem_span_singleton'.1 (hw α) |>.imp
    fun b hb => by rw [← hb, mul_comm]
  choose e he using h
  let w' : MvPowerSeries τ B := e
  refine ⟨w', ?_⟩
  ext α
  rw [← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  exact he α

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A 1) := GlobalTheory.isAdicComplete_of_finite_projective _ _`. Use `haveI : IsAdicComplete (Ideal.span {(p : G.A 1)}) (G.A 1) := adicComplete_ring (O := O) p`. Establish `hT` using `(GlobalTheory.CEval.continuous_eval p O (G.A 1) (Fin d) (c.x 1) (c.nil 1)).2 (c.ev 1) (c.isEval 1)`. Set `E' : MvPowerSeries (Fin d) O →ₐ[O] G.A 1` to `{ (algebraMap O (G.A 1)).comp (constantCoeff : MvPowerSeries (Fin d) O →+* O) with commutes' := fun r => by show algebraMap O (G.A 1) (constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r)) = _`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }`.

Establish `hE'apply : ∀ f, E' f = algebraMap O (G.A 1) (constantCoeff f)` using `fun _ => rfl`. Establish `hu : ∀ j, constantCoeff (nmul c.μ p j) = 0` using `GlobalTheory.MapNMul.cc_nmul c.μ (fun j => c.isLaw.const j) p`. Establish `hpt : ∀ j, c.ev 1 (nmul c.μ p j) = 0` using `fun j => by`. Establish `h1` using `G.mulBy_pow_self 1 (c.x 1 j)`. Rewrite `h1` using `[pow_one]`.

Rewrite using `[GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c 1 p j, h1, c.aug 1 j, map_zero]`. Establish `hE' : IsEval p (fun j => c.ev 1 (nmul c.μ p j)) E'`. Prove the components needed by the constructor for the conclusion. Introduce `j show _ = c.ev 1 (nmul c.μ p j)`. Rewrite using `[hE'apply, constantCoeff_X, map_zero, hpt]`.

Introduce `m`. Use `⟨1, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h0 : constantCoeff f = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `hf 0 (by simp)`.

Rewrite using `[hE'apply, h0, map_zero]`. Conclude with `dvd_zero _`. Rewrite using `[hT.1 (Fin d) (nmul c.μ p) E' hu hE' s, hE'apply, hs, map_zero]`.
-/
theorem ev_one_subst_nmul (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O)
    (d : ℕ) (c : QLog.Chart G d) (s : MvPowerSeries (Fin d) O) (hs : constantCoeff s = 0) :
    c.ev 1 (subst (nmul c.μ p) s) = 0 := by
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A 1) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A 1)}) (G.A 1) := adicComplete_ring (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A 1) (Fin d) (c.x 1) (c.nil 1)).2
    (c.ev 1) (c.isEval 1)
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A 1 :=
    { (algebraMap O (G.A 1)).comp (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show algebraMap O (G.A 1) (constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r)) = _
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }
  have hE'apply : ∀ f, E' f = algebraMap O (G.A 1) (constantCoeff f) := fun _ => rfl
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    GlobalTheory.MapNMul.cc_nmul c.μ (fun j => c.isLaw.const j) p
  have hpt : ∀ j, c.ev 1 (nmul c.μ p j) = 0 := fun j => by
    have h1 := G.mulBy_pow_self 1 (c.x 1 j)
    rw [pow_one] at h1
    rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c 1 p j, h1, c.aug 1 j, map_zero]
  have hE' : IsEval p (fun j => c.ev 1 (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show _ = c.ev 1 (nmul c.μ p j)
      rw [hE'apply, constantCoeff_X, map_zero, hpt]
    · intro m
      refine ⟨1, fun f hf => ?_⟩
      have h0 : constantCoeff f = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply]
        exact hf 0 (by simp)
      rw [hE'apply, h0, map_zero]
      exact dvd_zero _
  rw [hT.1 (Fin d) (nmul c.μ p) E' hu hE' s, hE'apply, hs, map_zero]

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Simplify using `only [frob, expand, substAlgHom_apply]`.
-/
theorem frob_eq_expand' (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

/- English proof (translation)
Establish `hU : HasSubst (up Q (nmul μ p))` using `hasSubst_of_constantCoeff_zero fun i => by`. Simplify using `[up, constantCoeff_map, h0]`. Establish `hV : HasSubst (up Q fun i => map t (nmul μ p i))` using `hasSubst_of_constantCoeff_zero fun i => by`. Simplify using `[up, constantCoeff_map, h0]`. Establish `hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)` using `HasSubst.X_pow hp`.

Establish `hexp : ∀ (g : MvPowerSeries (Fin d) Q), expand p hp g = subst (fun i => X i ^ p) g` using `fun g => by simp only [expand, substAlgHom_apply]`. Establish `e1 : subst (up Q (nmul μ p)) (expand p hp (map s f)) =`. Substitute `(up Q fun i => nmul μ p i ^ p) (map s f) := by` using the available equality. Rewrite using `[hexp, subst_comp_subst_apply hXp hU]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[subst_pow hU, subst_X hU]`. Simplify using `[up, map_pow]`. Establish `hmapU : (fun i => map s (up Q (nmul μ p) i)) = up Q (fun i => map t (nmul μ p i))`. Use function extensionality and compare the values at `i`.

Use extensionality with `n`. Simplify using `[up, coeff_map, hs]`. Establish `m1 : map s (subst (up Q (nmul μ p)) f) = subst (up Q fun i => map t (nmul μ p i)) (map s f)`. Rewrite using `[map_subst hU, hmapU]`. Establish `x1 : expand p hp (subst (up Q fun i => map t (nmul μ p i)) (map s f)) =`.

Substitute `(up Q fun i => expand p hp (map t (nmul μ p i))) (map s f) := by` using the available equality. Rewrite using `[expand_subst p hp hV]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[up, map_expand]`.

Establish `hsm : map s ((p : Q) • f) = (p : Q) • map s f`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]`. Rewrite using `[frob_eq_expand' p hp, defect, defect, e1, map_sub, hsm, m1, map_sub, map_smul, x1]`. Normalize the expressions using the abelian group laws.
-/
theorem defect_frob (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (nmul μ p i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    defect μ p (frob p s f) = expand p hp (map s (defect μ p f)) +
      (subst (up Q fun i => expand p hp (map t (nmul μ p i))) (map s f) -
        subst (up Q fun i => nmul μ p i ^ p) (map s f)) := by
  have hU : HasSubst (up Q (nmul μ p)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hV : HasSubst (up Q fun i => map t (nmul μ p i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hexp : ∀ (g : MvPowerSeries (Fin d) Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have e1 : subst (up Q (nmul μ p)) (expand p hp (map s f)) =
      subst (up Q fun i => nmul μ p i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have hmapU : (fun i => map s (up Q (nmul μ p) i)) = up Q (fun i => map t (nmul μ p i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have m1 : map s (subst (up Q (nmul μ p)) f) = subst (up Q fun i => map t (nmul μ p i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have x1 : expand p hp (subst (up Q fun i => map t (nmul μ p i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (nmul μ p i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have hsm : map s ((p : Q) • f) = (p : Q) • map s f := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [frob_eq_expand' p hp, defect, defect, e1, map_sub, hsm, m1, map_sub, map_smul, x1]
  abel

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Establish `hU : HasSubst (up Q (nmul μ n))` using `hasSubst_of_constantCoeff_zero fun i => by`. Simplify using `[up, constantCoeff_map, h0]`. Unfold `defect`. Rewrite using `[← coe_substAlgHom hU, map_sub, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem defect_sub {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (n : ℕ)
    (h0 : ∀ i, constantCoeff (nmul μ n i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    defect μ n (f - g) = defect μ n f - defect μ n g := by
  have hU : HasSubst (up Q (nmul μ n)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  unfold defect
  rw [← coe_substAlgHom hU, map_sub, smul_sub]
  abel

/- English proof (translation)
Establish `hU : HasSubst (nmul μ n)` using `hasSubst_of_constantCoeff_zero h0`. Unfold `defect`. Rewrite using `[map_sub, map_subst hU]`. Use `congr 1`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]`.
-/
theorem defect_map {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (n : ℕ)
    (h0 : ∀ i, constantCoeff (nmul μ n i) = 0) (h : MvPowerSeries (Fin d) B) :
    defect μ n (map (algebraMap B Q) h) =
      map (algebraMap B Q) ((n : B) • h - subst (nmul μ n) h) := by
  have hU : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero h0
  unfold defect
  rw [map_sub, map_subst hU]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.QLog

open GlobalTheory.FrobPowDefect in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ hθμ f g a b hf hg hfg ha hb`. Establish `hpp : p.Prime` using `Fact.out`. Establish `hp : p ≠ 0` using `hpp.ne_zero`. Establish `hnu : ¬IsUnit (p : O)` using `Fact.out`. Establish `huB : ¬IsUnit (p : F.B)` using `fun h => hnu (by simpa using h.map F.θ)`.

Establish `hinj : ∀ x y : MvPowerSeries (Fin d) F.B, map (algebraMap F.B F.Q) x = map (algebraMap F.B F.Q) y → x = y` using `fun x y h => by`. Use extensionality with `α`. Conclude with `F.frame.inj (by simpa [coeff_map] using congrArg (coeff α) h)`. Establish `hc : ∀ i, constantCoeff (nmul μ' p i) = 0` using `GlobalTheory.MapNMul.cc_nmul μ' hμ.const p`. Use `choose e _ he using hfg`.

Set `h₀ : MvPowerSeries (Fin d) F.B` to `e`. Establish `hh₀ : map (algebraMap F.B F.Q) h₀ = frob p F.s f - g`. Use extensionality with `α`. Rewrite using `[coeff_map]`. Conclude with `(he α).symm`.

Establish `hh₀c : constantCoeff h₀ = 0`. Apply `F.frame.inj` to reduce the goal to its premises. Establish `h1` using `congrArg constantCoeff hh₀`. Rewrite `h1` using `[constantCoeff_map]`. Rewrite using `[h1, map_zero, map_sub, hg.1, frob_eq_expand' p hp, constantCoeff_expand, constantCoeff_map, hf.1, map_zero, sub_zero]`.

Establish `hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y`. Introduce `x hx`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `e' : (p : F.B) ^ p = p * p ^ (p - 1)`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use `hpp.one_lt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨(p : F.B) ^ (p - 1) * r ^ p, Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, e']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hD : DIn (⊤ : Ideal F.B) (map F.s f)`. Establish `h` using `GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf`. Introduce `α i`. Take `⟨r, _, e'⟩` from `h α i`.

Conclude with `⟨F.σ r, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e', F.s_alg]⟩`. Establish `hK` using `GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d) ⊤ (map F.s f) (fun i => nmul μ' p i ^ p) (fun i => expand p hp (map F.σ (nmul μ' p i))) hD (fun i => by rw [map_pow, hc i, zero_pow hp]) (fun i => by rw [constantCoeff_expand, constantCoeff_map, hc i …`. Rewrite `hK` using `[Ideal.mul_top]`. Use `choose k hkJ hk using hK`. Set `kB : MvPowerSeries (Fin d) F.B` to `k`.

Establish `hkB : map (algebraMap F.B F.Q) kB =`. Substitute `(up F.Q fun i => nmul μ' p i ^ p) (map F.s f) -` using the available equality. Substitute `(up F.Q fun i => expand p hp (map F.σ (nmul μ' p i))) (map F.s f) := by` using the available equality. Use extensionality with `α`. Rewrite using `[coeff_map]`.

Conclude with `(hk α).symm`. Establish `hg' : g = frob p F.s f - map (algebraMap F.B F.Q) h₀` using `by rw [hh₀]; abel`. Establish `hfa : expand p hp (map F.s (defect μ' p f)) = map (algebraMap F.B F.Q) (expand p hp (map F.σ a))`. Rewrite using `[← ha, map_expand, map_map, map_map, show F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ from RingHom.ext F.s_alg]`. Establish `heq : map (algebraMap F.B F.Q) b = map (algebraMap F.B F.Q) (expand p hp (map F.σ a) - kB - ((p : F.B) • h₀ - subst (nmul μ' p) h₀))`.

Rewrite using `[hb, hg', defect_sub μ' p hc, defect_frob p hp F.σ F.s F.s_alg μ' hc f, defect_map μ' p hc, hfa]`. Simplify using `only [map_sub, hkB]`. Normalize the expressions using the abelian group laws. Establish `hbeq` using `hinj _ _ heq`. Use `set T := subst (nmul μ' p) h₀ with hT`.

Establish `hW : ∀ α, coeff α (b - a ^ p - T) ∈ Ideal.span {(p : F.B)}`. Introduce `α`. Establish `e' : b - a ^ p - T = -(a ^ p - expand p hp (map F.σ a)) - kB - (p : F.B) • h₀`. Rewrite using `[hbeq]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e']`. Simplify using `only [map_sub, map_neg, coeff_smul, smul_eq_mul]`. Use `sub_mem (sub_mem (neg_mem (pow_sub_expand_mem p F.σ F.σ_pow huB a α)) (hkJ α)) ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Take `⟨w', hw'⟩` from `exists_eq_p_mul p _ hW`.

Establish `hT0 : c.ev 1 (map F.θ T) = 0`. Establish `hs : HasSubst (nmul μ' p)` using `hasSubst_of_constantCoeff_zero hc`. Establish `hm : (fun i => map F.θ (nmul μ' p i)) = nmul c.μ p`. Use function extensionality and compare the values at `i`. Rewrite using `[GlobalTheory.MapNMul.map_nmul F.B O F.θ d μ' hμ.const p i]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `hθμ j`. Rewrite using `[hT, map_subst hs, hm]`. Conclude with `ev_one_subst_nmul p C v O hv G d c _ (by rw [constantCoeff_map, hh₀c, map_zero])`.

Establish `key : b = a ^ p + T + (p : MvPowerSeries (Fin d) F.B) * w'`. Take the linear combination `hw'`. Rewrite using `[key]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Rewrite using `[hT0]`.

Establish `e' : c.ev 1 (map F.θ a) ^ p + 0 + (p : G.A 1) * c.ev 1 (map F.θ w') - c.ev 1 (map F.θ a) ^ p = algebraMap O (G.A 1) (p : O) * c.ev 1 (map F.θ w')`. Rewrite using `[map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨p, hnu, rfl⟩)`.
-/
theorem defect_frob_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (a b : MvPowerSeries (Fin d) F.B), QL μ' ⊤ f → QL μ' ⊤ g → In (⊤ : Ideal F.B) (frob p F.s f - g) → map (algebraMap F.B F.Q) a = defect μ' p f → map (algebraMap F.B F.Q) b = defect μ' p g → c.ev 1 (map F.θ b) - c.ev 1 (map F.θ a) ^ p ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ hθμ f g a b hf hg hfg ha hb
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hnu : ¬IsUnit (p : O) := Fact.out
  have huB : ¬IsUnit (p : F.B) := fun h => hnu (by simpa using h.map F.θ)
  have hinj : ∀ x y : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) x = map (algebraMap F.B F.Q) y → x = y := fun x y h => by
    ext α
    exact F.frame.inj (by simpa [coeff_map] using congrArg (coeff α) h)
  have hc : ∀ i, constantCoeff (nmul μ' p i) = 0 := GlobalTheory.MapNMul.cc_nmul μ' hμ.const p

  choose e _ he using hfg
  let h₀ : MvPowerSeries (Fin d) F.B := e
  have hh₀ : map (algebraMap F.B F.Q) h₀ = frob p F.s f - g := by
    ext α; rw [coeff_map]; exact (he α).symm
  have hh₀c : constantCoeff h₀ = 0 := by
    apply F.frame.inj
    have h1 := congrArg constantCoeff hh₀
    rw [constantCoeff_map] at h1
    rw [h1, map_zero, map_sub, hg.1, frob_eq_expand' p hp, constantCoeff_expand, constantCoeff_map,
      hf.1, map_zero, sub_zero]

  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e' : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * r ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e']; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨r, _, e'⟩ := h α i
    exact ⟨F.σ r, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e', F.s_alg]⟩
  have hK := GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d) ⊤ (map F.s f)
    (fun i => nmul μ' p i ^ p) (fun i => expand p hp (map F.σ (nmul μ' p i))) hD
    (fun i => by rw [map_pow, hc i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hc i, map_zero])
    (fun i α => pow_sub_expand_mem p F.σ F.σ_pow huB (nmul μ' p i) α)
  rw [Ideal.mul_top] at hK
  choose k hkJ hk using hK
  let kB : MvPowerSeries (Fin d) F.B := k
  have hkB : map (algebraMap F.B F.Q) kB =
      subst (up F.Q fun i => nmul μ' p i ^ p) (map F.s f) -
        subst (up F.Q fun i => expand p hp (map F.σ (nmul μ' p i))) (map F.s f) := by
    ext α; rw [coeff_map]; exact (hk α).symm

  have hg' : g = frob p F.s f - map (algebraMap F.B F.Q) h₀ := by rw [hh₀]; abel
  have hfa : expand p hp (map F.s (defect μ' p f)) =
      map (algebraMap F.B F.Q) (expand p hp (map F.σ a)) := by
    rw [← ha, map_expand, map_map, map_map,
      show F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ from RingHom.ext F.s_alg]
  have heq : map (algebraMap F.B F.Q) b = map (algebraMap F.B F.Q)
      (expand p hp (map F.σ a) - kB - ((p : F.B) • h₀ - subst (nmul μ' p) h₀)) := by
    rw [hb, hg', defect_sub μ' p hc, defect_frob p hp F.σ F.s F.s_alg μ' hc f, defect_map μ' p hc,
      hfa]
    simp only [map_sub, hkB]
    abel
  have hbeq := hinj _ _ heq
  set T := subst (nmul μ' p) h₀ with hT
  have hW : ∀ α, coeff α (b - a ^ p - T) ∈ Ideal.span {(p : F.B)} := by
    intro α
    have e' : b - a ^ p - T = -(a ^ p - expand p hp (map F.σ a)) - kB - (p : F.B) • h₀ := by
      rw [hbeq]; abel
    rw [e']
    simp only [map_sub, map_neg, coeff_smul, smul_eq_mul]
    refine sub_mem (sub_mem (neg_mem (pow_sub_expand_mem p F.σ F.σ_pow huB a α)) (hkJ α)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨w', hw'⟩ := exists_eq_p_mul p _ hW
  have hT0 : c.ev 1 (map F.θ T) = 0 := by
    have hs : HasSubst (nmul μ' p) := hasSubst_of_constantCoeff_zero hc
    have hm : (fun i => map F.θ (nmul μ' p i)) = nmul c.μ p := by
      funext i
      rw [GlobalTheory.MapNMul.map_nmul F.B O F.θ d μ' hμ.const p i]
      congr 1
      funext j
      exact hθμ j
    rw [hT, map_subst hs, hm]
    exact ev_one_subst_nmul p C v O hv G d c _ (by rw [constantCoeff_map, hh₀c, map_zero])
  have key : b = a ^ p + T + (p : MvPowerSeries (Fin d) F.B) * w' := by
    linear_combination hw'
  rw [key]
  simp only [map_add, map_mul, map_pow, map_natCast]
  rw [hT0]
  have e' : c.ev 1 (map F.θ a) ^ p + 0 + (p : G.A 1) * c.ev 1 (map F.θ w') -
      c.ev 1 (map F.θ a) ^ p = algebraMap O (G.A 1) (p : O) * c.ev 1 (map F.θ w') := by
    rw [map_natCast]; ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨p, hnu, rfl⟩)

end GlobalTheory.QLog
