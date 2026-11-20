import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hnP`. Establish `h1 : n ≠ 1`.

Introduce and unpack `rfl`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hnP))`. Establish `hl` using `Nat.minFac_prime h1`. Take `⟨m, hm⟩` from `Nat.minFac_dvd n`. Establish `hm' : (n : R) = (n.minFac : R) * m` using `by rw [← Nat.cast_mul, ← hm]`.

Rewrite `hnP` using `[hm']`. Break down `hP.mem_or_mem hnP with h | h` into its components or cases. Conclude with `⟨_, hl, h⟩`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hn (by simpa using hm)`. Establish `h2` using `hl.two_le`.

Establish `hlt : m < n`. Generalize the expression as in `n.minFac = k at hm h2`. Substitute `hm` using the available equality. Establish `: 0 < m` using `Nat.pos_of_ne_zero hm0`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `ih m hlt hm0 h`.
-/
theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ l : ℕ, l.Prime ∧ (l : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hnP))
    have hl := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hm' : (n : R) = (n.minFac : R) * m := by rw [← Nat.cast_mul, ← hm]
    rw [hm'] at hnP
    rcases hP.mem_or_mem hnP with h | h
    · exact ⟨_, hl, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; exact hn (by simpa using hm)
      have h2 := hl.two_le
      have hlt : m < n := by
        generalize n.minFac = k at hm h2
        subst hm
        have : 0 < m := Nat.pos_of_ne_zero hm0
        nlinarith
      exact ih m hlt hm0 h

/- English proof (translation)
Distinguish the cases in `h : ∃ l : ℕ, l.Prime ∧ Ov l x`. Conclude with `Or.inl h`. Use `Or.inr (Isom.mem_range_j V ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hn : Ideal.absNorm (V.p x).asIdeal ≠ 0` using `fun h0 => hne (Ideal.absNorm_eq_zero_iff.1 h0)`.

Use `(V.p x).isPrime` as an intermediate fact. Take `⟨l, hl, hlP⟩` from `exists_prime_natCast_mem (V.p x).asIdeal _ hn (Ideal.absNorm_mem _)`. Conclude with `h ⟨l, hl, fun hu => (GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff V x l).1 hu hlP⟩`.
-/
theorem exists_ov_or_mem_range {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (x : V.X) :
    (∃ l : ℕ, l.Prime ∧ Ov l x) ∨ x ∈ Set.range V.j := by
  by_cases h : ∃ l : ℕ, l.Prime ∧ Ov l x
  · exact Or.inl h
  · refine Or.inr (Isom.mem_range_j V ?_)
    by_contra hne
    have hn : Ideal.absNorm (V.p x).asIdeal ≠ 0 := fun h0 => hne (Ideal.absNorm_eq_zero_iff.1 h0)
    have := (V.p x).isPrime
    obtain ⟨l, hl, hlP⟩ := exists_prime_natCast_mem (V.p x).asIdeal _ hn (Ideal.absNorm_mem _)
    exact h ⟨l, hl, fun hu => (GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff V x l).1 hu hlP⟩

/- English proof (translation)
Establish `hmul` using `OfModel.valAt_mul y hf.regAt hf.inv.regAt`. Establish `hone : TrueGeo.valAt y (1 : Z.functionField) = 1`. Use `OfModel.valAt_algebraMap y 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis. Rewrite `hmul` using `[mul_inv_cancel₀ hf.ne_zero, hone]`.

Establish `h₁` using `congrArg e.w hmul`. Rewrite `h₁` using `[map_one, map_mul]`. Establish `hw : e.w (TrueGeo.valAt y f) = 1`. Break down `Real.log_eq_zero.1 h with h0 | h0 | h0` into its components or cases. Rewrite `h₁` using `[h0, zero_mul]`.

Conclude with `absurd h₁ one_ne_zero`. Conclude with `h0`. Use `e.w.nonneg (TrueGeo.valAt y f)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨hw, by rw [hw, one_mul] at h₁; exact h₁.symm⟩`.
-/
theorem w_eq_one_of_log {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    {Z : Scheme.{0}} [IsIntegral Z] (y : Sp (AlgebraicClosure F) ⟶ Z) {f : Z.functionField} (hf : UnitAt (below y) f)
    (h : Real.log (e.w (TrueGeo.valAt y f)) = 0) :
    e.w (TrueGeo.valAt y f) = 1 ∧ e.w (TrueGeo.valAt y f⁻¹) = 1 := by
  have hmul := OfModel.valAt_mul y hf.regAt hf.inv.regAt
  have hone : TrueGeo.valAt y (1 : Z.functionField) = 1 := by
    have := OfModel.valAt_algebraMap y 1
    rwa [map_one, map_one] at this
  rw [mul_inv_cancel₀ hf.ne_zero, hone] at hmul
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  have hw : e.w (TrueGeo.valAt y f) = 1 := by
    rcases Real.log_eq_zero.1 h with h0 | h0 | h0
    · rw [h0, zero_mul] at h₁; exact absurd h₁ one_ne_zero
    · exact h0
    · have := e.w.nonneg (TrueGeo.valAt y f); linarith
  exact ⟨hw, by rw [hw, one_mul] at h₁; exact h₁.symm⟩

end GlobalTheory.LatChain

namespace GlobalTheory.LatChain

/- English proof (translation)
Introduce `F _ _ Y V M lg r hr hN S hS x hx`. Take `⟨i, hi⟩` from `exists_chart M.isLB x`. Establish `he : (M.div hr).IsEqn x (r i)` using `(presents_divOfRatSec M.isLB hr).isEqn i x hi`. It suffices to establish `hu : UnitAt x (r i : V.X.functionField) by`. Use `he.iff_unitAt.2 ?_` and prove the remaining obligations.

Rewrite using `[Units.val_one, one_div]`. Conclude with `hu.inv`. Break down `exists_ov_or_mem_range V x with ⟨l, hl, hlx⟩ | ⟨z, rfl⟩` into its components or cases. Establish `hlS : l ∉ S` using `fun h => hx l h hlx`. Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), resP v = l → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U i → e.w (TrueGeo.valAt (z ≫ V.j) (r i : V.X.functionField)) = 1 ∧ …`.

Introduce `v hv e y z yt hzy hyt hU`. Establish `h0 : lg v e y = 0` using `hS v (hv ▸ hlS) e y`. Establish `h1` using `hN.2.2 v e y z yt i hzy hyt hU`. Establish `hb : below (z ≫ V.j) = V.j (below z)` using `rfl`. Establish `hmem : V.j (below z) ∈ M.B.U i`.

Rewrite using `[← hb, ← hyt]`. Conclude with `hU (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial`. Establish `hunit : UnitAt (below (z ≫ V.j)) (r i : V.X.functionField)` using `hb ▸ hN.2.1 i (below z) hmem`. Conclude with `w_eq_one_of_log e (z ≫ V.j) hunit (h1 ▸ h0)`. Establish `hreg` using `GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V l hl ⊤ trivial (M.B.U i) (r i) (fun z hz => (hN.2.1 i z hz).regAt) (fun v hv e y _ z yt hzy hyt hU => (key v hv e y z yt hzy hyt hU).1.le) x hi hlx`.

Establish `hreg'` using `GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V l hl ⊤ trivial (M.B.U i) (r i)⁻¹ (fun z hz => (hN.2.1 i z hz).inv.regAt) (fun v hv e y _ z yt hzy hyt hU => (key v hv e y z yt hzy hyt hU).2.le) x hi hlx`. Conclude with `(unitAt_iff (r i).ne_zero).2 ⟨hreg, hreg'⟩`. Conclude with `hN.2.1 i z hi`.
-/
theorem isEqn_one_off : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), NormsX V M lg r hr → ∀ S : Finset ℕ, (∀ v, resP v ∉ S → ∀ e y, lg v e y = 0) → ∀ x, (∀ p ∈ S, ¬ Ov p x) → (M.div hr).IsEqn x 1 := by
  intro F _ _ Y V M lg r hr hN S hS x hx
  obtain ⟨i, hi⟩ := exists_chart M.isLB x
  have he : (M.div hr).IsEqn x (r i) := (presents_divOfRatSec M.isLB hr).isEqn i x hi
  suffices hu : UnitAt x (r i : V.X.functionField) by
    refine he.iff_unitAt.2 ?_
    rw [Units.val_one, one_div]
    exact hu.inv
  rcases exists_ov_or_mem_range V x with ⟨l, hl, hlx⟩ | ⟨z, rfl⟩
  · have hlS : l ∉ S := fun h => hx l h hlx

    have key : ∀ v : HeightOneSpectrum (𝓞 F), resP v = l → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y),
        ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
        ⊤ ≤ yt ⁻¹ᵁ M.B.U i → e.w (TrueGeo.valAt (z ≫ V.j) (r i : V.X.functionField)) = 1 ∧
          e.w (TrueGeo.valAt (z ≫ V.j) (r i : V.X.functionField)⁻¹) = 1 := by
      intro v hv e y z yt hzy hyt hU
      have h0 : lg v e y = 0 := hS v (hv ▸ hlS) e y
      have h1 := hN.2.2 v e y z yt i hzy hyt hU
      have hb : below (z ≫ V.j) = V.j (below z) := rfl
      have hmem : V.j (below z) ∈ M.B.U i := by
        rw [← hb, ← hyt]
        exact hU (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial
      have hunit : UnitAt (below (z ≫ V.j)) (r i : V.X.functionField) := hb ▸ hN.2.1 i (below z) hmem
      exact w_eq_one_of_log e (z ≫ V.j) hunit (h1 ▸ h0)
    have hreg := GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V l hl ⊤ trivial (M.B.U i) (r i)
      (fun z hz => (hN.2.1 i z hz).regAt)
      (fun v hv e y _ z yt hzy hyt hU => (key v hv e y z yt hzy hyt hU).1.le) x hi hlx
    have hreg' := GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V l hl ⊤ trivial (M.B.U i) (r i)⁻¹
      (fun z hz => (hN.2.1 i z hz).inv.regAt)
      (fun v hv e y _ z yt hzy hyt hU => (key v hv e y z yt hzy hyt hU).2.le) x hi hlx
    exact (unitAt_iff (r i).ne_zero).2 ⟨hreg, hreg'⟩
  · exact hN.2.1 i z hi

end GlobalTheory.LatChain
