import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.FrameSign

open GlobalTheory.CubeValues GlobalTheory.SelfCube

/- English proof (translation)
Take `⟨s, hs, hsp, hli⟩` from `exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))`. Use `haveI : Finite s := hli.finite`. Use `haveI : Fintype s := Fintype.ofFinite s`. Set `b : Module.Basis s ℝ (Fin g → ℂ)` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, h])`. Establish `hb : Submodule.span ℤ (Set.range b) ≤ Λ.toIntSubmodule`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Module.Basis.mk_apply]`. Conclude with `hs i.2`. Use `⟨∑ i, ‖b i‖, fun z => ⟨-(ZSpan.floor b z : Fin g → ℂ), Λ.neg_mem (hb (ZSpan.floor b z).2), ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_add_neg, ← ZSpan.fract_apply]`. Conclude with `ZSpan.norm_fract_le b z`.
-/
theorem exists_norm_add_le {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ))
    (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ R : ℝ, ∀ z : Fin g → ℂ, ∃ l ∈ (Λ : Set (Fin g → ℂ)), ‖z + l‖ ≤ R := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  haveI : Finite s := hli.finite
  haveI : Fintype s := Fintype.ofFinite s
  let b : Module.Basis s ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, h])
  have hb : Submodule.span ℤ (Set.range b) ≤ Λ.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.mk_apply]
    exact hs i.2
  refine ⟨∑ i, ‖b i‖, fun z => ⟨-(ZSpan.floor b z : Fin g → ℂ), Λ.neg_mem (hb (ZSpan.floor b z).2), ?_⟩⟩
  rw [← sub_eq_add_neg, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b z

/- English proof (translation)
Establish `hv : ValueRules` using `valAt'_rules`. Take `⟨t, ht⟩` from `hiso`. Establish `hp' : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ p z ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (p z) U f) {z | ⊤ ≤ p z ⁻¹ᵁ U}` using `fun U f => by`. Simplify `hp U f` using `only [Set.mem_univ, true_and]`. Set `V : L.ι → Set (Fin g → ℂ)` to `fun i => {z | ⊤ ≤ p z ⁻¹ᵁ L.U i}`.

Set `D : (K → L.ι) × L.ι → Set (Fin g → ℂ)` to `fun j => {z | ⊤ ≤ p z ⁻¹ᵁ ((LB.LinComb L φ ε).U j.1 ⊓ L.U j.2)}`. Establish `hD : ∀ j z, z ∈ D j ↔ (∀ I, lam I z ∈ V (j.1 I)) ∧ z ∈ V j.2` using `fun j z => by`. Use `(le_preimage_inf _ _ _).trans (and_congr ?_ Iff.rfl)` and prove the remaining obligations. Use `(le_preimage_wchart (p z) L _ _).trans ?_` and prove the remaining obligations. Simplify using `only [hlam]`.

Both sides reduce to the same expression. Set `T : (K → L.ι) × L.ι → (Fin g → ℂ) → ℂ` to `fun j z => valAt' (p z) ((LB.LinComb L φ ε).U j.1 ⊓ L.U j.2) (t.s j).val`. Set `G : (K → L.ι) × L.ι → (Fin g → ℂ) → ℂ` to `fun j z => T j z * fr j.2 z * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I)`. Establish `hch : ∀ z, ∃ i, ⊤ ≤ p z ⁻¹ᵁ L.U i` using `fun z => by`. Establish `h : p z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i`.

Rewrite using `[hL.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Conclude with `⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩`. Establish `hcov : ∀ z, ∃ j, z ∈ D j` using `fun z => by choose c hc using hch`.

Conclude with `⟨(fun I => c (lam I z), c z), (hD _ _).2 ⟨fun I => hc _, hc _⟩⟩`. Take `⟨ψ, hψ, hG⟩` from `SelfCube.exists_glue D G (fun j => (hp' _ 0).1) hcov (fun j => by`. Use `((hp' _ (t.s j).val).2.mul ((fr_hol j.2).mono fun z hz => ((hD j z).1 hz).2)).mul (differentiableOn_prod' _ fun I => ?_)` and prove the remaining obligations. Use `DifferentiableOn.zpow ((fr_hol (j.1 I)).comp (hld I).differentiableOn fun z hz => ((hD j z).1 hz).1 I) ?_` and prove the remaining obligations. Conclude with `Or.inl fun z hz => fr_ne _ _ (((hD j z).1 hz).1 I))`.

Use the proof step `(fun j j' z hz hz' => by`. Establish `e1 : T j z = _ * T j' z` using `val_gen (p z) hv t ht j j' hz hz'`. Establish `e2` using `val_div hv (p z) (LB.LinComb L φ ε) L j j' hz hz'`. Establish `e3` using `val_linComb (p z) hv L _ ε j.1 j'.1 ((le_preimage_inf _ _ _).1 hz).1 ((le_preimage_inf _ _ _).1 hz').1`. Establish `e4` using `e2.trans e3`.

Simplify using `only [hlam] at e4`. Take `⟨h1, h2⟩` from `(hD j z).1 hz`. Take `⟨h1', h2'⟩` from `(hD j' z).1 hz'`. Establish `c0` using `fr_g _ _ z ((le_preimage_inf _ _ _).2 ⟨h2, h2'⟩)`. Establish `c1 : ∏ I, fr (j'.1 I) (lam I z) ^ (-ε I) = (∏ I, valAt' (p (lam I z)) (L.U (j.1 I) ⊓ L.U (j'.1 I)) (L.g (j.1 I) (j'.1 I)).val ^ ε I) * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I)`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun I _ => ?_` and prove the remaining obligations. Establish `hI` using `(le_preimage_inf _ _ _).2 ⟨h1 I, h1' I⟩`. Rewrite using `[fr_g _ _ _ hI, mul_zpow, ← _root_.mul_assoc, ← zpow_add₀ (val_unit_ne_zero _ hv hI _)]`. Simplify using the standard rewrite rules.

Simplify using `only [G]`. Rewrite using `[e1, c0, c1, ← e4]`. Use the proof step `ring)`. Use `⟨ψ, hψ, fun z => ?_, fun z z' a₀ a hz h0 ha => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hcov z`.

Take `⟨h1, h2⟩` from `(hD j z).1 hj`. Rewrite using `[hG j z hj]`. Conclude with `mul_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hj _) (fr_ne _ _ h2)) (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (fr_ne _ _ (h1 I)))`. Take `⟨j, hj⟩` from `hcov z`. Establish `hj' : z' ∈ D j`.

Simplify using `only [D, Set.mem_setOf_eq, hz]`. Conclude with `hj`. Take `⟨h1, h2⟩` from `(hD j z).1 hj`. Establish `eT : T j z' = T j z` using `by simp only [T, hz]`. Establish `c1 : ∏ I, fr (j.1 I) (lam I z') ^ (-ε I) = (∏ I, a I ^ ε I) * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I)`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun I _ => ?_` and prove the remaining obligations. Establish `e` using `ha _ _ (h1 I)`. Establish `n0 : a I ≠ 0` using `fun h => fr_ne _ _ (h1 I) (by rw [e, h, zero_mul])`. Rewrite using `[e, mul_zpow, ← _root_.mul_assoc, ← zpow_add₀ n0]`.

Simplify using the standard rewrite rules. Rewrite using `[hG j z hj, hG j _ hj']`. Simplify using `only [G]`. Rewrite using `[eT, c1, h0 _ h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_unit {g : ℕ} {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
    (hp : IsHolTo Set.univ p) {K : Type} [Fintype K] (φ : K → (Y ⟶ Y)) (ε : K → ℤ)
    (lam : K → (Fin g → ℂ) → (Fin g → ℂ)) (hld : ∀ k, Differentiable ℂ (lam k))
    (hlam : ∀ k z, p z ≫ φ k = p (lam k z)) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ p z ⁻¹ᵁ L.U j})
    (fr_ne : ∀ j z, ⊤ ≤ p z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ p z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (p z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z)
    (hiso : Geo.Tor.LBIso L (LB.LinComb L φ ε)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ (∀ z, ψ z ≠ 0) ∧ ∀ z z' (a₀ : ℂ) (a : K → ℂ), p z' = p z →
      (∀ i, ⊤ ≤ p z ⁻¹ᵁ L.U i → fr i z = a₀ * fr i z') →
      (∀ k i, ⊤ ≤ p (lam k z) ⁻¹ᵁ L.U i → fr i (lam k z) = a k * fr i (lam k z')) →
      ψ z' * a₀ = (∏ k, a k ^ ε k) * ψ z := by
  have hv : ValueRules := valAt'_rules
  obtain ⟨t, ht⟩ := hiso
  have hp' : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (p z) U f) {z | ⊤ ≤ p z ⁻¹ᵁ U} := fun U f => by
    simpa only [Set.mem_univ, true_and] using hp U f
  let V : L.ι → Set (Fin g → ℂ) := fun i => {z | ⊤ ≤ p z ⁻¹ᵁ L.U i}
  let D : (K → L.ι) × L.ι → Set (Fin g → ℂ) := fun j =>
    {z | ⊤ ≤ p z ⁻¹ᵁ ((LB.LinComb L φ ε).U j.1 ⊓ L.U j.2)}
  have hD : ∀ j z, z ∈ D j ↔ (∀ I, lam I z ∈ V (j.1 I)) ∧ z ∈ V j.2 := fun j z => by
    refine (le_preimage_inf _ _ _).trans (and_congr ?_ Iff.rfl)
    refine (le_preimage_wchart (p z) L _ _).trans ?_
    simp only [hlam]
    rfl
  let T : (K → L.ι) × L.ι → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (p z) ((LB.LinComb L φ ε).U j.1 ⊓ L.U j.2) (t.s j).val
  let G : (K → L.ι) × L.ι → (Fin g → ℂ) → ℂ := fun j z =>
    T j z * fr j.2 z * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I)
  have hch : ∀ z, ∃ i, ⊤ ≤ p z ⁻¹ᵁ L.U i := fun z => by
    have h : p z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  have hcov : ∀ z, ∃ j, z ∈ D j := fun z => by
    choose c hc using hch
    exact ⟨(fun I => c (lam I z), c z), (hD _ _).2 ⟨fun I => hc _, hc _⟩⟩
  obtain ⟨ψ, hψ, hG⟩ := SelfCube.exists_glue D G (fun j => (hp' _ 0).1) hcov
    (fun j => by
      refine ((hp' _ (t.s j).val).2.mul ((fr_hol j.2).mono fun z hz => ((hD j z).1 hz).2)).mul
        (differentiableOn_prod' _ fun I => ?_)
      refine DifferentiableOn.zpow
        ((fr_hol (j.1 I)).comp (hld I).differentiableOn fun z hz => ((hD j z).1 hz).1 I) ?_
      exact Or.inl fun z hz => fr_ne _ _ (((hD j z).1 hz).1 I))
    (fun j j' z hz hz' => by
      have e1 : T j z = _ * T j' z := val_gen (p z) hv t ht j j' hz hz'
      have e2 := val_div hv (p z) (LB.LinComb L φ ε) L j j' hz hz'
      have e3 := val_linComb (p z) hv L _ ε j.1 j'.1
        ((le_preimage_inf _ _ _).1 hz).1 ((le_preimage_inf _ _ _).1 hz').1
      have e4 := e2.trans e3
      simp only [hlam] at e4
      obtain ⟨h1, h2⟩ := (hD j z).1 hz
      obtain ⟨h1', h2'⟩ := (hD j' z).1 hz'
      have c0 := fr_g _ _ z ((le_preimage_inf _ _ _).2 ⟨h2, h2'⟩)
      have c1 : ∏ I, fr (j'.1 I) (lam I z) ^ (-ε I) =
          (∏ I, valAt' (p (lam I z)) (L.U (j.1 I) ⊓ L.U (j'.1 I))
            (L.g (j.1 I) (j'.1 I)).val ^ ε I) * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I _ => ?_
        have hI := (le_preimage_inf _ _ _).2 ⟨h1 I, h1' I⟩
        rw [fr_g _ _ _ hI, mul_zpow, ← _root_.mul_assoc,
          ← zpow_add₀ (val_unit_ne_zero _ hv hI _)]
        simp
      simp only [G]
      rw [e1, c0, c1, ← e4]
      ring)
  refine ⟨ψ, hψ, fun z => ?_, fun z z' a₀ a hz h0 ha => ?_⟩
  · obtain ⟨j, hj⟩ := hcov z
    obtain ⟨h1, h2⟩ := (hD j z).1 hj
    rw [hG j z hj]
    exact mul_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hj _) (fr_ne _ _ h2))
      (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (fr_ne _ _ (h1 I)))
  · obtain ⟨j, hj⟩ := hcov z
    have hj' : z' ∈ D j := by
      simp only [D, Set.mem_setOf_eq, hz]
      exact hj
    obtain ⟨h1, h2⟩ := (hD j z).1 hj
    have eT : T j z' = T j z := by simp only [T, hz]
    have c1 : ∏ I, fr (j.1 I) (lam I z') ^ (-ε I) =
        (∏ I, a I ^ ε I) * ∏ I, fr (j.1 I) (lam I z) ^ (-ε I) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      have e := ha _ _ (h1 I)
      have n0 : a I ≠ 0 := fun h => fr_ne _ _ (h1 I) (by rw [e, h, zero_mul])
      rw [e, mul_zpow, ← _root_.mul_assoc, ← zpow_add₀ n0]
      simp
    rw [hG j z hj, hG j _ hj']
    simp only [G]
    rw [eT, c1, h0 _ h2]
    ring

/- English proof (translation)
Establish `key : ∀ s : List (Fin n), q ≫ s.foldr (fun k acc => padd G (y k) acc) (pzero G T) = ex (s.map w).sum`. Introduce `s`. Proceed by induction on `s with`. Consider the case `nil`. Express the relevant statement in the definitionally equal form `q ≫ (1 : T ⟶ G) = _`.

Simplify using `[h0]`. Consider the case `cons a s ih`. Express the relevant statement in the definitionally equal form `q ≫ (y a * _) = _`. Rewrite using `[MonObj.comp_mul, ih, h, List.map_cons, List.sum_cons, hadd]`. Unfold `psum`.

Rewrite using `[key, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]`. Use `congr 2`. Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem comp_psum {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] {V : Type} [AddCommGroup V]
    (ex : V → (T' ⟶ G)) (h0 : ex 0 = 1) (hadd : ∀ z w, ex (z + w) = ex z * ex w) (q : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ G)) (w : Fin n → V) (h : ∀ k, q ≫ y k = ex (w k)) (I : Finset (Fin n)) :
    q ≫ psum G y I = ex (∑ a ∈ I, w a) := by
  have key : ∀ s : List (Fin n),
      q ≫ s.foldr (fun k acc => padd G (y k) acc) (pzero G T) = ex (s.map w).sum := by
    intro s
    induction s with
    | nil =>
      change q ≫ (1 : T ⟶ G) = _
      simp [h0]
    | cons a s ih =>
      change q ≫ (y a * _) = _
      rw [MonObj.comp_mul, ih, h, List.map_cons, List.sum_cons, hadd]
  unfold psum
  rw [key, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 2
  ext a
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y)

/- English proof (translation)
Rewrite using `[pv, per_add]`. Both sides reduce to the same expression.
-/
theorem pv_add (u v : Fin r → E) : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  rw [pv, per_add]; rfl

/- English proof (translation)
Rewrite using `[pv, per_zero]`. Both sides reduce to the same expression.
-/
theorem pv_zero : pv X idx x 0 = 0 := by
  rw [pv, per_zero]; rfl

/- English proof (translation)
Rewrite using `[A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]`.
-/
theorem ex_add_pv (z : Fin g → ℂ) {v : Fin r → E} (hv : v ∈ L) : A.ex (z + pv X idx x v) = A.ex z := by
  rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ⊤ ≤ (A.ex 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := by`. Establish `h : (A.ex 0).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i`. Rewrite using `[Xo.univ.t.PP.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`.

Conclude with `⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩`. Establish `hH` using `Hm_isHermitian idx hs hx`. Establish `e1` using `A.fr_per u hu i 0 hi`. Establish `e2` using `A.fr_per v hv i (0 + pv X idx x u) (by rw [ex_add_pv A _ hu]; exact hi)`. Establish `e3` using `A.fr_per (u + v) (L.add_mem hu hv) i 0 hi`.

Establish `n0` using `A.fr_ne i (0 + pv X idx x (u + v)) (by rw [ex_add_pv A _ (L.add_mem hu hv)]; exact hi)`. Establish `e4` using `e3.symm.trans e1`. Rewrite `e4` using `[e2, add_assoc, ← pv_add, ← _root_.mul_assoc]`. Establish `e5` using `mul_right_cancel₀ n0 e4`. Establish `e6` using `Complex.sub_conj (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v))`.

Establish `him : (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)` using `im_hermForm_Hm idx hs hx u v`. Rewrite `e6` using `[him, ← herm_conj _ hH]`. Rewrite `e6` using `[Complex.ofReal_mul, Complex.ofReal_ratCast, Complex.ofReal_ofNat]`. Simplify using `only [hx_eq_hermForm, herm_zero_left, zero_add, mul_zero, pv_add, herm_add_left, SelfCube.herm_add_right] at e5`. Use `mul_right_cancel₀ (Complex.exp_ne_zero _) (e5.trans ?_)` and prove the remaining obligations.

Rewrite using `[_root_.mul_mul_mul_comm, ← Complex.exp_add, _root_.mul_assoc (A.χ u * A.χ v), ← Complex.exp_add]`. Use `congr 2`. Take the linear combination `(Real.pi / 2 : ℂ) * e6`.
-/
theorem chi_add (hs : IsSympl X bas) (hx : x ∈ X.dom) {u v : Fin r → E} (hu : u ∈ L) (hv : v ∈ L) :
    A.χ (u + v) = A.χ u * A.χ v * cexp (Real.pi * I * ((EF X u v : ℚ) : ℂ)) := by
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (A.ex 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := by
    have h : (A.ex 0).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  have hH := Hm_isHermitian idx hs hx
  have e1 := A.fr_per u hu i 0 hi
  have e2 := A.fr_per v hv i (0 + pv X idx x u) (by rw [ex_add_pv A _ hu]; exact hi)
  have e3 := A.fr_per (u + v) (L.add_mem hu hv) i 0 hi
  have n0 := A.fr_ne i (0 + pv X idx x (u + v)) (by rw [ex_add_pv A _ (L.add_mem hu hv)]; exact hi)
  have e4 := e3.symm.trans e1
  rw [e2, add_assoc, ← pv_add, ← _root_.mul_assoc] at e4
  have e5 := mul_right_cancel₀ n0 e4
  have e6 := Complex.sub_conj (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v))
  have him : (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  rw [him, ← herm_conj _ hH] at e6
  rw [Complex.ofReal_mul, Complex.ofReal_ratCast, Complex.ofReal_ofNat] at e6
  simp only [hx_eq_hermForm, herm_zero_left, zero_add, mul_zero, pv_add, herm_add_left,
    SelfCube.herm_add_right] at e5
  refine mul_right_cancel₀ (Complex.exp_ne_zero _) (e5.trans ?_)
  rw [_root_.mul_mul_mul_comm, ← Complex.exp_add, _root_.mul_assoc (A.χ u * A.χ v), ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2 : ℂ) * e6

end GlobalTheory.Dict.FrameSign

open GlobalTheory.Dict.FrameSign GlobalTheory.SelfCube in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL`. Establish `hH` using `Hm_isHermitian idx hs hx`. Use `set M := ThFr.Hm X bas idx x with hM`. Establish `hχ0 : ∀ v ∈ L, A.χ v ≠ 0` using `fun v hv h => by simpa [h] using A.χ_norm v hv`. Establish `hz : A.χ 0 = 1`.

Use `chi_add A hs hx L.zero_mem L.zero_mem` as an intermediate fact. Establish `h0 : EF X 0 0 = 0` using `by simp [EF_def, herm]`. Simplify using `only [add_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero, _root_.mul_one] at this`. Conclude with `(mul_eq_left₀ (hχ0 0 L.zero_mem)).1 this.symm`. Establish `hw : ∀ v ∈ L, (H.w0 : E) • v ∈ L` using `fun v hv => L.smul_mem H.w0 hv`.

Set `F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `{ toFun := fun z j => rowType X (idx j) (H.w0 : E) * z j map_add' := fun z w => funext fun j => mul_add _ _ _ map_smul' := fun t z => funext fun j => mul_left_comm _ _ _ }`. Establish `hF : ∀ v, pv X idx x ((H.w0 : E) • v) = F (pv X idx x v)` using `fun v => pv_smul idx x _ v`. Set `lam : ULift.{0} (Finset (Fin 2)) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `fun J => ∑ k ∈ J.down, ![LinearMap.id, F] k`. Establish `hex0 : A.ex 0 = 1` using `(A.ex_ker 0).2 ⟨0, L.zero_mem, pv_zero.symm⟩`. Take `⟨ψ, hψ, hψ0, hper⟩` from `exists_unit Xo.univ.t.PP.isLB (fun z => (A.ex z).left) A.hol _ _ (fun J => lam J) (fun J => (LinearMap.toContinuousLinearMap (lam J)).differentiable) (fun J z => by`.

Use `FrameSign.comp_psum A.ex hex0 A.ex_add (A.ex z) ![𝟙 _, Xo.univ.t.act.act H.w0] (fun k => ![LinearMap.id, F] k z) (fun k => by fin_cases k` as an intermediate fact. Conclude with `Category.comp_id _`. Conclude with `(A.ex_lin H.w0 z).symm) J.down`. Simplify using `only [lam, LinearMap.sum_apply]`. Conclude with `congrArg (·.left) this)`.

Use the proof step `A.fr A.fr_hol A.fr_ne A.fr_g Xo.univ.t.prim`. Set `pvh : (Fin r → E) →+ (Fin g → ℂ)` to `AddMonoidHom.mk' (pv X idx x) pv_add`. Take `⟨R, hR⟩` from `exists_norm_add_le (L.toAddSubgroup.map pvh) (span_image_pv idx hs hx L (TensLat.span_of_selfD X hL))`. Establish `hFc : Continuous F` using `LinearMap.continuous_of_finiteDimensional F`. Establish `key : ∀ v ∈ L, ∀ z, ψ (z + pv X idx x v) = eps1 X (H.w0 : E) v / A.χ v * cexp (Real.pi * (hermForm M z (F (pv X idx x v)) + hermForm M (F z) (pv X idx x v) - hermForm M z (pv X idx x v)) + Real.pi / 2 * (hermForm M (pv X idx x v) (F (pv X idx x v)) + hermForm M (F (pv X idx x v)) …`.

Introduce `v hv z`. Set `u : Finset (Fin 2) → Fin r → E` to `fun J => ∑ k ∈ J, ![v, (H.w0 : E) • v] k`. Establish `huL : ∀ J, u J ∈ L` using `fun J => L.sum_mem fun k _ => by fin_cases k`. Conclude with `hv`. Conclude with `hw v hv`.

Establish `hup : ∀ J : ULift.{0} (Finset (Fin 2)), pv X idx x (u J.down) = lam J (pv X idx x v)` using `fun J => by`. Simplify using `only [lam, LinearMap.sum_apply]`. Use `(map_sum pvh _ _).trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Use `fin_cases k`. Both sides reduce to the same expression.

Conclude with `hF v`. Establish `h` using `hper z (z + pv X idx x v) _ (fun J => A.χ (u J.down) * cexp (Real.pi * hermForm M (lam J z) (lam J (pv X idx x v)) + Real.pi / 2 * hermForm M (lam J (pv X idx x v)) (lam J (pv X idx x v)))) (congrArg (·.left) (ex_add_pv A z hv)) (fun i hi => A.fr_per v hv i z hi) (fun J i hi => b …`. Use `A.fr_per _ (huL J.down) i _ hi` as an intermediate fact. Rewrite `this` using `[hx_eq_hermForm, hx_eq_hermForm, hup]`. Rewrite using `[map_add]`.

Conclude with `this)`. Rewrite `h` using `[prod_finset_fin_two (fun J : Finset (Fin 2) => (A.χ (u J) * cexp (Real.pi * hermForm M (lam ⟨J⟩ z) (lam ⟨J⟩ (pv X idx x v)) + Real.pi / 2 * hermForm M (lam ⟨J⟩ (pv X idx x v)) (lam ⟨J⟩ (pv X idx x v)))) ^ ((-1 : ℤ) ^ (2 - J.card)))]`. Establish `a2 : A.χ (v + (H.w0 : E) • v) = A.χ v * A.χ ((H.w0 : E) • v) * eps1 X (H.w0 : E) v` using `chi_add A hs hx hv (hw v hv)`. Establish `c2 : ({0, 1} : Finset (Fin 2)).card = 2` using `by decide`. Establish `d2 : (0 : Fin 2) ≠ 1` using `by decide`.

Simplify using `only [u, lam, Finset.sum_pair d2, c2, hx_eq_hermForm, ← hM, Finset.sum_empty, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply, LinearMap.zero_apply, LinearMap.id_apply, Finset.card_empty, Finset.card_singleton, herm_zero_left, hz, a2, herm_add …`. Establish `n1` using `hχ0 v hv`. Establish `n2` using `hχ0 _ (hw v hv)`. Generalize the expression as in `A.χ ((H.w0 : E) • v) = b at h n2`. Evaluate the numerical expressions using `at h`.

Use `mul_right_cancel₀ (mul_ne_zero n1 (Complex.exp_ne_zero _)) (h.trans ?_)` and prove the remaining obligations. Simplify using `only [mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]`. Clear the denominators using the available nonvanishing facts. Take `⟨hD, hc⟩` from `FrameUnits.form_eq_zero_and_const hR ψ hψ hψ0 (fun z w => hermForm M z (F w) + hermForm M (F z) w - hermForm M z w) (((herm_continuous M continuous_id hFc).add (herm_continuous M hFc continuous_id)).sub (herm_continuous M continuous_id continuous_id)) (fun z z' w => by simp only …`. Simplify using `only [Complex.star_def, map_add, map_sub, ← herm_conj M hH]`.

Use the proof step `ring)`. Use the proof step `(by`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `⟨_, ?_, key v hv⟩` and prove the remaining obligations. Rewrite using `[norm_div, A.χ_norm v hv, div_one, eps1, Complex.norm_exp]`.

Use the proof step `simp)`. Introduce `v hv`. Establish `h` using `key v hv 0`. Establish `h1` using `hD 0 (pv X idx x v)`. Establish `h2` using `hD (pv X idx x v) (pv X idx x v)`.

Rewrite `h` using `[hc, h1, h2]`. Simplify using `only [mul_zero, add_zero, Complex.exp_zero, _root_.mul_one] at h`. Conclude with `((div_eq_one_iff_eq (hχ0 v hv)).1 ((mul_eq_right₀ (hψ0 0)).1 h.symm)).symm`.
-/
theorem GlobalTheory.Dict.analyticFibre_principalBundle_sign_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ v ∈ L, A.χ v = eps1 X (H.w0 : E) v := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have hH := Hm_isHermitian idx hs hx
  set M := ThFr.Hm X bas idx x with hM
  have hχ0 : ∀ v ∈ L, A.χ v ≠ 0 := fun v hv h => by simpa [h] using A.χ_norm v hv
  have hz : A.χ 0 = 1 := by
    have := chi_add A hs hx L.zero_mem L.zero_mem
    have h0 : EF X 0 0 = 0 := by simp [EF_def, herm]
    simp only [add_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero, _root_.mul_one] at this
    exact (mul_eq_left₀ (hχ0 0 L.zero_mem)).1 this.symm
  have hw : ∀ v ∈ L, (H.w0 : E) • v ∈ L := fun v hv => L.smul_mem H.w0 hv
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := fun z j => rowType X (idx j) (H.w0 : E) * z j
      map_add' := fun z w => funext fun j => mul_add _ _ _
      map_smul' := fun t z => funext fun j => mul_left_comm _ _ _ }
  have hF : ∀ v, pv X idx x ((H.w0 : E) • v) = F (pv X idx x v) := fun v => pv_smul idx x _ v
  let lam : ULift.{0} (Finset (Fin 2)) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    fun J => ∑ k ∈ J.down, ![LinearMap.id, F] k
  have hex0 : A.ex 0 = 1 := (A.ex_ker 0).2 ⟨0, L.zero_mem, pv_zero.symm⟩
  obtain ⟨ψ, hψ, hψ0, hper⟩ := exists_unit Xo.univ.t.PP.isLB (fun z => (A.ex z).left) A.hol _ _
    (fun J => lam J) (fun J => (LinearMap.toContinuousLinearMap (lam J)).differentiable)
    (fun J z => by
      have := FrameSign.comp_psum A.ex hex0 A.ex_add (A.ex z) ![𝟙 _, Xo.univ.t.act.act H.w0]
        (fun k => ![LinearMap.id, F] k z) (fun k => by
          fin_cases k
          · exact Category.comp_id _
          · exact (A.ex_lin H.w0 z).symm) J.down
      simp only [lam, LinearMap.sum_apply]
      exact congrArg (·.left) this)
    A.fr A.fr_hol A.fr_ne A.fr_g Xo.univ.t.prim
  let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) pv_add
  obtain ⟨R, hR⟩ := exists_norm_add_le (L.toAddSubgroup.map pvh)
    (span_image_pv idx hs hx L (TensLat.span_of_selfD X hL))
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have key : ∀ v ∈ L, ∀ z, ψ (z + pv X idx x v) = eps1 X (H.w0 : E) v / A.χ v *
      cexp (Real.pi * (hermForm M z (F (pv X idx x v)) + hermForm M (F z) (pv X idx x v) -
          hermForm M z (pv X idx x v)) +
        Real.pi / 2 * (hermForm M (pv X idx x v) (F (pv X idx x v)) +
          hermForm M (F (pv X idx x v)) (pv X idx x v) - hermForm M (pv X idx x v) (pv X idx x v))) * ψ z := by
    intro v hv z
    let u : Finset (Fin 2) → Fin r → E := fun J => ∑ k ∈ J, ![v, (H.w0 : E) • v] k
    have huL : ∀ J, u J ∈ L := fun J => L.sum_mem fun k _ => by
      fin_cases k
      · exact hv
      · exact hw v hv
    have hup : ∀ J : ULift.{0} (Finset (Fin 2)), pv X idx x (u J.down) = lam J (pv X idx x v) := fun J => by
      simp only [lam, LinearMap.sum_apply]
      refine (map_sum pvh _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
      fin_cases k
      · rfl
      · exact hF v
    have h := hper z (z + pv X idx x v) _
      (fun J => A.χ (u J.down) * cexp (Real.pi * hermForm M (lam J z) (lam J (pv X idx x v)) +
        Real.pi / 2 * hermForm M (lam J (pv X idx x v)) (lam J (pv X idx x v))))
      (congrArg (·.left) (ex_add_pv A z hv)) (fun i hi => A.fr_per v hv i z hi)
      (fun J i hi => by
        have := A.fr_per _ (huL J.down) i _ hi
        rw [hx_eq_hermForm, hx_eq_hermForm, hup] at this
        rw [map_add]
        exact this)
    rw [prod_finset_fin_two (fun J : Finset (Fin 2) =>
      (A.χ (u J) * cexp (Real.pi * hermForm M (lam ⟨J⟩ z) (lam ⟨J⟩ (pv X idx x v)) +
        Real.pi / 2 * hermForm M (lam ⟨J⟩ (pv X idx x v)) (lam ⟨J⟩ (pv X idx x v)))) ^
          ((-1 : ℤ) ^ (2 - J.card)))] at h
    have a2 : A.χ (v + (H.w0 : E) • v) = A.χ v * A.χ ((H.w0 : E) • v) * eps1 X (H.w0 : E) v :=
      chi_add A hs hx hv (hw v hv)
    have c2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have d2 : (0 : Fin 2) ≠ 1 := by decide
    simp only [u, lam, Finset.sum_pair d2, c2, hx_eq_hermForm, ← hM, Finset.sum_empty, Finset.sum_singleton,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply, LinearMap.zero_apply,
      LinearMap.id_apply, Finset.card_empty, Finset.card_singleton, herm_zero_left, hz, a2,
      herm_add_left, SelfCube.herm_add_right, mul_zero, add_zero, Complex.exp_zero] at h
    have n1 := hχ0 v hv
    have n2 := hχ0 _ (hw v hv)
    generalize A.χ ((H.w0 : E) • v) = b at h n2
    norm_num at h
    refine mul_right_cancel₀ (mul_ne_zero n1 (Complex.exp_ne_zero _)) (h.trans ?_)
    simp only [mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]
    field_simp
  obtain ⟨hD, hc⟩ := FrameUnits.form_eq_zero_and_const hR ψ hψ hψ0
    (fun z w => hermForm M z (F w) + hermForm M (F z) w - hermForm M z w)
    (((herm_continuous M continuous_id hFc).add (herm_continuous M hFc continuous_id)).sub
      (herm_continuous M continuous_id continuous_id))
    (fun z z' w => by simp only [map_add, herm_add_left]; ring)
    (fun t z w => by simp only [map_smul, herm_smul_left]; ring)
    (fun z w => by
      simp only [Complex.star_def, map_add, map_sub, ← herm_conj M hH]; ring)
    (by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨_, ?_, key v hv⟩
      rw [norm_div, A.χ_norm v hv, div_one, eps1, Complex.norm_exp]
      simp)
  intro v hv
  have h := key v hv 0
  have h1 := hD 0 (pv X idx x v)
  have h2 := hD (pv X idx x v) (pv X idx x v)
  rw [hc, h1, h2] at h
  simp only [mul_zero, add_zero, Complex.exp_zero, _root_.mul_one] at h
  exact ((div_eq_one_iff_eq (hχ0 v hv)).1 ((mul_eq_right₀ (hψ0 0)).1 h.symm)).symm
