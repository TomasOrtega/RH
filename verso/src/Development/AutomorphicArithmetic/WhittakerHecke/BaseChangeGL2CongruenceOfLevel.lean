import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
import GroundTheory.AutomorphicForms.GLnLocal
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open scoped ValuativeRel

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one`.
-/
private theorem mem_int_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

/- English proof (translation)
Establish `h1 : Matrix.GeneralLinearGroup.map (H.cp v) g ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion ℚ) 2`. Rewrite using `[← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq]`. Conclude with `h`. Establish `h2` using `((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).1 h1).2 i j`. Rewrite `h2` using `[← map_inv]`.

Conclude with `(mem_int_iff v _).1 h2`.
-/
private theorem inv_entry_int (v : H.P ℚ) (g : GL (Fin 2) (A ℚ)) (h : H.KAt v g) (i j : Fin 2) :
    Valued.v (((g⁻¹).val i j).2 v) ≤ 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp v) g ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion ℚ) 2 := by
    rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq]
    exact h
  have h2 := ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).1 h1).2 i j
  rw [← map_inv] at h2
  exact (mem_int_iff v _).1 h2

/- English proof (translation)
Establish `hcp : ∀ v : H.P ℚ, ((N : A ℚ)).2 v = (N : H.Kv v)` using `fun v => map_natCast (H.cp v) N`. Establish `hio : ∀ v : H.P ℚ, (iota N).2 v = (N : H.Kv v)⁻¹`. Introduce `v`. Establish `hN' : (N : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `h0 : (iota N).2 * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1`.

Express the relevant statement in the definitionally equal form `algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1`. Rewrite using `[← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)), ← map_mul, inv_mul_cancel₀ hN', map_one]`. Establish `h3` using `congrArg (pLoc ℚ v) h0`. Rewrite `h3` using `[map_mul, map_natCast, map_one]`. Conclude with `eq_inv_of_mul_eq_one_left h3`.

Establish `hne : ∀ v : H.P ℚ, (N : H.Kv v) ≠ 0`. Introduce `v`. Establish `: CharZero (H.Kv v)` using `algebraRat.charZero _`. Conclude with `Nat.cast_ne_zero.2 hN.ne'`. Use `⟨x * iota N, ⟨?_, fun v => ?_⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x.1 * (iota N).1 = 0`. Rewrite using `[h1, zero_mul]`. Express the relevant statement in the definitionally equal form `Valued.v (x.2 v * (iota N).2 v) ≤ 1`. Rewrite using `[hio, map_mul, map_inv₀]`. Establish `hv : Valued.v (N : H.Kv v) ≠ 0` using `(Valuation.ne_zero_iff _).2 (hne v)`.

Conclude with `mul_inv_le_one_of_le₀ (h2 v) zero_le'`. Use `Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1 = (N : A ℚ).1 * (x.1 * (iota N).1)`. Rewrite using `[h1, zero_mul, mul_zero]`. Express the relevant statement in the definitionally equal form `x.2 v = (N : A ℚ).2 v * (x.2 v * (iota N).2 v)`.

Rewrite using `[hcp, hio]`. Clear denominators, using `[hne v]` for the nonvanishing conditions.
-/
private theorem div_of_dv (N : ℕ) (hN : 0 < N) (x : A ℚ) (h1 : x.1 = 0) (h2 : ∀ v, Dv N v x) :
    ∃ c ∈ Oh ℚ, x = (N : A ℚ) * c := by
  have hcp : ∀ v : H.P ℚ, ((N : A ℚ)).2 v = (N : H.Kv v) := fun v => map_natCast (H.cp v) N
  have hio : ∀ v : H.P ℚ, (iota N).2 v = (N : H.Kv v)⁻¹ := by
    intro v
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h0 : (iota N).2 * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
      change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
      rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)), ← map_mul, inv_mul_cancel₀ hN', map_one]
    have h3 := congrArg (pLoc ℚ v) h0
    rw [map_mul, map_natCast, map_one] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hne : ∀ v : H.P ℚ, (N : H.Kv v) ≠ 0 := by
    intro v
    have : CharZero (H.Kv v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN.ne'
  refine ⟨x * iota N, ⟨?_, fun v => ?_⟩, ?_⟩
  · change x.1 * (iota N).1 = 0
    rw [h1, zero_mul]
  · change Valued.v (x.2 v * (iota N).2 v) ≤ 1
    rw [hio, map_mul, map_inv₀]
    have hv : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 (hne v)
    exact mul_inv_le_one_of_le₀ (h2 v) zero_le'
  · refine Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun v => ?_)
    · change x.1 = (N : A ℚ).1 * (x.1 * (iota N).1)
      rw [h1, zero_mul, mul_zero]
    · change x.2 v = (N : A ℚ).2 v * (x.2 v * (iota N).2 v)
      rw [hcp, hio]
      field_simp [hne v]

/- English proof (translation)
Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a.1 + b.1 = 0`. Rewrite using `[ha.1, hb.1, add_zero]`. Express the relevant statement in the definitionally equal form `Valued.v (a.2 v + b.2 v) ≤ 1`. Conclude with `(Valuation.map_add _ _ _).trans (max_le (ha.2 v) (hb.2 v))`.
-/
private theorem oh_add {K : Type} [Field K] [NumberField K] {a b : A K} (ha : a ∈ Oh K) (hb : b ∈ Oh K) :
    a + b ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 + b.1 = 0
    rw [ha.1, hb.1, add_zero]
  · change Valued.v (a.2 v + b.2 v) ≤ 1
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 v) (hb.2 v))

/- English proof (translation)
Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-a.1 = 0`. Rewrite using `[ha.1, neg_zero]`. Express the relevant statement in the definitionally equal form `Valued.v (-(a.2 v)) ≤ 1`. Rewrite using `[Valuation.map_neg]`.

Conclude with `ha.2 v`.
-/
private theorem oh_neg {K : Type} [Field K] [NumberField K] {a : A K} (ha : a ∈ Oh K) : -a ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change -a.1 = 0
    rw [ha.1, neg_zero]
  · change Valued.v (-(a.2 v)) ≤ 1
    rw [Valuation.map_neg]
    exact ha.2 v

/- English proof (translation)
Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a.1 * c.1 = 0`. Rewrite using `[hc.1, mul_zero]`. Express the relevant statement in the definitionally equal form `Valued.v (a.2 v * c.2 v) ≤ 1`. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (ha v) (hc.2 v)`.
-/
private theorem oh_mul (a c : A ℚ) (ha : ∀ v : H.P ℚ, Valued.v (a.2 v) ≤ 1) (hc : c ∈ Oh ℚ) : a * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v (a.2 v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (ha v) (hc.2 v)

/- English proof (translation)
Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations. Establish `: (AdeleBaseChange.adeleMap ℚ E c).1 = GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K` using `ℚ) (L := E) c.1 := rfl`. Rewrite using `[this, hc.1]`. Conclude with `map_zero _`. Rewrite using `[GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply, GroundTheory.Global.SemiLocal.valued_completionMap]`.

Conclude with `pow_le_one' (hc.2 _) _`.
-/
private theorem oh_map (E : Type) [Field E] [NumberField E] {c : A ℚ} (hc : c ∈ Oh ℚ) :
    AdeleBaseChange.adeleMap ℚ E c ∈ Oh E := by
  refine ⟨?_, fun w => ?_⟩
  · have : (AdeleBaseChange.adeleMap ℚ E c).1 =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) c.1 := rfl
    rw [this, hc.1]
    exact map_zero _
  · rw [GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply, GroundTheory.Global.SemiLocal.valued_completionMap]
    exact pow_le_one' (hc.2 _) _

/- English proof (translation)
Take `⟨c, hc, h⟩` from `h`. Use `⟨AdeleBaseChange.adeleMap ℚ E c, oh_map E hc, ?_⟩` and prove the remaining obligations. Establish `h1 : (em E g).val i j = AdeleBaseChange.adeleMap ℚ E (g.val i j)` using `rfl`. Establish `h2 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Matrix.one_apply_eq, map_one]`. Simplify using `only [Matrix.one_apply_ne hij, map_zero]`. Rewrite using `[h1, h2, ← map_sub, h, map_mul, map_natCast]`.
-/
private theorem entry_map (E : Type) [Field E] [NumberField E] (N : ℕ) (g : GL (Fin 2) (A ℚ)) (i j : Fin 2)
    (h : ∃ c ∈ Oh ℚ, g.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c) :
    ∃ c ∈ Oh E, (em E g).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (N : A E) * c := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨AdeleBaseChange.adeleMap ℚ E c, oh_map E hc, ?_⟩
  have h1 : (em E g).val i j = AdeleBaseChange.adeleMap ℚ E (g.val i j) := rfl
  have h2 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
      AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h1, h2, ← map_sub, h, map_mul, map_natCast]

/- English proof (translation)
Introduce `E _ _ N hN k hk`. Establish `hk1 : ∀ i j, ∃ c ∈ Oh ℚ, k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c`. Introduce `i j`. Use `div_of_dv N hN _ ?_ fun v => (hk.2 v).2 i j` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(k.val i j).1 - ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 = 0`.

Rewrite using `[hk.1 i j, sub_self]`. Use `choose c hc hkc using hk1`. Establish `hk2 : ∀ i j, ∃ d ∈ Oh ℚ, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * d`. Introduce `i j`. Establish `hint : ∀ l, (k⁻¹).val i l * c l j ∈ Oh ℚ` using `fun l => oh_mul _ _ (fun v => inv_entry_int v k (hk.2 v).1 i l) (hc l j)`.

Use `⟨-((k⁻¹).val i 0 * c 0 j + (k⁻¹).val i 1 * c 1 j), oh_neg (oh_add (hint 0) (hint 1)), ?_⟩` and prove the remaining obligations. Establish `hm : (k⁻¹).val * k.val = 1`. Use `congrArg Units.val (inv_mul_cancel k)` as an intermediate fact. Simplify using `using this`. Establish `hs : ((k⁻¹).val * (k.val - 1)) i j = (1 - (k⁻¹).val) i j`.

Rewrite using `[Matrix.mul_sub, hm, Matrix.mul_one]`. Rewrite `hs` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, hkc 0 j, hkc 1 j]`. Take the linear combination `hs`. Introduce `i j`. Use `⟨entry_map E N k i j ⟨c i j, hc i j, hkc i j⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Conclude with `entry_map E N k⁻¹ i j (hk2 i j)`.
-/
theorem UpperTheory.baseChangeGL2_congruence_of_level :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ k : GL (Fin 2) (A ℚ), Lev N k → CongE N (em E k) := by
  intro E _ _ N hN k hk
  have hk1 : ∀ i j, ∃ c ∈ Oh ℚ, k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c := by
    intro i j
    refine div_of_dv N hN _ ?_ fun v => (hk.2 v).2 i j
    change (k.val i j).1 - ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 = 0
    rw [hk.1 i j, sub_self]
  choose c hc hkc using hk1
  have hk2 : ∀ i j, ∃ d ∈ Oh ℚ, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * d := by
    intro i j
    have hint : ∀ l, (k⁻¹).val i l * c l j ∈ Oh ℚ := fun l =>
      oh_mul _ _ (fun v => inv_entry_int v k (hk.2 v).1 i l) (hc l j)
    refine ⟨-((k⁻¹).val i 0 * c 0 j + (k⁻¹).val i 1 * c 1 j), oh_neg (oh_add (hint 0) (hint 1)), ?_⟩
    have hm : (k⁻¹).val * k.val = 1 := by
      have := congrArg Units.val (inv_mul_cancel k)
      simpa using this
    have hs : ((k⁻¹).val * (k.val - 1)) i j = (1 - (k⁻¹).val) i j := by
      rw [Matrix.mul_sub, hm, Matrix.mul_one]
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
      hkc 0 j, hkc 1 j] at hs
    linear_combination hs
  intro i j
  refine ⟨entry_map E N k i j ⟨c i j, hc i j, hkc i j⟩, ?_⟩
  rw [← map_inv]
  exact entry_map E N k⁻¹ i j (hk2 i j)
