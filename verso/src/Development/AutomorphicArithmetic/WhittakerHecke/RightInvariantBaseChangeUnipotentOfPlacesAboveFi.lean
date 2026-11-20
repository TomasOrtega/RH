import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Establish `hc' : c ∈ v.adicCompletionIntegers K` using `hc`. Establish `hn : -c ∈ v.adicCompletionIntegers K` using `neg_mem hc'`. Rewrite using `[GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]`. Establish `h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K` using `one_mem _`. Establish `h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K` using `zero_mem _`.

Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1`. Conclude with `hc'`. Conclude with `h0`.

Conclude with `h1`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1`. Conclude with `hn`. Conclude with `h0`.

Conclude with `h1`.
-/
private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v 2 := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K := one_mem _
  have h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `_ z h1 h2 _ g`. Establish `hz : z = 0` using `Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))`. Establish `h : nU (0 : A K) = 1`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU]`. Rewrite using `[hz, h, gl, map_one, mul_one]`. Consider the case `insert w S hw ih`. Introduce `hF z h1 h2 h3 g`.

Take `⟨-, -, hc, -, -, -, -, hs, -, -⟩` from `H.sgLaws K w`. Establish `hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0` using `fun u hu => (hs _).2 u hu`. Establish `e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z)` using `(sub_add_cancel _ _).symm`. Rewrite using `[e, nU_add, gl, map_mul, ← mul_assoc]`. Establish `e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z))` using `((H.lcLaws K w).1 _).symm`.

Rewrite using `[e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]`. Use `ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g` and prove the remaining obligations. Use `show z.1 - (H.sg w (H.cp w z)).1 = 0`. Rewrite using `[h1, (hs _).1, sub_zero]`. Rewrite using `[map_sub]`.

Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[hc, sub_self]`. Rewrite using `[hne u h, sub_zero]`. Conclude with `h2 u (by simp [h, hu])`.

Rewrite using `[map_sub]`. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[hc, sub_self, map_zero]`. Conclude with `zero_le'`.

Rewrite using `[hne u h, sub_zero]`. Conclude with `h3 u`.
-/
private lemma fix_sum {K : Type} [Field K] [NumberField K] (φ : GL (Fin 2) (A K) → ℂ) (S : Finset (H.P K)) :
    (∀ w ∈ S, H.Fix w φ) → ∀ z : A K, z.1 = 0 → (∀ w, w ∉ S → H.cp w z = 0) → (∀ w, Valued.v (H.cp w z) ≤ 1) →
      ∀ g, φ (g * gl (nU z)) = φ g := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ z h1 h2 _ g
    have hz : z = 0 := Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))
    have h : nU (0 : A K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU]
    rw [hz, h, gl, map_one, mul_one]
  | insert w S hw ih =>
    intro hF z h1 h2 h3 g
    obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := H.sgLaws K w
    have hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0 := fun u hu => (hs _).2 u hu
    have e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z) := (sub_add_cancel _ _).symm
    rw [e, nU_add, gl, map_mul, ← mul_assoc]
    have e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z)) :=
      ((H.lcLaws K w).1 _).symm
    rw [e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]
    refine ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g
    · show z.1 - (H.sg w (H.cp w z)).1 = 0
      rw [h1, (hs _).1, sub_zero]
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self]
      · rw [hne u h, sub_zero]
        exact h2 u (by simp [h, hu])
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self, map_zero]
        exact zero_le'
      · rw [hne u h, sub_zero]
        exact h3 u

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Use `Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h` and prove the remaining obligations. Use `(IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩`.
-/
private lemma fin_over {E : Type} [Field E] [NumberField E] (v : H.P ℚ) :
    {w : H.P E | AdeleBaseChange.below ℚ w = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩

/- English proof (translation)
Introduce `E _ _ D φ v hG hF c hc g`. Take `⟨-, -, hcp, -, -, -, -, hs, -, -⟩` from `H.sgLaws ℚ v`. Establish `hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ`. Rewrite using `[Dat.mkE, map_zero, zero_add]`. Establish `hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0` using `fun w hw => by`.

Establish `h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0`. Express the relevant statement in the definitionally equal form `SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0`. Rewrite using `[(hs c).2 _ hw, map_zero]`. Rewrite using `[hz, map_mul, h, zero_mul]`. Express the relevant statement in the definitionally equal form `φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g`.

Use `fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_ (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g` and prove the remaining obligations. Rewrite using `[hz]`. Express the relevant statement in the definitionally equal form `InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0`. Rewrite using `[(hs c).1, map_zero, zero_mul]`. Distinguish the cases in `hw : AdeleBaseChange.below ℚ w = v`.

Substitute `hw` using the available equality. Establish `hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 → Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1` using `fun x hx => by`. Rewrite using `[SemiLocal.valued_completionMap]`. Conclude with `pow_le_one' hx _`. Establish `h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c` using `congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)`.

Establish `h2 : H.cp w (rt D.θ) ^ 2 = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w))`. Rewrite using `[← map_pow, ← map_pow, D.sq]`. Establish `a` using `eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ`. Rewrite using `[map_ratCast]`. Conclude with `a`.

Establish `h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1`. Establish `hd` using `hG.del`. Rewrite `hd` using `[eq_ratCast]`. Establish `h` using `hk _ hd.le`. Rewrite `h` using `[← h2, map_pow]`.

Conclude with `(pow_le_one_iff two_ne_zero).1 h`. Rewrite using `[hz, map_mul, h1, map_mul]`. Conclude with `mul_le_one' (hk c hc) h3`. Rewrite using `[hoff w hw, map_zero]`. Conclude with `zero_le'`.
-/
theorem UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (v : H.P ℚ), H.Gd D.δ v → (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Fix w φ) → ∀ c : H.Kv v, H.IsInt c → ∀ g, φ (g * Xg.nu D (H.sg v c)) = φ g := by
  intro E _ _ D φ v hG hF c hc g
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  have hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ := by
    rw [Dat.mkE, map_zero, zero_add]
  have hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0 := fun w hw => by
    have h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0 := by
      change SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0
      rw [(hs c).2 _ hw, map_zero]
    rw [hz, map_mul, h, zero_mul]
  change φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g
  refine fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_
    (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g
  · rw [hz]
    change InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0
    rw [(hs c).1, map_zero, zero_mul]
  · by_cases hw : AdeleBaseChange.below ℚ w = v
    · subst hw
      have hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 →
          Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1 := fun x hx => by
        rw [SemiLocal.valued_completionMap]
        exact pow_le_one' hx _
      have h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c :=
        congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)
      have h2 : H.cp w (rt D.θ) ^ 2 =
          SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w)) := by
        rw [← map_pow, ← map_pow, D.sq]
        have a := eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ
        rw [map_ratCast]
        exact a
      have h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1 := by
        have hd := hG.del
        rw [eq_ratCast] at hd
        have h := hk _ hd.le
        rw [← h2, map_pow] at h
        exact (pow_le_one_iff two_ne_zero).1 h
      rw [hz, map_mul, h1, map_mul]
      exact mul_le_one' (hk c hc) h3
    · rw [hoff w hw, map_zero]
      exact zero_le'
