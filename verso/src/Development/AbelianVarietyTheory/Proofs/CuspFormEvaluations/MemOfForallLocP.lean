import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.StdNab

open IsDedekindDomain

/- English proof (translation)
Use `⟨fun hx a => GlobalTheory.NabStab.int_of_mem_colLat_one hx a, fun h => ?_⟩` and prove the remaining obligations. Use `choose y hy using h`. Establish `hx : x = ∑ j, y j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j`. Use function extensionality and compare the values at `a`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hy]`.

Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  refine ⟨fun hx a => GlobalTheory.NabStab.int_of_mem_colLat_one hx a, fun h => ?_⟩
  choose y hy using h
  have hx : x = ∑ j, y j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hy]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `(mem_colLat_one _).2 fun a => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Submodule.mem_one.1 (hx a (Set.mem_univ a))`.

Use `⟨⟨emb t (x a), ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `map_isIntegral_int (emb t) y.isIntegral_coe`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `Submodule.subset_span ⟨fun a => if a = j then 1 else 0, fun a _ => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : a = j`. Conclude with `Submodule.mem_one.2 ⟨1, by simp [h]⟩`. Conclude with `Submodule.mem_one.2 ⟨0, by simp [h]⟩`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `by_cases h : a = j <;> simp [h, Matrix.one_apply]`.
-/
theorem tauLat_stdLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {Ix : Type} {n : ℕ}
    (emb : Ix → E →+* K) (t : Ix) : tauLat emb t (stdLat E n) = colLat (1 : GL (Fin n) K) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx a (Set.mem_univ a))
    refine ⟨⟨emb t (x a), ?_⟩, rfl⟩
    rw [← hy]
    exact map_isIntegral_int (emb t) y.isIntegral_coe
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨fun a => if a = j then 1 else 0, fun a _ => ?_, ?_⟩
    · by_cases h : a = j
      · exact Submodule.mem_one.2 ⟨1, by simp [h]⟩
      · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩
    · funext a
      by_cases h : a = j <;> simp [h, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(mem_colLat_one _).2 fun a => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Submodule.mem_one.1 (h _ (Submodule.subset_span ⟨a, rfl⟩))`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[hy]`. Simplify using `[dotProduct, Matrix.one_apply]`. Introduce `h x hx choose y hy using (mem_colLat_one _).1 h choose z hz using (mem_colLat_one _).1 hx`. Use `Submodule.mem_one.2 ⟨∑ a, y a * z a, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sum, map_mul, hy, hz, dotProduct]`.
-/
theorem dualFr_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} :
    dualFr (colLat (1 : GL (Fin n) K)) = colLat (1 : GL (Fin n) K) := by
  ext φ
  constructor
  · intro h
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (h _ (Submodule.subset_span ⟨a, rfl⟩))
    refine ⟨y, ?_⟩
    rw [hy]
    simp [dotProduct, Matrix.one_apply]
  · intro h x hx
    choose y hy using (mem_colLat_one _).1 h
    choose z hz using (mem_colLat_one _).1 hx
    refine Submodule.mem_one.2 ⟨∑ a, y a * z a, ?_⟩
    simp only [map_sum, map_mul, hy, hz, dotProduct]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Set `I : Ideal (𝓞 K)` to `T.comap (LinearMap.toSpanSingleton (𝓞 K) W x)`. Establish `hI : I ≠ ⊤`. Introduce `hI`. Establish `h1 : (1 : 𝓞 K) ∈ I` using `hI ▸ Submodule.mem_top`.

Conclude with `hx (by simpa [I] using h1)`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨s, hs, hsx⟩` from `h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩`. Conclude with `hs (hIm (show s ∈ I from hsx))`.
-/
theorem mem_of_forall_locP {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module (𝓞 K) W]
    (T : Submodule (𝓞 K) W) (x : W) (h : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : x ∈ T := by
  by_contra hx
  let I : Ideal (𝓞 K) := T.comap (LinearMap.toSpanSingleton (𝓞 K) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := hI ▸ Submodule.mem_top
    exact hx (by simpa [I] using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
  exact hs (hIm (show s ∈ I from hsx))

/- English proof (translation)
Simplify using `[actP, detTwK_one, trAct_one]`.
-/
theorem polyAction_one₂ {K Ix : Type} [Field K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) (F : Pol K Ix n) :
    actP lam 1 F = F := by
  simp [actP, detTwK_one, trAct_one]

/- English proof (translation)
Use extensionality with `F`. Prove the components needed by the constructor for the conclusion. Introduce `hF`. Use `mem_of_forall_locP _ _ fun w => ?_` and prove the remaining obligations. Establish `h` using `nabP_colLat_le lam 1 w hF`.

Rewrite `h` using `[inv_one, polyAction_one₂]`. Then use the resulting hypothesis. Introduce `hF`. Simplify using `only [nabP, transLat, Submodule.mem_iInf]`. Introduce `w B hB`. Conclude with `GlobalTheory.NabStab.polyAction_mem_locP_nabStd K Ix n lam w B⁻¹ (fun t => GlobalTheory.NabStab.isBasisAt_inv w (B t) (hB t)) F ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩`.
-/
theorem nabP_colLat_one {K Ix : Type} [Field K] [NumberField K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) :
    nabP lam (fun _ => colLat (1 : GL (Fin n) K)) = nabStd K lam := by
  ext F
  constructor
  · intro hF
    refine mem_of_forall_locP _ _ fun w => ?_
    have h := nabP_colLat_le lam 1 w hF
    rwa [inv_one, polyAction_one₂] at h
  · intro hF
    simp only [nabP, transLat, Submodule.mem_iInf]
    intro w B hB
    exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd K Ix n lam w B⁻¹ (fun t => GlobalTheory.NabStab.isBasisAt_inv w (B t) (hB t)) F
      ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

/- English proof (translation)
Unfold `extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, RingHom.map_det]`. Establish `h : ∀ (k : ℕ) (h1 h2 : k ≤ n), (eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1`.

Introduce `k h1 h2`. Use extensionality with `p q`. Simplify using `[Matrix.one_apply, Fin.ext_iff]`. Rewrite using `[h, Matrix.det_one, one_pow]`.
-/
theorem eval_extremal {R : Type} [CommRing R] {n : ℕ} (lam : DomWeight n) :
    eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0) (extremal R n lam) = 1 := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  have h : ∀ (k : ℕ) (h1 h2 : k ≤ n),
      (eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix
        (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [h, Matrix.det_one, one_pow]

/- English proof (translation)
Introduce `E K _ _ _ _ Ix _ n emb lam`. Use `⟨fun F => ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Unfold `nabAtr nabK`. Simplify using `only [tauLat_stdLat, dualFr_colLat_one, nabP_colLat_one]`. Both sides reduce to the same expression.

Use `Submodule.subset_span ⟨fun t => extremal K n (lam t), fun t => ?_, rfl⟩` and prove the remaining obligations. Conclude with `⟨extremal (𝓞 K) n (lam t), Formalism.GradedWeylDivisibility.hwMem (𝓞 K) n n le_rfl _ (natW_antitone (lam t)), map_extremal _ n (lam t)⟩`. Take `⟨Q, hQ⟩` from `GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hx`. Set `e : ∀ (R : Type) [CommRing R], Ix × Fin n × Fin n → R` to `fun R _ v => if v.2.1 = v.2.2 then 1 else 0`. Use `⟨eval (e (𝓞 K)) Q, ?_⟩` and prove the remaining obligations.

Establish `h1 : eval (e K) (ten fun t => extremal K n (lam t)) = 1`. Unfold `ten`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun t _ => ?_` and prove the remaining obligations. Unfold `Formalism.GradedWeylDivisibility.blockEmb`.

Rewrite using `[eval_rename]`. Conclude with `eval_extremal (lam t)`. Establish `h2 : eval (e K) (map (algebraMap (𝓞 K) K) Q) = algebraMap (𝓞 K) K (eval (e (𝓞 K)) Q)`. Establish `h3 : e K = algebraMap (𝓞 K) K ∘ e (𝓞 K)`. Use function extensionality and compare the values at `v`.

Apply the tactic sequence `by_cases h : v.2.1 = v.2.2 <;> simp [e, h]`. Rewrite using `[h3, ← map_eval]`. Establish `h4` using `congrArg (eval (e K)) hQ`. Rewrite `h4` using `[GlobalTheory.NabStab.toK_apply, h2, smul_eval, h1, mul_one]`. Conclude with `h4.symm`.
-/
theorem nabAtr_stdLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ) (emb : Ix → E →+* K) (lam : Ix → DomWeight n), (∀ F : VV K lam, F ∈ nabAtr emb lam (stdLat E n) ↔ (F : Pol K Ix n) ∈ nabStd K lam) ∧ (ten fun t => extremal K n (lam t)) ∈ nabStd K lam ∧ ∀ x : K, x • (ten fun t => extremal K n (lam t)) ∈ nabStd K lam → ∃ o : 𝓞 K, x = (o : K) := by
  intro E K _ _ _ _ Ix _ n emb lam
  refine ⟨fun F => ?_, ?_, fun x hx => ?_⟩
  · unfold nabAtr nabK
    simp only [tauLat_stdLat, dualFr_colLat_one, nabP_colLat_one]
    rfl
  · refine Submodule.subset_span ⟨fun t => extremal K n (lam t), fun t => ?_, rfl⟩
    exact ⟨extremal (𝓞 K) n (lam t), Formalism.GradedWeylDivisibility.hwMem (𝓞 K) n n le_rfl _ (natW_antitone (lam t)),
      map_extremal _ n (lam t)⟩
  · obtain ⟨Q, hQ⟩ := GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hx
    let e : ∀ (R : Type) [CommRing R], Ix × Fin n × Fin n → R := fun R _ v => if v.2.1 = v.2.2 then 1 else 0
    refine ⟨eval (e (𝓞 K)) Q, ?_⟩
    have h1 : eval (e K) (ten fun t => extremal K n (lam t)) = 1 := by
      unfold ten
      rw [map_prod]
      refine Finset.prod_eq_one fun t _ => ?_
      unfold Formalism.GradedWeylDivisibility.blockEmb
      rw [eval_rename]
      exact eval_extremal (lam t)
    have h2 : eval (e K) (map (algebraMap (𝓞 K) K) Q) = algebraMap (𝓞 K) K (eval (e (𝓞 K)) Q) := by
      have h3 : e K = algebraMap (𝓞 K) K ∘ e (𝓞 K) := by
        funext v
        by_cases h : v.2.1 = v.2.2 <;> simp [e, h]
      rw [h3, ← map_eval]
    have h4 := congrArg (eval (e K)) hQ
    rw [GlobalTheory.NabStab.toK_apply, h2, smul_eval, h1, mul_one] at h4
    exact h4.symm

end GlobalTheory.StdNab
