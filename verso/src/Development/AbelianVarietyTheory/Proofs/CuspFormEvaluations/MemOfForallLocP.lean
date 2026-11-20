import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.StdNab

open IsDedekindDomain

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
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
Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules.
-/
theorem polyAction_one₂ {K Ix : Type} [Field K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) (F : Pol K Ix n) :
    actP lam 1 F = F := by
  simp [actP, detTwK_one, trAct_one]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
