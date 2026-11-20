import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.NormAssemble

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, Polynomial.map_add, map_add, ← hp, ← hq]`. Use extensionality with `i j`. Simplify using `[cT]`.

Consider the case `monomial k a`. Rewrite using `[Polynomial.map_monomial, aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]`. Establish `hp : ((M ^ k).map σ)ᵀ = ((M.map σ)ᵀ) ^ k`. Rewrite using `[← Matrix.transpose_pow, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]`. Simplify using `only [cT, Matrix.map_smul', hp]`.

Use extensionality with `i j`. Simplify using `[Matrix.transpose_smul]`. Use `left`. Rewrite using `[← hp]`. Both sides reduce to the same expression.
-/
theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval M p) = aeval (cT σ M) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]
    have hp : ((M ^ k).map σ)ᵀ = ((M.map σ)ᵀ) ^ k := by
      rw [← Matrix.transpose_pow, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    simp only [cT, Matrix.map_smul', hp]
    ext i j; simp [Matrix.transpose_smul]
    left; rw [← hp]; rfl

def toFld {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r) : E[X] →+* Fld Q :=
  AdjoinRoot.mk Q.1

def sr {E : Type} [Field E] [NumberField E] [IsCMField E] (Q : E[X]) (h : IsSelfRecip E Q.natDegree Q) :
    SelfRecip E Q.natDegree := ⟨Q, h⟩

/- English proof (translation)
Introduce `E _ _ _ n γ hγ hP hself m hy`. Use `set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ`. Use `set P := γ.val.charpoly with hPdef`. Establish `hPsep : P.Separable` using `hP.2.2.1`. Establish `hP0 : P ≠ 0` using `hP.1.ne_zero`.

Establish `hXP : IsCoprime X P`. Rewrite using `[Polynomial.irreducible_X.coprime_iff_not_dvd]`. Introduce `hX`. Conclude with `(hself X monic_X irreducible_X hX).2.2.2.1 (by simp)`. Take `⟨a, b, hab⟩` from `hXP`.

Establish `hCH : aeval γ.val P = 0` using `Matrix.aeval_self_charpoly _`. Establish `haγ : aeval γ.val a * γ.val = 1`. Use `congrArg (aeval γ.val) hab` as an intermediate fact. Simplify `this` using `[hCH]`. Establish `hu : cT σ γ.val * γ.val = 1`.

Establish `: cT σ γ.val * 1 * γ.val = 1` using `hγ`. Simplify using `using this`. Establish `h1 : γ.val * (γ⁻¹).val = 1` using `Units.mul_inv γ`. Establish `hcTa : cT σ γ.val = aeval γ.val a`. Combine the equalities or inequalities in the displayed calculation.

Use `set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS`. Establish `hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P`. Introduce `Q hQ`. Rewrite `hQ` using `[hS, Multiset.mem_toFinset]`. Establish `hirr` using `UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ`.

Use `⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩` and prove the remaining obligations. Establish `hn` using `UniqueFactorizationMonoid.normalize_normalized_factor Q hQ`. Rewrite using `[← hn]`. Conclude with `Polynomial.monic_normalize hirr.ne_zero`. Establish `hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q)`.

Introduce `Q hQ Q' hQ' hne`. Simplify using `only [Function.onFun]`. Rewrite using `[(hmem Q hQ).2.1.coprime_iff_not_dvd]`. Introduce `hd`. Conclude with `hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1 ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))`.

Establish `hsr : ∀ Q : S, IsSelfRecip E Q.1.natDegree Q.1` using `fun Q => hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2`. Establish `hloc : ∀ Q : S, ∃ fQ : E[X], toFld (sr Q.1 (hsr Q)) fQ * invol (sr Q.1 (hsr Q)) (toFld _ fQ) = toFld _ m`. Introduce `Q`. Take `⟨y, hy'⟩` from `hy _ (sr Q.1 (hsr Q)) (hmem Q.1 Q.2).2.2`. Take `⟨fQ, rfl⟩` from `AdjoinRoot.mk_surjective y`.

Conclude with `⟨fQ, hy'⟩`. Use `choose fQ hfQ using hloc`. Establish `hcop : Pairwise (Function.onFun IsCoprime fun Q : S => Ideal.span {Q.1})`. Introduce `Q Q' hne`. Simplify using `only [Function.onFun]`.

Rewrite using `[Ideal.isCoprime_span_singleton_iff]`. Conclude with `hcopS Q.2 Q'.2 (fun h => hne (Subtype.ext h))`. Take `⟨q, hq⟩` from `Ideal.quotientInfToPiQuotient_surj hcop (fun Q => Ideal.Quotient.mk (Ideal.span {Q.1}) (fQ Q))`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hf : ∀ Q : S, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 (fQ Q)`.

Introduce `Q`. Use `congrFun hq Q` as an intermediate fact. Rewrite `this` using `[Ideal.quotientInfToPiQuotient_mk]`. Conclude with `this`. Use `set g := (f.map σ).comp a * f - m with hg`.

Establish `hdiv : ∀ Q ∈ S, Q ∣ g`. Introduce `Q hQ`. Set `Q' : SelfRecip E Q.natDegree` to `sr Q (hsr ⟨Q, hQ⟩)`. Establish `hQP` using `(hmem Q hQ).2.2`. Establish `ha : toFld Q' a = (alpha Q')⁻¹`.

Use `congrArg (toFld Q') hab` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_mul, map_one]`. Establish `hX : toFld Q' X = alpha Q'` using `AdjoinRoot.mk_X`. Establish `hPz : toFld Q' P = 0` using `AdjoinRoot.mk_eq_zero.2 hQP`. Rewrite `this` using `[hX, hPz, mul_zero, add_zero]`.

Conclude with `eq_inv_of_mul_eq_one_left this`. Establish `hc : toFld Q' ((f.map σ).comp a) = invol Q' (toFld Q' f)`. Express the relevant statement in the definitionally equal form `AdjoinRoot.mk Q'.1 ((f.map σ).comp a) = AdjoinRoot.lift _ _ (eval₂_conj_inv_root Q') (AdjoinRoot.mk Q'.1 f)`. Rewrite using `[← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_def, eval₂_map]`. Express the relevant statement in the definitionally equal form `eval₂ _ (toFld Q' a) f = _`.

Rewrite using `[ha]`. Both sides reduce to the same expression. Establish `hfQ' : toFld Q' (fQ ⟨Q, hQ⟩) * invol Q' (toFld Q' (fQ ⟨Q, hQ⟩)) = toFld Q' m` using `hfQ ⟨Q, hQ⟩`. Establish `hf' : toFld Q' f = toFld Q' (fQ ⟨Q, hQ⟩)` using `hf ⟨Q, hQ⟩`. Establish `: toFld Q' g = 0`.

Rewrite using `[hg, map_sub, map_mul, hc, hf', mul_comm, hfQ', sub_self]`. Conclude with `AdjoinRoot.mk_eq_zero.1 this`. Establish `hprod : (∏ Q ∈ S, Q) ∣ g` using `Finset.prod_dvd_of_coprime hcopS hdiv`. Establish `hassoc : Associated (∏ Q ∈ S, Q) P`. Establish `hnd` using `(UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree`.

Rewrite using `[Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']`. Conclude with `UniqueFactorizationMonoid.prod_normalizedFactors hP0`. Establish `hPg : P ∣ g` using `hassoc.symm.dvd.trans hprod`. Take `⟨k, hk⟩` from `hPg`. Establish `hg0 : aeval γ.val g = 0` using `by rw [hk, map_mul, hCH, zero_mul]`.

Use `⟨aeval γ.val f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show γ.val * aeval γ.val f = aeval γ.val (X * f) by simp, show aeval γ.val f * γ.val = aeval γ.val (f * X) by simp, mul_comm]`. Rewrite using `[cT_aeval, hcTa, ← aeval_comp, ← map_mul]`. Rewrite `hg0` using `[hg, map_sub]`. Conclude with `sub_eq_zero.1 hg0`.
-/
theorem exists_norm_of_factors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → (∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q)) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = aeval γ.val m := by
  intro E _ _ _ n γ hγ hP hself m hy
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  set P := γ.val.charpoly with hPdef
  have hPsep : P.Separable := hP.2.2.1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  have hCH : aeval γ.val P = 0 := Matrix.aeval_self_charpoly _
  have haγ : aeval γ.val a * γ.val = 1 := by
    have := congrArg (aeval γ.val) hab
    simpa [hCH] using this
  have hu : cT σ γ.val * γ.val = 1 := by
    have : cT σ γ.val * 1 * γ.val = 1 := hγ
    simpa using this
  have h1 : γ.val * (γ⁻¹).val = 1 := Units.mul_inv γ
  have hcTa : cT σ γ.val = aeval γ.val a := by
    calc cT σ γ.val = cT σ γ.val * γ.val * (γ⁻¹).val := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = aeval γ.val a * γ.val * (γ⁻¹).val := by rw [hu, haγ]
      _ = aeval γ.val a := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hsr : ∀ Q : S, IsSelfRecip E Q.1.natDegree Q.1 := fun Q =>
    hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2
  have hloc : ∀ Q : S, ∃ fQ : E[X], toFld (sr Q.1 (hsr Q)) fQ *
      invol (sr Q.1 (hsr Q)) (toFld _ fQ) = toFld _ m := by
    intro Q
    obtain ⟨y, hy'⟩ := hy _ (sr Q.1 (hsr Q)) (hmem Q.1 Q.2).2.2
    obtain ⟨fQ, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨fQ, hy'⟩
  choose fQ hfQ using hloc
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : S => Ideal.span {Q.1}) := by
    intro Q Q' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcopS Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun Q => Ideal.Quotient.mk (Ideal.span {Q.1}) (fQ Q))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : ∀ Q : S, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 (fQ Q) := by
    intro Q
    have := congrFun hq Q
    rw [Ideal.quotientInfToPiQuotient_mk] at this
    exact this
  set g := (f.map σ).comp a * f - m with hg
  have hdiv : ∀ Q ∈ S, Q ∣ g := by
    intro Q hQ
    let Q' : SelfRecip E Q.natDegree := sr Q (hsr ⟨Q, hQ⟩)
    have hQP := (hmem Q hQ).2.2
    have ha : toFld Q' a = (alpha Q')⁻¹ := by
      have := congrArg (toFld Q') hab
      rw [map_add, map_mul, map_mul, map_one] at this
      have hX : toFld Q' X = alpha Q' := AdjoinRoot.mk_X
      have hPz : toFld Q' P = 0 := AdjoinRoot.mk_eq_zero.2 hQP
      rw [hX, hPz, mul_zero, add_zero] at this
      exact eq_inv_of_mul_eq_one_left this
    have hc : toFld Q' ((f.map σ).comp a) = invol Q' (toFld Q' f) := by
      change AdjoinRoot.mk Q'.1 ((f.map σ).comp a) = AdjoinRoot.lift _ _ (eval₂_conj_inv_root Q') (AdjoinRoot.mk Q'.1 f)
      rw [← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_def, eval₂_map]
      change eval₂ _ (toFld Q' a) f = _
      rw [ha]; rfl
    have hfQ' : toFld Q' (fQ ⟨Q, hQ⟩) * invol Q' (toFld Q' (fQ ⟨Q, hQ⟩)) = toFld Q' m := hfQ ⟨Q, hQ⟩
    have hf' : toFld Q' f = toFld Q' (fQ ⟨Q, hQ⟩) := hf ⟨Q, hQ⟩
    have : toFld Q' g = 0 := by
      rw [hg, map_sub, map_mul, hc, hf', mul_comm, hfQ', sub_self]
    exact AdjoinRoot.mk_eq_zero.1 this
  have hprod : (∏ Q ∈ S, Q) ∣ g := Finset.prod_dvd_of_coprime hcopS hdiv
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hPg : P ∣ g := hassoc.symm.dvd.trans hprod
  obtain ⟨k, hk⟩ := hPg
  have hg0 : aeval γ.val g = 0 := by rw [hk, map_mul, hCH, zero_mul]
  refine ⟨aeval γ.val f, ?_, ?_⟩
  · rw [show γ.val * aeval γ.val f = aeval γ.val (X * f) by simp,
      show aeval γ.val f * γ.val = aeval γ.val (f * X) by simp, mul_comm]
  · rw [cT_aeval, hcTa, ← aeval_comp, ← map_mul]
    rw [hg, map_sub] at hg0
    exact sub_eq_zero.1 hg0

end GlobalTheory.NormAssemble
