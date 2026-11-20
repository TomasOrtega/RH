import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteOfCommuteCyclicMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialProjectionInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveIdempotentsSeparatingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLatticeDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvolutionAdjoinNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeIsotropicIffInvolutionMulZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNegStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeMulIdempotentRangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnLambdaSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerCompactReductionStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Proceed by induction on `h using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq, Matrix.transpose_add]`. Consider the case `monomial k a => simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_pow]`.
-/
theorem aeval_transpose {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (h : K[X]) :
    aeval γᵀ h = (aeval γ h)ᵀ := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.transpose_add]
  | monomial k a => simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_pow]

section Lemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.commute_polynomial_of_mem_centralizer E n d t ht e he`.
-/
theorem commute_of_mem (d : GL (Fin n) E) (t : GA E n) (ht : t ∈ adCent d) (e : Matrix (Fin n) (Fin n) E)
    (he : IsPol (nrm d).val e) : t.val * rm e = rm e * t.val :=
  GlobalTheory.T.commute_polynomial_of_mem_centralizer E n d t ht e he

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.T.exists_cyclic_vector_of_separable E n (nrm d).val hd`. Establish `hγ : IsPol (nrm d).val (nrm d).val` using `⟨X, (aeval_X _).symm⟩`. Conclude with `Units.ext (GlobalTheory.T.commute_of_commute_cyclic_matrix E (Ad E) n (nrm d).val v hv t.val t'.val (commute_of_mem d t ht _ hγ) (commute_of_mem d t' ht' _ hγ))`.
-/
theorem adCent_comm (d : GL (Fin n) E) (hd : IsRegD d) (t t' : GA E n) (ht : t ∈ adCent d) (ht' : t' ∈ adCent d) :
    t * t' = t' * t := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_cyclic_vector_of_separable E n (nrm d).val hd
  have hγ : IsPol (nrm d).val (nrm d).val := ⟨X, (aeval_X _).symm⟩
  exact Units.ext (GlobalTheory.T.commute_of_commute_cyclic_matrix E (Ad E) n (nrm d).val v hv t.val t'.val
    (commute_of_mem d t ht _ hγ) (commute_of_mem d t' ht' _ hγ))

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.T.exists_cyclic_vector_of_separable K n γ hγ`. Conclude with `GlobalTheory.T.exists_polynomial_projection_invariant K n γ v hγ hv W hW`.
-/
theorem exists_idem' {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : γ.charpoly.Separable)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) :
    ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_cyclic_vector_of_separable K n γ hγ
  exact GlobalTheory.T.exists_polynomial_projection_invariant K n γ v hγ hv W hW

/- English proof (translation)
Take `⟨σ, hσ1, -⟩` from `GlobalTheory.T.exists_involution_adjoin_norm E n d`. Use `(σ ⟨x, (isPol_iff _ _).1 hx⟩).2` as an intermediate fact. Rewrite `this` using `[hσ1]`. Conclude with `(isPol_iff _ _).2 this`.
-/
theorem sg_pol (d : GL (Fin n) E) (x : Matrix (Fin n) (Fin n) E) (hx : IsPol (nrm d).val x) :
    IsPol (nrm d).val (sg d x) := by
  obtain ⟨σ, hσ1, -⟩ := GlobalTheory.T.exists_involution_adjoin_norm E n d
  have := (σ ⟨x, (isPol_iff _ _).1 hx⟩).2
  rw [hσ1] at this
  exact (isPol_iff _ _).2 this

/- English proof (translation)
Take `⟨σ, hσ1, hσ2⟩` from `GlobalTheory.T.exists_involution_adjoin_norm E n d`. Establish `hcomm : ∀ a b : Algebra.adjoin E {(nrm d).val}, a * b = b * a` using `fun a b => Subtype.ext (pol_comm _ _ _ ((isPol_iff _ _).2 a.2) ((isPol_iff _ _).2 b.2))`. Set `x : Algebra.adjoin E {(nrm d).val}` to `⟨e, (isPol_iff _ _).1 he.pol⟩`. Establish `hsx : ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d e` using `hσ1 x`. Establish `hxx : x * x = x` using `Subtype.ext he.idem`.

Take `⟨f, hf⟩` from `(isPol_iff _ _).2 (σ x).2`. Rewrite `hf` using `[hsx]`. Distinguish the cases in `h0 : aeval (nrm d).val f * e = 0`. Use `left`. Rewrite using `[hf, pol_comm _ e _ he.pol ⟨f, rfl⟩, h0]`.

Use `right`. Take `⟨h', hh⟩` from `he.inv f h0`. Establish `hsq : σ x * σ x = σ x` using `by rw [← map_mul, hxx]`. Establish `hq : sg d e * sg d e = sg d e`. Use `congrArg Subtype.val hsq` as an intermediate fact.

Rewrite `this` using `[Subalgebra.coe_mul, hsx]`. Then use the resulting hypothesis. Use `set q := aeval (nrm d).val f * e with hqdef`. Establish `hfe : aeval (nrm d).val f * e = sg d e * e` using `by rw [← hf]`. Establish `hcm : sg d e * e = e * sg d e` using `pol_comm _ _ _ (sg_pol d e he.pol) he.pol`. Establish `hqq : q * q = q`.

Rewrite using `[hqdef, hfe]`. Combine the equalities or inequalities in the displayed calculation. Establish `heq : e * q = q`. Rewrite using `[hqdef, hfe]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : e = q`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : x = σ x * x` using `Subtype.ext (by`. Rewrite using `[Subalgebra.coe_mul, hsx]`. Use `show e = sg d e * e`.

Rewrite using `[← hfe]`. Conclude with `h3)`. Establish `h2 : σ x = x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hsx, h2]`.
-/
theorem prim_dich (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (he : IsPrim (nrm d).val e) :
    e * sg d e = 0 ∨ sg d e = e := by
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.exists_involution_adjoin_norm E n d
  have hcomm : ∀ a b : Algebra.adjoin E {(nrm d).val}, a * b = b * a := fun a b =>
    Subtype.ext (pol_comm _ _ _ ((isPol_iff _ _).2 a.2) ((isPol_iff _ _).2 b.2))
  let x : Algebra.adjoin E {(nrm d).val} := ⟨e, (isPol_iff _ _).1 he.pol⟩
  have hsx : ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d e := hσ1 x
  have hxx : x * x = x := Subtype.ext he.idem
  obtain ⟨f, hf⟩ := (isPol_iff _ _).2 (σ x).2
  rw [hsx] at hf
  by_cases h0 : aeval (nrm d).val f * e = 0
  · left
    rw [hf, pol_comm _ e _ he.pol ⟨f, rfl⟩, h0]
  · right
    obtain ⟨h', hh⟩ := he.inv f h0
    have hsq : σ x * σ x = σ x := by rw [← map_mul, hxx]
    have hq : sg d e * sg d e = sg d e := by
      have := congrArg Subtype.val hsq
      rwa [Subalgebra.coe_mul, hsx] at this
    set q := aeval (nrm d).val f * e with hqdef
    have hfe : aeval (nrm d).val f * e = sg d e * e := by rw [← hf]
    have hcm : sg d e * e = e * sg d e := pol_comm _ _ _ (sg_pol d e he.pol) he.pol
    have hqq : q * q = q := by
      rw [hqdef, hfe]
      calc sg d e * e * (sg d e * e) = sg d e * (e * sg d e) * e := by simp only [mul_assoc]
        _ = sg d e * (sg d e * e) * e := by rw [hcm]
        _ = (sg d e * sg d e) * (e * e) := by simp only [mul_assoc]
        _ = sg d e * e := by rw [hq, he.idem]
    have heq : e * q = q := by
      rw [hqdef, hfe]
      calc e * (sg d e * e) = (e * sg d e) * e := by rw [mul_assoc]
        _ = (sg d e * e) * e := by rw [hcm]
        _ = sg d e * (e * e) := by rw [mul_assoc]
        _ = sg d e * e := by rw [he.idem]
    have h3 : e = q := by
      calc e = aeval (nrm d).val h' * q := hh.symm
        _ = aeval (nrm d).val h' * (q * q) := by rw [hqq]
        _ = (aeval (nrm d).val h' * q) * q := (mul_assoc _ _ _).symm
        _ = e * q := by rw [hh]
        _ = q := heq
    have h1 : x = σ x * x := Subtype.ext (by
      rw [Subalgebra.coe_mul, hsx]
      show e = sg d e * e
      rw [← hfe]; exact h3)
    have h2 : σ x = x := by
      calc σ x = σ (σ x * x) := by rw [← h1]
        _ = σ (σ x) * σ x := map_mul _ _ _
        _ = x * σ x := by rw [hσ2]
        _ = σ x * x := hcomm _ _
        _ = x := h1.symm
    rw [← hsx, h2]

/- English proof (translation)
The claim follows from `GlobalTheory.T.lambda_involution_neg E n d e he2 t ht (commute_of_mem d t ht e he) (commute_of_mem d t ht _ (sg_pol d e he))`.
-/
theorem lam_sg (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (he : IsPol (nrm d).val e) (he2 : e * e = e) (t : GA E n)
    (ht : t ∈ adCent d) : lam (sg d e) t = - lam e t :=
  GlobalTheory.T.lambda_involution_neg E n d e he2 t ht (commute_of_mem d t ht e he) (commute_of_mem d t ht _ (sg_pol d e he))

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.T.exists_cyclic_vector_of_separable K n γᵀ (by rwa [Matrix.charpoly_transpose])`. Use `GlobalTheory.T.exists_epsilon_centralizer_bound K n γ v (fun y => ?_) e he c hc` and prove the remaining obligations. Take `⟨h, hh⟩` from `hv y`. Conclude with `⟨h, by rw [hh, aeval_transpose, Matrix.mulVec_transpose]⟩`.
-/
theorem height_lb {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : γ.charpoly.Separable)
    (e : Matrix (Fin n) (Fin n) K) (he : IsPrim γ e) {c : ℝ} (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n,
      g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val →
      ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det →
      c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 →
        ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_cyclic_vector_of_separable K n γᵀ (by rwa [Matrix.charpoly_transpose])
  refine GlobalTheory.T.exists_epsilon_centralizer_bound K n γ v (fun y => ?_) e he c hc
  obtain ⟨h, hh⟩ := hv y
  exact ⟨h, by rw [hh, aeval_transpose, Matrix.mulVec_transpose]⟩

end Lemmas

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_pos, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨ε, h0, h1⟩` from `ih fun b hb => hf b (Finset.mem_insert_of_mem hb)`. Use `⟨min ε (f a), lt_min h0 (hf a (Finset.mem_insert_self _ _)), fun b hb => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hb with rfl | hb` into its components or cases. Conclude with `min_le_right _ _`. Conclude with `(min_le_left _ _).trans (h1 b hb)`.
-/
theorem exists_pos_le {α : Type} (S : Finset α) (f : α → ℝ) (hf : ∀ a ∈ S, 0 < f a) : ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ S, ε ≤ f a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, h0, h1⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    refine ⟨min ε (f a), lt_min h0 (hf a (Finset.mem_insert_self _ _)), fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h1 b hb)

/- English proof (translation)
Introduce `hDA E _ _ _ n d m Wof hIso hU h0 hMeet hLe hReg`. Use `set γ : Matrix (Fin n) (Fin n) E := (nrm d).val with hγdef`. Establish `hsep : γ.charpoly.Separable` using `hReg`. Use `⟨fun t ht t' ht' => adCent_comm d hReg t t' ht ht', ?_⟩` and prove the remaining obligations. Establish `hst : ∀ e, (Wof e).map (Matrix.toLin' γ) ≤ Wof e` using `fun e => (hIso e).1.le`.

Use `choose π hπp hπi hπr using fun e => exists_idem' γ hsep (Wof e) (hst e)`. Establish `hcomm : ∀ x y : Algebra.adjoin E {γ}, x * y = y * x`. Introduce `x y`. Conclude with `Subtype.ext (pol_comm γ _ _ ((isPol_iff _ _).2 x.2) ((isPol_iff _ _).2 y.2))`. Take `⟨σ, hσ1, hσ2⟩` from `GlobalTheory.T.exists_involution_adjoin_norm E n d`.

Set `P : (Fin m → SignType) → Algebra.adjoin E {γ}` to `fun e => ⟨π e, (isPol_iff _ _).1 (hπp e)⟩`. Establish `hPv : ∀ e, (P e : Matrix (Fin n) (Fin n) E) = π e` using `fun _ => rfl`. Establish `hsgpol : ∀ x : Matrix (Fin n) (Fin n) E, IsPol γ x → IsPol γ (sg d x)` using `fun x hx => by`. Use `(σ ⟨x, (isPol_iff _ _).1 hx⟩).2` as an intermediate fact. Rewrite `this` using `[hσ1]`.

Conclude with `(isPol_iff _ _).2 this`. Establish `hisoπ : ∀ e, sg d (π e) * π e = 0` using `fun e => (GlobalTheory.T.range_isotropic_iff_involution_mul_zero E n d (π e)).1 (by rw [hπr e]; exact (hIso e).2)`. Establish `hfind : ∀ p : Matrix (Fin n) (Fin n) E, IsPol γ p → p * p = p → sg d p * p = 0 → ∃ e, π e = p`. Introduce `p hp hp2 hp3`. Establish `hiso : IsoStab d (LinearMap.range (Matrix.toLin' p))` using `⟨img_of_pol (nrm d) p hp, (GlobalTheory.T.range_isotropic_iff_involution_mul_zero E n d p).2 hp3⟩`.

Take `⟨e, he, -⟩` from `hU _ hiso`. Use `⟨e, (idem_facts γ _ _ (hπp e) hp (hπi e) hp2).2.1 ?_⟩` and prove the remaining obligations. Rewrite using `[hπr e, he]`. Establish `hmeetπ : ∀ e e', π (sMeet e e') = π e * π e'`. Introduce `e e'`.

Establish `hpol : IsPol γ (π e * π e')` using `(isPol_iff _ _).2 (mul_mem ((isPol_iff _ _).1 (hπp e)) ((isPol_iff _ _).1 (hπp e')))`. Establish `hc'` using `pol_comm γ _ _ (hπp e) (hπp e')`. Establish `hid : (π e * π e') * (π e * π e') = π e * π e'`. Combine the equalities or inequalities in the displayed calculation. Use `(idem_facts γ _ _ (hπp _) hpol (hπi _) hid).2.1 ?_` and prove the remaining obligations.

Rewrite using `[(idem_facts γ _ _ (hπp e) (hπp e') (hπi e) (hπi e')).2.2, hπr, hπr, hπr, hMeet]`. Establish `hc` using `GlobalTheory.T.idempotent_lattice_decomposition _ hcomm σ hσ2 m P (fun e => Subtype.ext (hπi e)) (fun e => by`. Rewrite using `[hcomm]`. Conclude with `Subtype.ext (by rw [Subalgebra.coe_mul, hσ1]; exact hisoπ e))`. Use the proof step `(fun p hp1 hp2 => by`.

Take `⟨e, he⟩` from `hfind p.1 ((isPol_iff _ _).2 p.2) (congrArg Subtype.val hp1) (by`. Use `congrArg Subtype.val (hcomm p (σ p) ▸ hp2)` as an intermediate fact. Rewrite `this` using `[Subalgebra.coe_mul, hσ1]`. Conclude with `this)`. Conclude with `⟨e, Subtype.ext he⟩)`.

Use the proof step `(fun e e' h => by`. Establish `h1 : π e = π e'` using `congrArg Subtype.val h`. Establish `h2 : Wof e' = Wof e` using `by rw [← hπr e, ← hπr e', h1]`. Conclude with `(hU _ (hIso e)).unique rfl h2)`. Use the proof step `(Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `π 0 = 0`. Establish `h1 : LinearMap.range (Matrix.toLin' (π 0)) = ⊥` using `by rw [hπr 0, h0]`. Establish `h2` using `LinearMap.range_eq_bot.1 h1`. Conclude with `Matrix.toLin'.injective (by rw [h2, map_zero])))`. Use the proof step `(fun e e' => Subtype.ext (hmeetπ e e'))`.

Use the proof step `(fun e e' h => Subtype.ext ((idem_facts γ _ _ (hπp e) (hπp e') (hπi e) (hπi e')).1 (by`. Rewrite using `[hπr, hπr]`. Conclude with `hLe e e' h)))`. Take `⟨hsum, hneg⟩` from `hc`. Establish `hsum' : ∀ e, π e = ∑ j, π (Pi.single j (e j))` using `fun e => by`.

Use `congrArg Subtype.val (hsum e)` as an intermediate fact. Rewrite `this` using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `this`. Establish `hneg' : ∀ j, π (Pi.single j (-1)) = sg d (π (Pi.single j 1))` using `fun j => by`. Use `congrArg Subtype.val (hneg j)` as an intermediate fact.

Rewrite `this` using `[hσ1]`. Conclude with `this`. Establish `hcm : ∀ t ∈ adCent d, ∀ e, t.val * rm (π e) = rm (π e) * t.val` using `fun t ht e => commute_of_mem d t ht _ (hπp e)`. Set `a : GA E n → (Fin m → ℝ)` to `fun t j => lam (π (Pi.single j 1)) t`. Establish `hπ0 : π 0 = 0`.

Establish `h1 : LinearMap.range (Matrix.toLin' (π 0)) = ⊥` using `by rw [hπr 0, h0]`. Establish `h2` using `LinearMap.range_eq_bot.1 h1`. Conclude with `Matrix.toLin'.injective (by rw [h2, map_zero])`. Establish `hsign : ∀ t ∈ adCent d, ∀ e, lam (π e) t = sdot e (a t)`. Introduce `t ht e`.

Establish `horth : ∀ (j k : Fin m) (x y : SignType), j ≠ k → π (Pi.single j x) * π (Pi.single k y) = 0`. Introduce `j k x y hjk`. Rewrite using `[← hmeetπ]`. Establish `h1 : sMeet (Pi.single j x : Fin m → SignType) (Pi.single k y) = 0`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hx : x = 0`. Simplify using `[sMeet, Pi.single_apply, hjk, hx]`. Simplify using `[sMeet, Pi.single_apply, hjk, hx]`.

Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using `[sMeet, Pi.single_apply, hij]`. Simplify using `[sMeet, Pi.single_apply, hij, hik]`. Rewrite using `[h1, hπ0]`.

Rewrite using `[hsum' e, lam_sum Finset.univ _ (fun j _ => hπi _) (fun j _ k _ hjk => horth j k _ _ hjk) t (fun j _ => hcm t ht _), sdot]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: ∀ s : SignType, s = 0 ∨ s = -1 ∨ s = 1` using `by decide`. Break down `this (e j) with h | h | h` into its components or cases. Rewrite using `[h, Pi.single_zero, hπ0, lam_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[h, hneg', lam_sg d _ (hπp _) (hπi _) t ht]`. Simplify using `[a]`. Rewrite using `[h]`. Simplify using `[a]`.

Use `⟨a, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht x e`. Rewrite using `[← hsign t ht e, ← hπr e]`. Conclude with `GlobalTheory.T.degree_mul_idempotent_range E n hDA _ (hπi e) t x (hcm t ht e)`. Introduce `t ht t' ht'`.

Use function extensionality and compare the values at `j`. Conclude with `lam_mul _ (hπi _) t t' (hcm t ht _) (hcm t' ht' _)`. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Use function extensionality and compare the values at `j`. Conclude with `lam_rat _ (hπi _) r (hcm _ (GlobalTheory.CompanionTheory.RatDisc.ratCent_le d ⟨r, hr, rfl⟩) _)`.

Conclude with `continuousOn_pi.2 fun j => GlobalTheory.T.continuousOn_lambda_subgroup E n _ (hπi _) (GlobalTheory.T.log_abs_eq_log_idele_module E) (adCent d) fun t ht => hcm t ht _`. Introduce `M`. Take `⟨S, hS, hSx⟩` from `GlobalTheory.T.exists_primitive_idempotents_separating E n γ hsep`. Establish `hbd : ∀ e ∈ S, ∀ t ∈ adCent d, (∀ i, |a t i| ≤ M) → |lam e t| ≤ m * |M|`. Introduce `e he t ht hM`.

Establish `hp` using `hS e he`. Break down `prim_dich d e hp with h | h` into its components or cases. Establish `h' : sg d e * e = 0` using `by rw [pol_comm γ _ _ (hsgpol e hp.pol) hp.pol, h]`. Take `⟨s, rfl⟩` from `hfind e hp.pol hp.idem h'`. Rewrite using `[hsign t ht s, sdot]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[abs_mul]`. Establish `h1 : |((s i : SignType) : ℝ)| ≤ 1`. Establish `: ∀ s : SignType, s = 0 ∨ s = -1 ∨ s = 1` using `by decide`.

Apply the tactic sequence `rcases this (s i) with h | h | h <;> simp [h]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = m * |M| := by simp`. Establish `h1` using `lam_sg d e hp.pol hp.idem t ht`. Rewrite `h1` using `[h]`.

Establish `h2 : lam e t = 0` using `by linarith`. Rewrite using `[h2, abs_zero]`. Check the signs of the components of the expression. Establish `hex : ∀ e, ∃ ε : ℝ, 0 < ε ∧ (e ∈ S → ∀ (g : GroundTheory.Automorphic.AdelicGLn.AdelicGL E n), g.val * γ.map (algebraMap E (AdeleRing (𝓞 E) E)) = γ.map (algebraMap E (AdeleRing (𝓞 E) E)) * g.val → ∀ s : (AdeleRing (𝓞 E) E)ˣ, (s : AdeleRing (𝓞 E) E) = (1 + e.map (algebraMap E (Adel …`. Introduce `e`.

Distinguish the cases in `he : e ∈ S`. Take `⟨ε, h0, h1⟩` from `height_lb γ hsep e (hS e he) (Real.exp_pos (-(m * |M|)))`. Conclude with `⟨ε, h0, fun _ => h1⟩`. Conclude with `⟨1, one_pos, fun h => absurd h he⟩`. Use `choose f hf0 hf using hex`.

Take `⟨ε, hε, hεf⟩` from `exists_pos_le S f fun e _ => hf0 e`. Take `⟨C, hC, hred⟩` from `GroundTheory.Automorphic.Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := n) hε`. Take `⟨C', hC', hred'⟩` from `GlobalTheory.T.centralizer_compact_reduction E n d C hC`. Use `⟨C', hC', fun t ht hM => hred' t ht ?_⟩` and prove the remaining obligations. Establish `hnorm : t ∈ GroundTheory.Automorphic.Reduction.normOneGL E n`.

Rewrite using `[GroundTheory.Automorphic.Reduction.mem_normOneGL]`. Establish `h1` using `lam_sg d 1 ⟨1, by simp⟩ (by simp) t ht`. Establish `h2 : sg d (1 : Matrix (Fin n) (Fin n) E) = 1`. Simplify using `[sg, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `h1` using `[h2]`.

Establish `h3 : lam (1 : Matrix (Fin n) (Fin n) E) t = 0` using `by linarith`. Establish `h4 : lam (1 : Matrix (Fin n) (Fin n) E) t = logAbs ((GroundTheory.Automorphic.AdelicGLn.det E n t : (Ad E)ˣ) : Ad E)`. Simplify using `[lam, chi, rm, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `h3` using `[h4, GlobalTheory.T.log_abs_eq_log_idele_module E]`. Conclude with `Real.eq_one_of_pos_of_log_eq_zero (GroundTheory.Global.IdeleGroup.ideleModule E _).2 h3`.

Establish `hheight : ∀ x : Fin n → E, x ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height t x`. Introduce `x hx`. Take `⟨e, he, hxe⟩` from `hSx x hx`. Establish `hcm'` using `commute_of_mem d t ht e (hS e he).pol`. Establish `hu` using `chi_isUnit e (hS e he).idem t hcm'`.

Use `(hεf e he).trans (hf e he t (commute_of_mem d t ht γ ⟨X, (aeval_X γ).symm⟩) hu.unit hu.unit_spec ?_ x hxe)` and prove the remaining obligations. Establish `h1` using `abs_le.1 (hbd e he t ht hM)`. Establish `h2 : lam e t = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E hu.unit : ℝ)`. Rewrite using `[← GlobalTheory.T.log_abs_eq_log_idele_module E]`. Both sides reduce to the same expression.

Rewrite using `[← Real.exp_log (GroundTheory.Global.IdeleGroup.ideleModule E hu.unit).2, ← h2]`. Conclude with `Real.exp_le_exp.2 (by linarith [h1.1])`. Take `⟨_, ⟨r, rfl⟩, c, hc, rfl⟩` from `hred t hnorm hheight`. Conclude with `⟨ratGL E n r, ⟨r, rfl⟩, c, hc, rfl⟩`.
-/
theorem torusChar : DegAdelic → TorusChar := by
  intro hDA E _ _ _ n d m Wof hIso hU h0 hMeet hLe hReg
  classical
  set γ : Matrix (Fin n) (Fin n) E := (nrm d).val with hγdef
  have hsep : γ.charpoly.Separable := hReg
  refine ⟨fun t ht t' ht' => adCent_comm d hReg t t' ht ht', ?_⟩
  have hst : ∀ e, (Wof e).map (Matrix.toLin' γ) ≤ Wof e := fun e => (hIso e).1.le
  choose π hπp hπi hπr using fun e => exists_idem' γ hsep (Wof e) (hst e)
  have hcomm : ∀ x y : Algebra.adjoin E {γ}, x * y = y * x := by
    intro x y
    exact Subtype.ext (pol_comm γ _ _ ((isPol_iff _ _).2 x.2) ((isPol_iff _ _).2 y.2))
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.exists_involution_adjoin_norm E n d
  let P : (Fin m → SignType) → Algebra.adjoin E {γ} := fun e => ⟨π e, (isPol_iff _ _).1 (hπp e)⟩
  have hPv : ∀ e, (P e : Matrix (Fin n) (Fin n) E) = π e := fun _ => rfl
  have hsgpol : ∀ x : Matrix (Fin n) (Fin n) E, IsPol γ x → IsPol γ (sg d x) := fun x hx => by
    have := (σ ⟨x, (isPol_iff _ _).1 hx⟩).2
    rw [hσ1] at this
    exact (isPol_iff _ _).2 this
  have hisoπ : ∀ e, sg d (π e) * π e = 0 := fun e =>
    (GlobalTheory.T.range_isotropic_iff_involution_mul_zero E n d (π e)).1 (by rw [hπr e]; exact (hIso e).2)
  have hfind : ∀ p : Matrix (Fin n) (Fin n) E, IsPol γ p → p * p = p → sg d p * p = 0 → ∃ e, π e = p := by
    intro p hp hp2 hp3
    have hiso : IsoStab d (LinearMap.range (Matrix.toLin' p)) :=
      ⟨img_of_pol (nrm d) p hp, (GlobalTheory.T.range_isotropic_iff_involution_mul_zero E n d p).2 hp3⟩
    obtain ⟨e, he, -⟩ := hU _ hiso
    refine ⟨e, (idem_facts γ _ _ (hπp e) hp (hπi e) hp2).2.1 ?_⟩
    rw [hπr e, he]
  have hmeetπ : ∀ e e', π (sMeet e e') = π e * π e' := by
    intro e e'
    have hpol : IsPol γ (π e * π e') := (isPol_iff _ _).2 (mul_mem ((isPol_iff _ _).1 (hπp e)) ((isPol_iff _ _).1 (hπp e')))
    have hc' := pol_comm γ _ _ (hπp e) (hπp e')
    have hid : (π e * π e') * (π e * π e') = π e * π e' := by
      calc (π e * π e') * (π e * π e') = π e * (π e' * π e) * π e' := by simp only [mul_assoc]
        _ = π e * (π e * π e') * π e' := by rw [hc']
        _ = (π e * π e) * (π e' * π e') := by simp only [mul_assoc]
        _ = _ := by rw [hπi, hπi]
    refine (idem_facts γ _ _ (hπp _) hpol (hπi _) hid).2.1 ?_
    rw [(idem_facts γ _ _ (hπp e) (hπp e') (hπi e) (hπi e')).2.2, hπr, hπr, hπr, hMeet]
  have hc := GlobalTheory.T.idempotent_lattice_decomposition _ hcomm σ hσ2 m P (fun e => Subtype.ext (hπi e))
    (fun e => by
      rw [hcomm]
      exact Subtype.ext (by rw [Subalgebra.coe_mul, hσ1]; exact hisoπ e))
    (fun p hp1 hp2 => by
      obtain ⟨e, he⟩ := hfind p.1 ((isPol_iff _ _).2 p.2) (congrArg Subtype.val hp1) (by
        have := congrArg Subtype.val (hcomm p (σ p) ▸ hp2)
        rw [Subalgebra.coe_mul, hσ1] at this
        exact this)
      exact ⟨e, Subtype.ext he⟩)
    (fun e e' h => by
      have h1 : π e = π e' := congrArg Subtype.val h
      have h2 : Wof e' = Wof e := by rw [← hπr e, ← hπr e', h1]
      exact (hU _ (hIso e)).unique rfl h2)
    (Subtype.ext (by
      change π 0 = 0
      have h1 : LinearMap.range (Matrix.toLin' (π 0)) = ⊥ := by rw [hπr 0, h0]
      have h2 := LinearMap.range_eq_bot.1 h1
      exact Matrix.toLin'.injective (by rw [h2, map_zero])))
    (fun e e' => Subtype.ext (hmeetπ e e'))
    (fun e e' h => Subtype.ext ((idem_facts γ _ _ (hπp e) (hπp e') (hπi e) (hπi e')).1 (by
      rw [hπr, hπr]; exact hLe e e' h)))
  obtain ⟨hsum, hneg⟩ := hc
  have hsum' : ∀ e, π e = ∑ j, π (Pi.single j (e j)) := fun e => by
    have := congrArg Subtype.val (hsum e)
    rw [AddSubmonoidClass.coe_finset_sum] at this
    exact this
  have hneg' : ∀ j, π (Pi.single j (-1)) = sg d (π (Pi.single j 1)) := fun j => by
    have := congrArg Subtype.val (hneg j)
    rw [hσ1] at this
    exact this
  have hcm : ∀ t ∈ adCent d, ∀ e, t.val * rm (π e) = rm (π e) * t.val := fun t ht e =>
    commute_of_mem d t ht _ (hπp e)
  let a : GA E n → (Fin m → ℝ) := fun t j => lam (π (Pi.single j 1)) t
  have hπ0 : π 0 = 0 := by
    have h1 : LinearMap.range (Matrix.toLin' (π 0)) = ⊥ := by rw [hπr 0, h0]
    have h2 := LinearMap.range_eq_bot.1 h1
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hsign : ∀ t ∈ adCent d, ∀ e, lam (π e) t = sdot e (a t) := by
    intro t ht e
    have horth : ∀ (j k : Fin m) (x y : SignType), j ≠ k → π (Pi.single j x) * π (Pi.single k y) = 0 := by
      intro j k x y hjk
      rw [← hmeetπ]
      have h1 : sMeet (Pi.single j x : Fin m → SignType) (Pi.single k y) = 0 := by
        funext i
        by_cases hij : i = j
        · subst hij
          by_cases hx : x = 0
          · simp [sMeet, Pi.single_apply, hjk, hx]
          · simp [sMeet, Pi.single_apply, hjk, hx]
        · by_cases hik : i = k
          · subst hik
            simp [sMeet, Pi.single_apply, hij]
          · simp [sMeet, Pi.single_apply, hij, hik]
      rw [h1, hπ0]
    rw [hsum' e, lam_sum Finset.univ _ (fun j _ => hπi _) (fun j _ k _ hjk => horth j k _ _ hjk) t
      (fun j _ => hcm t ht _), sdot]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ s : SignType, s = 0 ∨ s = -1 ∨ s = 1 := by decide
    rcases this (e j) with h | h | h
    · rw [h, Pi.single_zero, hπ0, lam_zero]; simp
    · rw [h, hneg', lam_sg d _ (hπp _) (hπi _) t ht]; simp [a]
    · rw [h]; simp [a]
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x e
    rw [← hsign t ht e, ← hπr e]
    exact GlobalTheory.T.degree_mul_idempotent_range E n hDA _ (hπi e) t x (hcm t ht e)
  · intro t ht t' ht'
    funext j
    exact lam_mul _ (hπi _) t t' (hcm t ht _) (hcm t' ht' _)
  · rintro _ ⟨r, hr, rfl⟩
    funext j
    exact lam_rat _ (hπi _) r (hcm _ (GlobalTheory.CompanionTheory.RatDisc.ratCent_le d ⟨r, hr, rfl⟩) _)
  · exact continuousOn_pi.2 fun j => GlobalTheory.T.continuousOn_lambda_subgroup E n _ (hπi _) (GlobalTheory.T.log_abs_eq_log_idele_module E) (adCent d) fun t ht => hcm t ht _
  · intro M
    obtain ⟨S, hS, hSx⟩ := GlobalTheory.T.exists_primitive_idempotents_separating E n γ hsep
    have hbd : ∀ e ∈ S, ∀ t ∈ adCent d, (∀ i, |a t i| ≤ M) → |lam e t| ≤ m * |M| := by
      intro e he t ht hM
      have hp := hS e he
      rcases prim_dich d e hp with h | h
      · have h' : sg d e * e = 0 := by rw [pol_comm γ _ _ (hsgpol e hp.pol) hp.pol, h]
        obtain ⟨s, rfl⟩ := hfind e hp.pol hp.idem h'
        rw [hsign t ht s, sdot]
        calc |∑ i, ((s i : SignType) : ℝ) * a t i| ≤ ∑ i, |((s i : SignType) : ℝ) * a t i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin m, |M| := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            have h1 : |((s i : SignType) : ℝ)| ≤ 1 := by
              have : ∀ s : SignType, s = 0 ∨ s = -1 ∨ s = 1 := by decide
              rcases this (s i) with h | h | h <;> simp [h]
            calc _ ≤ 1 * |a t i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
              _ ≤ |M| := by rw [one_mul]; exact (hM i).trans (le_abs_self _)
          _ = m * |M| := by simp
      · have h1 := lam_sg d e hp.pol hp.idem t ht
        rw [h] at h1
        have h2 : lam e t = 0 := by linarith
        rw [h2, abs_zero]
        positivity
    have hex : ∀ e, ∃ ε : ℝ, 0 < ε ∧ (e ∈ S → ∀ (g : GroundTheory.Automorphic.AdelicGLn.AdelicGL E n),
        g.val * γ.map (algebraMap E (AdeleRing (𝓞 E) E)) = γ.map (algebraMap E (AdeleRing (𝓞 E) E)) * g.val →
        ∀ s : (AdeleRing (𝓞 E) E)ˣ, (s : AdeleRing (𝓞 E) E) = (1 + e.map (algebraMap E (AdeleRing (𝓞 E) E)) * (g.val - 1)).det →
        Real.exp (-(m * |M|)) ≤ (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) → ∀ x : Fin n → E, x ᵥ* e ≠ 0 →
          ε ≤ GroundTheory.Automorphic.Reduction.height g x) := by
      intro e
      by_cases he : e ∈ S
      · obtain ⟨ε, h0, h1⟩ := height_lb γ hsep e (hS e he) (Real.exp_pos (-(m * |M|)))
        exact ⟨ε, h0, fun _ => h1⟩
      · exact ⟨1, one_pos, fun h => absurd h he⟩
    choose f hf0 hf using hex
    obtain ⟨ε, hε, hεf⟩ := exists_pos_le S f fun e _ => hf0 e
    obtain ⟨C, hC, hred⟩ := GroundTheory.Automorphic.Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := n) hε
    obtain ⟨C', hC', hred'⟩ := GlobalTheory.T.centralizer_compact_reduction E n d C hC
    refine ⟨C', hC', fun t ht hM => hred' t ht ?_⟩
    have hnorm : t ∈ GroundTheory.Automorphic.Reduction.normOneGL E n := by
      rw [GroundTheory.Automorphic.Reduction.mem_normOneGL]
      have h1 := lam_sg d 1 ⟨1, by simp⟩ (by simp) t ht
      have h2 : sg d (1 : Matrix (Fin n) (Fin n) E) = 1 := by
        simp [sg, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [h2] at h1
      have h3 : lam (1 : Matrix (Fin n) (Fin n) E) t = 0 := by linarith
      have h4 : lam (1 : Matrix (Fin n) (Fin n) E) t = logAbs ((GroundTheory.Automorphic.AdelicGLn.det E n t : (Ad E)ˣ) : Ad E) := by
        simp [lam, chi, rm, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [h4, GlobalTheory.T.log_abs_eq_log_idele_module E] at h3
      exact Real.eq_one_of_pos_of_log_eq_zero (GroundTheory.Global.IdeleGroup.ideleModule E _).2 h3
    have hheight : ∀ x : Fin n → E, x ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height t x := by
      intro x hx
      obtain ⟨e, he, hxe⟩ := hSx x hx
      have hcm' := commute_of_mem d t ht e (hS e he).pol
      have hu := chi_isUnit e (hS e he).idem t hcm'
      refine (hεf e he).trans (hf e he t (commute_of_mem d t ht γ ⟨X, (aeval_X γ).symm⟩) hu.unit hu.unit_spec ?_ x hxe)
      have h1 := abs_le.1 (hbd e he t ht hM)
      have h2 : lam e t = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E hu.unit : ℝ) := by
        rw [← GlobalTheory.T.log_abs_eq_log_idele_module E]; rfl
      rw [← Real.exp_log (GroundTheory.Global.IdeleGroup.ideleModule E hu.unit).2, ← h2]
      exact Real.exp_le_exp.2 (by linarith [h1.1])
    obtain ⟨_, ⟨r, rfl⟩, c, hc, rfl⟩ := hred t hnorm hheight
    exact ⟨ratGL E n r, ⟨r, rfl⟩, c, hc, rfl⟩

end GlobalTheory.CompanionTheory.TorusCh

end
