import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniDepthZero

/- English proof (translation)
Set `e : L ≃ₐ[(maximalRealSubfield L)] ψ.fieldRange` to `AlgEquiv.ofInjectiveField ψ`. Use `haveI : Normal (maximalRealSubfield L) ψ.fieldRange := Normal.of_algEquiv e`. Establish `hR : φ.fieldRange = ψ.fieldRange`. Establish `h` using `AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)`. Rewrite using `[← h]`.

Use extensionality with `x`. Simplify using `only [AlgHom.mem_fieldRange, AlgHom.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩; exact ⟨e y, by simp⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨_, rfl⟩`. Establish `hmem : ∀ z, φ z ∈ ψ.fieldRange` using `fun z => hR ▸ ⟨z, rfl⟩`. Set `g₀ : L →ₐ[(maximalRealSubfield L)] L` to `e.symm.toAlgHom.comp (φ.codRestrict ψ.fieldRange.toSubalgebra hmem)`. Establish `hg₀ : ∀ z, ψ (g₀ z) = φ z` using `fun z => by`. Use `congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hmem z⟩)` as an intermediate fact.

Conclude with `this`. Set `σ : L ≃ₐ[(maximalRealSubfield L)] L` to `AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)`. Establish `hσ : ∀ z, ψ (σ z) = φ z` using `hg₀`. Establish `htop` using `IsCMField.zpowers_complexConj_eq_top L`. Establish `hmemσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj L)` using `by rw [htop]; trivial`.

Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 hmemσ`. Establish `hk2 : IsCMField.complexConj L ^ (k % 2) = σ`. Establish `h` using `zpow_mod_orderOf (IsCMField.complexConj L) k`. Rewrite `h` using `[IsCMField.orderOf_complexConj L]`. Rewrite using `[← hk]`.

Conclude with `h` after adjusting the coercions. Break down `Int.emod_two_eq_zero_or_one k with h0 | h1` into its components or cases. Use `left`. Rewrite `hk2` using `[h0, zpow_zero]`. Use extensionality with `z`.

Rewrite using `[← hσ, ← hk2]`. Both sides reduce to the same expression. Use `right`. Rewrite `hk2` using `[h1, zpow_one]`. Use extensionality with `z`.

Rewrite using `[← hσ, ← hk2]`. Both sides reduce to the same expression.
-/
theorem algHom_eq_or_conj {L K : Type} [Field L] [NumberField L] [IsCMField L] [Field K] [Algebra (maximalRealSubfield L) K]
    (φ ψ : L →ₐ[(maximalRealSubfield L)] K) : φ = ψ ∨ φ = ψ.comp (IsCMField.complexConj L).toAlgHom := by
  let e : L ≃ₐ[(maximalRealSubfield L)] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal (maximalRealSubfield L) ψ.fieldRange := Normal.of_algEquiv e
  have hR : φ.fieldRange = ψ.fieldRange := by
    have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
    rw [← h]
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
  have hmem : ∀ z, φ z ∈ ψ.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : L →ₐ[(maximalRealSubfield L)] L := e.symm.toAlgHom.comp (φ.codRestrict ψ.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, ψ (g₀ z) = φ z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hmem z⟩)
    exact this
  let σ : L ≃ₐ[(maximalRealSubfield L)] L := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  have hσ : ∀ z, ψ (σ z) = φ z := hg₀
  have htop := IsCMField.zpowers_complexConj_eq_top L
  have hmemσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj L) := by rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemσ
  have hk2 : IsCMField.complexConj L ^ (k % 2) = σ := by
    have h := zpow_mod_orderOf (IsCMField.complexConj L) k
    rw [IsCMField.orderOf_complexConj L] at h
    rw [← hk]
    exact_mod_cast h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl
  · right
    rw [h1, zpow_one] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

/- English proof (translation)
Substitute `hi` using the available equality. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`.
-/
theorem proj_conj {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) (x : AL L) :
    (SplitPlace.proj (⟨v, i⟩ : SplitPlace L)) x = (SplitPlace.proj (⟨v, i₀⟩ : SplitPlace L)) (conjAL L x) := by
  subst hi
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Establish `hm` using `κ.2`. Simplify using `only [GA, UGroup, Subgroup.mem_mk] at hm`. Establish `h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1` using `Units.inv_eq_of_mul_eq_one_right hm`. Establish `h2 : (((κ⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a = conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b)`. Rewrite using `[InvMemClass.coe_inv, h1]`.

Both sides reduce to the same expression. Simplify using `only [SplitPlace.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply]`. Rewrite using `[h2, proj_conj v i i₀ hi]`.
-/
theorem loc_conj_apply {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) {n : ℕ} (κ : GA L n) (a b : Fin n) :
    (SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ).val a b =
      (SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹).val b a := by
  have hm := κ.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  have h2 : (((κ⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a = conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) := by
    rw [InvMemClass.coe_inv, h1]; rfl
  simp only [SplitPlace.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
  rw [h2, proj_conj v i i₀ hi]

/- English proof (translation)
Break down `algHom_eq_or_conj i i₀ with rfl | hi` into its components or cases. Conclude with `h`. Establish `h' : SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n)`. Use `(GlobalTheory.FixedAtSplit.mem_KOne_iff' _).2 fun a b => ?_` and prove the remaining obligations. Use `(GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h b a` as an intermediate fact.

Simplify using `only [Matrix.sub_apply, Matrix.one_apply] at this ⊢`. Rewrite using `[← loc_conj_apply v i i₀ hi]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `using this`.

Simplify `this` using `[hab, Ne.symm hab]`. Use `inv_mem h'` as an intermediate fact. Rewrite `this` using `[map_inv, inv_inv]`. Then use the resulting hypothesis.
-/
theorem loc_mem_KOne_of_same {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) {n : ℕ} (κ : GA L n)
    (h : SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
  rcases algHom_eq_or_conj i i₀ with rfl | hi
  · exact h
  · have h' : SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
      refine (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).2 fun a b => ?_
      have := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h b a
      simp only [Matrix.sub_apply, Matrix.one_apply] at this ⊢
      rw [← loc_conj_apply v i i₀ hi]
      by_cases hab : a = b
      · subst hab; simpa using this
      · simpa [hab, Ne.symm hab] using this
    have := inv_mem h'
    rwa [map_inv, inv_inv] at this

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

/- English proof (translation)
Use `set g := s₀.loc n κ with hg`. Establish `hv` using `(GlobalTheory.FixedAtSplit.mem_KOne_iff' g).1 hK`. Establish `hoff : ∀ a b : Fin n, a ≠ b → Valued.v (g.val a b) < 1` using `fun a b hab => by`. Simplify `hv a b` using `[Matrix.sub_apply, Matrix.one_apply_ne hab]`. Establish `hdiag : ∀ a : Fin n, Valued.v (g.val a a - 1) < 1` using `fun a => by`.

Simplify `hv a a` using `[Matrix.sub_apply]`. Establish `hint : g ∈ Formalism.UG.GLint (Fin n) (s₀.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring`. Rewrite using `[(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s₀.v n).1]`. Conclude with `GlobalTheory.StepData.KOne_le_KO hK`. Establish `huni : NG.UniRT s₀ r g`.

Use `⟨⟨hint, fun a b ha hb => hoff a b ?_⟩, fun a b ha hb => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers.

Substitute `hab` using the available equality. Conclude with `hdiag a`. Establish `hmem : κ ∈ J` using `(hJ.mem κ hκ).2 huni`. Set `D : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s₀.v.adicCompletion (maximalRealSubfield L))` to `Matrix.of fun a b => g.val a.1 b.1`. Establish `hD : GlobalTheory.StepData.MaxM (D - 1)`.

Establish `hm` using `GlobalTheory.StepData.mem_KOne.1 hK`. Introduce `a b`. Establish `h3` using `hm a.1 b.1`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify `h3` using `[D, Matrix.sub_apply]`. Establish `h4 : a.1 ≠ b.1` using `fun h => hab (Subtype.ext h)`. Simplify `h3` using `[D, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne h4]`. Take `⟨u', hu', hu'v⟩` from `GlobalTheory.StepData.exists_mem_KOne hD`. Establish `hdet` using `GlobalTheory.StepData.det_of_mem_KOne hu'`.

Establish `: (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Establish `he` using `isEquiv (valuation (s₀.v.adicCompletion (maximalRealSubfield L))) (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)))`. Establish `hdetv : Valued.v (NG.detDD s₀ r g - 1) < 1`. Rewrite using `[← he.lt_one_iff_lt_one]`. Use `hdet using 3` and compare the differences between its conclusion and the goal.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hu'v]`. Both sides reduce to the same expression. Establish `hne : NG.detDD s₀ r g ≠ 0` using `fun h0 => by`. Rewrite `hdetv` using `[h0, zero_sub, Valuation.map_neg, Valuation.map_one]`. Conclude with `lt_irrefl _ hdetv`.

Establish `hχ` using `hJ.chr κ hmem hκ (Units.mk0 _ hne) rfl`. Establish `h1 : ψ₀ (NG.supDiag s₀ r g) = 1`. Use `hψ.1 _ ?_` and prove the remaining obligations. Use `Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Conclude with `hoff a b (fun e => by subst e; omega)`. Simplify using the standard rewrite rules. Establish `h2 : ξ (Units.mk0 _ hne) = 1` using `hξ _ (by simpa using hdetv)`. Use `⟨hmem, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hχ, h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem level_trivial {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s₀ : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
    (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)
    (hJ : NG.LevelUni J χ s₀ r ψ₀ ξ) (hψ : NG.IsPsi0 s₀ ψ₀)
    (hξ : ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1)
    (κ : GAf L n) (hκ : TrivOutside {s₀.v} κ)
    (hK : s₀.loc n κ ∈ KOne (s₀.v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1 := by
  set g := s₀.loc n κ with hg
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' g).1 hK
  have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (g.val a b) < 1 := fun a b hab => by
    simpa [Matrix.sub_apply, Matrix.one_apply_ne hab] using hv a b
  have hdiag : ∀ a : Fin n, Valued.v (g.val a a - 1) < 1 := fun a => by
    simpa [Matrix.sub_apply] using hv a a
  have hint : g ∈ Formalism.UG.GLint (Fin n) (s₀.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s₀.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hK
  have huni : NG.UniRT s₀ r g := by
    refine ⟨⟨hint, fun a b ha hb => hoff a b ?_⟩, fun a b ha hb => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · rintro rfl; omega
    · rintro rfl; omega
    · subst hab; exact hdiag a
  have hmem : κ ∈ J := (hJ.mem κ hκ).2 huni
  let D : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s₀.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.of fun a b => g.val a.1 b.1
  have hD : GlobalTheory.StepData.MaxM (D - 1) := by
    have hm := GlobalTheory.StepData.mem_KOne.1 hK
    intro a b
    have h3 := hm a.1 b.1
    by_cases hab : a = b
    · subst hab
      simpa [D, Matrix.sub_apply] using h3
    · have h4 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simpa [D, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne h4] using h3
  obtain ⟨u', hu', hu'v⟩ := GlobalTheory.StepData.exists_mem_KOne hD
  have hdet := GlobalTheory.StepData.det_of_mem_KOne hu'
  have : (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (s₀.v.adicCompletion (maximalRealSubfield L)))
    (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)))
  have hdetv : Valued.v (NG.detDD s₀ r g - 1) < 1 := by
    rw [← he.lt_one_iff_lt_one]
    convert hdet using 3
    rw [Matrix.GeneralLinearGroup.val_det_apply, hu'v]
    rfl
  have hne : NG.detDD s₀ r g ≠ 0 := fun h0 => by
    rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdetv
    exact lt_irrefl _ hdetv
  have hχ := hJ.chr κ hmem hκ (Units.mk0 _ hne) rfl
  have h1 : ψ₀ (NG.supDiag s₀ r g) = 1 := by
    refine hψ.1 _ ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with h
    · exact hoff a b (fun e => by subst e; omega)
    · simp
  have h2 : ξ (Units.mk0 _ hne) = 1 := hξ _ (by simpa using hdetv)
  refine ⟨hmem, Units.ext ?_⟩
  rw [hχ, h1, h2]
  simp

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

/- English proof (translation)
Introduce `L _ _ _ n a S hS J χ _ s₀ r ψ₀ ξ hJ hψ hξ f hf hfJ hf0 s hs σ hσ`. Take `⟨c, T, hc, hci, -⟩` from `id hσ`. Establish `hfix : ∀ κ : GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f`. Introduce `κ hκ hK`. Take `⟨v, i⟩` from `s`.

Take `⟨v₀, i₀⟩` from `s₀`. Take `rfl : v = v₀` from `hs`. Establish `hK₀` using `loc_mem_KOne_of_same _ i i₀ κ hK`. Take `⟨hm, h1⟩` from `level_trivial J χ _ r ψ₀ ξ hJ hψ hξ κ hκ hK₀`. Establish `h2` using `hfJ.2 ⟨κ, hm⟩`.

Rewrite `h2` using `[h1]`. Simplify using `using h2`. Take `⟨u, hu0, hu⟩` from `GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 (fun g hg => by`. Rewrite using `[(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]`. Conclude with `GlobalTheory.StepData.KOne_le_KO hg)`.

Use the proof step `(by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)`. Use `f hf hf0 (fun κ hκ h => by rw [hfix κ hκ h]; simp)`. Use `GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep σ).some.symm ?_` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`. Use `⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩` and prove the remaining obligations.

Establish `e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hg` using `GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)`. Establish `h3` using `hu _ hg`.

Rewrite `h3` using `[e]`. Simplify using `using h3`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (s₀ : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ → NG.IsPsi0 s₀ ψ₀ → (∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v = s₀.v → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → fixed (GlobalTheory.LocLanglands.cls σ).rep (KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n a S hS J χ _ s₀ r ψ₀ ξ hJ hψ hξ f hf hfJ hf0 s hs σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hfix : ∀ κ : GAf L n, TrivOutside {s.v} κ →
      s.loc n κ ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f := by
    intro κ hκ hK
    obtain ⟨v, i⟩ := s
    obtain ⟨v₀, i₀⟩ := s₀
    obtain rfl : v = v₀ := hs
    have hK₀ := loc_mem_KOne_of_same _ i i₀ κ hK
    obtain ⟨hm, h1⟩ := level_trivial J χ _ r ψ₀ ξ hJ hψ hξ κ hκ hK₀
    have h2 := hfJ.2 ⟨κ, hm⟩
    rw [h1] at h2
    simpa using h2
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1
    (fun g hg => by
      rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
      exact GlobalTheory.StepData.KOne_le_KO hg)
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hf hf0 (fun κ hκ h => by rw [hfix κ hκ h]; simp)
  refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep σ).some.symm ?_
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3

end GlobalTheory.UniDepthZero

end
