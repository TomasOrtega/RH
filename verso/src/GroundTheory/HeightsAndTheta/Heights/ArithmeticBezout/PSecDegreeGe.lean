import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecDegreeGe

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [Vertical.specRest]`. Consider the case `add p q hp hq => simp only [Vertical.specRest] at hp hq ⊢`. Simplify using `[hp, hq]`. Consider the case `mul_X p ij hp`.

Simplify using `only [Vertical.specRest] at hp ⊢`. Take `⟨i, j⟩` from `ij`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [hp]`. Consider the case `succ i => simp [hp]`.
-/
theorem eval_specRest (ψ : k →+* R) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) (v : Fin n → R) :
    eval v (Vertical.specRest ψ f y) =
      eval₂ ψ (fun ij => Fin.cases (motive := fun _ => R) (v ij.2)
        (fun i => y (.inl (i, ij.2))) ij.1) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Vertical.specRest]
  | add p q hp hq => simp only [Vertical.specRest] at hp hq ⊢; simp [hp, hq]
  | mul_X p ij hp =>
    simp only [Vertical.specRest] at hp ⊢
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [hp]
    | succ i => simp [hp]

/- English proof (translation)
Rewrite using `[eval_specRest, eval_specRest, MvPolynomial.eval₂_comp_left]`. Use `congr 1`. Use function extensionality and compare the values at `⟨i, j⟩`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => rfl`.

Consider the case `succ i => rfl`.
-/
theorem map_eval_specRest (ψ : k →+* R) (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) :
    φ (eval (fun j => y (.inr j)) (Vertical.specRest ψ f y)) =
      eval (fun j => φ (y (.inr j))) (Vertical.specRest (φ.comp ψ) f (φ ∘ y)) := by
  rw [eval_specRest, eval_specRest, MvPolynomial.eval₂_comp_left]
  congr 1
  funext ⟨i, j⟩
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SecDegreeGe

open SecDegreeGe in

/- English proof (translation)
Introduce `k E _ _ _ _ n e δ Q g y hQ hg hδ hne`. Use `⟨hFin k E n e δ Q g y hg hδ (isUnit_iff_ne_zero.2 hne), ?_⟩` and prove the remaining obligations. Set `𝔭 : Ideal (MvPolynomial (Vertical.Par e n) E)` to `RingHom.ker (eval y)`. Establish `: 𝔭.IsPrime` using `RingHom.ker_isPrime _`. Set `R` to `Localization.AtPrime 𝔭`.

Establish `: IsDomain R` using `IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors 𝔭)`. Set `K` to `FractionRing (MvPolynomial (Vertical.Par e n) E)`. Establish `: IsScalarTower k R K` using `IsScalarTower.of_algebraMap_eq fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R, ← IsScalarTower.algebraMap_apply (MvPolynomial (Vertical.Par e n) E) R K, ← IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) K]`. Set `π : R →+* E` to `IsLocalization.lift (M := 𝔭.primeCompl) (g := eval y) (fun s => isUnit_iff_ne_zero.2 fun h => s.2 (RingHom.mem_ker.2 h))`.

Establish `hπ : ∀ p, π (algebraMap (MvPolynomial (Vertical.Par e n) E) R p) = eval y p` using `fun p => IsLocalization.lift_eq _ _`. Set `_ : Algebra R E` to `π.toAlgebra`. Set `Y : Vertical.Par e n → R` to `fun p => algebraMap (MvPolynomial (Vertical.Par e n) E) R (X p)`. Establish `hπY : algebraMap R E ∘ Y = y` using `funext fun p => by`. Simplify using `[RingHom.algebraMap_toAlgebra, Y, hπ]`.

Establish `hπk : (algebraMap R E).comp (algebraMap k R) = algebraMap k E`. Use extensionality with `a`. Use `show π (algebraMap k R a) = algebraMap k E a`. Rewrite using `[IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R, hπ, MvPolynomial.algebraMap_apply, eval_C]`. Establish `hsurj : Function.Surjective (algebraMap R E)` using `fun a => ⟨algebraMap (MvPolynomial (Vertical.Par e n) E) R (C a), by simp [RingHom.algebraMap_toAlgebra, hπ]⟩`.

Establish `hunit : IsUnit (eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y))`. Establish `h1` using `map_eval_specRest (algebraMap k R) (algebraMap R E) g Y`. Rewrite `h1` using `[hπk, hπY]`. Establish `hker : RingHom.ker (algebraMap R E) = IsLocalRing.maximalIdeal R` using `by haveI := RingHom.ker_isMaximal_of_surjective _ hsurj`. Conclude with `IsLocalRing.eq_maximalIdeal this`.

Assume the negation of the conclusion as `hu`. Establish `hm : eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y) ∈ RingHom.ker (algebraMap R E)`. Rewrite using `[hker]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hu`. Establish `hv : (fun j => algebraMap R E (Y (.inr j))) = fun j => y (.inr j)`.

Use function extensionality and compare the values at `fun j => congrFun hπY (.inr j)`. Rewrite `hm` using `[RingHom.mem_ker, h1, hv]`. Conclude with `hne hm`. Establish `hB` using `hFin k R n e δ Q g Y hg hδ hunit`. Establish `hle` using `hSpec R K E n e (Q.map (MvPolynomial.map (algebraMap k R))) Y hsurj hB`.

Establish `hmapK : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R K)) = Q.map (MvPolynomial.map (algebraMap k K))`. Rewrite using `[Ideal.map_map]`. Use `congr 1`. Apply the tactic sequence `refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_) <;>`. Simplify using `[← IsScalarTower.algebraMap_apply]`.

Establish `hmapE : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R E)) = Q.map (MvPolynomial.map (algebraMap k E))`. Rewrite using `[Ideal.map_map]`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, map_C]`.

Conclude with `congrArg C (RingHom.congr_fun hπk a)`. Simplify using the standard rewrite rules. Rewrite `hle` using `[hmapK, hmapE, hπY]`. Establish `hind : AlgebraicIndependent k (algebraMap R K ∘ Y)`. Establish `h0 : AlgebraicIndependent k (X : Vertical.Par e n → MvPolynomial (Vertical.Par e n) E)` using `(MvPolynomial.algebraicIndependent_X _ _).restrictScalars (FaithfulSMul.algebraMap_injective k E)`.

Set `f : MvPolynomial (Vertical.Par e n) E →ₐ[k] K` to `(IsScalarTower.toAlgHom k R K).comp (IsScalarTower.toAlgHom k (MvPolynomial (Vertical.Par e n) E) R)`. Establish `hinj : Function.Injective f` using `(IsFractionRing.injective R K).comp (IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors 𝔭))`. Establish `h1 : AlgebraicIndependent k (f ∘ X)` using `h0.map' hinj`. Establish `heq : f ∘ X = algebraMap R K ∘ Y` using `funext fun p => rfl`. Rewrite `h1` using `[heq]`. Then use the resulting hypothesis.

Establish `hgen` using `Vertical.ChowSecDegree.proof (Vertical.ChowNormForm.proof (Vertical.ChowNormFormGeneric.proof Vertical.SecAlgFinite.full Vertical.GenSecDomain.full Vertical.GenSecSeparable.full Vertical.ChowSecDvd.full Vertical.NormFormIrreducible.full Vertical.GenChowIrreducible.full Vertical.N …`. Establish `hdeg : δ = chowDegree Q (e + 1)` using `Vertical.chowForm_degree_unique (Nat.succ_pos e) hg hg hδ (Vertical.ChowFormHomog.full k n (e + 1) Q g hg)`. Rewrite `hle` using `[hgen]`. Conclude with `hdeg ▸ hle`.
-/
theorem SecDegreeGe.proof (hFin : SecFiniteUnit.Statement) (hSpec : SecRankSpecialize.Statement) :
    SecDegreeGe.Statement := by
  intro k E _ _ _ _ n e δ Q g y hQ hg hδ hne
  refine ⟨hFin k E n e δ Q g y hg hδ (isUnit_iff_ne_zero.2 hne), ?_⟩

  let 𝔭 : Ideal (MvPolynomial (Vertical.Par e n) E) := RingHom.ker (eval y)
  have : 𝔭.IsPrime := RingHom.ker_isPrime _
  let R := Localization.AtPrime 𝔭
  have : IsDomain R :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  let K := FractionRing (MvPolynomial (Vertical.Par e n) E)
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Vertical.Par e n) E) R K,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) K]
  let π : R →+* E := IsLocalization.lift (M := 𝔭.primeCompl) (g := eval y)
    (fun s => isUnit_iff_ne_zero.2 fun h => s.2 (RingHom.mem_ker.2 h))
  have hπ : ∀ p, π (algebraMap (MvPolynomial (Vertical.Par e n) E) R p) = eval y p := fun p => IsLocalization.lift_eq _ _
  let _ : Algebra R E := π.toAlgebra
  let Y : Vertical.Par e n → R := fun p => algebraMap (MvPolynomial (Vertical.Par e n) E) R (X p)
  have hπY : algebraMap R E ∘ Y = y := funext fun p => by
    simp [RingHom.algebraMap_toAlgebra, Y, hπ]
  have hπk : (algebraMap R E).comp (algebraMap k R) = algebraMap k E := by
    ext a
    show π (algebraMap k R a) = algebraMap k E a
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R, hπ,
      MvPolynomial.algebraMap_apply, eval_C]
  have hsurj : Function.Surjective (algebraMap R E) := fun a =>
    ⟨algebraMap (MvPolynomial (Vertical.Par e n) E) R (C a), by simp [RingHom.algebraMap_toAlgebra, hπ]⟩

  have hunit : IsUnit (eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y)) := by
    have h1 := map_eval_specRest (algebraMap k R) (algebraMap R E) g Y
    rw [hπk, hπY] at h1
    have hker : RingHom.ker (algebraMap R E) = IsLocalRing.maximalIdeal R := by
      haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
      exact IsLocalRing.eq_maximalIdeal this
    by_contra hu
    have hm : eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y) ∈
        RingHom.ker (algebraMap R E) := by
      rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    have hv : (fun j => algebraMap R E (Y (.inr j))) = fun j => y (.inr j) :=
      funext fun j => congrFun hπY (.inr j)
    rw [RingHom.mem_ker, h1, hv] at hm
    exact hne hm
  have hB := hFin k R n e δ Q g Y hg hδ hunit
  have hle := hSpec R K E n e (Q.map (MvPolynomial.map (algebraMap k R))) Y hsurj hB
  have hmapK : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R K)) =
      Q.map (MvPolynomial.map (algebraMap k K)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_) <;>
      simp [← IsScalarTower.algebraMap_apply]
  have hmapE : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R E)) =
      Q.map (MvPolynomial.map (algebraMap k E)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, map_C]
      exact congrArg C (RingHom.congr_fun hπk a)
    · simp
  rw [hmapK, hmapE, hπY] at hle

  have hind : AlgebraicIndependent k (algebraMap R K ∘ Y) := by
    have h0 : AlgebraicIndependent k (X : Vertical.Par e n → MvPolynomial (Vertical.Par e n) E) :=
      (MvPolynomial.algebraicIndependent_X _ _).restrictScalars
        (FaithfulSMul.algebraMap_injective k E)
    let f : MvPolynomial (Vertical.Par e n) E →ₐ[k] K :=
      (IsScalarTower.toAlgHom k R K).comp
        (IsScalarTower.toAlgHom k (MvPolynomial (Vertical.Par e n) E) R)
    have hinj : Function.Injective f :=
      (IsFractionRing.injective R K).comp
        (IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors 𝔭))
    have h1 : AlgebraicIndependent k (f ∘ X) := h0.map' hinj
    have heq : f ∘ X = algebraMap R K ∘ Y := funext fun p => rfl
    rwa [heq] at h1
  have hgen := Vertical.ChowSecDegree.proof
    (Vertical.ChowNormForm.proof
      (Vertical.ChowNormFormGeneric.proof Vertical.SecAlgFinite.full Vertical.GenSecDomain.full
        Vertical.GenSecSeparable.full Vertical.ChowSecDvd.full Vertical.NormFormIrreducible.full
        Vertical.GenChowIrreducible.full Vertical.NormFormDvd.full)
      Vertical.SecAlgFieldChange.full)
    Vertical.ChowFormHomog.full Vertical.NormFormEval.full k K n e Q g (algebraMap R K ∘ Y) hind hQ hg
  have hdeg : δ = chowDegree Q (e + 1) :=
    Vertical.chowForm_degree_unique (Nat.succ_pos e) hg hg hδ
      (Vertical.ChowFormHomog.full k n (e + 1) Q g hg)
  rw [hgen] at hle
  exact hdeg ▸ hle

end

end GroundTheory.Heights₂.Heights
