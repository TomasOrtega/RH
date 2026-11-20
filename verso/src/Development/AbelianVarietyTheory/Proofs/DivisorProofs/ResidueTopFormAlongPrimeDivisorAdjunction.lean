import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Residue

open KaehlerDifferential IsLocalRing Module

/- English proof (translation)
Take `⟨b₀⟩` from `hb₀`. Use `haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V`. Set `κ` to `ResidueField V`. Set `wb : Fin n → κ` to `fun i => algebraMap V κ (w i)`. Establish `hai : AlgebraicIndependent k wb`.

Rewrite using `[algebraicIndependent_iff]`. Introduce `P hP`. Assume the negation of the conclusion as `hne`. Establish `hu` using `hw P hne`. Establish `e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ (algebraMap k V) w P)`.

Rewrite using `[show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]`. Both sides reduce to the same expression. Rewrite `hP` using `[e]`. Conclude with `(residue_ne_zero_iff_isUnit _).mpr hu hP`. Establish `hdli : LinearIndependent κ fun i => D k κ (wb i)`.

Establish `hs : AlgebraicIndepOn k id (Set.range wb)`. Conclude with `(algebraicIndependent_subtype_range hai.injective).mpr hai`. Take `⟨s, hsub, hs⟩` from `exists_isTranscendenceBasis_superset hs`. Use `haveI := hs.isAlgebraic_field`. Use `haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ := Algebra.IsAlgebraic.isSeparable_of_perfectField`.

Take `⟨b, hb⟩` from `exists_basis_kaehler_of_algebraicIndependent hs.1`. Set `ι : Fin n → s` to `fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩`. Establish `hι : Function.Injective ι` using `fun i j h => hai.injective (congrArg Subtype.val h)`. Use `b.linearIndependent.comp ι hι` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using `[ι, hb]`. Establish `ht₀ : algebraMap V κ t = 0` using `(residue_eq_zero_iff t).mpr (by`. Rewrite using `[ht.maximalIdeal_eq]`. Conclude with `Ideal.mem_span_singleton_self t)`.

Set `z : Fin (n + 1) → V` to `Fin.cons t w`. Establish `hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_succ]`.

Simplify using `only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg`. Establish `hφ` using `congrArg (mapBaseChange k V κ) hg`. Simplify using `only [map_add, map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀, Derivation.map_zero, smul_zero, zero_add] at hφ`. Establish `hs : ∀ i : Fin n, g i.succ = 0` using `Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ`. Simplify using `only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg`.

Establish `h0 : g 0 = 0`. Break down `smul_eq_zero.mp hg with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (one_tmul_D_ne_zero k ht)`. Introduce `i`.

Conclude with `Fin.cases h0 hs i`. Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank' (by`. Rewrite using `[Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])`. Use `haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀`. Use `haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀`.

Use `haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _`. Conclude with `Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype Subtype.val_injective)`.
-/
theorem exists_basis_D_cons (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra k V] [Algebra.EssFiniteType k V] (n : ℕ) {t : V}
    (w : Fin n → V) (ht : Irreducible t) (hb₀ : Nonempty (Module.Basis (Fin (n + 1)) V Ω[V⁄k]))
    (hw : ∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap k V) w P)) :
    ∃ b : Module.Basis (Fin (n + 1)) V Ω[V⁄k], ∀ i, b i = D k V ((Fin.cons t w : Fin (n + 1) → V) i) := by
  obtain ⟨b₀⟩ := hb₀
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)
  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ (algebraMap k V) w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP
  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    simp only [map_add, map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  exact Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)

/- English proof (translation)
Introduce `L K _ _ cL cK n S ψ hψ hc t f v w H ht hf hvK hvL hH`. Use `letI : Algebra ℂ S.ring := S.const.toAlgebra`. Use `letI : Algebra ℂ L := cL.toAlgebra`. Use `letI : Algebra ℂ K := cK.toAlgebra`. Use `letI : Algebra S.ring K := ψ.toAlgebra`.

Use `haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl`. Establish `hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K` using `RingHom.ext hc`. Use `haveI : IsScalarTower ℂ S.ring K := IsScalarTower.of_algebraMap_eq' hcomp.symm`. Use `haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType`. Use `haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring`.

Establish `hker : RingHom.ker ψ = maximalIdeal S.ring` using `by haveI := RingHom.ker_isMaximal_of_surjective ψ hψ`. Conclude with `IsLocalRing.eq_maximalIdeal this`. Establish `hψt : ψ t = 0`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `ht.not_isUnit`.

Establish `hb₀ : Nonempty (Module.Basis (Fin (n + 1)) S.ring Ω[S.ring⁄ℂ])`. Take `⟨m, z, b, -, -⟩` from `exists_basis_kaehler_uniformiser ℂ ht`. Establish `h1` using `trdeg_eq_of_basis_kaehler ℂ L b`. Establish `h2` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hvL`. Rewrite `h2` using `[h1, Cardinal.mk_fin]`.

Establish `h3 : n + 1 = m + 1` using `by exact_mod_cast h2`. Take `rfl : n = m` from `by omega`. Conclude with `⟨b⟩`. Establish `hvu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P)`. Introduce `P hP`.

Assume the negation of the conclusion as `hu`. Establish `hm : MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P ∈ RingHom.ker ψ`. Rewrite using `[hker]`. Conclude with `hu`. Rewrite `hm` using `[RingHom.mem_ker, MvPolynomial.hom_eval₂, hcomp]`.

Establish `hind : AlgebraicIndependent ℂ (fun i => ψ (v i))` using `hvK.1`. Conclude with `hP ((algebraicIndependent_iff.1 hind) P hm)`. Take `⟨b, hb⟩` from `exists_basis_D_cons ℂ S.ring n v ht hb₀ hvu`. Take `⟨u, hu⟩` from `IsDiscreteValuationRing.associated_of_irreducible _ ht hf`. Use `set z : Fin (n + 1) → S.ring := Fin.cons t v with hz`.

Establish `hω : IsFreeGen S.ring (dForm S.const z)` using `isFreeGen_dForm z b hb`. Set `M : Matrix (Fin (n + 1)) (Fin (n + 1)) S.ring` to `Matrix.of fun i j => b.repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i)) j`. Establish `hM : dForm S.const (Fin.cons f w : Fin (n + 1) → S.ring) = M.det • dForm S.const z`. Use `dForm_eq_det_smul _ _ M fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D ℂ S.ring _ = ∑ j, M i j • D ℂ S.ring (z j)`.

Use `conv_lhs => rw [← b.sum_repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i))]`. Simplify using `only [hb, M, Matrix.of_apply, hz]`. Establish `hcons : ∀ (a : S.ring) (g : Fin n → S.ring), (fun i => S.ring.subtype ((Fin.cons a g : Fin (n + 1) → S.ring) i)) = (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L)`. Introduce `a g`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp`. Establish `htoRat : ∀ (a : S.ring) (g : Fin n → S.ring), S.toRat (n + 1) (dForm S.const (Fin.cons a g : Fin (n + 1) → S.ring)) = dForm cL (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L)`. Introduce `a g`. Conclude with `(formMap_dForm (D := n + 1) S.ring.subtype rfl _).trans (congrArg _ (hcons a g))`. Establish `hML : dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) = (M.det : L) • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L)`.

Use `congrArg (S.toRat (n + 1)) hM` as an intermediate fact. Rewrite `this` using `[map_smulₛₗ, hz, htoRat, htoRat]`. Conclude with `this`. Establish `hHM : H = (M.det : L)`. Establish `hne` using `S.toRat_ne_zero hω`.

Rewrite `hne` using `[hz, htoRat]`. Conclude with `smul_left_injective L hne (hH.symm.trans hML)`. Establish `hmain : M.det * ↑u⁻¹ * f = M.det * t`. Rewrite using `[← hu, mul_comm t, ← mul_assoc, mul_assoc M.det, Units.inv_mul, mul_one]`. Use `⟨M.det * ↑u⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hHM]`. Conclude with `congrArg Subtype.val hmain` after adjusting the coercions. Set `N : Matrix (Fin n) (Fin n) K` to `Matrix.of fun i j => ψ (M i.succ j.succ)`. Establish `hN : dForm cK (fun i => ψ (w i)) = N.det • dForm cK (fun i => ψ (v i))`. Use `dForm_eq_det_smul _ _ N fun i => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `D ℂ K (ψ (w i)) = ∑ j, N i j • D ℂ K (ψ (v j))`. Use `congrArg (KaehlerDifferential.map ℂ ℂ S.ring K) (b.sum_repr (D ℂ S.ring (w i)))` as an intermediate fact. Rewrite `this` using `[map_sum, KaehlerDifferential.map_D, Fin.sum_univ_succ, RingHom.algebraMap_toAlgebra]`. Rewrite using `[← this]`. Simplify using `only [map_smul, hb, KaehlerDifferential.map_D, hz, Fin.cons_zero, Fin.cons_succ, RingHom.algebraMap_toAlgebra, hψt, map_zero, smul_zero, zero_add]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K]`. Simplify using `[N, M, RingHom.algebraMap_toAlgebra]`. Establish `hDt : D ℂ S.ring t = b 0` using `by rw [hb]; rfl`. Establish `hrow : ∀ j, ψ (M 0 j) = ψ (u * Finsupp.single (0 : Fin (n + 1)) (1 : S.ring) j)`.

Introduce `j`. Simplify using `only [M, Matrix.of_apply, Fin.cons_zero]`. Rewrite using `[← hu, Derivation.leibniz, hDt, map_add, map_smul, map_smul, b.repr_self]`. Rewrite using `[Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_mul, hψt, zero_mul, zero_add]`. Establish `hsub : (ψ.mapMatrix M).submatrix Fin.succ Fin.succ = N` using `Matrix.ext fun _ _ => rfl`.

Establish `h0 : ∀ j : Fin n, ψ.mapMatrix M 0 j.succ = 0` using `fun j => by`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hrow]`. Simplify using `[Finsupp.single_apply, (Fin.succ_ne_zero j).symm]`. Establish `h00 : ψ.mapMatrix M 0 0 = ψ u`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hrow]`.

Simplify using the standard rewrite rules. Establish `hdet : ψ M.det = ψ u * N.det`. Rewrite using `[RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero, hsub]`. Simplify using `only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]`. Rewrite using `[hN, map_mul, hdet, mul_comm (ψ u), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`.
-/
theorem residue_dForm : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → ∀ (t f : S.ring) (v w : Fin n → S.ring) (H : L),
  Irreducible t → Irreducible f → TrBasis cK (fun i => ψ (v i)) →
  TrBasis cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
    H • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  ∃ h : S.ring, (h : L) * f = H * t ∧ dForm cK (fun i => ψ (w i)) = ψ h • dForm cK (fun i => ψ (v i)) := by
  intro L K _ _ cL cK n S ψ hψ hc t f v w H ht hf hvK hvL hH
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  letI : Algebra S.ring K := ψ.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : IsScalarTower ℂ S.ring K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hψt : ψ t = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact ht.not_isUnit
  have hb₀ : Nonempty (Module.Basis (Fin (n + 1)) S.ring Ω[S.ring⁄ℂ]) := by
    obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ L b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hvL
    rw [h1, Cardinal.mk_fin] at h2
    have h3 : n + 1 = m + 1 := by exact_mod_cast h2
    obtain rfl : n = m := by omega
    exact ⟨b⟩
  have hvu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P) := by
    intro P hP
    by_contra hu
    have hm : MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P ∈ RingHom.ker ψ := by
      rw [hker]
      exact hu
    rw [RingHom.mem_ker, MvPolynomial.hom_eval₂, hcomp] at hm
    have hind : AlgebraicIndependent ℂ (fun i => ψ (v i)) := hvK.1
    exact hP ((algebraicIndependent_iff.1 hind) P hm)
  obtain ⟨b, hb⟩ := exists_basis_D_cons ℂ S.ring n v ht hb₀ hvu

  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ ht hf
  set z : Fin (n + 1) → S.ring := Fin.cons t v with hz
  have hω : IsFreeGen S.ring (dForm S.const z) := isFreeGen_dForm z b hb
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) S.ring :=
    Matrix.of fun i j => b.repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i)) j
  have hM : dForm S.const (Fin.cons f w : Fin (n + 1) → S.ring) = M.det • dForm S.const z := by
    refine dForm_eq_det_smul _ _ M fun i => ?_
    change D ℂ S.ring _ = ∑ j, M i j • D ℂ S.ring (z j)
    conv_lhs => rw [← b.sum_repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i))]
    simp only [hb, M, Matrix.of_apply, hz]
  have hcons : ∀ (a : S.ring) (g : Fin n → S.ring),
      (fun i => S.ring.subtype ((Fin.cons a g : Fin (n + 1) → S.ring) i)) =
        (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have htoRat : ∀ (a : S.ring) (g : Fin n → S.ring),
      S.toRat (n + 1) (dForm S.const (Fin.cons a g : Fin (n + 1) → S.ring)) =
        dForm cL (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    exact (formMap_dForm (D := n + 1) S.ring.subtype rfl _).trans (congrArg _ (hcons a g))
  have hML : dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
      (M.det : L) • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) := by
    have := congrArg (S.toRat (n + 1)) hM
    rw [map_smulₛₗ, hz, htoRat, htoRat] at this
    exact this
  have hHM : H = (M.det : L) := by
    have hne := S.toRat_ne_zero hω
    rw [hz, htoRat] at hne
    exact smul_left_injective L hne (hH.symm.trans hML)

  have hmain : M.det * ↑u⁻¹ * f = M.det * t := by
    rw [← hu, mul_comm t, ← mul_assoc, mul_assoc M.det, Units.inv_mul, mul_one]
  refine ⟨M.det * ↑u⁻¹, ?_, ?_⟩
  · rw [hHM]
    exact_mod_cast congrArg Subtype.val hmain
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ψ (M i.succ j.succ)
  have hN : dForm cK (fun i => ψ (w i)) = N.det • dForm cK (fun i => ψ (v i)) := by
    refine dForm_eq_det_smul _ _ N fun i => ?_
    change D ℂ K (ψ (w i)) = ∑ j, N i j • D ℂ K (ψ (v j))
    have := congrArg (KaehlerDifferential.map ℂ ℂ S.ring K) (b.sum_repr (D ℂ S.ring (w i)))
    rw [map_sum, KaehlerDifferential.map_D, Fin.sum_univ_succ, RingHom.algebraMap_toAlgebra] at this
    rw [← this]
    simp only [map_smul, hb, KaehlerDifferential.map_D, hz, Fin.cons_zero, Fin.cons_succ,
      RingHom.algebraMap_toAlgebra, hψt, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K]
    simp [N, M, RingHom.algebraMap_toAlgebra]
  have hDt : D ℂ S.ring t = b 0 := by rw [hb]; rfl
  have hrow : ∀ j, ψ (M 0 j) = ψ (u * Finsupp.single (0 : Fin (n + 1)) (1 : S.ring) j) := by
    intro j
    simp only [M, Matrix.of_apply, Fin.cons_zero]
    rw [← hu, Derivation.leibniz, hDt, map_add, map_smul, map_smul, b.repr_self]
    rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, hψt, zero_mul, zero_add]
  have hsub : (ψ.mapMatrix M).submatrix Fin.succ Fin.succ = N := Matrix.ext fun _ _ => rfl
  have h0 : ∀ j : Fin n, ψ.mapMatrix M 0 j.succ = 0 := fun j => by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp [Finsupp.single_apply, (Fin.succ_ne_zero j).symm]
  have h00 : ψ.mapMatrix M 0 0 = ψ u := by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp
  have hdet : ψ M.det = ψ u * N.det := by
    rw [RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero, hsub]
    simp only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul]
  rw [hN, map_mul, hdet, mul_comm (ψ u), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end GlobalTheory.Residue
