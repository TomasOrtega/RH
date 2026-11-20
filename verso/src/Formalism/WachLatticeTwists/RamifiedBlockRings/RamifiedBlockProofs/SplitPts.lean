import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SplitFibre

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `O _ _ Xs T t P hPc hPr`. Break down `isEmpty_or_nonempty Xs with hX | hX` into its components or cases. Conclude with `⟨fun _ _ => 0, fun _ => (splitT T t P).zero_mem, fun f' _ => ⟨fun _ _ => 0, fun _ => T.zero_mem,`. Use function extensionality and compare the values at `fun y => (hX.elim y.1.1)⟩, fun x => hX.elim x⟩`. Establish `hnt : Nontrivial T` using `inferInstance`.

Set `evT : Xs → (T →+* O)` to `fun x => (Pi.evalRingHom (fun _ : Xs => O) x).comp T.val.toRingHom`. Establish `hmonP : ∀ x, (P x).Monic` using `fun x => by`. Take `⟨α, -, h⟩` from `hPr x`. Rewrite using `[h]`. Conclude with `Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _`.

Establish `hdegP : ∀ x, (P x).natDegree = t` using `fun x => by`. Take `⟨α, -, h⟩` from `hPr x`. Rewrite using `[h, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]`. Simplify using the standard rewrite rules. Set `PT : Polynomial T` to `∑ k ∈ range (t + 1), Polynomial.monomial k ⟨fun x => (P x).coeff k, hPc k⟩`.

Establish `hcoef : ∀ k, PT.coeff k = if k ≤ t then ⟨fun x => (P x).coeff k, hPc k⟩ else 0`. Introduce `k`. Simplify using `only [PT, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]`. Establish `hmap : ∀ x, PT.map (evT x) = P x`. Introduce `x`.

Use extensionality with `k`. Rewrite using `[Polynomial.coeff_map, hcoef]`. Use `split_ifs with hk`. Both sides reduce to the same expression. Rewrite using `[map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegP]; omega)]`.

Establish `hle : PT.natDegree ≤ t`. Rewrite using `[Polynomial.natDegree_le_iff_coeff_eq_zero]`. Introduce `N hN`. Rewrite using `[hcoef, if_neg (by omega)]`. Establish `hone : PT.coeff t = 1`.

Rewrite using `[hcoef, if_pos le_rfl]`. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Use `(hmonP x).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hdegP]`. Conclude with `this`.

Establish `hmon : PT.Monic` using `Polynomial.monic_of_natDegree_le_of_coeff_eq_one t hle hone`. Establish `hdeg : PT.natDegree = t` using `le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hone]; exact one_ne_zero))`. Establish `key` using `splitAlg T PT hmon`. Rewrite `key` using `[hdeg]`. Take `⟨T', _, _, rr, hfree, hfin, hrank, hfac, hadj, huniv⟩` from `key`.

Establish `hψ : ∀ y : SplitPts t P, ∃ ψ : T' →+* O, ψ.comp (algebraMap T T') = evT y.1.1 ∧ ∀ i, ψ (rr i) = y.1.2 i`. Introduce `y`. Use `letI : Algebra T O := (evT y.1.1).toAlgebra`. Take `⟨φ, hφ, -⟩` from `huniv O y.1.2 (by show PT.map (evT y.1.1) = _`. Rewrite using `[hmap]`.

Conclude with `y.2)`. Conclude with `⟨φ.toRingHom, RingHom.ext fun τ => φ.commutes τ, hφ⟩`. Use `choose ψ hψ1 hψ2 using hψ`. Set `Ψ : T' →+* (SplitPts t P → O)` to `Pi.ringHom ψ`. Set `bas : Module.Basis (Fin t.factorial) T T'` to `Module.finBasisOfFinrankEq T T' hrank`.

Establish `hΨa : ∀ τ : T, Ψ (algebraMap T T' τ) = fun y => τ.1 y.1.1` using `fun τ => funext fun y => RingHom.congr_fun (hψ1 y) τ`. Establish `hrange : ∀ f' ∈ splitT T t P, ∃ z, Ψ z = f'`. Introduce `f' hf'`. Proceed by induction on `hf' using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Break down `hx with ⟨f, hf, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Conclude with `⟨algebraMap T T' ⟨f, hf⟩, hΨa _⟩`. Conclude with `⟨rr i, funext fun y => hψ2 y i⟩`. Consider the case `algebraMap c => exact ⟨algebraMap T T' (algebraMap O T c), hΨa _⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, map_mul _ _ _⟩`. Establish `hmemΨ : ∀ z, Ψ z ∈ splitT T t P`. Introduce `z`. Establish `hz : z ∈ Algebra.adjoin T (Set.range rr)` using `hadj ▸ Algebra.mem_top`.

Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Establish `h1 : Ψ (rr i) = splitRoot t P i` using `funext fun y => hψ2 y i`. Rewrite using `[h1]`.

Conclude with `Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)`. Consider the case `algebraMap τ`. Rewrite using `[hΨa]`. Conclude with `Algebra.subset_adjoin (Or.inl ⟨τ.1, τ.2, rfl⟩)`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Use `⟨fun k => Ψ (bas k), fun k => hmemΨ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `f' hf'`.

Take `⟨z, rfl⟩` from `hrange f' hf'`. Use `⟨fun k => (bas.repr z k).1, fun k => (bas.repr z k).2, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← bas.sum_repr z]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, map_mul, hΨa]`. Introduce `x a ha`. Set `K` to `FractionRing O`. Set `ι : O →+* K` to `algebraMap O K`. Establish `hι : Function.Injective ι` using `IsFractionRing.injective O K`.

Take `⟨α, hα, hPα⟩` from `hPr x`. Establish `hmapK : PT.map (ι.comp (evT x)) = ∏ i, (Polynomial.X - Polynomial.C (ι (α i)))`. Rewrite using `[← Polynomial.map_map, hmap, hPα, Polynomial.map_prod]`. Simplify using the standard rewrite rules. Establish `sf` using `splitFibre T T' K PT hmon`.

Rewrite `sf` using `[hdeg]`. Establish `hz` using `sf rr hfac hadj bas (ι.comp (evT x)) (fun i => ι (α i)) (hι.comp hα) hmapK (fun k => ι (a k)) (by`. Introduce `φ hφ`. Establish `h1 : ∏ i, (Polynomial.X - Polynomial.C (φ (rr i))) = ∏ i, (Polynomial.X - Polynomial.C (ι (α i)))`. Rewrite using `[← hmapK, ← hφ, ← Polynomial.map_map, hfac, Polynomial.map_prod]`.

Simplify using the standard rewrite rules. Establish `h2 : ∀ i, ∃ j, φ (rr i) = ι (α j)`. Introduce `i`. Establish `h3 : (∏ j, (Polynomial.X - Polynomial.C (ι (α j)))).eval (φ (rr i)) = 0`. Rewrite using `[← h1, Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_zero (mem_univ i) (by simp)`. Rewrite `h3` using `[Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj⟩` from `h3`. Conclude with `⟨j, by simpa [sub_eq_zero] using hj⟩`. Use `choose σ hσ using h2`.

Establish `hy : P x = ∏ i, (Polynomial.X - Polynomial.C (α (σ i)))`. Apply `Polynomial.map_injective ι hι` to reduce the goal to its premises. Rewrite using `[hPα, Polynomial.map_prod, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Rewrite using `[← h1]`.

Conclude with `Finset.prod_congr rfl fun i _ => by rw [hσ]`. Set `y : SplitPts t P` to `⟨(x, fun i => α (σ i)), hy⟩`. Establish `hφy : ∀ z, φ z = ι (ψ y z)`. Use `letI : Algebra T K := (ι.comp (evT x)).toAlgebra`. Set `φ1 : T' →ₐ[T] K` to `{ φ with commutes' := fun τ => RingHom.congr_fun hφ τ }`.

Set `φ2 : T' →ₐ[T] K` to `{ (ι.comp (ψ y)) with commutes' := fun τ => by show ι (ψ y (algebraMap T T' τ)) = _`. Rewrite using `[show ψ y (algebraMap T T' τ) = evT x τ from RingHom.congr_fun (hψ1 y) τ]`. Use `rfl }`. Establish `h12 : φ1 = φ2` using `AlgHom.ext_of_adjoin_eq_top hadj (by`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `show φ (rr i) = ι (ψ y (rr i))`. Rewrite using `[hψ2, hσ])`. Conclude with `fun z => DFunLike.congr_fun h12 z`. Establish `h4` using `congrArg ι (ha y rfl)`. Rewrite `h4` using `[map_sum, map_zero]`.

Rewrite using `[← h4]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hφy, map_mul]`. Use the proof step `rfl)`. Use function extensionality and compare the values at `k`.

Conclude with `hι (by show ι (a k) = ι 0`. Rewrite using `[map_zero]`. Conclude with `congrFun hz k)`.
-/
theorem splitPts : StatSplitPts := by
  intro O _ _ Xs T t P hPc hPr
  rcases isEmpty_or_nonempty Xs with hX | hX
  · exact ⟨fun _ _ => 0, fun _ => (splitT T t P).zero_mem, fun f' _ => ⟨fun _ _ => 0, fun _ => T.zero_mem,
      funext fun y => (hX.elim y.1.1)⟩, fun x => hX.elim x⟩
  have hnt : Nontrivial T := inferInstance
  let evT : Xs → (T →+* O) := fun x => (Pi.evalRingHom (fun _ : Xs => O) x).comp T.val.toRingHom
  have hmonP : ∀ x, (P x).Monic := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h]; exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdegP : ∀ x, (P x).natDegree = t := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]; simp
  let PT : Polynomial T := ∑ k ∈ range (t + 1), Polynomial.monomial k ⟨fun x => (P x).coeff k, hPc k⟩
  have hcoef : ∀ k, PT.coeff k = if k ≤ t then ⟨fun x => (P x).coeff k, hPc k⟩ else 0 := by
    intro k
    simp only [PT, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range, Nat.lt_succ_iff]
  have hmap : ∀ x, PT.map (evT x) = P x := by
    intro x
    ext k
    rw [Polynomial.coeff_map, hcoef]
    split_ifs with hk
    · rfl
    · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegP]; omega)]
  have hle : PT.natDegree ≤ t := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoef, if_neg (by omega)]
  have hone : PT.coeff t = 1 := by
    rw [hcoef, if_pos le_rfl]
    refine Subtype.ext (funext fun x => ?_)
    have := (hmonP x).coeff_natDegree
    rw [hdegP] at this
    exact this
  have hmon : PT.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one t hle hone
  have hdeg : PT.natDegree = t :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hone]; exact one_ne_zero))
  have key := splitAlg T PT hmon
  rw [hdeg] at key
  obtain ⟨T', _, _, rr, hfree, hfin, hrank, hfac, hadj, huniv⟩ := key
  have hψ : ∀ y : SplitPts t P, ∃ ψ : T' →+* O, ψ.comp (algebraMap T T') = evT y.1.1 ∧
      ∀ i, ψ (rr i) = y.1.2 i := by
    intro y
    letI : Algebra T O := (evT y.1.1).toAlgebra
    obtain ⟨φ, hφ, -⟩ := huniv O y.1.2 (by
      show PT.map (evT y.1.1) = _
      rw [hmap]; exact y.2)
    exact ⟨φ.toRingHom, RingHom.ext fun τ => φ.commutes τ, hφ⟩
  choose ψ hψ1 hψ2 using hψ
  let Ψ : T' →+* (SplitPts t P → O) := Pi.ringHom ψ
  let bas : Module.Basis (Fin t.factorial) T T' := Module.finBasisOfFinrankEq T T' hrank
  have hΨa : ∀ τ : T, Ψ (algebraMap T T' τ) = fun y => τ.1 y.1.1 :=
    fun τ => funext fun y => RingHom.congr_fun (hψ1 y) τ
  have hrange : ∀ f' ∈ splitT T t P, ∃ z, Ψ z = f' := by
    intro f' hf'
    induction hf' using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨f, hf, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨algebraMap T T' ⟨f, hf⟩, hΨa _⟩
      · exact ⟨rr i, funext fun y => hψ2 y i⟩
    | algebraMap c => exact ⟨algebraMap T T' (algebraMap O T c), hΨa _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  have hmemΨ : ∀ z, Ψ z ∈ splitT T t P := by
    intro z
    have hz : z ∈ Algebra.adjoin T (Set.range rr) := hadj ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have h1 : Ψ (rr i) = splitRoot t P i := funext fun y => hψ2 y i
      rw [h1]
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
    | algebraMap τ =>
      rw [hΨa]
      exact Algebra.subset_adjoin (Or.inl ⟨τ.1, τ.2, rfl⟩)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨fun k => Ψ (bas k), fun k => hmemΨ _, ?_, ?_⟩
  · intro f' hf'
    obtain ⟨z, rfl⟩ := hrange f' hf'
    refine ⟨fun k => (bas.repr z k).1, fun k => (bas.repr z k).2, ?_⟩
    conv_lhs => rw [← bas.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hΨa]
  · intro x a ha
    let K := FractionRing O
    let ι : O →+* K := algebraMap O K
    have hι : Function.Injective ι := IsFractionRing.injective O K
    obtain ⟨α, hα, hPα⟩ := hPr x
    have hmapK : PT.map (ι.comp (evT x)) = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
      rw [← Polynomial.map_map, hmap, hPα, Polynomial.map_prod]; simp
    have sf := splitFibre T T' K PT hmon
    rw [hdeg] at sf
    have hz := sf rr hfac hadj bas (ι.comp (evT x)) (fun i => ι (α i)) (hι.comp hα) hmapK
      (fun k => ι (a k)) (by
      intro φ hφ
      have h1 : ∏ i, (Polynomial.X - Polynomial.C (φ (rr i))) =
          ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
        rw [← hmapK, ← hφ, ← Polynomial.map_map, hfac, Polynomial.map_prod]; simp
      have h2 : ∀ i, ∃ j, φ (rr i) = ι (α j) := by
        intro i
        have h3 : (∏ j, (Polynomial.X - Polynomial.C (ι (α j)))).eval (φ (rr i)) = 0 := by
          rw [← h1, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (mem_univ i) (by simp)
        rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h3
        obtain ⟨j, -, hj⟩ := h3
        exact ⟨j, by simpa [sub_eq_zero] using hj⟩
      choose σ hσ using h2
      have hy : P x = ∏ i, (Polynomial.X - Polynomial.C (α (σ i))) := by
        apply Polynomial.map_injective ι hι
        rw [hPα, Polynomial.map_prod, Polynomial.map_prod]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rw [← h1]
        exact Finset.prod_congr rfl fun i _ => by rw [hσ]
      let y : SplitPts t P := ⟨(x, fun i => α (σ i)), hy⟩
      have hφy : ∀ z, φ z = ι (ψ y z) := by
        letI : Algebra T K := (ι.comp (evT x)).toAlgebra
        let φ1 : T' →ₐ[T] K := { φ with commutes' := fun τ => RingHom.congr_fun hφ τ }
        let φ2 : T' →ₐ[T] K :=
          { (ι.comp (ψ y)) with
            commutes' := fun τ => by
              show ι (ψ y (algebraMap T T' τ)) = _
              rw [show ψ y (algebraMap T T' τ) = evT x τ from RingHom.congr_fun (hψ1 y) τ]
              rfl }
        have h12 : φ1 = φ2 := AlgHom.ext_of_adjoin_eq_top hadj (by
          rintro _ ⟨i, rfl⟩
          show φ (rr i) = ι (ψ y (rr i))
          rw [hψ2, hσ])
        exact fun z => DFunLike.congr_fun h12 z
      have h4 := congrArg ι (ha y rfl)
      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hφy, map_mul]
      rfl)
    funext k
    exact hι (by
      show ι (a k) = ι 0
      rw [map_zero]; exact congrFun hz k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
