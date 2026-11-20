import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HighWtEmb

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ hBC N ν hν`. Use `haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν`. Use `haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'`. Set `b` to `(Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)`. Use `⟨_, b, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha i`. Use `choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)`. Set `g : dualWeyl O N N ν` to `∑ j, c j • b j`. Establish `hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0`.

Rewrite using `[← ha]`. Simplify using `only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]`. Take `⟨h, hh, hgh⟩` from `(hBC O ϖ hϖ N ν hν).2 g g.2 hg`. Establish `hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν)` using `Subtype.ext (by simpa using hgh)`. Establish `hci : c i = ϖ * b.repr ⟨h, hh⟩ i`.

Establish `h2` using `congrArg (fun x => b.repr x i) hgh'`. Simplify using `only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2`. Rewrite using `[← h2]`. Simplify using `[g, map_sum, Finsupp.single_apply]`. Rewrite using `[← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]`.
-/
theorem exists_basis_reduction_linearIndependent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → GlobalTheory.HighWt.BaseChange →
    ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∃ (n : ℕ) (b : Module.Basis (Fin n) O (dualWeyl O N N ν)),
      LinearIndependent (O ⧸ Ideal.span {ϖ})
        (fun i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b i : MvPolynomial (Fin N × Fin N) O)) := by
  intro O _ _ _ ϖ hϖ hBC N ν hν
  haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν
  haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)
  refine ⟨_, b, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)
  let g : dualWeyl O N N ν := ∑ j, c j • b j
  have hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0 := by
    rw [← ha]
    simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]
  obtain ⟨h, hh, hgh⟩ := (hBC O ϖ hϖ N ν hν).2 g g.2 hg
  have hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν) := Subtype.ext (by simpa using hgh)
  have hci : c i = ϖ * b.repr ⟨h, hh⟩ i := by
    have h2 := congrArg (fun x => b.repr x i) hgh'
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    simp [g, map_sum, Finsupp.single_apply]
  rw [← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]

/- English proof (translation)
Set `B` to `Module.Basis.span hv`. Use `⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩` and prove the remaining obligations. Establish `h` using `(LinearMap.exists_extend (B.coord l)).choose_spec`. Establish `hvi : v i ∈ Submodule.span k (Set.range v)` using `Submodule.subset_span ⟨i, rfl⟩`. Establish `h1` using `LinearMap.congr_fun h ⟨v i, hvi⟩`.

Establish `hBi : B i = ⟨v i, hvi⟩` using `Module.Basis.span_apply hv i`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1`. Rewrite using `[h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]`.
-/
theorem exists_dual_family (k : Type) [Field k] (σ : Type) (κ : Type) [DecidableEq κ] (v : κ → MvPolynomial σ k)
    (hv : LinearIndependent k v) : ∃ ψ : κ → (MvPolynomial σ k →ₗ[k] k), ∀ i l, ψ l (v i) = if i = l then 1 else 0 := by
  let B := Module.Basis.span hv
  refine ⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩
  have h := (LinearMap.exists_extend (B.coord l)).choose_spec
  have hvi : v i ∈ Submodule.span k (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have h1 := LinearMap.congr_fun h ⟨v i, hvi⟩
  have hBi : B i = ⟨v i, hvi⟩ := Module.Basis.span_apply hv i
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
  rw [h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[Finsupp.curry_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single τ]`. Conclude with `Finsupp.mapDomain_apply (fun _ _ h => congrArg Prod.snd h) _ _`. Introduce `ρ _ hρ`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises.

Introduce and unpack `⟨t, ht⟩`. Conclude with `hρ (congrArg Prod.fst ht)`. Simplify using the standard rewrite rules.
-/
theorem curry_sum_mapDomain {ι σ : Type} [Fintype ι] [DecidableEq ι] (F : ι → σ →₀ ℕ) (τ : ι) :
    (∑ ρ, Finsupp.mapDomain (fun s : σ => ((ρ, s) : ι × σ)) (F ρ)).curry τ = F τ := by
  classical
  ext s
  rw [Finsupp.curry_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (fun _ _ h => congrArg Prod.snd h) _ _
  · intro ρ _ hρ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨t, ht⟩
    exact hρ (congrArg Prod.fst ht)
  · simp

/- English proof (translation)
Introduce `k _ ι _ _ σ φ`. Set `w : ((ι × σ) →₀ ℕ) → k` to `fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)`. Set `Φ` to `(MvPolynomial.basisMonomials (ι × σ) k).constr k w`. Establish `hmono : ∀ M c, Φ (monomial M c) = c * w M`. Introduce `M c`.

Establish `: (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M)`. Rewrite using `[MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, Module.Basis.constr_basis, smul_eq_mul]`. Establish `hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1)`. Introduce `τ m c`.

Rewrite using `[← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]`. Use `⟨Φ, fun f => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) = ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (coeff m (f τ))`. Introduce `τ`. Use `conv_lhs => rw [as_sum (f τ)]`.

Simplify using `only [map_sum, rename_monomial]`. Establish `h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, coeff m (f τ) * φ τ (monomial m 1)`. Introduce `τ`. Use `conv_lhs => rw [as_sum (f τ)]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun m _ => hφ τ m _`. Rewrite using `[Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum, Finset.prod_univ_sum, map_sum]`. Use `Finset.sum_congr rfl fun F _ => ?_` and prove the remaining obligations. Rewrite using `[← monomial_sum_prod, hmono]`. Simplify using `only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]`.
-/
theorem exists_prod_functional : ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type)
    (φ : ι → (MvPolynomial σ k →ₗ[k] k)), ∃ Φ : MvPolynomial (ι × σ) k →ₗ[k] k,
      ∀ f : ι → MvPolynomial σ k, Φ (∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ)) = ∏ τ, φ τ (f τ) := by
  intro k _ ι _ _ σ φ
  classical
  let w : ((ι × σ) →₀ ℕ) → k := fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)
  let Φ := (MvPolynomial.basisMonomials (ι × σ) k).constr k w
  have hmono : ∀ M c, Φ (monomial M c) = c * w M := by
    intro M c
    have : (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M) := by
      rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1) := by
    intro τ m c
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  refine ⟨Φ, fun f => ?_⟩
  have h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) =
      ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (coeff m (f τ)) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, coeff m (f τ) * φ τ (monomial m 1) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ τ m _
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum,
    Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← monomial_sum_prod, hmono]
  simp only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]

/- English proof (translation)
Introduce `k _ ι _ _ σ κ _ v hv`. Use `choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha l`. Take `⟨Φ, hΦ⟩` from `exists_prod_functional k ι σ (fun τ => ψ τ (l τ))`.

Establish `h` using `congrArg Φ ha`. Rewrite `h` using `[map_sum, map_zero]`. Simplify using `only [map_smul, hΦ, hψ, smul_eq_mul] at h`. Rewrite `h` using `[Finset.sum_eq_single l]`. Simplify using `using h`.

Introduce `p _ hp`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hp (funext hc)`.

Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem linearIndependent_prod_rename : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (v : ∀ τ, κ τ → MvPolynomial σ k), (∀ τ, LinearIndependent k (v τ)) →
    LinearIndependent k (fun p : (∀ τ, κ τ) => ∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (v τ (p τ))) := by
  intro k _ ι _ _ σ κ _ v hv
  classical
  choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)
  rw [Fintype.linearIndependent_iff]
  intro a ha l
  obtain ⟨Φ, hΦ⟩ := exists_prod_functional k ι σ (fun τ => ψ τ (l τ))
  have h := congrArg Φ ha
  rw [map_sum, map_zero] at h
  simp only [map_smul, hΦ, hψ, smul_eq_mul] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro p _ hp
    obtain ⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by
      by_contra hc
      push_neg at hc
      exact hp (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  · simp

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [blockRed, MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p s hp => simp [hp, blockRed] at *`.
-/
theorem blockRed_eq (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, blockRed] at *

/- English proof (translation)
Introduce `O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy`. Use `haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Use `letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`. Establish `hb` using `fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)`. Use `choose n b hli using hb`.

Set `B` to `Basis.piTensorProduct b`. Establish `hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O))`. Introduce `p`. Simplify using `only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]`. Conclude with `Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _`.

Establish `hL` using `linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ)) (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli`. Rewrite `hL` using `[Fintype.linearIndependent_iff]`. Establish `hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0`. Rewrite using `[← hy]`. Use `conv_rhs => rw [← B.sum_repr y]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hred]`. Conclude with `algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _`. Establish `hc` using `hL _ hy'`.

Rewrite using `[← B.sum_repr y]`. Use `Submodule.sum_mem _ fun p _ => ?_` and prove the remaining obligations. Establish `hp : B.repr y p ∈ Ideal.span {ϖ}` using `Ideal.Quotient.eq_zero_iff_mem.mp (hc p)`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.mp hp`. Rewrite using `[← hd, mul_comm, mul_smul]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top`.
-/
theorem mem_smul_top_of_redT_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hb := fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)
  choose n b hli using hb
  let B := Basis.piTensorProduct b
  have hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) := by
    intro p
    simp only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
    exact Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _
  have hL := linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ))
    (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli
  rw [Fintype.linearIndependent_iff] at hL
  have hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0 := by
    rw [← hy]
    conv_rhs => rw [← B.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.map_smul, hred]
    exact algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _
  have hc := hL _ hy'
  rw [← B.sum_repr y]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hp : B.repr y p ∈ Ideal.span {ϖ} := Ideal.Quotient.eq_zero_iff_mem.mp (hc p)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hp
  rw [← hd, mul_comm, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

end GlobalTheory.HighWtEmb

end
