import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearRelationDescendBaseFieldStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

namespace GlobalTheory.PointsDetectAlg

/- English proof (translation)
Assume the negation of the conclusion as `hw0`. Set `wP : ι → PAt φ` to `w`. Establish `hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0`. Introduce `L _ _ _ σ y`. Take `⟨z, u, hu, hz⟩` from `GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom) (fun a => by simp [toCp_algebraMap]) y a n`.

Establish `h1` using `hw z`. Simplify using `only [hz _ (hg _)] at h1`. Establish `h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0`. Rewrite using `[Finset.mul_sum, ← h1]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 h2).resolve_left hu`. Set `K` to `algebraicClosure c.F (PAt φ)`. Set `V : Set (ι → K)` to `{v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L) (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}`.

Take `⟨d, hd0, hd⟩` from `GlobalTheory.T.exists_linear_relation_descend_base_field K (PAt φ) ι V wP hw0 (by`. Introduce and unpack `v ⟨L, _, _, _, σ, y, hv⟩`. Simplify `hrel L σ y)` using `only [IntermediateField.algebraMap_apply, hv]`. Establish `hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0`. Introduce `L _ _ _ σ y`.

Establish `hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R` using `c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V := ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩`. Use `congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)` as an intermediate fact. Simplify using `using this`. Set `K0` to `IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))`. Establish `hfin : FiniteDimensional c.F K0` using `IntermediateField.finiteDimensional_adjoin (fun x hx => by`.

Take `⟨s, rfl⟩` from `hx`. Conclude with `(mem_algebraicClosure_iff.1 (d s).2).isIntegral)`. Set `bs` to `Module.finBasis c.F K0`. Set `m` to `Module.finrank c.F K0`. Set `e : Fin m → PAt φ` to `fun t => (bs t : PAt φ)`.

Establish `he : LinearIndependent c.F e` using `bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)`. Establish `hea : ∀ t, IsAlgebraic c.F (e t)` using `fun t => (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val`. Establish `dmem : ∀ s, (d s : PAt φ) ∈ K0` using `fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩`. Set `q : ι → Fin m → c.F` to `fun s t => bs.repr ⟨d s, dmem s⟩ t`. Establish `hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t`.

Introduce `s`. Establish `h` using `congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)`. Simplify using `only [IntermediateField.coe_sum, Algebra.smul_def] at h`. Conclude with `h.symm`. Set `hh : Fin m → Rul Xo c` to `fun t => ∑ s, q s t • g s`.

Establish `hhsec : ∀ t, hh t ∈ sec Xo c a n` using `fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)`. Establish `hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m), evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y`. Introduce `L _ _ y t`. Use `map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (fun s => q s t • g s) Finset.univ` as an intermediate fact. Simplify using `only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this`.

Conclude with `this`. Establish `hzero : ∀ t, hh t = 0`. Introduce `t`. Use `GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_` and prove the remaining obligations. Use `GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by` as an intermediate fact.

Rewrite using `[← hdrel L σ y]`. Simplify using `only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use the proof step `ring)`.

Conclude with `congrFun this t`. Establish `hq0 : ∀ s t, q s t = 0` using `fun s t => Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s`. Apply `hd0` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hq s]`. Simplify using `[hq0]`.
-/
theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (hI : IntAll Xo c)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {ι : Type} [Fintype ι] (g : ι → Rul Xo c) (hg : ∀ s, g s ∈ sec Xo c a n)
    (hli : LinearIndependent c.F g) (w : ι → ℂ_[p])
    (hw : ∀ z : PtC Xo c φ, ∑ s, w s * valC z.1 (g s) = 0) : w = 0 := by
  by_contra hw0
  let wP : ι → PAt φ := w
  have hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    obtain ⟨z, u, hu, hz⟩ := GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom)
      (fun a => by simp [toCp_algebraMap]) y a n
    have h1 := hw z
    simp only [hz _ (hg _)] at h1
    have h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      change u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))
      ring
    exact (mul_eq_zero.1 h2).resolve_left hu
  let K := algebraicClosure c.F (PAt φ)
  let V : Set (ι → K) := {v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L)
    (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_linear_relation_descend_base_field K (PAt φ) ι V wP hw0 (by
    rintro v ⟨L, _, _, _, σ, y, hv⟩
    simpa only [IntermediateField.algebraMap_apply, hv] using hrel L σ y)

  have hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    have hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V :=
      ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩
    have := congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)
    simpa using this

  let K0 := IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))
  have hfin : FiniteDimensional c.F K0 := IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact (mem_algebraicClosure_iff.1 (d s).2).isIntegral)
  let bs := Module.finBasis c.F K0
  let m := Module.finrank c.F K0
  let e : Fin m → PAt φ := fun t => (bs t : PAt φ)
  have he : LinearIndependent c.F e :=
    bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)
  have hea : ∀ t, IsAlgebraic c.F (e t) := fun t =>
    (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val
  have dmem : ∀ s, (d s : PAt φ) ∈ K0 := fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩
  let q : ι → Fin m → c.F := fun s t => bs.repr ⟨d s, dmem s⟩ t
  have hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t := by
    intro s
    have h := congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)
    simp only [IntermediateField.coe_sum, Algebra.smul_def] at h
    exact h.symm
  let hh : Fin m → Rul Xo c := fun t => ∑ s, q s t • g s
  have hhsec : ∀ t, hh t ∈ sec Xo c a n := fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)
  have hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m),
      evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y := by
    intro L _ _ y t
    have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
      (fun s => q s t • g s) Finset.univ
    simp only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this
    exact this
  have hzero : ∀ t, hh t = 0 := by
    intro t
    refine GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_
    have := GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by
      rw [← hdrel L σ y]
      simp only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    exact congrFun this t
  have hq0 : ∀ s t, q s t = 0 := fun s t =>
    Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s
  apply hd0
  funext s
  apply Subtype.ext
  rw [hq s]
  simp [hq0]

end GlobalTheory.PointsDetectAlg

namespace GlobalTheory.PointsDetectAlg

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

/- English proof (translation)
Introduce `D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx`. Set `bV` to `Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))`. Set `B` to `Algebra.TensorProduct.basis (NX.KB S i b) bV`. Set `r` to `B.repr x`. Set `g : r.support → T0.R ((j : ℕ) + 1)` to `fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))`.

Establish `hx' : x = ∑ s : r.support, r s • B s` using `by conv_lhs => rw [← B.linearCombination_repr x]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Conclude with `(Finset.sum_coe_sort r.support (fun s => r s • B s)).symm`. Establish `hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0`. Introduce `z`.

Establish `h` using `hx z`. Rewrite `h` using `[hx']`. Establish `e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s)` using `map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ`. Rewrite using `[← h]`. Use `Eq.trans ?_ e.symm` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm` and prove the remaining obligations. Use `congr 1`. Establish `hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _)` using `Algebra.TensorProduct.basis_apply _ _`. Use `Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm` and prove the remaining obligations.

Use `Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm` and prove the remaining obligations. Conclude with `(one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)`. Establish `hli : LinearIndependent T0.Q.c.F g`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `cf hcf s`.

Establish `h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0`. Rewrite using `[← hcf, map_sum]`. Simplify using `only [cuspOf_smul, RingEquiv.apply_symm_apply]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0` using `(cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)`. Establish `h3` using `Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s`. Simplify using `using h3`. Establish `hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c` using `fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩`. Establish `hw` using `core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli (fun s => iC (r s)) hval`.

Establish `hr : ∀ s : r.support, r s = 0` using `fun s => (map_eq_zero iC).1 (congrFun hw s)`. Rewrite using `[hx']`. Conclude with `(Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl`.
-/
theorem detects : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), Detects YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx
  let bV := Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))
  let B := Algebra.TensorProduct.basis (NX.KB S i b) bV
  let r := B.repr x
  let g : r.support → T0.R ((j : ℕ) + 1) := fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))
  have hx' : x = ∑ s : r.support, r s • B s := by
    conv_lhs => rw [← B.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_coe_sort r.support (fun s => r s • B s)).symm
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0 := by
    intro z
    have h := hx z
    rw [hx'] at h
    have e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s) :=
      map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ
    rw [← h]
    refine Eq.trans ?_ e.symm
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm
    congr 1
    have hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _) :=
      Algebra.TensorProduct.basis_apply _ _
    refine Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm
    refine Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm
    exact (one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)
  have hli : LinearIndependent T0.Q.c.F g := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf s
    have h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0 := by
      rw [← hcf, map_sum]
      simp only [cuspOf_smul, RingEquiv.apply_symm_apply]
      push_cast
      rfl
    have h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0 :=
      (cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)
    have h3 := Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s
    simpa using h3
  have hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩
  have hw := core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli
    (fun s => iC (r s)) hval
  have hr : ∀ s : r.support, r s = 0 := fun s => (map_eq_zero iC).1 (congrFun hw s)
  rw [hx']
  exact (Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl

end GlobalTheory.PointsDetectAlg

end
