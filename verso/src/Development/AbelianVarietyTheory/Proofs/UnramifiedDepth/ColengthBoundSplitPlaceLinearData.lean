import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiscrPowerBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTransposeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasLenExistsMonoFp
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

/- English proof (translation)
Set `e : (J → O) ≃ₗ[O] (Fin (Fintype.card J) → O)` to `LinearEquiv.funCongrLeft O O (Fintype.equivFin J).symm`. Establish `h1` using `h _ (M.map e.toLinearMap) (N.map e.toLinearMap) (hM.map _) (hN.map _) (Submodule.map_mono hle)`. Use `Module.FinitePresentation.of_equiv (Submodule.Quotient.equiv ((N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype) (N.comap M.subtype) (e.submoduleMap M).symm ?_)` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, hz, hzy⟩, rfl⟩`. Establish `: (((e.submoduleMap M).symm y : M) : J → O) = z`. Rewrite using `[LinearEquiv.submoduleMap_symm_apply, ← hzy]`. Conclude with `e.symm_apply_apply z`.

Conclude with `this ▸ hz`. Introduce `hx`. Conclude with `⟨e.submoduleMap M x, ⟨x, hx, rfl⟩, (e.submoduleMap M).symm_apply_apply x⟩`.
-/
private theorem lav_fp {O : Type} [CommRing O] {J : Type} [Fintype J]
    (h : ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M →
      Module.FinitePresentation O (M ⧸ N.comap M.subtype))
    (M N : Submodule O (J → O)) (hM : M.FG) (hN : N.FG) (hle : N ≤ M) :
    Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  let e : (J → O) ≃ₗ[O] (Fin (Fintype.card J) → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin J).symm
  have h1 := h _ (M.map e.toLinearMap) (N.map e.toLinearMap) (hM.map _) (hN.map _)
    (Submodule.map_mono hle)
  refine Module.FinitePresentation.of_equiv
    (Submodule.Quotient.equiv ((N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype) (N.comap M.subtype)
      (e.submoduleMap M).symm ?_)
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have : (((e.submoduleMap M).symm y : M) : J → O) = z := by
      rw [LinearEquiv.submoduleMap_symm_apply, ← hzy]
      exact e.symm_apply_apply z
    exact this ▸ hz
  · intro hx
    exact ⟨e.submoduleMap M x, ⟨x, hx, rfl⟩, (e.submoduleMap M).symm_apply_apply x⟩

/- English proof (translation)
Establish `hD0 : 0 < D` using `hD ▸ Real.rpow_pos_of_pos hP0 _`. Establish `hD1 : D ≤ 1` using `hD ▸ Real.rpow_le_one hP0.le hP1 hvd`. Establish `h0 : 0 < P ^ ((n * rm) / q)` using `Real.rpow_pos_of_pos hP0 _`. Establish `h1 : D ^ (rp + rm') ≤ D ^ h` using `pow_le_pow_of_le_one hD0.le hD1 hh`. Establish `h2 : c ^ 2 * D ^ rm' ≤ X ^ 2`.

Establish `: c ^ 2 * D ^ rm' * D ^ rp ≤ X ^ 2 * D ^ rp`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right this (pow_pos hD0 _)`. Establish `h3 : (P ^ (n * rm * (1 / q + vd / 2))) ^ 2 = (P ^ ((n * rm) / q)) ^ 2 * D ^ rm'`. Rewrite using `[hD, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0, ← hrm]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `(pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hP0 _).le hX two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[h3]`.

Use `le_trans ?_ h2` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le (hcw.trans hc) 2) (pow_pos hD0 _).le`.
-/
private theorem lav_num (P D c cw X : ℝ) (n rm vd q : ℝ) (rp rm' h : ℕ) (hrm : rm = rm')
    (hP0 : 0 < P) (hP1 : P ≤ 1) (hvd : 0 ≤ n * vd) (hD : D = P ^ (n * vd)) (hh : h ≤ rp + rm')
    (hcw : P ^ ((n * rm) / q) ≤ cw) (hc : cw ≤ c) (hX : 0 ≤ X)
    (hl : c ^ 2 * D ^ h ≤ X ^ 2 * D ^ rp) : P ^ (n * rm * (1 / q + vd / 2)) ≤ X := by
  have hD0 : 0 < D := hD ▸ Real.rpow_pos_of_pos hP0 _
  have hD1 : D ≤ 1 := hD ▸ Real.rpow_le_one hP0.le hP1 hvd
  have h0 : 0 < P ^ ((n * rm) / q) := Real.rpow_pos_of_pos hP0 _
  have h1 : D ^ (rp + rm') ≤ D ^ h := pow_le_pow_of_le_one hD0.le hD1 hh
  have h2 : c ^ 2 * D ^ rm' ≤ X ^ 2 := by
    have : c ^ 2 * D ^ rm' * D ^ rp ≤ X ^ 2 * D ^ rp := by
      calc c ^ 2 * D ^ rm' * D ^ rp = c ^ 2 * D ^ (rp + rm') := by ring
        _ ≤ c ^ 2 * D ^ h := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ ≤ _ := hl
    exact le_of_mul_le_mul_right this (pow_pos hD0 _)
  have h3 : (P ^ (n * rm * (1 / q + vd / 2))) ^ 2 = (P ^ ((n * rm) / q)) ^ 2 * D ^ rm' := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le,
      ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0, ← hrm]
    congr 1
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hP0 _).le hX two_ne_zero).1 ?_
  rw [h3]
  refine le_trans ?_ h2
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le (hcw.trans hc) 2) (pow_pos hD0 _).le

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t vd hvd rp rm W hW hW'`. Establish `hp0 : 0 < v (algebraMap O C (p : O))`. Rewrite using `[map_natCast, zero_lt_iff, Ne, map_eq_zero]`. Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions. Establish `hp1 : v (algebraMap O C (p : O)) < 1` using `lt_of_le_of_ne (hv.map_le_one _) fun h => (Fact.out : ¬IsUnit (p : O)) (hv.isUnit_iff_valuation_eq_one.2 h)`.

Take `⟨-, -, α, b, hb⟩` from `GlobalTheory.PlaceMono.place_monogenic p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩`. Establish `hrm : ∀ τ ∈ Emb (O` using `O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm := by`. Introduce `τ hτ`. Take `⟨W', hW''⟩` from `hW' τ hτ`. Establish `h1` using `(GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rm ρG τ W' hW'').2.2`.

Establish `h2` using `(GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG ((RingHom.mapMatrix (Int.castRingHom O)).comp N) (H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom) hL.eqB hL.eqA ((algebraMap O C).comp τ)).1`. Rewrite `h2` using `[h1]`. Conclude with `le_of_le_of_eq (Nat.le_add_left _ _) h2.symm`. Take `⟨cw, hcw, hcwb⟩` from `GlobalTheory.T.abelianPart_cokernel_length_le p C v O hv OE cp hU g H hL.noPad.1 hL.noPad.2 w t rm hrm`. Take `⟨h, ψ, hh, hψ, f, hf⟩` from `GlobalTheory.T.exists_abelian_torus_generators_at_place p C v O hv OE cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm`.

Take `⟨hinj, hvd0, hD⟩` from `GlobalTheory.PowerBasisDiscr.discr_power_basis p C v O hv OE w t vd hvd α b hb`. Take `⟨hex, hmono, hfp⟩` from `GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv`. Establish `hres` using `fun j => GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rp ρG _ (W j) (hW j)`. Establish `hstab : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), ∃ u' : Fin d → O, ∀ j, Pdiv.ChartF.res (W j) u' = tauExt ((t j : Emb (O` using `O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) u := by`. Introduce `x u`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, fun j => by simp⟩`. Consider the case `tmul c a`. Use `⟨algebraMap ℤ_[p] O c • ((ρG a)ᵀ *ᵥ u), fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, (hres j).2.1, smul_smul]`.

Simplify using `[tauExt, Algebra.ofId_apply]`. Consider the case `add x y hx hy`. Take `⟨u1, h1⟩` from `hx`. Take `⟨u2, h2⟩` from `hy`. Conclude with `⟨u1 + u2, fun j => by rw [map_add, h1, h2, map_add, add_smul]⟩`.

Set `κ : (Fin d → O) →ₗ[O] (Fin w.n × Fin rp → O)` to `LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))`. Establish `hκa : ∀ u y, κ u y = Pdiv.ChartF.res (W y.1) u y.2` using `fun u y => rfl`. Establish `hMfg : (LinearMap.range κ).FG`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`.

Establish `hmem : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), (fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O` using `O) w.e) : OE →+* O) x * κ u y) ∈ LinearMap.range κ := by`. Introduce `x u`. Take `⟨u', hu'⟩` from `hstab x u`. Use `⟨u', funext fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hκa, hκa, hu']`.

Both sides reduce to the same expression. Take `⟨c, hc⟩` from `hex _ (lav_fp hfp (LinearMap.range κ) (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2)) hMfg (Submodule.fg_span (Set.finite_range _)) (by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, rfl⟩`. Use `hmem (α ^ (q.1 : ℕ)) (ψ q.2)` as an intermediate fact.

Simplify using `only [map_pow] at this`. Conclude with `this))`. Establish `hcc : cw ≤ c` using `hmono _ _ f cw c hf hcw hc`. Establish `hcw0 : (0 : ℝ) < cw` using `lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) hcwb`. Establish `hc0 : c ≠ 0` using `(lt_of_lt_of_le (by exact_mod_cast hcw0) hcc : (0 : NNReal) < c).ne'`.

Take `⟨x, hx, hineq⟩` from `GlobalTheory.T.lattice_inequality_valuation_integers C v O hv ⟨_, hp0, hp1⟩ w.n rp h (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) hinj (LinearMap.range κ) hMfg (by rintro _ ⟨u, rfl⟩; exact hmem α u) (by`. Introduce `τ z`. Take `⟨u, hu⟩` from `(hres τ).1 z`. Conclude with `⟨κ u, ⟨u, rfl⟩, fun i => by rw [hκa, hu]⟩)`. Use the proof step `(fun l => κ (ψ l)) (fun l => ⟨ψ l, rfl⟩) c hc0 hc`.

Establish `hxs : ∀ j, ∃ y, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) y ∧ x j ≤ y`. Introduce `j`. Establish `hle : Submodule.span O (Set.range fun l => fun i => κ (ψ l) (j, i)) ≤ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Conclude with `hψ l j`. Take `⟨y, hy⟩` from `hex ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))`. Conclude with `⟨y, hy, hmono _ _ (Submodule.factor hle) _ _ (Submodule.factor_surjective hle) (hx j) hy⟩`. Use `choose xs hxs1 hxs2 using hxs`. Use `⟨xs, hxs1, le_trans ?_ (Finset.prod_le_prod' fun j _ => hxs2 j)⟩` and prove the remaining obligations.

Rewrite using `[← NNReal.coe_le_coe, NNReal.coe_rpow]`. Use `lav_num _ _ c cw _ _ _ _ _ rp rm h rfl (by exact_mod_cast hp0) (by exact_mod_cast hp1.le) hvd0 hD hh hcwb (by exact_mod_cast hcc) (NNReal.coe_nonneg _) ?_` and prove the remaining obligations. Conclude with `hineq` after adjusting the coercions.
-/
theorem colength_bound_linDat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t vd hvd rp rm W hW hW'
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast, zero_lt_iff, Ne, map_eq_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : v (algebraMap O C (p : O)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) fun h =>
      (Fact.out : ¬IsUnit (p : O)) (hv.isUnit_iff_valuation_eq_one.2 h)
  obtain ⟨-, -, α, b, hb⟩ := GlobalTheory.PlaceMono.place_monogenic p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  have hrm : ∀ τ ∈ Emb (O := O) w.bar,
      eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm := by
    intro τ hτ
    obtain ⟨W', hW''⟩ := hW' τ hτ
    have h1 := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rm ρG τ W' hW'').2.2
    have h2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG
      ((RingHom.mapMatrix (Int.castRingHom O)).comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp τ)).1
    rw [h1] at h2
    exact le_of_le_of_eq (Nat.le_add_left _ _) h2.symm
  obtain ⟨cw, hcw, hcwb⟩ := GlobalTheory.T.abelianPart_cokernel_length_le p C v O hv OE cp hU g H hL.noPad.1 hL.noPad.2 w t rm hrm
  obtain ⟨h, ψ, hh, hψ, f, hf⟩ := GlobalTheory.T.exists_abelian_torus_generators_at_place p C v O hv OE cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm
  obtain ⟨hinj, hvd0, hD⟩ := GlobalTheory.PowerBasisDiscr.discr_power_basis p C v O hv OE w t vd hvd α b hb
  obtain ⟨hex, hmono, hfp⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  have hres := fun j => GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rp ρG _ (W j) (hW j)
  have hstab : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), ∃ u' : Fin d → O, ∀ j,
      Pdiv.ChartF.res (W j) u' = tauExt ((t j : Emb (O := O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) u := by
    intro x u
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, fun j => by simp⟩
    | tmul c a =>
      refine ⟨algebraMap ℤ_[p] O c • ((ρG a)ᵀ *ᵥ u), fun j => ?_⟩
      rw [map_smul, (hres j).2.1, smul_smul]
      simp [tauExt, Algebra.ofId_apply]
    | add x y hx hy =>
      obtain ⟨u1, h1⟩ := hx
      obtain ⟨u2, h2⟩ := hy
      exact ⟨u1 + u2, fun j => by rw [map_add, h1, h2, map_add, add_smul]⟩
  let κ : (Fin d → O) →ₗ[O] (Fin w.n × Fin rp → O) :=
    LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))
  have hκa : ∀ u y, κ u y = Pdiv.ChartF.res (W y.1) u y.2 := fun u y => rfl
  have hMfg : (LinearMap.range κ).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hmem : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), (fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) x * κ u y) ∈ LinearMap.range κ := by
    intro x u
    obtain ⟨u', hu'⟩ := hstab x u
    refine ⟨u', funext fun y => ?_⟩
    rw [hκa, hκa, hu']
    rfl
  obtain ⟨c, hc⟩ := hex _ (lav_fp hfp (LinearMap.range κ)
    (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2))
    hMfg (Submodule.fg_span (Set.finite_range _)) (by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      have := hmem (α ^ (q.1 : ℕ)) (ψ q.2)
      simp only [map_pow] at this
      exact this))
  have hcc : cw ≤ c := hmono _ _ f cw c hf hcw hc
  have hcw0 : (0 : ℝ) < cw := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) hcwb
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hcw0) hcc : (0 : NNReal) < c).ne'
  obtain ⟨x, hx, hineq⟩ := GlobalTheory.T.lattice_inequality_valuation_integers C v O hv ⟨_, hp0, hp1⟩ w.n rp h
    (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) hinj (LinearMap.range κ) hMfg
    (by rintro _ ⟨u, rfl⟩; exact hmem α u)
    (by
      intro τ z
      obtain ⟨u, hu⟩ := (hres τ).1 z
      exact ⟨κ u, ⟨u, rfl⟩, fun i => by rw [hκa, hu]⟩)
    (fun l => κ (ψ l)) (fun l => ⟨ψ l, rfl⟩) c hc0 hc
  have hxs : ∀ j, ∃ y, HasLen v O ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) y ∧ x j ≤ y := by
    intro j
    have hle : Submodule.span O (Set.range fun l => fun i => κ (ψ l) (j, i)) ≤
        Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k)) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hψ l j
    obtain ⟨y, hy⟩ := hex ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k)))
      (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
    exact ⟨y, hy, hmono _ _ (Submodule.factor hle) _ _ (Submodule.factor_surjective hle) (hx j) hy⟩
  choose xs hxs1 hxs2 using hxs
  refine ⟨xs, hxs1, le_trans ?_ (Finset.prod_le_prod' fun j _ => hxs2 j)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine lav_num _ _ c cw _ _ _ _ _ rp rm h rfl (by exact_mod_cast hp0) (by exact_mod_cast hp1.le) hvd0 hD hh
    hcwb (by exact_mod_cast hcc) (NNReal.coe_nonneg _) ?_
  exact_mod_cast hineq

end GlobalTheory.ChF
