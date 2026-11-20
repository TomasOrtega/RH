import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing

noncomputable section

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

/- English proof (translation)
Set `f : (Fin r → R) →ₗ[R] M` to `Fintype.linearCombination R v`. Establish `hf : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination]`. Conclude with `hv`. Set `g : (Fin r → R) →ₗ[R] (Fin r → R)` to `d.equivFun.toLinearMap ∘ₗ f`.

Establish `hg : Function.Surjective g` using `d.equivFun.surjective.comp hf`. Establish `hgi : Function.Injective g` using `OrzechProperty.injective_of_surjective_endomorphism g hg`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `h1 : g a = g 0`.

Simplify using `only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, f, Fintype.linearCombination_apply, ha]`. Conclude with `fun i => congrFun (hgi h1) i`.
-/
theorem linearIndependent_of_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (d : Basis (Fin r) R M) (v : Fin r → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R v := by
  let f : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hv
  let g : (Fin r → R) →ₗ[R] (Fin r → R) := d.equivFun.toLinearMap ∘ₗ f
  have hg : Function.Surjective g := d.equivFun.surjective.comp hf
  have hgi : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h1 : g a = g 0 := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, f, Fintype.linearCombination_apply, ha]
  exact fun i => congrFun (hgi h1) i

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x t => simp [TWmap, TensorProduct.smul_tmul', map_mul]`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
theorem twmap_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (a : R) (z : TW R T) :
    TWmap f T (a • z) = f a • TWmap f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TWmap, TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
The claim follows from `TensorProduct.map_surjective (g := f.toLinearMap) hf (g' := LinearMap.id) (fun x => ⟨x, rfl⟩)`.
-/
theorem twmap_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (hf : Function.Surjective f) :
    Function.Surjective (TWmap f T) :=
  TensorProduct.map_surjective (g := f.toLinearMap) hf (g' := LinearMap.id) (fun x => ⟨x, rfl⟩)

end GlobalTheory.EtaleFrob

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `haveI hfreeD : Module.Free W.EE (W.DD T) := (W.DD_free T).1`. Establish `hrk : finrank W.EE (W.DD T) = finrank O ↥T.L.T` using `(W.DD_free T).2`. Take `⟨d0⟩ : Nonempty (Basis (Fin (finrank O ↥T.L.T)) RW (TW RW T))` from `⟨Algebra.TensorProduct.basis RW (Module.finBasis O ↥T.L.T)⟩`. Use `haveI hfin : Module.Finite W.EE (W.DD T) := by`. Break down `Nat.eq_zero_or_pos (finrank W.EE (W.DD T)) with h0 | h0` into its components or cases.

Use `haveI : IsEmpty (Fin (finrank O ↥T.L.T)) := by rw [← hrk, h0]; infer_instance`. Establish `hz : ∀ x : W.DD T, x = 0` using `fun x => E.jD_inj T (by`. Rewrite using `[map_zero, ← d0.sum_repr (E.jD T x)]`. Use the proof step `simp)`. Use `haveI : Subsingleton (W.DD T) := ⟨fun x y => by rw [hz x, hz y]⟩`.

Use `infer_instance`. Conclude with `Module.finite_of_finrank_pos h0`. Take `⟨r, hr⟩ : ∃ r, r = finrank W.EE (W.DD T)` from `⟨_, rfl⟩`. Take `⟨b⟩ : Nonempty (Basis (Fin r) W.EE (W.DD T))` from `⟨(Module.finBasis W.EE (W.DD T)).reindex (finCongr hr.symm)⟩`. Take `⟨d⟩ : Nonempty (Basis (Fin r) RW (TW RW T))` from `⟨d0.reindex (finCongr (hr.trans hrk).symm)⟩`.

Take `⟨c, hcdef⟩ : ∃ c : Fin r → TW RW T, ∀ j, c j = E.jD T (b j)` from `⟨_, fun _ => rfl⟩`. Establish `hjD : ∀ x : W.DD T, E.jD T x = ∑ i, E.ioE (b.repr x i) • c i`. Introduce `x`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, hcdef]`. Establish `hc : Submodule.span RW (Set.range c) = ⊤`. Rewrite using `[eq_top_iff, ← E.jD_span T, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hjD x]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))`. Take `⟨cb, hcb⟩ : ∃ cb : Basis (Fin r) RW (TW RW T), ∀ i, cb i = c i` from `⟨Basis.mk (linearIndependent_of_span d c hc) hc.ge, fun i => Basis.mk_apply _ _ i⟩`. Take `⟨c', hc'def⟩ : ∃ c' : Fin r → TW RW T, ∀ j, c' j = TWmap φR T (c j)` from `⟨_, fun _ => rfl⟩`. Establish `hTW : ∀ y : TW RW T, ∃ x, TWmap φR T x = y` using `fun y => twmap_surjective φR T hφ y`. Establish `himg : ∀ x : TW RW T, TWmap φR T x ∈ Submodule.span RW (Set.range c')`.

Introduce `x`. Establish `hx : x ∈ Submodule.span RW (Set.range c)` using `by rw [hc]; exact Submodule.mem_top`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun RW).1 hx`. Rewrite using `[← ha, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[twmap_smul, ← hc'def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))`. Establish `hc' : Submodule.span RW (Set.range c') = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Take `⟨x, hxy⟩` from `hTW y`. Rewrite using `[← hxy]`. Conclude with `himg x`. Establish `hdet : IsUnit (cb.det c')` using `cb.is_basis_iff_det.1 ⟨linearIndependent_of_span d c' hc', hc'⟩`. Take `⟨M, hMdef⟩ : ∃ M : Matrix (Fin r) (Fin r) W.EE, M = b.toMatrix (fun j => W.φD T (b j))` from `⟨_, rfl⟩`.

Establish `hM : cb.toMatrix c' = M.map E.ioE`. Use extensionality with `i j`. Rewrite using `[Basis.toMatrix_apply, Matrix.map_apply]`. Establish `e1 : c' j = ∑ k, E.ioE (M k j) • cb k`. Rewrite using `[hc'def, hcdef, ← E.jD_φ, hjD]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hcb, hMdef, Basis.toMatrix_apply]`. Rewrite using `[e1, ← Basis.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hdetM : IsUnit (E.ioE M.det)`. Rewrite using `[AlgHom.map_det]`.

Rewrite `hdet` using `[Basis.det_apply, hM]`. Conclude with `hdet`. Establish `hbas` using `(b.is_basis_iff_det (v := fun j => W.φD T (b j))).2 (by rw [Basis.det_apply, ← hMdef]; exact hunits _ hdetM)`. Conclude with `⟨r, b, Basis.mk hbas.1 hbas.2.ge, fun j => Basis.mk_apply _ _ j⟩`.
-/
theorem phi_basis_of_tie {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) [Nontrivial W.EE] [Nontrivial O]
    (hφ : Function.Surjective φR) (hunits : ∀ x : W.EE, IsUnit (E.ioE x) → IsUnit x)
    (T : LocLat G Qp LL O) (hTfree : Module.Free O ↥T.L.T) (hTfin : Module.Finite O ↥T.L.T) :
    ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  haveI hfreeD : Module.Free W.EE (W.DD T) := (W.DD_free T).1
  have hrk : finrank W.EE (W.DD T) = finrank O ↥T.L.T := (W.DD_free T).2
  obtain ⟨d0⟩ : Nonempty (Basis (Fin (finrank O ↥T.L.T)) RW (TW RW T)) :=
    ⟨Algebra.TensorProduct.basis RW (Module.finBasis O ↥T.L.T)⟩
  haveI hfin : Module.Finite W.EE (W.DD T) := by
    rcases Nat.eq_zero_or_pos (finrank W.EE (W.DD T)) with h0 | h0
    · haveI : IsEmpty (Fin (finrank O ↥T.L.T)) := by rw [← hrk, h0]; infer_instance
      have hz : ∀ x : W.DD T, x = 0 := fun x => E.jD_inj T (by
        rw [map_zero, ← d0.sum_repr (E.jD T x)]; simp)
      haveI : Subsingleton (W.DD T) := ⟨fun x y => by rw [hz x, hz y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos h0
  obtain ⟨r, hr⟩ : ∃ r, r = finrank W.EE (W.DD T) := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Basis (Fin r) W.EE (W.DD T)) :=
    ⟨(Module.finBasis W.EE (W.DD T)).reindex (finCongr hr.symm)⟩
  obtain ⟨d⟩ : Nonempty (Basis (Fin r) RW (TW RW T)) := ⟨d0.reindex (finCongr (hr.trans hrk).symm)⟩

  obtain ⟨c, hcdef⟩ : ∃ c : Fin r → TW RW T, ∀ j, c j = E.jD T (b j) := ⟨_, fun _ => rfl⟩
  have hjD : ∀ x : W.DD T, E.jD T x = ∑ i, E.ioE (b.repr x i) • c i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, hcdef]
  have hc : Submodule.span RW (Set.range c) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hjD x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨cb, hcb⟩ : ∃ cb : Basis (Fin r) RW (TW RW T), ∀ i, cb i = c i :=
    ⟨Basis.mk (linearIndependent_of_span d c hc) hc.ge, fun i => Basis.mk_apply _ _ i⟩

  obtain ⟨c', hc'def⟩ : ∃ c' : Fin r → TW RW T, ∀ j, c' j = TWmap φR T (c j) := ⟨_, fun _ => rfl⟩
  have hTW : ∀ y : TW RW T, ∃ x, TWmap φR T x = y := fun y => twmap_surjective φR T hφ y
  have himg : ∀ x : TW RW T, TWmap φR T x ∈ Submodule.span RW (Set.range c') := by
    intro x
    have hx : x ∈ Submodule.span RW (Set.range c) := by rw [hc]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun RW).1 hx
    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twmap_smul, ← hc'def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hc' : Submodule.span RW (Set.range c') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxy⟩ := hTW y
    rw [← hxy]
    exact himg x
  have hdet : IsUnit (cb.det c') := cb.is_basis_iff_det.1 ⟨linearIndependent_of_span d c' hc', hc'⟩

  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin r) (Fin r) W.EE, M = b.toMatrix (fun j => W.φD T (b j)) :=
    ⟨_, rfl⟩
  have hM : cb.toMatrix c' = M.map E.ioE := by
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply]
    have e1 : c' j = ∑ k, E.ioE (M k j) • cb k := by
      rw [hc'def, hcdef, ← E.jD_φ, hjD]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcb, hMdef, Basis.toMatrix_apply]
    rw [e1, ← Basis.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hdetM : IsUnit (E.ioE M.det) := by
    rw [AlgHom.map_det]
    rw [Basis.det_apply, hM] at hdet
    exact hdet
  have hbas := (b.is_basis_iff_det (v := fun j => W.φD T (b j))).2
    (by rw [Basis.det_apply, ← hMdef]; exact hunits _ hdetM)
  exact ⟨r, b, Basis.mk hbas.1 hbas.2.ge, fun j => Basis.mk_apply _ _ j⟩

end Generic

/- English proof (translation)
Use `haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1`. Establish `h : Function.Surjective (frobW l)` using `WittVector.map_surjective (frobenius (Cb l) l) fun x => IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos`. Conclude with `LinearMap.lTensor_surjective ↥(OL LL) (g := (frobW l).toLinearMap) h`.
-/
theorem φRW_onto {l : ℕ} [Fact l.Prime] (LL : FinExt l) : Function.Surjective (φRW LL) := by
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have h : Function.Surjective (frobW l) :=
    WittVector.map_surjective (frobenius (Cb l) l) fun x =>
      IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
  exact LinearMap.lTensor_surjective ↥(OL LL) (g := (frobW l).toLinearMap) h

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h W T`. Use `haveI : Nontrivial W.EE := W.EE_inj.nontrivial`. Conclude with `phi_basis_of_tie ((F l).E K s LL h).tie (φRW_onto LL) (GlobalTheory.IoInj.ioE_injective_saturated_inter l (D.loc l) (D.locA l) K s LL h _ _ _ (GlobalTheory.NL.ioW (HW l) (F l) h (GlobalTheory.NL.Holds.laws (HW l) (F l) h))).2.1 T T.L.free (Module.Finite.iff_fg.mpr T.L.fg)`.
-/
theorem phi_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  intro D HW F l _ K s LL h W T
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  exact phi_basis_of_tie ((F l).E K s LL h).tie (φRW_onto LL)
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l (D.loc l) (D.locA l) K s LL h _ _ _
      (GlobalTheory.NL.ioW (HW l) (F l) h (GlobalTheory.NL.Holds.laws (HW l) (F l) h))).2.1
    T T.L.free (Module.Finite.iff_fg.mpr T.L.fg)

end GlobalTheory.EtaleFrob
