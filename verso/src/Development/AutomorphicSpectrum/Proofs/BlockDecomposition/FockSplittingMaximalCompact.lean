import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactIsOpenCosVN
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Box

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

/- English proof (translation)
Use `⟨fun v => ?_, ?_, fun X => ?_⟩` and prove the remaining obligations. Use `haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space`. Establish `hcl : IsClopen (A v)` using `⟨(hA v).1.isClosed, (hA v).2⟩`. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ A v`.

Conclude with `⟨A v, (hA v).2, hx, fun y hy => by beta_reduce`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hy]`. Use the proof step `rfl⟩`. Conclude with `⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by beta_reduce`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩`.

Use `Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hv ?_` and prove the remaining obligations. Use `show (A v).indicator 1 = _`. Rewrite using `[hS v h]`.

Distinguish the cases in `hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A`. Rewrite using `[Set.indicator_of_mem hX]`. Conclude with `(finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm`. Rewrite using `[Set.indicator_of_notMem hX]`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hX h`. Use `(finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm` and prove the remaining obligations. Establish `hfin` using `Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)`.

Use `(hfin.union S.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h`. Apply `hv` to reduce the goal to its premises. Use `show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1`.

Rewrite using `[hS v h.2]`. Conclude with `Set.indicator_of_mem h.1 _`.
-/
theorem isPureFin_box (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v))
    (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b ((GlobalTheory.CompanionTheory.WhitFree.boxF A).indicator (fun _ => (1 : ℂ)))
      (fun v => (A v).indicator 1) := by
  classical
  refine ⟨fun v => ?_, ?_, fun X => ?_⟩
  · haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
      (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space
    have hcl : IsClopen (A v) := ⟨(hA v).1.isClosed, (hA v).2⟩
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
      HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ A v
    · exact ⟨A v, (hA v).2, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        rfl⟩
    · exact ⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    refine hv ?_
    show (A v).indicator 1 = _
    rw [hS v h]
  · by_cases hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A
    · rw [Set.indicator_of_mem hX]
      exact (finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm
    · rw [Set.indicator_of_notMem hX]
      obtain ⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by
        by_contra h
        push_neg at h
        exact hX h
      refine (finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm
      have hfin := Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)
      refine (hfin.union S.finite_toSet).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h
      apply hv
      show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1
      rw [hS v h.2]
      exact Set.indicator_of_mem h.1 _

end Box

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩`. Consider the case `zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨N, f, rfl, hf⟩` from `hx`.

Take `⟨N', f', rfl, hf'⟩` from `hy`. Use `⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify `hf i` using `[Fin.append_left]`. Simplify `hf' i` using `[Fin.append_right]`.

Consider the case `smul a x _ hx`. Take `⟨N, f, rfl, hf⟩` from `hx`. Conclude with `⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩`.
-/
theorem exists_fin_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {P : M → Prop}
    (hs : ∀ (a : ℂ) (x : M), P x → P (a • x)) {x : M} (hx : x ∈ Submodule.span ℂ {y | P y}) :
    ∃ (N : ℕ) (f : Fin N → M), x = ∑ j, f j ∧ ∀ j, P (f j) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩
  | zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    obtain ⟨N', f', rfl, hf'⟩ := hy
    refine ⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [Fin.append_left] using hf i
    · simpa [Fin.append_right] using hf' i
  | smul a x _ hx =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    exact ⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩

variable {D : D7} {n : ℕ}

/- English proof (translation)
Simplify using `only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]`.
-/
theorem evalPoly_monomial_mul {m : ℕ} (e : D.what₂.Tau × Fin m × Fin n × Bool →₀ ℕ) (a c : ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.monomial e (a * c)) z = a * evalPoly (MvPolynomial.monomial e c) z := by
  simp only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]

/- English proof (translation)
Take `⟨e, c, g, d, bs, gv, hp, rfl⟩` from `h`. Use `⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]`.
-/
theorem isMonoFock_smul {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : Mx D V.rank n → ℂ} (a : ℂ)
    (h : IsMonoFock θ V l s φ) : IsMonoFock θ V l s (a • φ) := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  refine ⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]

/- English proof (translation)
Use `haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Set `b` to `Module.finBasis D.host.F D.host.E`. Set `tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `{ toFun := fun X i j => X j i invFun := fun Z j i => Z i j left_inv := fun _ => rfl right_inv := fun _ => rfl continuous_toFun := continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j) continuous_invFun := continuous_pi fun j => continuous_pi …`. Set `g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ` to `fun X => g (tr X)`. Establish `hg' : IsSB g'` using `⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩`.

Take `⟨t, A, S, hA, hS, hdec⟩` from `Box.exists_box_combN b g' hg'`. Set `ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ` to `fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)`. Establish `hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i) (fun v => (A a v).indicator 1)` using `fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)`. Establish `hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) = ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n => evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) * gauss …`. Use function extensionality and compare the values at `x`.

Establish `hp : evalPoly p (fun τ => compAt θ τ x) = ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← p.as_sum]`. Use `_ = _ := by simp only [evalPoly, map_sum]`. Establish `hgx : g (fun i j => finPart D (x i j)) = ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j))` using `hdec (fun j i => finPart D (x i j))`.

Rewrite using `[hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hφ]`. Use `Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩`.
-/
theorem gen_mem_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  classical
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis D.host.F D.host.E
  let tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X i j => X j i
      invFun := fun Z j i => Z i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  let g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => g (tr X)
  have hg' : IsSB g' := ⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩
  obtain ⟨t, A, S, hA, hS, hdec⟩ := Box.exists_box_combN b g' hg'
  let ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)
  have hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i)
      (fun v => (A a v).indicator 1) := fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)
  have hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) =
      ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n =>
        evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) *
          gauss V l s (fun τ => compAt θ τ x) * ind a (fun i j => finPart D (x i j))) := by
    funext x
    have hp : evalPoly p (fun τ => compAt θ τ x) =
        ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
      calc evalPoly p (fun τ => compAt θ τ x)
          = evalPoly (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
            rw [← p.as_sum]
        _ = _ := by simp only [evalPoly, map_sum]
    have hgx : g (fun i j => finPart D (x i j)) =
        ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j)) :=
      hdec (fun j i => finPart D (x i j))
    rw [hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hφ]
  refine Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `φ ⟨p, g, hg, rfl⟩`. Conclude with `gen_mem_span θ V l s p g hg`.
-/
theorem fockA_le_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    fockA θ V n l s ≤ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  exact gen_mem_span θ V l s p g hg

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit

namespace GlobalTheory.CompanionTheory.PfSWUS

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk`. Conclude with `FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h) (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))`.
-/
theorem fockSplitK : PositivityTheory.PfSWUS.FockSplitK := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk
  exact FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h)
    (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))

end GlobalTheory.CompanionTheory.PfSWUS

end
