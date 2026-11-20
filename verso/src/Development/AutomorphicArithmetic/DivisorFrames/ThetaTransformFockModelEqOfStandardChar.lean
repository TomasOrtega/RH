import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding

section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealDict GlobalTheory.RealDict.FockMap

/- English proof (translation)
Use `choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)`. Establish `hS` using `Filter.eventually_cofinite.1 hs`. Set `y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F` to `fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ hS.toFinset`. Establish `: (fun k => evalV F v (y k)) = ξ v` using `funext fun k => by`. Rewrite using `[map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]`. Rewrite using `[this]`. Conclude with `hξ v`.

Establish `: (fun k => evalV F v (y k)) = 0` using `funext fun k => by`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _`. Rewrite using `[this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]`. Conclude with `one_ne_zero`.
-/
private theorem finPart_ne {F : Type} [Field F] [NumberField F] {n d : ℕ}
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y, GlobalTheory.BigNZ.finPartFn φ y ≠ 0 := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)
  have hS := Filter.eventually_cofinite.1 hs
  let y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  refine ⟨y, ?_⟩
  refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
  by_cases hv : v ∈ hS.toFinset
  · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
      rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
    rw [this]
    exact hξ v
  · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
      rw [map_sum]
      exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
    rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
    exact one_ne_zero

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨-, -, tinj, tth, -⟩` from `th_laws Mo hψ hθ hX hW hM`. Take `⟨Dr, hD1, hD2, hD3⟩` from `exists_der Mo hStd`. Take `⟨y, hy⟩` from `hy`. Take `⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg` from `⟨_, rfl⟩`. Establish `hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f` using `fun f => by rw [hΘ]; rfl`.

Rewrite `hv` using `[hΘ']`. Simplify using `only [hΘ']`. Establish `hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f)` using `hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg`. Establish `hi : Function.Injective Θ` using `fun f f' h => by`. Establish `e` using `tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)`.

Use `DFunLike.ext _ _ fun a => ?_` and prove the remaining obligations. Establish `e2` using `congrFun e (GlobalTheory.RealLift.ptAt a y)`. Rewrite `e2` using `[GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt]`. Conclude with `mul_right_cancel₀ hy e2`. Establish `hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ + Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0` using `fun t z => hi (by`.

Establish `h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0` using `hv.2 t z`. Rewrite `h` using `[annih, hd, hd, ← map_smul, ← map_add]`. Rewrite using `[h, map_zero])`. Set `um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ` to `fun k => Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2`. Set `Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank)` to `fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f - Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)`.

Set `Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank)` to `(MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀`. Establish `hΦ : Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀)`. Use `(MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]`. Proceed by induction on `(Finsupp.toMultiset k).toList with`.

Consider the case `nil => rfl`. Consider the case `cons i l ih`. Rewrite using `[List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub, ← map_smul]`. Establish `hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P` using `fun P => LinearMap.congr_fun hΦ P`. Establish `hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f = ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f` using `fun u hu f => by`.

Rewrite using `[← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]`. Establish `hG : Mo.IsGauss ψ τ g₀` using `⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by`. Rewrite using `[hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t, eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]⟩`.

Establish `hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ` using `fun u hu f hf => Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)`. Use `⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), hΦ'⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.constr_range, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `beta_reduce`.

Proceed by induction on `(Finsupp.toMultiset k).toList with`. Consider the case `nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG`. Consider the case `cons i l ih`. Conclude with `Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))`. Take `⟨z, rfl⟩` from `gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf`.

Conclude with `Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩`. Introduce and unpack `u hu _ ⟨P, rfl⟩ f₁ h1`. Rewrite using `[hD2 u hu _ _ h1, hsum u hu]`. Use `Submodule.sum_mem _ fun t _ => ?_` and prove the remaining obligations. Take `⟨Q, hQ⟩` from `dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P`.

Conclude with `⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩`.
-/
private theorem fock_of {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
    (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj)
    (g₀ : SInf D.host.F (Fin M.rank × Fin X.rank)) (g0 : g₀ ≠ 0)
    {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (hy : ∃ y, g y ≠ 0)
    (hv : IsVacF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g))) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      LinearMap.range Φ = Mo.Pol ψ τ ∧
      ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g) = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g)) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  simp only [hΘ']
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a y)
    rw [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt] at e2
    exact mul_right_cancel₀ hy e2
  have hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ +
      Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0 := fun t z => hi (by
    have h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0 := hv.2 t z
    rw [annih, hd, hd, ← map_smul, ← map_add] at h
    rw [h, map_zero])
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun hΦ P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t,
      eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), hΦ'⟩
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `D ψ θ hψ hθ ε M X k hk Xs Ws Mo hX hW hM A B τ hc f₀ φ hf hφ hφ' hφ0 hv`. Substitute `hk` using the available equality. Establish `hF : GlobalTheory.BigNZ.Fam Mo φ` using `⟨hφ, hφ'⟩`. Establish `h2X : ∀ w, Xs.θ w * Xs.θ w = 1` using `fun w => by`. Take `⟨t, -, h, -⟩` from `hc w`.

Rewrite using `[h, Matrix.smul_mul, Matrix.mul_smul, (GlobalTheory.ChainFr.Model.isCartanInv_cart A t).1, smul_smul]`. Apply the tactic sequence `cases ε <;> simp`. Establish `h2W : ∀ w, Ws.θ w * Ws.θ w = 1` using `fun w => by`. Take `⟨t, -, -, h⟩` from `hc w`. Establish `h' : Ws.θ w = (B.cart t).map (starRingEnd ℂ)` using `h`.

Rewrite using `[h', ← Matrix.map_mul, (GlobalTheory.ChainFr.Model.isCartanInv_cart B t).1, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `fock_of Mo hψ hθ A B (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) hX hW hM h2X h2W hc f₀ hf (hF.sb hM) (finPart_ne φ hφ0 (hF.std hM)) hv`.
-/
theorem UpperTheory.theta_transform_fock_model_eq_of_standard_char :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
        ∀ (ε : Bool) (M X : HSp D) (k : ℕ) (hk : k = X.rank) (Xs : Spc D.host.F D.host.E M.rank) (Ws : Spc D.host.F D.host.E k)
        (Mo : Model D.sp.cm.sig Xs Ws), Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram →
        Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (finCongr hk) (finCongr hk) → Mo.IsGood ψ →
        ∀ (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w),
        (∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
          Ws.θ w = ((B.cart t).submatrix (finCongr hk) (finCongr hk)).map conj) →
        ∀ (f₀ : SInf D.host.F (Fin M.rank × Fin k)) (φ : ∀ v : Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ), f₀ ≠ 0 →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) → (∀ v, φ v ≠ 0) →
        GlobalTheory.SquareComm.IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) →
        ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin k), LinearMap.range Φ = Mo.Pol ψ τ ∧
          ∀ P, GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
            GlobalTheory.SquareComm.fockF ψ θ ε A B
              (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) P := by
  intro D ψ θ hψ hθ ε M X k hk Xs Ws Mo hX hW hM A B τ hc f₀ φ hf hφ hφ' hφ0 hv
  subst hk
  have hF : GlobalTheory.BigNZ.Fam Mo φ := ⟨hφ, hφ'⟩
  have h2X : ∀ w, Xs.θ w * Xs.θ w = 1 := fun w => by
    obtain ⟨t, -, h, -⟩ := hc w
    rw [h, Matrix.smul_mul, Matrix.mul_smul, (GlobalTheory.ChainFr.Model.isCartanInv_cart A t).1, smul_smul]
    cases ε <;> simp
  have h2W : ∀ w, Ws.θ w * Ws.θ w = 1 := fun w => by
    obtain ⟨t, -, -, h⟩ := hc w
    have h' : Ws.θ w = (B.cart t).map (starRingEnd ℂ) := h
    rw [h', ← Matrix.map_mul, (GlobalTheory.ChainFr.Model.isCartanInv_cart B t).1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact fock_of Mo hψ hθ A B (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) hX hW hM h2X h2W hc
    f₀ hf (hF.sb hM) (finPart_ne φ hφ0 (hF.std hM)) hv
