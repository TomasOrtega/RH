import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelLocalOperatorAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentityStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.ThK.PolMatchStep
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
section Local
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end Local
/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T v hv h hh Φ Φ' hPM`. Take `⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩` from `hPM`. Establish `hT` using `hM.triple`. Establish `ex` using `(_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v`. Establish `ex'` using `(_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v`.

Establish `h1 : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v)`. Introduce `u _`. Use `show u • ((1 : Matrix _ _ _) - 1) = 0`. Simplify using the standard rewrite rules. Establish `h1' : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V' (GlobalTheory.AdelicU.evFin F v)`.

Introduce `u _`. Use `show u • ((1 : Matrix _ _ _) - 1) = 0`. Simplify using the standard rewrite rules. Establish `E1` using `fun x hx => (ex.1 1 h1 h hh x hx).exists`. Establish `E1'` using `fun x hx => (ex'.1 1 h1' h hh x hx).exists`.

Set `loc : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ` to `fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1 x hx).choose else 0`. Set `loc' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ` to `fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1' x hx).choose else 0`. Establish `hloc : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), loc x ∈ GlobalTheory.WeilM.SB _ ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h)) x (loc x)` using `fun x hx => by`. Simplify using `only [loc, dif_pos hx]`. Conclude with `(E1 x hx).choose_spec`.

Establish `hloc' : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), loc' x ∈ GlobalTheory.WeilM.SB _ ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)) x (loc' x)` using `fun x hx => by`. Simplify using `only [loc', dif_pos hx]`. Conclude with `(E1' x hx).choose_spec`. Establish `pre : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v x = y` using `fun y => by`. Establish `hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v)` using `by rw [hM.fin.onto v]; trivial`.

Conclude with `hy`. Establish `pre' : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y` using `fun y => by`. Establish `hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v)` using `by rw [hM.fin.onto' v]; trivial`. Conclude with `hy`. Set `A0 : Rf.Pi v → Rf.Pi v` to `fun y => Rf.p v (loc (pre y).choose)`.

Establish `K : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), A0 (Rf.p v x) = Rf.p v (loc x)`. Introduce `x hx`. Take `⟨hx0, hx0e⟩` from `(pre (Rf.p v x)).choose_spec`. Take `⟨x', hx', hx'e⟩` from `pre' (Rf.p v x)`. Establish `a1` using `hM.fin.equiv v h hh _ hx0 x' hx' _ (hloc _ hx0).1 _ (hloc' x' hx').1 (hloc _ hx0).2 (hloc' x' hx').2 (hx0e.trans hx'e.symm)`.

Establish `a2` using `hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hx'e.symm`. Conclude with `a1.trans a2.symm`. Establish `K' : ∀ x' ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), A0 (Rf.p' v x') = Rf.p' v (loc' x')`. Introduce `x' hx'`. Take `⟨x, hx, hxe⟩` from `pre (Rf.p' v x')`.

Rewrite using `[← hxe, K x hx]`. Conclude with `hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hxe`. Establish `Klin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ c d : ℂ, loc (c • x + d • y) = c • loc x + d • loc y`. Introduce `x hx y hy c d`. Establish `hs : c • x + d • y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)` using `add_mem ((GlobalTheory.WeilM.SB _).smul_mem c hx) ((GlobalTheory.WeilM.SB _).smul_mem d hy)`.

Conclude with `acts_lin_eq v (om (1, h)) hx hy (hloc x hx).2 (hloc y hy).2 c d (hloc _ hs).2`. Set `A : Rf.Pi v →ₗ[ℂ] Rf.Pi v` to `{ toFun := A0 map_add' := by`. Introduce `y z`. Take `⟨x, hx, rfl⟩` from `pre y`. Take `⟨w, hw, rfl⟩` from `pre z`.

Rewrite using `[← map_add, K _ (add_mem hx hw), K x hx, K w hw, ← map_add]`. Use `congr 1`. Simplify using `using Klin x hx w hw 1 1`. Use the proof step `map_smul' := by`. Introduce `c y`.

Take `⟨x, hx, rfl⟩` from `pre y`. Rewrite using `[← map_smul, K _ ((GlobalTheory.WeilM.SB _).smul_mem c hx), K x hx, RingHom.id_apply, ← map_smul]`. Use `congr 1`. Simplify using `using Klin x hx x hx c 0 }`. Establish `hvT : ∀ w, w ∉ T → w ≠ v` using `fun w hw e => hw (e ▸ hv)`.

Establish `evc : ∀ {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y G.W) (ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F w) → ℂ), (∀ …`. Introduce `n Y M ρ hρ hG`. Establish `e0 : ∀ᶠ w in Filter.cofinite, ρ w = M.vac w` using `Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun w hw => by`. Assume the negation of the conclusion as `hc`. Conclude with `hw (hρ w hc))`.

Use `filter_upwards [e0, hG.std] with w e1 e2`. Rewrite using `[e1, e2]`. Set `φN : Fin m → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ` to `fun i => Function.update (φ i) v (loc (φ i v))`. Set `φN' : Fin m' → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ` to `fun j => Function.update (φ' j) v (loc' (φ' j v))`. Use `⟨m, m', f, φN, f', φN', fun i => ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩, fun j => ⟨(hφ' j).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `only [φN, Function.update_self]`. Conclude with `(hloc _ ((hφ i).2.1 w)).1`. Simplify using `only [φN, Function.update_of_ne hw]`.

Conclude with `(hφ i).2.1 w`. Simplify using `only [φN, Function.update_of_ne (hvT w hw)]`. Conclude with `(hφ i).2.2 w hw`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Simplify using `only [φN', Function.update_self]`. Conclude with `(hloc' _ ((hφ' j).2.1 w)).1`. Simplify using `only [φN', Function.update_of_ne hw]`. Conclude with `(hφ' j).2.1 w`. Simplify using `only [φN', Function.update_of_ne (hvT w hw)]`.

Conclude with `(hφ' j).2.2 w hw`. Rewrite using `[hΦ, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `pure_update v (om (1, h)) (f i) (φ i) (hφ i).2.1 (evc G.M (φ i) (hφ i).2.2 hT.geo.hM) (hloc _ ((hφ i).2.1 v)).2`. Rewrite using `[hΦ', map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `pure_update v (om' (1, h)) (f' j) (φ' j) (hφ' j).2.1 (evc G.M' (φ' j) (hφ' j).2.2 hT.geo.hM') (hloc' _ ((hφ' j).2.1 v)).2`. Establish `key` using `congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map (Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A))) hsum`. Simplify using `only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key`. Establish `e1 : ∀ i, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u (Rf.p u (φ i u))) = fun u : T => Rf.p u (φN i u)`.

Introduce `i`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u = ⟨v, hv⟩`. Substitute `hu` using the available equality. Simplify using `only [Function.update_self, φN]`.

Conclude with `K _ ((hφ i).2.1 v)`. Establish `hu' : u.1 ≠ v` using `fun e => hu (Subtype.ext e)`. Simplify using `only [Function.update_of_ne hu, φN, Function.update_of_ne hu', LinearMap.id_apply]`. Establish `e2 : ∀ j, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u (Rf.p' u (φ' j u))) = fun u : T => Rf.p' u (φN' j u)`. Introduce `j`.

Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u = ⟨v, hv⟩`. Substitute `hu` using the available equality. Simplify using `only [Function.update_self, φN']`. Conclude with `K' _ ((hφ' j).2.1 v)`.

Establish `hu' : u.1 ≠ v` using `fun e => hu (Subtype.ext e)`. Simplify using `only [Function.update_of_ne hu, φN', Function.update_of_ne hu', LinearMap.id_apply]`. Simplify using `only [e1, e2] at key`. Conclude with `key`.
-/
theorem polynomial_matching_on_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T v hv h hh Φ Φ' hPM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hPM
  have hT := hM.triple
  have ex := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v
  have ex' := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v
  have h1 : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have h1' : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V' (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have E1 := fun x hx => (ex.1 1 h1 h hh x hx).exists
  have E1' := fun x hx => (ex'.1 1 h1' h hh x hx).exists
  let loc : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1 x hx).choose else 0
  let loc' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1' x hx).choose else 0
  have hloc : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), loc x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h)) x (loc x) := fun x hx => by
    simp only [loc, dif_pos hx]; exact (E1 x hx).choose_spec
  have hloc' : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), loc' x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)) x (loc' x) := fun x hx => by
    simp only [loc', dif_pos hx]; exact (E1' x hx).choose_spec
  have pre : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hM.fin.onto v]; trivial
    exact hy
  have pre' : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    exact hy
  let A0 : Rf.Pi v → Rf.Pi v := fun y => Rf.p v (loc (pre y).choose)
  have K : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), A0 (Rf.p v x) = Rf.p v (loc x) := by
    intro x hx
    obtain ⟨hx0, hx0e⟩ := (pre (Rf.p v x)).choose_spec
    obtain ⟨x', hx', hx'e⟩ := pre' (Rf.p v x)
    have a1 := hM.fin.equiv v h hh _ hx0 x' hx' _ (hloc _ hx0).1 _ (hloc' x' hx').1 (hloc _ hx0).2 (hloc' x' hx').2
      (hx0e.trans hx'e.symm)
    have a2 := hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2
      hx'e.symm
    exact a1.trans a2.symm
  have K' : ∀ x' ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), A0 (Rf.p' v x') = Rf.p' v (loc' x') := by
    intro x' hx'
    obtain ⟨x, hx, hxe⟩ := pre (Rf.p' v x')
    rw [← hxe, K x hx]
    exact hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hxe
  have Klin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∀ c d : ℂ, loc (c • x + d • y) = c • loc x + d • loc y := by
    intro x hx y hy c d
    have hs : c • x + d • y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((GlobalTheory.WeilM.SB _).smul_mem c hx) ((GlobalTheory.WeilM.SB _).smul_mem d hy)
    exact acts_lin_eq v (om (1, h)) hx hy (hloc x hx).2 (hloc y hy).2 c d (hloc _ hs).2
  let A : Rf.Pi v →ₗ[ℂ] Rf.Pi v :=
    { toFun := A0
      map_add' := by
        intro y z
        obtain ⟨x, hx, rfl⟩ := pre y
        obtain ⟨w, hw, rfl⟩ := pre z
        rw [← map_add, K _ (add_mem hx hw), K x hx, K w hw, ← map_add]
        congr 1
        simpa using Klin x hx w hw 1 1
      map_smul' := by
        intro c y
        obtain ⟨x, hx, rfl⟩ := pre y
        rw [← map_smul, K _ ((GlobalTheory.WeilM.SB _).smul_mem c hx), K x hx, RingHom.id_apply, ← map_smul]
        congr 1
        simpa using Klin x hx x hx c 0 }
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ hv)
  have evc : ∀ {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y G.W) (ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, w ∉ T → ρ w = M.vac w) → M.IsGood B.ψ →
      ∀ᶠ w in Filter.cofinite, ρ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    intro n Y M ρ hρ hG
    have e0 : ∀ᶠ w in Filter.cofinite, ρ w = M.vac w :=
      Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw (hρ w hc))
    filter_upwards [e0, hG.std] with w e1 e2
    rw [e1, e2]
  let φN : Fin m → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ :=
    fun i => Function.update (φ i) v (loc (φ i v))
  let φN' : Fin m' → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun j => Function.update (φ' j) v (loc' (φ' j v))
  refine ⟨m, m', f, φN, f', φN', fun i => ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩,
    fun j => ⟨(hφ' j).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; simp only [φN, Function.update_self]; exact (hloc _ ((hφ i).2.1 w)).1
    · simp only [φN, Function.update_of_ne hw]; exact (hφ i).2.1 w
  · simp only [φN, Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w hw
  · by_cases hw : w = v
    · subst hw; simp only [φN', Function.update_self]; exact (hloc' _ ((hφ' j).2.1 w)).1
    · simp only [φN', Function.update_of_ne hw]; exact (hφ' j).2.1 w
  · simp only [φN', Function.update_of_ne (hvT w hw)]; exact (hφ' j).2.2 w hw
  · rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact pure_update v (om (1, h)) (f i) (φ i) (hφ i).2.1 (evc G.M (φ i) (hφ i).2.2 hT.geo.hM)
      (hloc _ ((hφ i).2.1 v)).2
  · rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact pure_update v (om' (1, h)) (f' j) (φ' j) (hφ' j).2.1 (evc G.M' (φ' j) (hφ' j).2.2 hT.geo.hM')
      (hloc' _ ((hφ' j).2.1 v)).2
  · have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map
      (Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A))) hsum
    simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key
    have e1 : ∀ i, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p u (φ i u))) = fun u : T => Rf.p u (φN i u) := by
      intro i; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN]; exact K _ ((hφ i).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN, Function.update_of_ne hu', LinearMap.id_apply]
    have e2 : ∀ j, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p' u (φ' j u))) = fun u : T => Rf.p' u (φN' j u) := by
      intro j; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN']; exact K' _ ((hφ' j).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN', Function.update_of_ne hu', LinearMap.id_apply]
    simp only [e1, e2] at key
    exact key
end GlobalTheory.ThK.PolMatchStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | exact _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | (intros; apply _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.polynomial_matching_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  first | exact @_root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | exact _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | (intros; apply _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ <;> assumption)
end
