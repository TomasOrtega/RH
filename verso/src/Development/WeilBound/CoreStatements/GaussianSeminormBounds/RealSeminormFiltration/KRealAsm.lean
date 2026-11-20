import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.KRealAsmOne
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLParity
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.PolRange

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace PositivityTheory.KRealA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`.
-/
theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

/- English proof (translation)
Introduce `z hz`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `: piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0`. Establish `h0 : piInf (τ w) (z : AE F E) ≠ 0`.

Introduce `e`. Use `congrArg (piInf (τ w)) z.mul_inv` as an intermediate fact. Rewrite `this` using `[map_mul, e, zero_mul, map_one]`. Conclude with `zero_ne_one this`. Conclude with `div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)`.

Rewrite using `[zpow_sub₀ this]`.
-/
theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/- English proof (translation)
Unfold `atPl`. Rewrite using `[← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = w`.

Substitute `hi` using the available equality. Simplify using `[h]`. Simplify using `[Function.update_of_ne hi]`.
-/
theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x`.
-/
theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

/- English proof (translation)
The claim follows from `GlobalTheory.TensIrr.tensor_irr`.
-/
theorem i_tensirr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R S : ℕ) (M : ι → Formalism.BasicNotions.TH.GKMod R S), (∀ i, Formalism.MainNotions.SchurIrreducible.IrrGK (M i) ∧ GlobalTheory.RealLift.ScalarEnd (M i)) → Nontrivial (PiTensorProduct ℂ fun i => (M i).V) ∧ ∀ N : Submodule ℂ (PiTensorProduct ℂ fun i => (M i).V), (∀ i, ∀ Z ∈ Formalism.BasicNotions.TH.upq R S, ∀ y ∈ N, GlobalTheory.RealLift.atPl i ((M i).act Z) y ∈ N) → N = ⊥ ∨ N = ⊤ := GlobalTheory.TensIrr.tensor_irr

/- English proof (translation)
The claim follows from `GlobalTheory.RealLift.locFin_sumPl`.
-/
theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.RealLift.locFin_sumPl

/- English proof (translation)
The claim follows from `GlobalTheory.ExpAct.expAct_fock`.
-/
theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.ExpAct.expAct_fock

/- English proof (translation)
The claim follows from `PositivityTheory.RL.actsLaws`.
-/
theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := PositivityTheory.RL.actsLaws

/- English proof (translation)
The claim follows from `PositivityTheory.RL.derEx`.
-/
theorem i_derex : GlobalTheory.RealLift.DerEx := PositivityTheory.RL.derEx

/- English proof (translation)
The claim follows from `PositivityTheory.RL.fockEx`.
-/
theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := PositivityTheory.RL.fockEx

/- English proof (translation)
The claim follows from `PositivityTheory.RL.vacLine`.
-/
theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := PositivityTheory.RL.vacLine

/- English proof (translation)
The claim follows from `PositivityTheory.ThKEnd.Comp.PR.polRange_of`.
-/
theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := PositivityTheory.ThKEnd.Comp.PR.polRange_of

/- English proof (translation)
The claim follows from `PositivityTheory.RL.genEx`.
-/
theorem i_genex : GlobalTheory.RealLift.GenEx := PositivityTheory.RL.genEx

/- English proof (translation)
The claim follows from `PositivityTheory.RL.lineEx`.
-/
theorem i_lineex : GlobalTheory.RealLift.LineEx := PositivityTheory.RL.lineEx

/- English proof (translation)
The claim follows from `PositivityTheory.RL.kLine`.
-/
theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := PositivityTheory.RL.kLine

/- English proof (translation)
The claim follows from `PositivityTheory.RL.frameEx`.
-/
theorem i_frameex : GlobalTheory.RealLift.FrameEx := PositivityTheory.RL.frameEx

/- English proof (translation)
The claim follows from `PositivityTheory.RL.even_im_hermitian_sub`.
-/
theorem i_parity : GlobalTheory.RealLift.Parity := PositivityTheory.RL.even_im_hermitian_sub

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

/- English proof (translation)
Simplify using `only [atPl_eq, MultilinearMap.map_update_add]`.
-/
theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

/- English proof (translation)
Simplify using `only [atPl_eq, MultilinearMap.map_update_smul]`.
-/
theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul]

/- English proof (translation)
Rewrite using `[atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Simplify using `[Function.update_of_ne h]]`. Conclude with `PiTensorProduct.map_id`.
-/
theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

/- English proof (translation)
Simplify using `only [atPl_eq, MultilinearMap.map_update_zero]`.
-/
theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `choose x hx using fun i => hp i (y i)`. Conclude with `⟨PiTensorProduct.tprod ℂ x, by rw [PiTensorProduct.map_tprod]; simp [hx]⟩`.
-/
theorem map_surj (p : ∀ i, V i →ₗ[ℂ] W i) (hp : ∀ i, Function.Surjective (p i)) :
    Function.Surjective (PiTensorProduct.map p) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  choose x hx using fun i => hp i (y i)
  exact ⟨PiTensorProduct.tprod ℂ x, by rw [PiTensorProduct.map_tprod]; simp [hx]⟩

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h, LinearMap.comp_apply]`.
-/
theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

/- English proof (translation)
Use `sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Establish `a` using `hU v (l ∘ₗ q)`. Establish `b` using `hU' v' (l ∘ₗ q')`. Simplify using `only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b`.

Conclude with `a.unique b`.
-/
theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

/- English proof (translation)
Introduce `v l` and use `by have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l (((0 : Module.End ℂ V) ^ n) v)) = fun n => if n = 0 then l v else 0 := by funext n; rcases n with _ | n · simp · simp [pow_succ] rw [e]; simpa using hasSum_ite_eq 0 (l v)`.
-/
theorem exp_id : IsExp (0 : Module.End ℂ V) 1 := fun v l => by
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l (((0 : Module.End ℂ V) ^ n) v)) = fun n => if n = 0 then l v else 0 := by
    funext n; rcases n with _ | n
    · simp
    · simp [pow_succ]
  rw [e]; simpa using hasSum_ite_eq 0 (l v)

end Exp

/- English proof (translation)
Introduce `v` and use `by obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩`.
-/
theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

/- English proof (translation)
Introduce `v` and use `by obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩`.
-/
theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.smul_apply, Module.End.one_apply, map_smul, LinearMap.zero_apply]`. Rewrite using `[h.2.1 X f, ← add_smul, show (x : ℂ) * X.trace + c * X.trace = ((x : ℂ) + c) * X.trace by ring, hc, zero_mul, zero_smul]`.
-/
theorem isLift_fock1 {P Q R S : ℕ} {x t : ℚ} {N : GKMod R S} {p : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] N.V}
    (h : IsLift x t N p) (X : Mat P Q) (c : ℂ) (hc : (x : ℂ) + c = 0) :
    p ∘ₗ (fockAct1 P Q R S X + (c * X.trace) • 1) = 0 ∘ₗ p := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.smul_apply, Module.End.one_apply, map_smul,
    LinearMap.zero_apply]
  rw [h.2.1 X f, ← add_smul, show (x : ℂ) * X.trace + c * X.trace = ((x : ℂ) + c) * X.trace by ring, hc, zero_mul, zero_smul]

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.smul_apply, Module.End.one_apply, map_smul]`. Rewrite using `[h.2.2 Y f, hc, add_mul, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem isLift_fock2 {P Q R S : ℕ} {x t : ℚ} {N : GKMod R S} {p : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] N.V}
    (h : IsLift x t N p) (Y : Mat R S) (c c' : ℂ) (hc : c = (t : ℂ) + c') :
    p ∘ₗ (fockAct2 P Q R S Y + (c * Y.trace) • 1) = (N.act Y + (c' * Y.trace) • 1) ∘ₗ p := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  rw [h.2.2 Y f, hc, add_mul, add_smul]
  abel

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

/- English proof (translation)
Simplify using `[sumPl, atPl_zero]`.
-/
theorem sumPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] :
    sumPl (fun i => (0 : Module.End ℂ (V i))) = 0 := by
  simp [sumPl, atPl_zero]

include Φ in
/- English proof (translation)
Rewrite `hf` using `[← hrange]`. Take `⟨T, rfl⟩` from `hf`. Conclude with `⟨T, rfl⟩`.
-/
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

/- English proof (translation)
Establish `hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T` using `fun T => by`. Rewrite using `[LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]`. Establish `hz : PiTensorProduct.map p ∘ₗ sumPl (fun w => fockAct1 P Q R S (0 : Mat P Q) + (c w * (0 : Mat P Q).trace) • 1) = 0`. Simplify using `[sumPl_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hrange, ← LinearMap.range_comp, LinearMap.comp_assoc, hΨ, LinearMap.comp_id, LinearMap.range_eq_top]`. Conclude with `map_surj p fun w => (hp w).1`. Introduce `γ hγ f hf f₁ hf₁`. Take `⟨T, rfl⟩` from `pol_eq B M Φ hrange hf`. Take `⟨Yg, -, hY⟩` from `i_genex F E σ (Fin n) P Q B.emb (incM F Y.J) 1 A hcm hA γ hγ`.

Establish `hsd` using `hact γ hγ Yg hY T`. Establish `h1` using `(i_actslaws F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) hsd`. Establish `e` using `(i_actslaws F _ (Φ T) _ f₁).2.2.1 _ h1 hf₁`. Rewrite using `[← e, hpΦ, ← LinearMap.comp_apply, map_sumPl p _ (fun _ => 0) fun w => isLift_fock1 (hp w) _ _ (hxc w), sumPl_zero]`. Both sides reduce to the same expression.

Introduce `k hk f hf f₁ hf₁`. Take `⟨T, rfl⟩` from `pol_eq B M Φ hrange hf`. Take `⟨γ, hγ, Yg, hgen, hKC, hγ1⟩` from `i_kline i_lineex F E σ (Fin n) P Q B.emb (incM F Y.J) 1 A Y.θ hcm hA hAθ k hk.1 hk.2`. Establish `hloc` using `i_locfin _ _ _ (fun w => locFin_fock1 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))`. Take `⟨U, hU, hSA⟩` from `i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ) hloc (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)`.

Establish `h1` using `(i_actslaws F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)`. Rewrite `h1` using `[MonoidHom.comp_apply, hγ1]`. Establish `e` using `(i_actslaws F _ (Φ T) _ f₁).2.2.2.1 _ h1 hf₁`. Rewrite using `[← e, hpΦ, hpΦ]`. Establish `h0 : PiTensorProduct.map p ∘ₗ (0 : Module.End ℂ (Tens F P Q R S)) = sumPl (fun w => (0 : Module.End ℂ (N w).V)) ∘ₗ PiTensorProduct.map p`.

Rewrite using `[sumPl_zero, LinearMap.comp_zero, LinearMap.zero_comp]`. Use `exp_equiv hU exp_id (map_sumPl p _ (fun _ => 0) fun w => isLift_fock1 (hp w) _ _ (hxc w)) h0 (v := T) (v' := T) rfl` as an intermediate fact. Simplify using `using this`.
-/
theorem side_quot (x t : InfinitePlace F → ℚ) (hp : ∀ w, IsLift (x w) (t w) (N w) (p w)) (c : InfinitePlace F → ℂ)
    (hxc : ∀ w, (x w : ℂ) + c w = 0) (hΨ : Ψ ∘ₗ Φ = LinearMap.id) (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb)
    (hcm : IsCMExt F E σ) (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ)
    (hA : ∀ w, IsFrame ((1 : ℂ) • (incM F Y.J).map (piInf (B.emb w))) (A w)) (hAθ : ∀ w, Y.θ w * A w = A w * Jm P Q)
    (hact : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) :
    RealQuot B M om (PiTensorProduct.map p ∘ₗ Ψ) := by
  have hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T := fun T => by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  have hz : PiTensorProduct.map p ∘ₗ sumPl (fun w => fockAct1 P Q R S (0 : Mat P Q) + (c w * (0 : Mat P Q).trace) • 1) = 0 := by
    simp [sumPl_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrange, ← LinearMap.range_comp, LinearMap.comp_assoc, hΨ, LinearMap.comp_id, LinearMap.range_eq_top]
    exact map_surj p fun w => (hp w).1
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨T, rfl⟩ := pol_eq B M Φ hrange hf
    obtain ⟨Yg, -, hY⟩ := i_genex F E σ (Fin n) P Q B.emb (incM F Y.J) 1 A hcm hA γ hγ
    have hsd := hact γ hγ Yg hY T
    have h1 := (i_actslaws F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) hsd
    have e := (i_actslaws F _ (Φ T) _ f₁).2.2.1 _ h1 hf₁
    rw [← e, hpΦ, ← LinearMap.comp_apply, map_sumPl p _ (fun _ => 0) fun w => isLift_fock1 (hp w) _ _ (hxc w), sumPl_zero]
    rfl
  · intro k hk f hf f₁ hf₁
    obtain ⟨T, rfl⟩ := pol_eq B M Φ hrange hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := i_kline i_lineex F E σ (Fin n) P Q B.emb (incM F Y.J) 1 A Y.θ hcm hA hAθ k hk.1 hk.2
    have hloc := i_locfin _ _ _ (fun w => locFin_fock1 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))
    obtain ⟨U, hU, hSA⟩ := i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
      (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
    have h1 := (i_actslaws F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
    rw [MonoidHom.comp_apply, hγ1] at h1
    have e := (i_actslaws F _ (Φ T) _ f₁).2.2.2.1 _ h1 hf₁
    rw [← e, hpΦ, hpΦ]
    have h0 : PiTensorProduct.map p ∘ₗ (0 : Module.End ℂ (Tens F P Q R S)) =
        sumPl (fun w => (0 : Module.End ℂ (N w).V)) ∘ₗ PiTensorProduct.map p := by
      rw [sumPl_zero, LinearMap.comp_zero, LinearMap.zero_comp]
    have := exp_equiv hU exp_id (map_sumPl p _ (fun _ => 0) fun w => isLift_fock1 (hp w) _ _ (hxc w)) h0 (v := T) (v' := T) rfl
    simpa using this

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

/- English proof (translation)
Establish `hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T` using `fun T => by`. Rewrite using `[LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]`. Take `⟨T, rfl⟩` from `pol_eq B M Φ hrange hf`. Establish `hsd` using `hact γ hγ Yg hY T`. Establish `h1` using `(i_actslaws F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) hsd`.

Establish `e` using `(i_actslaws F _ (Φ T) _ f₁).2.2.1 _ h1 hf₁`. Rewrite using `[← e, hpΦ, hpΦ, ← LinearMap.comp_apply, map_sumPl p _ _ fun w => isLift_fock2 (hp w) _ _ _ (hct w)]`. Both sides reduce to the same expression.
-/
theorem side_wlie (x t : InfinitePlace F → ℚ) (hp : ∀ w, IsLift (x w) (t w) (N w) (p w)) (c c' : InfinitePlace F → ℂ)
    (hct : ∀ w, c w = (t w : ℂ) + c' w) (hΨ : Ψ ∘ₗ Φ = LinearMap.id) (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb)
    (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (γ : Multiplicative ℝ →* UG (cA σ) (incM F W.J)) (hγ : γ ∈ RLines σ (incM F W.J)) (Yg : InfinitePlace F → Mat R S)
    (hY : IsGen B.emb C γ Yg) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    (hf₁ : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) :
    (PiTensorProduct.map p ∘ₗ Ψ) f₁ =
      sumPl (fun w => (N w).act (Yg w) + (c' w * (Yg w).trace) • 1) ((PiTensorProduct.map p ∘ₗ Ψ) f) := by
  have hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T := fun T => by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  obtain ⟨T, rfl⟩ := pol_eq B M Φ hrange hf
  have hsd := hact γ hγ Yg hY T
  have h1 := (i_actslaws F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) hsd
  have e := (i_actslaws F _ (Φ T) _ f₁).2.2.1 _ h1 hf₁
  rw [← e, hpΦ, hpΦ, ← LinearMap.comp_apply, map_sumPl p _ _ fun w => isLift_fock2 (hp w) _ _ _ (hct w)]
  rfl

/- English proof (translation)
Establish `hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T` using `fun T => by`. Rewrite using `[LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]`. Take `⟨T, rfl⟩` from `pol_eq B M Φ hrange hf`. Establish `hloc` using `i_locfin _ _ _ (fun w => locFin_fock2 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))`. Take `⟨U, hU, hSA⟩` from `i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hY T)`.

Establish `h1` using `(i_actslaws F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)`. Rewrite `h1` using `[MonoidHom.comp_apply, hγ1]`. Establish `e` using `(i_actslaws F _ (Φ T) _ f₁).2.2.2.1 _ h1 hf₁`. Conclude with `⟨T, _, U, hpΦ T, by rw [← e, hpΦ], hU, map_sumPl p _ _ fun w => isLift_fock2 (hp w) _ _ _ (hct w)⟩`.
-/
theorem side_wcpt (x t : InfinitePlace F → ℚ) (hp : ∀ w, IsLift (x w) (t w) (N w) (p w)) (c c' : InfinitePlace F → ℂ)
    (hct : ∀ w, c w = (t w : ℂ) + c' w) (hΨ : Ψ ∘ₗ Φ = LinearMap.id) (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb)
    (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (γ : Multiplicative ℝ →* UG (cA σ) (incM F W.J)) (hγ : γ ∈ RLines σ (incM F W.J)) (Yg : InfinitePlace F → Mat R S)
    (hY : IsGen B.emb C γ Yg) (hKC : ∀ w, IsKC (Yg w)) {k : UA σ W.J} (hγ1 : γ (Multiplicative.ofAdd 1) = k)
    {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) (hf₁ : Acts (evI F) (om (1, k)) f f₁) :
    ∃ (T : Tens F P Q R S) (L U : Module.End ℂ (Tens F P Q R S)), (PiTensorProduct.map p ∘ₗ Ψ) f = PiTensorProduct.map p T ∧
      (PiTensorProduct.map p ∘ₗ Ψ) f₁ = PiTensorProduct.map p (U T) ∧ IsExp L U ∧
      PiTensorProduct.map p ∘ₗ L = sumPl (fun w => (N w).act (Yg w) + (c' w * (Yg w).trace) • 1) ∘ₗ PiTensorProduct.map p := by
  have hpΦ : ∀ T, (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T := fun T => by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  obtain ⟨T, rfl⟩ := pol_eq B M Φ hrange hf
  have hloc := i_locfin _ _ _ (fun w => locFin_fock2 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hY T)
  have h1 := (i_actslaws F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
  rw [MonoidHom.comp_apply, hγ1] at h1
  have e := (i_actslaws F _ (Φ T) _ f₁).2.2.2.1 _ h1 hf₁
  exact ⟨T, _, U, hpΦ T, by rw [← e, hpΦ], hU, map_sumPl p _ _ fun w => isLift_fock2 (hp w) _ _ _ (hct w)⟩

end SideW

/- English proof (translation)
Simplify using `[upq]`.
-/
theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' h`. Take `⟨hb, hg, hc, hw, hw'⟩` from `h`. Use `choose N p p' hp hp' hirr hsc using fun w => onePlace a a' G.p G.q (B.mα w - B.mβ w) hg.even (hg.kappa w) (i_parity F E σ B a a' G X om om' ⟨hb, hg, hc, hw, hw'⟩ w) hg.eBig hg.aBig`. Use `choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)`. Use `choose A' hA' hAθ' using fun w => i_frameex _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)`.

Use `choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)` using `fun w => by`. Rewrite using `[incM_map_piInf, one_smul]`. Conclude with `hA w`. Establish `hA1' : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A' w)` using `fun w => by`.

Rewrite using `[incM_map_piInf, one_smul]`. Conclude with `hA' w`. Establish `hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w)` using `fun w => by`. Rewrite using `[incM_map_piInf]`. Conclude with `hC w`.

Establish `fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, hC1⟩`. Establish `fr' : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A' C` using `⟨one_mul _, hA1', hC1⟩`. Establish `hvl` using `i_vacline i_derex`. Establish `hfe` using `i_fockex i_derex`. Take `⟨Φ, hΦ⟩` from `hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr`.

Take `⟨Φ', hΦ'⟩` from `hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C hb.cm hb.std fr'`. Establish `hr` using `i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`. Establish `hr'` using `i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C Φ' hb.cm hb.std fr' hAθ' hCθ hΦ'`. Establish `hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om` using `hw`. Establish `hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om'` using `hw'`.

Establish `hW2` using `hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ`. Establish `hW2'` using `hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C Φ' _ X.α B.mα hb.cm hb.std fr' hΦ' hwp'.1 hc.expα`. Take `⟨d, hd, hB1⟩` from `hwp.2.1`. Take `⟨d', hd', hB1'⟩` from `hwp'.2.1`. Establish `hW1` using `hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1 (hasExp_div B.emb hc.expβ hc.expα)`.

Establish `hW1'` using `hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d' 1 Complex.I A' C Φ' _ _ _ hb.cm hb.std fr' hΦ' hd' hB1' (hasExp_div B.emb hc.expα hc.expβ)`. Establish `hadm` using `fun g => (hwp.isUSplitting).adm g`. Establish `hadm'` using `fun g => (hwp'.isUSplitting).adm g`. Take `⟨Ψ, hΨ⟩` from `LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)`. Take `⟨Ψ', hΨ'⟩` from `LinearMap.exists_leftInverse_of_injective Φ' (LinearMap.ker_eq_bot.2 hΦ'.1)`.

Set `Rm : RealMaps F a a'` to `⟨PiTensorProduct ℂ fun w => (N w).V, PiTensorProduct.map p ∘ₗ Ψ, PiTensorProduct.map p' ∘ₗ Ψ'⟩`. Use `⟨Rm, ?_⟩` and prove the remaining obligations. Establish `hx : ∀ w, (((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) = 0` using `fun w => by push_cast; ring`. Establish `hx' : ∀ w, ((-(((B.mα w - B.mβ w : ℤ) : ℚ) / 2) : ℚ) : ℂ) + (((B.mα w - B.mβ w : ℤ) : ℂ) / 2) = 0` using `fun w => by push_cast; ring`. Establish `hct : ∀ w, (B.mβ w : ℂ) / 2 = ((0 : ℚ) : ℂ) + (B.mβ w : ℂ) / 2` using `fun w => by push_cast; ring`.

Establish `hct' : ∀ w, (B.mα w : ℂ) / 2 = ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (B.mβ w : ℂ) / 2` using `fun w => by push_cast; ring`. Use `⟨side_quot B G.M om N p Φ Ψ _ _ hp _ hx hΨ hr hb.cm A hA1 hAθ hW1 hadm, side_quot B G.M' om' N p' Φ' Ψ' _ _ hp' _ hx' hΨ' hr' hb.cm A' hA1' hAθ' hW1' hadm', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ f hf f' hf' f₁ f₁' h1 h1' e`. Take `⟨Yg, -, hY⟩` from `i_genex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ`. Express the relevant statement in the definitionally equal form `(PiTensorProduct.map p ∘ₗ Ψ) f₁ = (PiTensorProduct.map p' ∘ₗ Ψ') f₁'`.

Rewrite using `[side_wlie B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 γ hγ Yg hY hf h1, side_wlie B G.M' om' N p' Φ' Ψ' _ _ hp' _ _ hct' hΨ' hr' C hW2' γ hγ Yg hY hf' h1']`. Conclude with `congrArg _ e`. Introduce `k hk f hf f' hf' f₁ f₁' h1 h1' e`. Take `⟨γ, hγ, Yg, hgen, hKC, hγ1⟩` from `i_kline i_lineex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2`. Take `⟨T, L, U, e1, e2, hU, hL⟩` from `side_wcpt B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 hadm γ hγ Yg hgen hKC hγ1 hf h1`.

Take `⟨T', L', U', e1', e2', hU', hL'⟩` from `side_wcpt B G.M' om' N p' Φ' Ψ' _ _ hp' _ _ hct' hΨ' hr' C hW2' hadm' γ hγ Yg hgen hKC hγ1 hf' h1'`. Express the relevant statement in the definitionally equal form `(PiTensorProduct.map p ∘ₗ Ψ) f₁ = (PiTensorProduct.map p' ∘ₗ Ψ') f₁'`. Express the relevant statement in the definitionally equal form `(PiTensorProduct.map p ∘ₗ Ψ) f = (PiTensorProduct.map p' ∘ₗ Ψ') f' at e`. Rewrite using `[e2, e2']`. Rewrite `e` using `[e1, e1']`.

Conclude with `exp_equiv hU hU' hL hL' e`. Conclude with `(i_tensirr _ _ _ N fun w => ⟨hirr w, hsc w⟩).1`. Introduce `N0 hN0 _`. Use `(i_tensirr _ _ _ N fun w => ⟨hirr w, hsc w⟩).2 N0 fun w Z hZ y hy => ?_` and prove the remaining obligations. Take `⟨T, rfl⟩` from `map_surj p (fun w => (hp w).1) y`.

Set `Yg : InfinitePlace F → Mat _ _` to `Function.update (fun _ => 0) w Z`. Establish `hYu : ∀ w', Yg w' ∈ upq _ _` using `fun w' => by`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Simplify `hZ` using `[Yg]`.

Simplify `zero_mem_upq _ _` using `[Yg, Function.update_of_ne h]`. Take `⟨γ, hγ, hgen⟩` from `i_lineex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 Yg hYu`. Establish `hpΦ : (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T`. Rewrite using `[LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]`. Establish `hf : Φ T ∈ G.M.Pol B.ψ B.emb` using `hr ▸ LinearMap.mem_range_self Φ T`.

Establish `hsd` using `hW2 γ hγ Yg hgen T`. Establish `h1` using `(i_actslaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd`. Establish `hin` using `hN0 γ hγ (Φ T) hf _ h1 (by change (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) ∈ N0; rw [hpΦ]; exact hy)`. Express the relevant statement in the definitionally equal form `(PiTensorProduct.map p ∘ₗ Ψ) _ ∈ N0 at hin`. Rewrite `hin` using `[side_wlie B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 γ hγ Yg hgen hf h1, hpΦ]`.

Establish `hsum : sumPl (fun w' => (N w').act (Yg w') + ((B.mβ w' : ℂ) / 2 * (Yg w').trace) • 1) = atPl w ((N w).act Z) + (((B.mβ w : ℂ) / 2) * Z.trace) • 1`. Unfold `sumPl`. Rewrite using `[Finset.sum_eq_single w]`. Simplify using `[Yg, atPl_add, atPl_smul, atPl_one]`. Introduce `w' _ h`.

Simplify using `[Yg, Function.update_of_ne h, atPl_zero]`. Simplify using the standard rewrite rules. Rewrite `hin` using `[hsum, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]`. Simplify using `using N0.sub_mem hin (N0.smul_mem (((B.mβ w : ℂ) / 2) * Z.trace) hy)`.
-/
theorem kReal_of_lie (hsec : GlobalTheory.RealLift.LieSecond) (hfst : GlobalTheory.RealLift.LieFirst) : GlobalTheory.ThK.KReal := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, hw'⟩ := h
  choose N p p' hp hp' hirr hsc using fun w => onePlace a a' G.p G.q (B.mα w - B.mβ w) hg.even (hg.kappa w)
    (i_parity F E σ B a a' G X om om' ⟨hb, hg, hc, hw, hw'⟩ w) hg.eBig hg.aBig
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose A' hA' hAθ' using fun w => i_frameex _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hA1' : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A' w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA' w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A' C := ⟨one_mul _, hA1', hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  obtain ⟨Φ', hΦ'⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C hb.cm hb.std fr'
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hr' := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C Φ' hb.cm hb.std fr' hAθ' hCθ hΦ'
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw'
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  have hW2' := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C Φ' _ X.α B.mα hb.cm hb.std fr' hΦ' hwp'.1
    hc.expα
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  obtain ⟨d', hd', hB1'⟩ := hwp'.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hW1' := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d' 1 Complex.I A' C Φ' _ _ _ hb.cm hb.std fr' hΦ' hd' hB1'
    (hasExp_div B.emb hc.expα hc.expβ)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hadm' := fun g => (hwp'.isUSplitting).adm g
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Φ' (LinearMap.ker_eq_bot.2 hΦ'.1)
  let Rm : RealMaps F a a' := ⟨PiTensorProduct ℂ fun w => (N w).V, PiTensorProduct.map p ∘ₗ Ψ, PiTensorProduct.map p' ∘ₗ Ψ'⟩
  refine ⟨Rm, ?_⟩
  have hx : ∀ w, (((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) = 0 := fun w => by
    push_cast; ring
  have hx' : ∀ w, ((-(((B.mα w - B.mβ w : ℤ) : ℚ) / 2) : ℚ) : ℂ) + (((B.mα w - B.mβ w : ℤ) : ℂ) / 2) = 0 := fun w => by
    push_cast; ring
  have hct : ∀ w, (B.mβ w : ℂ) / 2 = ((0 : ℚ) : ℂ) + (B.mβ w : ℂ) / 2 := fun w => by push_cast; ring
  have hct' : ∀ w, (B.mα w : ℂ) / 2 = ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (B.mβ w : ℂ) / 2 := fun w => by
    push_cast; ring
  refine ⟨side_quot B G.M om N p Φ Ψ _ _ hp _ hx hΨ hr hb.cm A hA1 hAθ hW1 hadm,
    side_quot B G.M' om' N p' Φ' Ψ' _ _ hp' _ hx' hΨ' hr' hb.cm A' hA1' hAθ' hW1' hadm', ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f' hf' f₁ f₁' h1 h1' e
    obtain ⟨Yg, -, hY⟩ := i_genex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
    change (PiTensorProduct.map p ∘ₗ Ψ) f₁ = (PiTensorProduct.map p' ∘ₗ Ψ') f₁'
    rw [side_wlie B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 γ hγ Yg hY hf h1,
      side_wlie B G.M' om' N p' Φ' Ψ' _ _ hp' _ _ hct' hΨ' hr' C hW2' γ hγ Yg hY hf' h1']
    exact congrArg _ e
  · intro k hk f hf f' hf' f₁ f₁' h1 h1' e
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
      i_kline i_lineex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2
    obtain ⟨T, L, U, e1, e2, hU, hL⟩ := side_wcpt B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 hadm γ hγ Yg hgen hKC hγ1 hf h1
    obtain ⟨T', L', U', e1', e2', hU', hL'⟩ :=
      side_wcpt B G.M' om' N p' Φ' Ψ' _ _ hp' _ _ hct' hΨ' hr' C hW2' hadm' γ hγ Yg hgen hKC hγ1 hf' h1'
    change (PiTensorProduct.map p ∘ₗ Ψ) f₁ = (PiTensorProduct.map p' ∘ₗ Ψ') f₁'
    change (PiTensorProduct.map p ∘ₗ Ψ) f = (PiTensorProduct.map p' ∘ₗ Ψ') f' at e
    rw [e2, e2']
    rw [e1, e1'] at e
    exact exp_equiv hU hU' hL hL' e
  · exact (i_tensirr _ _ _ N fun w => ⟨hirr w, hsc w⟩).1
  · intro N0 hN0 _
    refine (i_tensirr _ _ _ N fun w => ⟨hirr w, hsc w⟩).2 N0 fun w Z hZ y hy => ?_
    obtain ⟨T, rfl⟩ := map_surj p (fun w => (hp w).1) y
    let Yg : InfinitePlace F → Mat _ _ := Function.update (fun _ => 0) w Z
    have hYu : ∀ w', Yg w' ∈ upq _ _ := fun w' => by
      by_cases h : w' = w
      · subst h; simpa [Yg] using hZ
      · simpa [Yg, Function.update_of_ne h] using zero_mem_upq _ _
    obtain ⟨γ, hγ, hgen⟩ := i_lineex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 Yg hYu
    have hpΦ : (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) = PiTensorProduct.map p T := by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
    have hf : Φ T ∈ G.M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ T
    have hsd := hW2 γ hγ Yg hgen T
    have h1 := (i_actslaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
    have hin := hN0 γ hγ (Φ T) hf _ h1 (by change (PiTensorProduct.map p ∘ₗ Ψ) (Φ T) ∈ N0; rw [hpΦ]; exact hy)
    change (PiTensorProduct.map p ∘ₗ Ψ) _ ∈ N0 at hin
    rw [side_wlie B G.M om N p Φ Ψ _ _ hp _ _ hct hΨ hr C hW2 γ hγ Yg hgen hf h1, hpΦ] at hin
    have hsum : sumPl (fun w' => (N w').act (Yg w') + ((B.mβ w' : ℂ) / 2 * (Yg w').trace) • 1) =
        atPl w ((N w).act Z) + (((B.mβ w : ℂ) / 2) * Z.trace) • 1 := by
      unfold sumPl
      rw [Finset.sum_eq_single w]
      · simp [Yg, atPl_add, atPl_smul, atPl_one]
      · intro w' _ h
        simp [Yg, Function.update_of_ne h, atPl_zero]
      · simp
    rw [hsum, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at hin
    simpa using N0.sub_mem hin (N0.smul_mem (((B.mβ w : ℂ) / 2) * Z.trace) hy)

end PositivityTheory.KRealA

end
