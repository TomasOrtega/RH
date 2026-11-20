import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElementStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjoinStableAndCommutes
set_option maxHeartbeats 1600000

noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `letI := X.fld`. Use `letI := X.alg`. Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use `HahnSeries.ext (funext fun r => ?_)` and prove the remaining obligations. Use `show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r`.

Rewrite using `[X.gal_exp, X.gal_exp, X.gal_exp, AlgEquiv.mul_apply]`.
-/
theorem gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) : X.gal (s * s') f = X.gal s (X.gal s' f) := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp, AlgEquiv.mul_apply]

/- English proof (translation)
Use `letI := X.fld`. Use `letI := X.alg`. Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use `HahnSeries.ext (funext fun r => ?_)` and prove the remaining obligations. Use `show (X.exp (X.gal 1 f)).coeff r = (X.exp f).coeff r`.

Rewrite using `[X.gal_exp, AlgEquiv.one_apply]`.
-/
theorem gal_one_apply (X : Tower Ω ε) (f : X.K) : X.gal 1 f = f := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal 1 f)).coeff r = (X.exp f).coeff r
  rw [X.gal_exp, AlgEquiv.one_apply]

/- English proof (translation)
Use `letI := X.fld`. Unfold `Tower.kmap`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]`.

Rewrite using `[← LinearMap.comp_apply (AdicCompletion.map _ _), AdicCompletion.map_comp, ← LinearMap.baseChange_comp]`. Establish `h : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) = AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (ψ.trans φ).toMonoidHom))`. Use extensionality with `u`. Both sides reduce to the same expression. Rewrite using `[h]`.
-/
theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) :
    X.kmap l φ ∘ₗ X.kmap l ψ = X.kmap l (ψ.trans φ) := by
  letI := X.fld
  unfold Tower.kmap
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [← LinearMap.comp_apply (AdicCompletion.map _ _), AdicCompletion.map_comp, ← LinearMap.baseChange_comp]
  have h : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) =
      AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (ψ.trans φ).toMonoidHom)) := by
    ext u; rfl
  rw [h]

/- English proof (translation)
Use `letI := X.fld`. Unfold `Tower.kmap`. Establish `h : AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom)) = LinearMap.id`. Use extensionality with `u`. Both sides reduce to the same expression.

Rewrite using `[h, LinearMap.baseChange_id, AdicCompletion.map_id]`. Both sides reduce to the same expression.
-/
theorem kmap_refl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.kmap l (RingEquiv.refl X.K) = LinearMap.id := by
  letI := X.fld
  unfold Tower.kmap
  have h : AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom)) =
      LinearMap.id := by
    ext u; rfl
  rw [h, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

/- English proof (translation)
Establish `hg : X.gal (s * s') = (X.gal s').trans (X.gal s)` using `RingEquiv.ext (gal_mul_apply X s s')`. Establish `hr : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv` using `RingEquiv.ext fun x => rfl`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `b`. Use function extensionality and compare the values at `u`.

Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]`. Rewrite using `[← LinearMap.comp_apply (X.kmap l (X.gal s)), kmap_comp, ← hg, hr, map_mul, Units.val_mul]`. Use `congr 2`. Apply the tactic sequence `ext i; fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]`.
-/
theorem galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) :
    X.galB l (s * s') = X.galB l s ∘ₗ X.galB l s' := by
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := RingEquiv.ext (gal_mul_apply X s s')
  have hr : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (X.kmap l (X.gal s)), kmap_comp, ← hg, hr, map_mul, Units.val_mul]
  congr 2
  ext i; fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

/- English proof (translation)
Establish `hg : X.gal 1 = RingEquiv.refl X.K` using `RingEquiv.ext (gal_one_apply X)`. Establish `hr : (1 : Ω ≃ₐ[ℚ] Ω).toRingEquiv = 1` using `RingEquiv.ext fun x => rfl`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `b`. Use function extensionality and compare the values at `u`.

Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]`. Rewrite using `[hg, kmap_refl, hr, map_one, Units.val_one, one_mul, LinearMap.id_apply]`. Use `congr 1`. Apply the tactic sequence `ext i; fin_cases i <;> rfl`.
-/
theorem galB_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.galB l 1 = LinearMap.id := by
  have hg : X.gal 1 = RingEquiv.refl X.K := RingEquiv.ext (gal_one_apply X)
  have hr : (1 : Ω ≃ₐ[ℚ] Ω).toRingEquiv = 1 := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [hg, kmap_refl, hr, map_one, Units.val_one, one_mul, LinearMap.id_apply]
  congr 1
  ext i; fin_cases i <;> rfl

section BC
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] (E : Type) [Field E] [Algebra R E]
  (B : Submodule R M)

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Use `⟨LinearMap.baseChange E (f.restrict hf) y, ?_⟩` and prove the remaining obligations. Establish `h : B.subtype ∘ₗ f.restrict hf = f ∘ₗ B.subtype` using `LinearMap.ext fun b => rfl`. Use `congrArg (fun φ => LinearMap.baseChange E φ y) h` as an intermediate fact. Simplify `this` using `[LinearMap.baseChange_comp]`.
-/
theorem bc_mem (f : M →ₗ[R] M) (hf : ∀ b ∈ B, f b ∈ B) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f x ∈ LinearMap.range (LinearMap.baseChange E B.subtype) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨LinearMap.baseChange E (f.restrict hf) y, ?_⟩
  have h : B.subtype ∘ₗ f.restrict hf = f ∘ₗ B.subtype := LinearMap.ext fun b => rfl
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Establish `h : f ∘ₗ g ∘ₗ B.subtype = g ∘ₗ f ∘ₗ B.subtype` using `LinearMap.ext fun b => hfg b b.2`. Use `congrArg (fun φ => LinearMap.baseChange E φ y) h` as an intermediate fact. Simplify `this` using `[LinearMap.baseChange_comp]`.
-/
theorem bc_comm (f g : M →ₗ[R] M) (hfg : ∀ b ∈ B, f (g b) = g (f b)) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f (LinearMap.baseChange E g x) = LinearMap.baseChange E g (LinearMap.baseChange E f x) := by
  obtain ⟨y, rfl⟩ := hx
  have h : f ∘ₗ g ∘ₗ B.subtype = g ∘ₗ f ∘ₗ B.subtype := LinearMap.ext fun b => hfg b b.2
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

end BC

section Gen
variable {E V G : Type} [Field E] [AddCommGroup V] [Module E V]

/- English proof (translation)
Proceed by induction on `hQ using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨T, hT, rfl⟩` from `hx`. Simplify using `[FreeAlgebra.lift_ι_apply, hy T hT]`. Consider the case `algebraMap r => simp`.

Consider the case `add a b _ _ ha hb => simp [ha, hb, add_smul]`. Consider the case `mul a b _ _ ha hb => simp [Module.End.mul_apply, ha, hb, smul_smul, mul_comm]`.
-/
theorem adj_eigen (A : Set Letter) (f : Letter → Module.End E V) (lam : Letter → E) (y : V)
    (hy : ∀ T ∈ A, f T y = lam T • y) (Q : FreeAlgebra E Letter)
    (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    FreeAlgebra.lift E f Q y = FreeAlgebra.lift E lam Q • y := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [FreeAlgebra.lift_ι_apply, hy T hT]
  | algebraMap r => simp
  | add a b _ _ ha hb => simp [ha, hb, add_smul]
  | mul a b _ _ ha hb => simp [Module.End.mul_apply, ha, hb, smul_smul, mul_comm]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes`. Consider the case `exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes`. Consider the case `(apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes ..)`.
-/
theorem adj_stab (A : Set Letter) (f : Letter → Module.End E V) (W : Submodule E V) (g : G → Module.End E V)
    (hs : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) (hc : ∀ T ∈ A, ∀ s, ∀ x ∈ W, f T (g s x) = g s (f T x))
    (Q : FreeAlgebra E Letter) (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    ∀ x ∈ W, FreeAlgebra.lift E f Q x ∈ W ∧ ∀ s, g s (FreeAlgebra.lift E f Q x) = FreeAlgebra.lift E f Q (g s x) := by
  first
  | exact @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | (apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes ..)

end Gen

end GlobalTheory.KZ.HeckeProj

namespace GlobalTheory.KZ.HeckeProj

/- English proof (translation)
Introduce `Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw E _ _ _ hnorm lam hSS ρ S0 htc hdc hfr hirr`. Take `⟨P, hPadm, hP1, hPe⟩` from `hSS`. Establish `hgal : ∀ s, ∀ x ∈ X.VB N l w E, X.galV l E s x ∈ X.VB N l w E` using `fun s x hx => HeckeProj.bc_mem E (X.B N l w) (X.galB l s) (GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s) x hx`. Establish `hstab : ∀ T ∈ {T | admitted N l T}, ∀ x ∈ X.VB N l w E, X.opV N l E T x ∈ X.VB N l w E` using `fun T hT x hx => HeckeProj.bc_mem E (X.B N l w) (X.op N l T) (GlobalTheory.T.hecke_letter_preserves_basis_set ε X hε hj N l w hl hN hNl hw T hT) x hx`. Establish `hcomm : ∀ T ∈ {T | admitted N l T}, ∀ s, ∀ x ∈ X.VB N l w E, X.opV N l E T (X.galV l E s x) = X.galV l E s (X.opV N l E T x)` using `fun T hT s x hx => HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.galB l s) (fun b hb => GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl hN hNl hw T hT s b hb) x hx`.

Establish `hfin : Module.Finite ℤ_[l] (X.B N l w)` using `(GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl hN hNl hw).2`. Establish `hVBfin : FiniteDimensional E (X.VB N l w E)`. Unfold `Tower.VB`. Use `infer_instance`. Use `set Pv := FreeAlgebra.lift E (X.opV N l E) P with hPv`.

Establish `hPst` using `HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E) (X.galV l E) hstab hcomm P hPadm`. Establish `heig : ∀ x ∈ X.VB N l w E, ∀ T, admitted N l T → X.opV N l E T (Pv x) = lam T • Pv x`. Introduce `x hx T hT`. Use `hPe x hx T hT` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.

Establish `hfix : ∀ y, (∀ T, admitted N l T → X.opV N l E T y = lam T • y) → Pv y = y`. Introduce `y hy`. Use `HeckeProj.adj_eigen {T | admitted N l T} (X.opV N l E) lam y hy P hPadm` as an intermediate fact. Rewrite `this` using `[hP1, one_smul]`. Conclude with `this`.

Use `set U : Submodule E (E ⊗[ℤ_[l]] X.Fn l) := (X.VB N l w E).map Pv with hU`. Establish `hUVB : ∀ u ∈ U, u ∈ X.VB N l w E`. Introduce and unpack `u ⟨x, hx, rfl⟩`. Conclude with `(hPst x hx).1`. Establish `hUeig : ∀ u ∈ U, ∀ T, admitted N l T → X.opV N l E T u = lam T • u`.

Introduce and unpack `u ⟨x, hx, rfl⟩`. Conclude with `heig x hx`. Establish `hUfix : ∀ u ∈ U, Pv u = u` using `fun u hu => hfix u (hUeig u hu)`. Establish `hUgal : ∀ s, ∀ u ∈ U, X.galV l E s u ∈ U`. Introduce and unpack `s u ⟨x, hx, rfl⟩`.

Conclude with `⟨X.galV l E s x, hgal s x hx, ((hPst x hx).2 s).symm⟩`. Use `haveI : FiniteDimensional E U := by rw [hU]; infer_instance`. Establish `hgm : ∀ s s', X.galV l E (s * s') = X.galV l E s * X.galV l E s'`. Introduce `s s'`. Simplify using `only [Tower.galV, HeckeProj.galB_mul, LinearMap.baseChange_comp, Module.End.mul_eq_comp]`.

Establish `hg1 : X.galV l E 1 = 1`. Simplify using `only [Tower.galV, HeckeProj.galB_one, LinearMap.baseChange_id, Module.End.one_eq_id]`. Set `σU : (Ω ≃ₐ[ℚ] Ω) →* Module.End E U` to `{ toFun := fun s => (X.galV l E s).restrict (hUgal s) map_one' := by`. Use extensionality with `u`. Simplify using `[LinearMap.restrict_apply, hg1]`.

Use the proof step `map_mul' := by`. Introduce `s s'`. Use extensionality with `u`. Simplify using `[LinearMap.restrict_apply, hgm, Module.End.mul_apply] }`. Establish `hσU : ∀ s (u : U), ((σU s u : U) : E ⊗[ℤ_[l]] X.Fn l) = X.galV l E s u` using `fun s u => rfl`.

Establish `h2 : (2 : E) ≠ 0`. Introduce `h`. Establish `h' : algebraMap ℤ_[l] E 2 = 0` using `by rw [map_ofNat]; exact h`. Use `hnorm 2` as an intermediate fact. Rewrite `this` using `[h', norm_zero]`.

Establish `h0 : (2 : ℤ_[l]) = 0` using `norm_eq_zero.mp this.symm`. Conclude with `two_ne_zero h0`. Establish `hCH : ∀ g, σU g * σU g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σU g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0`. Introduce `g`. Use extensionality with `u`.

Establish `hu` using `GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element ε X hε hj N l w hl hN hNl hw hnorm lam (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) S0 htc hdc hfr (u : E ⊗[ℤ_[l]] X.Fn l) (hUVB u u.2) (hUeig u …`. Simplify `hu` using `[Module.End.mul_apply, hσU]`. Take `⟨m, π', s', h1, h2', h3, h4⟩` from `GlobalTheory.T.two_dim_rep_quadratic_relation h2 ρ hirr σU hCH`. Set `Pr : X.VB N l w E →ₗ[E] U` to `LinearMap.codRestrict U (Pv ∘ₗ (X.VB N l w E).subtype) (fun x => Submodule.mem_map_of_mem x.2)`. Establish `hext : ∀ i : Fin m, ∃ g : (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E), g ∘ₗ (X.VB N l w E).subtype = π' i ∘ₗ Pr` using `fun i => LinearMap.exists_extend _`.

Use `choose π hπ using hext`. Establish `hπx : ∀ i x (hx : x ∈ X.VB N l w E), π i x = π' i (Pr ⟨x, hx⟩)` using `fun i x hx => LinearMap.congr_fun (hπ i) ⟨x, hx⟩`. Establish `hTT : ∀ T ∈ {T | admitted N l T}, ∀ T' : {T // admitted N l T}, ∀ x ∈ X.VB N l w E, X.opV N l E T (X.opV N l E T'.1 x) = X.opV N l E T'.1 (X.opV N l E T x)` using `fun T hT T' x hx => HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.op N l T'.1) (fun b hb => GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X hε hj N l w hl hN hNl hw T T'.1 hT T'.2 b hb) x hx`. Establish `hPT` using `HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E) (fun T' : {T // admitted N l T} => X.opV N l E T'.1) hstab hTT P hPadm`. Establish `hsumP : ∀ x ∈ X.VB N l w E, Pv x = ∑ i, (U.subtype ∘ₗ s' i) (π i x)`.

Introduce `x hx`. Use `LinearMap.congr_fun h4 (Pr ⟨x, hx⟩)` as an intermediate fact. Establish `e2 : (∑ i, s' i (π' i (Pr ⟨x, hx⟩))) = Pr ⟨x, hx⟩` using `by simpa [LinearMap.sum_apply] using this`. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype, hπx _ x hx]`. Rewrite using `[← Submodule.coe_sum, e2]`.

Both sides reduce to the same expression. Use `⟨m, π, fun i => U.subtype ∘ₗ s' i, P, hPadm, hP1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx hxe`. Rewrite using `[← hsumP x hx]`. Conclude with `hfix x hxe`.

Introduce `i v`. Conclude with `hUVB _ (s' i v).2`. Introduce `i s x hx`. Rewrite using `[hπx i _ (hgal s x hx), hπx i x hx]`. Establish `e : Pr ⟨X.galV l E s x, hgal s x hx⟩ = σU s (Pr ⟨x, hx⟩)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, hσU]`. Conclude with `((hPst x hx).2 s).symm`. Rewrite using `[e]`. Use `LinearMap.congr_fun (h1 i s) (Pr ⟨x, hx⟩)` as an intermediate fact.

Simplify `this` using `[Matrix.toLin'_apply]`. Introduce `i s v`. Use `LinearMap.congr_fun (h2' i s) v` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.comp_apply]`. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype]`.

Rewrite using `[← hσU, this]`. Simplify using `[Matrix.toLin'_apply]`. Introduce `i T v hT`. Conclude with `hUeig _ (s' i v).2 T hT`. Introduce `i T hT x hx`.

Establish `hTx` using `hstab T hT x hx`. Rewrite using `[hπx i _ hTx, hπx i x hx]`. Establish `e : Pr ⟨X.opV N l E T x, hTx⟩ = lam T • Pr ⟨x, hx⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hc` using `(hPT x hx).2 ⟨T, hT⟩`.

Simplify using `only at hc`. Simplify using `only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul]`. Rewrite using `[← hc]`. Conclude with `hUeig _ (Submodule.mem_map_of_mem hx) T hT`. Rewrite using `[e, map_smul]`.

Introduce `i j v`. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype]`. Rewrite using `[hπx i _ (hUVB _ (s' j v).2)]`. Establish `e : Pr ⟨((s' j v : U) : E ⊗[ℤ_[l]] X.Fn l), hUVB _ (s' j v).2⟩ = s' j v`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype]`. Conclude with `hUfix _ (s' j v).2`. Rewrite using `[e]`. Use `LinearMap.congr_fun (h3 i j) v` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply]`.

Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `x hx`. Conclude with `hsumP x hx`.
-/
theorem heckeProj_main : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw E _ _ _ hnorm lam hSS ρ S0 htc hdc hfr hirr
  obtain ⟨P, hPadm, hP1, hPe⟩ := hSS
  have hgal : ∀ s, ∀ x ∈ X.VB N l w E, X.galV l E s x ∈ X.VB N l w E := fun s x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.galB l s) (GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s) x hx
  have hstab : ∀ T ∈ {T | admitted N l T}, ∀ x ∈ X.VB N l w E, X.opV N l E T x ∈ X.VB N l w E := fun T hT x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.op N l T) (GlobalTheory.T.hecke_letter_preserves_basis_set ε X hε hj N l w hl hN hNl hw T hT) x hx
  have hcomm : ∀ T ∈ {T | admitted N l T}, ∀ s, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.galV l E s x) = X.galV l E s (X.opV N l E T x) := fun T hT s x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.galB l s)
      (fun b hb => GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl hN hNl hw T hT s b hb) x hx
  have hfin : Module.Finite ℤ_[l] (X.B N l w) := (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl hN hNl hw).2
  have hVBfin : FiniteDimensional E (X.VB N l w E) := by
    unfold Tower.VB; infer_instance
  set Pv := FreeAlgebra.lift E (X.opV N l E) P with hPv
  have hPst := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E) (X.galV l E) hstab hcomm P hPadm
  have heig : ∀ x ∈ X.VB N l w E, ∀ T, admitted N l T → X.opV N l E T (Pv x) = lam T • Pv x := by
    intro x hx T hT
    have := hPe x hx T hT
    simpa [sub_eq_zero] using this
  have hfix : ∀ y, (∀ T, admitted N l T → X.opV N l E T y = lam T • y) → Pv y = y := by
    intro y hy
    have := HeckeProj.adj_eigen {T | admitted N l T} (X.opV N l E) lam y hy P hPadm
    rw [hP1, one_smul] at this
    exact this
  set U : Submodule E (E ⊗[ℤ_[l]] X.Fn l) := (X.VB N l w E).map Pv with hU
  have hUVB : ∀ u ∈ U, u ∈ X.VB N l w E := by
    rintro u ⟨x, hx, rfl⟩; exact (hPst x hx).1
  have hUeig : ∀ u ∈ U, ∀ T, admitted N l T → X.opV N l E T u = lam T • u := by
    rintro u ⟨x, hx, rfl⟩; exact heig x hx
  have hUfix : ∀ u ∈ U, Pv u = u := fun u hu => hfix u (hUeig u hu)
  have hUgal : ∀ s, ∀ u ∈ U, X.galV l E s u ∈ U := by
    rintro s u ⟨x, hx, rfl⟩
    exact ⟨X.galV l E s x, hgal s x hx, ((hPst x hx).2 s).symm⟩
  haveI : FiniteDimensional E U := by rw [hU]; infer_instance
  have hgm : ∀ s s', X.galV l E (s * s') = X.galV l E s * X.galV l E s' := by
    intro s s'
    simp only [Tower.galV, HeckeProj.galB_mul, LinearMap.baseChange_comp, Module.End.mul_eq_comp]
  have hg1 : X.galV l E 1 = 1 := by
    simp only [Tower.galV, HeckeProj.galB_one, LinearMap.baseChange_id, Module.End.one_eq_id]
  let σU : (Ω ≃ₐ[ℚ] Ω) →* Module.End E U :=
    { toFun := fun s => (X.galV l E s).restrict (hUgal s)
      map_one' := by
        ext u; simp [LinearMap.restrict_apply, hg1]
      map_mul' := by
        intro s s'; ext u; simp [LinearMap.restrict_apply, hgm, Module.End.mul_apply] }
  have hσU : ∀ s (u : U), ((σU s u : U) : E ⊗[ℤ_[l]] X.Fn l) = X.galV l E s u := fun s u => rfl
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] E 2 = 0 := by rw [map_ofNat]; exact h
    have := hnorm 2
    rw [h', norm_zero] at this
    have h0 : (2 : ℤ_[l]) = 0 := norm_eq_zero.mp this.symm
    exact two_ne_zero h0
  have hCH : ∀ g, σU g * σU g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σU g +
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0 := by
    intro g
    ext u
    have hu := GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element ε X hε hj N l w hl hN hNl hw hnorm lam
      (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E))
      S0 htc hdc hfr (u : E ⊗[ℤ_[l]] X.Fn l) (hUVB u u.2) (hUeig u u.2) g
    simpa [Module.End.mul_apply, hσU] using hu
  obtain ⟨m, π', s', h1, h2', h3, h4⟩ := GlobalTheory.T.two_dim_rep_quadratic_relation h2 ρ hirr σU hCH
  let Pr : X.VB N l w E →ₗ[E] U :=
    LinearMap.codRestrict U (Pv ∘ₗ (X.VB N l w E).subtype) (fun x => Submodule.mem_map_of_mem x.2)
  have hext : ∀ i : Fin m, ∃ g : (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E),
      g ∘ₗ (X.VB N l w E).subtype = π' i ∘ₗ Pr := fun i => LinearMap.exists_extend _
  choose π hπ using hext
  have hπx : ∀ i x (hx : x ∈ X.VB N l w E), π i x = π' i (Pr ⟨x, hx⟩) := fun i x hx =>
    LinearMap.congr_fun (hπ i) ⟨x, hx⟩
  have hTT : ∀ T ∈ {T | admitted N l T}, ∀ T' : {T // admitted N l T}, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.opV N l E T'.1 x) = X.opV N l E T'.1 (X.opV N l E T x) := fun T hT T' x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.op N l T'.1)
      (fun b hb => GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X hε hj N l w hl hN hNl hw T T'.1 hT T'.2 b hb) x hx
  have hPT := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E)
    (fun T' : {T // admitted N l T} => X.opV N l E T'.1) hstab hTT P hPadm
  have hsumP : ∀ x ∈ X.VB N l w E, Pv x = ∑ i, (U.subtype ∘ₗ s' i) (π i x) := by
    intro x hx
    have := LinearMap.congr_fun h4 (Pr ⟨x, hx⟩)
    have e2 : (∑ i, s' i (π' i (Pr ⟨x, hx⟩))) = Pr ⟨x, hx⟩ := by simpa [LinearMap.sum_apply] using this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, hπx _ x hx]
    rw [← Submodule.coe_sum, e2]
    rfl
  refine ⟨m, π, fun i => U.subtype ∘ₗ s' i, P, hPadm, hP1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hxe
    rw [← hsumP x hx]
    exact hfix x hxe
  · intro i v
    exact hUVB _ (s' i v).2
  · intro i s x hx
    rw [hπx i _ (hgal s x hx), hπx i x hx]
    have e : Pr ⟨X.galV l E s x, hgal s x hx⟩ = σU s (Pr ⟨x, hx⟩) := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, hσU]
      exact ((hPst x hx).2 s).symm
    rw [e]
    have := LinearMap.congr_fun (h1 i s) (Pr ⟨x, hx⟩)
    simpa [Matrix.toLin'_apply] using this
  · intro i s v
    have := LinearMap.congr_fun (h2' i s) v
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [← hσU, this]
    simp [Matrix.toLin'_apply]
  · intro i T v hT
    exact hUeig _ (s' i v).2 T hT
  · intro i T hT x hx
    have hTx := hstab T hT x hx
    rw [hπx i _ hTx, hπx i x hx]
    have e : Pr ⟨X.opV N l E T x, hTx⟩ = lam T • Pr ⟨x, hx⟩ := by
      apply Subtype.ext
      have hc := (hPT x hx).2 ⟨T, hT⟩
      simp only at hc
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul]
      rw [← hc]
      exact hUeig _ (Submodule.mem_map_of_mem hx) T hT
    rw [e, map_smul]
  · intro i j v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hπx i _ (hUVB _ (s' j v).2)]
    have e : Pr ⟨((s' j v : U) : E ⊗[ℤ_[l]] X.Fn l), hUVB _ (s' j v).2⟩ = s' j v := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact hUfix _ (s' j v).2
    rw [e]
    have := LinearMap.congr_fun (h3 i j) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    split_ifs <;> simp
  · intro x hx
    exact hsumP x hx

end GlobalTheory.KZ.HeckeProj
