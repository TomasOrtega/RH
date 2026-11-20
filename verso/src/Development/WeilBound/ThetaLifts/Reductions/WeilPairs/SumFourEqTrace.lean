import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfTrivial

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
open GlobalTheory.FinLatF

namespace PositivityTheory.ThKW.LatA

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => Eq.symm ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `(Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `h1 : (P * (k.map σ)ᵀ * P') * k = 1`. Rewrite using `[Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]`. Establish `h2 : k * (P * (k.map σ)ᵀ * P') = 1` using `mul_eq_one_comm.1 h1`. Establish `hP' : P' * P = 1` using `mul_eq_one_comm.1 hP`. Establish `hk' : k * P * (k.map σ)ᵀ = P`.

Combine the equalities or inequalities in the displayed calculation. Establish `e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) = (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k`. Simplify using `only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc k, hk']`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]`.
-/
theorem sig_sig {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

/- English proof (translation)
Establish `h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS.2)]`. Conclude with `Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one`. Conclude with `sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E)) (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y`.
-/
theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS.2)]
    exact Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one
  exact sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E)) (JS.map (incAF F E)) (mtF σ JS g⁻¹)
    h1 h.2 (g⁻¹).2 x y

/- English proof (translation)
Unfold `symplOF`. Rewrite using `[hOF_actOF hS]`.
-/
theorem symplOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF hS]

/- English proof (translation)
Rewrite using `[gamFF, gamFF, coe_rhoFF, coe_rhoFF, symplOF_actOF hS]`.
-/
theorem gamFF_rhoFF (hS : IsHermND σ JS) (p : GAF σ JS × GAF σ JT) (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  rw [gamFF, gamFF, coe_rhoFF, coe_rhoFF, symplOF_actOF hS]

/- English proof (translation)
Rewrite using `[phaseF, phaseF, coe_rhoFF, ← actOF_smul, symplOHF, symplOHF, symplOF_actOF hS]`.
-/
theorem phaseF_rhoFF (hS : IsHermND σ JS) (w : 𝓞 E) (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) :
    phaseF σ JS JT ξ₀ ψ w (rhoFF σ JS JT p x) = phaseF σ JS JT ξ₀ ψ w x := by
  rw [phaseF, phaseF, coe_rhoFF, ← actOF_smul, symplOHF, symplOHF, symplOF_actOF hS]

/- English proof (translation)
Unfold `phaseF`. Conclude with `(ψ.val_isUnit _).ne_zero`.
-/
theorem phaseF_ne_zero (w : 𝓞 E) (x : XFF F E nS nT) : phaseF σ JS JT ξ₀ ψ w x ≠ 0 := by
  unfold phaseF
  exact (ψ.val_isUnit _).ne_zero

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (1 : Ainf F) + 0 = 1`. Rewrite using `[add_zero]`. Use `show (0 : Af F) + 1 = 1`. Rewrite using `[zero_add]`.
-/
theorem idem_add : pairA F 1 0 + pairA F 0 1 = 1 := by
  refine Prod.ext ?_ ?_
  · show (1 : Ainf F) + 0 = 1
    rw [add_zero]
  · show (0 : Af F) + 1 = 1
    rw [zero_add]

/- English proof (translation)
Rewrite using `[← add_smul, idem_add, one_smul]`.
-/
theorem dec (u : WOF F E nS nT) : u = pairA F 1 0 • u + pairA F 0 1 • u := by
  rw [← add_smul, idem_add, one_smul]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `φ.map_sub _ _`.
-/
theorem map_sub' {R : Type} [CommRing R] (φ : AEF F E →+* R) (u v : WOF F E nS nT) :
    (u - v).map φ = u.map φ - v.map φ := by
  ext i j
  exact φ.map_sub _ _

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← smul_sub]`. Conclude with `GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (by rw [map_sub', h, sub_self])`.
-/
theorem real_eq {u v : WOF F E nS nT} (h : u.map (infPartF F E) = v.map (infPartF F E)) :
    pairA F 1 0 • u = pairA F 1 0 • v := by
  rw [← sub_eq_zero, ← smul_sub]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (by rw [map_sub', h, sub_self])

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← smul_sub]`. Conclude with `GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF (by rw [map_sub', h, sub_self])`.
-/
theorem fin_eq {u v : WOF F E nS nT} (h : u.map (finPartF F E) = v.map (finPartF F E)) :
    pairA F 0 1 • u = pairA F 0 1 • v := by
  rw [← sub_eq_zero, ← smul_sub]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF (by rw [map_sub', h, sub_self])

/- English proof (translation)
Use extensionality with `i j`. Use `show infPartF F E (pairA F 0 1 • u i j) = 0`. Establish `h : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 0` using `by show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 1) = 0 from rfl, TensorProduct.zero_tmul]`. Rewrite using `[Algebra.smul_def, map_mul, h, zero_mul]`.
-/
theorem fin_smul_fin (u : WOF F E nS nT) : (pairA F 0 1 • u).map (infPartF F E) = 0 := by
  ext i j
  show infPartF F E (pairA F 0 1 • u i j) = 0
  have h : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 0 := by
    show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 0
    rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 1) = 0 from rfl, TensorProduct.zero_tmul]
  rw [Algebra.smul_def, map_mul, h, zero_mul]

/- English proof (translation)
Unfold `actOF`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem actOF_smulA (g : GAF σ JS) (h : GAF σ JT) (a : AF F) (x : WOF F E nS nT) :
    actOF σ JS JT g h (a • x) = a • actOF σ JS JT g h x := by
  unfold actOF
  rw [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : (mtF σ JS g⁻¹).map (finPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))`. Establish `h2 : (mtF σ JT h).map (finPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hh)`. Unfold `actOF`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem map_act_fin {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (u : WOF F E nS nT) : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
  have h1 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h2 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `h1 : (mtF σ JS g⁻¹).map (infPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))`. Establish `h2 : (mtF σ JT h).map (infPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hh)`. Unfold `actOF`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem map_act_inf {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GfCF σ JT)
    (u : WOF F E nS nT) : (actOF σ JS JT g h u).map (infPartF F E) = u.map (infPartF F E) := by
  have h1 : (mtF σ JS g⁻¹).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h2 : (mtF σ JT h).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Apply `XFF.ext` to reduce the goal to its premises. Rewrite using `[dec (rhoFF σ JS JT (g, h) x : WOF F E nS nT), real_eq ((rhoFF σ JS JT (g, h) x).fin.trans x.fin.symm), coe_rhoFF, fin_eq (map_act_fin hg hh _), ← dec]`.
-/
theorem rhoFF_real {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [dec (rhoFF σ JS JT (g, h) x : WOF F E nS nT), real_eq ((rhoFF σ JS JT (g, h) x).fin.trans x.fin.symm), coe_rhoFF,
    fin_eq (map_act_fin hg hh _), ← dec]

/- English proof (translation)
Rewrite using `[GlobalTheory.HeisThetaF.symplOHF_smul_left, ← GlobalTheory.HeisThetaF.symplOHF_smul_right, GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF hx, GlobalTheory.HeisThetaF.symplOHF_zero_right]`.
-/
theorem sympl_real_fin (u : WOF F E nS nT) {x : WOF F E nS nT} (hx : x.map (infPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ (pairA F 1 0 • u) x = 0 := by
  rw [GlobalTheory.HeisThetaF.symplOHF_smul_left, ← GlobalTheory.HeisThetaF.symplOHF_smul_right,
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF hx, GlobalTheory.HeisThetaF.symplOHF_zero_right]

/- English proof (translation)
Rewrite using `[GlobalTheory.HeisThetaF.symplOHF_smul_right, ← GlobalTheory.HeisThetaF.symplOHF_smul_left, GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF hx, GlobalTheory.HeisThetaF.symplOHF_zero_left]`.
-/
theorem sympl_fin_real (u : WOF F E nS nT) {x : WOF F E nS nT} (hx : x.map (infPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ x (pairA F 1 0 • u) = 0 := by
  rw [GlobalTheory.HeisThetaF.symplOHF_smul_right, ← GlobalTheory.HeisThetaF.symplOHF_smul_left,
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF hx, GlobalTheory.HeisThetaF.symplOHF_zero_left]

variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨isHeis_opFF hσ hS hT hξ hc h.hw, h.good, h.sd, h.span, gamFF_rhoFF hS, h.fin⟩`.
-/
theorem sys (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatSystem (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS JT) :=
  ⟨isHeis_opFF hσ hS hT hξ hc h.hw, h.good, h.sd, h.span, gamFF_rhoFF hS, h.fin⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.op, h.vac⟩`.
-/
theorem rep (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatRep (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS JT) Om :=
  ⟨h.op, h.vac⟩

/- English proof (translation)
Establish `h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f'` using `Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])`. Establish `h2` using `congrArg Subtype.val (h.op p x f)`. Rewrite `h2` using `[h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF]`. Conclude with `smul_right_injective _ (phaseF_ne_zero w x) h2`.
-/
theorem heis_fin (hS : IsHermND σ JS) (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT)
    (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ x f) :
    (Om p f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT p.1 p.2 x) (Om p f) := by
  have h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f' := Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (h.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF] at h2
  exact smul_right_injective _ (phaseF_ne_zero w x) h2

/- English proof (translation)
Set `L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ` to `(heisLF σ JS JT ξ₀ ψ (pairA F 1 0 • u)).restrict fun f hf => hc _ f hf`. Establish `hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (pairA F 1 0 • u) m` using `fun _ => rfl`. Set `f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ` to `⟨_, hc (pairA F 0 1 • u) f f.2⟩`. Establish `e : f' = L f₁`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hf, hL]`. Use `show _ = heisOF σ JS JT ξ₀ ψ (pairA F 1 0 • u) (heisOF σ JS JT ξ₀ ψ (pairA F 0 1 • u) f)`. Rewrite using `[heisOF_heisOF', sympl_real_fin u (fin_smul_fin u), AddChar.map_zero_eq_one, one_smul, ← dec]`. Rewrite using `[e, (rep h).comm (sys hσ hS hT hξ h) L (fun x v => Subtype.ext (by`. Rewrite using `[hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF', sympl_real_fin u x.fin, sympl_fin_real u x.fin, add_comm])), hL,`.

Use `heis_fin hS h (g, k) (XFF.mk _ (fin_smul_fin u)) f f₁ rfl, XFF.coe_mk, actOF_smulA, heisOF_heisOF',`. Use `sympl_real_fin u (fin_smul_fin _), AddChar.map_zero_eq_one, one_smul, ← real_eq (map_act_inf hg hk u), ← dec]`.
-/
theorem Heisenberg₂ (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) {g : GAF σ JS} {k : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS)
    (hk : k ∈ GlobalTheory.WeilPartsF.GfCF σ JT) (u : WOF F E nS nT) (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ u f) :
    (Om (g, k) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT g k u) (Om (g, k) f) := by
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ :=
    (heisLF σ JS JT ξ₀ ψ (pairA F 1 0 • u)).restrict fun f hf => hc _ f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (pairA F 1 0 • u) m := fun _ => rfl
  let f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ := ⟨_, hc (pairA F 0 1 • u) f f.2⟩
  have e : f' = L f₁ := by
    apply Subtype.ext
    rw [hf, hL]
    show _ = heisOF σ JS JT ξ₀ ψ (pairA F 1 0 • u) (heisOF σ JS JT ξ₀ ψ (pairA F 0 1 • u) f)
    rw [heisOF_heisOF', sympl_real_fin u (fin_smul_fin u), AddChar.map_zero_eq_one, one_smul, ← dec]
  rw [e, (rep h).comm (sys hσ hS hT hξ h) L (fun x v => Subtype.ext (by
        rw [hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF',
          sympl_real_fin u x.fin, sympl_fin_real u x.fin, add_comm])), hL,
      heis_fin hS h (g, k) (XFF.mk _ (fin_smul_fin u)) f f₁ rfl, XFF.coe_mk, actOF_smulA, heisOF_heisOF',
      sympl_real_fin u (fin_smul_fin _), AddChar.map_zero_eq_one, one_smul, ← real_eq (map_act_inf hg hk u), ← dec]

/- English proof (translation)
Establish `hs` using `sys hσ hS hT hξ h`. Establish `H` using `hs.1`. Use `GlobalTheory.LatticeRep.transl_induction hs.2.2.2.1 (p := fun f => ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f) (fun x e he => ?_) (Filter.Eventually.of_forall fun p => map_zero _) (fun u v hu hv => ?_) (fun c u hu => ?_) f` and prove the remaining obligations. Take `⟨N, hN, hNU⟩` from `h.lev (w • x) filter_upwards [h.near, h.near' x N hN] with p hp hp'`. Take `⟨l, hl, e1⟩` from `hp'`.

Establish `e2 : gamFF σ JS JT ξ₀ ψ (w • x) (N • l) = 1`. Rewrite using `[gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNU l hl, one_mul]`. Establish `e4` using `H.comp x (N • l) e`. Rewrite `e4` using `[he _ (nsmul_mem hl N), e2, one_smul]`. Rewrite using `[h.op, (rep h).fix_of_map_le hs (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he, e1, ← e4]`.

Use `filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]`. Use `filter_upwards [hu] with p h3 using by rw [map_smul, h3]`.
-/
theorem eventually_fix (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
  have hs := sys hσ hS hT hξ h
  have H := hs.1
  refine GlobalTheory.LatticeRep.transl_induction hs.2.2.2.1 (p := fun f => ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f)
    (fun x e he => ?_) (Filter.Eventually.of_forall fun p => map_zero _) (fun u v hu hv => ?_) (fun c u hu => ?_) f
  · obtain ⟨N, hN, hNU⟩ := h.lev (w • x)
    filter_upwards [h.near, h.near' x N hN] with p hp hp'
    obtain ⟨l, hl, e1⟩ := hp'
    have e2 : gamFF σ JS JT ξ₀ ψ (w • x) (N • l) = 1 := by
      rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNU l hl, one_mul]
    have e4 := H.comp x (N • l) e
    rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
    rw [h.op, (rep h).fix_of_map_le hs (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he, e1, ← e4]
  · filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]
  · filter_upwards [hu] with p h3 using by rw [map_smul, h3]

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Use `haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))`. Use `haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))`. Use `continuous_iff_continuousAt.2 fun q => ?_` and prove the remaining obligations. Establish `h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1)` using `(continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)`.

Use `continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_` and prove the remaining obligations. Use `filter_upwards [h1.eventually (eventually_fix hσ hS hT hξ h f)] with p hp`. Use `conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]`.
-/
theorem cont (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) (u : WOF F E nS nT) :
    Continuous fun p => (Om p f : WOF F E nS nT → ℂ) u := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (eventually_fix hσ hS hT hξ h f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

end PositivityTheory.ThKW.LatA

end
