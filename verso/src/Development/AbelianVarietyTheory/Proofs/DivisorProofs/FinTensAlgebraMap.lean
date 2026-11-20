import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacSign

open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

def sgnW (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) (u : WO S T) : ℂ := ψ (symplOH S T u (w • u))

/- English proof (translation)
Establish `h` using `SplitScalar.symplOH_skew S T u u`. Establish `h2 : symplO S T u u = 0`. Rewrite using `[← SplitScalar.symplOH_add_self]`. Conclude with `add_eq_zero_iff_eq_neg.2 h`. Rewrite using `[symplOH, h2, mul_zero]`.
-/
theorem symplOH_self (u : WO S T) : symplOH S T u u = 0 := by
  have h := SplitScalar.symplOH_skew S T u u
  have h2 : symplO S T u u = 0 := by
    rw [← SplitScalar.symplOH_add_self]
    exact add_eq_zero_iff_eq_neg.2 h
  rw [symplOH, h2, mul_zero]

/- English proof (translation)
Rewrite using `[symplOH, symplOH, SplitScalar.symplO_smul]`.
-/
theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, SplitScalar.symplO_smul]

/- English proof (translation)
Establish `h1 : symplOH S T u u' = symplOH S T u (w • u') + symplOH S T u (cA D w • u')`. Rewrite using `[← SplitScalar.symplOH_add_right, ← add_smul, hw, one_smul]`. Establish `h2 : symplOH S T u' (w • u) = -symplOH S T u (cA D w • u')`. Rewrite using `[SplitScalar.symplOH_skew, symplOH_smul]`. Rewrite using `[smul_add, SplitScalar.symplOH_add_left, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_right, h1, h2, ← SplitScalar.symplOH_add_self]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem symplOH_quad {w : AE D} (hw : w + cA D w = 1) (u u' : WO S T) :
    symplOH S T u u' + symplOH S T (u + u') (w • (u + u')) =
      symplOH S T u (w • u) + symplOH S T u' (w • u') + symplO S T u (w • u') := by
  have h1 : symplOH S T u u' = symplOH S T u (w • u') + symplOH S T u (cA D w • u') := by
    rw [← SplitScalar.symplOH_add_right, ← add_smul, hw, one_smul]
  have h2 : symplOH S T u' (w • u) = -symplOH S T u (cA D w • u') := by
    rw [SplitScalar.symplOH_skew, symplOH_smul]
  rw [smul_add, SplitScalar.symplOH_add_left, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_right, h1, h2,
    ← SplitScalar.symplOH_add_self]
  ring

/- English proof (translation)
Rewrite using `[sgnW, ← ψ.map_add_eq_mul, symplOH_quad hw, ψ.map_add_eq_mul, ψ.map_add_eq_mul, h, mul_one, sgnW, sgnW]`.
-/
theorem sgnW_add (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u u' : WO S T}
    (h : ψ (symplO S T u (w • u')) = 1) :
    ψ (symplOH S T u u') * sgnW ψ w (u + u') = sgnW ψ w u * sgnW ψ w u' := by
  rw [sgnW, ← ψ.map_add_eq_mul, symplOH_quad hw, ψ.map_add_eq_mul, ψ.map_add_eq_mul, h, mul_one, sgnW, sgnW]

/- English proof (translation)
Rewrite using `[sgnW, symplOH, SplitScalar.symplO_zero_left, mul_zero, ψ.map_zero_eq_one]`.
-/
theorem sgnW_zero (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) : sgnW ψ w (0 : WO S T) = 1 := by
  rw [sgnW, symplOH, SplitScalar.symplO_zero_left, mul_zero, ψ.map_zero_eq_one]

/- English proof (translation)
Introduce `h` and use `by have := ψ.map_add_eq_mul a (-a) rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this exact one_ne_zero this`.
-/
theorem char_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

/- English proof (translation)
Establish `h : symplO S T u (w • u) = 0` using `SplitScalar.symplO_eq_zero S T (a := e) (b := e) (by rw [mul_comm, he.2.1]) hu fun i j => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, mul_left_comm, hu i j]`. Rewrite using `[sgnW, symplOH, h, mul_zero, ψ.map_zero_eq_one]`.
-/
theorem sgnW_half (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) {e : AE D} (he : IsSplitIdem D e) {u : WO S T}
    (hu : IsHalf e u) : sgnW ψ w u = 1 := by
  have h : symplO S T u (w • u) = 0 :=
    SplitScalar.symplO_eq_zero S T (a := e) (b := e) (by rw [mul_comm, he.2.1]) hu fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hu i j]
  rw [sgnW, symplOH, h, mul_zero, ψ.map_zero_eq_one]

/- English proof (translation)
Establish `h1` using `sgnW_add ψ hw h`. Rewrite `h1` using `[symplOH_self, ψ.map_zero_eq_one, one_mul]`. Rewrite using `[two_nsmul, h1]`. Conclude with `char_half h`.
-/
theorem sgnW_two (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u : WO S T}
    (h : ψ (symplO S T u (w • u)) = 1) : sgnW ψ w (2 • u) = 1 := by
  have h1 := sgnW_add ψ hw h
  rw [symplOH_self, ψ.map_zero_eq_one, one_mul] at h1
  rw [two_nsmul, h1]
  exact char_half h

def sgnGroup (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u (w • u')) = 1) (f : WO S T → ℂ) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ heisO ψ S T u f = sgnW ψ w u • f}
  zero_mem' := ⟨zero_mem _, by rw [heisO_zero, sgnW_zero, one_smul]⟩
  add_mem' := by
    rintro u u' ⟨hu, h⟩ ⟨hu', h'⟩
    refine ⟨add_mem hu hu', ?_⟩
    have h1 := heisO_heisO ψ u u' f
    rw [h', heisO_smul, h, smul_smul, mul_comm, ← sgnW_add ψ hw (hΛ u hu u' hu'), mul_smul] at h1
    exact (smul_right_injective _ (char_ne_zero ψ _) h1).symm
  neg_mem' := by
    rintro u ⟨hu, h⟩
    refine ⟨neg_mem hu, ?_⟩
    have h1 := heisO_heisO ψ (-u) u f
    have h2 := sgnW_add ψ hw (hΛ (-u) (neg_mem hu) u hu)
    rw [neg_add_cancel, sgnW_zero, mul_one] at h2
    rw [h, heisO_smul, neg_add_cancel, heisO_zero, h2, mul_comm, mul_smul] at h1
    exact smul_right_injective _ (char_ne_zero ψ _) h1

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * M i j)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem incA_smul_finTens {m n : ℕ} (x : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    incA D x • finTens α M = finTens α (x • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Use `latO_induction (p := fun u => incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce `α hα M hM`. Rewrite using `[incA_smul_finTens]`. Conclude with `finTens_mem_latO hα (smul_mem_latRat c hM)`. Rewrite using `[smul_zero]`.

Conclude with `zero_mem _`. Introduce `x y hx hy`. Rewrite using `[smul_add]`. Conclude with `add_mem hx hy`. Introduce `x hx`.

Rewrite using `[smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem smul_mem_latO {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (c : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact finTens_mem_latO hα (smul_mem_latRat c hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use extensionality with `i j`. Use `SplitScalar.adele_ext ?_ ?_` and prove the remaining obligations. Conclude with `(congrFun (congrFun h1 i) j).trans (infPart_pair _ _).symm`.

Conclude with `congrFun (congrFun h2 i) j`. Introduce and unpack `rfl`. Conclude with `⟨Matrix.ext fun i j => infPart_pair _ _, rfl⟩`.
-/
theorem isFinOf_iff (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (u : WO S T) :
    IsFinOf S T γ u ↔ u = finTens 1 γ := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    refine SplitScalar.adele_ext ?_ ?_
    · exact (congrFun (congrFun h1 i) j).trans (infPart_pair _ _).symm
    · exact congrFun (congrFun h2 i) j
  · rintro rfl
    exact ⟨Matrix.ext fun i j => infPart_pair _ _, rfl⟩

/- English proof (translation)
Establish `hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α` using `continuous_const.prodMk continuous_id`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `e : (fun α : Af D.host.F => finTens α M i j) = fun α => pairA D.host.F 0 α • incA D (M i j)`. Use function extensionality and compare the values at `α`. Express the relevant statement in the definitionally equal form `pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e]`. Conclude with `Continuous.smul (g := fun _ : Af D.host.F => incA D (M i j)) hp continuous_const`.
-/
theorem continuous_finTens {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Continuous fun α : Af D.host.F => finTens α M := by
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun α : Af D.host.F => finTens α M i j) = fun α => pairA D.host.F 0 α • incA D (M i j) := by
    funext α
    change pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  exact Continuous.smul (g := fun _ : Af D.host.F => incA D (M i j)) hp continuous_const

/- English proof (translation)
Rewrite using `[← TensorProduct.smul_tmul]`. Use `congr 1`. Conclude with `Prod.ext (smul_zero _).symm (Algebra.algebraMap_eq_smul_one a)`.
-/
theorem pair_tmul_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : F) (x : E) :
    pairA F 0 (algebraMap F (Af F) a) ⊗ₜ[F] x = pairA F 0 1 ⊗ₜ[F] (a • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  exact Prod.ext (smul_zero _).symm (Algebra.algebraMap_eq_smul_one a)

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a • M i j)`. Conclude with `pair_tmul_smul a (M i j)`.
-/
theorem finTens_algebraMap {m n : ℕ} (a : D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (algebraMap D.host.F (Af D.host.F) a) M = finTens 1 (a • M) := by
  ext i j
  change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a • M i j)
  exact pair_tmul_smul a (M i j)

/- English proof (translation)
Establish `hc` using `continuous_finTens (D := D) M`. Use function extensionality and compare the values at `x`. Use `IntDense.mem_of_isClosed D.host.F (C := {α | heisO ψ S T (finTens α M) f x = (sgnW ψ w (finTens α M : WO S T) • f) x}) (isClosed_eq ?_ ?_) (fun a => ?_) α hα` and prove the remaining obligations. Conclude with `(hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T continuous_const hc))).mul (hf.comp (continuous_const.add hc))`. Establish `hc' : Continuous fun α : Af D.host.F => w • finTens α M` using `continuous_pi fun i => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hc))`.

Conclude with `(hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T hc hc'))).mul continuous_const`. Establish `hm : finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈ latO S T LS LT fun _ => True` using `finTens_mem_latO (fun v => by`. Rewrite using `[AlgHom.commutes]`. Conclude with `v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM`. Rewrite `*` using `[Set.mem_setOf_eq, finTens_algebraMap]`.

Conclude with `congrFun (h _ hm) x`.
-/
theorem sgn_of_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (w : AE D) {f : WO S T → ℂ} (hf : Continuous f)
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (h : ∀ γ, finTens 1 γ ∈ (latO S T LS LT fun _ => True) →
      heisO ψ S T (finTens 1 γ) f = sgnW ψ w (finTens 1 γ : WO S T) • f)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hM : M ∈ latRat S T LS LT) : heisO ψ S T (finTens α M) f = sgnW ψ w (finTens α M : WO S T) • f := by
  have hc := continuous_finTens (D := D) M
  funext x
  refine IntDense.mem_of_isClosed D.host.F
    (C := {α | heisO ψ S T (finTens α M) f x = (sgnW ψ w (finTens α M : WO S T) • f) x})
    (isClosed_eq ?_ ?_) (fun a => ?_) α hα
  · exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T continuous_const hc))).mul
      (hf.comp (continuous_const.add hc))
  · have hc' : Continuous fun α : Af D.host.F => w • finTens α M :=
      continuous_pi fun i => continuous_pi fun j =>
        continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hc))
    exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T hc hc'))).mul continuous_const
  · have hm : finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈ latO S T LS LT fun _ => True :=
      finTens_mem_latO (fun v => by
        rw [AlgHom.commutes]; exact v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM
    rw [Set.mem_setOf_eq, finTens_algebraMap] at *
    exact congrFun (h _ hm) x

/- English proof (translation)
Substitute `hr` using the available equality. Simplify using `only [EF_def]`. Rewrite using `[← map_sum, ← map_neg, hX.kap, ← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[show ∀ x : D.host.E, -(-(2 * x) / 2) = x from fun x => by ring, ← mul_neg]`.

Use `congr 1`. Rewrite using `[hRat, hS, inv_one, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), herm, Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hX.model.1, Matrix.one_apply_eq]`. Express the relevant statement in the definitionally equal form `γ d a * -(T.gram c d) * star (γ' c a) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_EF {r : ℕ} (hr : T.rank = r) (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∑ k, EF X (colsR hr γ k) (colsR hr γ' k) = -Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T γ γ') := by
  subst hr
  simp only [EF_def]
  rw [← map_sum, ← map_neg, hX.kap, ← Finset.mul_sum]
  congr 1
  rw [show ∀ x : D.host.E, -(-(2 * x) / 2) = x from fun x => by ring, ← mul_neg]
  congr 1
  rw [hRat, hS, inv_one, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), herm, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hX.model.1, Matrix.one_apply_eq]
  change γ d a * -(T.gram c d) * star (γ' c a) = _
  ring

/- English proof (translation)
Establish `h1` using `sum_EF hr X hS hX γ (w • γ)`. Establish `h2 : epsW X w (colsR hr γ) = cexp (Real.pi * I * ((∑ k, EF X (colsR hr γ k) (colsR hr (w • γ) k) : ℚ) : ℂ))` using `rfl`. Establish `h3 : symplOH S T (finTens 1 γ) (finTens 1 (w • γ)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T γ (w • γ))))`. Rewrite using `[symplOH, symplO_finTens, one_mul, one_mul, RingHom.map_mul]`. Conclude with `Prod.ext (mul_zero _) rfl`.

Rewrite using `[h2, h1, sgnW, incA_smul_finTens, h3, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ, ← Complex.exp_add, show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul, Algebra.trace_trace, smul_eq_mul]`. Use `Eq.trans (congrArg cexp ?_) Complex.exp_zero` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgnW_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {r : ℕ} (hr : T.rank = r)
    (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X) (w : D.host.E)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    sgnW ψ (incA D w) (finTens 1 γ : WO S T) * epsW X w (colsR hr γ) = 1 := by
  have h1 := sum_EF hr X hS hX γ (w • γ)
  have h2 : epsW X w (colsR hr γ) = cexp (Real.pi * I * ((∑ k, EF X (colsR hr γ k) (colsR hr (w • γ) k) : ℚ) : ℂ)) := rfl
  have h3 : symplOH S T (finTens 1 γ) (finTens 1 (w • γ)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T γ (w • γ)))) := by
    rw [symplOH, symplO_finTens, one_mul, one_mul, RingHom.map_mul]
    exact Prod.ext (mul_zero _) rfl
  rw [h2, h1, sgnW, incA_smul_finTens, h3, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ, ← Complex.exp_add,
    show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
    Algebra.trace_trace, smul_eq_mul]
  refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
  push_cast
  ring

/- English proof (translation)
Introduce `D ψ θ V W r g hr X bas idx hψ _ hV _ hX _ H hH ΛV ΛW hΛV hΛW f hf`. Establish `hw0 : (H.w0 : D.host.E) + star (H.w0 : D.host.E) = 1`. Establish `h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD`. Rewrite using `[← hH]`. Conclude with `congrArg Subtype.val H.two_weight_eq_one_add_root`.

Establish `h2` using `congrArg star h1`. Rewrite `h2` using `[star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD, D.host.conj_sqrtMinusD]`. Take the linear combination `(1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2`. Establish `hw : incA D (H.w0 : D.host.E) + cA D (incA D (H.w0 : D.host.E)) = 1`. Rewrite using `[DualPairCheck.cA_incA, ← RingHom.map_add, hw0, RingHom.map_one]`.

Establish `hΛ : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), ∀ u' ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), ψ (symplO V W u (incA D (H.w0 : D.host.E) • u')) = 1` using `fun u hu u' hu' => char_sympl_eq_one hψ hΛV hΛW hu (smul_mem_latO H.w0 hu')`. Establish `he : ∀ γ, (finTens 1 γ : WO V W) ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) → epsW X (H.w0 : D.host.E) (colsR hr γ) = sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W)`. Introduce `γ hγ`. Establish `h1` using `sgnW_rat hψ hr X hV hX (H.w0 : D.host.E) γ`. Establish `h2 : sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) * sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) = 1` using `char_half (hΛ _ hγ _ hγ)`.

Conclude with `mul_left_cancel₀ (char_ne_zero ψ _) (h1.trans h2.symm)`. Prove the components needed by the constructor for the conclusion. Introduce `hv γ u hu hm`. Rewrite `hu` using `[isFinOf_iff]`. Substitute `hu` using the available equality.

Rewrite using `[he γ hm]`. Conclude with `(le_of_two_of_half (sgnGroup ψ hw _ hΛ f) (fun u hu => ⟨nsmul_mem hu 2, by rw [hv.1 u hu, sgnW_two ψ hw (hΛ u hu u hu), one_smul]⟩) (fun e he u hu hh => ⟨hu, by rw [hv.2 e he u hu hh, sgnW_half ψ _ he hh, one_smul]⟩) hm).2`. Introduce `h`. Establish `hall : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u ∈ sgnGroup ψ hw _ hΛ f` using `fun u hu => latO_induction (p := fun u => u ∈ sgnGroup ψ hw _ hΛ f) (fun α hα M hM => ⟨finTens_mem_latO hα hM, sgn_of_rat hψ.1.1 _ hf.cont (fun γ hγ => by rw [h γ _ ((isFinOf_iff _ _).2 rfl) hγ, he γ hγ]) hα hM⟩) (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hu`. Use `⟨fun u hu => ?_, fun e hs u hu hh => ?_⟩` and prove the remaining obligations.

Rewrite using `[(hall _ (nsmul_mem hu 2)).2, sgnW_two ψ hw (hΛ u hu u hu), one_smul]`. Rewrite using `[(hall _ hu).2, sgnW_half ψ _ hs hh, one_smul]`.
-/
theorem isLatVac_iff_epsW : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f ↔ ∀ γ u, IsFinOf V W γ u → u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) → heisO ψ V W u f = epsW X (H.w0 : D.host.E) (colsR hr γ) • f) := by
  intro D ψ θ V W r g hr X bas idx hψ _ hV _ hX _ H hH ΛV ΛW hΛV hΛW f hf
  have hw0 : (H.w0 : D.host.E) + star (H.w0 : D.host.E) = 1 := by
    have h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD := by
      rw [← hH]; exact congrArg Subtype.val H.two_weight_eq_one_add_root
    have h2 := congrArg star h1
    rw [star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD,
      D.host.conj_sqrtMinusD] at h2
    linear_combination (1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2
  have hw : incA D (H.w0 : D.host.E) + cA D (incA D (H.w0 : D.host.E)) = 1 := by
    rw [DualPairCheck.cA_incA, ← RingHom.map_add, hw0, RingHom.map_one]
  have hΛ : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ψ (symplO V W u (incA D (H.w0 : D.host.E) • u')) = 1 :=
    fun u hu u' hu' => char_sympl_eq_one hψ hΛV hΛW hu (smul_mem_latO H.w0 hu')
  have he : ∀ γ, (finTens 1 γ : WO V W) ∈
      (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) →
      epsW X (H.w0 : D.host.E) (colsR hr γ) = sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) := by
    intro γ hγ
    have h1 := sgnW_rat hψ hr X hV hX (H.w0 : D.host.E) γ
    have h2 : sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) *
        sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) = 1 := char_half (hΛ _ hγ _ hγ)
    exact mul_left_cancel₀ (char_ne_zero ψ _) (h1.trans h2.symm)
  constructor
  · intro hv γ u hu hm
    rw [isFinOf_iff] at hu
    subst hu
    rw [he γ hm]
    exact (le_of_two_of_half (sgnGroup ψ hw _ hΛ f)
      (fun u hu => ⟨nsmul_mem hu 2, by rw [hv.1 u hu, sgnW_two ψ hw (hΛ u hu u hu), one_smul]⟩)
      (fun e he u hu hh => ⟨hu, by rw [hv.2 e he u hu hh, sgnW_half ψ _ he hh, one_smul]⟩) hm).2
  · intro h
    have hall : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        u ∈ sgnGroup ψ hw _ hΛ f := fun u hu =>
      latO_induction (p := fun u => u ∈ sgnGroup ψ hw _ hΛ f)
        (fun α hα M hM => ⟨finTens_mem_latO hα hM, sgn_of_rat hψ.1.1 _ hf.cont
          (fun γ hγ => by rw [h γ _ ((isFinOf_iff _ _).2 rfl) hγ, he γ hγ]) hα hM⟩)
        (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hu
    refine ⟨fun u hu => ?_, fun e hs u hu hh => ?_⟩
    · rw [(hall _ (nsmul_mem hu 2)).2, sgnW_two ψ hw (hΛ u hu u hu), one_smul]
    · rw [(hall _ hu).2, sgnW_half ψ _ hs hh, one_smul]

end GlobalTheory.VacSign

end
