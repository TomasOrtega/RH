import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
noncomputable section
namespace GlobalTheory.Ex.Arch

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis ℤ L`. Establish `htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i))`. Rewrite using `[← hP, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[← e.sum_repr a, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V`. Rewrite using `[← hr, Module.finrank_eq_card_chooseBasisIndex]`.

Set `β` to `basisOfTopLeSpanOfCardEqFinrank _ htop hcard`. Establish `hβ : ∀ i, β i = P (e i)` using `fun i => by simp [β]`. Set `f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ)` to `β.constr ℝ fun i => b (e i)`. Establish `hf : ∀ a, f (P a) = b a` using `fun a => by`. Rewrite using `[← e.sum_repr a]`.

Simplify using `only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]`. Establish `hs : ∀ u v, f u v = f v u`. Set `F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ` to `LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)`. Establish `: F = F.flip` using `β.ext fun i => β.ext fun j => by`. Express the relevant statement in the definitionally equal form `f (β i) (β j) = f (β j) (β i)`.

Rewrite using `[hβ, hβ, hf, hf, hb]`. Conclude with `fun u v => LinearMap.congr_fun₂ this u v`. Use `⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp) (fun _ _ _ => by simp), hs, fun a v => ?_⟩` and prove the remaining obligations. Rewrite using `[hs, map_smul, hs]`. Conclude with `congrArg (fun g => g v) (hf a)`.
-/
theorem exists_symm_bilin_ext {L V : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (P : L →+ V) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ V) (b : L →+ (V →ₗ[ℂ] ℂ)) (hb : ∀ a c, b a (P c) = b c (P a)) :
    ∃ Bs : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ u v, Bs u v = Bs v u) ∧ ∀ a v, Bs (P a) v = b a v := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i)) := by
    rw [← hP, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← e.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  let β := basisOfTopLeSpanOfCardEqFinrank _ htop hcard
  have hβ : ∀ i, β i = P (e i) := fun i => by simp [β]
  let f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ) := β.constr ℝ fun i => b (e i)
  have hf : ∀ a, f (P a) = b a := fun a => by
    rw [← e.sum_repr a]
    simp only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]
  have hs : ∀ u v, f u v = f v u := by
    let F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    have : F = F.flip := β.ext fun i => β.ext fun j => by
      change f (β i) (β j) = f (β j) (β i)
      rw [hβ, hβ, hf, hf, hb]
    exact fun u v => LinearMap.congr_fun₂ this u v
  refine ⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp), hs, fun a v => ?_⟩
  · rw [hs, map_smul, hs]
  · exact congrArg (fun g => g v) (hf a)

/- English proof (translation)
Establish `h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i` using `fun i k => hH.apply k i`. Establish `hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z`. Simplify using `only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply, RCLike.star_def, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`.

Rewrite using `[← hc, Complex.sub_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_sub_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm z w - hermForm Hm w z = 2 * Complex.I * (hermForm Hm z w).im := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  have hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z := by
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [← hc, Complex.sub_conj]
  push_cast; ring

variable {O : Type} [CommRing O] [StarRing O] (B : AnArc O)

/- English proof (translation)
Use `Complex.I_ne_zero` as an intermediate fact. Rewrite using `[lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lin_period (w : ℂ) (a c : B.La) : lin B a (B.Pw w c) =
    -(2 * Real.pi * Complex.I) * (B.T c.y a.y + c.n a.y + w * B.be c.y a.y) +
      Real.pi * (B.H (B.ct a.y) c.l + B.H (B.ct c.y) a.l + B.H c.l a.l) := by
  have := Complex.I_ne_zero
  rw [lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]
  field_simp
  ring

/- English proof (translation)
Establish `h` using `hermForm_sub_swap B.Hm_herm a.l c.l`. Rewrite `h` using `[← B.Ef_eq, ← B.H_def, ← B.H_def]`. Rewrite using `[lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]`. Move the coercions through the operations in `at h ⊢`. Take the linear combination `(-Real.pi : ℂ) * h`.
-/
theorem lin_period_sub (w : ℂ) (a c : B.La) :
    lin B a (B.Pw w c) - lin B c (B.Pw w a) = -(2 * Real.pi * Complex.I) * B.EF a c := by
  have h := hermForm_sub_swap B.Hm_herm a.l c.l
  rw [← B.Ef_eq, ← B.H_def, ← B.H_def] at h
  rw [lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]
  push_cast at h ⊢
  linear_combination (-Real.pi : ℂ) * h

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hp`. Establish `hy : w₀ • a.y + star w₀ • a.y = a.y` using `by rw [← add_smul, h1, one_smul]`. Establish `hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y)`. Use `congrArg (B.T a.y) hy` as an intermediate fact. Rewrite `this` using `[map_add, ← B.T_adj, B.T_symm (w₀ • a.y)]`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y)))`. Use `congrArg a.n hy` as an intermediate fact. Rewrite `this` using `[map_add]`.

Rewrite using `[AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]`. Use linear arithmetic over natural numbers and integers. Establish `hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y` using `by rw [← B.two_mul_q]; push_cast; ring`. Establish `hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y)`. Rewrite using `[zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]`.

Evaluate the numerical expressions. Rewrite using `[hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left, ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem perFactor_of_isPrim {w₀ : O} (hp : IsPrim B w₀) (w : ℂ) (a : B.La) (v : B.V) :
    B.perFactor w a v = (-1) ^ B.EF a (w₀ • a) * Complex.exp (lin B a v + lin B a (B.Pw w a) / 2) := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : w₀ • a.y + star w₀ • a.y = a.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y) := by
    have := congrArg (B.T a.y) hy
    rw [map_add, ← B.T_adj, B.T_symm (w₀ • a.y)] at this
    rw [← this]; ring
  have hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y))) := by
    have := congrArg a.n hy
    rw [map_add] at this
    rw [AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]
    omega
  have hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y := by rw [← B.two_mul_q]; push_cast; ring
  have hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y) := by
    rw [zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  rw [hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left,
    ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

/- English proof (translation)
Introduce `O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE`. Set `b : B.La →+ (B.V →ₗ[ℂ] ℂ)` to `AddMonoidHom.mk' (fun a => { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) map_add' := fun v v' => by`. Simplify using `only [lin, hermForm, map_add, add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.H_add_left]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c v => by`.

Simplify using `only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]`. Use `ring }) fun a a' => LinearMap.ext fun v => by`. Simplify using `only [lin, hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l, Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))` using `fun _ _ => rfl`.

Take `⟨Bs, hs, hB⟩` from `exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by`. Establish `h1` using `hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))`. Rewrite `h1` using `[hE]`. Move the coercions through the operations in `at h1`. Rewrite using `[hb, hb]`.

Take the linear combination `lin_period_sub B w a c + (Real.pi : ℂ) * h1`. Use `⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_, fun a z => ?_, fun a m hm => ?_⟩` and prove the remaining obligations. Establish `hd : Differentiable ℂ fun z => h.symm z` using `h.symm.toContinuousLinearEquiv.differentiable`. Set `Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)`. Establish `hq : Differentiable ℂ fun v : B.V => Bs v v` using `Bc.differentiable.clm_apply differentiable_id`.

Establish `hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z)` using `hq.comp hd`. Establish `hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2)`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(hq'.mul_const _).neg`. Conclude with `hq''.cexp.mul (hS.comp hd)`.

Simplify using `only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]`. Take `⟨v, rfl⟩` from `h.surjective z`. Simplify using `only [← map_add, h.symm_apply_apply]`. Rewrite using `[B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]`. Simplify using `only [map_add, LinearMap.add_apply, hs v (B.Pw w a), hB, hb]`.

Establish `e : ∀ s x y x' y' S : ℂ, x + y = x' + y' → Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S)` using `fun s x y x' y' S e => by`. Use `congrArg Complex.exp e` as an intermediate fact. Rewrite `this` using `[Complex.exp_add, Complex.exp_add]`. Take the linear combination `s * S * this`. Conclude with `e _ _ _ _ _ _ (by ring)`.

Establish `hm' : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hm`. Simplify using `only [← map_smul, h.symm_apply_apply]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]`. Rewrite using `[← mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_sum_appellHumbert : ThetaSt := by
  intro O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE
  let b : B.La →+ (B.V →ₗ[ℂ] ℂ) := AddMonoidHom.mk' (fun a =>
    { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))
      map_add' := fun v v' => by
        simp only [lin, hermForm, map_add, add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply,
          AnArc.H_add_left]
        ring
      map_smul' := fun c v => by
        simp only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply,
          AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }) fun a a' => LinearMap.ext fun v => by
      simp only [lin, hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l,
        Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) := fun _ _ => rfl
  obtain ⟨Bs, hs, hB⟩ := exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by
    have h1 := hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))
    rw [hE] at h1
    push_cast at h1
    rw [hb, hb]
    linear_combination lin_period_sub B w a c + (Real.pi : ℂ) * h1
  refine ⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_,
    fun a z => ?_, fun a m hm => ?_⟩
  · have hd : Differentiable ℂ fun z => h.symm z := h.symm.toContinuousLinearEquiv.differentiable
    let Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)
    have hq : Differentiable ℂ fun v : B.V => Bs v v := Bc.differentiable.clm_apply differentiable_id
    have hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z) := hq.comp hd
    have hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2) := by
      simp only [div_eq_mul_inv]
      exact (hq'.mul_const _).neg
    exact hq''.cexp.mul (hS.comp hd)
  · simp only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]
  · obtain ⟨v, rfl⟩ := h.surjective z
    simp only [← map_add, h.symm_apply_apply]
    rw [B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]
    simp only [map_add, LinearMap.add_apply, hs v (B.Pw w a), hB, hb]
    have e : ∀ s x y x' y' S : ℂ, x + y = x' + y' →
        Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S) := fun s x y x' y' S e => by
      have := congrArg Complex.exp e
      rw [Complex.exp_add, Complex.exp_add] at this
      linear_combination s * S * this
    exact e _ _ _ _ _ _ (by ring)
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    simp only [← map_smul, h.symm_apply_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring

end GlobalTheory.Ex.Arch
end
