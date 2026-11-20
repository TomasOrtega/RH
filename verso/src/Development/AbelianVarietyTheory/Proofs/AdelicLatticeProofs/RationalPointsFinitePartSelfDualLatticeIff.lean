import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.RatSelfDual

variable {D : D7}

def symplB (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => symplO S T x y) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 x))
    (fun x x' => AddMonoidHom.ext fun y => (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 x x' y)

/- English proof (translation)
Establish `h1 : symplO S T x (N • y) = N • symplO S T x y` using `(symplB S T x).map_nsmul N y`. Establish `h2 : symplO S T (N • x) y = N • symplO S T x y` using `((symplB S T).flip y).map_nsmul N x`. Rewrite using `[h1, h2]`.
-/
theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T x (N • y) = symplO S T (N • x) y := by
  have h1 : symplO S T x (N • y) = N • symplO S T x y := (symplB S T x).map_nsmul N y
  have h2 : symplO S T (N • x) y = N • symplO S T x y := ((symplB S T).flip y).map_nsmul N x
  rw [h1, h2]

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]`.
-/
theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]

/- English proof (translation)
Rewrite using `[symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_real {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    ψ (symplO S T x y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  rw [symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Take `⟨θ, hθ⟩` from `hψ.2.1`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨a, ha⟩` from `(GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y`. Establish `h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1` using `by rw [ha]; exact hψ.1.2.2.1 a`. Establish `hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0` using `hσ.real_iota T S _`.

Establish `hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0` using `hσ.real_iota T S _`. Establish `e1` using `psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)`. Establish `e2` using `psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)`. Rewrite `e1` using `[hσ.pi_iota, piW_ratW hθ]`. Rewrite `e2` using `[piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero]`.

Establish `d1 : symplO S T (ratW T S x) (ratW T S y) = symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y)` using `(congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)`. Establish `d2 : symplO S T (finRat S T x) (ratW T S y) = symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y)` using `(congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)`. Rewrite `h1` using `[d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm]`. Conclude with `h1`.
-/
theorem psi_fin_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, ha⟩ := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y
  have h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1 := by rw [ha]; exact hψ.1.2.2.1 a
  have hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have e1 := psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)
  have e2 := psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)
  rw [hσ.pi_iota, piW_ratW hθ] at e1
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at e2
  have d1 : symplO S T (ratW T S x) (ratW T S y) =
      symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)
  have d2 : symplO S T (finRat S T x) (ratW T S y) =
      symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm] at h1
  exact h1

/- English proof (translation)
Establish `h` using `psi_fin_mul hψ S T x y`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Rewrite `h` using `[h1, one_mul, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Establish `h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ)`. Apply `mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)` to reduce the goal to its premises. Rewrite using `[hn]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h2` after adjusting the coercions. Introduce and unpack `⟨k, hk⟩`. Establish `h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1`. Rewrite using `[hk, Complex.exp_eq_one_iff]`.

Conclude with `⟨-k, by push_cast; ring⟩`. Rewrite `h` using `[h2, mul_one]`. Then use the resulting hypothesis.
-/
theorem psi_fin_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) = 1 ↔ ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  have h := psi_fin_mul hψ S T x y
  constructor
  · intro h1
    rw [h1, one_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [hn]; push_cast; ring
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
      rw [hk, Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; ring⟩
    rwa [h2, mul_one] at h

/- English proof (translation)
Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Use function extensionality and compare the values at `i j`. Use `hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_` and prove the remaining obligations. Establish `: infPart D (z i j) = 0` using `congrFun (congrFun hi i) j`. Rewrite using `[this, RingHom.map_zero]`.
-/
theorem eq_zero_of_parts {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {z : WO S T}
    (hf : z.map (finPart D) = 0) (hi : z.map (infPart D) = 0) : z = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_
  have : infPart D (z i j) = 0 := congrFun (congrFun hi i) j
  rw [this, RingHom.map_zero]

/- English proof (translation)
Use `⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Establish `: infPart D (u i j) = 0` using `congrFun (congrFun hu i) j`. Use `show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0`. Rewrite using `[RingHom.map_mul, this, mul_zero]`.

Use function extensionality and compare the values at `i j show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j`. Establish `h1 : (N : AE D) = incA D (N : D.host.E)` using `(map_natCast (incA D) N).symm`. Establish `h2 : (N : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Rewrite using `[nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]`.
-/
theorem exists_div {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ γ : WO S T, γ.map (infPart D) = 0 ∧ N • γ = u := by
  refine ⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩
  · funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0
    rw [RingHom.map_mul, this, mul_zero]
  · funext i j
    show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j
    have h1 : (N : AE D) = incA D (N : D.host.E) := (map_natCast (incA D) N).symm
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]

/- English proof (translation)
Introduce `D S T ψ Λ hψ hinf hdual happ hden x`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Conclude with `(psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)`. Introduce `h`.

Use `(hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_` and prove the remaining obligations. Take `⟨θ, hθ⟩` from `hψ.2.1`. Take `⟨N, hN, hNx⟩` from `hden x`. Take `⟨γ, hγ, hNγ⟩` from `exists_div (hinf u' hu') hN`. Take `⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩` from `happ γ hγ`.

Establish `hz0 : γ - finRat S T y₀ - u = 0`. Use `eq_zero_of_parts hθ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Establish `e0 : finPart D (γ i j - ρ i j - u i j) = 0` using `congrFun (congrFun hz i) j`. Establish `e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j)` using `by rw [← hy₀]; rfl`.

Use `show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0`. Rewrite `e0`, the goal using `[RingHom.map_sub, RingHom.map_sub]`. Rewrite using `[e1, e0]`. Use function extensionality and compare the values at `i j`. Establish `e0 : infPart D (γ i j) = 0` using `congrFun (congrFun hγ i) j`.

Establish `e1 : infPart D (finRat S T y₀ i j) = 0` using `congrFun (congrFun (finRat_inf S T y₀) i) j`. Establish `e2 : infPart D (u i j) = 0` using `congrFun (congrFun (hinf u hu) i) j`. Use `show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0`. Rewrite using `[RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]`. Establish `hγe : γ = finRat S T y₀ + u`.

Rewrite `hz0` using `[sub_sub]`. Conclude with `sub_eq_zero.1 hz0`. Establish `hu'e : u' = finRat S T (N • y₀) + N • u`. Rewrite using `[← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]`. Establish `hmem : finRat S T (N • y₀) ∈ Λ`.

Establish `: finRat S T (N • y₀) = u' - N • u` using `(sub_eq_of_eq_add hu'e).symm`. Rewrite using `[this]`. Conclude with `Λ.sub_mem hu' (Λ.nsmul_mem hu N)`. Rewrite using `[hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul, symplO_nsmul]`. Conclude with `(hdual _ (hinf _ hNx)).1 hNx u hu`.
-/
theorem finRat_mem_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  intro D S T ψ Λ hψ hinf hdual happ hden x
  constructor
  · intro hx y hy
    exact (psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)
  · intro h
    refine (hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_
    obtain ⟨θ, hθ⟩ := hψ.2.1
    obtain ⟨N, hN, hNx⟩ := hden x
    obtain ⟨γ, hγ, hNγ⟩ := exists_div (hinf u' hu') hN
    obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
    have hz0 : γ - finRat S T y₀ - u = 0 := by
      refine eq_zero_of_parts hθ ?_ ?_
      · funext i j
        have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
        have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
        show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub] at e0 ⊢
        rw [e1, e0]
      · funext i j
        have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
        have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
        have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
        show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]
    have hγe : γ = finRat S T y₀ + u := by
      rw [sub_sub] at hz0
      exact sub_eq_zero.1 hz0
    have hu'e : u' = finRat S T (N • y₀) + N • u := by
      rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]
    have hmem : finRat S T (N • y₀) ∈ Λ := by
      have : finRat S T (N • y₀) = u' - N • u := (sub_eq_of_eq_add hu'e).symm
      rw [this]
      exact Λ.sub_mem hu' (Λ.nsmul_mem hu N)
    rw [hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul,
      symplO_nsmul]
    exact (hdual _ (hinf _ hNx)).1 hNx u hu

end GlobalTheory.RatSelfDual

end
