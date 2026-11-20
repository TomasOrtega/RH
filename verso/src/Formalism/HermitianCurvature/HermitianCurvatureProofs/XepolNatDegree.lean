import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZKapLeft
import Mathlib.LinearAlgebra.Lagrange

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

section poly

/- English proof (translation)
Set `v : Fin (k + 1) → ℂ` to `fun j => ((j : ℕ) : ℂ)`. Establish `hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1)))`. Introduce `a _ b _ hab`. Establish `h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ)` using `hab`. Conclude with `Fin.ext (by exact_mod_cast h')`.

Use `⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card`. Rewrite using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)`.

Use `conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]`. Rewrite using `[Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `j _`. Rewrite using `[Polynomial.coeff_C_mul, mul_comm]`.
-/
theorem lag_weights (k : ℕ) : ∃ lam : Fin (k + 1) → ℂ, ∀ p : ℂ[X], p.natDegree ≤ k →
    ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1) := by
  classical
  let v : Fin (k + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := by
    intro a _ b _ hab
    have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast h')
  refine ⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩
  intro p hp
  have hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, mul_comm]

def xpol (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Finset.Icc 1 (P.k - 1), (X + C ((M.rho P ρ i : ℝ) : ℂ))

def xepol (P : M.Par) (l : ℕ) (ρ : M.Ty P) : ℂ[X] :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (X + C ((M.rho P ρ i : ℝ) : ℂ))

/- English proof (translation)
Simplify using `[xpol, M.xC, Polynomial.eval_prod]`.
-/
theorem xpol_eval (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xpol P ρ).eval Y = M.xC P ρ Y := by
  simp [xpol, M.xC, Polynomial.eval_prod]

/- English proof (translation)
Simplify using `[xepol, M.xEx, Polynomial.eval_prod]`.
-/
theorem xepol_eval (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℂ) : (xepol P l ρ).eval Y = M.xEx P {l} ρ Y := by
  simp [xepol, M.xEx, Polynomial.eval_prod]

/- English proof (translation)
The claim follows from `Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)`.
-/
theorem xpol_monic (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

/- English proof (translation)
Unfold `xpol`. Rewrite using `[Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]`. Simplify using `[Polynomial.natDegree_X_add_C]`.
-/
theorem xpol_natDegree (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree = P.k - 1 := by
  unfold xpol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [Polynomial.natDegree_X_add_C]

/- English proof (translation)
Rewrite using `[← xpol_natDegree P ρ]`. Conclude with `(xpol_monic P ρ).coeff_natDegree`.
-/
theorem xpol_coeff (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).coeff (P.k - 1) = 1 := by
  rw [← xpol_natDegree P ρ]
  exact (xpol_monic P ρ).coeff_natDegree

/- English proof (translation)
Unfold `xepol`. Rewrite using `[Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]`. Simplify using `only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]`. Rewrite using `[Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem xepol_natDegree (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree = P.k - 2 := by
  unfold xepol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]
  omega

end poly

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def fl (P : M.Par) (l : ℕ) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ0 => if M.Up P l ρ0 ρ then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[h1 i, h2 i]`.
-/
theorem up_func {l : ℕ} {ρ0 ρ ρ' : M.Ty P} (h1 : M.Up P l ρ0 ρ) (h2 : M.Up P l ρ0 ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h1 i, h2 i]

/- English proof (translation)
Establish `h : g = ∑ ρ0, g ρ0 • dl ρ0`. Use function extensionality and compare the values at `ρ`. Simplify using `[dl, Finset.sum_apply]`. Use `conv_lhs => rw [h]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul]`.
-/
theorem kap_decomp (d : Q.NFData P A) (g : M.Ty P → ℂ) : d.κ g = ∑ ρ0, g ρ0 • d.κ (dl ρ0) := by
  have h : g = ∑ ρ0, g ρ0 • dl ρ0 := by
    funext ρ
    simp [dl, Finset.sum_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  simp only [map_smul]

/- English proof (translation)
Establish `h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1`. Use function extensionality and compare the values at `x`. Simplify using `[dl, Finset.sum_apply]`. Rewrite using `[← map_sum, h, map_one]`.
-/
theorem sum_dl (d : Q.NFData P A) : ∑ ρ, d.κ (dl ρ) = 1 := by
  have h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1 := by
    funext x
    simp [dl, Finset.sum_apply]
  rw [← map_sum, h, map_one]

/- English proof (translation)
Establish `h : dl ρ * g = g ρ • dl ρ`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = ρ`. Substitute `hx` using the available equality. Simplify using `[dl]`.

Simplify using `[dl, hx]`. Rewrite using `[← map_mul, h, map_smul]`.
-/
theorem dl_mul_kap (d : Q.NFData P A) (ρ : M.Ty P) (g : M.Ty P → ℂ) :
    d.κ (dl ρ) * d.κ g = g ρ • d.κ (dl ρ) := by
  have h : dl ρ * g = g ρ • dl ρ := by
    funext x
    by_cases hx : x = ρ
    · subst hx
      simp [dl]
    · simp [dl, hx]
  rw [← map_mul, h, map_smul]

/- English proof (translation)
Establish `hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}` using `Or.inl (Or.inr hg)`. Conclude with `(hR.2.1 f g hm).eq`.
-/
theorem kap_comm (d : Q.NFData P A) (hR : d.Rel) (f : M.Ty P → ℂ) {g : A}
    (hg : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : d.κ f * g = g * d.κ f := by
  have hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} := Or.inl (Or.inr hg)
  exact (hR.2.1 f g hm).eq

/- English proof (translation)
The claim follows from `d.L.fns_comm x (Or.inr hx) y (Or.inr hy)`.
-/
theorem fns_comm' (d : Q.NFData P A) {x y : A}
    (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

/- English proof (translation)
Repeatedly rewrite using `[smul_smul]`. Rewrite using `[← Finset.sum_smul, hlam p hp]`.
-/
theorem comb {k : ℕ} {lam : Fin (k + 1) → ℂ}
    (hlam : ∀ p : ℂ[X], p.natDegree ≤ k → ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1))
    (p : ℂ[X]) (hp : p.natDegree ≤ k) (O : A) :
    ∑ j : Fin (k + 1), lam j • (p.eval ((j : ℕ) : ℂ) • O) = p.coeff (k - 1) • O := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hlam p hp]

/- English proof (translation)
Establish `hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ)` using `kap_comm d hR _ (by simp)`. Establish `hGGi : d.L.GG * d.L.GGi = 1` using `d.L.GG_GGi`. Establish `hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG` using `fns_comm' d (by simp) (by simp)`. Establish `hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ)`. Rewrite using `[Q.NFData.x, dl_mul_kap]`.

Simplify using `only [xpol_eval]`. Establish `key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [mul_assoc]`.

Use `_ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]`. Use `_ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]`. Use `show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _`. Rewrite using `[mul_add]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, hG]`. Simplify using `only [mul_assoc]`. Use `_ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by`. Rewrite using `[hx, mul_smul_comm, smul_mul_assoc]`.

Use `_ = _ := by`. Rewrite using `[R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]`. Use `module`. Rewrite using `[Q.NFData.weightedSumBis, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Establish `hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ)`. Apply `hR.2.2.2.1 l` to reduce the goal to its premises. Introduce `ρ0 ρ' hup`. Distinguish the cases in `h : ρ' = ρ`.

Substitute `h` using the available equality. Simplify using `[dl, fl, hup]`. Establish `hn : ¬ M.Up P l ρ0 ρ` using `fun h2 => h (up_func hup h2)`. Simplify using `[dl, fl, h, hn]`. Rewrite using `[← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun ρ0 _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`. Use `congr 1`. Simplify using `[Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]`.
-/
theorem e10 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 1 0 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nab)) +
      ((xpol P ρ) * (X + C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζb)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0, (C (fl P l ρ ρ0) * xepol P l ρ0).eval Y • (d.SS l * d.κ (dl ρ0)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζb * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.l0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.weightedSumBis, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ) := by
      apply hR.2.2.2.1 l
      intro ρ0 ρ' hup
      by_cases h : ρ' = ρ
      · subst h
        simp [dl, fl, hup]
      · have hn : ¬ M.Up P l ρ0 ρ := fun h2 => h (up_func hup h2)
        simp [dl, fl, h, hn]
    rw [← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ0 _ => ?_)
    rw [mul_smul_comm]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]

/- English proof (translation)
Establish `hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ)` using `kap_comm d hR _ (by simp)`. Establish `hGGi : d.L.GG * d.L.GGi = 1` using `d.L.GG_GGi`. Establish `hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG` using `fns_comm' d (by simp) (by simp)`. Establish `hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ)`. Rewrite using `[Q.NFData.x, dl_mul_kap]`.

Simplify using `only [xpol_eval]`. Establish `key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [mul_assoc]`.

Use `_ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]`. Use `_ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]`. Use `show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _`. Rewrite using `[mul_add]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, hG]`. Simplify using `only [mul_assoc]`. Use `_ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by`. Rewrite using `[hx, mul_smul_comm, smul_mul_assoc]`.

Use `_ = _ := by`. Rewrite using `[R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Use `module`. Rewrite using `[Q.NFData.S12, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, dl_mul_kap]`. Simplify using `only [xepol_eval, smul_mul_assoc]`.
-/
theorem e01 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 0 1 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nabs)) +
      ((xpol P ρ) * (X - C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζ)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (xepol P l ρ).eval Y • (d.κ (dl ρ) * star (d.SS l)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζ * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.m0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.S12, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, dl_mul_kap]
    simp only [xepol_eval, smul_mul_assoc]

end ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
