import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace CompanionTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨hd, Iff.rfl⟩`.
-/
theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

/- English proof (translation)
The claim follows from `GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s)) (isIrreducible_twist hi _)`.
-/
theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in
set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `y hy N hd hirr`. Take `⟨ρ, z, hρ, hu, rfl⟩` from `h2 y hy`. Take `⟨s, hs0, hs⟩` from `h1 ρ hρ hu`. Establish `hpos : 0 < ρ.1` using `hρ.1`. Establish `hs2 : s = 1 / 2`.

Assume the negation of the conclusion as `hne`. Establish `hd0 : ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 = ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1` using `rfl`. Use `hs _ hd0 (h3 _ _ _ hd0 (hρ.nu _) (hρ.nu _) ?_ ?_)` and prove the remaining obligations. Introduce `e`. Rewrite `e` using `[IrrGL.nu_nu, show -(s : ℂ) + 1 = ((-s + 1 : ℝ) : ℂ) by push_cast; ring]`.

Use `(IrrGL.nu_ofReal_inj hpos).1 e` as an intermediate fact. Conclude with `hne (by linarith)`. Introduce `e`. Rewrite `e` using `[IrrGL.nu_nu, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring]`. Use `(IrrGL.nu_ofReal_inj hpos).1 e` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set t : ℂ := -((z : ℂ) + 1 / 2) with ht`. Establish `key : (fun a => (![ρ.nu (z : ℂ), (ρ.nu (z : ℂ)).nu 1] a).nu t) = ![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)]`. Use function extensionality and compare the values at `a`. Use `fin_cases a`.

Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero]`. Rewrite using `[IrrGL.nu_nu, hs2, ht]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]`. Rewrite using `[IrrGL.nu_nu, IrrGL.nu_nu, hs2, ht]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨hd', hiff⟩` from `irr_congr key hd`. Conclude with `hs N hd' (hiff.1 (irr_tw _ hd t hirr))`.
-/
theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  intro y hy N hd hirr
  obtain ⟨ρ, z, hρ, hu, rfl⟩ := h2 y hy
  obtain ⟨s, hs0, hs⟩ := h1 ρ hρ hu
  have hpos : 0 < ρ.1 := hρ.1
  have hs2 : s = 1 / 2 := by
    by_contra hne
    have hd0 : ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 = ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 := rfl
    refine hs _ hd0 (h3 _ _ _ hd0 (hρ.nu _) (hρ.nu _) ?_ ?_)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) + 1 = ((-s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      exact hne (by linarith)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
        show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      linarith
  set t : ℂ := -((z : ℂ) + 1 / 2) with ht
  have key : (fun a => (![ρ.nu (z : ℂ), (ρ.nu (z : ℂ)).nu 1] a).nu t) = ![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [IrrGL.nu_nu, IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
  obtain ⟨hd', hiff⟩ := irr_congr key hd
  exact hs N hd' (hiff.1 (irr_tw _ hd t hirr))

/- English proof (translation)
Introduce `k _ _ _ _ d hd σ hσ hirr`. Use `set y : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr with hy`. Establish `hyc : y.IsCusp` using `IrrGL.isCusp_of.2 ⟨hd, hσ⟩`. Set `x : Fin 2 → IrrGL k` to `fun a => y.nu ((a : ℕ) : ℂ)`. Establish `hx1 : ∀ a, (x a).1 = d` using `fun _ => rfl`.

Establish `hdx : ∑ a, (x a).1 = 2 * d`. Simplify using `only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Set `φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep` to `fun a => (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)`. Establish `E1` using `multiProdEquiv (consecBlocks 2 d) φ`. Establish `hdd : ∑ _a : Fin 2, d = 2 * d` using `by simp`.

Establish `hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd`. Use extensionality with `⟨a, i⟩`. Rewrite using `[consecBlocks_val, stdBlocks_val]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : (prodIrr x hdx).IsIrreducible`. Establish `h4` using `GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr`. Rewrite `h4` using `[hE]`. Conclude with `h4`. Establish `e : x = ![y, y.nu 1]`.

Use function extensionality and compare the values at `a`. Use `fin_cases a`. Simplify using `[x]`. Simplify using `[x]`. Take `⟨hd', hiff⟩` from `RedC.irr_congr e hdx`.

Conclude with `h k y hyc (2 * d) hd' (hiff.1 h3)`.
-/
theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : CompanionTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := by
  intro k _ _ _ _ d hd σ hσ hirr
  set y : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr with hy
  have hyc : y.IsCusp := IrrGL.isCusp_of.2 ⟨hd, hσ⟩
  let x : Fin 2 → IrrGL k := fun a => y.nu ((a : ℕ) : ℂ)
  have hx1 : ∀ a, (x a).1 = d := fun _ => rfl
  have hdx : ∑ a, (x a).1 = 2 * d := by
    simp only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)
  have E1 := multiProdEquiv (consecBlocks 2 d) φ
  have hdd : ∑ _a : Fin 2, d = 2 * d := by simp
  have hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd := by
    ext ⟨a, i⟩
    rw [consecBlocks_val, stdBlocks_val]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h3 : (prodIrr x hdx).IsIrreducible := by
    have h4 := GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr
    rw [hE] at h4
    exact h4
  have e : x = ![y, y.nu 1] := by
    funext a
    fin_cases a
    · simp [x]
    · simp [x]
  obtain ⟨hd', hiff⟩ := RedC.irr_congr e hdx
  exact h k y hyc (2 * d) hd' (hiff.1 h3)

end CompanionTheory.RgGu.NR
