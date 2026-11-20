import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.LevZZero

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

/- English proof (translation)
Establish `hx : pm k (wOpen d hd) * u * a = leviEmb k (stdBlocks d hd) l * (pm k (wOpen d hd) * (a⁻¹ * u * a))`. Rewrite using `[← hl]`. Use `group`. Establish `hf` using `f.1.2 ⟨leviEmb k (stdBlocks d hd) l, leviEmb_mem_parab k _ l⟩ (pm k (wOpen d hd) * (a⁻¹ * u * a))`. Express the relevant statement in the definitionally equal form `f.1.1 (pm k (wOpen d hd) * u * a) = _`.

Rewrite using `[hx]`. Use `hf.trans ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, leviProj_leviEmb]`. Both sides reduce to the same expression.
-/
theorem translate_apply (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (f : IndSp (stdBlocks d hd) ρ) (u : GL (Fin N) k) :
    (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * u) =
      (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l (f.1.1 (pm k (wOpen d hd) * (a⁻¹ * u * a))) := by
  have hx : pm k (wOpen d hd) * u * a =
      leviEmb k (stdBlocks d hd) l * (pm k (wOpen d hd) * (a⁻¹ * u * a)) := by
    rw [← hl]
    group
  have hf := f.1.2 ⟨leviEmb k (stdBlocks d hd) l, leviEmb_mem_parab k _ l⟩ (pm k (wOpen d hd) * (a⁻¹ * u * a))
  change f.1.1 (pm k (wOpen d hd) * u * a) = _
  rw [hx]
  refine hf.trans ?_
  rw [MonoidHom.comp_apply, leviProj_leviEmb]
  rfl

/- English proof (translation)
Establish `hf' : ∀ g : GL (Fin N) k, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)` using `hf`. Use `show ∀ g : GL (Fin N) k, (parInd (stdBlocks d hd) ρ a f).1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)`. Introduce `g hg`. Take `⟨p, hp, n, hn, hpn⟩` from `hf' (g * a) hg`. Use `⟨p * (leviEmb k (stdBlocks d hd) l)⁻¹, (parab k _).mul_mem hp ((parab k _).inv_mem (leviEmb_mem_parab k _ l)), a * n * a⁻¹, haB n hn, ?_⟩` and prove the remaining obligations.

Establish `hg' : g = p * pm k (wOpen d hd) * n * a⁻¹`. Rewrite using `[← hpn]`. Use `group`. Rewrite using `[hg', ← hl]`. Use `group`.
-/
theorem translate_mem_openFns (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    {f : IndSp (stdBlocks d hd) ρ} (hf : f ∈ openFns d hd ρ) :
    parInd (stdBlocks d hd) ρ a f ∈ openFns d hd ρ := by
  have hf' : ∀ g : GL (Fin N) k, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd) := hf
  show ∀ g : GL (Fin N) k, (parInd (stdBlocks d hd) ρ a f).1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
  intro g hg
  obtain ⟨p, hp, n, hn, hpn⟩ := hf' (g * a) hg
  refine ⟨p * (leviEmb k (stdBlocks d hd) l)⁻¹,
    (parab k _).mul_mem hp ((parab k _).inv_mem (leviEmb_mem_parab k _ l)), a * n * a⁻¹, haB n hn, ?_⟩
  have hg' : g = p * pm k (wOpen d hd) * n * a⁻¹ := by
    rw [← hpn]
    group
  rw [hg', ← hl]
  group

end General

section Two

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two, dd]`.
-/
theorem modExp_two_one (r m : ℕ) : modExp (fun a => Fin (dd r m a)) 1 = -(r : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two, dd]

/- English proof (translation)
Simplify using `[nabs, map_pow]`.
-/
theorem nabs_pow (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by
  simp [nabs, map_pow]

/- English proof (translation)
Apply the tactic sequence `have h0 : levZ k r m z 0 = 1 := by simp [levZ] <;> rfl`. Establish `h1 : levZ k r m z 1 = GeneralLinearGroup.scalar (Fin (dd r m 1)) z` using `by simp [levZ]`. Establish `hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (dd r m 1)) z) = z ^ m`. Rewrite using `[GeneralLinearGroup.det_scalar]`. Simplify using `[dd]`.

Establish `key : (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) = ((nabs k (GeneralLinearGroup.det (levZ k r m z 0)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 0 : ℂ) / 2)) * ((nabs k (GeneralLinearGroup.det (levZ k r m z 1)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 1 : ℂ) / 2))`. Simplify using `only [deltaHalf, Fin.prod_univ_two, MonoidHom.finset_prod_apply, Units.val_mul]`. Both sides reduce to the same expression. Rewrite using `[key, h0, h1, hdet, map_one, modExp_two_one, nabs_pow]`. Establish `hx : 0 ≤ nabs k z` using `by simp [nabs]`.

Establish `hn1 : nabs k 1 = 1` using `by simp [nabs]`. Rewrite using `[hn1]`. Simplify using `only [Complex.ofReal_one, Complex.one_cpow, one_mul]`. Establish `hexp : (((-(r : ℤ) : ℤ) : ℂ) / 2) = (((-(r : ℝ)) / 2 : ℝ) : ℂ)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp, ← Complex.ofReal_cpow (pow_nonneg hx m), ← Real.rpow_natCast_mul hx]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaHalf_levZ (r m : ℕ) (z : kˣ) :
    (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k z ^ (-((m * r : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  have h0 : levZ k r m z 0 = 1 := by simp [levZ] <;> rfl
  have h1 : levZ k r m z 1 = GeneralLinearGroup.scalar (Fin (dd r m 1)) z := by simp [levZ]
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (dd r m 1)) z) = z ^ m := by
    rw [GeneralLinearGroup.det_scalar]
    simp [dd]
  have key : (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 0)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 0 : ℂ) / 2)) *
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 1)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 1 : ℂ) / 2)) := by
    simp only [deltaHalf, Fin.prod_univ_two, MonoidHom.finset_prod_apply, Units.val_mul]
    rfl
  rw [key, h0, h1, hdet, map_one, modExp_two_one, nabs_pow]
  have hx : 0 ≤ nabs k z := by simp [nabs]
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  rw [hn1]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hexp : (((-(r : ℤ) : ℤ) : ℂ) / 2) = (((-(r : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_cpow (pow_nonneg hx m), ← Real.rpow_natCast_mul hx]
  congr 2
  push_cast
  ring

end Two

end PositivityTheory.RgUd.CellA
