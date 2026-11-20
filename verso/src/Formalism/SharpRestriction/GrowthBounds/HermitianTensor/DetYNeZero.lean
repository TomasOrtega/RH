import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
The claim follows from `Matrix.det_mvPolynomialX_ne_zero (Fin r) K`.
-/
theorem detY_ne_zero (K : Type) [Field K] (r : ℕ) : detY K r ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin r) K

/- English proof (translation)
Introduce `p n' R r hr a c N α hαA hαN hc hca`. Use `letI := R.charZeroO`. Use `haveI := R.std.1.frac_O`. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Take `⟨m, rfl⟩ : ∃ m, r = m + 1` from `⟨r - 1, by omega⟩`.

Take `⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e` from `⟨_, rfl⟩`. Establish `he : ∀ i, e ≤ α i` using `fun i => he_def ▸ hαA (Fin.le_last i)`. Establish `hex : ∃ i, α i = e` using `⟨_, he_def⟩`. Establish `heN : e ≤ N` using `he_def ▸ hαN _`. Establish `hγA : Antitone (fun i => α i - e)`.

Introduce `i j hij`. Use `hαA hij` as an intermediate fact. Use `show α j - e ≤ α i - e`. Use linear arithmetic over natural numbers and integers. Establish `wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf}, ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν'`.

Introduce and unpack `_ _ _ rfl h`. Conclude with `h`. Establish `wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O}, ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν'`. Introduce and unpack `_ _ _ rfl h`. Conclude with `h`.

Establish `hwα : (fun j => (fun i => α i - e) j + e) = α`. Use function extensionality and compare the values at `j`. Use `he j` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Take `⟨τ, hτK, hτO, hτsurj, hτeq⟩` from `hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex`. Take `⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩` from `hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])`. Use `set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def`. Establish `hD0 : D ≠ 0` using `pow_ne_zero _ (detY_ne_zero R.Kf _)`. Set `μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf` to `LinearMap.mulLeft R.Kf D`.

Establish `hμ : Function.Injective μ` using `fun u v h => mul_left_cancel₀ hD0 h`. Take `⟨Cc, hCc⟩` from `Submodule.exists_isCompl (LinearMap.range μ)`. Set `σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf` to `(LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc`. Establish `hσ : ∀ g, σ (D * g) = g`. Introduce `g`.

Establish `hmem : D * g ∈ LinearMap.range μ` using `⟨g, rfl⟩`. Use `show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g`. Rewrite using `[show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl, Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]`. Use `ext1`. Rewrite using `[LinearEquiv.ofInjective_apply]`.

Both sides reduce to the same expression. Take `⟨L, hL⟩` from `hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)`. Establish `hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f')`. Introduce `f f'`. Rewrite using `[hL]`.

Both sides reduce to the same expression. Establish `hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D`. Rewrite using `[map_pow, detY_map]`. Establish `hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α, ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g`. Introduce `f hf`.

Conclude with `hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)`. Establish `hdivO : ∀ f ∈ intO R.O (m + 1) α, ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g`. Introduce `f hf`. Take `⟨fO, hfO, rfl⟩` from `Submodule.mem_map.1 hf`. Take `⟨gO, hgO, hfg⟩` from `hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)`.

Use `⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show map (algebraMap R.O R.Kf) fO = _`. Rewrite using `[hfg, map_mul, hmapD]`. Use `choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')`. Use `⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩` and prove the remaining obligations.

Introduce `l hl f hf f' hf'`. Take `⟨g, hg, rfl⟩` from `hdivK f hf`. Rewrite using `[hL', hL', hσ]`. Establish `hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g)`. Rewrite using `[map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]`. Introduce `f hf f' hf'`. Take `⟨g, hg, rfl⟩` from `hdivO f hf`. Rewrite using `[hL', hσ]`.

Conclude with `hBint g hg (τ f') (hτO f' hf')`. Rewrite using `[hnb]`. Unfold `weylDim`. Use `Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Simplify using `only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]`.

Introduce `b`. Use `(hka b).trans ?_` and prove the remaining obligations. Establish `h1` using `hc 0 (Fin.last m)`. Conclude with `hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca`. Introduce `b`.

Take `⟨xO, hxO, hxe⟩` from `Submodule.mem_map.1 (hx b)`. Use `Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO, wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega) (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩` and prove the remaining obligations. Use `show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b`. Rewrite using `[map_mul, hmapD, ← hxe]`. Both sides reduce to the same expression.

Introduce `a' b`. Rewrite using `[hL', hσ, hτU]`. Conclude with `hdual a' b`.
-/
theorem qPh_of (hTau : TauP) (hSm : SmithP) (hBil : BilinP) (hDet : DetFactsP) (hNum : NumP) (hDD : DetDivP) : QPh := by
  intro p n' R r hr a c N α hαA hαN hc hca
  letI := R.charZeroO
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e := ⟨_, rfl⟩
  have he : ∀ i, e ≤ α i := fun i => he_def ▸ hαA (Fin.le_last i)
  have hex : ∃ i, α i = e := ⟨_, he_def⟩
  have heN : e ≤ N := he_def ▸ hαN _
  have hγA : Antitone (fun i => α i - e) := by
    intro i j hij
    have := hαA hij
    show α j - e ≤ α i - e
    omega
  have wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf},
      ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O},
      ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have hwα : (fun j => (fun i => α i - e) j + e) = α := by
    funext j
    have := he j
    simp only
    omega
  obtain ⟨τ, hτK, hτO, hτsurj, hτeq⟩ := hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex
  obtain ⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩ :=
    hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])
  set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def
  have hD0 : D ≠ 0 := pow_ne_zero _ (detY_ne_zero R.Kf _)
  let μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := LinearMap.mulLeft R.Kf D
  have hμ : Function.Injective μ := fun u v h => mul_left_cancel₀ hD0 h
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (LinearMap.range μ)
  let σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc
  have hσ : ∀ g, σ (D * g) = g := by
    intro g
    have hmem : D * g ∈ LinearMap.range μ := ⟨g, rfl⟩
    show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g
    rw [show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl,
      Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  obtain ⟨L, hL⟩ := hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)
  have hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f') := by
    intro f f'
    rw [hL]
    rfl
  have hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D := by
    rw [map_pow, detY_map]
  have hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α,
      ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    exact hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)
  have hdivO : ∀ f ∈ intO R.O (m + 1) α,
      ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    obtain ⟨fO, hfO, rfl⟩ := Submodule.mem_map.1 hf
    obtain ⟨gO, hgO, hfg⟩ := hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)
    refine ⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩
    show map (algebraMap R.O R.Kf) fO = _
    rw [hfg, map_mul, hmapD]
  choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')
  refine ⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩
  · intro l hl f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivK f hf
    rw [hL', hL', hσ]
    have hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g) := by
      rw [map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]
  · intro f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivO f hf
    rw [hL', hσ]
    exact hBint g hg (τ f') (hτO f' hf')
  · rw [hnb]
    unfold weylDim
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    simp only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]
  · intro b
    refine (hka b).trans ?_
    have h1 := hc 0 (Fin.last m)
    exact hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca
  · intro b
    obtain ⟨xO, hxO, hxe⟩ := Submodule.mem_map.1 (hx b)
    refine Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO,
      wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega)
        (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩
    show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b
    rw [map_mul, hmapD, ← hxe]
    rfl
  · intro a' b
    rw [hL', hσ, hτU]
    exact hdual a' b

end Formalism.MainNotions.flipOneThree.Pf

end
