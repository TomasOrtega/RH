import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section
namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y)` using `fun y => Prod.ext (mul_zero _) rfl`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (F …`. Generalize the expression as in `idemS S = I at hI ⊢`. Generalize the expression as in `idemSf S = J at hI ⊢`.

Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add, mul_add, mul_sub, hI, sub_zero, zero_sub, zero_add] <;> ring`.
-/
theorem prS_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prS S a (finGL E a k) = finGL E a (prSf S a k) := by
  have hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - idemSf S * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + idemSf S * k i j)
  generalize idemS S = I at hI ⊢
  generalize idemSf S = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add, mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

/- English proof (translation)
Establish `hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y)` using `fun y => Prod.ext (mul_zero _) rfl`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 …`. Generalize the expression as in `(1 - idemS S) = I at hI ⊢`. Generalize the expression as in `(1 - idemSf S) = J at hI ⊢`.

Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add, mul_add, mul_sub, hI, sub_zero, zero_sub, zero_add] <;> ring`.
-/
theorem prO_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prO S a (finGL E a k) = finGL E a (prOf S a k) := by
  have hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - (1 - idemSf S) * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + (1 - idemSf S) * k i j)
  generalize (1 - idemS S) = I at hI ⊢
  generalize (1 - idemSf S) = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add, mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x`. Use `continuous_const.add ?_` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp ((continuous_apply j).comp (continuous_apply i))`.
-/
theorem continuous_cornerGL_idemHom (a : ℕ) (e : Af E) (he : IsIdempotentElem e) :
    Continuous (cornerGL a (idemHom e he)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp
      ((continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
The claim follows from `continuous_cornerGL_idemHom a _ _`.
-/
theorem continuous_prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prSf S a) :=
  continuous_cornerGL_idemHom a _ _

/- English proof (translation)
The claim follows from `continuous_cornerGL_idemHom a _ _`.
-/
theorem continuous_prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prOf S a) :=
  continuous_cornerGL_idemHom a _ _

end GlobalTheory.SchurExt

/- English proof (translation)
Introduce `E _ _ a S V V' hV hV'`. Establish `h1` using `(continuous_prSf S a).tendsto 1`. Establish `h2` using `(continuous_prOf S a).tendsto 1`. Rewrite `h1`, `h2` using `[map_one]`. Use `filter_upwards [h1 hV, h2 hV'] with k hk hk'`.

Conclude with `⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩`.
-/
theorem GlobalTheory.SchurExt.eventually_prS_prO_finGL :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  intro E _ _ a S V V' hV hV'
  have h1 := (continuous_prSf S a).tendsto 1
  have h2 := (continuous_prOf S a).tendsto 1
  rw [map_one] at h1 h2
  filter_upwards [h1 hV, h2 hV'] with k hk hk'
  exact ⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩
