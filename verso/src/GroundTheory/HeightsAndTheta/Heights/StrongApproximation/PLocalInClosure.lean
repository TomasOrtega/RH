import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Introduce `F E _ _ _ _ _ c hrk hc N J hJ hdet ⟨e, he0, hee⟩ _ _ v g hg`. Take `⟨hinv, hfix, hrank2, hred, h2, hcomm, hform⟩` from `hLR F E c hrk hc v`. Establish `hinj : Function.Injective (inclV E v)` using `Algebra.TensorProduct.includeRight_injective (algebraMap F (v.adicCompletion F)).injective`. Establish `hcinv : ∀ x, c.toRingHom (c.toRingHom x) = x` using `fun x => hinj (by`. Express the relevant statement in the definitionally equal form `inclV E v (c (c x)) = inclV E v x`.

Rewrite using `[← hcomm, ← hcomm, hinv])`. Take `⟨f, hff, hef⟩` from `hHP E c.toRingHom hcinv two_ne_zero N J hJ hdet e he0 hee`. Take `⟨-, h1, hmul, heich⟩` from `hCl F E c hrk hc N J hJ hdet e f hee hff hef`. Establish `hJv : (J.map (inclV E v))ᵀ = (J.map (inclV E v)).map (sigV c v)`. Use extensionality with `i j`.

Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[hcomm]`. Establish `h` using `Matrix.ext_iff.mpr hJ i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply] at h`. Rewrite using `[h]`.

Establish `hdetv : IsUnit (J.map (inclV E v)).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hdet.map _`. Establish `hzero : ∀ x y : Fin N → E, hf c.toRingHom J x y = 0 → hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y) = 0` using `fun x y h => by rw [← hform, h, map_zero]`. Establish `hefv : hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f) = 1`.

Rewrite using `[← hform, hef, map_one]`. Establish `hg'` using `hg`. Rewrite `hg'` using `[locGen _ _ (sigV c v) hinv hfix hrank2 hred h2 N _ hJv hdetv _ _ (hzero e e hee) (hzero f f hff) hefv]`. Use `clear hg`. Take `⟨-, hPv⟩` from `hPM F E c hrk hc`.

Take `⟨-, -, -, -, -, -, -, -, hPN⟩` from `hPv v`. Take `⟨hemb1, hembmul, -⟩` from `hPN N`. Proceed by induction on `hg' using Submonoid.closure_induction with`. Consider the case `mem x hx => exact heich ((hEA F E c hrk hc v N J).2 hJ e f hee hff hef x hx)`. Consider the case `one => rw [hemb1]`.

Conclude with `h1`. Consider the case `mul x y _ _ hx hy => rw [hembmul]`. Conclude with `hmul _ hx _ hy`.
-/
theorem LocalInClosure.proof (hHP : HypPairExists.Statement) (hCl : ClosureIsSubmonoid.Statement)
    (hLR : LocalRingHypotheses.Statement) (hPM : PlaceMaps.Statement)
    (hEA : EichlerAtPlace.Statement) : LocalInClosure.Statement := by
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet ⟨e, he0, hee⟩ _ _ v g hg
  obtain ⟨hinv, hfix, hrank2, hred, h2, hcomm, hform⟩ := hLR F E c hrk hc v

  have hinj : Function.Injective (inclV E v) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (v.adicCompletion F)).injective
  have hcinv : ∀ x, c.toRingHom (c.toRingHom x) = x := fun x =>
    hinj (by
      change inclV E v (c (c x)) = inclV E v x
      rw [← hcomm, ← hcomm, hinv])

  obtain ⟨f, hff, hef⟩ := hHP E c.toRingHom hcinv two_ne_zero N J hJ hdet e he0 hee
  obtain ⟨-, h1, hmul, heich⟩ := hCl F E c hrk hc N J hJ hdet e f hee hff hef

  have hJv : (J.map (inclV E v))ᵀ = (J.map (inclV E v)).map (sigV c v) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [hcomm]
    have h := Matrix.ext_iff.mpr hJ i j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h
    rw [h]
  have hdetv : IsUnit (J.map (inclV E v)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hzero : ∀ x y : Fin N → E, hf c.toRingHom J x y = 0 →
      hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y) = 0 :=
    fun x y h => by rw [← hform, h, map_zero]
  have hefv : hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f) = 1 := by
    rw [← hform, hef, map_one]
  have hg' := hg
  rw [locGen _ _ (sigV c v) hinv hfix hrank2 hred h2 N _ hJv hdetv _ _ (hzero e e hee)
    (hzero f f hff) hefv] at hg'
  clear hg

  obtain ⟨-, hPv⟩ := hPM F E c hrk hc
  obtain ⟨-, -, -, -, -, -, -, -, hPN⟩ := hPv v
  obtain ⟨hemb1, hembmul, -⟩ := hPN N
  induction hg' using Submonoid.closure_induction with
  | mem x hx => exact heich ((hEA F E c hrk hc v N J).2 hJ e f hee hff hef x hx)
  | one => rw [hemb1]; exact h1
  | mul x y _ _ hx hy => rw [hembmul]; exact hmul _ hx _ hy

end StrongApprox

end GroundTheory.Heights₂.Heights
