import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

noncomputable section

namespace PI.VolStabS.AdmissibleCompactSupport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabS PI.VolStabS.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 F))` to `{v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}`. Establish `hS : cofinite ≤ 𝓟 S` using `le_principal_iff.2 hf`. Set `R` to `fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F`. Set `A` to `fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Set `K : Set (Πʳ v, [R v, A v]_[𝓟 S])` to `{x | ∀ v, x v ∈ D v}`.

Establish `hK : IsCompact K`. Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]`. Establish `e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩ v _`. Conclude with `hx v`. Introduce `hg`. Use `⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩` and prove the remaining obligations. Rewrite using `[eventually_principal]`.

Introduce `v hv`. Establish `h` using `hg v (mem_univ v)`. Rewrite `h` using `[show D v = _ from hv]`. Then use the resulting hypothesis. Rewrite using `[e]`. Conclude with `isCompact_univ_pi hc`.

Establish `e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨⟨x, ?_⟩, hx, rfl⟩` and prove the remaining obligations.

Rewrite using `[eventually_principal]`. Introduce `v hv`. Establish `h` using `hx v`. Rewrite `h` using `[show D v = _ from hv]`. Then use the resulting hypothesis. Introduce and unpack `⟨y, hy, rfl⟩ v`.

Conclude with `hy v`. Rewrite using `[e]`. Conclude with `hK.image (RestrictedProduct.continuous_inclusion hS)`.
-/
theorem isCompact_finBox {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[𝓟 S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩
        rw [eventually_principal]
        intro v hv
        have h := hg v (mem_univ v)
        rwa [show D v = _ from hv] at h
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [eventually_principal]
      intro v hv
      have h := hx v
      rwa [show D v = _ from hv] at h
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

/- English proof (translation)
Simplify using `only [projV]`. Rewrite using `[crd_map]`. Both sides reduce to the same expression.
-/
theorem crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl

/- English proof (translation)
Establish `h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite, (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F` using `fun i j k => (crd b (Af F) (Y i j) k).2`. Use `filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k => h i j k] with v hv`. Introduce `i j k`. Use `crd_projV b Y v i j k` as an intermediate fact. Simplify using `only [crd] at this`.

Rewrite using `[this]`. Conclude with `hv i j k`.
-/
theorem eventually_mem_latV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k

variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)

/- English proof (translation)
Use `(Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b Y))).subset ?_` and prove the remaining obligations. Introduce `v hv h`. Apply `hv` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[h.1, Set.indicator_of_mem h.2]`.

Both sides reduce to the same expression.
-/
theorem mulSupport_finite
    (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1) (Y : Fin a → Fin M → Af F ⊗[F] E) :
    (Function.mulSupport fun v => Φv v (projV v Y)).Finite := by
  refine (Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b Y))).subset ?_
  intro v hv h
  apply hv
  simp only
  rw [h.1, Set.indicator_of_mem h.2]
  rfl

/- English proof (translation)
Establish `hfin` using `mulSupport_finite b Φv hae Y`. Rewrite `h` using `[finprod_eq_prod _ hfin]`. Distinguish the cases in `hv : v ∈ hfin.toFinset`. Conclude with `Finset.prod_ne_zero_iff.1 h v hv`. Rewrite `hv` using `[Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not]`.

Rewrite using `[hv]`. Conclude with `one_ne_zero`.
-/
theorem factor_ne_zero (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1)
    (Y : Fin a → Fin M → Af F ⊗[F] E) (h : ∏ᶠ v, Φv v (projV v Y) ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Φv v (projV v Y) ≠ 0 := by
  have hfin := mulSupport_finite b Φv hae Y
  rw [finprod_eq_prod _ hfin] at h
  by_cases hv : v ∈ hfin.toFinset
  · exact Finset.prod_ne_zero_iff.1 h v hv
  · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
    rw [hv]
    exact one_ne_zero

end PI.VolStabS.AdmissibleCompactSupport

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabS.AdmissibleCompactSupport

end PI.VolStabS
