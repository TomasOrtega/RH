import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IotaConj

/- English proof (translation)
Simplify using `[sigR, inclE]`.
-/
theorem sigR_inclE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) :
    sigR σ R (inclE (F := F) R x) = inclE (F := F) R (σ x) := by
  simp [sigR, inclE]

/- English proof (translation)
Establish `key : OAd F E ≤ (OAd F E).comap (sigR σ (Ad F))` using `by show tensInt (F := F) (Ad F) (intOE E) (intAd F) ≤ (tensInt (F := F) (Ad F) (intOE E) (intAd F)).comap (sigR σ (Ad F))`. Use `(Subring.closure_le).2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Take `⟨z, rfl⟩` from `hx`. Establish `hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E z))` using `(RingOfIntegers.isIntegral_coe z).map (σ : E →+* E).toIntAlgHom`.

Use `Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E z), ⟨⟨_, hint⟩, rfl⟩⟩, ?_⟩)` and prove the remaining obligations. Simplify using `[sigR]`. Use `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)` and prove the remaining obligations. Simplify using `[sigR]`. Conclude with `key ha`.
-/
theorem sigR_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) : sigR σ (Ad F) a ∈ OAd F E := by

  have key : OAd F E ≤ (OAd F E).comap (sigR σ (Ad F)) := by
    show tensInt (F := F) (Ad F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (Ad F) (intOE E) (intAd F)).comap (sigR σ (Ad F))
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E z)) :=
        (RingOfIntegers.isIntegral_coe z).map (σ : E →+* E).toIntAlgHom
      refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E z), ⟨⟨_, hint⟩, rfl⟩⟩, ?_⟩)
      simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
      simp [sigR]
  exact key ha

/- English proof (translation)
Take `⟨-, h2, -, h4, -⟩` from `GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E`. Take `⟨-, -, h3', -, -⟩` from `GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F' E'`. Use `set D : E ⊗[F] Ad F → E' ⊗[F'] Ad F' := fun b => ι (sigR σ (Ad F) b) - sigR σ' (Ad F') (ι b) with hD`. Establish `Dadd : ∀ b c, D (b + c) = D b + D c`. Introduce `b c`.

Simplify using `only [hD, map_add]`. Normalize the expressions using the abelian group laws. Establish `Dmul : ∀ (m : ℕ) b, D ((m : E ⊗[F] Ad F) * b) = (m : E' ⊗[F'] Ad F') * D b`. Introduce `m b`. Simplify using `only [hD, map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `Dincl : ∀ x : E, D (inclE (F` using `F) (Ad F) x) = 0 := by`. Introduce `x`. Simplify using `only [hD, sigR_inclE, hι, he, sub_self]`. Establish `DO : ∀ b ∈ OAd F E, D b ∈ OAd F' E'`.

Introduce `b hb`. Conclude with `Subring.sub_mem _ ((hO _).1 (sigR_mem_OAd σ hb)) (sigR_mem_OAd σ' ((hO _).1 hb))`. Establish `Dzero : ∀ b ∈ OAd F E, D b = 0`. Introduce `b hb`. Use `h3' (D b) fun m hm => ?_` and prove the remaining obligations.

Take `⟨x, t, ht, hbt⟩` from `h2 b hb m hm`. Conclude with `⟨D t, DO t ht, by rw [hbt, Dadd, Dincl, Dmul, zero_add]⟩`. Take `⟨m, hm, hma⟩` from `h4 a`. Establish `h0 : (m : E' ⊗[F'] Ad F') * D a = 0` using `by rw [← Dmul]; exact Dzero _ hma`. Establish `hu : IsUnit (m : E' ⊗[F'] Ad F')`.

Rewrite using `[← map_natCast (inclE (F := F') (E := E') (Ad F')) m]`. Conclude with `(IsUnit.mk0 (m : E') (Nat.cast_ne_zero.2 hm.ne')).map _`. Establish `hDa : D a = 0` using `hu.mul_right_eq_zero.1 h0`. Simplify using `only [hD] at hDa`. Conclude with `sub_eq_zero.1 hDa`.
-/
theorem iota_sigR (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (σ : E →ₐ[F] E) (σ' : E' →ₐ[F'] E') (e : E ≃+* E') (ι : E ⊗[F] Ad F ≃+* E' ⊗[F'] Ad F')
    (he : ∀ x, e (σ x) = σ' (e x))
    (hι : ∀ x, ι (inclE (F := F) (Ad F) x) = inclE (F := F') (Ad F') (e x))
    (hO : ∀ a, a ∈ OAd F E ↔ ι a ∈ OAd F' E') (a : E ⊗[F] Ad F) :
    ι (sigR σ (Ad F) a) = sigR σ' (Ad F') (ι a) := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E
  obtain ⟨-, -, h3', -, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F' E'

  set D : E ⊗[F] Ad F → E' ⊗[F'] Ad F' :=
    fun b => ι (sigR σ (Ad F) b) - sigR σ' (Ad F') (ι b) with hD
  have Dadd : ∀ b c, D (b + c) = D b + D c := by
    intro b c; simp only [hD, map_add]; abel
  have Dmul : ∀ (m : ℕ) b, D ((m : E ⊗[F] Ad F) * b) = (m : E' ⊗[F'] Ad F') * D b := by
    intro m b; simp only [hD, map_mul, map_natCast]; ring
  have Dincl : ∀ x : E, D (inclE (F := F) (Ad F) x) = 0 := by
    intro x; simp only [hD, sigR_inclE, hι, he, sub_self]
  have DO : ∀ b ∈ OAd F E, D b ∈ OAd F' E' := by
    intro b hb
    exact Subring.sub_mem _ ((hO _).1 (sigR_mem_OAd σ hb)) (sigR_mem_OAd σ' ((hO _).1 hb))
  have Dzero : ∀ b ∈ OAd F E, D b = 0 := by
    intro b hb
    refine h3' (D b) fun m hm => ?_
    obtain ⟨x, t, ht, hbt⟩ := h2 b hb m hm
    exact ⟨D t, DO t ht, by rw [hbt, Dadd, Dincl, Dmul, zero_add]⟩
  obtain ⟨m, hm, hma⟩ := h4 a
  have h0 : (m : E' ⊗[F'] Ad F') * D a = 0 := by rw [← Dmul]; exact Dzero _ hma
  have hu : IsUnit (m : E' ⊗[F'] Ad F') := by
    rw [← map_natCast (inclE (F := F') (E := E') (Ad F')) m]
    exact (IsUnit.mk0 (m : E') (Nat.cast_ne_zero.2 hm.ne')).map _
  have hDa : D a = 0 := hu.mul_right_eq_zero.1 h0
  simp only [hD] at hDa
  exact sub_eq_zero.1 hDa

end GlobalTheory.St.G.IotaConj
