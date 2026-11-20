import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

/- English proof (translation)
Establish `h' : ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ Q.TauCoord a b k` using `h`. Use `choose k hk hc using h'`. Use `⟨fun a b => Exists.choose (hc a b), fun a b => ⟨(Exists.choose_spec (hc a b)).1, k a b, hk a b, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Exists.choose_spec (hc a b)).2`.
-/
theorem exists_tauIn {Q : Data V} {N : ℕ} {s : Fin N → V} {ε : Fin N → LinearMap.BilinForm ℤ Q.X}
    (h : Q.IsMonomialTau s ε) : ∃ τ₀ : Gens Q, TauIn Q τ₀ s ε := by
  have h' : ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ Q.TauCoord a b k := h

  choose k hk hc using h'
  refine ⟨fun a b => Exists.choose (hc a b), fun a b => ⟨(Exists.choose_spec (hc a b)).1, k a b, hk a b, ?_⟩⟩
  exact (Exists.choose_spec (hc a b)).2

/- English proof (translation)
Introduce `a b`. Take `⟨hg, k, hk, hv⟩` from `h a b`. Conclude with `⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩`.
-/
theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

/- English proof (translation)
The claim follows from `exists_tauIn (Wit.tate_isMonomialTau k)`.
-/
theorem tate_tauIn (k : ℤ) :
    ∃ τ₀ : Gens (Wit.tate k), TauIn (Wit.tate k) τ₀ ![PowerSeries.X] ![k • mulForm] :=
  exists_tauIn (Wit.tate_isMonomialTau k)

/- English proof (translation)
Use `⟨spMap ((Subfield.topEquiv (K := K)).symm : K →+* (⊤ : Subfield K)) ≫ P, ?_⟩` and prove the remaining obligations. Establish `hid : (⊤ : Subfield K).subtype.comp ((Subfield.topEquiv (K` using `K)).symm : K →+* (⊤ : Subfield K)) = RingHom.id K := by`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc]`.

Unfold `spMap`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`.
-/
theorem defOver_top {K : Type} [Field K] {Y : Scheme.{0}} (P : Sp K ⟶ Y) : DefOver (⊤ : Subfield K) P := by
  refine ⟨spMap ((Subfield.topEquiv (K := K)).symm : K →+* (⊤ : Subfield K)) ≫ P, ?_⟩

  have hid : (⊤ : Subfield K).subtype.comp ((Subfield.topEquiv (K := K)).symm : K →+* (⊤ : Subfield K)) =
      RingHom.id K := by
    ext x
    rfl
  rw [← Category.assoc]
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end GlobalTheory.Poinc.Sep.Model
