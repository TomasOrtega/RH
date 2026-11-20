import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
Use `show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))`. Establish `: H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj` using `map_mul (H.gal).symm g (R.cc)`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem emb_mul_cc (g : R.GG) (x : H.E) : H.emb (g * R.cc) x = H.emb g (H.conj x) := by
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj := map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

/- English proof (translation)
The claim follows from `(H.conjE_mem_hostF_iff x).1 hx`.
-/
theorem conj_of_mem_F {x : H.E} (hx : x ∈ H.F) : H.conj x = x :=
  (H.conjE_mem_hostF_iff x).1 hx

/- English proof (translation)
Rewrite `hg`, the goal using `[Formalism.HC.Frame.mem_Psi_iff]`. Use `show g.1.2 * (-1) = 1`. Break down `Int.units_eq_one_or g.1.2 with h | h` into its components or cases. Conclude with `absurd h hg`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem mul_cc_mem_Psi {g : R.GG} (hg : g ∉ R.Psi) : g * R.cc ∈ R.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
  show g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h
  · exact absurd h hg
  · rw [h]; rfl

/- English proof (translation)
Introduce `w`. Establish `: Algebra.IsAlgebraic H.F H.E` using `Algebra.IsAlgebraic.tower_top (K := ℚ) H.F`. Take `⟨W, rfl⟩` from `InfinitePlace.comap_surjective (K := H.E) w`. Take `⟨g, hg⟩` from `(factEmb R H).1.2 W.embedding`. Establish `hW : InfinitePlace.mk (H.emb g) = W` using `by rw [hg]; exact InfinitePlace.mk_embedding W`.

Distinguish the cases in `hgP : g ∈ R.Psi`. Use `⟨⟨g, hgP⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hW]`. Conclude with `(InfinitePlace.comap_mk _ _).symm`. Use `⟨⟨g * R.cc, mul_cc_mem_Psi hgP⟩, ?_⟩` and prove the remaining obligations.

Establish `: (H.emb (g * R.cc)).comp H.F.subtype = (H.emb g).comp H.F.subtype` using `RingHom.ext fun x => by show H.emb (g * R.cc) (x : H.E) = H.emb g (x : H.E)`. Rewrite using `[emb_mul_cc, conj_of_mem_F H x.2]`. Rewrite using `[realPl, this, ← hW]`. Conclude with `(InfinitePlace.comap_mk _ _).symm`.
-/
theorem realPl_surjective : Function.Surjective (realPl H) := by
  intro w
  have : Algebra.IsAlgebraic H.F H.E := Algebra.IsAlgebraic.tower_top (K := ℚ) H.F
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (K := H.E) w
  obtain ⟨g, hg⟩ := (factEmb R H).1.2 W.embedding
  have hW : InfinitePlace.mk (H.emb g) = W := by rw [hg]; exact InfinitePlace.mk_embedding W
  by_cases hgP : g ∈ R.Psi
  · refine ⟨⟨g, hgP⟩, ?_⟩
    rw [← hW]; exact (InfinitePlace.comap_mk _ _).symm
  · refine ⟨⟨g * R.cc, mul_cc_mem_Psi hgP⟩, ?_⟩
    have : (H.emb (g * R.cc)).comp H.F.subtype = (H.emb g).comp H.F.subtype := RingHom.ext fun x => by
      show H.emb (g * R.cc) (x : H.E) = H.emb g (x : H.E)
      rw [emb_mul_cc, conj_of_mem_F H x.2]
    rw [realPl, this, ← hW]; exact (InfinitePlace.comap_mk _ _).symm

/- English proof (translation)
Use `(realPl_surjective H).bijective_of_nat_card_le ?_` and prove the remaining obligations. Establish `h1` using `IsTotallyReal.finrank (K := H.F)`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces H.F`. Establish `h3 : Module.finrank ℚ H.F = R.f` using `H.finrank_hostF`. Rewrite using `[(factCardPsi R H).1, Nat.card_eq_fintype_card, h2, ← h1, h3]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem realPlBij : RealPlBij H := by
  refine (realPl_surjective H).bijective_of_nat_card_le ?_
  have h1 := IsTotallyReal.finrank (K := H.F)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces H.F
  have h3 : Module.finrank ℚ H.F = R.f := H.finrank_hostF
  rw [(factCardPsi R H).1, Nat.card_eq_fintype_card, h2, ← h1, h3]
  omega

def tauPl (D : D7) : D.what₂.Tau ≃ InfinitePlace D.host.F :=
  D.eTau.trans (Equiv.ofBijective (realPl D.host) (realPlBij D.host))

end Formalism.L2.Host
