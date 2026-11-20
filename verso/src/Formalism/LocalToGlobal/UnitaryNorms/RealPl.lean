import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem emb_mul_cc (g : R.GG) (x : H.E) : H.emb (g * R.cc) x = H.emb g (H.conj x) := by
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj := map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_of_mem_F {x : H.E} (hx : x ∈ H.F) : H.conj x = x :=
  (H.conjE_mem_hostF_iff x).1 hx

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mul_cc_mem_Psi {g : R.GG} (hg : g ∉ R.Psi) : g * R.cc ∈ R.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
  show g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h
  · exact absurd h hg
  · rw [h]; rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

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
