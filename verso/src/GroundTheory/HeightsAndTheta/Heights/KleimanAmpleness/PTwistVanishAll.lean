import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x G B r η hη hspan`. Take `⟨M₀, -, hM₀⟩` from `hE S Ω N x Ω G.toSubFamily G.fg`. Take `⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩` from `hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan`. Take `⟨c₀, hc₀⟩` from `hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin`. Use `⟨c₀, fun i b c hi hc => ?_⟩` and prove the remaining obligations.

Take `⟨ι, π, hπ⟩` from `hsplit b c i`. Use `hc₀ i hi c hc` as an intermediate fact. Conclude with `⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩`.
-/
theorem TwistVanishAll.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanishAll.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun i b c hi hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c i
  have := hc₀ i hi c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
