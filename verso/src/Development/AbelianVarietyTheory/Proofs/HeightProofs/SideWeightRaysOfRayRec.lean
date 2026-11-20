import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Formalism.LocalToGlobal.NumberFieldFamilies.RamifiedPrimesTrivialTuple
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX
  GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.RaysW

/- English proof (translation)
Take `⟨P, hne, hP⟩` from `(Ring.not_isField_iff_exists_prime (R := 𝓞 L)).1 (NumberField.RingOfIntegers.not_isField L)`. Conclude with `⟨⟨P, hP, hne⟩⟩`.
-/
theorem nonempty_heightOneSpectrum (L : Type) [Field L] [NumberField L] : Nonempty (HeightOneSpectrum (𝓞 L)) := by
  obtain ⟨P, hne, hP⟩ := (Ring.not_isField_iff_exists_prime (R := 𝓞 L)).1 (NumberField.RingOfIntegers.not_isField L)
  exact ⟨⟨P, hP, hne⟩⟩

/- English proof (translation)
Introduce `hL 𝒮 ν K p hR t`. Establish `hlev` using `p.x.what₂.r.z.lev`. Establish `hmu` using `p.x.what₂.mu`. Establish `hn` using `p.x.n.Q`. Express the relevant statement in the definitionally equal form `R3.TupU p.w.I (R3.usedOf p.w.I p.T p.x.Wt) at t`.

Use `show GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField _ (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.x.what₂.r.z.R.toRealDat t)`. Break down `(R3.mem_range_ixOf p.w.I).1 ⟨t, rfl⟩ with h0 | ⟨w, hw, hxi⟩` into its components or cases. Take `⟨v⟩` from `nonempty_heightOneSpectrum (p.w.D p.Z).what₂.LL`. Use `hR ((p.w.D p.Z).plEq.symm v) _ fun P hP ↦ ?_` and prove the remaining obligations. Establish `hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P` using `(hlev.is.Q_ram t P).2 (Or.inl hP)`.

Rewrite `hram` using `[hlev.xiH t, h0, p.w.ok.trueColumnChoices_heckeChar_reference_eq_one]`. Conclude with `absurd (Formalism.L2.Fam.DivCQ.unrAt_one P) hram`. Use `hR w _ fun P hP ↦ ?_` and prove the remaining obligations. Establish `hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P` using `(hlev.is.Q_ram t P).2 (Or.inl hP)`. Establish `hpl` using `(hlev.is.Q_pl t P hP).1`.

Distinguish the cases in `hpd : (((p.w.D p.Z).host.pde * (p.w.D p.Z).host.pde' : ℕ) : 𝓞 (p.w.D p.Z).host.E) ∈ P.asIdeal`. Take `⟨q, hq, hc, -⟩` from `hpl`. Conclude with `Or.inl ⟨hpd, hc ▸ hq⟩`. Use `right`. Establish `hx : p.x.what₂.r.z.R.xiH t = p.T.xiTw p.f w`.

Rewrite using `[hlev.xiH t, hxi, p.w.C_eq]`. Rewrite `hram` using `[hx]`. Establish `h1 : ¬ ((p.B.host.pde : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal` using `fun h ↦ hpd (by`. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ h)`.

Establish `h2 : ¬ ((p.B.host.pde' : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal` using `fun h ↦ hpd (by`. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_left _ _ h)`. Establish `hδ : (if p.B.places.resChar w = p.B.host.pde then p.f.del' else p.f.del).UnrAt P` using `by split_ifs`. Conclude with `p.f.isDel'.unr P h2`.

Conclude with `p.f.isDel.unr P h1`. Establish `hψ : ¬ (p.T.psi w).UnrAt P` using `fun h ↦ hram (Formalism.L2.Host.HChar.UnrAt.mul hδ h)`. Establish `hQ : P ∈ p.T.Q w`. Assume the negation of the conclusion as `hq`. Conclude with `hψ (((p.T.psi_is w).ram P).2 hq)`.

Use `⟨fun hm ↦ ?_, (hn w hw).1 ▸ hQ⟩` and prove the remaining obligations. Establish `e1 : p.T.xiTw p.f w = 1`. Rewrite using `[← hmu.tw w, ← hmu.on w hw]`. Conclude with `(congrArg p.w.I.xi hm).trans hmu.mu0`. Rewrite `hram` using `[e1]`.

Conclude with `hram (Formalism.L2.Fam.DivCQ.unrAt_one P)`.
-/
theorem rays_of_rayRec : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K),
    RayRec (p.w.D p.Z) p.O.ex.nch → (sideW ν p).Rays := by
  intro hL 𝒮 ν K p hR t
  have hlev := p.x.what₂.r.z.lev
  have hmu := p.x.what₂.mu
  have hn := p.x.n.Q
  change R3.TupU p.w.I (R3.usedOf p.w.I p.T p.x.Wt) at t
  show GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField _ (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.x.what₂.r.z.R.toRealDat t)
  rcases (R3.mem_range_ixOf p.w.I).1 ⟨t, rfl⟩ with h0 | ⟨w, hw, hxi⟩
  ·
    obtain ⟨v⟩ := nonempty_heightOneSpectrum (p.w.D p.Z).what₂.LL
    refine hR ((p.w.D p.Z).plEq.symm v) _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    rw [hlev.xiH t, h0, p.w.ok.trueColumnChoices_heckeChar_reference_eq_one] at hram
    exact absurd (Formalism.L2.Fam.DivCQ.unrAt_one P) hram
  ·
    refine hR w _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    have hpl := (hlev.is.Q_pl t P hP).1
    by_cases hpd : (((p.w.D p.Z).host.pde * (p.w.D p.Z).host.pde' : ℕ) : 𝓞 (p.w.D p.Z).host.E) ∈ P.asIdeal
    · obtain ⟨q, hq, hc, -⟩ := hpl
      exact Or.inl ⟨hpd, hc ▸ hq⟩
    · right
      have hx : p.x.what₂.r.z.R.xiH t = p.T.xiTw p.f w := by
        rw [hlev.xiH t, hxi, p.w.C_eq]
      rw [hx] at hram
      have h1 : ¬ ((p.B.host.pde : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
      have h2 : ¬ ((p.B.host.pde' : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)

      have hδ : (if p.B.places.resChar w = p.B.host.pde then p.f.del' else p.f.del).UnrAt P := by
        split_ifs
        · exact p.f.isDel'.unr P h2
        · exact p.f.isDel.unr P h1
      have hψ : ¬ (p.T.psi w).UnrAt P := fun h ↦ hram (Formalism.L2.Host.HChar.UnrAt.mul hδ h)
      have hQ : P ∈ p.T.Q w := by
        by_contra hq
        exact hψ (((p.T.psi_is w).ram P).2 hq)
      refine ⟨fun hm ↦ ?_, (hn w hw).1 ▸ hQ⟩

      have e1 : p.T.xiTw p.f w = 1 := by
        rw [← hmu.tw w, ← hmu.on w hw]
        exact (congrArg p.w.I.xi hm).trans hmu.mu0
      rw [e1] at hram
      exact hram (Formalism.L2.Fam.DivCQ.unrAt_one P)

end GlobalTheory.Plug.RaysW

end
