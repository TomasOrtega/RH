import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.Under

/- English proof (translation)
Establish `hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E)` using `Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)`. Take `⟨x, y, hxy⟩` from `hc`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))`.
-/
theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]`. Use `card_nsmul_eq_zero' (G := kP P) (x := 1)` as an intermediate fact. Rewrite `this` using `[nsmul_one]`. Then use the resulting hypothesis.
-/
theorem q_mem {D : D7} {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

/- English proof (translation)
Introduce `D T L μ0 hL hPg i t PP hPP v hv`. Distinguish the cases in `hg : v ∈ gPl D`. Conclude with `Or.inl hg`. Break down `hPP with hP | hQ` into its components or cases. Take `⟨k, w, rfl⟩` from `(hPg _).1 hP`.

Conclude with `absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg`. Use `Or.inr ⟨hg, PP, hv, fun hu => ?_⟩` and prove the remaining obligations. Take `⟨⟨q, hq1, hq2, -, hq4⟩, -⟩` from `hL.Q_pl t PP hQ`. Establish `hm : (L.C.mu0 i).UnrAt PP` using `(L.C.isMu0 i).unr PP fun l hl => not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)`. Establish `hx : (L.xiH t).UnrAt PP`.

Introduce `x hx`. Establish `h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1` using `hu x hx`. Rewrite `h1` using `[hm x hx, one_mul]`. Then use the resulting hypothesis. Conclude with `(hL.Q_ram t PP).2 (Or.inl hQ) hx`.
-/
theorem places_under : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ L.Pg ∨ PP ∈ L.Q t → ∀ v, NG.OverPl PP v → v ∈ gPl D ∪ qPl D (L.C.mu0 i * L.xiH t) := by
  intro D T L μ0 hL hPg i t PP hPP v hv
  by_cases hg : v ∈ gPl D
  · exact Or.inl hg
  rcases hPP with hP | hQ
  · obtain ⟨k, w, rfl⟩ := (hPg _).1 hP
    exact absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg
  · refine Or.inr ⟨hg, PP, hv, fun hu => ?_⟩
    obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hQ
    have hm : (L.C.mu0 i).UnrAt PP := (L.C.isMu0 i).unr PP fun l hl =>
      not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    have hx : (L.xiH t).UnrAt PP := by
      intro x hx
      have h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1 := hu x hx
      rwa [hm x hx, one_mul] at h1
    exact (hL.Q_ram t PP).2 (Or.inl hQ) hx

end GlobalTheory.MtIn.Under

end
