import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ModelShortOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

/- English proof (translation)
Introduce `p _ lam h2 hin`. Use `Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host` as an intermediate fact. Take `⟨b, hb, -⟩` from `exists_gen_K D.host`. Establish `hb' : b ^ 2 = -(D.host.d : D.host.K)` using `by rw [hb]; push_cast; rfl`. Establish `hpr` using `HI D.host.K (finrank_K D.host) b D.host.d p hb' (Fact.out) hin`.

Set `φK : D.host.K →+* Qbar` to `(D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun x => test_vector_mem_schwartz_bruhat D _)`. Set `c : D.host.K →+* D.host.K` to `(AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)`. Establish `hc : ∀ x : D.host.K, ((c x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)` using `fun x => AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x`. Establish `hne : ∃ x, c x ≠ x`. Use `⟨b, fun h => ?_⟩` and prove the remaining obligations.

Establish `hbE : ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E)`. Use `congrArg (fun z : D.host.K => (z : D.host.E)) hb'` as an intermediate fact. Simplify using `using this`. Establish `h1` using `hc b`. Rewrite `h1` using `[h]`.

Establish `h3` using `Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ (b : D.host.E)`. Rewrite `h3` using `[← h1]`. Establish `h4 : (D.host.φ₀ (b : D.host.E)) ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[← map_pow, hbE]`. Simplify using the standard rewrite rules.

Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h3.symm`. Rewrite `h4` using `[hr]`. Establish `h5 : ((r ^ 2 : ℝ) : ℂ) = ((-(D.host.d : ℝ) : ℝ) : ℂ)` using `by push_cast; exact h4`. Establish `h6 : r ^ 2 = -(D.host.d : ℝ)` using `by exact_mod_cast h5`. Establish `h7 : (0 : ℝ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`.

Use polynomial arithmetic with `[sq_nonneg r]`. Establish `key` using `HO D.host.K c p (lam.comp φK) (finrank_K D.host) hne h2 hpr`. Rewrite using `[← key]`. Unfold `OKp`. Use `congr 1`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [tauK, tauKc, RingHom.comp_apply]`.

Rewrite using `[lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]`. Use `congr 2`. Conclude with `Subtype.ext (congrArg D.host.φ₀ (hc _))`. Introduce and unpack `⟨a, rfl⟩`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Simplify using `only [tauK, tauKc, RingHom.comp_apply]`. Rewrite using `[lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]`. Use `congr 2`. Conclude with `Subtype.ext (congrArg D.host.φ₀ (hc _)).symm`.
-/
theorem okpInert_of (HO : OkpInertG) (HI : InertPrime) (D : D7) : okpInert D := by
  intro p _ lam h2 hin
  have := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  obtain ⟨b, hb, -⟩ := exists_gen_K D.host
  have hb' : b ^ 2 = -(D.host.d : D.host.K) := by rw [hb]; push_cast; rfl
  have hpr := HI D.host.K (finrank_K D.host) b D.host.d p hb' (Fact.out) hin

  let φK : D.host.K →+* Qbar :=
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun x => test_vector_mem_schwartz_bruhat D _)
  let c : D.host.K →+* D.host.K := (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)
  have hc : ∀ x : D.host.K, ((c x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := fun x =>
    AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x
  have hne : ∃ x, c x ≠ x := by
    refine ⟨b, fun h => ?_⟩
    have hbE : ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) := by
      have := congrArg (fun z : D.host.K => (z : D.host.E)) hb'
      simpa using this
    have h1 := hc b
    rw [h] at h1

    have h3 := Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ (b : D.host.E)
    rw [← h1] at h3
    have h4 : (D.host.φ₀ (b : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, hbE]; simp
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hr] at h4
    have h5 : ((r ^ 2 : ℝ) : ℂ) = ((-(D.host.d : ℝ) : ℝ) : ℂ) := by push_cast; exact h4
    have h6 : r ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h5
    have h7 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
    nlinarith [sq_nonneg r]
  have key := HO D.host.K c p (lam.comp φK) (finrank_K D.host) hne h2 hpr
  rw [← key]
  unfold OKp
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _))
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _)).symm

end Formalism.MainNotions.Ext
