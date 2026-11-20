import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports

open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `hRP hRI L _ _ _ N σ hσ`. Establish `G` using `UpperTheory.V.KT.good L N`. Establish `hqc : ∀ (y : NZ L N) (k : HS L N), qc L N y k = q k (y : Lat L N)` using `fun y k => by`. Simplify using `[qc, ev_apply]`. Establish `hpoly : ∀ h : HR L N, h ∈ ConeExtensionAcyclic.poly (qr L N) → (h : HS L N) ∈ ConeExtensionAcyclic.poly (qc L N)` using `fun h hh y => by`.

Use `hh y` as an intermediate fact. Rewrite `this` using `[qr_apply]`. Rewrite using `[hqc]`. Conclude with `this`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h hh`. Take `⟨S, hS, hev⟩` from `G.locFin _ (hpoly h hh)`. Use `⟨S, hS, ?_⟩` and prove the remaining obligations. Use `(continuous_subtype_val.tendsto h).eventually hev` as an intermediate fact. Use `filter_upwards [this] with h' hh' y hy`.

Rewrite using `[qr_apply, ← hqc]`. Conclude with `hh' y hy`. Take `⟨k, hk⟩` from `G.nonempty`. Take `⟨k', hk', -⟩` from `hRP L N σ hσ k`. Establish `hinv` using `(hRI L N σ hσ).1`.

Use `⟨k', fun y => ?_⟩` and prove the remaining obligations. Establish `hne : sLat σ (y : Lat L N) ≠ 0`. Introduce `h0`. Apply `y.2` to reduce the goal to its premises. Use function extensionality and compare the values at `a`.

Use `congrFun h0 a` as an intermediate fact. Simplify using `only [sLat, Pi.zero_apply] at this`. Use `show (y : Lat L N) a = 0`. Rewrite using `[← hinv ((y : Lat L N) a), this, map_zero]`. Establish `h1` using `hk y`.

Establish `h2` using `hk ⟨_, hne⟩`. Rewrite `h1`, `h2` using `[hqc]`. Rewrite using `[qr_apply, hk']`. Establish `h2' : 1 ≤ q k (sLat σ (y : Lat L N))` using `h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `G.closed.preimage continuous_subtype_val`. Introduce `c hc k hk`. Conclude with `G.smul_mem c hc _ hk`. Introduce `h hh`. Conclude with `G.sub (hpoly h hh)`.

Take `⟨x, hx⟩` from `G.pos`. Use `⟨x.comp (HR L N).subtypeL, fun k hk hk0 => ?_⟩` and prove the remaining obligations. Conclude with `hx _ hk (fun h => hk0 (Subtype.ext h))`.
-/
theorem UpperTheory.good_real_form_of_real_part_of_real_involution :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe := by
  intro hRP hRI L _ _ _ N σ hσ
  have G := UpperTheory.V.KT.good L N
  have hqc : ∀ (y : NZ L N) (k : HS L N), qc L N y k = q k (y : Lat L N) := fun y k => by
    simp [qc, ev_apply]
  have hpoly : ∀ h : HR L N, h ∈ ConeExtensionAcyclic.poly (qr L N) → (h : HS L N) ∈ ConeExtensionAcyclic.poly (qc L N) :=
    fun h hh y => by
      have := hh y
      rw [qr_apply] at this
      rw [hqc]
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨S, hS, hev⟩ := G.locFin _ (hpoly h hh)
    refine ⟨S, hS, ?_⟩
    have := (continuous_subtype_val.tendsto h).eventually hev
    filter_upwards [this] with h' hh' y hy
    rw [qr_apply, ← hqc]
    exact hh' y hy
  · obtain ⟨k, hk⟩ := G.nonempty
    obtain ⟨k', hk', -⟩ := hRP L N σ hσ k
    have hinv := (hRI L N σ hσ).1
    refine ⟨k', fun y => ?_⟩
    have hne : sLat σ (y : Lat L N) ≠ 0 := by
      intro h0
      apply y.2
      funext a
      have := congrFun h0 a
      simp only [sLat, Pi.zero_apply] at this
      show (y : Lat L N) a = 0
      rw [← hinv ((y : Lat L N) a), this, map_zero]
    have h1 := hk y
    have h2 := hk ⟨_, hne⟩
    rw [hqc] at h1 h2
    rw [qr_apply, hk']
    have h2' : 1 ≤ q k (sLat σ (y : Lat L N)) := h2
    linarith
  · exact G.closed.preimage continuous_subtype_val
  · intro c hc k hk
    exact G.smul_mem c hc _ hk
  · intro h hh
    exact G.sub (hpoly h hh)
  · obtain ⟨x, hx⟩ := G.pos
    refine ⟨x.comp (HR L N).subtypeL, fun k hk hk0 => ?_⟩
    exact hx _ hk (fun h => hk0 (Subtype.ext h))
