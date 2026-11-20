import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T hfit _ c' h K R _ _ Q ψ hψ hsep`. Take `⟨hrange, -, -, -, hres, hloc⟩` from `P1.towerGal D T`. Use `haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h`. Establish `hlev` using `P1.levEps K.V`. Use `⟨hlev.2.2.1, fun v i j hij => ?_⟩` and prove the remaining obligations.

Take `⟨s, ⟨hsI, hscyc, hsr⟩, hne⟩` from `hsep (K.e v) i j hij`. Establish `hsL : s ∈ T.GalL` using `hfit.1.unr _ hsI`. Rewrite `hsL` using `[← hrange]`. Take `⟨g', rfl⟩` from `hsL`. Establish `hgD : g' ∈ (Dec (K.s.A (show W.Vl l T.L from v).1) : Subgroup (G T.L Ω))`.

Rewrite using `[K.hA v]`. Conclude with `Ine_le_Dec _ (((hloc _ g').2).1 hsI)`. Establish `hr : D.rbar (resQ T.L g') = 1` using `by rw [← (hres g').1]; exact hsr`. Establish `hk : ∀ k, residue c'.O (inc h ↑(chi D T.pr k (resQ T.L g'))) = 1`. Introduce `k`.

Establish `e` using `congrArg (fun M => M (lab T.pr k) (lab T.pr k)) hr`. Simplify using `[Raw.rbar, Raw.r0, mapRep, diagRep] at e`. Rewrite using `[← ResidueField.map_residue]`. Simplify using `[chi, e]`. Use `⟨⟨g', hgD⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show K.V.pr g' ∈ K.V.frame.G'`. Rewrite using `[(hlev.2.1 g'), ← (hres g').2.1]`. Conclude with `hscyc`. Establish `hc : K.r.chib i (K.V.pr g') = K.r.chib j (K.V.pr g')`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[K.chib, K.chib, map_mul, map_mul, hk, hk]`. Conclude with `(K.psib v i ⟨g', hgD⟩).trans (hc.trans (K.psib v j ⟨g', hgD⟩).symm)`. Introduce `heq`. Apply `hne` to reduce the goal to its premises. Establish `e1` using `hψ v i ⟨g', hgD⟩`.

Establish `e2` using `hψ v j ⟨g', hgD⟩`. Rewrite `e1` using `[heq]`. Establish `hu : IsUnit (algebraMap c'.O R ↑(K.κ g'))` using `(K.κ g').isUnit.map _`. Conclude with `hu.mul_left_cancel (e1.symm.trans e2)`.
-/
theorem UpperTheory.V.Ws.P1.condA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ), K.IsPsi ψ Q → (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, Q.ψ v i s ≠ Q.ψ v j s) →
          Nonempty K.V.frame.Vl ∧ ∀ v i j, i ≠ j → ∃ g, K.V.frame.φ v g ∈ K.V.frame.G' ∧ K.r.psib v i g = K.r.psib v j g ∧ ψ v i g ≠ ψ v j g := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K R _ _ Q ψ hψ hsep
  obtain ⟨hrange, -, -, -, hres, hloc⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hlev := P1.levEps K.V
  refine ⟨hlev.2.2.1, fun v i j hij => ?_⟩
  obtain ⟨s, ⟨hsI, hscyc, hsr⟩, hne⟩ := hsep (K.e v) i j hij
  have hsL : s ∈ T.GalL := hfit.1.unr _ hsI
  rw [← hrange] at hsL
  obtain ⟨g', rfl⟩ := hsL
  have hgD : g' ∈ (Dec (K.s.A (show W.Vl l T.L from v).1) : Subgroup (G T.L Ω)) := by
    rw [K.hA v]
    exact Ine_le_Dec _ (((hloc _ g').2).1 hsI)
  have hr : D.rbar (resQ T.L g') = 1 := by rw [← (hres g').1]; exact hsr
  have hk : ∀ k, residue c'.O (inc h ↑(chi D T.pr k (resQ T.L g'))) = 1 := by
    intro k
    have e := congrArg (fun M => M (lab T.pr k) (lab T.pr k)) hr
    simp [Raw.rbar, Raw.r0, mapRep, diagRep] at e
    rw [← ResidueField.map_residue]
    simp [chi, e]
  refine ⟨⟨g', hgD⟩, ?_, ?_, ?_⟩
  · show K.V.pr g' ∈ K.V.frame.G'
    rw [(hlev.2.1 g'), ← (hres g').2.1]
    exact hscyc
  · have hc : K.r.chib i (K.V.pr g') = K.r.chib j (K.V.pr g') := by
      apply Units.ext
      rw [K.chib, K.chib, map_mul, map_mul, hk, hk]
    exact (K.psib v i ⟨g', hgD⟩).trans (hc.trans (K.psib v j ⟨g', hgD⟩).symm)
  · intro heq
    apply hne
    have e1 := hψ v i ⟨g', hgD⟩
    have e2 := hψ v j ⟨g', hgD⟩
    rw [heq] at e1
    have hu : IsUnit (algebraMap c'.O R ↑(K.κ g')) := (K.κ g').isUnit.map _
    exact hu.mul_left_cancel (e1.symm.trans e2)
