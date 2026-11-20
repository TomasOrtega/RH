import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PureK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
/- English proof (translation)
Introduce `hP K _ _ _ n hn`. Take `⟨c, A, hcard⟩` from `cardK hP K n hn`. Use `⟨c, A, fun m hm _ H hH M hM p w hp hw hpM hpd => ?_⟩` and prove the remaining obligations. Establish `hwM : (M : 𝓞 K) ∉ w.asIdeal` using `natCast_notMem_of_not_dvd hp hw hpM`. Set `Wd` to `{v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}`.

Set `sys : CuspSub K n → Wd → Multiset ℂ` to `fun π v => if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0`. Establish `hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B`. Introduce `π v B hB`. Establish `h : ∃ B, (CG.mk π).HasSat v.1 B` using `⟨B, hB⟩`. Simplify using `only [sys, dif_pos h]`.

Rewrite using `[h.choose_spec.unique hB]`. Establish `hsat : ∀ π ∈ SigK K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B` using `fun π hπ v => satK hP K n M π hπ.2.2 v.1 v.2`. Take `⟨D, hD, cl, hcl, hβ⟩` from `exists_eigData (SigK K m M) (fun π π' => π.Iso π') sys (fun π hπ π' _ h => funext fun v => by`. Take `⟨B, hB⟩` from `hsat π hπ v`. Rewrite using `[hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])`.

Use the proof step `(c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)`. Use the proof step `(fun σ π hπ => by`. Take `⟨π', hπ', h⟩` from `conjK hP K n hn m hm M hM σ π hπ`. Use `⟨π', hπ', fun v => ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `hsat π hπ v`.

Take `⟨B', hB', e⟩` from `h v.1 B hB`. Rewrite using `[hsys π v B hB, hsys π' v B' hB', e])`. Use the proof step `⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := 1 - n)`. Use the proof step `(fun π hπ => by`. Take `⟨B, hB⟩` from `hsat π hπ ⟨w, hwM⟩`.

Rewrite using `[hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]`. Use the proof step `simp)`. Use the proof step `(fun π hπ b hb => by`. Take `⟨B, hB⟩` from `hsat π hπ ⟨w, hwM⟩`. Rewrite `hb` using `[hsys π _ B hB]`.

Rewrite using `[pureK hP K n hn m hm M π hπ w B hB b hb]`. Use `congr 1`. Use `push_cast`. Use the proof step `ring)`. Use the proof step `(fun π hπ => by`.

Take `⟨B, hB⟩` from `hsat π hπ ⟨w, hwM⟩`. Rewrite using `[hsys π _ B hB]`. Conclude with `intK hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)`. Use `⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩` and prove the remaining obligations. Establish `hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmK ι M m r}, ∃ π : ↥(SigK K m M), IsSSRep r.1 ∧ ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v)`.

Introduce `r`. Take `⟨π, h1, h2, h3⟩` from `r.2.aut`. Take `⟨hπ, hF⟩` from `levelK hP K n hn m hm M hM l hl2 Ω ι r.1 π r.2.level h1 h2 h3`. Use `⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `hsat π hπ v`.

Rewrite using `[hsys π v B hB]`. Conclude with `hF v.1 hv B hB`. Use `choose f hss hf using hform`. Use `⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩` and prove the remaining obligations. Use `isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_ filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega), eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl` and prove the remaining obligations.

Use `⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩` and prove the remaining obligations. Rewrite using `[hcl _ _ h]`. Conclude with `hf r' ⟨v, hvM⟩ hvl`. Rewrite using `[hβ]`. Use `hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)` and prove the remaining obligations.

Conclude with `((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm`.
-/
theorem UpperTheory.V.Af.countK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.CountK := by
  intro hP K _ _ _ n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardK hP K n hn
  refine ⟨c, A, fun m hm _ H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigK K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigK K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjK hP K n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := 1 - n)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (fun π hπ b hb => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB] at hb
      rw [pureK hP K n hn m hm M π hπ w B hB b hb]
      congr 1
      push_cast
      ring)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intK hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmK ι M m r}, ∃ π : ↥(SigK K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := levelK hP K n hn m hm M hM l hl2 Ω ι r.1 π r.2.level h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm
