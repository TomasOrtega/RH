import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

open Module

namespace GlobalTheory.CommutingHecke

/- English proof (translation)
Use `haveI := Fintype.ofFinite ι`. Set `Y : Finset ι → Submodule ℂ V` to `fun s => sInf {Y | E ≤ Y ∧ ∀ c ∈ s, ∀ g, ∀ v ∈ Y, a c g v ∈ Y}`. Establish `hEY : ∀ s, E ≤ Y s` using `fun s => le_sInf fun _ h => h.1`. Establish `hYst : ∀ s, ∀ c ∈ s, ∀ g, ∀ v ∈ Y s, a c g v ∈ Y s`. Introduce `s c hc g v hv`.

Simplify using `only [Y, Submodule.mem_sInf] at hv ⊢`. Conclude with `fun p hp => hp.2 c hc g v (hv p hp)`. Establish `hind : ∀ s, v ∈ Y s → v ∈ E`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Introduce `h`. Establish `: Y ∅ ≤ E` using `sInf_le ⟨le_rfl, by simp⟩`. Conclude with `this h`. Consider the case `insert c s hc ih`.

Introduce `h`. Apply `ih` to reduce the goal to its premises. Set `Z : Submodule ℂ V` to `⨅ g, (Y s).comap (e c * a c g)`. Establish `hZ : ∀ w, w ∈ Z ↔ ∀ g, e c (a c g w) ∈ Y s`. Introduce `w`.

Simplify using `[Z, Submodule.mem_iInf]`. Establish `hle : Y (insert c s) ≤ Z`. Use `sInf_le ⟨fun w hw => (hZ w).2 fun g => hEY s (hst c g w hw), ?_⟩` and prove the remaining obligations. Introduce `c' hc' g w hw`. Rewrite `hw`, the goal using `[hZ]`.

Introduce `g'`. Break down `Finset.mem_insert.1 hc' with rfl | hc'` into its components or cases. Use `hw (g' * g)` as an intermediate fact. Rewrite `this` using `[map_mul, Module.End.mul_apply]`. Then use the resulting hypothesis. Establish `hne : c ≠ c'` using `fun h => hc (h ▸ hc')`.

Establish `h1 : a c g' (a c' g w) = a c' g (a c g' w)` using `LinearMap.congr_fun (haa c c' hne g' g).eq w`. Establish `h2 : e c (a c' g (a c g' w)) = a c' g (e c (a c g' w))` using `LinearMap.congr_fun (hea c c' hne g).eq _`. Rewrite using `[h1, h2]`. Conclude with `hYst s c' hc' g _ (hw g')`. Use `(hZ v).1 (hle h) 1` as an intermediate fact.

Rewrite `this` using `[map_one, Module.End.one_apply, hv]`. Then use the resulting hypothesis. Apply `hind Finset.univ` to reduce the goal to its premises. Break down `hirr (Y Finset.univ) (fun c => hYst _ c (Finset.mem_univ c)) with h | h` into its components or cases. Conclude with `absurd (le_bot_iff.1 (h ▸ hEY _)) hE`. Rewrite using `[h]`.

Discharge the goal by the elementary cases of `trivial`.
-/
theorem fixed_mem_of_stable {ι : Type} [Finite ι] {H : ι → Type} [∀ c, Monoid (H c)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (E : Submodule ℂ V) (hE : E ≠ ⊥) (hst : ∀ c g, ∀ v ∈ E, e c (a c g v) ∈ E)
    (v : V) (hv : ∀ c, e c v = v) : v ∈ E := by
  classical
  haveI := Fintype.ofFinite ι
  let Y : Finset ι → Submodule ℂ V := fun s =>
    sInf {Y | E ≤ Y ∧ ∀ c ∈ s, ∀ g, ∀ v ∈ Y, a c g v ∈ Y}
  have hEY : ∀ s, E ≤ Y s := fun s => le_sInf fun _ h => h.1
  have hYst : ∀ s, ∀ c ∈ s, ∀ g, ∀ v ∈ Y s, a c g v ∈ Y s := by
    intro s c hc g v hv
    simp only [Y, Submodule.mem_sInf] at hv ⊢
    exact fun p hp => hp.2 c hc g v (hv p hp)
  have hind : ∀ s, v ∈ Y s → v ∈ E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      have : Y ∅ ≤ E := sInf_le ⟨le_rfl, by simp⟩
      exact this h
    | insert c s hc ih =>
      intro h
      apply ih
      let Z : Submodule ℂ V := ⨅ g, (Y s).comap (e c * a c g)
      have hZ : ∀ w, w ∈ Z ↔ ∀ g, e c (a c g w) ∈ Y s := by
        intro w
        simp [Z, Submodule.mem_iInf]
      have hle : Y (insert c s) ≤ Z := by
        refine sInf_le ⟨fun w hw => (hZ w).2 fun g => hEY s (hst c g w hw), ?_⟩
        intro c' hc' g w hw
        rw [hZ] at hw ⊢
        intro g'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · have := hw (g' * g)
          rwa [map_mul, Module.End.mul_apply] at this
        · have hne : c ≠ c' := fun h => hc (h ▸ hc')
          have h1 : a c g' (a c' g w) = a c' g (a c g' w) :=
            LinearMap.congr_fun (haa c c' hne g' g).eq w
          have h2 : e c (a c' g (a c g' w)) = a c' g (e c (a c g' w)) :=
            LinearMap.congr_fun (hea c c' hne g).eq _
          rw [h1, h2]
          exact hYst s c' hc' g _ (hw g')
      have := (hZ v).1 (hle h) 1
      rwa [map_one, Module.End.one_apply, hv] at this
  apply hind Finset.univ
  rcases hirr (Y Finset.univ) (fun c => hYst _ c (Finset.mem_univ c)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hEY _)) hE
  · rw [h]; trivial

/- English proof (translation)
Set `W0 : Submodule ℂ V` to `⨅ c, LinearMap.eqLocus (e c) LinearMap.id`. Establish `hW0 : ∀ v, v ∈ W0 ↔ ∀ c, e c v = v`. Introduce `v`. Simplify using `[W0, Submodule.mem_iInf]`. Establish `hpres : ∀ c g, ∀ v ∈ W0, e c (a c g v) ∈ W0`.

Introduce `c g v hv`. Rewrite `hv`, the goal using `[hW0]`. Introduce `c'`. Distinguish the cases in `h : c' = c`. Substitute `h` using the available equality.

Conclude with `LinearMap.congr_fun (hee c') _`. Establish `h1 : e c' (e c (a c g v)) = e c (e c' (a c g v))` using `LinearMap.congr_fun (hec c' c h).eq _`. Establish `h2 : e c' (a c g v) = a c g (e c' v)` using `LinearMap.congr_fun (hea c' c h g).eq _`. Rewrite using `[h1, h2, hv]`. Establish `hcomm : ∀ c g c' h, ∀ v ∈ W0, e c (a c g (e c' (a c' h v))) = e c' (a c' h (e c (a c g v)))`.

Introduce `c g c' h v hv`. Rewrite `hv` using `[hW0]`. Distinguish the cases in `hc : c = c'`. Substitute `hc` using the available equality. Use `LinearMap.congr_fun (hhk c g h) v` as an intermediate fact.

Simplify `this` using `only [Module.End.mul_apply, hv]`. Establish `: Commute (e c * a c g) (e c' * a c' h)` using `Commute.mul_left ((hec c c' hc).mul_right (hea c c' hc h)) ((hea c' c (Ne.symm hc) g).symm.mul_right (haa c c' hc g h))`. Conclude with `LinearMap.congr_fun this.eq v`. Establish `hWle : W ≤ W0` using `fun v hv => (hW0 v).2 (hW v hv)`. Use `le_trans (Submodule.finrank_mono hWle) ?_` and prove the remaining obligations.

Distinguish the cases in `hbot : W0 = ⊥`. Rewrite using `[hbot]`. Simplify using the standard rewrite rules. Use `haveI : Nontrivial W0 := Submodule.nontrivial_iff_ne_bot.2 hbot`. Establish `hscal : ∀ c g, ∃ μ : ℂ, ∀ v ∈ W0, e c (a c g v) = μ • v`.

Introduce `c g`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue ((e c * a c g).restrict (p := W0) (q := W0) (hpres c g))`. Take `⟨w, hw⟩` from `hμ.exists_hasEigenvector`. Establish `hw1 : e c (a c g w) = μ • (w : V)` using `congrArg Subtype.val hw.apply_eq_smul`. Use `⟨μ, fun v hv => ?_⟩` and prove the remaining obligations.

Use `fixed_mem_of_stable a e hea haa hirr (W0 ⊓ Module.End.eigenspace (e c * a c g) μ) ?_ ?_ v ((hW0 v).1 hv)` as an intermediate fact. Conclude with `Module.End.mem_eigenspace_iff.1 this.2`. Rewrite using `[Submodule.ne_bot_iff]`. Conclude with `⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩`. Introduce `c' h u hu`.

Use `⟨hpres c' h u hu.1, Module.End.mem_eigenspace_iff.2 ?_⟩` and prove the remaining obligations. Establish `hu2 : e c (a c g u) = μ • u` using `Module.End.mem_eigenspace_iff.1 hu.2`. Rewrite using `[Module.End.mul_apply, hcomm c g c' h u hu.1, hu2, map_smul, map_smul]`. Take `⟨w, hw, hw0⟩` from `(Submodule.ne_bot_iff _).1 hbot`. Establish `hle : W0 ≤ ℂ ∙ w`.

Introduce `v hv`. Use `fixed_mem_of_stable a e hea haa hirr (ℂ ∙ w) (by simpa using hw0) ?_ v ((hW0 v).1 hv)` and prove the remaining obligations. Introduce `c g u hu`. Take `⟨μ, hμ⟩` from `hscal c g`. Rewrite using `[hμ u ((Submodule.span_singleton_le_iff_mem _ _).2 hw hu)]`.

Conclude with `Submodule.smul_mem _ _ hu`. Conclude with `le_trans (Submodule.finrank_mono hle) (finrank_span_singleton hw0).le`.
-/
theorem finrank_fixed_le_one (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hee : ∀ c, e c * e c = e c)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (hec : ∀ c c', c ≠ c' → Commute (e c) (e c'))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hhk : ∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c)
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (W : Submodule ℂ V) (hW : ∀ v ∈ W, ∀ c, e c v = v) : finrank ℂ W ≤ 1 := by
  classical
  let W0 : Submodule ℂ V := ⨅ c, LinearMap.eqLocus (e c) LinearMap.id
  have hW0 : ∀ v, v ∈ W0 ↔ ∀ c, e c v = v := by
    intro v
    simp [W0, Submodule.mem_iInf]
  have hpres : ∀ c g, ∀ v ∈ W0, e c (a c g v) ∈ W0 := by
    intro c g v hv
    rw [hW0] at hv ⊢
    intro c'
    by_cases h : c' = c
    · subst h
      exact LinearMap.congr_fun (hee c') _
    · have h1 : e c' (e c (a c g v)) = e c (e c' (a c g v)) :=
        LinearMap.congr_fun (hec c' c h).eq _
      have h2 : e c' (a c g v) = a c g (e c' v) := LinearMap.congr_fun (hea c' c h g).eq _
      rw [h1, h2, hv]
  have hcomm : ∀ c g c' h, ∀ v ∈ W0,
      e c (a c g (e c' (a c' h v))) = e c' (a c' h (e c (a c g v))) := by
    intro c g c' h v hv
    rw [hW0] at hv
    by_cases hc : c = c'
    · subst hc
      have := LinearMap.congr_fun (hhk c g h) v
      simpa only [Module.End.mul_apply, hv] using this
    · have : Commute (e c * a c g) (e c' * a c' h) :=
        Commute.mul_left ((hec c c' hc).mul_right (hea c c' hc h))
          ((hea c' c (Ne.symm hc) g).symm.mul_right (haa c c' hc g h))
      exact LinearMap.congr_fun this.eq v
  have hWle : W ≤ W0 := fun v hv => (hW0 v).2 (hW v hv)
  refine le_trans (Submodule.finrank_mono hWle) ?_
  by_cases hbot : W0 = ⊥
  · rw [hbot]; simp
  haveI : Nontrivial W0 := Submodule.nontrivial_iff_ne_bot.2 hbot
  have hscal : ∀ c g, ∃ μ : ℂ, ∀ v ∈ W0, e c (a c g v) = μ • v := by
    intro c g
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
      ((e c * a c g).restrict (p := W0) (q := W0) (hpres c g))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : e c (a c g w) = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨μ, fun v hv => ?_⟩
    have := fixed_mem_of_stable a e hea haa hirr (W0 ⊓ Module.End.eigenspace (e c * a c g) μ)
      ?_ ?_ v ((hW0 v).1 hv)
    · exact Module.End.mem_eigenspace_iff.1 this.2
    · rw [Submodule.ne_bot_iff]
      exact ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩
    · intro c' h u hu
      refine ⟨hpres c' h u hu.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hu2 : e c (a c g u) = μ • u := Module.End.mem_eigenspace_iff.1 hu.2
      rw [Module.End.mul_apply, hcomm c g c' h u hu.1, hu2, map_smul, map_smul]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hle : W0 ≤ ℂ ∙ w := by
    intro v hv
    refine fixed_mem_of_stable a e hea haa hirr (ℂ ∙ w) (by simpa using hw0) ?_ v ((hW0 v).1 hv)
    intro c g u hu
    obtain ⟨μ, hμ⟩ := hscal c g
    rw [hμ u ((Submodule.span_singleton_le_iff_mem _ _).2 hw hu)]
    exact Submodule.smul_mem _ _ hu
  exact le_trans (Submodule.finrank_mono hle) (finrank_span_singleton hw0).le

end GlobalTheory.CommutingHecke
