import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

open ReciprocityTheory.AnForm.M

/- English proof (translation)
Set `E` to `ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ`. Establish `hg : DifferentiableOn ℂ (u ∘ E.symm) (E.symm ⁻¹' t)` using `hu.comp E.symm.differentiableOn (fun z hz => hz)`. Establish `hopen : IsOpen (E.symm ⁻¹' t)` using `ht.preimage E.symm.continuous`. Establish `hmem : E v ∈ E.symm ⁻¹' t` using `by simpa using hv`. Establish `ha : AnalyticAt ℂ (u ∘ E.symm) (E v)` using `hg.analyticAt (hopen.mem_nhds hmem)`.

Establish `hE : AnalyticAt ℂ (E : (Fin 1 → ℂ) → ℂ) v` using `(E : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt v`. Use `ha.comp hE` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules.
-/
theorem analyticAt_of_differentiableOn_fin_one {u : (Fin 1 → ℂ) → ℂ} {t : Set (Fin 1 → ℂ)}
    (ht : IsOpen t) (hu : DifferentiableOn ℂ u t) {v : Fin 1 → ℂ} (hv : v ∈ t) :
    AnalyticAt ℂ u v := by
  let E := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hg : DifferentiableOn ℂ (u ∘ E.symm) (E.symm ⁻¹' t) :=
    hu.comp E.symm.differentiableOn (fun z hz => hz)
  have hopen : IsOpen (E.symm ⁻¹' t) := ht.preimage E.symm.continuous
  have hmem : E v ∈ E.symm ⁻¹' t := by simpa using hv
  have ha : AnalyticAt ℂ (u ∘ E.symm) (E v) := hg.analyticAt (hopen.mem_nhds hmem)
  have hE : AnalyticAt ℂ (E : (Fin 1 → ℂ) → ℂ) v := (E : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt v
  have := ha.comp hE
  convert this using 1
  funext w
  simp

end GlobalTheory

namespace GlobalTheory

open Classical in

/- English proof (translation)
Distinguish the cases in `hxr : x ∈ Set.range P`. Take `⟨k0, hk0⟩` from `hxr`. Rewrite using `[Finset.prod_eq_single k0]`. Rewrite using `[if_pos hk0, hm k0 hk0]`. Introduce `k _ hk`.

Establish `: P k ≠ x` using `fun h' => hk (hP (h'.trans hk0.symm))`. Simplify using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[hn0 hxr]`. Establish `: ∀ k, P k ≠ x` using `fun k h' => hxr ⟨k, h'⟩`.

Simplify using `[this]`.
-/
theorem prod_ite_pow_of_injective {X : Type} {r : ℕ} {P : Fin r → X} (hP : Function.Injective P)
    (x : X) (a : ℂ) (m : Fin r → ℕ) (n : ℕ) (hm : ∀ j, P j = x → n = m j)
    (hn0 : x ∉ Set.range P → n = 0) :
    (∏ k, if P k = x then a ^ m k else 1) = a ^ n := by
  classical
  by_cases hxr : x ∈ Set.range P
  · obtain ⟨k0, hk0⟩ := hxr
    rw [Finset.prod_eq_single k0]
    · rw [if_pos hk0, hm k0 hk0]
    · intro k _ hk
      have : P k ≠ x := fun h' => hk (hP (h'.trans hk0.symm))
      simp [this]
    · simp
  · rw [hn0 hxr]
    have : ∀ k, P k ≠ x := fun k h' => hxr ⟨k, h'⟩
    simp [this]

end GlobalTheory

namespace GlobalTheory

open ReciprocityTheory.AnForm.M

/- English proof (translation)
Introduce `X _ _ A L s r m P hP h x`. Take `⟨ψ, hψ, hx, n, u, hud, hu0, hform, hm, hn0⟩` from `h x`. Establish `hev : ∀ᶠ v in 𝓝 (ψ x), (DifferentiableAt ℂ u v ∧ u v ≠ 0 ∧ s x (ψ.symm v) = u v * (v 0 - ψ x 0) ^ n) ∧ v ∈ ψ.target`. Establish `hcont : ∀ᶠ v in 𝓝 (ψ x), u v ≠ 0` using `(hud.self_of_nhds.continuousAt).eventually_ne hu0`. Conclude with `((hud.and (hcont.and hform)).and (ψ.open_target.mem_nhds (ψ.map_source hx)))`.

Take `⟨t0, ht0, ht0o, hxt0⟩` from `eventually_nhds_iff.1 hev`. Use `set t := t0 with ht_def`. Establish `htd : DifferentiableOn ℂ u t` using `fun v hv => (ht0 v hv).1.1.differentiableWithinAt`. Use `set F : Set X := Set.range P \ {x} with hF`. Establish `hFc : IsClosed F` using `((Set.finite_range P).diff).isClosed`.

Use `set V : Set X := (ψ.source ∩ ψ ⁻¹' t) ∩ L.U x ∩ Fᶜ with hV`. Establish `hVo : IsOpen V` using `((ψ.isOpen_inter_preimage ht0o).inter (L.isOpen_U x)).inter hFc.isOpen_compl`. Use `set ψ' : OpenPartialHomeomorph X (Fin 1 → ℂ) := (ψ.restrOpen V hVo).transHomeomorph (pa_aff 1 one_ne_zero (ψ x)) with hψ'`. Establish `hsrc : ψ'.source = ψ.source ∩ V`. Simplify using `[ψ', OpenPartialHomeomorph.restrOpen_source]`.

Establish `hψ'app : ∀ y, ψ' y = ψ y - ψ x`. Introduce `y`. Simplify using `[ψ', pa_aff]`. Establish `hmemV : ∀ {y}, y ∈ ψ'.source → y ∈ ψ.source ∧ ψ y ∈ t ∧ y ∈ L.U x ∧ y ∉ F`. Introduce `y hy`.

Rewrite `hy` using `[hsrc]`. Conclude with `⟨hy.1, hy.2.1.1.2, hy.2.1.2, hy.2.2⟩`. Use `⟨ψ', pa_compat_aff A _ (pa_compat_restr A ψ hψ V hVo) 1 one_ne_zero (ψ x), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsrc]`. Use `⟨hx, ⟨⟨hx, hxt0⟩, L.mem_U x⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[F]`. Introduce `y hy`. Conclude with `(hmemV hy).2.2.1`. Use `⟨fun k => if P k = x then some 0 else none, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k k' i hk hk'`.

Distinguish the cases in `h1 : P k = x`. Distinguish the cases in `h2 : P k' = x`. Conclude with `hP (h1.trans h2.symm)`. Simplify using `[h2] at hk'`. Simplify using `[h1] at hk`.

Introduce `k`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, hy⟩`.

Use `⟨hy, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : P k = x`. Use `⟨0, by simp [h1], ?_⟩` and prove the remaining obligations. Rewrite using `[hψ'app, h1]`. Simplify using the standard rewrite rules.

It suffices to derive a contradiction. Conclude with `(hmemV hy).2.2.2 ⟨⟨k, rfl⟩, h1⟩`. Introduce and unpack `⟨hy, i, hi, hz⟩`. Distinguish the cases in `h1 : P k = x`. Use `⟨?_, hy⟩` and prove the remaining obligations.

Rewrite using `[h1]`. Establish `hy0 : ψ y 0 = ψ x 0`. Rewrite `hz` using `[Fin.fin_one_eq_zero i, hψ'app]`. Simplify `hz` using `[sub_eq_zero]`. Establish `hyx : ψ y = ψ x`.

Use function extensionality and compare the values at `i'`. Rewrite using `[Fin.fin_one_eq_zero i']`. Conclude with `hy0`. Conclude with `ψ.injOn (hmemV hy).1 hx hyx`. Simplify using `[h1] at hi`.

Use `⟨fun y => u (ψ y), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j z hz`. Establish `hzs : (A.chart j).symm z ∈ ψ'.source` using `hz.2`. Establish `hz'` using `hmemV hzs`. Establish `h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) z` using `(hψ j).1 z ⟨hz.1, hz'.1⟩`.

Establish `h2 : AnalyticAt ℂ u (ψ ((A.chart j).symm z))` using `analyticAt_of_differentiableOn_fin_one ht0o htd hz'.2.1`. Establish `h3 : AnalyticAt ℂ (u ∘ (ψ ∘ (A.chart j).symm)) z` using `AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) h2 h1`. Conclude with `h3`. Introduce `y hy`. Conclude with `(ht0 _ (hmemV hy).2.1).1.2.1`.

Introduce `y hy`. Take `⟨hys, hyt, -, -⟩` from `hmemV hy`. Establish `hf` using `(ht0 _ hyt).1.2.2`. Rewrite `hf` using `[ψ.left_inv hys]`. Rewrite using `[hf]`.

Use `congr 1`. Rewrite using `[← prod_ite_pow_of_injective hP x (ψ y 0 - ψ x 0) m n hm hn0]`. Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h1 : P k = x`. Simplify using `[h1, hψ'app]`.

Simplify using `[h1]`.
-/
theorem isSNC_of_local_power : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas 1 X) (L : ReciprocityTheory.AnForm.M.LocPot X) (s : X → X → ℂ)
    (r : ℕ) (m : Fin r → ℕ) (P : Fin r → X), Function.Injective P →
    (∀ x : X, ∃ ψ : OpenPartialHomeomorph X (Fin 1 → ℂ), ReciprocityTheory.AnForm.M.IsCompatChart A ψ ∧
      x ∈ ψ.source ∧ ∃ (n : ℕ) (u : (Fin 1 → ℂ) → ℂ), (∀ᶠ v in 𝓝 (ψ x), DifferentiableAt ℂ u v) ∧
      u (ψ x) ≠ 0 ∧ (∀ᶠ v in 𝓝 (ψ x), s x (ψ.symm v) = u v * (v 0 - ψ x 0) ^ n) ∧
      (∀ j, P j = x → n = m j) ∧ (x ∉ Set.range P → n = 0)) →
    ReciprocityTheory.AnForm.M.IsSNC A L s m (fun j => {P j}) := by
  intro X _ _ A L s r m P hP h x
  classical
  obtain ⟨ψ, hψ, hx, n, u, hud, hu0, hform, hm, hn0⟩ := h x

  have hev : ∀ᶠ v in 𝓝 (ψ x), (DifferentiableAt ℂ u v ∧ u v ≠ 0 ∧
      s x (ψ.symm v) = u v * (v 0 - ψ x 0) ^ n) ∧ v ∈ ψ.target := by
    have hcont : ∀ᶠ v in 𝓝 (ψ x), u v ≠ 0 :=
      (hud.self_of_nhds.continuousAt).eventually_ne hu0
    exact ((hud.and (hcont.and hform)).and (ψ.open_target.mem_nhds (ψ.map_source hx)))
  obtain ⟨t0, ht0, ht0o, hxt0⟩ := eventually_nhds_iff.1 hev
  set t := t0 with ht_def
  have htd : DifferentiableOn ℂ u t := fun v hv => (ht0 v hv).1.1.differentiableWithinAt

  set F : Set X := Set.range P \ {x} with hF
  have hFc : IsClosed F := ((Set.finite_range P).diff).isClosed
  set V : Set X := (ψ.source ∩ ψ ⁻¹' t) ∩ L.U x ∩ Fᶜ with hV
  have hVo : IsOpen V :=
    ((ψ.isOpen_inter_preimage ht0o).inter (L.isOpen_U x)).inter hFc.isOpen_compl
  set ψ' : OpenPartialHomeomorph X (Fin 1 → ℂ) :=
    (ψ.restrOpen V hVo).transHomeomorph (pa_aff 1 one_ne_zero (ψ x)) with hψ'
  have hsrc : ψ'.source = ψ.source ∩ V := by
    simp [ψ', OpenPartialHomeomorph.restrOpen_source]
  have hψ'app : ∀ y, ψ' y = ψ y - ψ x := by
    intro y
    simp [ψ', pa_aff]
  have hmemV : ∀ {y}, y ∈ ψ'.source → y ∈ ψ.source ∧ ψ y ∈ t ∧ y ∈ L.U x ∧ y ∉ F := by
    intro y hy
    rw [hsrc] at hy
    exact ⟨hy.1, hy.2.1.1.2, hy.2.1.2, hy.2.2⟩
  refine ⟨ψ', pa_compat_aff A _ (pa_compat_restr A ψ hψ V hVo) 1 one_ne_zero (ψ x), ?_, ?_, ?_⟩
  · rw [hsrc]
    refine ⟨hx, ⟨⟨hx, hxt0⟩, L.mem_U x⟩, ?_⟩
    simp [F]
  · intro y hy
    exact (hmemV hy).2.2.1
  refine ⟨fun k => if P k = x then some 0 else none, ?_, ?_, ?_⟩
  · intro k k' i hk hk'
    by_cases h1 : P k = x
    · by_cases h2 : P k' = x
      · exact hP (h1.trans h2.symm)
      · simp [h2] at hk'
    · simp [h1] at hk
  · intro k
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, hy⟩
      refine ⟨hy, ?_⟩
      by_cases h1 : P k = x
      · refine ⟨0, by simp [h1], ?_⟩
        rw [hψ'app, h1]
        simp
      · exfalso
        exact (hmemV hy).2.2.2 ⟨⟨k, rfl⟩, h1⟩
    · rintro ⟨hy, i, hi, hz⟩
      by_cases h1 : P k = x
      · refine ⟨?_, hy⟩
        rw [h1]
        have hy0 : ψ y 0 = ψ x 0 := by
          rw [Fin.fin_one_eq_zero i, hψ'app] at hz
          simpa [sub_eq_zero] using hz
        have hyx : ψ y = ψ x := by
          funext i'
          rw [Fin.fin_one_eq_zero i']
          exact hy0
        exact ψ.injOn (hmemV hy).1 hx hyx
      · simp [h1] at hi
  · refine ⟨fun y => u (ψ y), ?_, ?_, ?_⟩
    · intro j z hz
      have hzs : (A.chart j).symm z ∈ ψ'.source := hz.2
      have hz' := hmemV hzs
      have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) z := (hψ j).1 z ⟨hz.1, hz'.1⟩
      have h2 : AnalyticAt ℂ u (ψ ((A.chart j).symm z)) :=
        analyticAt_of_differentiableOn_fin_one ht0o htd hz'.2.1
      have h3 : AnalyticAt ℂ (u ∘ (ψ ∘ (A.chart j).symm)) z :=
        AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) h2 h1
      exact h3
    · intro y hy
      exact (ht0 _ (hmemV hy).2.1).1.2.1
    · intro y hy
      obtain ⟨hys, hyt, -, -⟩ := hmemV hy
      have hf := (ht0 _ hyt).1.2.2
      rw [ψ.left_inv hys] at hf
      rw [hf]
      congr 1
      rw [← prod_ite_pow_of_injective hP x (ψ y 0 - ψ x 0) m n hm hn0]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      by_cases h1 : P k = x
      · simp [h1, hψ'app]
      · simp [h1]

end GlobalTheory
