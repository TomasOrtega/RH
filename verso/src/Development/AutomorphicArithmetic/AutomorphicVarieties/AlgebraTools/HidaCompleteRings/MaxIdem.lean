import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CofinalCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IdemLift

open IsLocalRing

/- English proof (translation)
Introduce `Λ T _ _ _ _ _ _ _ m hm`. Take `⟨hfin, -, n, h1, h2⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax Λ T`. Use `set I' := Ideal.map (algebraMap Λ T) (maximalIdeal Λ) with hI'`. Establish `key : ∀ (k : ℕ) (y : T), y ∈ ((maximalIdeal Λ) ^ k • (⊤ : Submodule Λ T)) ↔ y ∈ (I' ^ k • (⊤ : Submodule T T))`. Introduce `k y`.

Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, Ideal.smul_eq_mul, Ideal.mul_top]`. Use `haveI hΛ : IsAdicComplete (maximalIdeal Λ) T := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl Λ T (maximalIdeal Λ)`. Establish `hT : IsAdicComplete I' T` using `{ haus' := fun y hy => IsHausdorff.haus' (I := maximalIdeal Λ) y fun k => SModEq.sub_mem.mpr ((key k _).mpr (SModEq.sub_mem.mp (hy k))) prec' := fun f hf => by`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := maximalIdeal Λ) f fun hmn => SModEq.sub_mem.mpr ((key _ _).mpr (SModEq.sub_mem.mp (hf hmn)))`. Conclude with `⟨L, fun k => SModEq.sub_mem.mpr ((key k _).mp (SModEq.sub_mem.mp (hL k)))⟩ }`.

Use `haveI hJ : IsAdicComplete (⊥ : Ideal T).jacobson T := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T I' _ n h1 h2 hT`. Use `haveI := hfin`. Use `haveI := Fintype.ofFinite (MaximalSpectrum T)`. Use `set s := Finset.univ.filter (fun p : MaximalSpectrum T => p.asIdeal ≠ m) with hs`. Use `set m'' := s.inf (fun p => p.asIdeal) with hm''`.

Establish `hnot : ¬ m'' ≤ m`. Introduce `h`. Take `⟨p, hp, hpm⟩` from `(Ideal.IsPrime.inf_le' hm.isPrime).mp h`. Conclude with `(Finset.mem_filter.mp hp).2 (p.isMaximal.eq_of_le hm.ne_top hpm)`. Establish `htop : m ⊔ m'' = ⊤` using `hm.out.2 _ (lt_of_le_of_ne le_sup_left fun h => hnot (h ▸ le_sup_right))`.

Establish `h1mem : (1 : T) ∈ m ⊔ m''` using `htop ▸ Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1mem`. Establish `hbp : ∀ p : Ideal T, p.IsMaximal → p ≠ m → b ∈ p`. Introduce `p hp hpm`. Establish `hle : m'' ≤ p` using `Finset.inf_le (f := fun p : MaximalSpectrum T => p.asIdeal) (b := ⟨p, hp⟩) (by simp [s, hpm])`.

Conclude with `hle hb`. Establish `memJ : ∀ y : T, (∀ p : Ideal T, p.IsMaximal → y ∈ p) → y ∈ (⊥ : Ideal T).jacobson` using `fun y hy => Ideal.mem_sInf.mpr fun p hp => hy p hp.2`. Establish `hJm : ∀ y : T, y ∈ (⊥ : Ideal T).jacobson → ∀ p : Ideal T, p.IsMaximal → y ∈ p` using `fun y hy p hp => Ideal.mem_sInf.mp hy ⟨bot_le, hp⟩`. Establish `hxx : b * b - b ∈ (⊥ : Ideal T).jacobson`. Establish `e1 : b * b - b = -(b * a)`.

Establish `ha' : a = 1 - b` using `by rw [← hab]; ring`. Rewrite using `[ha']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `memJ _ fun p hp => p.neg_mem ?_` and prove the remaining obligations.

Distinguish the cases in `hpm : p = m`. Rewrite using `[hpm]`. Conclude with `m.mul_mem_left _ ha`. Conclude with `p.mul_mem_right _ (hbp p hp hpm)`. Take `⟨e, he, hex⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idemLift T _ b hxx`.

Use `⟨e, he, fun hem => ?_, fun p hp hpm => ?_⟩` and prove the remaining obligations. Apply `hm.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h3 : e - b ∈ m` using `hJm _ hex m hm`. Establish `h4 : (1 : T) = e - (e - b) + a` using `by rw [← hab]; ring`.

Rewrite using `[h4]`. Conclude with `m.add_mem (m.sub_mem hem h3) ha`. Establish `h3 : e - b ∈ p` using `hJm _ hex p hp`. Establish `h4 : e = (e - b) + b` using `by ring`. Rewrite using `[h4]`.

Conclude with `p.add_mem h3 (hbp p hp hpm)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.maxIdem :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (m : Ideal T), m.IsMaximal → ∃ e : T, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal T, m'.IsMaximal → m' ≠ m → e ∈ m' := by
  intro Λ T _ _ _ _ _ _ _ m hm
  classical
  obtain ⟨hfin, -, n, h1, h2⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax Λ T
  set I' := Ideal.map (algebraMap Λ T) (maximalIdeal Λ) with hI'
  have key : ∀ (k : ℕ) (y : T), y ∈ ((maximalIdeal Λ) ^ k • (⊤ : Submodule Λ T)) ↔
      y ∈ (I' ^ k • (⊤ : Submodule T T)) := by
    intro k y
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, Ideal.smul_eq_mul,
      Ideal.mul_top]
  haveI hΛ : IsAdicComplete (maximalIdeal Λ) T := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl Λ T (maximalIdeal Λ)
  have hT : IsAdicComplete I' T :=
    { haus' := fun y hy => IsHausdorff.haus' (I := maximalIdeal Λ) y fun k =>
        SModEq.sub_mem.mpr ((key k _).mpr (SModEq.sub_mem.mp (hy k)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal Λ) f fun hmn =>
          SModEq.sub_mem.mpr ((key _ _).mpr (SModEq.sub_mem.mp (hf hmn)))
        exact ⟨L, fun k => SModEq.sub_mem.mpr ((key k _).mp (SModEq.sub_mem.mp (hL k)))⟩ }
  haveI hJ : IsAdicComplete (⊥ : Ideal T).jacobson T :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T I' _ n h1 h2 hT
  haveI := hfin
  haveI := Fintype.ofFinite (MaximalSpectrum T)
  set s := Finset.univ.filter (fun p : MaximalSpectrum T => p.asIdeal ≠ m) with hs
  set m'' := s.inf (fun p => p.asIdeal) with hm''
  have hnot : ¬ m'' ≤ m := by
    intro h
    obtain ⟨p, hp, hpm⟩ := (Ideal.IsPrime.inf_le' hm.isPrime).mp h
    exact (Finset.mem_filter.mp hp).2 (p.isMaximal.eq_of_le hm.ne_top hpm)
  have htop : m ⊔ m'' = ⊤ :=
    hm.out.2 _ (lt_of_le_of_ne le_sup_left fun h => hnot (h ▸ le_sup_right))
  have h1mem : (1 : T) ∈ m ⊔ m'' := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  have hbp : ∀ p : Ideal T, p.IsMaximal → p ≠ m → b ∈ p := by
    intro p hp hpm
    have hle : m'' ≤ p :=
      Finset.inf_le (f := fun p : MaximalSpectrum T => p.asIdeal) (b := ⟨p, hp⟩) (by simp [s, hpm])
    exact hle hb
  have memJ : ∀ y : T, (∀ p : Ideal T, p.IsMaximal → y ∈ p) → y ∈ (⊥ : Ideal T).jacobson :=
    fun y hy => Ideal.mem_sInf.mpr fun p hp => hy p hp.2
  have hJm : ∀ y : T, y ∈ (⊥ : Ideal T).jacobson → ∀ p : Ideal T, p.IsMaximal → y ∈ p :=
    fun y hy p hp => Ideal.mem_sInf.mp hy ⟨bot_le, hp⟩
  have hxx : b * b - b ∈ (⊥ : Ideal T).jacobson := by
    have e1 : b * b - b = -(b * a) := by
      have ha' : a = 1 - b := by rw [← hab]; ring
      rw [ha']
      ring
    rw [e1]
    refine memJ _ fun p hp => p.neg_mem ?_
    by_cases hpm : p = m
    · rw [hpm]
      exact m.mul_mem_left _ ha
    · exact p.mul_mem_right _ (hbp p hp hpm)
  obtain ⟨e, he, hex⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idemLift T _ b hxx
  refine ⟨e, he, fun hem => ?_, fun p hp hpm => ?_⟩
  · apply hm.ne_top
    rw [Ideal.eq_top_iff_one]
    have h3 : e - b ∈ m := hJm _ hex m hm
    have h4 : (1 : T) = e - (e - b) + a := by rw [← hab]; ring
    rw [h4]
    exact m.add_mem (m.sub_mem hem h3) ha
  · have h3 : e - b ∈ p := hJm _ hex p hp
    have h4 : e = (e - b) + b := by ring
    rw [h4]
    exact p.add_mem h3 (hbp p hp hpm)
