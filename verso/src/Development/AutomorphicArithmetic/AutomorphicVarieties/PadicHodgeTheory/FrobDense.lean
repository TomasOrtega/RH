import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocRootsY
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Rewrite using `[← pow_mul, mul_comm, pow_mul, h, one_pow]`.
-/
private theorem fd_pow_root {K : Type*} [Field K] {m n : ℕ} {y : K} (h : y ^ m = 1) :
    (y ^ n) ^ m = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

/- English proof (translation)
Establish `hv : v.Prime` using `Fact.out`. Establish `key : ∀ {a b : Om v}, (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a) → (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g b = h b) → ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a ∧ g b = …`. Introduce and unpack `a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩`. Use `⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h fun y hy => ?_, hb g h fun y hy => ?_⟩⟩` and prove the remaining obligations. Conclude with `hgh y (by rw [pow_mul, hy, one_pow])`.

Conclude with `hgh y (by rw [mul_comm, pow_mul, hy, one_pow])`. Unfold `MaximalUnramifiedExtension at hx`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨m, -, hm, hx⟩` from `hx`.

Conclude with `⟨m, hm, fun g h hgh => hgh x hx⟩`. Consider the case `algebraMap x`. Conclude with `⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m, hm, h⟩` from `key hx hy`.

Conclude with `⟨m, hm, fun g k hgk => by rw [map_add, map_add, (h g k hgk).1, (h g k hgk).2]⟩`. Consider the case `inv x _ hx`. Take `⟨m, hm, h⟩` from `hx`. Conclude with `⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨m, hm, h⟩` from `key hx hy`. Conclude with `⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩`.
-/
private theorem fd_level {v : ℕ} [Fact v.Prime] {x : Om v} (hx : x ∈ MaximalUnramifiedExtension v) :
    ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g x = h x := by
  have hv : v.Prime := Fact.out
  have key : ∀ {a b : Om v},
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a) →
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g b = h b) →
      ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) →
        g a = h a ∧ g b = h b := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h fun y hy => ?_,
      hb g h fun y hy => ?_⟩⟩
    · exact hgh y (by rw [pow_mul, hy, one_pow])
    · exact hgh y (by rw [mul_comm, pow_mul, hy, one_pow])
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, hm, hx⟩ := hx
    exact ⟨m, hm, fun g h hgh => hgh x hx⟩
  | algebraMap x =>
    exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_add, map_add, (h g k hgk).1, (h g k hgk).2]⟩
  | inv x _ hx =>
    obtain ⟨m, hm, h⟩ := hx
    exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero _)`. Establish `h1 : σ y = y ^ v`. Establish `hn : ‖y‖ ^ m = 1` using `by rw [← norm_pow, hy, norm_one]`. Establish `hn'` using `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hn`. Conclude with `KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hy, map_one]) (fd_pow_root hy) (hσ y hn'.le)`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1, ← pow_mul, pow_succ']`.
-/
private theorem fd_frob {v : ℕ} [Fact v.Prime] {σ : GQ v} (hσ : IsFrob σ) {m : ℕ} (hm : ¬ v ∣ m)
    (j : ℕ) (y : Om v) (hy : y ^ m = 1) : (σ ^ j) y = y ^ v ^ j := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : σ y = y ^ v := by
    have hn : ‖y‖ ^ m = 1 := by rw [← norm_pow, hy, norm_one]
    have hn' := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hn
    exact KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hy, map_one])
      (fd_pow_root hy) (hσ y hn'.le)
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1, ← pow_mul, pow_succ']

/- English proof (translation)
Introduce `v _ σ hσ`. Set `H : ClosedSubgroup (GQ v)` to `⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩`. Establish `hH` using `InfiniteGalois.fixingSubgroup_fixedField H`. Establish `hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v))` using `Subgroup.le_topologicalClosure _`. Use `eq_top_iff.mpr fun g _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g ∈ (H : Subgroup (GQ v))`. Rewrite using `[← hH, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Establish `hxK : x ∈ MaximalUnramifiedExtension v`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v), IntermediateField.mem_fixedField_iff]`. Conclude with `fun f hf => hx f (hle (Subgroup.mem_sup_left hf))`. Take `⟨m, hm, h⟩` from `fd_level hxK`. Take `⟨j, hj⟩` from `KStar.IdealValuations.exists_pow_of_aut g hm`. Rewrite using `[h g (σ ^ j) fun y hy => by rw [hj y hy, fd_frob hσ hm j y hy]]`.

Conclude with `hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))`.
-/
theorem UpperTheory.V.Loc.frobDense :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), IsFrob σ → (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
  intro v _ σ hσ
  let H : ClosedSubgroup (GQ v) :=
    ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hH := InfiniteGalois.fixingSubgroup_fixedField H
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
  refine eq_top_iff.mpr fun g _ => ?_
  change g ∈ (H : Subgroup (GQ v))
  rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hxK : x ∈ MaximalUnramifiedExtension v := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v), IntermediateField.mem_fixedField_iff]
    exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
  obtain ⟨m, hm, h⟩ := fd_level hxK
  obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
  rw [h g (σ ^ j) fun y hy => by rw [hj y hy, fd_frob hσ hm j y hy]]
  exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
