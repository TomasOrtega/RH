import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Generic

variable {A B M : Type} [CommRing A] [Ring B] [Algebra A B] [AddCommGroup M] [Module B M]

private def idealSub (B M : Type) {A : Type} [CommRing A] [Ring B] [Algebra A B] [AddCommGroup M] [Module B M]
    (𝔞 : Ideal A) : Submodule B M :=
  Submodule.span B {z | ∃ c ∈ 𝔞, ∃ z' : M, z = algebraMap A B c • z'}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨c, hc, z, rfl⟩`.
-/
private theorem smul_mem_idealSub {𝔞 : Ideal A} {c : A} (hc : c ∈ 𝔞) (z : M) :
    algebraMap A B c • z ∈ idealSub B M 𝔞 :=
  Submodule.subset_span ⟨c, hc, z, rfl⟩

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, z', rfl⟩` from `hx`. Take `⟨e, he⟩` from `hb (f z')`. Conclude with `⟨c * e, 𝔞.mul_mem_right e hc, by rw [map_smul, ← he, smul_eq_mul, map_mul]⟩`.

Consider the case `zero => exact ⟨0, 𝔞.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d₁, h₁, e₁⟩` from `hx`. Take `⟨d₂, h₂, e₂⟩` from `hy`. Conclude with `⟨d₁ + d₂, 𝔞.add_mem h₁ h₂, by rw [map_add, e₁, e₂, map_add]⟩`.

Consider the case `smul b x _ hx`. Take `⟨d, hd, e⟩` from `hx`. Take `⟨a, rfl⟩` from `hb b`. Conclude with `⟨a * d, 𝔞.mul_mem_left a hd, by rw [map_smul, e, smul_eq_mul, map_mul]⟩`.
-/
private theorem functional_mem (hb : Function.Surjective (algebraMap A B)) (f : M →ₗ[B] B) (𝔞 : Ideal A) {w : M}
    (hw : w ∈ idealSub B M 𝔞) : ∃ d ∈ 𝔞, f w = algebraMap A B d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    obtain ⟨e, he⟩ := hb (f z')
    exact ⟨c * e, 𝔞.mul_mem_right e hc, by rw [map_smul, ← he, smul_eq_mul, map_mul]⟩
  | zero => exact ⟨0, 𝔞.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁, e₁⟩ := hx
    obtain ⟨d₂, h₂, e₂⟩ := hy
    exact ⟨d₁ + d₂, 𝔞.add_mem h₁ h₂, by rw [map_add, e₁, e₂, map_add]⟩
  | smul b x _ hx =>
    obtain ⟨d, hd, e⟩ := hx
    obtain ⟨a, rfl⟩ := hb b
    exact ⟨a * d, 𝔞.mul_mem_left a hd, by rw [map_smul, e, smul_eq_mul, map_mul]⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def'.mp ‹Module.Projective B M›`. Establish `key : ∀ m : M, ∃ d ∈ J, s z m = algebraMap A B d`. Introduce `m`. Set `f : M →ₗ[B] B` to `Finsupp.lapply m ∘ₗ s`. Take `⟨e, he⟩` from `hb.2 (f z)`.

Use `⟨e, ?_, he.symm⟩` and prove the remaining obligations. Establish `hle : I * Ideal.span {e} ≤ I * J`. Rewrite using `[Ideal.mul_le]`. Introduce `r hr t ht`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.mp ht`.

Take `⟨d, hd, hde⟩` from `functional_mem hb.2 f (I * J) (h (r * u) (I.mul_mem_right u hr))`. Establish `hrd : algebraMap A B (r * u * e) = algebraMap A B d`. Rewrite using `[← hde, map_smul, smul_eq_mul, ← he, ← map_mul]`. Rewrite using `[← _root_.mul_assoc, hb.1 hrd]`. Conclude with `hd`.

Establish `hdvd : I * J ∣ I * Ideal.span {e}` using `Ideal.dvd_iff_le.mpr hle`. Rewrite `hdvd` using `[mul_dvd_mul_iff_left hI]`. Conclude with `(Ideal.dvd_iff_le.mp hdvd) (Ideal.mem_span_singleton_self e)`. Establish `hz : z = Finsupp.linearCombination B id (s z)` using `(LinearMap.congr_fun hs z).symm`. Rewrite using `[hz, Finsupp.linearCombination_apply, Finsupp.sum]`.

Use `Submodule.sum_mem _ (fun m _ => ?_)` and prove the remaining obligations. Take `⟨d, hd, e⟩` from `key m`. Rewrite using `[e]`. Conclude with `smul_mem_idealSub hd m`.
-/
private theorem mem_of_mul_mem [IsDedekindDomain A] [Module.Projective B M]
    (hb : Function.Bijective (algebraMap A B)) (I J : Ideal A) (hI : I ≠ ⊥) (z : M)
    (h : ∀ c ∈ I, algebraMap A B c • z ∈ idealSub B M (I * J)) : z ∈ idealSub B M J := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective B M›
  have key : ∀ m : M, ∃ d ∈ J, s z m = algebraMap A B d := by
    intro m
    let f : M →ₗ[B] B := Finsupp.lapply m ∘ₗ s
    obtain ⟨e, he⟩ := hb.2 (f z)
    refine ⟨e, ?_, he.symm⟩
    have hle : I * Ideal.span {e} ≤ I * J := by
      rw [Ideal.mul_le]
      intro r hr t ht
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ht
      obtain ⟨d, hd, hde⟩ := functional_mem hb.2 f (I * J) (h (r * u) (I.mul_mem_right u hr))
      have hrd : algebraMap A B (r * u * e) = algebraMap A B d := by
        rw [← hde, map_smul, smul_eq_mul, ← he, ← map_mul]
      rw [← _root_.mul_assoc, hb.1 hrd]
      exact hd
    have hdvd : I * J ∣ I * Ideal.span {e} := Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_left hI] at hdvd
    exact (Ideal.dvd_iff_le.mp hdvd) (Ideal.mem_span_singleton_self e)
  have hz : z = Finsupp.linearCombination B id (s z) := (LinearMap.congr_fun hs z).symm
  rw [hz, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  obtain ⟨d, hd, e⟩ := key m
  rw [e]
  exact smul_mem_idealSub hd m

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, z', rfl⟩` from `hx`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.mp hc`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hu`.

Use `⟨algebraMap A B a • z', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← map_mul, mul_comm ε a, map_add, add_smul, add_sub_cancel_left]`. Conclude with `smul_mem_idealSub hv z'`. Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_zero, sub_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Take `⟨y₁, h₁⟩` from `hx`. Take `⟨y₂, h₂⟩` from `hy`.

Use `⟨y₁ + y₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, add_sub_add_comm]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul b x _ hx`. Take `⟨y, h⟩` from `hx`.

Use `⟨b • y, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ b h` as an intermediate fact. Rewrite `this` using `[smul_sub, smul_smul, ← Algebra.commutes, ← smul_smul]`. Then use the resulting hypothesis.
-/
private theorem exists_sub_mem {ε : A} {𝔟 : Ideal A} {z : M}
    (hz : z ∈ idealSub B M (Ideal.span {ε} ⊔ 𝔟)) :
    ∃ y, z - algebraMap A B ε • y ∈ idealSub B M 𝔟 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨algebraMap A B a • z', ?_⟩
    rw [smul_smul, ← map_mul, mul_comm ε a, map_add, add_smul, add_sub_cancel_left]
    exact smul_mem_idealSub hv z'
  | zero =>
    refine ⟨0, ?_⟩
    rw [smul_zero, sub_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁⟩ := hx
    obtain ⟨y₂, h₂⟩ := hy
    refine ⟨y₁ + y₂, ?_⟩
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂
  | smul b x _ hx =>
    obtain ⟨y, h⟩ := hx
    refine ⟨b • y, ?_⟩
    have := Submodule.smul_mem _ b h
    rwa [smul_sub, smul_smul, ← Algebra.commutes, ← smul_smul] at this

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, z', rfl⟩` from `hx`. Rewrite using `[smul_smul, ← map_mul]`. Establish `hm : ε * c ∈ 𝔟₁`.

Rewrite using `[← h]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self ε)) hc`. Conclude with `smul_mem_idealSub hm z'`. Consider the case `zero`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul b x _ hx`.

Rewrite using `[smul_smul, Algebra.commutes, ← smul_smul]`. Conclude with `Submodule.smul_mem _ b hx`.
-/
private theorem smul_mem_of_mul {ε : A} {𝔟₁ 𝔟₂ : Ideal A} (h : (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁) {x : M}
    (hx : x ∈ idealSub B M 𝔟₂) : algebraMap A B ε • x ∈ idealSub B M 𝔟₁ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [smul_smul, ← map_mul]
    have hm : ε * c ∈ 𝔟₁ := by
      rw [← h]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self ε)) hc
    exact smul_mem_idealSub hm z'
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    rw [smul_smul, Algebra.commutes, ← smul_smul]
    exact Submodule.smul_mem _ b hx

/- English proof (translation)
Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.mp hc`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hu`. Rewrite using `[map_add, add_smul, map_mul, ← smul_smul]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (smul_mem_idealSub hv y)`.
-/
private theorem smul_mem_of_eps {ε c : A} {𝔟 : Ideal A} {y : M} (hc : c ∈ Ideal.span {ε} ⊔ 𝔟)
    (hy : algebraMap A B ε • y ∈ idealSub B M 𝔟) : algebraMap A B c • y ∈ idealSub B M 𝔟 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  rw [map_add, add_smul, map_mul, ← smul_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (smul_mem_idealSub hv y)

end Generic

/- English proof (translation)
Unfold `wSub idealSub`. Rewrite using `[pow_one]`.
-/
private theorem wSub_one {q : ℕ} [Fact q.Prime] (D : Datum q) (𝔟 : Ideal (𝓞 D.F)) :
    wSub D 𝔟 1 = idealSub D.O D.La 𝔟 := by
  unfold wSub idealSub
  rw [pow_one]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Unfold `LevDown`. Introduce `q _ D hm R _ b N S s o 𝔟₁ 𝔟₂ ε h𝔟 hmul l hl`. Take `⟨hbij, hproj, -⟩` from `mOne q D hm`. Use `haveI := hproj`. Establish `hw₁ : wSub D 𝔟₁ 1 = idealSub D.O D.La 𝔟₁` using `wSub_one D 𝔟₁`.

Establish `hw₂ : wSub D 𝔟₂ 1 = idealSub D.O D.La 𝔟₂` using `wSub_one D 𝔟₂`. Establish `hI : Ideal.span {ε} ⊔ 𝔟₁ ≠ ⊥` using `fun h0 => h𝔟 (eq_bot_iff.mpr (h0 ▸ le_sup_right))`. Establish `h𝔟₂ : 𝔟₂ ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `h𝔟 (by rw [← hmul, Ideal.mul_bot])`.

Establish `h21 : ∀ c, c ∈ 𝔟₁ ^ 1 → c ∈ 𝔟₂ ^ 1`. Introduce `c hc`. Rewrite `hc`, the goal using `[pow_one]`. Rewrite `hc` using `[← hmul]`. Conclude with `Ideal.mul_le_right (I := Ideal.span {ε} ⊔ 𝔟₁) (J := 𝔟₂) hc`.

Establish `down : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ε • y ∈ idealSub D.O D.La 𝔟₁ → y ∈ idealSub D.O D.La 𝔟₂`. Introduce `y hy`. Use `mem_of_mul_mem hbij _ 𝔟₂ hI y (fun c hc => ?_)` and prove the remaining obligations. Rewrite using `[hmul]`. Conclude with `smul_mem_of_eps hc hy`.

Take `⟨hadd, hact, hker, hpt⟩` from `id hl`. Unfold `IsEtLev`. Use `beta_reduce`. Use `⟨fun x y => by rw [smul_add, hadd], fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[smul_smul, Algebra.commutes, ← smul_smul, hact]`.

Apply `hker` to reduce the goal to its premises. Rewrite using `[hw₁]`. Rewrite `hx` using `[hw₂]`. Conclude with `smul_mem_of_mul hmul hx`. Rewrite using `[hw₂]`.

Conclude with `down y (by rw [← hw₁]; exact (hpt k x).1 _ hy)`. Take `⟨hpt1, hpt2⟩` from `hpt k x`. Take `⟨y, hy⟩` from `hpt2 g (fun c hc => hg c (h21 c hc))`. Establish `hyI : y ∈ idealSub D.O D.La (Ideal.span {ε} ⊔ 𝔟₁)`. Use `mem_of_mul_mem hbij 𝔟₂ _ h𝔟₂ y (fun c hc => ?_)` and prove the remaining obligations.

Rewrite using `[mul_comm, hmul, ← hw₁]`. Apply `hpt1` to reduce the goal to its premises. Rewrite using `[hact, ← Category.assoc, hy]`. Conclude with `hg c (by rw [pow_one]; exact hc)`. Take `⟨y', hy'⟩` from `exists_sub_mem hyI`.

Use `⟨y', ?_⟩` and prove the remaining obligations. Establish `e` using `hl.congr (show y - algebraMap (𝓞 D.F) D.O ε • y' ∈ wSub D 𝔟₁ 1 by rw [hw₁]; exact hy')`. Rewrite using `[← hy, e]`.
-/
theorem levDown : LevDown := by
  unfold LevDown
  intro q _ D hm R _ b N S s o 𝔟₁ 𝔟₂ ε h𝔟 hmul l hl
  obtain ⟨hbij, hproj, -⟩ := mOne q D hm
  haveI := hproj
  have hw₁ : wSub D 𝔟₁ 1 = idealSub D.O D.La 𝔟₁ := wSub_one D 𝔟₁
  have hw₂ : wSub D 𝔟₂ 1 = idealSub D.O D.La 𝔟₂ := wSub_one D 𝔟₂
  have hI : Ideal.span {ε} ⊔ 𝔟₁ ≠ ⊥ := fun h0 => h𝔟 (eq_bot_iff.mpr (h0 ▸ le_sup_right))
  have h𝔟₂ : 𝔟₂ ≠ ⊥ := by
    rintro rfl
    exact h𝔟 (by rw [← hmul, Ideal.mul_bot])
  have h21 : ∀ c, c ∈ 𝔟₁ ^ 1 → c ∈ 𝔟₂ ^ 1 := by
    intro c hc
    rw [pow_one] at hc ⊢
    rw [← hmul] at hc
    exact Ideal.mul_le_right (I := Ideal.span {ε} ⊔ 𝔟₁) (J := 𝔟₂) hc
  have down : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ε • y ∈ idealSub D.O D.La 𝔟₁ →
      y ∈ idealSub D.O D.La 𝔟₂ := by
    intro y hy
    refine mem_of_mul_mem hbij _ 𝔟₂ hI y (fun c hc => ?_)
    rw [hmul]
    exact smul_mem_of_eps hc hy
  obtain ⟨hadd, hact, hker, hpt⟩ := id hl
  unfold IsEtLev
  beta_reduce
  refine ⟨fun x y => by rw [smul_add, hadd], fun c x => ?_, fun x hx => ?_,
    fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · rw [smul_smul, Algebra.commutes, ← smul_smul, hact]
  · apply hker
    rw [hw₁]
    rw [hw₂] at hx
    exact smul_mem_of_mul hmul hx
  · rw [hw₂]
    exact down y (by rw [← hw₁]; exact (hpt k x).1 _ hy)
  · obtain ⟨hpt1, hpt2⟩ := hpt k x
    obtain ⟨y, hy⟩ := hpt2 g (fun c hc => hg c (h21 c hc))
    have hyI : y ∈ idealSub D.O D.La (Ideal.span {ε} ⊔ 𝔟₁) := by
      refine mem_of_mul_mem hbij 𝔟₂ _ h𝔟₂ y (fun c hc => ?_)
      rw [mul_comm, hmul, ← hw₁]
      apply hpt1
      rw [hact, ← Category.assoc, hy]
      exact hg c (by rw [pow_one]; exact hc)
    obtain ⟨y', hy'⟩ := exists_sub_mem hyI
    refine ⟨y', ?_⟩
    have e := hl.congr (show y - algebraMap (𝓞 D.F) D.O ε • y' ∈ wSub D 𝔟₁ 1 by rw [hw₁]; exact hy')
    rw [← hy, e]

end UpperTheory.Gal.FiniteEtaleModels.O
