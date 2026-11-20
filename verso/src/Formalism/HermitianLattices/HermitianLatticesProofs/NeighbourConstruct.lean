import Mathlib
import Formalism.HermitianLattices.NeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourBasic

noncomputable section

open nonZeroDivisors

namespace Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Unfold `invIdeal`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]`. Both sides reduce to the same expression.
-/
theorem neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`.

Consider the case `add y y' _ _ h1 h2`. Take `⟨a, ha, rfl⟩` from `h1`. Take `⟨b, hb, rfl⟩` from `h2`. Conclude with `⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩`. Consider the case `smul r y _ h1`.

Take `⟨a, ha, rfl⟩` from `h1`. Use `⟨r • a, Submodule.smul_mem _ r ha, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Introduce `hz`. Conclude with `Submodule.subset_span hz`.
-/
theorem neighbourConstruct_mem_span {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz

/- English proof (translation)
Unfold `neighbourCore`. Simplify using `only [Submodule.mem_inf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_map, Algebra.linearMap_apply]`.
-/
theorem neighbourConstruct_mem_core (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V)
    (x y : V) : y ∈ neighbourCore h P L x ↔
      y ∈ L ∧ ∃ t ∈ conjIdeal (K := K) P, algebraMap R K t = h x y := by
  unfold neighbourCore
  simp only [Submodule.mem_inf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.mem_map, Algebra.linearMap_apply]

end Gen

section DedekindLFunctions

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Establish `e` using `FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0`. Establish `e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) * (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1`. Rewrite using `[← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]`. Establish `h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) * (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)`. Rewrite using `[e2]`.

Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Establish `hne : (P : FractionalIdeal R⁰ K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hP0`. Use `(mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1` and prove the remaining obligations. Rewrite using `[FractionalIdeal.coe_coeIdeal]`. Conclude with `le_rfl`.

Introduce `a ha`. Rewrite using `[neighbourConstruct_mem_inv]`. Introduce `p hp`. Use `(FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p) (FractionalIdeal.mem_coeIdeal_of_mem _ hp)` as an intermediate fact. Rewrite using `[mul_comm]`.

Conclude with `(FractionalIdeal.mem_one_iff _).mp this`.
-/
theorem neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this

/- English proof (translation)
Establish `h1` using `neighbourConstruct_one_mem (K := K) P hP0`. Establish `: ((1 : K) • x) ∈ P • L`. Use `Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_` and prove the remaining obligations. Introduce `m hm n hn`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hm`.

Rewrite using `[Algebra.linearMap_apply, mul_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem_smul hp (H n hn)`. Introduce `a b ha hb`. Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ ha hb`.

Simplify using `using this`.
-/
theorem neighbourConstruct_key (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this

end DedekindLFunctions

section Avoid

variable {R : Type*} [CommRing R]

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push Not at H`. Establish `hsub : (A : Set R) ⊆ (B : Set R) ∪ C`. Introduce `s hs`. Distinguish the cases in `hsB : s ∈ B`.

Conclude with `Or.inl hsB`. Conclude with `Or.inr (H s hs hsB)`. Break down `Ideal.subset_union.mp hsub with h1 | h1` into its components or cases. Conclude with `hAB (hA.eq_of_le hB.ne_top h1)`. Conclude with `hAC (hA.eq_of_le hC.ne_top h1)`.
-/
theorem neighbourConstruct_avoid {A B C : Ideal R} (hA : A.IsMaximal) (hB : B.IsMaximal)
    (hC : C.IsMaximal) (hAB : A ≠ B) (hAC : A ≠ C) : ∃ s ∈ A, s ∉ B ∧ s ∉ C := by
  by_contra H
  push Not at H
  have hsub : (A : Set R) ⊆ (B : Set R) ∪ C := by
    intro s hs
    by_cases hsB : s ∈ B
    · exact Or.inl hsB
    · exact Or.inr (H s hs hsB)
  rcases Ideal.subset_union.mp hsub with h1 | h1
  · exact hAB (hA.eq_of_le hB.ne_top h1)
  · exact hAC (hA.eq_of_le hC.ne_top h1)

end Avoid

section Main

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective R K`. Use `set σ := locBasic_sigma hinj hstar with hσdef`. Establish `hσ : ∀ r : R, algebraMap R K (σ r) = star (algebraMap R K r)` using `fun r => locBasic_sigma_spec hinj hstar r`. Establish `hσσ : ∀ r : R, σ (σ r) = r` using `fun r => hinj (by rw [hσ, hσ, star_star])`. Establish `hconj : ∀ I : Ideal R, conjIdeal (K` using `K) (conjIdeal (K := K) I) = I := by`.

Introduce `I`. Rewrite using `[locBasic_conj_eq hinj hstar, locBasic_conj_eq hinj hstar]`. Use extensionality with `r`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hσσ]`. Establish `hcmax : ∀ I : Ideal R, I.IsMaximal → (conjIdeal (K` using `K) I).IsMaximal := by`.

Introduce `I hI`. Rewrite using `[locBasic_conj_eq hinj hstar]`. Conclude with `Ideal.comap_isMaximal_of_surjective _ (fun r => ⟨_, hσσ r⟩)`. Establish `hPc : (conjIdeal (K` using `K) P).IsMaximal := hcmax P hP`. Establish `hcmem : ∀ t : R, t ∈ conjIdeal (K` using `K) P ↔ σ t ∈ P := by`.

Introduce `t`. Rewrite using `[locBasic_conj_eq hinj hstar, Ideal.mem_comap]`. Establish `hone : ∀ k : K, k ∈ (1 : Submodule R K) ↔ k ∈ Set.range (algebraMap R K)` using `fun k => by rw [Submodule.mem_one]; rfl`. Establish `rmul : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) → a * b ∈ Set.range (algebraMap R K)`. Introduce and unpack `_ _ ⟨u, rfl⟩ ⟨v, rfl⟩`.

Conclude with `⟨u * v, map_mul _ _ _⟩`. Establish `radd : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) → a + b ∈ Set.range (algebraMap R K)`. Introduce and unpack `_ _ ⟨u, rfl⟩ ⟨v, rfl⟩`. Conclude with `⟨u + v, map_add _ _ _⟩`. Establish `rstar : ∀ a : K, a ∈ Set.range (algebraMap R K) → star a ∈ Set.range (algebraMap R K)`.

Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `hstar u`. Establish `hsl : ∀ (a : K) (u v : V), h (a • u) v = star a * h u v`. Introduce `a u v`. Rewrite using `[LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]`.

Establish `hsr : ∀ (a : K) (u v : V), h u (a • v) = a * h u v`. Introduce `a u v`. Rewrite using `[map_smul, smul_eq_mul]`. Establish `rs : ∀ (r : R) (u : V), r • u = algebraMap R K r • u` using `fun r u => (algebraMap_smul K r u).symm`. Establish `hsymm : ∀ u v : V, h v u = star (h u v)`.

Introduce `u v`. Rewrite using `[← hs.eq u v, starRingEnd_apply]`. Establish `memL : ∀ y : V, y ∈ L ↔ ∀ z ∈ L, h z y ∈ Set.range (algebraMap R K)`. Introduce `y`. Use `conv_lhs => rw [← hL]`.

Rewrite using `[dualBasic_mem_dual]`. Simplify using `only [hone]`. Establish `hLL : ∀ z ∈ L, ∀ y ∈ L, h z y ∈ Set.range (algebraMap R K)` using `fun z hz y hy => (memL y).mp hy z hz`. Establish `F2 : ∀ a ∈ invIdeal (K` using `K) P, ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := fun a ha => neighbourConstruct_mem_inv.mp ha`. Establish `F3 : ∀ a ∈ invIdeal (K` using `K) P, ∀ t ∈ conjIdeal (K := K) P, star a * algebraMap R K t ∈ Set.range (algebraMap R K) := by`.

Introduce `a ha t ht`. Use `rstar _ (F2 a ha (σ t) ((hcmem t).mp ht))` as an intermediate fact. Rewrite `this` using `[star_mul', hσ, star_star, mul_comm]`. Conclude with `this`. Take `⟨r₀, hr₀, hr₀x⟩` from `hxx`.

Establish `hr₀c : r₀ ∈ conjIdeal (K` using `K) P := Ideal.mul_le_right hr₀`. Establish `F4 : ∀ a ∈ invIdeal (K` using `K) P, ∀ b ∈ invIdeal (K := K) P, star a * b * h x x ∈ Set.range (algebraMap R K) := by`. Introduce `a ha b hb`. Rewrite using `[← hr₀x]`. Use `Submodule.mul_induction_on (C := fun r => star a * b * algebraMap R K r ∈ Set.range (algebraMap R K)) hr₀ ?_ ?_` and prove the remaining obligations.

Introduce `p hp q hq`. Establish `e : star a * b * algebraMap R K (p * q) = (algebraMap R K p * b) * (star a * algebraMap R K q)` using `by rw [map_mul]; ring`. Rewrite using `[e]`. Conclude with `rmul _ _ (F2 b hb p hp) (F3 a ha q hq)`. Introduce `u v hu hv`.

Rewrite using `[map_add, mul_add]`. Conclude with `radd _ _ hu hv`. Use `set Lx := neighbourCore h P L x with hLxdef`. Establish `memLx : ∀ y, y ∈ Lx ↔ y ∈ L ∧ ∃ t ∈ conjIdeal (K` using `K) P, algebraMap R K t = h x y := fun y => neighbourConstruct_mem_core h P L x y`. Establish `hLxL : Lx ≤ L` using `fun y hy => ((memLx y).mp hy).1`.

Establish `rx : ∀ r : R, r • x ∈ Lx`. Introduce `r`. Use `(memLx _).mpr ⟨L.smul_mem r hx, r * r₀, Ideal.mul_mem_left _ r hr₀c, ?_⟩` and prove the remaining obligations. Rewrite using `[rs, hsr, map_mul, hr₀x]`. Establish `sLx : ∀ s ∈ conjIdeal (K` using `K) P, ∀ l ∈ L, s • l ∈ Lx := by`.

Introduce `s hs l hl`. Take `⟨t, ht⟩` from `hLL x hx l hl`. Use `(memLx _).mpr ⟨L.smul_mem s hl, s * t, Ideal.mul_mem_right _ _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[rs, hsr, map_mul, ht]`. Use `set M := neighbourOf h P L x with hMdef`.

Establish `memM : ∀ z, z ∈ M ↔ ∃ a ∈ invIdeal (K` using `K) P, ∃ y ∈ Lx, z = a • x + y := by`. Introduce `z`. Rewrite using `[hMdef, neighbourOf, Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, y, hy, rfl⟩`.

Take `⟨a, ha, rfl⟩` from `neighbourConstruct_mem_span.mp hw`. Conclude with `⟨a, ha, y, hy, rfl⟩`. Introduce and unpack `⟨a, ha, y, hy, rfl⟩`. Conclude with `⟨a • x, neighbourConstruct_mem_span.mpr ⟨a, ha, rfl⟩, y, hy, rfl⟩`. Establish `hLxM : Lx ≤ M` using `fun y hy => (memM y).mpr ⟨0, Submodule.zero_mem _, y, hy, by simp⟩`.

Establish `hIxM : ∀ a ∈ invIdeal (K` using `K) P, a • x ∈ M := fun a ha => (memM _).mpr ⟨a, ha, 0, Submodule.zero_mem _, by simp⟩`. Establish `hD : ∀ a ∈ invIdeal (K` using `K) P, a • x ∈ L → a ∈ Set.range (algebraMap R K) := by`. Introduce `a ha hax`. Assume the negation of the conclusion as `hna`. Apply `hxP` to reduce the goal to its premises.

Use `neighbourConstruct_key (K := K) P hP0 L x ?_` and prove the remaining obligations. Introduce `c hc`. Take `⟨u, b, hub⟩` from `neighbourBasic_ded P hP c a (F2 c hc) (F2 a ha) hna`. Rewrite using `[hub, add_smul, mul_smul, ← rs, ← rs]`. Conclude with `L.add_mem (L.smul_mem u hx) (L.smul_mem b hax)`.

Take `⟨c', hc'I, hc'R⟩ : ∃ c' ∈ invIdeal (K` from `K) P, c' ∉ Set.range (algebraMap R K) := by`. Assume the negation of the conclusion as `H`. Use `push Not at H`. Apply `hxP` to reduce the goal to its premises. Use `neighbourConstruct_key (K := K) P hP0 L x ?_` and prove the remaining obligations.

Introduce `c hc`. Take `⟨u, hu⟩` from `H c hc`. Rewrite using `[← hu, ← rs]`. Conclude with `L.smul_mem u hx`. Establish `hdec : ∀ c ∈ invIdeal (K` using `K) P, ∃ u b : R, c = algebraMap R K u + algebraMap R K b * c' := fun c hc => neighbourBasic_ded P hP c c' (F2 c hc) (F2 c' hc'I) hc'R`.

Establish `hE : L ⊓ M = Lx`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Take `⟨hzL, hzM⟩` from `Submodule.mem_inf.mp hz`. Take `⟨a, ha, y, hy, rfl⟩` from `(memM z).mp hzM`.

Establish `hax : a • x ∈ L`. Use `L.sub_mem hzL (hLxL hy)` as an intermediate fact. Simplify using `using this`. Take `⟨u, rfl⟩` from `hD a ha hax`. Rewrite using `[← rs]`.

Conclude with `Lx.add_mem (rx u) hy`. Conclude with `le_inf hLxL hLxM`. Establish `hInt : IsIntegralLat h M`. Introduce `z hz w hw`. Rewrite using `[hone]`.

Take `⟨a, ha, y, hy, rfl⟩` from `(memM z).mp hz`. Take `⟨b, hb, y', hy', rfl⟩` from `(memM w).mp hw`. Take `⟨hyL, t, ht, hty⟩` from `(memLx y).mp hy`. Take `⟨hy'L, t', ht', hty'⟩` from `(memLx y').mp hy'`. Establish `e : h (a • x + y) (b • x + y') = star a * b * h x x + star a * h x y' + b * h y x + h y y'`.

Simplify using `only [map_add, LinearMap.add_apply, hsl, hsr]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hsymm x y, ← hty, ← hty', ← hσ]`. Use `radd _ _ (radd _ _ (radd _ _ (F4 a ha b hb) (F3 a ha t' ht')) ?_) (hLL y hyL y' hy'L)` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `F2 b hb (σ t) ((hcmem t).mp ht)`. Establish `eL : (L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K` using `K) P) := by`. Set `φ : V → R` to `fun v => if hv : h x v ∈ Set.range (algebraMap R K) then hv.choose else 0`. Establish `hφ : ∀ v ∈ L, algebraMap R K (φ v) = h x v`. Introduce `v hv`.

Simplify using `only [φ, dif_pos (hLL x hx v hv)]`. Conclude with `(hLL x hx v hv).choose_spec`. Set `g : L →ₗ[R] R` to `{ toFun := fun y => φ y.1 map_add' := fun y y' => hinj (by`. Rewrite using `[map_add, hφ _ (y + y').2, hφ _ y.2, hφ _ y'.2, Submodule.coe_add, map_add])`. Use the proof step `map_smul' := fun r y => hinj (by`.

Rewrite using `[hφ _ (r • y).2, RingHom.id_apply, smul_eq_mul, map_mul, hφ _ y.2, Submodule.coe_smul, rs, hsr]) }`. Set `f : L →ₗ[R] R ⧸ conjIdeal (K` to `K) P := (conjIdeal (K := K) P).mkQ ∘ₗ g`. Establish `hker : LinearMap.ker f = (L ⊓ M).comap L.subtype`. Use extensionality with `y`. Rewrite using `[LinearMap.mem_ker, hE, Submodule.mem_comap, Submodule.subtype_apply, memLx]`.

Use `show Submodule.Quotient.mk (φ y.1) = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨y.2, φ y, hy, hφ _ y.2⟩`.

Introduce and unpack `⟨_, t, ht, hty⟩`. Establish `: t = φ y` using `hinj (by rw [hty, hφ _ y.2])`. Rewrite using `[← this]`. Conclude with `ht`. Establish `hsurj : Function.Surjective f`.

Take `⟨y₀, hy₀, hy₀P⟩ : ∃ y₀ ∈ L, φ y₀ ∉ conjIdeal (K` from `K) P := by`. Assume the negation of the conclusion as `H`. Use `push Not at H`. Apply `hxP` to reduce the goal to its premises. Use `neighbourConstruct_key (K := K) P hP0 L x ?_` and prove the remaining obligations.

Introduce `a ha`. Rewrite using `[memL]`. Introduce `z hz`. Rewrite using `[hsr, hsymm x z, ← hφ z hz, ← hσ, mul_comm]`. Conclude with `F2 a ha _ ((hcmem _).mp (H z hz))`.

Take `⟨b, i, hi, hbi⟩` from `hPc.exists_inv hy₀P`. Introduce `w`. Take `⟨r, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Use `⟨(r * b) • ⟨y₀, hy₀⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (g ((r * b) • ⟨y₀, hy₀⟩)) = Submodule.Quotient.mk r`.

Rewrite using `[map_smul, Submodule.Quotient.eq, smul_eq_mul]`. Establish `e : r * b * g ⟨y₀, hy₀⟩ - r = -(r * i)` using `by show r * b * φ y₀ - r = _`. Take the linear combination `r * hbi`. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (Ideal.mul_mem_left _ r hi)`.

Conclude with `(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)`. Establish `hc'M : c' • x ∈ M` using `hIxM c' hc'I`. Establish `eM : (M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P)`. Set `N` to `(L ⊓ M).comap M.subtype`. Set `m₀ : M` to `⟨c' • x, hc'M⟩`.

Set `g2 : R →ₗ[R] M ⧸ N` to `LinearMap.toSpanSingleton R (M ⧸ N) (Submodule.Quotient.mk m₀)`. Establish `hmemN : ∀ z : M, z ∈ N ↔ (z : V) ∈ Lx`. Introduce `z`. Simplify using `only [N, Submodule.mem_comap, Submodule.subtype_apply, hE]`. Establish `hsurj2 : Function.Surjective g2`.

Introduce `w`. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨a, ha, y, hy, hzy⟩` from `(memM z).mp hz`. Take `⟨u, b, hub⟩` from `hdec a ha`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Simplify using `only [g2, LinearMap.toSpanSingleton_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hmemN]`. Establish `e : ((b • m₀ - ⟨z, hz⟩ : M) : V) = -(u • x + y)`. Rewrite using `[Submodule.coe_sub, Submodule.coe_smul]`. Use `show b • (c' • x) - z = _`.

Rewrite using `[hzy, hub, add_smul, mul_smul, ← rs, ← rs]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Lx.neg_mem (Lx.add_mem (rx u) hy)`. Establish `hker2 : LinearMap.ker g2 = P`.

Use extensionality with `b`. Simplify using `only [g2, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hmemN]`. Establish `e : ((b • m₀ : M) : V) = (algebraMap R K b * c') • x`. Rewrite using `[Submodule.coe_smul]`.

Use `show b • (c' • x) = _`. Rewrite using `[mul_smul, ← rs]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `hb`.

Assume the negation of the conclusion as `hbP`. Establish `hbI : algebraMap R K b * c' ∈ invIdeal (K` using `K) P := by`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ b hc'I`. Take `⟨v, hv⟩` from `hD _ hbI (hLxL hb)`.

Take `⟨e', i, hi, hei⟩` from `hP.exists_inv hbP`. Apply `hc'R` to reduce the goal to its premises. Take `⟨w, hw⟩` from `F2 c' hc'I i hi`. Use `⟨e' * v + w, ?_⟩` and prove the remaining obligations. Establish `: c' = algebraMap R K (e' * b + i) * c'` using `by rw [hei, map_one, one_mul]`.

Rewrite using `[this]`. Simplify using `only [map_add, map_mul]`. Rewrite using `[hv, hw]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hb`.

Take `⟨v, hv⟩` from `F2 c' hc'I b hb`. Rewrite using `[← hv, ← rs]`. Conclude with `rx v`. Conclude with `(g2.quotKerEquivOfSurjective hsurj2).symm.trans (Submodule.quotEquivOfEq _ _ hker2)`. Establish `hloc : ∀ q : Ideal R, q.IsMaximal → q ≠ P → q ≠ conjIdeal (K` using `K) P → loc (K := K) q L = loc (K := K) q M := by`.

Introduce `q hq hqP hqPc`. Establish `hqc` using `hcmax q hq`. Take `⟨s, hsP, hsq, hsq'⟩` from `neighbourConstruct_avoid hP hq hqc (Ne.symm hqP) (by`. Introduce `e`. Apply `hqPc` to reduce the goal to its premises.

Rewrite using `[e, hconj])`. Take `⟨s', hs'P, hs'q, hs'q'⟩` from `neighbourConstruct_avoid hPc hq hqc (Ne.symm hqPc) (by`. Introduce `e`. Apply `hqP` to reduce the goal to its premises. Rewrite using `[← hconj P, e, hconj])`.

Establish `hs` using `locBasic_mem_hcompl (K := K) q s hsq hsq'`. Establish `hs'` using `locBasic_mem_hcompl (K := K) q s' hs'q hs'q'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Take `⟨s₀, hs₀, hz⟩` from `locBasic_mem_locS.mp hz`.

Use `locBasic_mem_locS.mpr ⟨s' * s₀, Submonoid.mul_mem _ hs' hs₀, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `hLxM (sLx s' hs'P _ hz)`. Introduce `z hz`. Take `⟨s₀, hs₀, hz⟩` from `locBasic_mem_locS.mp hz`.

Use `locBasic_mem_locS.mpr ⟨s * s₀, Submonoid.mul_mem _ hs hs₀, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, y, hy, hzy⟩` from `(memM _).mp hz`. Rewrite using `[mul_smul, hzy, smul_add]`. Take `⟨u, hu⟩` from `F2 a ha s hsP`. Rewrite using `[rs s (a • x), smul_smul, ← hu, ← rs]`.

Conclude with `L.add_mem (L.smul_mem u hx) (L.smul_mem s (hLxL hy))`. Establish `hLat' : Submodule.IsLattice K M`. Establish `hT : (Submodule.span R {c' • x} ⊔ L).FG` using `(Submodule.fg_span_singleton _).sup hLat.fg`. Use `isNoetherian_of_fg_of_noetherian _ hT` as an intermediate fact. Establish `hMT : M ≤ Submodule.span R {c' • x} ⊔ L`.

Introduce `z hz`. Take `⟨a, ha, y, hy, rfl⟩` from `(memM z).mp hz`. Take `⟨u, b, hub⟩` from `hdec a ha`. Establish `e : a • x + y = b • (c' • x) + (u • x + y)`. Rewrite using `[hub, add_smul, mul_smul, ← rs, ← rs]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)) (L.add_mem (L.smul_mem u hx) (hLxL hy))`. Use `⟨Submodule.FG.of_le_of_isNoetherian hMT, ?_⟩` and prove the remaining obligations. Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`.

Establish `hsP : σ p ∈ conjIdeal (K` using `K) P := (hcmem _).mpr (by rw [hσσ]; exact hp)`. Establish `hα : algebraMap R K (σ p) ≠ 0`. Rewrite using `[hσ, star_ne_zero]`. Conclude with `(map_ne_zero_iff _ hinj).mpr hp0`. Rewrite using `[eq_top_iff, ← hLat.span_eq_top, Submodule.span_le]`.

Introduce `l hl`. Establish `e : l = (algebraMap R K (σ p))⁻¹ • ((σ p) • l)`. Rewrite using `[rs, smul_smul, inv_mul_cancel₀ hα, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hLxM (sLx _ hsP l hl)))`.

Conclude with `⟨hLat', hInt, neighbourBasic_unimod h hs hstar P hP hPc L M eL eM hL hInt, ⟨hloc, ⟨eL⟩, ⟨eM⟩⟩, hE⟩`.
-/
theorem neighbourConstruct_main (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (P : Ideal R) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) (L : Submodule R V)
    (hLat : Submodule.IsLattice K L) (hL : IsUnimodular h L) (x : V) (hx : x ∈ L)
    (hxP : x ∉ P • L) (hxx : ∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) :
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x := by
  classical
  have hinj := IsFractionRing.injective R K
  set σ := locBasic_sigma hinj hstar with hσdef
  have hσ : ∀ r : R, algebraMap R K (σ r) = star (algebraMap R K r) :=
    fun r => locBasic_sigma_spec hinj hstar r
  have hσσ : ∀ r : R, σ (σ r) = r := fun r =>
    hinj (by rw [hσ, hσ, star_star])
  have hconj : ∀ I : Ideal R, conjIdeal (K := K) (conjIdeal (K := K) I) = I := by
    intro I
    rw [locBasic_conj_eq hinj hstar, locBasic_conj_eq hinj hstar]
    ext r
    rw [Ideal.mem_comap, Ideal.mem_comap, hσσ]
  have hcmax : ∀ I : Ideal R, I.IsMaximal → (conjIdeal (K := K) I).IsMaximal := by
    intro I hI
    rw [locBasic_conj_eq hinj hstar]
    exact Ideal.comap_isMaximal_of_surjective _ (fun r => ⟨_, hσσ r⟩)
  have hPc : (conjIdeal (K := K) P).IsMaximal := hcmax P hP
  have hcmem : ∀ t : R, t ∈ conjIdeal (K := K) P ↔ σ t ∈ P := by
    intro t; rw [locBasic_conj_eq hinj hstar, Ideal.mem_comap]

  have hone : ∀ k : K, k ∈ (1 : Submodule R K) ↔ k ∈ Set.range (algebraMap R K) :=
    fun k => by rw [Submodule.mem_one]; rfl
  have rmul : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a * b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u * v, map_mul _ _ _⟩
  have radd : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a + b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, map_add _ _ _⟩
  have rstar : ∀ a : K, a ∈ Set.range (algebraMap R K) → star a ∈ Set.range (algebraMap R K) := by
    rintro _ ⟨u, rfl⟩; exact hstar u

  have hsl : ∀ (a : K) (u v : V), h (a • u) v = star a * h u v := by
    intro a u v; rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
  have hsr : ∀ (a : K) (u v : V), h u (a • v) = a * h u v := by
    intro a u v; rw [map_smul, smul_eq_mul]
  have rs : ∀ (r : R) (u : V), r • u = algebraMap R K r • u := fun r u =>
    (algebraMap_smul K r u).symm
  have hsymm : ∀ u v : V, h v u = star (h u v) := by
    intro u v; rw [← hs.eq u v, starRingEnd_apply]

  have memL : ∀ y : V, y ∈ L ↔ ∀ z ∈ L, h z y ∈ Set.range (algebraMap R K) := by
    intro y
    conv_lhs => rw [← hL]
    rw [dualBasic_mem_dual]
    simp only [hone]
  have hLL : ∀ z ∈ L, ∀ y ∈ L, h z y ∈ Set.range (algebraMap R K) :=
    fun z hz y hy => (memL y).mp hy z hz

  have F2 : ∀ a ∈ invIdeal (K := K) P, ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) :=
    fun a ha => neighbourConstruct_mem_inv.mp ha
  have F3 : ∀ a ∈ invIdeal (K := K) P, ∀ t ∈ conjIdeal (K := K) P,
      star a * algebraMap R K t ∈ Set.range (algebraMap R K) := by
    intro a ha t ht
    have := rstar _ (F2 a ha (σ t) ((hcmem t).mp ht))
    rw [star_mul', hσ, star_star, mul_comm] at this
    exact this
  obtain ⟨r₀, hr₀, hr₀x⟩ := hxx
  have hr₀c : r₀ ∈ conjIdeal (K := K) P := Ideal.mul_le_right hr₀
  have F4 : ∀ a ∈ invIdeal (K := K) P, ∀ b ∈ invIdeal (K := K) P, star a * b * h x x ∈ Set.range (algebraMap R K) := by
    intro a ha b hb
    rw [← hr₀x]
    refine Submodule.mul_induction_on
      (C := fun r => star a * b * algebraMap R K r ∈ Set.range (algebraMap R K)) hr₀ ?_ ?_
    · intro p hp q hq
      have e : star a * b * algebraMap R K (p * q) =
          (algebraMap R K p * b) * (star a * algebraMap R K q) := by rw [map_mul]; ring
      rw [e]
      exact rmul _ _ (F2 b hb p hp) (F3 a ha q hq)
    · intro u v hu hv
      rw [map_add, mul_add]
      exact radd _ _ hu hv

  set Lx := neighbourCore h P L x with hLxdef
  have memLx : ∀ y, y ∈ Lx ↔ y ∈ L ∧ ∃ t ∈ conjIdeal (K := K) P, algebraMap R K t = h x y :=
    fun y => neighbourConstruct_mem_core h P L x y
  have hLxL : Lx ≤ L := fun y hy => ((memLx y).mp hy).1
  have rx : ∀ r : R, r • x ∈ Lx := by
    intro r
    refine (memLx _).mpr ⟨L.smul_mem r hx, r * r₀, Ideal.mul_mem_left _ r hr₀c, ?_⟩
    rw [rs, hsr, map_mul, hr₀x]
  have sLx : ∀ s ∈ conjIdeal (K := K) P, ∀ l ∈ L, s • l ∈ Lx := by
    intro s hs l hl
    obtain ⟨t, ht⟩ := hLL x hx l hl
    refine (memLx _).mpr ⟨L.smul_mem s hl, s * t, Ideal.mul_mem_right _ _ hs, ?_⟩
    rw [rs, hsr, map_mul, ht]

  set M := neighbourOf h P L x with hMdef
  have memM : ∀ z, z ∈ M ↔ ∃ a ∈ invIdeal (K := K) P, ∃ y ∈ Lx, z = a • x + y := by
    intro z
    rw [hMdef, neighbourOf, Submodule.mem_sup]
    constructor
    · rintro ⟨w, hw, y, hy, rfl⟩
      obtain ⟨a, ha, rfl⟩ := neighbourConstruct_mem_span.mp hw
      exact ⟨a, ha, y, hy, rfl⟩
    · rintro ⟨a, ha, y, hy, rfl⟩
      exact ⟨a • x, neighbourConstruct_mem_span.mpr ⟨a, ha, rfl⟩, y, hy, rfl⟩
  have hLxM : Lx ≤ M := fun y hy => (memM y).mpr ⟨0, Submodule.zero_mem _, y, hy, by simp⟩
  have hIxM : ∀ a ∈ invIdeal (K := K) P, a • x ∈ M := fun a ha =>
    (memM _).mpr ⟨a, ha, 0, Submodule.zero_mem _, by simp⟩

  have hD : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L → a ∈ Set.range (algebraMap R K) := by
    intro a ha hax
    by_contra hna
    apply hxP
    refine neighbourConstruct_key (K := K) P hP0 L x ?_
    intro c hc
    obtain ⟨u, b, hub⟩ := neighbourBasic_ded P hP c a (F2 c hc) (F2 a ha) hna
    rw [hub, add_smul, mul_smul, ← rs, ← rs]
    exact L.add_mem (L.smul_mem u hx) (L.smul_mem b hax)
  obtain ⟨c', hc'I, hc'R⟩ : ∃ c' ∈ invIdeal (K := K) P, c' ∉ Set.range (algebraMap R K) := by
    by_contra H
    push Not at H
    apply hxP
    refine neighbourConstruct_key (K := K) P hP0 L x ?_
    intro c hc
    obtain ⟨u, hu⟩ := H c hc
    rw [← hu, ← rs]
    exact L.smul_mem u hx
  have hdec : ∀ c ∈ invIdeal (K := K) P, ∃ u b : R, c = algebraMap R K u + algebraMap R K b * c' :=
    fun c hc => neighbourBasic_ded P hP c c' (F2 c hc) (F2 c' hc'I) hc'R

  have hE : L ⊓ M = Lx := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzL, hzM⟩ := Submodule.mem_inf.mp hz
      obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hzM
      have hax : a • x ∈ L := by
        have := L.sub_mem hzL (hLxL hy)
        simpa using this
      obtain ⟨u, rfl⟩ := hD a ha hax
      rw [← rs]
      exact Lx.add_mem (rx u) hy
    · exact le_inf hLxL hLxM

  have hInt : IsIntegralLat h M := by
    intro z hz w hw
    rw [hone]
    obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hz
    obtain ⟨b, hb, y', hy', rfl⟩ := (memM w).mp hw
    obtain ⟨hyL, t, ht, hty⟩ := (memLx y).mp hy
    obtain ⟨hy'L, t', ht', hty'⟩ := (memLx y').mp hy'
    have e : h (a • x + y) (b • x + y') =
        star a * b * h x x + star a * h x y' + b * h y x + h y y' := by
      simp only [map_add, LinearMap.add_apply, hsl, hsr]; ring
    rw [e, hsymm x y, ← hty, ← hty', ← hσ]
    refine radd _ _ (radd _ _ (radd _ _ (F4 a ha b hb) (F3 a ha t' ht')) ?_) (hLL y hyL y' hy'L)
    rw [mul_comm]; exact F2 b hb (σ t) ((hcmem t).mp ht)

  have eL : (L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K := K) P) := by
    let φ : V → R := fun v => if hv : h x v ∈ Set.range (algebraMap R K) then hv.choose else 0
    have hφ : ∀ v ∈ L, algebraMap R K (φ v) = h x v := by
      intro v hv
      simp only [φ, dif_pos (hLL x hx v hv)]
      exact (hLL x hx v hv).choose_spec
    let g : L →ₗ[R] R :=
      { toFun := fun y => φ y.1
        map_add' := fun y y' => hinj (by
          rw [map_add, hφ _ (y + y').2, hφ _ y.2, hφ _ y'.2, Submodule.coe_add, map_add])
        map_smul' := fun r y => hinj (by
          rw [hφ _ (r • y).2, RingHom.id_apply, smul_eq_mul, map_mul, hφ _ y.2,
            Submodule.coe_smul, rs, hsr]) }
    let f : L →ₗ[R] R ⧸ conjIdeal (K := K) P := (conjIdeal (K := K) P).mkQ ∘ₗ g
    have hker : LinearMap.ker f = (L ⊓ M).comap L.subtype := by
      ext y
      rw [LinearMap.mem_ker, hE, Submodule.mem_comap, Submodule.subtype_apply, memLx]
      show Submodule.Quotient.mk (φ y.1) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hy; exact ⟨y.2, φ y, hy, hφ _ y.2⟩
      · rintro ⟨_, t, ht, hty⟩
        have : t = φ y := hinj (by rw [hty, hφ _ y.2])
        rw [← this]; exact ht
    have hsurj : Function.Surjective f := by
      obtain ⟨y₀, hy₀, hy₀P⟩ : ∃ y₀ ∈ L, φ y₀ ∉ conjIdeal (K := K) P := by
        by_contra H
        push Not at H
        apply hxP
        refine neighbourConstruct_key (K := K) P hP0 L x ?_
        intro a ha
        rw [memL]
        intro z hz
        rw [hsr, hsymm x z, ← hφ z hz, ← hσ, mul_comm]
        exact F2 a ha _ ((hcmem _).mp (H z hz))
      obtain ⟨b, i, hi, hbi⟩ := hPc.exists_inv hy₀P
      intro w
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      refine ⟨(r * b) • ⟨y₀, hy₀⟩, ?_⟩
      show Submodule.Quotient.mk (g ((r * b) • ⟨y₀, hy₀⟩)) = Submodule.Quotient.mk r
      rw [map_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : r * b * g ⟨y₀, hy₀⟩ - r = -(r * i) := by
        show r * b * φ y₀ - r = _
        linear_combination r * hbi
      rw [e]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ r hi)
    exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)

  have hc'M : c' • x ∈ M := hIxM c' hc'I
  have eM : (M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P) := by
    let N := (L ⊓ M).comap M.subtype
    let m₀ : M := ⟨c' • x, hc'M⟩
    let g2 : R →ₗ[R] M ⧸ N := LinearMap.toSpanSingleton R (M ⧸ N) (Submodule.Quotient.mk m₀)
    have hmemN : ∀ z : M, z ∈ N ↔ (z : V) ∈ Lx := by
      intro z; simp only [N, Submodule.mem_comap, Submodule.subtype_apply, hE]
    have hsurj2 : Function.Surjective g2 := by
      intro w
      obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      obtain ⟨a, ha, y, hy, hzy⟩ := (memM z).mp hz
      obtain ⟨u, b, hub⟩ := hdec a ha
      refine ⟨b, ?_⟩
      simp only [g2, LinearMap.toSpanSingleton_apply]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hmemN]
      have e : ((b • m₀ - ⟨z, hz⟩ : M) : V) = -(u • x + y) := by
        rw [Submodule.coe_sub, Submodule.coe_smul]
        show b • (c' • x) - z = _
        rw [hzy, hub, add_smul, mul_smul, ← rs, ← rs]; abel
      rw [e]
      exact Lx.neg_mem (Lx.add_mem (rx u) hy)
    have hker2 : LinearMap.ker g2 = P := by
      ext b
      simp only [g2, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hmemN]
      have e : ((b • m₀ : M) : V) = (algebraMap R K b * c') • x := by
        rw [Submodule.coe_smul]
        show b • (c' • x) = _
        rw [mul_smul, ← rs]
      rw [e]
      constructor
      · intro hb
        by_contra hbP
        have hbI : algebraMap R K b * c' ∈ invIdeal (K := K) P := by
          rw [← Algebra.smul_def]; exact Submodule.smul_mem _ b hc'I
        obtain ⟨v, hv⟩ := hD _ hbI (hLxL hb)
        obtain ⟨e', i, hi, hei⟩ := hP.exists_inv hbP
        apply hc'R
        obtain ⟨w, hw⟩ := F2 c' hc'I i hi
        refine ⟨e' * v + w, ?_⟩
        have : c' = algebraMap R K (e' * b + i) * c' := by rw [hei, map_one, one_mul]
        rw [this]
        simp only [map_add, map_mul]
        rw [hv, hw]; ring
      · intro hb
        obtain ⟨v, hv⟩ := F2 c' hc'I b hb
        rw [← hv, ← rs]
        exact rx v
    exact (g2.quotKerEquivOfSurjective hsurj2).symm.trans (Submodule.quotEquivOfEq _ _ hker2)

  have hloc : ∀ q : Ideal R, q.IsMaximal → q ≠ P → q ≠ conjIdeal (K := K) P →
      loc (K := K) q L = loc (K := K) q M := by
    intro q hq hqP hqPc
    have hqc := hcmax q hq
    obtain ⟨s, hsP, hsq, hsq'⟩ := neighbourConstruct_avoid hP hq hqc (Ne.symm hqP) (by
      intro e; apply hqPc; rw [e, hconj])
    obtain ⟨s', hs'P, hs'q, hs'q'⟩ := neighbourConstruct_avoid hPc hq hqc (Ne.symm hqPc) (by
      intro e; apply hqP; rw [← hconj P, e, hconj])
    have hs := locBasic_mem_hcompl (K := K) q s hsq hsq'
    have hs' := locBasic_mem_hcompl (K := K) q s' hs'q hs'q'
    apply le_antisymm
    · intro z hz
      obtain ⟨s₀, hs₀, hz⟩ := locBasic_mem_locS.mp hz
      refine locBasic_mem_locS.mpr ⟨s' * s₀, Submonoid.mul_mem _ hs' hs₀, ?_⟩
      rw [mul_smul]
      exact hLxM (sLx s' hs'P _ hz)
    · intro z hz
      obtain ⟨s₀, hs₀, hz⟩ := locBasic_mem_locS.mp hz
      refine locBasic_mem_locS.mpr ⟨s * s₀, Submonoid.mul_mem _ hs hs₀, ?_⟩
      obtain ⟨a, ha, y, hy, hzy⟩ := (memM _).mp hz
      rw [mul_smul, hzy, smul_add]
      obtain ⟨u, hu⟩ := F2 a ha s hsP
      rw [rs s (a • x), smul_smul, ← hu, ← rs]
      exact L.add_mem (L.smul_mem u hx) (L.smul_mem s (hLxL hy))

  have hLat' : Submodule.IsLattice K M := by
    have hT : (Submodule.span R {c' • x} ⊔ L).FG := (Submodule.fg_span_singleton _).sup hLat.fg
    have := isNoetherian_of_fg_of_noetherian _ hT
    have hMT : M ≤ Submodule.span R {c' • x} ⊔ L := by
      intro z hz
      obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hz
      obtain ⟨u, b, hub⟩ := hdec a ha
      have e : a • x + y = b • (c' • x) + (u • x + y) := by
        rw [hub, add_smul, mul_smul, ← rs, ← rs]; abel
      rw [e]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _))
        (L.add_mem (L.smul_mem u hx) (hLxL hy))
    refine ⟨Submodule.FG.of_le_of_isNoetherian hMT, ?_⟩
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hsP : σ p ∈ conjIdeal (K := K) P := (hcmem _).mpr (by rw [hσσ]; exact hp)
    have hα : algebraMap R K (σ p) ≠ 0 := by
      rw [hσ, star_ne_zero]; exact (map_ne_zero_iff _ hinj).mpr hp0
    rw [eq_top_iff, ← hLat.span_eq_top, Submodule.span_le]
    intro l hl
    have e : l = (algebraMap R K (σ p))⁻¹ • ((σ p) • l) := by
      rw [rs, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hLxM (sLx _ hsP l hl)))
  exact ⟨hLat', hInt, neighbourBasic_unimod h hs hstar P hP hPc L M eL eM hL hInt,
    ⟨hloc, ⟨eL⟩, ⟨eM⟩⟩, hE⟩

end Main

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ _ _ _ h hs _ hstar P hP hP0 L hLat hL x hx hxP hxx`. Conclude with `neighbourConstruct_main h hs hstar P hP hP0 L hLat hL x hx hxP hxx`.
-/
theorem neighbourConstruct : NeighbourConstruct := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs _ hstar P hP hP0 L hLat hL x hx hxP hxx
  exact neighbourConstruct_main h hs hstar P hP hP0 L hLat hL x hx hxP hxx

end Formalism.HermitianLatticesTheory
