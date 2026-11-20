import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NsmulMemSpanOfCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevelsStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharSpan

open UpperTheory.V.X

variable {O Γ : Type} [CommRing O] [TopologicalSpace O] [Group Γ] [TopologicalSpace Γ]

/- English proof (translation)
Use `⟨hp.comp ha, fun s t => ?_⟩` and prove the remaining obligations. Establish `h` using `(Lev.mk_eq_zero p _).2 (hc s t)`. Rewrite `h` using `[map_sub, sub_eq_zero, map_add, ← smul_eq_mul ((θ s : Oˣ) : O), map_smul]`. Conclude with `h`.
-/
theorem red_mem (p : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (a : Γ → O) (ha : Continuous a)
    (hc : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t)) :
    (fun s => Lev.mk p (a s)) ∈ Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := by
  refine ⟨hp.comp ha, fun s t => ?_⟩
  have h := (Lev.mk_eq_zero p _).2 (hc s t)
  rw [map_sub, sub_eq_zero, map_add, ← smul_eq_mul ((θ s : Oˣ) : O), map_smul] at h
  exact h

omit [TopologicalSpace O] in

/- English proof (translation)
Take `⟨y', hy'⟩` from `(mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)`. Take `⟨y, rfl⟩` from `Lev.mk_surjective p y'`. Use `⟨y, fun s => (Lev.mk_eq_zero p _).1 ?_⟩` and prove the remaining obligations. Establish `h : z.1 s = ((θ s : Oˣ) : O) • Lev.mk p y - Lev.mk p y` using `hy' s`. Rewrite using `[map_sub, map_sub, ← hf, h, ← smul_eq_mul, map_smul, sub_self]`.
-/
theorem lift_cob (p : O) (θ : Γ →* Oˣ) (z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) (f : Γ → O)
    (hf : ∀ s, z.1 s = Lev.mk p (f s))
    (hz : (Submodule.Quotient.mk z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) = 0) :
    ∃ y : O, ∀ s, p ∣ f s - (((θ s : Oˣ) : O) * y - y) := by
  obtain ⟨y', hy'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
  obtain ⟨y, rfl⟩ := Lev.mk_surjective p y'
  refine ⟨y, fun s => (Lev.mk_eq_zero p _).1 ?_⟩
  have h : z.1 s = ((θ s : Oˣ) : O) • Lev.mk p y - Lev.mk p y := hy' s
  rw [map_sub, map_sub, ← hf, h, ← smul_eq_mul, map_smul, sub_self]

omit [TopologicalSpace O] in

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`. Establish `h0 : p • z = 0` using `Subtype.ext (funext fun s => by`. Take `⟨y, hy⟩` from `Lev.mk_surjective p (z.1 s)`. Express the relevant statement in the definitionally equal form `p • z.1 s = 0`. Rewrite using `[← hy, ← map_smul, Lev.mk_eq_zero]`.

Conclude with `Dvd.intro _ rfl)`. Rewrite using `[← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]`.
-/
theorem kill (p : O) (θ : Γ →* Oˣ) (h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) : p • h = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  have h0 : p • z = 0 := Subtype.ext (funext fun s => by
    obtain ⟨y, hy⟩ := Lev.mk_surjective p (z.1 s)
    change p • z.1 s = 0
    rw [← hy, ← map_smul, Lev.mk_eq_zero]
    exact Dvd.intro _ rfl)
  rw [← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]

/- English proof (translation)
Set `z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)` to `⟨_, red_mem _ hp θ a ha hca⟩`. Set `z' : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)` to `⟨_, red_mem _ hp θ a' ha' hca'⟩`. Take `⟨x, hx⟩` from `hcount (Submodule.Quotient.mk z) (fun x hx => by`. Rewrite `hx` using `[← Submodule.Quotient.mk_smul]`. Take `⟨y, hy⟩` from `lift_cob _ θ (x • z) (fun s => x * a s) (fun s => ((Lev.mk p).map_smul x (a s)).symm) hx`.

Conclude with `hann x y hy) (Submodule.Quotient.mk z')`. Rewrite `hx` using `[← Nat.cast_smul_eq_nsmul O, ← sub_eq_zero, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]`. Take `⟨y, hy⟩` from `lift_cob _ θ ((m : O) • z' - x • z) (fun s => (m : O) * a' s - x * a s) (fun s => by`. Rewrite using `[map_sub, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]`. Use the proof step `rfl) hx`.

Use `⟨x, y, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_sub]`. Conclude with `hy s`.
-/
theorem span_of_classes (p q : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (m : ℕ)
    (hcount : ∀ z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), (∀ x : O, x • z = 0 → q ∣ x) →
      ∀ h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), ∃ x : O, m • h = x • z)
    (a : Γ → O) (ha : Continuous a) (hca : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t))
    (hann : ∀ x y : O, (∀ s, p ∣ x * a s - (((θ s : Oˣ) : O) * y - y)) → q ∣ x)
    (a' : Γ → O) (ha' : Continuous a') (hca' : ∀ s t, p ∣ a' (s * t) - (a' s + ((θ s : Oˣ) : O) * a' t)) :
    ∃ x y : O, ∀ s, p ∣ (m : O) * a' s - (x * a s + (((θ s : Oˣ) : O) * y - y)) := by
  let z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a ha hca⟩
  let z' : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a' ha' hca'⟩
  obtain ⟨x, hx⟩ := hcount (Submodule.Quotient.mk z) (fun x hx => by
      rw [← Submodule.Quotient.mk_smul] at hx
      obtain ⟨y, hy⟩ := lift_cob _ θ (x • z) (fun s => x * a s)
        (fun s => ((Lev.mk p).map_smul x (a s)).symm) hx
      exact hann x y hy) (Submodule.Quotient.mk z')
  rw [← Nat.cast_smul_eq_nsmul O, ← sub_eq_zero, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub] at hx
  obtain ⟨y, hy⟩ := lift_cob _ θ ((m : O) • z' - x • z) (fun s => (m : O) * a' s - x * a s)
    (fun s => by
      rw [map_sub, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]
      rfl) hx
  refine ⟨x, y, fun s => ?_⟩
  rw [← sub_sub]
  exact hy s

end GlobalTheory.LocCharSpan

/- English proof (translation)
Introduce `h1 h2 h3 l _ Ω _ _ _ c A hA θ hθ hn1 hn2 r`. Take `⟨C, hC⟩` from `GlobalTheory.T.local_character_h1_finite_levels h1 h2 h3 l Ω c A hA θ hθ hn1 hn2`. Take `⟨m, hm, hcount⟩` from `GlobalTheory.CycIndex.nsmul_mem_span_of_card_le l c C r`. Use `⟨m, hm, fun n hn a ha hca hann a' ha' hca' => ?_⟩` and prove the remaining obligations. Take `⟨hfin, hcard⟩` from `hC n hn`.

Establish `hl : ((l : ℕ) : c.O) ≠ 0` using `fun h => by`. Establish `h'` using `congrArg Subtype.val h`. Simplify using `only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'`. Conclude with `(Fact.out : l.Prime).ne_zero h'`. Establish `hp` using `(UpperTheory.V.X.So.adicCont l c).1 _ (pow_ne_zero n hl)`.

Conclude with `GlobalTheory.LocCharSpan.span_of_classes _ _ hp θ m (hcount n _ (GlobalTheory.LocCharSpan.kill _ θ) hcard) a ha hca hann a' ha' hca'`.
-/
theorem GlobalTheory.LocCharSpan.span : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → (∃ g, θ' g ≠ 1) → (∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∀ r : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → (∀ x y : c.O, (∀ s, ((l : ℕ) : c.O) ^ n ∣ x * a s - (((θ' s : c.Oˣ) : c.O) * y - y)) → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ a' : ↥(Dec (F := ℚ) A) → c.O, Continuous a' → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a' (s * t) - (a' s + ((θ' s : c.Oˣ) : c.O) * a' t)) → ∃ x y : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ (m : c.O) * a' s - (x * a s + (((θ' s : c.Oˣ) : c.O) * y - y)) := by
  intro h1 h2 h3 l _ Ω _ _ _ c A hA θ hθ hn1 hn2 r
  obtain ⟨C, hC⟩ := GlobalTheory.T.local_character_h1_finite_levels h1 h2 h3 l Ω c A hA θ hθ hn1 hn2
  obtain ⟨m, hm, hcount⟩ := GlobalTheory.CycIndex.nsmul_mem_span_of_card_le l c C r
  refine ⟨m, hm, fun n hn a ha hca hann a' ha' hca' => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hl : ((l : ℕ) : c.O) ≠ 0 := fun h => by
    have h' := congrArg Subtype.val h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hp := (UpperTheory.V.X.So.adicCont l c).1 _ (pow_ne_zero n hl)
  exact GlobalTheory.LocCharSpan.span_of_classes _ _ hp θ m
    (hcount n _ (GlobalTheory.LocCharSpan.kill _ θ) hcard) a ha hca hann a' ha' hca'
