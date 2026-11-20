import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

/- English proof (translation)
Introduce `A _ _ _ _ B _ _ _ a ha m hm`. Set `I : Ideal A` to `Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})`. Establish `hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m'`. Introduce `u`. Simplify using `only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩`. Introduce and unpack `⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩`. Take `⟨S, hS⟩` from `(IsNoetherian.noetherian I : I.FG)`. Establish `hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m'` using `fun s => (hI s).1 (hS ▸ Submodule.subset_span s.2)`.

Use `choose m' hm'' using hm'`. Set `f : (S → A) →ₗ[A] A × (S → A)` to `LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)`. Set `x : A × (S → A) →ₗ[A] B` to `(LinearMap.fst A A (S → A)).smulRight m - ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)`. Establish `hxf : x ∘ₗ f = 0`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `c`. Establish `e : ∀ s : S, (c s * s) • m = (a * c s) • m' s`. Introduce `s`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[x, f, Finset.sum_smul, e]`. Take `⟨k, α, y, hxy, hαf⟩` from `Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf`. Use `set v := α ((1 : A), (0 : S → A)) with hvdef`. Establish `hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a}`. Introduce `s j`.

Establish `e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1)`. Use extensionality with `t`. Simplify using `[f, Pi.single_apply]`. Simplify using `[f]`. Establish `h0 : α (f (Pi.single s 1)) = 0`.

Simplify using `using congrArg (fun g => g (Pi.single s 1)) hαf`. Rewrite `h0` using `[e, map_add, map_smul, map_smul]`. Establish `h1` using `congrArg (fun w => w j) h0`. Simplify using `only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h1`. Rewrite using `[Ideal.mem_span_singleton']`.

Conclude with `⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩`. Establish `hv : ∀ j, v j ∈ Ideal.span {a}`. Introduce `j`. Apply `GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one` to reduce the goal to its premises. Introduce `q hq h1`.

Take `⟨u, hu, m'', h⟩` from `hm q hq h1`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `huI : u ∈ I` using `(hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩`. Establish `hle : I ≤ (Ideal.span {a}).colon {v j}`. Rewrite using `[← hS, Submodule.span_le]`.

Introduce `s hs`. Rewrite using `[SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]`. Conclude with `hsv ⟨s, hs⟩ j`. Use `hle huI` as an intermediate fact. Rewrite `this` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Then use the resulting hypothesis.

Use `choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)`. Use `⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩` and prove the remaining obligations. Establish `hv' : v = a • Finsupp.equivFunOnFinite.symm z`. Use extensionality with `j`. Simplify using `[← hz j, mul_comm]`.

Establish `hmx : m = x ((1 : A), (0 : S → A))` using `by simp [x]`. Rewrite using `[hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]`.
-/
theorem hart_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  intro A _ _ _ _ B _ _ _ a ha m hm
  classical
  let I : Ideal A := Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})
  have hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m' := by
    intro u
    simp only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m' := fun s =>
    (hI s).1 (hS ▸ Submodule.subset_span s.2)
  choose m' hm'' using hm'
  let f : (S → A) →ₗ[A] A × (S → A) :=
    LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)
  let x : A × (S → A) →ₗ[A] B := (LinearMap.fst A A (S → A)).smulRight m -
    ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)
  have hxf : x ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro c
    have e : ∀ s : S, (c s * s) • m = (a * c s) • m' s := by
      intro s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]; ring
    simp [x, f, Finset.sum_smul, e]
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  set v := α ((1 : A), (0 : S → A)) with hvdef
  have hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a} := by
    intro s j
    have e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1) := by
      ext t
      · simp [f, Pi.single_apply]
      · simp [f]
    have h0 : α (f (Pi.single s 1)) = 0 := by
      simpa using congrArg (fun g => g (Pi.single s 1)) hαf
    rw [e, map_add, map_smul, map_smul] at h0
    have h1 := congrArg (fun w => w j) h0
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Ideal.mem_span_singleton']
    exact ⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩
  have hv : ∀ j, v j ∈ Ideal.span {a} := by
    intro j
    apply GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one
    intro q hq h1
    obtain ⟨u, hu, m'', h⟩ := hm q hq h1
    refine ⟨u, hu, ?_⟩
    have huI : u ∈ I := (hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩
    have hle : I ≤ (Ideal.span {a}).colon {v j} := by
      rw [← hS, Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      exact hsv ⟨s, hs⟩ j
    have := hle huI
    rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
  choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)
  refine ⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩
  have hv' : v = a • Finsupp.equivFunOnFinite.symm z := by
    ext j; simp [← hz j, mul_comm]
  have hmx : m = x ((1 : A), (0 : S → A)) := by simp [x]
  rw [hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]

end GlobalTheory.GoodEtale
