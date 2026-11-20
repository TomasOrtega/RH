import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨x.toAdd, fun i _ => hx i, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `fun i => hy i trivial`.
-/
theorem coe_polyBall_eq (n : ℕ) (t : kˣ) :
    (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.ofAdd '' FourierPi.box (Fin n) t := by
  ext x
  constructor
  · intro hx
    exact ⟨x.toAdd, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i trivial

/- English proof (translation)
Rewrite using `[coe_polyBall_eq]`. Conclude with `(FourierPi.isCompact_box t).image (continuous_ofAdd)`.
-/
theorem isCompact_polyBall (n : ℕ) (t : kˣ) :
    IsCompact (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  rw [coe_polyBall_eq]
  exact (FourierPi.isCompact_box t).image (continuous_ofAdd)

/- English proof (translation)
Establish `h : (polyBall (k` using `k) n t : Set (Multiplicative (Fin n → k))) = Multiplicative.toAdd ⁻¹' FourierPi.box (Fin n) t := by`. Use extensionality with `x`. Conclude with `⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩`. Rewrite using `[h]`. Conclude with `(FourierPi.isOpen_box t).preimage continuous_toAdd`.
-/
theorem isOpen_polyBall (n : ℕ) (t : kˣ) :
    IsOpen (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  have h : (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.toAdd ⁻¹' FourierPi.box (Fin n) t := by
    ext x
    exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩
  rw [h]
  exact (FourierPi.isOpen_box t).preimage continuous_toAdd

/- English proof (translation)
Use `Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_` and prove the remaining obligations. Use `show valuation k (u i * x i) ≤ valuation k (c : k)`. Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (hu i) (hx i)).trans h`.
-/
theorem dotProduct_mem_cball {n : ℕ} {a b c : kˣ} (h : valuation k (a : k) * valuation k (b : k) ≤ valuation k (c : k))
    {u x : Fin n → k} (hu : ∀ i, u i ∈ cball a) (hx : ∀ i, x i ∈ cball b) : u ⬝ᵥ x ∈ cball c := by
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (u i * x i) ≤ valuation k (c : k)
  rw [map_mul]
  exact (mul_le_mul' (hu i) (hx i)).trans h

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ n t s`. Take `⟨c, hc⟩` from `exists_cball_addChar_eq_one ψ hψ`. Choose the witnesses or unpack the hypotheses as in `⟨t', ht1, ht2⟩ : ∃ t' : kˣ, valuation k (t' : k) ≤ valuation k (t : k) ∧ valuation k (t' : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by`. Break down `le_total (valuation k (t : k)) (valuation k ((c * s⁻¹ : kˣ) : k)) with h | h` into its components or cases. Conclude with `⟨t, le_rfl, h⟩`.

Conclude with `⟨c * s⁻¹, h, le_rfl⟩`. Establish `hts : valuation k (t' : k) * valuation k (s : k) ≤ valuation k (c : k)`. Establish `hs0 : valuation k (s : k) ≠ 0` using `by simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Set `H : Subgroup (Multiplicative (Fin n → k))` to `polyBall n t`. Set `N : Subgroup H` to `(polyBall n t').subgroupOf H`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_polyBall n t)`. Establish `hNopen : IsOpen (N : Set H)` using `(isOpen_polyBall n t').preimage continuous_subtype_val`.

Use `haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNopen`. Use `letI : Fintype (H ⧸ N) := Fintype.ofFinite _`. Use `haveI : N.Normal := ⟨fun a ha b => by`. Rewrite using `[mul_comm b a, mul_inv_cancel_right]`. Conclude with `ha⟩`.

Set `rep : H ⧸ N → Fin n → k` to `fun q => ((q.out : H) : Multiplicative (Fin n → k)).toAdd`. Establish `hinj : Function.Injective rep` using `fun p q h => Quotient.out_injective (Subtype.ext (Multiplicative.toAdd.injective h))`. Use `⟨Finset.univ.image rep, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨rep 1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩`. Introduce `a ha`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `(q.out : H).2`. Introduce `x hx`. Rewrite using `[Finset.sum_image (fun a _ b _ h => hinj h)]`. Take `⟨l₀, hl₀, hne⟩ : ∃ a ∈ polyBall (k` from `k) n t, ψ (a.toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) ≠ 1 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hx h`. Set `y : H → Circle` to `fun b => (ψ ((b : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd))⁻¹`. Set `f : H → ℂ` to `fun b => (y b : ℂ)`.

Establish `hmul : ∀ b b' : H, f (b * b') = f b * f b'`. Introduce `b b'`. Simplify using `only [f, y, ← Circle.coe_mul]`. Use `congr 1`. Rewrite using `[Subgroup.coe_mul, toAdd_mul, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]`.

Establish `hN : ∀ b, ∀ u ∈ N, f (b * u) = f b`. Introduce `b u hu`. Establish `h1 : ψ ((u : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1` using `hc _ (dotProduct_mem_cball hts (Subgroup.mem_subgroupOf.1 hu) x.2)`. Establish `h2 : f u = 1` using `by simp [f, y, h1]`. Rewrite using `[hmul, h2, mul_one]`.

Set `l : H` to `⟨l₀, hl₀⟩`. Establish `hl : f l ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Establish `h3 : y l = 1` using `Circle.ext (by simpa [f] using h)`.

Simplify `h3` using `[y, l]`. Establish `hsum` using `GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right N f hN l`. Simplify using `only [hmul] at hsum`. Rewrite `hsum` using `[← Finset.sum_mul]`. Establish `hS : ∑ q : H ⧸ N, f q.out = 0`.

Establish `h4 : (∑ q : H ⧸ N, f q.out) * (f l - 1) = 0`. Rewrite using `[mul_sub, hsum, mul_one, sub_self]`. Conclude with `(mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hl)`. Rewrite using `[← hS]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Use `show (((Circle.toUnits (ψ (rep q ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)))⁻¹ : ℂˣ) : ℂ) = f q.out`. Simplify using `[f, y, rep]`.
-/
theorem exists_reps_sum_eq_zero :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (t s : kˣ),
      ∃ R : Finset (Fin n → k), R.Nonempty ∧ (∀ a ∈ R, Multiplicative.ofAdd a ∈ polyBall n t) ∧
        ∀ x : polyBall (k := k) n s, (x : Multiplicative (Fin n → k)) ∉ ann ψ n t →
          ∑ a ∈ R, (((resChr ψ a (polyBall n s) x)⁻¹ : ℂˣ) : ℂ) = 0 := by
  intro k _ _ _ _ ψ hψ n t s
  classical
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨t', ht1, ht2⟩ : ∃ t' : kˣ, valuation k (t' : k) ≤ valuation k (t : k) ∧
      valuation k (t' : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    rcases le_total (valuation k (t : k)) (valuation k ((c * s⁻¹ : kˣ) : k)) with h | h
    · exact ⟨t, le_rfl, h⟩
    · exact ⟨c * s⁻¹, h, le_rfl⟩
  have hts : valuation k (t' : k) * valuation k (s : k) ≤ valuation k (c : k) := by
    have hs0 : valuation k (s : k) ≠ 0 := by simp
    calc valuation k (t' : k) * valuation k (s : k)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul_left ht2 _
      _ = valuation k (c : k) := by
        rw [← map_mul]
        simp
  let H : Subgroup (Multiplicative (Fin n → k)) := polyBall n t
  let N : Subgroup H := (polyBall n t').subgroupOf H
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_polyBall n t)
  have hNopen : IsOpen (N : Set H) := (isOpen_polyBall n t').preimage continuous_subtype_val
  haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNopen
  letI : Fintype (H ⧸ N) := Fintype.ofFinite _
  haveI : N.Normal := ⟨fun a ha b => by
    rw [mul_comm b a, mul_inv_cancel_right]; exact ha⟩
  let rep : H ⧸ N → Fin n → k := fun q => ((q.out : H) : Multiplicative (Fin n → k)).toAdd
  have hinj : Function.Injective rep := fun p q h =>
    Quotient.out_injective (Subtype.ext (Multiplicative.toAdd.injective h))
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · exact ⟨rep 1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  · intro a ha
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (q.out : H).2
  · intro x hx
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    obtain ⟨l₀, hl₀, hne⟩ : ∃ a ∈ polyBall (k := k) n t, ψ (a.toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) ≠ 1 := by
      by_contra h
      push Not at h
      exact hx h
    let y : H → Circle := fun b => (ψ ((b : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd))⁻¹
    let f : H → ℂ := fun b => (y b : ℂ)
    have hmul : ∀ b b' : H, f (b * b') = f b * f b' := by
      intro b b'
      simp only [f, y, ← Circle.coe_mul]
      congr 1
      rw [Subgroup.coe_mul, toAdd_mul, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
    have hN : ∀ b, ∀ u ∈ N, f (b * u) = f b := by
      intro b u hu
      have h1 : ψ ((u : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 :=
        hc _ (dotProduct_mem_cball hts (Subgroup.mem_subgroupOf.1 hu) x.2)
      have h2 : f u = 1 := by simp [f, y, h1]
      rw [hmul, h2, mul_one]
    let l : H := ⟨l₀, hl₀⟩
    have hl : f l ≠ 1 := by
      intro h
      apply hne
      have h3 : y l = 1 := Circle.ext (by simpa [f] using h)
      simpa [y, l] using h3
    have hsum := GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right N f hN l
    simp only [hmul] at hsum
    rw [← Finset.sum_mul] at hsum
    have hS : ∑ q : H ⧸ N, f q.out = 0 := by
      have h4 : (∑ q : H ⧸ N, f q.out) * (f l - 1) = 0 := by
        rw [mul_sub, hsum, mul_one, sub_self]
      exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hl)
    rw [← hS]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (((Circle.toUnits (ψ (rep q ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)))⁻¹ : ℂˣ) : ℂ) = f q.out
    simp [f, y, rep]

end GlobalTheory.CompanionTheory.MirFourier

end
