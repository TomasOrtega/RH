import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModelNef
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModelGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

/- English proof (translation)
Assume the negation of the conclusion as `hJ`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hJ`. Establish `hmM : (m : A) ∈ M` using `hM.isPrime.mem_of_pow_mem e (hJM hm)`. Rewrite `hmM` using `[Nat.prod_primeFactors_pow_factorization hm0, Nat.cast_prod]`. Take `⟨p, hp', hpM⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hM.isPrime)).mp hmM`.

Rewrite `hpM` using `[Nat.cast_pow]`. Establish `h1 : (p : A) ∈ M` using `hM.isPrime.mem_of_pow_mem _ hpM`. Establish `hle : J ⊔ Ideal.span {(p : A)} ≤ M` using `sup_le hJM ((Ideal.span_singleton_le_iff_mem M).mpr h1)`. Rewrite `hle` using `[hp p hp']`. Conclude with `hM.ne_top (top_le_iff.mp hle)`.
-/
theorem LiftModel.ideal_eq_top_of_pow_mem {A : Type} [CommRing A] (J : Ideal A) {m : ℕ} (hm0 : m ≠ 0) (e : ℕ)
    (hm : (m : A) ^ e ∈ J) (hp : ∀ p ∈ m.primeFactors, J ⊔ Ideal.span {(p : A)} = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hmM : (m : A) ∈ M := hM.isPrime.mem_of_pow_mem e (hJM hm)
  rw [Nat.prod_primeFactors_pow_factorization hm0, Nat.cast_prod] at hmM
  obtain ⟨p, hp', hpM⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hM.isPrime)).mp hmM
  rw [Nat.cast_pow] at hpM
  have h1 : (p : A) ∈ M := hM.isPrime.mem_of_pow_mem _ hpM
  have hle : J ⊔ Ideal.span {(p : A)} ≤ M := sup_le hJM ((Ideal.span_singleton_le_iff_mem M).mpr h1)
  rw [hp p hp'] at hle
  exact hM.ne_top (top_le_iff.mp hle)

/- English proof (translation)
Establish `h` using `hx c hc`. Simplify using `using h`.
-/
theorem LiftModel.mem_chartRingZ_of_mem_chartLat {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {n : K → ℤ} {x : Ω} (hx : x ∈ chartLat y n 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : x * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingZ y c := by
  have h := hx c hc
  simpa using h

/- English proof (translation)
Set `F : Finset Ω` to `Finset.univ.image x₁ ∪ m.primeFactors.biUnion (fun p => Finset.univ.image (xP p)) ∪ Finset.univ.image x₃`. Establish `h₁F : ∀ j, x₁ j ∈ F` using `fun j => by simp [F]`. Establish `hPF : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ F`. Introduce `p hp j`. Simplify using `only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]`.

Conclude with `Or.inl (Or.inr ⟨p, hp, j, rfl⟩)`. Establish `h₃F : ∀ j, x₃ j ∈ F` using `fun j => by simp [F]`. Establish `hFmem : ∀ f ∈ F, f ∈ chartLat y n 1`. Introduce `f hf`. Simplify using `only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf`.

Break down `hf with (⟨j, rfl⟩ | ⟨p, hp, j, rfl⟩) | ⟨j, rfl⟩` into its components or cases. Conclude with `hx₁ j`. Conclude with `hxP p hp j`. Conclude with `hx₃ j`. Use `⟨F, hFmem, fun c hc => ?_, h₃F⟩` and prove the remaining obligations.

Set `v : F → chartRingZ y c` to `fun f => ⟨(f : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f f.2) c hc⟩`. Establish `hv : ∀ f (hf : f ∈ F), (⟨f * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f hf) c hc⟩ : chartRingZ y c) ∈ Ideal.span (Set.range v)` using `fun f hf => Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩`. Take `⟨e, u, hu, hsum⟩` from `hg₁ c hc`. Establish `htop : Ideal.span (Set.range v) = ⊤`. Use `LiftModel.ideal_eq_top_of_pow_mem _ hm0 e ?_ fun p hp => ?_` and prove the remaining obligations.

Establish `heq : ((m : chartRingZ y c) ^ e) = ∑ j, (⟨u j, hu j⟩ : chartRingZ y c) * ⟨x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (h₁F j)) c hc⟩`. Apply `Subtype.val_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `hsum.symm`. Rewrite using `[heq]`.

Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (h₁F j))`. Take `⟨u', w, hu', hw, hsum'⟩` from `hgP p hp c hc`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `heq : (1 : chartRingZ y c) = ∑ j, (⟨u' j, hu' j⟩ : chartRingZ y c) * ⟨xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (hPF p hp j)) c hc⟩ + (p : chartRingZ y c) * ⟨w, hw⟩`. Apply `Subtype.val_injective` to reduce the goal to its premises.

Use `push_cast`. Conclude with `hsum'.symm`. Rewrite using `[heq]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (hPF p hp j)))) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))`. Establish `h1 : (1 : chartRingZ y c) ∈ Ideal.span (Set.range v)`.

Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Take `⟨a, ha⟩` from `Ideal.mem_span_range_iff_exists_fun.mp h1`. Use `⟨fun f => (a f : Ω), fun f => (a f).2, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val ha`.

Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem LiftModel.combine {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) {m : ℕ} (hm0 : m ≠ 0) {r₁ : ℕ} (x₁ : Fin r₁ → Ω)
    (hx₁ : ∀ j, x₁ j ∈ chartLat y n 1)
    (hg₁ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r₁ → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
      ∑ j, u j * (x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = (m : Ω) ^ e)
    (rP : ℕ → ℕ) (xP : ∀ p, Fin (rP p) → Ω) (hxP : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ chartLat y n 1)
    (hgP : ∀ p ∈ m.primeFactors, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin (rP p) → Ω) (v : Ω),
      (∀ j, u j ∈ chartRingZ y c) ∧ v ∈ chartRingZ y c ∧
        ∑ j, u j * (xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) + p * v = 1)
    {r₃ : ℕ} (x₃ : Fin r₃ → Ω) (hx₃ : ∀ j, x₃ j ∈ chartLat y n 1) :
    ∃ F : Finset Ω, (∀ f ∈ F, f ∈ chartLat y n 1) ∧ KH.GeneratesOn y n (fun f : F => (f : Ω)) ∧
      ∀ j, x₃ j ∈ F := by
  classical
  let F : Finset Ω := Finset.univ.image x₁ ∪ m.primeFactors.biUnion (fun p => Finset.univ.image (xP p)) ∪
    Finset.univ.image x₃
  have h₁F : ∀ j, x₁ j ∈ F := fun j => by simp [F]
  have hPF : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ F := by
    intro p hp j
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨p, hp, j, rfl⟩)
  have h₃F : ∀ j, x₃ j ∈ F := fun j => by simp [F]
  have hFmem : ∀ f ∈ F, f ∈ chartLat y n 1 := by
    intro f hf
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf
    rcases hf with (⟨j, rfl⟩ | ⟨p, hp, j, rfl⟩) | ⟨j, rfl⟩
    · exact hx₁ j
    · exact hxP p hp j
    · exact hx₃ j
  refine ⟨F, hFmem, fun c hc => ?_, h₃F⟩
  let v : F → chartRingZ y c := fun f =>
    ⟨(f : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f f.2) c hc⟩
  have hv : ∀ f (hf : f ∈ F), (⟨f * ∏ k, y ⟨k, c k⟩ ^ (-n k),
      LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f hf) c hc⟩ : chartRingZ y c) ∈ Ideal.span (Set.range v) :=
    fun f hf => Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨e, u, hu, hsum⟩ := hg₁ c hc
  have htop : Ideal.span (Set.range v) = ⊤ := by
    refine LiftModel.ideal_eq_top_of_pow_mem _ hm0 e ?_ fun p hp => ?_
    · have heq : ((m : chartRingZ y c) ^ e) = ∑ j, (⟨u j, hu j⟩ : chartRingZ y c) *
          ⟨x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (h₁F j)) c hc⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum.symm
      rw [heq]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (h₁F j))
    · obtain ⟨u', w, hu', hw, hsum'⟩ := hgP p hp c hc
      rw [Ideal.eq_top_iff_one]
      have heq : (1 : chartRingZ y c) = ∑ j, (⟨u' j, hu' j⟩ : chartRingZ y c) *
          ⟨xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (hPF p hp j)) c hc⟩ +
          (p : chartRingZ y c) * ⟨w, hw⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum'.symm
      rw [heq]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (hPF p hp j))))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have h1 : (1 : chartRingZ y c) ∈ Ideal.span (Set.range v) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  refine ⟨fun f => (a f : Ω), fun f => (a f).2, ?_⟩
  have h := congrArg Subtype.val ha
  push_cast at h
  exact h

/- English proof (translation)
Establish `hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩`. Introduce `τ _ m`. Rewrite using `[Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by`. Simplify using `using hx), Fintype.sum_sigma, Fintype.sum_unique]`. Establish `hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree`.

Introduce `τ m`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression. Establish `hH : g.IsHomogeneous (d ())`. Introduce `m hm`.

Rewrite using `[hw, hdeg]`. Conclude with `hg m (mem_support_iff.mpr hm) ()`. Establish `h` using `hH.rename_isHomogeneous (f := φ)`. Introduce `m hm k`. Use `h (mem_support_iff.mp hm)` as an intermediate fact.

Rewrite `this` using `[hw, hdeg]`. Conclude with `this`.
-/
theorem LiftModel.isMultiHomog_rename {κ κ' : Type} [Fintype κ] [Fintype κ']
    (φ : (Σ _ : Unit, κ) → (Σ _ : Unit, κ')) {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ}
    (hg : IsMultiHomog g d) : IsMultiHomog (rename φ g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have h := hH.rename_isHomogeneous (f := φ)
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

/- English proof (translation)
Introduce `s`. Take `⟨d, g, g', hg, hg', hg0, hgs⟩` from `hb s`. Set `φ : (Σ _ : Unit, Fin r) → (Σ _ : Unit, F)` to `fun p => ⟨(), ⟨x₃ p.2, h p.2⟩⟩`. Establish `hev : ∀ f : MRing (fun _ : Unit => Fin r), aeval (fun p : Σ _ : Unit, F => (p.2 : Ω)) (rename φ f) = aeval (fun p : Σ _ : Unit, Fin r => x₃ p.2) f` using `fun f => by`. Rewrite using `[aeval_rename]`.

Both sides reduce to the same expression. Use `⟨d, rename φ g, rename φ g', LiftModel.isMultiHomog_rename φ hg, LiftModel.isMultiHomog_rename φ hg', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`. Conclude with `hg0`. Rewrite using `[hev, hev]`.

Conclude with `hgs`.
-/
theorem LiftModel.birational_of_subfamily {Ω : Type} [Field Ω] {r : ℕ} (x₃ : Fin r → Ω) (F : Finset Ω)
    (h : ∀ j, x₃ j ∈ F) (hb : Birational (fun p : Σ _ : Unit, Fin r => x₃ p.2)) :
    Birational (fun p : Σ _ : Unit, F => (p.2 : Ω)) := by
  intro s
  obtain ⟨d, g, g', hg, hg', hg0, hgs⟩ := hb s
  let φ : (Σ _ : Unit, Fin r) → (Σ _ : Unit, F) := fun p => ⟨(), ⟨x₃ p.2, h p.2⟩⟩
  have hev : ∀ f : MRing (fun _ : Unit => Fin r), aeval (fun p : Σ _ : Unit, F => (p.2 : Ω)) (rename φ f) =
      aeval (fun p : Σ _ : Unit, Fin r => x₃ p.2) f := fun f => by
    rw [aeval_rename]
    rfl
  refine ⟨d, rename φ g, rename φ g', LiftModel.isMultiHomog_rename φ hg, LiftModel.isMultiHomog_rename φ hg', ?_, ?_⟩
  · rw [hev]
    exact hg0
  · rw [hev, hev]
    exact hgs

/- English proof (translation)
Establish `h` using `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hV`. Conclude with `⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩`.
-/
theorem LiftModel.isProjVarF_genIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} (hV : IsArithVar (mCoordIdeal y) (D + 1)) :
    IsProjVarF (KH.genIdeal y) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hV
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

/- English proof (translation)
Establish `hprod : ∀ s ⊆ m.primeFactors, 1 ≤ ∏ p ∈ s, qP p` using `fun s hs => Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => by have := hqP p (hs hp); omega)`. Establish `hprodS` using `hprod m.primeFactors subset_rfl`. Use `set t := t₁ + t₃ + ∑ p ∈ m.primeFactors, tP p + 1 with ht`. Use `set Q := q₁ * q₃ * ∏ p ∈ m.primeFactors, qP p with hQ`. Establish `hQ1 : 1 ≤ Q` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`.

Establish `ht1 : 1 ≤ t` using `by omega`. Establish `hT₁ : t₁ ≤ t * (q₃ * ∏ p ∈ m.primeFactors, qP p)` using `le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))`. Take `⟨r₁, x₁, hx₁, hg₁⟩` from `h₁ _ hT₁`. Establish `e₁ : t * (q₃ * ∏ p ∈ m.primeFactors, qP p) * q₁ = t * Q` using `by rw [hQ]; ring`. Rewrite `hx₁`, `hg₁` using `[e₁]`.

Establish `hT₃ : t₃ ≤ t * (q₁ * ∏ p ∈ m.primeFactors, qP p)` using `le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))`. Take `⟨r₃, x₃, hx₃, hB₃⟩` from `h₃ _ hT₃`. Establish `e₃ : t * (q₁ * ∏ p ∈ m.primeFactors, qP p) * q₃ = t * Q` using `by rw [hQ]; ring`. Rewrite `hx₃` using `[e₃]`. Establish `hP' : ∀ p ∈ m.primeFactors, ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * Q) • N) 1) ∧ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧ v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * Q) • N) k)) + p * …`.

Introduce `p hp`. Establish `hprodp` using `hprod (m.primeFactors.erase p) (Finset.erase_subset _ _)`. Establish `htp : tP p ≤ t`. Use `Finset.single_le_sum (f := tP) (fun _ _ => Nat.zero_le _) hp` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hTp : tP p ≤ t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p')` using `le_trans htp (Nat.le_mul_of_pos_right _ (by positivity))`. Take `⟨r, x', hx, hg⟩` from `hP p hp _ hTp`. Establish `ep : t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') * qP p = t * Q`. Rewrite using `[hQ, ← Finset.mul_prod_erase m.primeFactors qP hp]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hx`, `hg` using `[ep]`. Conclude with `⟨r, x', hx, hg⟩`. Use `choose! rP xP hxP hgP using hP'`. Take `⟨F, hFmem, hFgen, hF₃⟩` from `LiftModel.combine y ((t * Q) • N) (by omega) x₁ hx₁ hg₁ rP xP hxP hgP x₃ hx₃`. Conclude with `⟨t * Q, F, Nat.one_le_iff_ne_zero.mpr (by positivity), hFmem, hFgen, r₃, x₃, hF₃, hB₃⟩`.
-/
theorem LiftModel.core {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (N : K → ℤ) (B : ∀ r : ℕ, (Fin r → Ω) → Prop) {q₁ m t₁ : ℕ} (hq₁ : 1 ≤ q₁) (hm : 1 ≤ m)
    (h₁ : ∀ t : ℕ, t₁ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₁) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q₁) • N) k)) = (m : Ω) ^ e)
    (qP tP : ℕ → ℕ) (hqP : ∀ p ∈ m.primeFactors, 1 ≤ qP p)
    (hP : ∀ p ∈ m.primeFactors, ∀ t : ℕ, tP p ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω),
      (∀ j, x' j ∈ chartLat y ((t * qP p) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * qP p) • N) k)) + p * v = 1)
    {q₃ t₃ : ℕ} (hq₃ : 1 ≤ q₃)
    (h₃ : ∀ t : ℕ, t₃ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₃) • N) 1) ∧ B r x') :
    ∃ (a : ℕ) (F : Finset Ω), 1 ≤ a ∧ (∀ f ∈ F, f ∈ chartLat y (a • N) 1) ∧
      KH.GeneratesOn y (a • N) (fun f : F => (f : Ω)) ∧ ∃ (r : ℕ) (x₃ : Fin r → Ω), (∀ j, x₃ j ∈ F) ∧ B r x₃ := by
  classical
  have hprod : ∀ s ⊆ m.primeFactors, 1 ≤ ∏ p ∈ s, qP p := fun s hs =>
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => by have := hqP p (hs hp); omega)
  have hprodS := hprod m.primeFactors subset_rfl
  set t := t₁ + t₃ + ∑ p ∈ m.primeFactors, tP p + 1 with ht
  set Q := q₁ * q₃ * ∏ p ∈ m.primeFactors, qP p with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht1 : 1 ≤ t := by omega

  have hT₁ : t₁ ≤ t * (q₃ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₁, x₁, hx₁, hg₁⟩ := h₁ _ hT₁
  have e₁ : t * (q₃ * ∏ p ∈ m.primeFactors, qP p) * q₁ = t * Q := by rw [hQ]; ring
  rw [e₁] at hx₁ hg₁

  have hT₃ : t₃ ≤ t * (q₁ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₃, x₃, hx₃, hB₃⟩ := h₃ _ hT₃
  have e₃ : t * (q₁ * ∏ p ∈ m.primeFactors, qP p) * q₃ = t * Q := by rw [hQ]; ring
  rw [e₃] at hx₃

  have hP' : ∀ p ∈ m.primeFactors, ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * Q) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * Q) • N) k)) + p * v = 1 := by
    intro p hp
    have hprodp := hprod (m.primeFactors.erase p) (Finset.erase_subset _ _)
    have htp : tP p ≤ t := by
      have := Finset.single_le_sum (f := tP) (fun _ _ => Nat.zero_le _) hp
      omega
    have hTp : tP p ≤ t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') :=
      le_trans htp (Nat.le_mul_of_pos_right _ (by positivity))
    obtain ⟨r, x', hx, hg⟩ := hP p hp _ hTp
    have ep : t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') * qP p = t * Q := by
      rw [hQ, ← Finset.mul_prod_erase m.primeFactors qP hp]
      ring
    rw [ep] at hx hg
    exact ⟨r, x', hx, hg⟩
  choose! rP xP hxP hgP using hP'
  obtain ⟨F, hFmem, hFgen, hF₃⟩ :=
    LiftModel.combine y ((t * Q) • N) (by omega) x₁ hx₁ hg₁ rP xP hxP hgP x₃ hx₃
  exact ⟨t * Q, F, Nat.one_le_iff_ne_zero.mpr (by positivity), hFmem, hFgen, r₃, x₃, hF₃, hB₃⟩

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y D N hV hQ hF`. Take `⟨q₁, m, t₁, hq₁, hm, h₁⟩` from `hS K ι Ω y D N hV hQ`. Establish `hP` using `fun p (hp : p ∈ m.primeFactors) => hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))`. Use `choose! qP tP hqP hP using hP`. Take `⟨a, F, ha, hmem, hgen, -⟩` from `LiftModel.core y N (fun _ _ => True) hq₁ hm h₁ qP tP hqP hP (q₃ := 1) (t₃ := 0) le_rfl fun _ _ => ⟨0, Fin.elim0, fun j => j.elim0, trivial⟩`.

Conclude with `⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen⟩`.
-/
theorem LiftModelGen.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement) : LiftModelGen.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hQ hF
  classical
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨a, F, ha, hmem, hgen, -⟩ := LiftModel.core y N (fun _ _ => True) hq₁ hm h₁ qP tP hqP hP
    (q₃ := 1) (t₃ := 0) le_rfl fun _ _ => ⟨0, Fin.elim0, fun j => j.elim0, trivial⟩
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen⟩

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y D α b a₀ I hI hV hbir hnef hb ha₀ hF`. Establish `hQ : KH.AmpleV ℚ (KH.genIdeal y) (b • α + fun _ => (a₀ : ℤ))` using `hKA ℚ K ι I (KH.genIdeal y) D α b a₀ hI (LiftModel.isProjVarF_genIdeal hV) hnef hb ha₀`. Take `⟨q₁, m, t₁, hq₁, hm, h₁⟩` from `hS K ι Ω y D _ hV hQ`. Establish `hP` using `fun p (hp : p ∈ m.primeFactors) => hA K ι Ω y D _ p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))`. Use `choose! qP tP hqP hP using hP`.

Take `⟨q₃, t₃, hq₃, h₃⟩` from `hB K ι Ω y D α b a₀ I hI hV hbir hnef hb ha₀`. Take `⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩` from `LiftModel.core y _ (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃`. Conclude with `⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen, LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩`.
-/
theorem LiftModelNef.proof (hKA : KH.KAmpStatement) (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalNef.Statement) : LiftModelNef.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D α b a₀ I hI hV hbir hnef hb ha₀ hF
  classical
  have hQ : KH.AmpleV ℚ (KH.genIdeal y) (b • α + fun _ => (a₀ : ℤ)) :=
    hKA ℚ K ι I (KH.genIdeal y) D α b a₀ hI (LiftModel.isProjVarF_genIdeal hV) hnef hb ha₀
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D _ hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D _ p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D α b a₀ I hI hV hbir hnef hb ha₀
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y _ (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y D N hV hbir hQ hcQ hF`. Take `⟨c, hc1, hcQ⟩` from `hcQ`. Take `⟨q₁, m, t₁, hq₁, hm, h₁⟩` from `hS K ι Ω y D N hV hQ`. Establish `hP` using `fun p (hp : p ∈ m.primeFactors) => hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))`. Use `choose! qP tP hqP hP using hP`.

Take `⟨q₃, t₃, hq₃, h₃⟩` from `hB K ι Ω y D N c hV hbir hc1 hcQ`. Take `⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩` from `LiftModel.core y N (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃`. Conclude with `⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen, LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩`.
-/
theorem LiftModel.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalAmple.Statement) : LiftModel.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hbir hQ hcQ hF
  classical
  obtain ⟨c, hc1, hcQ⟩ := hcQ
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D N c hV hbir hc1 hcQ
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y N (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
