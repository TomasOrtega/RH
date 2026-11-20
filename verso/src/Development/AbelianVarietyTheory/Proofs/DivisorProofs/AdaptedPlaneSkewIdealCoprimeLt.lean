import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlacesStatement

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open scoped nonZeroDivisors Matrix TensorProduct
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.PlaneSkewIdeal

section Ideals

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Establish `hr0 : r ≠ 0` using `fun e => hr (e ▸ zero_mem _)`. Establish `h : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r)) = -WithZero.log (w.valuation E (algebraMap (𝓞 E) E r))`. Rewrite using `[← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe E w (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]), HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hr0, WithZero.log_exp, neg_neg]`. Rewrite using `[h, (w.valuation_eq_one_iff_notMem (K := E)).2 hr]`. Simplify using the standard rewrite rules.
-/
theorem count_span_eq_zero {r : 𝓞 E} (hr : r ∉ w.asIdeal) :
    FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r)) = 0 := by
  have hr0 : r ≠ 0 := fun e => hr (e ▸ zero_mem _)
  have h : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r)) =
      -WithZero.log (w.valuation E (algebraMap (𝓞 E) E r)) := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe E w
      (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hr0, WithZero.log_exp,
      neg_neg]
  rw [h, (w.valuation_eq_one_iff_notMem (K := E)).2 hr]
  simp

/- English proof (translation)
Take `⟨S, rfl⟩` from `hN`. Establish `h1 : ∀ s : S, ∃ d : w.asIdeal.primeCompl, ∃ m : 𝓞 E, ((d : 𝓞 E) : E) * s = m` using `fun s => by`. Take `⟨m, d, e⟩` from `w.exists_primeCompl_mul_eq_of_integer (s : E) (h _ (Submodule.subset_span s.2))`. Conclude with `⟨d, m, by rw [mul_comm]; exact e⟩`. Use `choose d m hd using h1`.

Use `⟨((∏ s, d s : w.asIdeal.primeCompl) : 𝓞 E), (∏ s, d s).2, fun s hs => ?_⟩` and prove the remaining obligations. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`. Use `⟨((∏ s ∈ Finset.univ.erase ⟨x, hx⟩, d s : w.asIdeal.primeCompl) : 𝓞 E) * m ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : S))]`.

Use `hd ⟨x, hx⟩` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Rewrite using `[mul_assoc, this]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [mul_add, ha, hb]; simp⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`.

Conclude with `⟨c * a, by rw [mul_smul_comm, ha, Algebra.smul_def]; simp⟩`.
-/
theorem exists_den {N : Submodule (𝓞 E) E} (hN : N.FG) (h : ∀ s ∈ N, w.valuation E s ≤ 1) :
    ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ ∀ s ∈ N, ∃ m : 𝓞 E, (d : E) * s = m := by
  obtain ⟨S, rfl⟩ := hN
  have h1 : ∀ s : S, ∃ d : w.asIdeal.primeCompl, ∃ m : 𝓞 E, ((d : 𝓞 E) : E) * s = m := fun s => by
    obtain ⟨m, d, e⟩ := w.exists_primeCompl_mul_eq_of_integer (s : E) (h _ (Submodule.subset_span s.2))
    exact ⟨d, m, by rw [mul_comm]; exact e⟩
  choose d m hd using h1
  classical
  refine ⟨((∏ s, d s : w.asIdeal.primeCompl) : 𝓞 E), (∏ s, d s).2, fun s hs => ?_⟩
  induction hs using Submodule.span_induction with
  | mem x hx =>
    refine ⟨((∏ s ∈ Finset.univ.erase ⟨x, hx⟩, d s : w.asIdeal.primeCompl) : 𝓞 E) * m ⟨x, hx⟩, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : S))]
    have := hd ⟨x, hx⟩
    push_cast at this ⊢
    rw [mul_assoc, this]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [mul_add, ha, hb]; simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [mul_smul_comm, ha, Algebra.smul_def]; simp⟩

/- English proof (translation)
Establish `hu0 : u ≠ 0` using `fun e => by simp [e] at hu1`. Establish `hI : I ≠ 0` using `fun e => hu0 (by simpa [e] using hu)`. Establish `hne : ∀ r : 𝓞 E, r ∉ w.asIdeal → FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) ≠ 0` using `fun r hr => FractionalIdeal.spanSingleton_ne_zero_iff.2 fun e => hr ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨m, d, e⟩` from `w.exists_primeCompl_mul_eq_of_integer u hu1.le`.

Establish `hm : m ∉ w.asIdeal`. Rewrite using `[← w.valuation_eq_one_iff_notMem (K := E), ← e, map_mul, hu1, one_mul]`. Conclude with `(w.valuation_eq_one_iff_notMem (K := E)).2 d.2`. Establish `hmI : algebraMap (𝓞 E) E m ∈ I`. Rewrite using `[← e, mul_comm, ← Algebra.smul_def]`.

Conclude with `(I : Submodule (𝓞 E) E).smul_mem _ hu`. Rewrite using `[← count_span_eq_zero w hm]`. Conclude with `FractionalIdeal.count_mono E w (hne m hm) (FractionalIdeal.spanSingleton_le_iff_mem.2 hmI)`. Take `⟨d, hd, hdI⟩` from `exists_den w (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) h`. Establish `hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E d) * I ≤ 1`.

Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `FractionalIdeal.mem_singleton_mul.1 hx`. Take `⟨m, hm⟩` from `hdI y hy`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨m, hm.symm⟩`. Use `FractionalIdeal.count_mono E w (mul_ne_zero (hne d hd) hI) hle` as an intermediate fact.

Rewrite `this` using `[FractionalIdeal.count_mul E w (hne d hd) hI, count_span_eq_zero w hd, zero_add, FractionalIdeal.count_one]`. Then use the resulting hypothesis.
-/
theorem count_eq_zero {I : FractionalIdeal (𝓞 E)⁰ E} (h : ∀ s ∈ I, w.valuation E s ≤ 1) {u : E} (hu : u ∈ I)
    (hu1 : w.valuation E u = 1) : FractionalIdeal.count E w I = 0 := by
  have hu0 : u ≠ 0 := fun e => by simp [e] at hu1
  have hI : I ≠ 0 := fun e => hu0 (by simpa [e] using hu)
  have hne : ∀ r : 𝓞 E, r ∉ w.asIdeal → FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) ≠ 0 :=
    fun r hr => FractionalIdeal.spanSingleton_ne_zero_iff.2 fun e =>
      hr ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  apply le_antisymm
  · obtain ⟨m, d, e⟩ := w.exists_primeCompl_mul_eq_of_integer u hu1.le
    have hm : m ∉ w.asIdeal := by
      rw [← w.valuation_eq_one_iff_notMem (K := E), ← e, map_mul, hu1, one_mul]
      exact (w.valuation_eq_one_iff_notMem (K := E)).2 d.2
    have hmI : algebraMap (𝓞 E) E m ∈ I := by
      rw [← e, mul_comm, ← Algebra.smul_def]
      exact (I : Submodule (𝓞 E) E).smul_mem _ hu
    rw [← count_span_eq_zero w hm]
    exact FractionalIdeal.count_mono E w (hne m hm) (FractionalIdeal.spanSingleton_le_iff_mem.2 hmI)
  · obtain ⟨d, hd, hdI⟩ := exists_den w (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) h
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E d) * I ≤ 1 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
      obtain ⟨m, hm⟩ := hdI y hy
      exact (FractionalIdeal.mem_one_iff _).2 ⟨m, hm.symm⟩
    have := FractionalIdeal.count_mono E w (mul_ne_zero (hne d hd) hI) hle
    rwa [FractionalIdeal.count_mul E w (hne d hd) hI, count_span_eq_zero w hd, zero_add,
      FractionalIdeal.count_one] at this

/- English proof (translation)
Establish `h1 : x ∈ (diffE E)⁻¹`. Unfold `diffE`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ, inv_inv, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Introduce `a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`.

Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hx o)`. Conclude with `⟨k, hk⟩`. Establish `h2 : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal` using `fun hle => by`. Use `FractionalIdeal.count_mono E w (diffE_ne_zero (E := E)) ((FractionalIdeal.coeIdeal_le_coeIdeal E).2 hle)` as an intermediate fact.

Rewrite `this` using `[hw, FractionalIdeal.count_self]`. Use linear arithmetic over natural numbers and integers. Take `⟨d, hd, hdw⟩` from `SetLike.not_le_iff_exists.1 h2`. Establish `h3 : algebraMap (𝓞 E) E d * x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[← mul_inv_cancel₀ (diffE_ne_zero (E := E))]`.

Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hd) h1`. Take `⟨m, hm⟩` from `(FractionalIdeal.mem_one_iff _).1 h3`. Establish `h4 : w.valuation E (algebraMap (𝓞 E) E m) ≤ 1` using `w.valuation_le_one (K := E) m`. Rewrite `h4` using `[hm, map_mul, (w.valuation_eq_one_iff_notMem (K := E)).2 hdw, one_mul]`. Then use the resulting hypothesis.
-/
theorem valuation_le_one_of_trace (hw : FractionalIdeal.count E w (diffE E) = 0) {x : E}
    (hx : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * x))) : w.valuation E x ≤ 1 := by
  have h1 : x ∈ (diffE E)⁻¹ := by
    unfold diffE
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx o)
    exact ⟨k, hk⟩
  have h2 : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := fun hle => by
    have := FractionalIdeal.count_mono E w (diffE_ne_zero (E := E))
      ((FractionalIdeal.coeIdeal_le_coeIdeal E).2 hle)
    rw [hw, FractionalIdeal.count_self] at this
    omega
  obtain ⟨d, hd, hdw⟩ := SetLike.not_le_iff_exists.1 h2
  have h3 : algebraMap (𝓞 E) E d * x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← mul_inv_cancel₀ (diffE_ne_zero (E := E))]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hd) h1
  obtain ⟨m, hm⟩ := (FractionalIdeal.mem_one_iff _).1 h3
  have h4 : w.valuation E (algebraMap (𝓞 E) E m) ≤ 1 := w.valuation_le_one (K := E) m
  rwa [hm, map_mul, (w.valuation_eq_one_iff_notMem (K := E)).2 hdw, one_mul] at h4

end Ideals

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

omit [NumberField F] [NumberField E] in

def formL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := form σ J x y
  map_add' a b := add_dotProduct _ _ _
  map_smul' c a := smul_dotProduct _ _ _

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem formL_apply (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) : formL σ J y x = form σ J x y := rfl

omit [NumberField E] in
/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, hJ]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem form_skew (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (x y : Fin n → E) : form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, hJ]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hu`. Use `latLoc_induction (p := fun y => Valued.v (splitVec τ y ⬝ᵥ fun i => τ (c i)) < 1) (fun a ha z hz => ?_) ?_ ?_ ?_ hy` and prove the remaining obligations. Establish `e : (splitVec τ (fun i => a ⊗ₜ[F] z i) ⬝ᵥ fun i => τ (c i)) = a * τ (z ⬝ᵥ c)`. Simplify using `[splitVec, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[e, map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ha) (h z hz)`. Simplify using `[splitVec, dotProduct]`. Introduce `y z hy hz`. Rewrite using `[splitVec_add, add_dotProduct]`. Conclude with `Valuation.map_add_lt _ hy hz`.

Introduce `y hy`. Establish `e : splitVec τ (-y) = -splitVec τ y` using `by funext r; simp [splitVec]`. Rewrite using `[e, neg_dotProduct, Valuation.map_neg]` and apply the resulting hypothesis.
-/
theorem valued_lt_one_of_mem_splitLat (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) (c : Fin n → E)
    (h : ∀ z ∈ L, Valued.v (τ (z ⬝ᵥ c)) < 1) {u : Fin n → Fv F v} (hu : u ∈ splitLat τ L) :
    Valued.v (u ⬝ᵥ fun i => τ (c i)) < 1 := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => Valued.v (splitVec τ y ⬝ᵥ fun i => τ (c i)) < 1) (fun a ha z hz => ?_)
    ?_ ?_ ?_ hy
  · have e : (splitVec τ (fun i => a ⊗ₜ[F] z i) ⬝ᵥ fun i => τ (c i)) = a * τ (z ⬝ᵥ c) := by
      simp [splitVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) (h z hz)
  · simp [splitVec, dotProduct]
  · intro y z hy hz
    rw [splitVec_add, add_dotProduct]
    exact Valuation.map_add_lt _ hy hz
  · intro y hy
    have e : splitVec τ (-y) = -splitVec τ y := by funext r; simp [splitVec]
    rwa [e, neg_dotProduct, Valuation.map_neg]

/- English proof (translation)
Establish `hcol : ∀ a : Fv F v, β.1 *ᵥ Pi.single i a = fun r => a * τ (x r)` using `fun a => by`. Use function extensionality and compare the values at `r`. Rewrite using `[Matrix.mulVec_single, ← hx r]`. Simplify using `[mul_comm]`. Use `⟨fun s hs => ?_, fun c hc => ?_⟩` and prove the remaining obligations.

Establish `h1 : β.1 *ᵥ Pi.single i (τ s) ∈ splitLat τ L`. Rewrite using `[hcol]`. Conclude with `⟨fun r => (1 : Fv F v) ⊗ₜ[F] (s • x) r, tmul_mem_latLoc (one_mem _) hs, funext fun r => by simp [splitVec]⟩`. Use `(hβ _).2 h1 i` as an intermediate fact. Rewrite `this` using `[Pi.single_eq_same]`.

Conclude with `this`. Assume the negation of the conclusion as `hcon push Not at hcon`. Establish `h1 : β.1 *ᵥ Pi.single i 1 ∈ splitLat τ L` using `(hβ _).1 fun j => by`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[e]`. Establish `h2` using `valued_lt_one_of_mem_splitLat τ L c hcon h1`. Rewrite `h2` using `[hcol]`. Establish `e : ((fun r => 1 * τ (x r)) ⬝ᵥ fun i => τ (c i)) = τ (x ⬝ᵥ c)` using `by simp [dotProduct]`.

Rewrite `h2` using `[e, hc]`. Conclude with `lt_irrefl _ h2`.
-/
theorem col_spec {τ : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) {x : Fin n → E} {i : Fin n} (hx : ∀ r, β.1 r i = τ (x r)) :
    (∀ s : E, s • x ∈ L → Valued.v (τ s) ≤ 1) ∧
      ∀ c : Fin n → E, Valued.v (τ (x ⬝ᵥ c)) = 1 → ∃ z ∈ L, 1 ≤ Valued.v (τ (z ⬝ᵥ c)) := by
  have hcol : ∀ a : Fv F v, β.1 *ᵥ Pi.single i a = fun r => a * τ (x r) := fun a => by
    funext r
    rw [Matrix.mulVec_single, ← hx r]
    simp [mul_comm]
  refine ⟨fun s hs => ?_, fun c hc => ?_⟩
  · have h1 : β.1 *ᵥ Pi.single i (τ s) ∈ splitLat τ L := by
      rw [hcol]
      exact ⟨fun r => (1 : Fv F v) ⊗ₜ[F] (s • x) r, tmul_mem_latLoc (one_mem _) hs, funext fun r => by simp [splitVec]⟩
    have := (hβ _).2 h1 i
    rw [Pi.single_eq_same] at this
    exact this
  · by_contra hcon
    push Not at hcon
    have h1 : β.1 *ᵥ Pi.single i 1 ∈ splitLat τ L := (hβ _).1 fun j => by
      by_cases e : j = i
      · subst e; simp
      · simp [e]
    have h2 := valued_lt_one_of_mem_splitLat τ L c hcon h1
    rw [hcol] at h2
    have e : ((fun r => 1 * τ (x r)) ⬝ᵥ fun i => τ (c i)) = τ (x ⬝ᵥ c) := by simp [dotProduct]
    rw [e, hc] at h2
    exact lt_irrefl _ h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH h01 h1n`. Establish `hσ` using `cm_conj_conj hB.cm`. Establish `hsk` using `form_skew hσ hY.skew`. Establish `hyx : form σ Y.J H.y H.x = -1` using `by rw [hsk, hH.xy, map_one]`. Establish `hzy : ∀ z ∈ Y.L, form σ Y.J z H.y • H.x ∈ Y.L` using `fun z hz => by`.

Take `⟨a, t, u, ha, -, -, rfl⟩` from `hH.split z hz`. Establish `: formL σ Y.J H.y (a • H.x + H.ι *ᵥ u + t • H.y) = a`. Rewrite using `[map_add, map_add, map_smul, map_smul]`. Simplify using `[formL_apply, hH.xy, hH.yy, (hH.orth u).2]`. Rewrite using `[show form σ Y.J _ H.y = a from this]` and apply the resulting hypothesis.

Establish `hzx : ∀ z ∈ Y.L, form σ Y.J z H.x • H.y ∈ Y.L` using `fun z hz => by`. Take `⟨a, t, u, -, ht, -, rfl⟩` from `hH.split z hz`. Establish `: formL σ Y.J H.x (a • H.x + H.ι *ᵥ u + t • H.y) = -t`. Rewrite using `[map_add, map_add, map_smul, map_smul]`. Simplify using `[formL_apply, hH.xx, hyx, (hH.orth u).1]`.

Rewrite using `[show form σ Y.J _ H.x = -t from this, neg_smul]`. Conclude with `neg_mem ht`. Use `⟨fun h0 => ?_, fun v hv w hw => ?_⟩` and prove the remaining obligations. Establish `h1 : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.ker (formL σ Y.J H.y)`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Use `(hH.ideal _).2 (hzy z hz)` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify `this` using `[formL_apply]`. Use `haveI := hY.lat`.

Rewrite `h1` using `[Submodule.IsLattice.span_eq_top]`. Use `h1 (Submodule.mem_top (x := H.x))` as an intermediate fact. Simplify using `[formL_apply, hH.xy] at this`. Use `set τ := B.τ ⟨v, hv⟩ with hτ`. Take `⟨hx1, hx2⟩` from `col_spec (hY.bas ⟨v, hv⟩) ((hH.bas ⟨v, hv⟩ ⟨i₀, h01.trans h1n⟩).1 rfl)`.

Take `⟨hy1, hy2⟩` from `col_spec (hY.bas ⟨v, hv⟩) ((hH.bas ⟨v, hv⟩ ⟨i₁, h1n⟩).2.1 rfl)`. Establish `hm : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E)` using `⟨w.isPrime, ⟨hw ▸ rfl⟩⟩`. Rewrite `hm` using `[primesOver_eq_split hB.cm τ]`. Break down `hm with e | e` into its components or cases. Take `rfl : w = splitPrime τ` from `HeightOneSpectrum.ext e`.

Take `⟨z, hz, hz1⟩` from `hx2 (Y.J *ᵥ fun i => σ (H.y i)) (by`. Express the relevant statement in the definitionally equal form `Valued.v (τ (form σ Y.J H.x H.y)) = 1`. Rewrite using `[hH.xy]`. Use the proof step `simp)`. Use `count_eq_zero _ (fun a ha => ?_) ((hH.ideal _).2 (hzy z hz)) ?_` and prove the remaining obligations.

Rewrite using `[← valued_apply_eq_valuation]`. Conclude with `hx1 a ((hH.ideal a).1 ha)`. Rewrite using `[← valued_apply_eq_valuation]`. Conclude with `le_antisymm (hx1 _ (hzy z hz)) hz1`. Take `rfl : w = splitPrime (τ.comp σ)` from `HeightOneSpectrum.ext e`.

Establish `hD` using `GlobalTheory.T.different_coprime_at_good_places σ B hB v hv _ hw`. Take `⟨z, hz, hz1⟩` from `hy2 (Y.J *ᵥ fun i => σ (H.x i)) (by`. Express the relevant statement in the definitionally equal form `Valued.v (τ (form σ Y.J H.y H.x)) = 1`. Rewrite using `[hyx]`. Use the proof step `simp)`.

Establish `hz2 : Valued.v (τ (form σ Y.J z H.x)) = 1` using `le_antisymm (hy1 _ (hzx z hz)) hz1`. Use `haveI := hY.lat`. Take `⟨d, hd, hdL⟩` from `exists_den (splitPrime τ) (N := Y.L.map ((formL σ Y.J H.x).restrictScalars (𝓞 E))) (Submodule.IsLattice.fg.map _) (by`. Introduce and unpack `_ ⟨z', hz', rfl⟩`. Rewrite using `[← valued_apply_eq_valuation]`.

Conclude with `hy1 _ (hzx z' hz'))`. Establish `hsm : ∀ (a : E) z', form σ Y.J (a • H.x) z' = -(a * σ (form σ Y.J z' H.x))` using `fun a z' => by`. Use `(formL σ Y.J z').map_smul a H.x` as an intermediate fact. Rewrite using `[show form σ Y.J (a • H.x) z' = a * form σ Y.J H.x z' from this, hsk H.x, mul_neg]`. Use `count_eq_zero _ (u := σ d) (fun a ha => ?_) ((hH.ideal _).2 ((hY.dual _).2 fun z' hz' o => ?_)) ?_` and prove the remaining obligations.

Establish `h1` using `valuation_le_one_of_trace _ hD ((hY.dual _).1 ((hH.ideal a).1 ha) z hz)`. Rewrite `h1` using `[hsm, Valuation.map_neg, map_mul, ← valued_apply_eq_valuation _ (σ _), AlgHom.comp_apply, hσ, hz2, mul_one]`. Conclude with `h1`. Take `⟨m, hm⟩` from `hdL _ ⟨z', hz', rfl⟩`. Establish `hm' : (d : E) * form σ Y.J z' H.x = m` using `hm`.

Rewrite using `[hsm, ← map_mul, hm']`. Conclude with `Algebra.isIntegral_trace (o * -conjO σ m : 𝓞 E).2`. Rewrite using `[← valued_apply_eq_valuation, AlgHom.comp_apply, hσ, valued_apply_eq_valuation]`. Conclude with `((splitPrime τ).valuation_eq_one_iff_notMem (K := E)).2 hd`.
-/
theorem ideal_ne_zero_and_count_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ), B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < i₁ → i₁ < n → H.𝔟 ≠ 0 ∧ ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH h01 h1n
  have hσ := cm_conj_conj hB.cm
  have hsk := form_skew hσ hY.skew
  have hyx : form σ Y.J H.y H.x = -1 := by rw [hsk, hH.xy, map_one]
  have hzy : ∀ z ∈ Y.L, form σ Y.J z H.y • H.x ∈ Y.L := fun z hz => by
    obtain ⟨a, t, u, ha, -, -, rfl⟩ := hH.split z hz
    have : formL σ Y.J H.y (a • H.x + H.ι *ᵥ u + t • H.y) = a := by
      rw [map_add, map_add, map_smul, map_smul]
      simp [formL_apply, hH.xy, hH.yy, (hH.orth u).2]
    rwa [show form σ Y.J _ H.y = a from this]
  have hzx : ∀ z ∈ Y.L, form σ Y.J z H.x • H.y ∈ Y.L := fun z hz => by
    obtain ⟨a, t, u, -, ht, -, rfl⟩ := hH.split z hz
    have : formL σ Y.J H.x (a • H.x + H.ι *ᵥ u + t • H.y) = -t := by
      rw [map_add, map_add, map_smul, map_smul]
      simp [formL_apply, hH.xx, hyx, (hH.orth u).1]
    rw [show form σ Y.J _ H.x = -t from this, neg_smul]
    exact neg_mem ht
  refine ⟨fun h0 => ?_, fun v hv w hw => ?_⟩
  · have h1 : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.ker (formL σ Y.J H.y) := by
      rw [Submodule.span_le]
      intro z hz
      have := (hH.ideal _).2 (hzy z hz)
      rw [h0] at this
      simpa [formL_apply] using this
    haveI := hY.lat
    rw [Submodule.IsLattice.span_eq_top] at h1
    have := h1 (Submodule.mem_top (x := H.x))
    simp [formL_apply, hH.xy] at this
  set τ := B.τ ⟨v, hv⟩ with hτ
  obtain ⟨hx1, hx2⟩ := col_spec (hY.bas ⟨v, hv⟩) ((hH.bas ⟨v, hv⟩ ⟨i₀, h01.trans h1n⟩).1 rfl)
  obtain ⟨hy1, hy2⟩ := col_spec (hY.bas ⟨v, hv⟩) ((hH.bas ⟨v, hv⟩ ⟨i₁, h1n⟩).2.1 rfl)
  have hm : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨hw ▸ rfl⟩⟩
  rw [primesOver_eq_split hB.cm τ] at hm
  rcases hm with e | e
  · obtain rfl : w = splitPrime τ := HeightOneSpectrum.ext e
    obtain ⟨z, hz, hz1⟩ := hx2 (Y.J *ᵥ fun i => σ (H.y i)) (by
      change Valued.v (τ (form σ Y.J H.x H.y)) = 1
      rw [hH.xy]; simp)
    refine count_eq_zero _ (fun a ha => ?_) ((hH.ideal _).2 (hzy z hz)) ?_
    · rw [← valued_apply_eq_valuation]; exact hx1 a ((hH.ideal a).1 ha)
    · rw [← valued_apply_eq_valuation]; exact le_antisymm (hx1 _ (hzy z hz)) hz1
  · obtain rfl : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext e
    have hD := GlobalTheory.T.different_coprime_at_good_places σ B hB v hv _ hw
    obtain ⟨z, hz, hz1⟩ := hy2 (Y.J *ᵥ fun i => σ (H.x i)) (by
      change Valued.v (τ (form σ Y.J H.y H.x)) = 1
      rw [hyx]; simp)
    have hz2 : Valued.v (τ (form σ Y.J z H.x)) = 1 := le_antisymm (hy1 _ (hzx z hz)) hz1
    haveI := hY.lat
    obtain ⟨d, hd, hdL⟩ := exists_den (splitPrime τ)
      (N := Y.L.map ((formL σ Y.J H.x).restrictScalars (𝓞 E))) (Submodule.IsLattice.fg.map _) (by
        rintro _ ⟨z', hz', rfl⟩
        rw [← valued_apply_eq_valuation]
        exact hy1 _ (hzx z' hz'))
    have hsm : ∀ (a : E) z', form σ Y.J (a • H.x) z' = -(a * σ (form σ Y.J z' H.x)) := fun a z' => by
      have := (formL σ Y.J z').map_smul a H.x
      rw [show form σ Y.J (a • H.x) z' = a * form σ Y.J H.x z' from this, hsk H.x, mul_neg]
    refine count_eq_zero _ (u := σ d) (fun a ha => ?_) ((hH.ideal _).2 ((hY.dual _).2 fun z' hz' o => ?_)) ?_
    · have h1 := valuation_le_one_of_trace _ hD ((hY.dual _).1 ((hH.ideal a).1 ha) z hz)
      rw [hsm, Valuation.map_neg, map_mul, ← valued_apply_eq_valuation _ (σ _), AlgHom.comp_apply, hσ, hz2,
        mul_one] at h1
      exact h1
    · obtain ⟨m, hm⟩ := hdL _ ⟨z', hz', rfl⟩
      have hm' : (d : E) * form σ Y.J z' H.x = m := hm
      rw [hsm, ← map_mul, hm']
      exact Algebra.isIntegral_trace (o * -conjO σ m : 𝓞 E).2
    · rw [← valued_apply_eq_valuation, AlgHom.comp_apply, hσ, valued_apply_eq_valuation]
      exact ((splitPrime τ).valuation_eq_one_iff_notMem (K := E)).2 hd

end GlobalTheory.PlaneSkewIdeal
