import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CellFaces

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

omit [Module O X] [Module.Finite O X] in

/- English proof (translation)
Establish `hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((u i a b : ℤ) : ℝ)`. Introduce `a b`. Use `congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B a b) hβ` as an intermediate fact. Simplify `this` using `[toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply]`. Establish `hπ : ∀ (π : ℝ →ₗ[ℚ] ℚ) (x : ℝ) (n : ℤ), π (x * (n : ℝ)) = π x * (n : ℚ)`.

Introduce `π x n`. Rewrite using `[mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]`. Establish `hrat : ∀ π : ℝ →ₗ[ℚ] ℚ, π 1 * (F β : ℚ) = ∑ i, π (c i) * (F (u i) : ℚ)`. Introduce `π`. Establish `hq : ∀ a b : X, π 1 * ((β a b : ℤ) : ℚ) = ∑ i, π (c i) * ((u i a b : ℤ) : ℚ)`.

Introduce `a b`. Establish `h1` using `congrArg π (hpt a b)`. Rewrite `h1` using `[← one_mul ((β a b : ℤ) : ℝ), hπ, map_sum]`. Simplify `h1` using `only [hπ]`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) (Finset.univ : Finset (Option (Fin m))) (fun o : Option (Fin m) => o.elim (π 1) (fun i => π (c i)))`.

Use `choose z hz using fun o => hb o (Finset.mem_univ o)`. Establish `hz' : ∀ o, ((z o : ℤ) : ℚ) = ((b : ℤ) : ℚ) * o.elim (π 1) (fun i => π (c i))`. Introduce `o`. Simplify `hz o` using `[zsmul_eq_mul]`. Establish `hint : z none • β = ∑ i, z (some i) • u i`.

Use extensionality with `x y`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz', Option.elim_none, Option.elim_some]`. Rewrite using `[mul_assoc, hq x y, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Establish `h2` using `congrArg (fun β => ((F β : ℤ) : ℚ)) hint`. Simplify using `only [map_zsmul, map_sum, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz', Option.elim_none, Option.elim_some] at h2`. Establish `hb0 : ((b : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.ne_zero b.2`. Apply `mul_left_cancel₀ hb0` to reduce the goal to its premises. Rewrite using `[Finset.mul_sum, ← mul_assoc, h2]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hr : ∑ i, c i * (F (u i) : ℝ) - (F β : ℝ) = 0`. Use `(Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun π => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_sum, ← one_mul ((F β : ℤ) : ℝ), hπ]`. Simplify using `only [hπ]`.

Rewrite using `[← hrat π]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((u i a b : ℤ) : ℝ) := by
    intro a b
    have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B a b) hβ
    simpa [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hπ : ∀ (π : ℝ →ₗ[ℚ] ℚ) (x : ℝ) (n : ℤ), π (x * (n : ℝ)) = π x * (n : ℚ) := by
    intro π x n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have hrat : ∀ π : ℝ →ₗ[ℚ] ℚ, π 1 * (F β : ℚ) = ∑ i, π (c i) * (F (u i) : ℚ) := by
    intro π
    have hq : ∀ a b : X, π 1 * ((β a b : ℤ) : ℚ) = ∑ i, π (c i) * ((u i a b : ℤ) : ℚ) := by
      intro a b
      have h1 := congrArg π (hpt a b)
      rw [← one_mul ((β a b : ℤ) : ℝ), hπ, map_sum] at h1
      simpa only [hπ] using h1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Option (Fin m))) (fun o : Option (Fin m) => o.elim (π 1) (fun i => π (c i)))
    choose z hz using fun o => hb o (Finset.mem_univ o)
    have hz' : ∀ o, ((z o : ℤ) : ℚ) = ((b : ℤ) : ℚ) * o.elim (π 1) (fun i => π (c i)) := by
      intro o
      simpa [zsmul_eq_mul] using hz o
    have hint : z none • β = ∑ i, z (some i) • u i := by
      ext x y
      apply Int.cast_injective (α := ℚ)
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz',
        Option.elim_none, Option.elim_some]
      rw [mul_assoc, hq x y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 := congrArg (fun β => ((F β : ℤ) : ℚ)) hint
    simp only [map_zsmul, map_sum, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz', Option.elim_none,
      Option.elim_some] at h2
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
    apply mul_left_cancel₀ hb0
    rw [Finset.mul_sum, ← mul_assoc, h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hr : ∑ i, c i * (F (u i) : ℝ) - (F β : ℝ) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun π => ?_
    rw [map_sub, map_sum, ← one_mul ((F β : ℤ) : ℝ), hπ]
    simp only [hπ]
    rw [← hrat π]
    ring
  linarith

/- English proof (translation)
Establish `hle'` using `hle u hu hp`. Establish `hhC` using `hC u hu hp`. Rewrite `hle'`, `hb`, the goal using `[hn]`. Establish `hleZ : (N : ℤ) * n ≤ ℓ u` using `by exact_mod_cast hle'`. Establish `hC0 : (0 : ℝ) ≤ C` using `Nat.cast_nonneg C`.

Break down `hleZ.lt_or_eq with hlt | heq` into its components or cases. Establish `h1 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u` using `hlt`. Establish `h1R : (N : ℝ) * n + 1 ≤ (ℓ u : ℝ)` using `by exact_mod_cast h1`. Establish `hLC : (C : ℝ) * (B0 + 1) ≤ L - C` using `by linarith`. Establish `hLC0 : (0 : ℝ) ≤ L - C` using `le_trans (mul_nonneg hC0 (by linarith)) hLC`.

Establish `k1 : (L - C) * 1 ≤ (L - C) * ((ℓ u : ℝ) - N * n)` using `mul_le_mul_of_nonneg_left (by linarith) hLC0`. Establish `k2 : (C : ℝ) * (N * n) ≤ C * B0` using `mul_le_mul_of_nonneg_left hb hC0`. Use polynomial arithmetic with `[k1, k2, hhC, hLC]`. Establish `heqR : (N : ℝ) * ψ.evalZ u = ℓ u` using `by rw [hn]; exact_mod_cast heq`. Take `⟨k, c, hk, hkc⟩` from `hstr u hu hp heqR`.

Establish `hsum : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (γ i)`. Use `congrArg h hkc` as an intermediate fact. Simplify `this` using `[map_nsmul, map_sum, nsmul_eq_mul]`. Establish `hnn : 0 ≤ ∑ i, (c i : ℤ) * h (γ i)` using `Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hγ i)`. Establish `hhu : 0 ≤ h u`.

Assume the negation of the conclusion as `hneg`. Establish `: (k : ℤ) * h u < 0` using `mul_neg_of_pos_of_neg (by exact_mod_cast hk) (not_le.mp hneg)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hhuR : (0 : ℝ) ≤ h u` using `by exact_mod_cast hhu`. Establish `hℓR : ((ℓ u : ℤ) : ℝ) = (N : ℝ) * n` using `by exact_mod_cast heq.symm`.

Rewrite using `[hℓR]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  have hle' := hle u hu hp
  have hhC := hC u hu hp
  rw [hn] at hle' hb ⊢
  have hleZ : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle'
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  rcases hleZ.lt_or_eq with hlt | heq
  · have h1 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := hlt
    have h1R : (N : ℝ) * n + 1 ≤ (ℓ u : ℝ) := by exact_mod_cast h1
    have hLC : (C : ℝ) * (B0 + 1) ≤ L - C := by linarith
    have hLC0 : (0 : ℝ) ≤ L - C := le_trans (mul_nonneg hC0 (by linarith)) hLC
    have k1 : (L - C) * 1 ≤ (L - C) * ((ℓ u : ℝ) - N * n) :=
      mul_le_mul_of_nonneg_left (by linarith) hLC0
    have k2 : (C : ℝ) * (N * n) ≤ C * B0 := mul_le_mul_of_nonneg_left hb hC0
    nlinarith [k1, k2, hhC, hLC]
  · have heqR : (N : ℝ) * ψ.evalZ u = ℓ u := by rw [hn]; exact_mod_cast heq
    obtain ⟨k, c, hk, hkc⟩ := hstr u hu hp heqR
    have hsum : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (γ i) := by
      have := congrArg h hkc
      simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hnn : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hγ i)
    have hhu : 0 ≤ h u := by
      by_contra hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) (not_le.mp hneg)
      linarith
    have hhuR : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
    have hℓR : ((ℓ u : ℤ) : ℝ) = (N : ℝ) * n := by exact_mod_cast heq.symm
    rw [hℓR]
    linarith

/- English proof (translation)
Introduce `O _ _ _ _ bar _ ψ X _ _ _ hfan hdom m m' γ s h hcell hface`. Take `⟨hmem, hnn, hlin, hstrict⟩` from `hcell`. Take `⟨N, ℓ, hN, hℓγ, hle, hstr⟩` from `hstrict`. Take `⟨hh0, hhz⟩` from `hface`. Establish `reidx : ∀ (c' : Fin m' → ℝ) (f : Fin m → ℝ), ∑ j, Function.extend s c' 0 j * f j = ∑ i, c' i * f (s i)`.

Introduce `c' f`. Use `((Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => ?_).symm.trans (Finset.sum_map Finset.univ s (fun j => Function.extend s c' 0 j * f j))).trans ?_` and prove the remaining obligations. Rewrite using `[Function.extend_apply' _ _ _ (by simpa using hj), Pi.zero_apply, zero_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [s.injective.extend_apply]`. Establish `hext_nn : ∀ c' : Fin m' → ℝ, (∀ i, 0 ≤ c' i) → ∀ j, 0 ≤ Function.extend s c' 0 j`.

Introduce `c' hc' j`. Distinguish the cases in `hj : ∃ i, s i = j`. Take `⟨i, rfl⟩` from `hj`. Rewrite using `[s.injective.extend_apply]`. Conclude with `hc' i`.

Rewrite using `[Function.extend_apply' _ _ _ hj]`. Conclude with `le_refl _`. Establish `hlin' : ψ.LinearOn (fun i => γ (s i))`. Introduce `c' hc'`. Establish `hl` using `hlin (Function.extend s c' 0) (hext_nn c' hc')`.

Use `show ψ.eval X (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) = ∑ i, c' i * ψ.evalZ (γ (s i))`. Establish `e1 : (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) = (fun a b => ∑ j, Function.extend s c' 0 j * ((γ j a b : ℤ) : ℝ))`. Use function extensionality and compare the values at `a b`. Rewrite using `[reidx c' (fun j => ((γ j a b : ℤ) : ℝ))]`. Rewrite using `[e1, hl, reidx c' (fun j => ψ.evalZ (γ j))]`.

Establish `hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β`. Introduce `β hβ hp hne`. Establish `h1` using `hle β hβ hp`. Establish `h2` using `hfan.pos β hβ hp hne`. Establish `hNR : (0 : ℝ) < N` using `by exact_mod_cast hN`.

Establish `: (0 : ℝ) < ℓ β` using `lt_of_lt_of_le (mul_pos hNR h2) h1`. Conclude with `this` after adjusting the coercions. Take `⟨C, hC⟩` from `hdom ℓ (-h) hpos`. Establish `hCR : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β`. Introduce `β hβ hp`.

Use `hC β hβ hp` as an intermediate fact. Rewrite `this` using `[LinearMap.neg_apply]`. Conclude with `this` after adjusting the coercions. Take `⟨S, hSfin, hcov⟩` from `hfan.finite`. Use `set B0 : ℝ := ∑ x ∈ hSfin.toFinset, |(N : ℝ) * ψ.evalZ x| with hB0def`.

Establish `hB0 : 0 ≤ B0` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hB0ge : ∀ x ∈ S, (N : ℝ) * ψ.evalZ x ≤ B0` using `fun x hx => (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |(N : ℝ) * ψ.evalZ x|) (fun _ _ => abs_nonneg _) (hSfin.mem_toFinset.mpr hx))`. Establish `key : ∀ L : ℝ, (C : ℝ) * (B0 + 1) + C ≤ L → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → L * (N * ψ.evalZ β) ≤ L * ℓ β + h β`. Introduce `L hL β hβ hp`. Establish `hB : toReal β ∈ psdCone bar X`.

Use `GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 (fun _ => β) (fun _ => 1) (fun _ => hβ) (fun _ => hp) (fun _ => zero_le_one)` as an intermediate fact. Simplify using `using this`. Take `⟨e, k, γ', c, hcell', hS', hc', heq⟩` from `hcov _ hB`. Establish `hsurj : Function.Surjective (e.symm : X →ₗ[O] X)` using `fun x => ⟨e x, by simp⟩`. Establish `hcellu : IsCell bar ψ (fun i => pull (e.symm : X →ₗ[O] X) (γ' i))` using `isCell_pull_equiv hcell' e.symm`.

Establish `hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((pull (e.symm : X →ₗ[O] X) (γ' i) a b : ℤ) : ℝ)`. Introduce `a b`. Use `congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B (e.symm a) (e.symm b)) heq` as an intermediate fact. Simplify `this` using `[pullR, pull_apply, toReal_apply, LinearMap.sum_apply]`. Establish `hrel : toReal β = ∑ i, c i • toReal (pull (e.symm : X →ₗ[O] X) (γ' i))`.

Use extensionality with `a b`. Simplify `hpt a b` using `[toReal_apply, LinearMap.sum_apply]`. Establish `hℓ` using `apply_eq_sum_of_toReal hrel ℓ`. Establish `hh` using `apply_eq_sum_of_toReal hrel h`. Establish `hφ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i))`.

Rewrite using `[← hcellu.linear c hc']`. Use `show ψ.eval X (fun a b => ((β a b : ℤ) : ℝ)) = _`. Use `congr 1`. Use function extensionality and compare the values at `a b`. Conclude with `hpt a b`.

Establish `hest : ∀ i, L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i))) ≤ L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i))`. Introduce `i`. Take `⟨n, hn⟩` from `hfan.integral _ (hcellu.mem i) (hcellu.nonneg i)`. Establish `hbi : (N : ℝ) * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) ≤ B0`. Rewrite using `[evalZ_pull ψ hsurj]`.

Conclude with `hB0ge _ (hS' i)`. Conclude with `est_at (bar := bar) hstr hle hh0 hCR (hcellu.mem i) (hcellu.nonneg i) n hn hbi hB0 hL`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hφ, Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Use `_ ≤ ∑ i, c i * (L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i))) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hest i) (hc' i)`. Use `_ = L * ℓ β + h β := by`. Rewrite using `[hℓ, hh, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hL0` using `Nat.le_ceil ((C : ℝ) * (B0 + 1) + C)`.

Use `set L0 : ℕ := ⌈(C : ℝ) * (B0 + 1) + C⌉₊ with hL0def`. Establish `reidxN : ∀ c : Fin m → ℕ, (∀ j, j ∉ Set.range s → c j = 0) → ∑ j, c j • γ j = ∑ i, c (s i) • γ (s i)`. Introduce `c hc`. Conclude with `(Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => by`. Rewrite using `[hc j (by simpa using hj), zero_smul]).symm.trans (Finset.sum_map Finset.univ s (fun j => c j • γ j))`.

Use `⟨fun i => hmem (s i), fun i => hnn (s i), hlin', ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.PolFan.IsStrict`. Use `⟨(L0 + 1) * N, ((L0 + 1 : ℕ) : ℤ) • ℓ + h, Nat.mul_pos (Nat.succ_pos _) hN, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Establish `hz : h (γ (s i)) = 0` using `(hhz (s i)).mpr ⟨i, rfl⟩`.

Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, hz, add_zero, smul_eq_mul]`. Use `push_cast`. Rewrite using `[hℓγ (s i)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `β hβ hp`.

Establish `hA` using `key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Move the coercions through the operations in `at hA ⊢`. Use polynomial arithmetic with `[hA]`. Introduce `β hβ hp heqβ`.

Establish `hA` using `key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp`. Establish `hB` using `key (L0 : ℝ) hL0 β hβ hp`. Establish `hle'` using `hle β hβ hp`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heqβ`. Move the coercions through the operations in `at heqβ hA`.

Establish `hd : (N : ℝ) * ψ.evalZ β = ℓ β` using `by nlinarith [hB, heqβ, hle']`. Establish `hh0β : (h β : ℝ) = 0` using `by nlinarith [hB, heqβ, hd]`. Take `⟨k, c, hk, hkc⟩` from `hstr β hβ hp hd`. Establish `hsum : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (γ j)`. Use `congrArg h hkc` as an intermediate fact.

Simplify `this` using `[map_nsmul, map_sum, nsmul_eq_mul]`. Establish `hhβ : h β = 0` using `by exact_mod_cast hh0β`. Rewrite `hsum` using `[hhβ, mul_zero]`. Establish `hterm` using `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (Int.natCast_nonneg (c j)) (hh0 j))).mp hsum.symm`. Establish `hc0 : ∀ j, j ∉ Set.range s → c j = 0`.

Introduce `j hj`. Establish `h2 : h (γ j) ≠ 0` using `fun h0 => hj ((hhz j).mp h0)`. Break down `mul_eq_zero.mp (hterm j (Finset.mem_univ j)) with h3 | h3` into its components or cases. Conclude with `h3` after adjusting the coercions. Conclude with `absurd h3 h2`.

Conclude with `⟨k, fun i => c (s i), hk, hkc.trans (reidxN c hc0)⟩`.
-/
theorem isCell_comp : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar ψ X → Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i)) := by
  intro O _ _ _ _ bar _ ψ X _ _ _ hfan hdom m m' γ s h hcell hface
  obtain ⟨hmem, hnn, hlin, hstrict⟩ := hcell
  obtain ⟨N, ℓ, hN, hℓγ, hle, hstr⟩ := hstrict
  obtain ⟨hh0, hhz⟩ := hface
  have reidx : ∀ (c' : Fin m' → ℝ) (f : Fin m → ℝ),
      ∑ j, Function.extend s c' 0 j * f j = ∑ i, c' i * f (s i) := by
    intro c' f
    refine ((Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => ?_).symm.trans
      (Finset.sum_map Finset.univ s (fun j => Function.extend s c' 0 j * f j))).trans ?_
    · rw [Function.extend_apply' _ _ _ (by simpa using hj), Pi.zero_apply, zero_mul]
    · exact Finset.sum_congr rfl fun i _ => by rw [s.injective.extend_apply]
  have hext_nn : ∀ c' : Fin m' → ℝ, (∀ i, 0 ≤ c' i) → ∀ j, 0 ≤ Function.extend s c' 0 j := by
    intro c' hc' j
    by_cases hj : ∃ i, s i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [s.injective.extend_apply]
      exact hc' i
    · rw [Function.extend_apply' _ _ _ hj]
      exact le_refl _
  have hlin' : ψ.LinearOn (fun i => γ (s i)) := by
    intro c' hc'
    have hl := hlin (Function.extend s c' 0) (hext_nn c' hc')
    show ψ.eval X (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) = ∑ i, c' i * ψ.evalZ (γ (s i))
    have e1 : (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) =
        (fun a b => ∑ j, Function.extend s c' 0 j * ((γ j a b : ℤ) : ℝ)) := by
      funext a b
      rw [reidx c' (fun j => ((γ j a b : ℤ) : ℝ))]
    rw [e1, hl, reidx c' (fun j => ψ.evalZ (γ j))]
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := by
    intro β hβ hp hne
    have h1 := hle β hβ hp
    have h2 := hfan.pos β hβ hp hne
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNR h2) h1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hdom ℓ (-h) hpos
  have hCR : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := by
    intro β hβ hp
    have := hC β hβ hp
    rw [LinearMap.neg_apply] at this
    exact_mod_cast this
  obtain ⟨S, hSfin, hcov⟩ := hfan.finite
  set B0 : ℝ := ∑ x ∈ hSfin.toFinset, |(N : ℝ) * ψ.evalZ x| with hB0def
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0ge : ∀ x ∈ S, (N : ℝ) * ψ.evalZ x ≤ B0 := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |(N : ℝ) * ψ.evalZ x|)
      (fun _ _ => abs_nonneg _) (hSfin.mem_toFinset.mpr hx))
  have key : ∀ L : ℝ, (C : ℝ) * (B0 + 1) + C ≤ L → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hB : toReal β ∈ psdCone bar X := by
      have := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 (fun _ => β) (fun _ => 1)
        (fun _ => hβ) (fun _ => hp) (fun _ => zero_le_one)
      simpa using this
    obtain ⟨e, k, γ', c, hcell', hS', hc', heq⟩ := hcov _ hB
    have hsurj : Function.Surjective (e.symm : X →ₗ[O] X) := fun x => ⟨e x, by simp⟩
    have hcellu : IsCell bar ψ (fun i => pull (e.symm : X →ₗ[O] X) (γ' i)) := isCell_pull_equiv hcell' e.symm
    have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((pull (e.symm : X →ₗ[O] X) (γ' i) a b : ℤ) : ℝ) := by
      intro a b
      have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B (e.symm a) (e.symm b)) heq
      simpa [pullR, pull_apply, toReal_apply, LinearMap.sum_apply] using this
    have hrel : toReal β = ∑ i, c i • toReal (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      ext a b
      simpa [toReal_apply, LinearMap.sum_apply] using hpt a b
    have hℓ := apply_eq_sum_of_toReal hrel ℓ
    have hh := apply_eq_sum_of_toReal hrel h
    have hφ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      rw [← hcellu.linear c hc']
      show ψ.eval X (fun a b => ((β a b : ℤ) : ℝ)) = _
      congr 1
      funext a b
      exact hpt a b
    have hest : ∀ i, L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i))) ≤
        L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      intro i
      obtain ⟨n, hn⟩ := hfan.integral _ (hcellu.mem i) (hcellu.nonneg i)
      have hbi : (N : ℝ) * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) ≤ B0 := by
        rw [evalZ_pull ψ hsurj]
        exact hB0ge _ (hS' i)
      exact est_at (bar := bar) hstr hle hh0 hCR (hcellu.mem i) (hcellu.nonneg i) n hn hbi hB0 hL
    calc L * (N * ψ.evalZ β)
        = ∑ i, c i * (L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)))) := by
          rw [hφ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, c i * (L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hest i) (hc' i)
      _ = L * ℓ β + h β := by
          rw [hℓ, hh, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hL0 := Nat.le_ceil ((C : ℝ) * (B0 + 1) + C)
  set L0 : ℕ := ⌈(C : ℝ) * (B0 + 1) + C⌉₊ with hL0def
  have reidxN : ∀ c : Fin m → ℕ, (∀ j, j ∉ Set.range s → c j = 0) →
      ∑ j, c j • γ j = ∑ i, c (s i) • γ (s i) := by
    intro c hc
    exact (Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => by
      rw [hc j (by simpa using hj), zero_smul]).symm.trans (Finset.sum_map Finset.univ s (fun j => c j • γ j))
  refine ⟨fun i => hmem (s i), fun i => hnn (s i), hlin', ?_⟩
  unfold GlobalTheory.PolFan.IsStrict
  refine ⟨(L0 + 1) * N, ((L0 + 1 : ℕ) : ℤ) • ℓ + h, Nat.mul_pos (Nat.succ_pos _) hN, ?_, ?_, ?_⟩
  · intro i
    have hz : h (γ (s i)) = 0 := (hhz (s i)).mpr ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hz, add_zero, smul_eq_mul]
    push_cast
    rw [hℓγ (s i)]
    ring
  · intro β hβ hp
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast at hA ⊢
    nlinarith [hA]
  · intro β hβ hp heqβ
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    have hB := key (L0 : ℝ) hL0 β hβ hp
    have hle' := hle β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heqβ
    push_cast at heqβ hA
    have hd : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith [hB, heqβ, hle']
    have hh0β : (h β : ℝ) = 0 := by nlinarith [hB, heqβ, hd]
    obtain ⟨k, c, hk, hkc⟩ := hstr β hβ hp hd
    have hsum : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (γ j) := by
      have := congrArg h hkc
      simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hhβ : h β = 0 := by exact_mod_cast hh0β
    rw [hhβ, mul_zero] at hsum
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (Int.natCast_nonneg (c j)) (hh0 j))).mp hsum.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := by
      intro j hj
      have h2 : h (γ j) ≠ 0 := fun h0 => hj ((hhz j).mp h0)
      rcases mul_eq_zero.mp (hterm j (Finset.mem_univ j)) with h3 | h3
      · exact_mod_cast h3
      · exact absurd h3 h2
    exact ⟨k, fun i => c (s i), hk, hkc.trans (reidxN c hc0)⟩

end GlobalTheory.CompanionTheory.Ar.Fan.CellFaces
