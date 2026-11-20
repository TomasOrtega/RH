import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.JSBoundStep

/- English proof (translation)
Introduce `h0 h3 h3c`. Unfold `FormHermitianPositive ForR ForF`. Introduce `F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm l k B B' hk hW hI hC`. Unfold `L0 ForF at h0`. Unfold `L3 ForR ForF at h3`.

Unfold `ColumnsMirabolic ForF at h3c`. Take `⟨-, hlat⟩` from `h0 F μ ψ hψ`. Take `⟨hlatM, hcv⟩` from `hlat (k + 1)`. Establish `h3'` using `h3 F μ ψ hψ n V ρ hsm`. Take `⟨hcadd, hc0, hcP, -, -, -⟩` from `h3c F μ ψ hψ n k hk`.

Take `⟨herm, psd, null, quasi, -⟩` from `hI`. Use `clear h0 h3 h3c hlat`. Establish `hψinv : ∀ t : F, ψ (-t) * ψ t = 1` using `fun t => by`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`. Establish `hψconj : ∀ t : F, conj (ψ (-t)) = ψ t`.

Introduce `t`. Establish `hn : ‖ψ (-t)‖ = 1` using `hψ.2.2 (-t)`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ∀ (x : Fin (k + 1) → F) (b : V), ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) = b`. Introduce `x b`.

Establish `h1 : PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x) = 1`. Rewrite using `[← hcadd, add_neg_cancel, hc0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : ∀ (x : Fin (k + 1) → F) (a b : V), B (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a) b = B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)`. Introduce `x a b`.

Establish `hq` using `quasi (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).1 a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)`. Rewrite `hq` using `[hinv, (hcP x).2.2.1, map_one]`. Simplify using `using hq`. Establish `hnegS : ∀ (M : ℕ), ∀ x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, -x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M`. Introduce `M x hx`.

Simplify using `only [PositivityTheory.JacquetShalikaLocal.lat, Set.mem_setOf_eq, Pi.neg_apply, mul_neg] at hx ⊢`. Conclude with `fun i => neg_mem (hx i)`. Establish `hvol : ∀ M : ℕ, 0 < (Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M)` using `fun M => (hlatM M).2.2.2`. Establish `hmeas : ∀ M : ℕ, MeasurableSet (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M)` using `fun M => (hlatM M).2.2.1`. Establish `hvol' : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) = (((Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) : ℝ) : ℂ)`.

Introduce `M`. Rewrite using `[setIntegral_const]`. Simplify using the standard rewrite rules. Establish `hv : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) ≠ 0`. Introduce `M`.

Rewrite using `[hvol' M]`. Conclude with `Complex.ofReal_ne_zero.mpr (hvol M).ne'`. Establish `hmv : ∀ x : Fin (k + 1) → F, (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x = -x`. Introduce `x`. Rewrite using `[Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]`.

Establish `hcvS : ∀ (M : ℕ) (f : (Fin (k + 1) → F) → ℂ), ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f (-x) ∂(Measure.pi fun _ => μ) = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f x ∂(Measure.pi fun _ => μ)`. Introduce `M f`. Establish `himg : (fun x => (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x) '' PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M = PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `only [hmv]`. Conclude with `hnegS M y hy`. Introduce `hx`. Conclude with `⟨-x, hnegS M x hx, by simp only [hmv, neg_neg]⟩`.

Establish `e1` using `hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) (fun _ => (1 : ℂ)) (hmeas M)`. Establish `e2` using `hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) f (hmeas M)`. Rewrite `e1`, `e2` using `[himg]`. Simplify using `only [hmv] at e2`. Establish `alg : ∀ c v I J : ℂ, v ≠ 0 → v = c * v → I = c * J → J = I`.

Introduce `c v I J hv0 h1 h2`. Establish `hc : c = 1`. Establish `: c * v = 1 * v` using `by rw [← h1, one_mul]`. Conclude with `mul_right_cancel₀ hv0 this`. Rewrite using `[h2, hc, one_mul]`.

Conclude with `alg _ _ _ _ (hv M) e1 e2`. Establish `hξ : ∀ x : Fin (k + 1) → F, Pi.single (Fin.last k) (1 : F) ⬝ᵥ x = x (Fin.last k)`. Introduce `x`. Simplify using `[dotProduct, Pi.single_apply]`. Use `choose P hP1 hP2 using fun (M : ℕ) (u : V) => h3' k M (Pi.single (Fin.last k) (1 : F)) u`.

Simplify using `only [hξ] at hP1 hP2`. Establish `hSA : ∀ (M : ℕ) (a b : V), B (P M a) b = B a (P M b)`. Introduce `M a b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hP1 M a (B b), integral_conj]`.

Use `_ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ψ (-(-x) (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) ∂(Measure.pi fun _ => μ) := by`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[map_mul, hψconj, herm, hB x a b]`. Simplify using `only [Pi.neg_apply, neg_neg]`.

Use `_ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b) ∂(Measure.pi fun _ => μ) := hcvS M (fun x => ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b))`. Use `_ = B a (P M b) := (hP1 M b (B a)).symm`. Establish `hE : ∀ (M : ℕ) (u v : V), (∀ y ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ρ (PositivityTheory.JacquetShalikaLocal.col n k y) v = ψ (y (Fin.last k)) • v) → B u (P M v) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * …`. Introduce `M u v hv0`. Rewrite using `[hP1 M v (B u), ← integral_mul_const]`.

Use `setIntegral_congr_fun (hmeas M) ?_` and prove the remaining obligations. Introduce `x hx`. Use `beta_reduce`. Rewrite using `[hv0 x hx, map_smul, smul_eq_mul, ← mul_assoc, hψinv]`. Establish `hL : ∀ (M : ℕ) (u : V), l (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * l u`.

Introduce `M u`. Rewrite using `[hP1 M u l, ← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[hW (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).2.1.1 u, (hcP x).2.2.2, ← mul_assoc, hψinv]`.

Establish `hrel : ∀ (M : ℕ) (u : V), B (P M u) (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u (P M u)`. Introduce `M u`. Rewrite using `[hSA M u (P M u), hE M u (P M u) (hP2 M u)]`. Establish `hchar : ∀ u u' : V, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u = B u' (P M u)`. Introduce `u u'`.

Take `⟨M₀, h⟩` from `hC u u'`. Conclude with `⟨M₀, fun M hM => by rw [h M hM, hP1 M u (B u')]⟩`. Use `⟨fun u u' => ?_, fun u => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨M1, h1⟩` from `hchar u u'`. Take `⟨M2, h2⟩` from `hchar u' u`.

Rewrite using `[h2 (max M1 M2) (le_max_right _ _), h1 (max M1 M2) (le_max_left _ _), herm, hSA]`. Take `⟨M1, h1⟩` from `hchar u u`. Rewrite using `[h1 M1 le_rfl]`. Establish `hp` using `psd (P M1 u)`. Rewrite `hp` using `[hrel M1 u, hvol' M1, Complex.re_ofReal_mul]`.

Conclude with `(mul_nonneg_iff_of_pos_left (hvol M1)).mp hp`. Take `⟨M1, h1⟩` from `hchar u u`. Rewrite `hu` using `[h1 M1 le_rfl]`. Establish `h0' : B (P M1 u) (P M1 u) = 0` using `by rw [hrel, hu, mul_zero]`. Establish `hl0` using `null (P M1 u) h0'`.

Rewrite `hl0` using `[hL M1 u]`. Conclude with `(mul_eq_zero.mp hl0).resolve_left (hv M1)`.
-/
theorem column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive := by
  intro h0 h3 h3c
  unfold FormHermitianPositive ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm l k B B' hk hW hI hC
  unfold L0 ForF at h0
  unfold L3 ForR ForF at h3
  unfold ColumnsMirabolic ForF at h3c
  obtain ⟨-, hlat⟩ := h0 F μ ψ hψ
  obtain ⟨hlatM, hcv⟩ := hlat (k + 1)
  have h3' := h3 F μ ψ hψ n V ρ hsm
  obtain ⟨hcadd, hc0, hcP, -, -, -⟩ := h3c F μ ψ hψ n k hk
  obtain ⟨herm, psd, null, quasi, -⟩ := hI
  clear h0 h3 h3c hlat
  have hψinv : ∀ t : F, ψ (-t) * ψ t = 1 := fun t => by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hψconj : ∀ t : F, conj (ψ (-t)) = ψ t := by
    intro t
    have hn : ‖ψ (-t)‖ = 1 := hψ.2.2 (-t)
    calc conj (ψ (-t)) = conj (ψ (-t)) * (ψ (-t) * ψ t) := by rw [hψinv, mul_one]
      _ = (conj (ψ (-t)) * ψ (-t)) * ψ t := by ring
      _ = ψ t := by rw [Complex.conj_mul', hn]; simp
  have hinv : ∀ (x : Fin (k + 1) → F) (b : V),
      ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) = b := by
    intro x b
    have h1 : PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x) = 1 := by
      rw [← hcadd, add_neg_cancel, hc0]
    calc ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
        = (ρ (PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x))) b := by rw [map_mul]; rfl
      _ = b := by rw [h1, map_one]; rfl
  have hB : ∀ (x : Fin (k + 1) → F) (a b : V),
      B (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a) b = B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) := by
    intro x a b
    have hq := quasi (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).1 a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
    rw [hinv, (hcP x).2.2.1, map_one] at hq
    simpa using hq

  have hnegS : ∀ (M : ℕ), ∀ x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, -x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
    intro M x hx
    simp only [PositivityTheory.JacquetShalikaLocal.lat, Set.mem_setOf_eq, Pi.neg_apply, mul_neg] at hx ⊢
    exact fun i => neg_mem (hx i)
  have hvol : ∀ M : ℕ, 0 < (Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) :=
    fun M => (hlatM M).2.2.2
  have hmeas : ∀ M : ℕ, MeasurableSet (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) := fun M => (hlatM M).2.2.1
  have hvol' : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)
      = (((Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) : ℝ) : ℂ) := by
    intro M
    rw [setIntegral_const]
    simp
  have hv : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) ≠ 0 := by
    intro M
    rw [hvol' M]
    exact Complex.ofReal_ne_zero.mpr (hvol M).ne'
  have hmv : ∀ x : Fin (k + 1) → F,
      (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x = -x := by
    intro x
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hcvS : ∀ (M : ℕ) (f : (Fin (k + 1) → F) → ℂ),
      ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f (-x) ∂(Measure.pi fun _ => μ)
        = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f x ∂(Measure.pi fun _ => μ) := by
    intro M f
    have himg : (fun x => (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x)
        '' PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M = PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [hmv]
        exact hnegS M y hy
      · intro hx
        exact ⟨-x, hnegS M x hx, by simp only [hmv, neg_neg]⟩
    have e1 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) (fun _ => (1 : ℂ)) (hmeas M)
    have e2 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) f (hmeas M)
    rw [himg] at e1 e2
    simp only [hmv] at e2
    have alg : ∀ c v I J : ℂ, v ≠ 0 → v = c * v → I = c * J → J = I := by
      intro c v I J hv0 h1 h2
      have hc : c = 1 := by
        have : c * v = 1 * v := by rw [← h1, one_mul]
        exact mul_right_cancel₀ hv0 this
      rw [h2, hc, one_mul]
    exact alg _ _ _ _ (hv M) e1 e2

  have hξ : ∀ x : Fin (k + 1) → F, Pi.single (Fin.last k) (1 : F) ⬝ᵥ x = x (Fin.last k) := by
    intro x
    simp [dotProduct, Pi.single_apply]
  choose P hP1 hP2 using fun (M : ℕ) (u : V) => h3' k M (Pi.single (Fin.last k) (1 : F)) u
  simp only [hξ] at hP1 hP2
  have hSA : ∀ (M : ℕ) (a b : V), B (P M a) b = B a (P M b) := by
    intro M a b
    calc B (P M a) b = conj (B b (P M a)) := (herm b (P M a)).symm
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            conj (ψ (-x (Fin.last k)) * B b (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a)) ∂(Measure.pi fun _ => μ) := by
          rw [hP1 M a (B b), integral_conj]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-(-x) (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) ∂(Measure.pi fun _ => μ) := by
          congr 1
          funext x
          rw [map_mul, hψconj, herm, hB x a b]
          simp only [Pi.neg_apply, neg_neg]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b) ∂(Measure.pi fun _ => μ) :=
          hcvS M (fun x => ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b))
      _ = B a (P M b) := (hP1 M b (B a)).symm
  have hE : ∀ (M : ℕ) (u v : V),
      (∀ y ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ρ (PositivityTheory.JacquetShalikaLocal.col n k y) v = ψ (y (Fin.last k)) • v) →
      B u (P M v) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u v := by
    intro M u v hv0
    rw [hP1 M v (B u), ← integral_mul_const]
    refine setIntegral_congr_fun (hmeas M) ?_
    intro x hx
    beta_reduce
    rw [hv0 x hx, map_smul, smul_eq_mul, ← mul_assoc, hψinv]
  have hL : ∀ (M : ℕ) (u : V),
      l (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * l u := by
    intro M u
    rw [hP1 M u l, ← integral_mul_const]
    congr 1
    funext x
    rw [hW (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).2.1.1 u, (hcP x).2.2.2, ← mul_assoc, hψinv]
  have hrel : ∀ (M : ℕ) (u : V), B (P M u) (P M u)
      = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u (P M u) := by
    intro M u
    rw [hSA M u (P M u), hE M u (P M u) (hP2 M u)]
  have hchar : ∀ u u' : V, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u = B u' (P M u) := by
    intro u u'
    obtain ⟨M₀, h⟩ := hC u u'
    exact ⟨M₀, fun M hM => by rw [h M hM, hP1 M u (B u')]⟩
  refine ⟨fun u u' => ?_, fun u => ?_, fun u hu => ?_⟩
  · obtain ⟨M1, h1⟩ := hchar u u'
    obtain ⟨M2, h2⟩ := hchar u' u
    rw [h2 (max M1 M2) (le_max_right _ _), h1 (max M1 M2) (le_max_left _ _), herm, hSA]
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl]
    have hp := psd (P M1 u)
    rw [hrel M1 u, hvol' M1, Complex.re_ofReal_mul] at hp
    exact (mul_nonneg_iff_of_pos_left (hvol M1)).mp hp
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl] at hu
    have h0' : B (P M1 u) (P M1 u) = 0 := by rw [hrel, hu, mul_zero]
    have hl0 := null (P M1 u) h0'
    rw [hL M1 u] at hl0
    exact (mul_eq_zero.mp hl0).resolve_left (hv M1)

end GlobalTheory.CompanionTheory.JSBoundStep

end
