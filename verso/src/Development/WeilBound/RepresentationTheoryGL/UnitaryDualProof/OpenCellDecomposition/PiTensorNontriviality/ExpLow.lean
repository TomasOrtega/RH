import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GroundTheory.Automorphic.Whittaker
open scoped TensorProduct

namespace PositivityTheory.RgUd.CellE

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h0 : ∀ t : ⨂[ℂ] i, M i, t = 0`. Introduce `t`. Proceed by induction on `t using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod c f`. Rewrite using `[(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Take `⟨a, b, hab⟩` from `h`. Conclude with `hab ((h0 a).trans (h0 b).symm)`.
-/
theorem nontrivial_of_piTensor {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (h : Nontrivial (⨂[ℂ] i, M i)) (i : ι) : Nontrivial (M i) := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ t : ⨂[ℂ] i, M i, t = 0 := by
    intro t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨a, b, hab⟩ := h
  exact hab ((h0 a).trans (h0 b).symm)

/- English proof (translation)
Set `P : Fin 2 → Σ n, GRep k n` to `![⟨r, ⟨V, A⟩⟩, ⟨m, ⟨W, x⟩⟩]`. Set `d : Fin 2 → ℕ` to `fun a => (P a).1`. Set `π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (P a).2.V` to `fun a => (P a).2.ρ`. Establish `hs : ∀ a, IsSmooth (π a)`. Introduce `a`.

Use `fin_cases a`. Use `exacts [hA, hx]`. Take `⟨E⟩` from `nonempty_prod₂_equiv_multiProd (Fin.sum_univ_two d) π`. Establish `h' : IsGenericFor ψ (multiProd (stdBlocks d (Fin.sum_univ_two d)) π)` using `IsGenericFor.of_equiv (π := prod₂ (π 0) (π 1)) h E`. Take `⟨L⟩` from `GlobalTheory.T.whittaker_heredity k ψ hc h1 2 _ d (Fin.sum_univ_two d) (fun a => (P a).2.V) π hs`.

Establish `hT : Nontrivial (⨂[ℂ] a, TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a)))`. Establish `: Nontrivial (TwJacquet (multiProd (stdBlocks d (Fin.sum_univ_two d)) π) (unipB k (Fin (d 0 + d 1))) (whitChar ψ (d 0 + d 1)))` using `h'`. Conclude with `L.symm.toEquiv.nontrivial`. Conclude with `⟨nontrivial_of_piTensor hT 0, nontrivial_of_piTensor hT 1⟩`.
-/
theorem isGenericFor_factors {r m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) (hA : IsSmooth A)
    (hx : IsSmooth x) (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (h : IsGenericFor ψ (prod₂ A x)) :
    IsGenericFor ψ A ∧ IsGenericFor ψ x := by
  let P : Fin 2 → Σ n, GRep k n := ![⟨r, ⟨V, A⟩⟩, ⟨m, ⟨W, x⟩⟩]
  let d : Fin 2 → ℕ := fun a => (P a).1
  let π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (P a).2.V := fun a => (P a).2.ρ
  have hs : ∀ a, IsSmooth (π a) := by
    intro a
    fin_cases a
    exacts [hA, hx]
  obtain ⟨E⟩ := nonempty_prod₂_equiv_multiProd (Fin.sum_univ_two d) π
  have h' : IsGenericFor ψ (multiProd (stdBlocks d (Fin.sum_univ_two d)) π) :=
    IsGenericFor.of_equiv (π := prod₂ (π 0) (π 1)) h E
  obtain ⟨L⟩ := GlobalTheory.T.whittaker_heredity k ψ hc h1 2 _ d (Fin.sum_univ_two d) (fun a => (P a).2.V) π hs
  have hT : Nontrivial (⨂[ℂ] a, TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) := by
    have : Nontrivial (TwJacquet (multiProd (stdBlocks d (Fin.sum_univ_two d)) π) (unipB k (Fin (d 0 + d 1)))
      (whitChar ψ (d 0 + d 1))) := h'
    exact L.symm.toEquiv.nontrivial
  exact ⟨nontrivial_of_piTensor hT 0, nontrivial_of_piTensor hT 1⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hn : 0 < Complex.normSq (Q v w)` using `Complex.normSq_pos.2 hne`. Use `set c := Q v w with hc`. Use `set t : ℝ := ((Q w w).re + 1) / (2 * Complex.normSq c) with ht`. Use `set l : ℂ := -(t : ℂ) * starRingEnd ℂ c with hl`.

Establish `key` using `hp (l • v + w)`. Establish `e : Q (l • v + w) (l • v + w) = l * starRingEnd ℂ l * Q v v + l * c + starRingEnd ℂ l * Q w v + Q w w`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlc : l * c = ((-(t * Complex.normSq c) : ℝ) : ℂ)`.

Rewrite using `[hl, Complex.ofReal_neg, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlc' : starRingEnd ℂ l * Q w v = ((-(t * Complex.normSq c) : ℝ) : ℂ)`. Rewrite using `[hh v w, ← map_mul, ← hc, hlc, Complex.conj_ofReal]`. Rewrite `key` using `[e, hv, mul_zero, zero_add, hlc, hlc']`.

Simplify using `only [Complex.add_re, Complex.ofReal_re] at key`. Establish `: t * Complex.normSq c = ((Q w w).re + 1) / 2`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sesq_eq_zero_of_self {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hh : ∀ v w, Q w v = starRingEnd ℂ (Q v w)) (hp : ∀ v, 0 ≤ (Q v v).re) {v : V} (hv : Q v v = 0) (w : V) :
    Q v w = 0 := by
  by_contra hne
  have hn : 0 < Complex.normSq (Q v w) := Complex.normSq_pos.2 hne
  set c := Q v w with hc
  set t : ℝ := ((Q w w).re + 1) / (2 * Complex.normSq c) with ht
  set l : ℂ := -(t : ℂ) * starRingEnd ℂ c with hl
  have key := hp (l • v + w)
  have e : Q (l • v + w) (l • v + w) =
      l * starRingEnd ℂ l * Q v v + l * c + starRingEnd ℂ l * Q w v + Q w w := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hc]
    ring
  have hlc : l * c = ((-(t * Complex.normSq c) : ℝ) : ℂ) := by
    rw [hl, Complex.ofReal_neg, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  have hlc' : starRingEnd ℂ l * Q w v = ((-(t * Complex.normSq c) : ℝ) : ℂ) := by
    rw [hh v w, ← map_mul, ← hc, hlc, Complex.conj_ofReal]
  rw [e, hv, mul_zero, zero_add, hlc, hlc'] at key
  simp only [Complex.add_re, Complex.ofReal_re] at key
  have : t * Complex.normSq c = ((Q w w).re + 1) / 2 := by
    rw [ht]
    field_simp
  linarith

/- English proof (translation)
Establish `hQt : ∀ w, Q (u - c • f₀) w = 0` using `sesq_eq_zero_of_self Q hh hp h`. Establish `hQt' : ∀ w, Q w (u - c • f₀) = 0` using `fun w => by rw [hh _ w, hQt w, map_zero]`. Establish `hut : u = c • f₀ + (u - c • f₀)` using `(add_sub_cancel _ _).symm`. Establish `hQu : Q u u = c * starRingEnd ℂ c * Q f₀ f₀`. Rewrite using `[hut]`.

Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hQt, hQt']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hQu, Complex.mul_conj, Complex.re_ofReal_mul]`.
-/
theorem quad_re {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hh : ∀ v w, Q w v = starRingEnd ℂ (Q v w)) (hp : ∀ v, 0 ≤ (Q v v).re) {u f₀ : V} (c : ℂ)
    (h : Q (u - c • f₀) (u - c • f₀) = 0) : (Q u u).re = Complex.normSq c * (Q f₀ f₀).re := by
  have hQt : ∀ w, Q (u - c • f₀) w = 0 := sesq_eq_zero_of_self Q hh hp h
  have hQt' : ∀ w, Q w (u - c • f₀) = 0 := fun w => by rw [hh _ w, hQt w, map_zero]
  have hut : u = c • f₀ + (u - c • f₀) := (add_sub_cancel _ _).symm
  have hQu : Q u u = c * starRingEnd ℂ c * Q f₀ f₀ := by
    rw [hut]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      hQt, hQt']
    ring
  rw [hQu, Complex.mul_conj, Complex.re_ofReal_mul]

/- English proof (translation)
Take `⟨r', rfl⟩ : ∃ r', r = r' + 1` from `⟨r - 1, by omega⟩`. Establish `e1 : r' + 1 + m - m - 1 = r'` using `by omega`. Rewrite using `[map_mul, map_pow, map_pow, Complex.normSq_ofReal, Real.mul_self_sqrt hb.le, Complex.normSq_eq_norm_sq, hw, e1, mul_pow, ← pow_mul, show i * m * (r' + 1) = i * m * r' + m * i by ring, pow_add, pow_mul]`. Establish `: b ^ (i * m * r') ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_eq (b s : ℝ) (hb : 0 < b) (r m i : ℕ) (hr : 1 ≤ r) (w : ℂ) (hw : ‖w‖ = b ^ ((m : ℝ) * s)) (q : ℝ) :
    (b ^ (i * m * (r + m - m - 1)))⁻¹ * (Complex.normSq (((Real.sqrt b : ℝ) : ℂ) ^ (i * m * r) * w ^ i) * q) =
      (b ^ m * (b ^ ((m : ℝ) * s)) ^ 2) ^ i * q := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e1 : r' + 1 + m - m - 1 = r' := by omega
  rw [map_mul, map_pow, map_pow, Complex.normSq_ofReal, Real.mul_self_sqrt hb.le, Complex.normSq_eq_norm_sq, hw, e1,
    mul_pow, ← pow_mul, show i * m * (r' + 1) = i * m * r' + m * i by ring, pow_add, pow_mul]
  have : b ^ (i * m * r') ≠ 0 := by positivity
  field_simp
  rw [pow_mul]
  ring

/- English proof (translation)
Use `set ρ : ℝ := b ^ m * (b ^ ((m : ℝ) * s)) ^ 2 with hρ`. Establish `hρ0 : 0 < ρ` using `by positivity`. Establish `hS' : Summable fun i : ℕ => ρ ^ (i + i₀) * q` using `((summable_nat_add_iff i₀).2 hg).congr fun i => hterm (i + i₀) (by omega)`. Establish `hG : Summable fun i : ℕ => ρ ^ i`. Establish `h2 : Summable fun i : ℕ => ρ ^ i * (ρ ^ i₀ * q)` using `hS'.congr fun i => by rw [pow_add]; ring`.

Conclude with `(summable_mul_right_iff (by positivity)).1 h2`. Establish `hρ1 : ρ < 1`. Use `summable_geometric_iff_norm_lt_one.1 hG` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs, abs_of_pos hρ0]`. Then use the resulting hypothesis. Establish `hρe : ρ = b ^ ((m : ℝ) * (1 + 2 * s))`.

Rewrite using `[hρ, ← Real.rpow_natCast b m, ← Real.rpow_natCast (b ^ ((m : ℝ) * s)) 2, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hρ1` using `[hρe, Real.rpow_lt_one_iff_of_pos hb0]`.

Establish `hm0 : (0 : ℝ) < m` using `by exact_mod_cast hm`. Break down `hρ1 with ⟨h, -⟩ | ⟨-, h⟩` into its components or cases. Conclude with `absurd h (not_lt.2 hb1.le)`. Establish `: 0 < 1 + 2 * s` using `pos_of_mul_pos_right h hm0.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geom_bound (b s : ℝ) (m : ℕ) (hm : 1 ≤ m) (hb0 : 0 < b) (hb1 : b < 1) (g : ℕ → ℝ) (hg : Summable g) (q : ℝ)
    (hq : 0 < q) (i₀ : ℕ) (hterm : ∀ i ≥ i₀, g i = (b ^ m * (b ^ ((m : ℝ) * s)) ^ 2) ^ i * q) : -1 / 2 < s := by
  set ρ : ℝ := b ^ m * (b ^ ((m : ℝ) * s)) ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hS' : Summable fun i : ℕ => ρ ^ (i + i₀) * q :=
    ((summable_nat_add_iff i₀).2 hg).congr fun i => hterm (i + i₀) (by omega)
  have hG : Summable fun i : ℕ => ρ ^ i := by
    have h2 : Summable fun i : ℕ => ρ ^ i * (ρ ^ i₀ * q) := hS'.congr fun i => by rw [pow_add]; ring
    exact (summable_mul_right_iff (by positivity)).1 h2
  have hρ1 : ρ < 1 := by
    have := summable_geometric_iff_norm_lt_one.1 hG
    rwa [Real.norm_eq_abs, abs_of_pos hρ0] at this
  have hρe : ρ = b ^ ((m : ℝ) * (1 + 2 * s)) := by
    rw [hρ, ← Real.rpow_natCast b m, ← Real.rpow_natCast (b ^ ((m : ℝ) * s)) 2, ← Real.rpow_mul hb0.le,
      ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  rw [hρe, Real.rpow_lt_one_iff_of_pos hb0] at hρ1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rcases hρ1 with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h (not_lt.2 hb1.le)
  · have : 0 < 1 + 2 * s := pos_of_mul_pos_right h hm0.le
    linarith

/- English proof (translation)
Introduce `hB hO r m V W _ _ _ _ A x ω s hr hm hAs hxs hgen hunit hω hωn`. Take `⟨ψ, hc, h1, hψ⟩` from `hgen`. Take `⟨hA, hx⟩` from `isGenericFor_factors k A x hAs hxs ψ hc h1 hψ`. Take `⟨z, -, hz1⟩` from `GlobalTheory.CentralExponent.exists_nabs_lt_one k`. Establish `hz0 : 0 < nabs k z` using `GlobalTheory.SmGL.nabs_pos' k z`.

Take `⟨f, f₀, hf₀, i₀, hi⟩` from `hO ψ hc h1 r m V W A x ω hAs hxs hA hx hω z hz1`. Take `⟨Q, hh, hp, hker, hsum⟩` from `hB ψ hc h1 (r + m) _ (prod₂ A x) (isSmooth_prod₂ A x) hunit`. Establish `hq0 : 0 < (Q f₀ f₀).re`. Establish `hne : Q f₀ f₀ ≠ 0` using `fun e => hf₀ ((hker f₀).1 e)`. Establish `him : (Q f₀ f₀).im = 0`.

Use `congrArg Complex.im (hh f₀ f₀)` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `(hp f₀).lt_or_eq with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (Complex.ext h.symm him) hne`. Use `geom_bound (nabs k z) s m hm hz0 hz1 _ (hsum m hm (by omega) z hz1 f) _ hq0 i₀ fun i hi' => ?_` and prove the remaining obligations. Rewrite using `[quad_re Q hh hp _ ((hker _).2 (hi i hi'))]`. Conclude with `term_eq (nabs k z) s hz0 r m i hr (ω z : ℂ) (hωn z) _`.
-/
theorem expLow : PositivityTheory.RgUd.BesselSum k → PositivityTheory.RgUd.OpenCell k → PositivityTheory.RgUd.ExpLow k := by
  intro hB hO r m V W _ _ _ _ A x ω s hr hm hAs hxs hgen hunit hω hωn
  obtain ⟨ψ, hc, h1, hψ⟩ := hgen
  obtain ⟨hA, hx⟩ := isGenericFor_factors k A x hAs hxs ψ hc h1 hψ
  obtain ⟨z, -, hz1⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hz0 : 0 < nabs k z := GlobalTheory.SmGL.nabs_pos' k z
  obtain ⟨f, f₀, hf₀, i₀, hi⟩ := hO ψ hc h1 r m V W A x ω hAs hxs hA hx hω z hz1
  obtain ⟨Q, hh, hp, hker, hsum⟩ := hB ψ hc h1 (r + m) _ (prod₂ A x) (isSmooth_prod₂ A x) hunit
  have hq0 : 0 < (Q f₀ f₀).re := by
    have hne : Q f₀ f₀ ≠ 0 := fun e => hf₀ ((hker f₀).1 e)
    have him : (Q f₀ f₀).im = 0 := by
      have := congrArg Complex.im (hh f₀ f₀)
      rw [Complex.conj_im] at this
      linarith
    rcases (hp f₀).lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm him) hne
  refine geom_bound (nabs k z) s m hm hz0 hz1 _ (hsum m hm (by omega) z hz1 f) _ hq0 i₀ fun i hi' => ?_
  rw [quad_re Q hh hp _ ((hker _).2 (hi i hi'))]
  exact term_eq (nabs k z) s hz0 r m i hr (ω z : ℂ) (hωn z) _

end PositivityTheory.RgUd.CellE
