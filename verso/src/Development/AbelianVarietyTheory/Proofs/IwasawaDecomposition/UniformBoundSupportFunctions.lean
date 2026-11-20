import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ConeGrow

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ}

/- English proof (translation)
Rewrite using `[← evalR_toReal, h, (linearOn_iff φ γ).1 hγ c hc]`.
-/
theorem evalZ_eq_of_toReal {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : φ.LinearOn γ) {c : Fin m → ℝ}
    (hc : ∀ i, 0 ≤ c i) {β : LinearMap.BilinForm ℤ X} (h : toReal β = ∑ i, c i • toReal (γ i)) :
    φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
  rw [← evalR_toReal, h, (linearOn_iff φ γ).1 hγ c hc]

omit [Module O X] [Module.Finite O X] in

/- English proof (translation)
Establish `h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal (j (Option.elim o β γ)) = 0`. Rewrite using `[Fintype.sum_option]`. Simplify using `only [Option.elim_none, Option.elim_some, h, neg_one_smul, neg_add_cancel]`. Use `sum_mul_eq_zero_of_sum_toReal hj ℓ h0` as an intermediate fact. Rewrite `this` using `[Fintype.sum_option]`.

Simplify using `only [Option.elim_none, Option.elim_some] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem apply_eq_of_toReal {L : Type} [AddCommGroup L] {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X}
    (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {β : L} {γ : Fin m → L} {c : Fin m → ℝ}
    (h : toReal (j β) = ∑ i, c i • toReal (j (γ i))) : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by
  have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal (j (Option.elim o β γ)) = 0 := by
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, h, neg_one_smul, neg_add_cancel]
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ h0
  rw [Fintype.sum_option] at this
  simp only [Option.elim_none, Option.elim_some] at this
  linarith

/- English proof (translation)
Take `⟨f, hf⟩` from `hγ.basis.exists_dual`. Use `⟨fun i => f i ⟨β, hβ⟩, fun i => ?_⟩` and prove the remaining obligations. Use `apply_eq_of_toReal (j := (balForms bar X).subtype) Subtype.val_injective (f i) (β := ⟨β, hβ⟩) (γ := fun k => ⟨γ k, hγ.mem k⟩) (c := c) h` as an intermediate fact. Rewrite using `[this]`. Simplify using `[hf]`.
-/
theorem coords_int {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (h : toReal β = ∑ i, c i • toReal (γ i)) :
    ∃ z : Fin m → ℤ, ∀ i, c i = z i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  refine ⟨fun i => f i ⟨β, hβ⟩, fun i => ?_⟩
  have := apply_eq_of_toReal (j := (balForms bar X).subtype) Subtype.val_injective (f i)
    (β := ⟨β, hβ⟩) (γ := fun k => ⟨γ k, hγ.mem k⟩) (c := c) h
  rw [this]
  simp [hf]

omit [Module O X] [Module.Finite O X] in

/- English proof (translation)
Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun₂ h a b` as an intermediate fact. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this ⊢`. Conclude with `this` after adjusting the coercions.
-/
theorem eq_sum_of_toReal {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {z : Fin m → ℤ}
    (h : toReal β = ∑ i, (z i : ℝ) • toReal (γ i)) : β = ∑ i, z i • γ i := by
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this ⊢
  exact_mod_cast this

end Help

end GlobalTheory.ConeGrow

namespace GlobalTheory.ConeGrow

/- English proof (translation)
Introduce `E _ _ _ H φ X _ _ _ _ hP Nmax hN m δ hδ w hw hwp`. Take `⟨Nd, ℓd, hNd, hd1, hd2, -⟩` from `hδ.strict`. Use `set u : LinearMap.BilinForm ℤ X := ∑ j, δ j with hu_def`. Establish `hu : u ∈ balForms H.bar X` using `Submodule.sum_mem _ fun j _ => hδ.mem j`. Establish `hup : ∀ a, 0 ≤ u a a` using `fun a => by`.

Simplify using `only [u, LinearMap.sum_apply]`. Conclude with `Finset.sum_nonneg fun j _ => hδ.nonneg j a`. Establish `hφu : φ.evalZ u = ∑ j, φ.evalZ (δ j)`. Use `evalZ_eq_of_toReal hδ.linear (c := fun _ => 1) (fun _ => zero_le_one) (β := u) (LinearMap.ext₂ fun a b => by simp [u, LinearMap.sum_apply])` as an intermediate fact. Simplify using `using this`.

Establish `hℓdu : (ℓd u : ℝ) = Nd * φ.evalZ u`. Rewrite using `[hφu, Finset.mul_sum, ← Finset.sum_congr rfl (fun j _ => hd1 j)]`. Simplify using `[u, map_sum]`. Establish `hK' : 0 ≤ (ℓd w : ℝ) - Nd * φ.evalZ w` using `sub_nonneg.2 (hd2 w hw hwp)`. Take `⟨n, hn⟩` from `exists_nat_gt ((Nmax : ℝ) * ((ℓd w : ℝ) - Nd * φ.evalZ w))`.

Use `set y : LinearMap.BilinForm ℤ X := (n : ℤ) • u + w with hy_def`. Establish `hy : y ∈ balForms H.bar X` using `add_mem (Submodule.smul_mem _ _ hu) hw`. Establish `hyp : ∀ a, 0 ≤ y a a` using `fun a => by`. Simplify using `only [y, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `add_nonneg (mul_nonneg (by positivity) (hup a)) (hwp a)`.

Take `⟨m', ε, c, hε, hc, hyc⟩` from `hP.cover (toReal y) (toReal_mem_psdCone_of_nonneg E H X y hy hyp)`. Take `⟨z, hz⟩` from `coords_int hε hy hyc`. Take `⟨Nn, ℓn, hNn, hNnmax, hn1, hn2, hn3⟩` from `hN m' ε hε`. Establish `hφy : φ.evalZ y = ∑ i, c i * φ.evalZ (ε i)` using `evalZ_eq_of_toReal hε.linear hc hyc`. Establish `hℓny : (ℓn y : ℝ) = Nn * φ.evalZ y`.

Establish `hh` using `apply_eq_of_toReal (j := LinearMap.id) (β := y) (γ := ε) (c := c) Function.injective_id ℓn hyc`. Rewrite using `[hh, hφy, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hn1]; ring`. Establish `hlin : ∀ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (ℓ y : ℝ) = n * ℓ u + ℓ w` using `fun ℓ => by`. Simplify using `[y]`.

Establish `b1` using `hd2 y hy hyp`. Establish `c1` using `hn2 u hu hup`. Establish `c2` using `hn2 w hw hwp`. Take `⟨pu, hpu⟩` from `hP.integral u hu hup`. Establish `hNd' : (1 : ℝ) ≤ Nd` using `by exact_mod_cast hNd`.

Establish `hNn' : (0 : ℝ) ≤ Nn` using `by positivity`. Establish `hNmax' : (Nn : ℝ) ≤ Nmax` using `by exact_mod_cast hNnmax`. Establish `key : (n : ℝ) * Nd * ((ℓn u : ℝ) - Nn * φ.evalZ u) < n`. Establish `e1` using `mul_le_mul_of_nonneg_left c2 (show (0 : ℝ) ≤ Nd by positivity)`. Establish `e2` using `mul_le_mul_of_nonneg_left b1 hNn'`.

Establish `e3` using `mul_le_mul_of_nonneg_right hNmax' hK'`. Rewrite `e2` using `[hlin, hℓdu]`. Establish `e4 : (Nn : ℝ) * φ.evalZ y = n * ℓn u + ℓn w` using `by rw [← hℓny, hlin]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hnpos : (0 : ℝ) < n` using `lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hK') hn`.

Use `set d : ℤ := ℓn u - Nn * pu with hd_def`. Establish `hdR : (d : ℝ) = (ℓn u : ℝ) - Nn * φ.evalZ u` using `by rw [hpu]; push_cast [d]; ring`. Establish `hd0 : 0 ≤ d`. Establish `: (0 : ℝ) ≤ d` using `by rw [hdR]; linarith`. Conclude with `this` after adjusting the coercions.

Establish `hdz : d = 0`. Establish `h1 : (Nd : ℝ) * d < 1`. Rewrite using `[hdR]`. Use `key` as an intermediate fact. Rewrite `this` using `[mul_assoc]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (d : ℝ) ≤ Nd * d` using `le_mul_of_one_le_left (by exact_mod_cast hd0) hNd'`. Establish `: (d : ℝ) < 1` using `lt_of_le_of_lt h2 h1`. Establish `: d < 1` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers.

Establish `ht : ∀ j, 0 ≤ (ℓn (δ j) : ℝ) - Nn * φ.evalZ (δ j)` using `fun j => sub_nonneg.2 (hn2 (δ j) (hδ.mem j) (hδ.nonneg j))`. Establish `hsum : ∑ j, ((ℓn (δ j) : ℝ) - Nn * φ.evalZ (δ j)) = 0`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, ← hφu]`. Establish `: (ℓn u : ℝ) = ∑ j, (ℓn (δ j) : ℝ)` using `by simp [u, map_sum]`. Rewrite using `[← this, ← hdR, hdz, Int.cast_zero]`.

Establish `heq : ∀ j, (Nn : ℝ) * φ.evalZ (δ j) = ℓn (δ j)` using `fun j => by`. Use `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => ht j).1 hsum j (Finset.mem_univ _)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose k cj hk hkc using fun j => hn3 (δ j) (hδ.mem j) (hδ.nonneg j) (heq j)`. Use `⟨m', ε, hε, fun j => ⟨k j, cj j, hk j, hkc j⟩, ∏ j, k j, fun i => (∏ j, k j : ℕ) * z i - n * ∑ j, ((∏ j' ∈ Finset.univ.erase j, k j' : ℕ) : ℤ) * cj j i, Finset.prod_pos fun j _ => hk j, ?_⟩` and prove the remaining obligations.

Establish `hyz : y = ∑ i, z i • ε i` using `eq_sum_of_toReal (by rw [hyc]; simp only [hz])`. Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Establish `hy_ab : y a b = n * u a b + w a b` using `by simp [y]`. Establish `hyz_ab : y a b = ∑ i, z i * ε i a b`. Rewrite using `[hyz]`.

Simplify using `[LinearMap.sum_apply]`. Establish `hu_ab : u a b = ∑ j, δ j a b` using `by simp [u, LinearMap.sum_apply]`. Establish `hkc_ab : ∀ j, (k j : ℤ) * δ j a b = ∑ i, (cj j i : ℤ) * ε i a b` using `fun j => by`. Use `LinearMap.congr_fun₂ (hkc j) a b` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply]`.

Establish `hK : ∀ j, ((∏ j, k j : ℕ) : ℤ) * δ j a b = ((∏ j' ∈ Finset.univ.erase j, k j' : ℕ) : ℤ) * ∑ i, (cj j i : ℤ) * ε i a b` using `fun j => by`. Rewrite using `[← hkc_ab, ← Finset.mul_prod_erase Finset.univ k (Finset.mem_univ j)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hy_ab, hu_ab, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Simplify using `only [hK, hyz_ab, Finset.mul_sum, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]`.

Rewrite using `[Finset.sum_comm (f := fun j i => _)]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem exists_cone_of_large_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFanOn H.bar φ X → ∀ Nmax : ℕ, (∀ (m : ℕ) (ε : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ ε → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ Nmax ∧ (∀ i, (ℓ (ε i) : ℝ) = N * φ.evalZ (ε i)) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β → ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • ε i) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → ∀ w ∈ balForms H.bar X, (∀ y, 0 ≤ w y y) → ∃ (m' : ℕ) (ε : Fin m' → LinearMap.BilinForm ℤ X), IsCone H.bar φ ε ∧ (∀ j, ∃ (k : ℕ) (c : Fin m' → ℕ), 0 < k ∧ k • δ j = ∑ i, c i • ε i) ∧ ∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • w = ∑ i, c i • ε i := by
  intro E _ _ _ H φ X _ _ _ _ hP Nmax hN m δ hδ w hw hwp
  classical
  obtain ⟨Nd, ℓd, hNd, hd1, hd2, -⟩ := hδ.strict
  set u : LinearMap.BilinForm ℤ X := ∑ j, δ j with hu_def
  have hu : u ∈ balForms H.bar X := Submodule.sum_mem _ fun j _ => hδ.mem j
  have hup : ∀ a, 0 ≤ u a a := fun a => by
    simp only [u, LinearMap.sum_apply]
    exact Finset.sum_nonneg fun j _ => hδ.nonneg j a
  have hφu : φ.evalZ u = ∑ j, φ.evalZ (δ j) := by
    have := evalZ_eq_of_toReal hδ.linear (c := fun _ => 1) (fun _ => zero_le_one) (β := u)
      (LinearMap.ext₂ fun a b => by simp [u, LinearMap.sum_apply])
    simpa using this
  have hℓdu : (ℓd u : ℝ) = Nd * φ.evalZ u := by
    rw [hφu, Finset.mul_sum, ← Finset.sum_congr rfl (fun j _ => hd1 j)]
    simp [u, map_sum]
  have hK' : 0 ≤ (ℓd w : ℝ) - Nd * φ.evalZ w := sub_nonneg.2 (hd2 w hw hwp)
  obtain ⟨n, hn⟩ := exists_nat_gt ((Nmax : ℝ) * ((ℓd w : ℝ) - Nd * φ.evalZ w))
  set y : LinearMap.BilinForm ℤ X := (n : ℤ) • u + w with hy_def
  have hy : y ∈ balForms H.bar X := add_mem (Submodule.smul_mem _ _ hu) hw
  have hyp : ∀ a, 0 ≤ y a a := fun a => by
    simp only [y, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (by positivity) (hup a)) (hwp a)
  obtain ⟨m', ε, c, hε, hc, hyc⟩ := hP.cover (toReal y) (toReal_mem_psdCone_of_nonneg E H X y hy hyp)
  obtain ⟨z, hz⟩ := coords_int hε hy hyc
  obtain ⟨Nn, ℓn, hNn, hNnmax, hn1, hn2, hn3⟩ := hN m' ε hε
  have hφy : φ.evalZ y = ∑ i, c i * φ.evalZ (ε i) := evalZ_eq_of_toReal hε.linear hc hyc
  have hℓny : (ℓn y : ℝ) = Nn * φ.evalZ y := by
    have hh := apply_eq_of_toReal (j := LinearMap.id) (β := y) (γ := ε) (c := c) Function.injective_id ℓn hyc
    rw [hh, hφy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hn1]; ring
  have hlin : ∀ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (ℓ y : ℝ) = n * ℓ u + ℓ w := fun ℓ => by
    simp [y]
  have b1 := hd2 y hy hyp
  have c1 := hn2 u hu hup
  have c2 := hn2 w hw hwp
  obtain ⟨pu, hpu⟩ := hP.integral u hu hup
  have hNd' : (1 : ℝ) ≤ Nd := by exact_mod_cast hNd
  have hNn' : (0 : ℝ) ≤ Nn := by positivity
  have hNmax' : (Nn : ℝ) ≤ Nmax := by exact_mod_cast hNnmax
  have key : (n : ℝ) * Nd * ((ℓn u : ℝ) - Nn * φ.evalZ u) < n := by
    have e1 := mul_le_mul_of_nonneg_left c2 (show (0 : ℝ) ≤ Nd by positivity)
    have e2 := mul_le_mul_of_nonneg_left b1 hNn'
    have e3 := mul_le_mul_of_nonneg_right hNmax' hK'
    rw [hlin, hℓdu] at e2
    have e4 : (Nn : ℝ) * φ.evalZ y = n * ℓn u + ℓn w := by rw [← hℓny, hlin]
    nlinarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hK') hn
  set d : ℤ := ℓn u - Nn * pu with hd_def
  have hdR : (d : ℝ) = (ℓn u : ℝ) - Nn * φ.evalZ u := by rw [hpu]; push_cast [d]; ring
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ d := by rw [hdR]; linarith
    exact_mod_cast this
  have hdz : d = 0 := by
    have h1 : (Nd : ℝ) * d < 1 := by
      rw [hdR]
      have := key
      rw [mul_assoc] at this
      nlinarith
    have h2 : (d : ℝ) ≤ Nd * d := le_mul_of_one_le_left (by exact_mod_cast hd0) hNd'
    have : (d : ℝ) < 1 := lt_of_le_of_lt h2 h1
    have : d < 1 := by exact_mod_cast this
    omega

  have ht : ∀ j, 0 ≤ (ℓn (δ j) : ℝ) - Nn * φ.evalZ (δ j) := fun j =>
    sub_nonneg.2 (hn2 (δ j) (hδ.mem j) (hδ.nonneg j))
  have hsum : ∑ j, ((ℓn (δ j) : ℝ) - Nn * φ.evalZ (δ j)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hφu]
    have : (ℓn u : ℝ) = ∑ j, (ℓn (δ j) : ℝ) := by simp [u, map_sum]
    rw [← this, ← hdR, hdz, Int.cast_zero]
  have heq : ∀ j, (Nn : ℝ) * φ.evalZ (δ j) = ℓn (δ j) := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ht j).1 hsum j (Finset.mem_univ _)
    linarith
  choose k cj hk hkc using fun j => hn3 (δ j) (hδ.mem j) (hδ.nonneg j) (heq j)
  refine ⟨m', ε, hε, fun j => ⟨k j, cj j, hk j, hkc j⟩, ∏ j, k j, fun i =>
    (∏ j, k j : ℕ) * z i - n * ∑ j, ((∏ j' ∈ Finset.univ.erase j, k j' : ℕ) : ℤ) * cj j i,
    Finset.prod_pos fun j _ => hk j, ?_⟩
  have hyz : y = ∑ i, z i • ε i := eq_sum_of_toReal (by rw [hyc]; simp only [hz])
  refine LinearMap.ext₂ fun a b => ?_
  have hy_ab : y a b = n * u a b + w a b := by simp [y]
  have hyz_ab : y a b = ∑ i, z i * ε i a b := by
    rw [hyz]; simp [LinearMap.sum_apply]
  have hu_ab : u a b = ∑ j, δ j a b := by simp [u, LinearMap.sum_apply]
  have hkc_ab : ∀ j, (k j : ℤ) * δ j a b = ∑ i, (cj j i : ℤ) * ε i a b := fun j => by
    have := LinearMap.congr_fun₂ (hkc j) a b
    simpa [LinearMap.sum_apply] using this
  have hK : ∀ j, ((∏ j, k j : ℕ) : ℤ) * δ j a b =
      ((∏ j' ∈ Finset.univ.erase j, k j' : ℕ) : ℤ) * ∑ i, (cj j i : ℤ) * ε i a b := fun j => by
    rw [← hkc_ab, ← Finset.mul_prod_erase Finset.univ k (Finset.mem_univ j)]
    push_cast; ring
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  calc ((∏ j, k j : ℕ) : ℤ) * w a b = (∏ j, k j : ℕ) * y a b - n * ∑ j, ((∏ j, k j : ℕ) : ℤ) * δ j a b := by
        rw [hy_ab, hu_ab, ← Finset.mul_sum]; ring
    _ = _ := by
        simp only [hK, hyz_ab, Finset.mul_sum, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
        rw [Finset.sum_comm (f := fun j i => _)]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConeGrow
