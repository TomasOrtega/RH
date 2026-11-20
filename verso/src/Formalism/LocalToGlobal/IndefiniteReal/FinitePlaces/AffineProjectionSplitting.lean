import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsThetaFunOPull

set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

/- English proof (translation)
Introduce `i j` and use `by rw [← hx i j, ← mul_assoc, mul_comm e e₁, h]`.
-/
theorem half_sub_of {e e₁ : AE D} (h : e₁ * e = e₁) {x : WO S T} (hx : IsHalf e₁ x) : IsHalf e x := fun i j => by
  rw [← hx i j, ← mul_assoc, mul_comm e e₁, h]

/- English proof (translation)
Introduce `i j` and use `by rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm e e₁, h]`.
-/
theorem chalf_sub_of {e e₁ : AE D} (h : e₁ * e = e₁) {y : WO S T} (hy : IsHalf (cA D e₁) y) :
    IsHalf (cA D e) y := fun i j => by
  rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm e e₁, h]

/- English proof (translation)
Establish `hc : ∀ c b, cA D (y c b) = e₁ * cA D (y c b)` using `fun c b => by conv_lhs => rw [← hy c b]`. Rewrite using `[map_mul, cA_cA]`. Establish `e1 : hO S T t y = hO S T (t.map (fun a => e₁ * a)) y`. Unfold `hO`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.map_apply]`. Use `conv_lhs => rw [hc c b]`. Expand and normalize the polynomial expressions, which then agree. Unfold `symplO`. Rewrite using `[e1]`.
-/
theorem symplO_left_e₁ {e₁ : AE D} {t y : WO S T} (hy : IsHalf (cA D e₁) y) :
    symplO S T t y = symplO S T (t.map (fun a => e₁ * a)) y := by
  have hc : ∀ c b, cA D (y c b) = e₁ * cA D (y c b) := fun c b => by
    conv_lhs => rw [← hy c b]
    rw [map_mul, cA_cA]
  have e1 : hO S T t y = hO S T (t.map (fun a => e₁ * a)) y := by
    unfold hO
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.map_apply]
    conv_lhs => rw [hc c b]
    ring
  unfold symplO
  rw [e1]

/- English proof (translation)
Establish `e1 : hO S T x y = hO S T x (y.map (fun a => cA D e₁ * a))`. Unfold `hO`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, map_mul, cA_cA]`. Use `conv_lhs => rw [← hx d a]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `symplO`. Rewrite using `[e1]`.
-/
theorem symplO_right_ce₁ {e₁ : AE D} {x y : WO S T} (hx : IsHalf e₁ x) :
    symplO S T x y = symplO S T x (y.map (fun a => cA D e₁ * a)) := by
  have e1 : hO S T x y = hO S T x (y.map (fun a => cA D e₁ * a)) := by
    unfold hO
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.map_apply, map_mul, cA_cA]
    conv_lhs => rw [← hx d a]
    ring
  unfold symplO
  rw [e1]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_smul, zero_smul, symplO_zero_right, symplO_zero_left]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_right, symplO_add_left, ih]`.
-/
theorem symplO_nsmul_right (t y : WO S T) (k : ℕ) : symplO S T t (k • y) = symplO S T (k • t) y := by
  induction k with
  | zero => rw [zero_smul, zero_smul, symplO_zero_right, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_right, symplO_add_left, ih]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hce : cA D e₁ * e = 0`. Establish `: cA D e₁ = cA D e₁ * cA D e` using `by rw [← map_mul, h1]`. Rewrite using `[this, mul_assoc, mul_comm (cA D e) e, he, mul_zero]`. Establish `hz : ∀ i j, (e₁ + cA D e₁) * t i j = 0` using `fun i j => by`. Rewrite using `[add_mul, h0 i j, zero_add, ← ht i j, ← mul_assoc, hce, zero_mul]`.

Establish `hL : HMul.hMul (mt T h) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = t`. Use extensionality with `i j`. Establish `h2 : ∀ k, ((mt T h) - 1) i k * t k j = 0` using `fun k => by`. Rewrite using `[← hh i k, mul_comm (e₁ + cA D e₁), mul_assoc, hz k j, mul_zero]`. Establish `h3 : ∑ k, ((mt T h) - 1) i k * t k j = 0` using `Finset.sum_eq_zero fun k _ => h2 k`.

Simplify using `only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3`. Rewrite using `[Matrix.mul_apply]`. Conclude with `sub_eq_zero.1 h3`. Establish `hR : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = t`. Use extensionality with `i j`.

Establish `h2 : ∀ k, t i k * ((mt S g) - 1) k j = 0` using `fun k => by`. Rewrite using `[← hg k j, ← mul_assoc, mul_comm (t i k), hz i k, zero_mul]`. Establish `h3 : ∑ k, t i k * ((mt S g) - 1) k j = 0` using `Finset.sum_eq_zero fun k _ => h2 k`. Simplify using `only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `sub_eq_zero.1 h3`. Establish `hinv : HMul.hMul (mt S g) (mt S g⁻¹) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))`. Rewrite using `[← Formalism.IndefR.Eqv.mt_mul, mul_inv_cancel, Formalism.IndefR.Eqv.mt_one]`. Establish `hR' : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = t` using `by conv_lhs => rw [← hR]`. Rewrite using `[Matrix.mul_assoc, hinv, Matrix.mul_one]`.

Unfold `actO`. Rewrite using `[hL, hR']`.
-/
theorem actO_fix {e e₁ : AE D} (he : e * cA D e = 0) (h1 : e₁ * e = e₁) {g : GA D S} {h : GA D T}
    (hg : SuppAt e₁ S g) (hh : SuppAt e₁ T h) {t : WO S T} (ht : IsHalf e t) (h0 : ∀ i j, e₁ * t i j = 0) :
    actO S T g h t = t := by
  have hce : cA D e₁ * e = 0 := by
    have : cA D e₁ = cA D e₁ * cA D e := by rw [← map_mul, h1]
    rw [this, mul_assoc, mul_comm (cA D e) e, he, mul_zero]
  have hz : ∀ i j, (e₁ + cA D e₁) * t i j = 0 := fun i j => by
    rw [add_mul, h0 i j, zero_add, ← ht i j, ← mul_assoc, hce, zero_mul]
  have hL : HMul.hMul (mt T h) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = t := by
    ext i j
    have h2 : ∀ k, ((mt T h) - 1) i k * t k j = 0 := fun k => by
      rw [← hh i k, mul_comm (e₁ + cA D e₁), mul_assoc, hz k j, mul_zero]
    have h3 : ∑ k, ((mt T h) - 1) i k * t k j = 0 := Finset.sum_eq_zero fun k _ => h2 k
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
    rw [Matrix.mul_apply]
    exact sub_eq_zero.1 h3
  have hR : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = t := by
    ext i j
    have h2 : ∀ k, t i k * ((mt S g) - 1) k j = 0 := fun k => by
      rw [← hg k j, ← mul_assoc, mul_comm (t i k), hz i k, zero_mul]
    have h3 : ∑ k, t i k * ((mt S g) - 1) k j = 0 := Finset.sum_eq_zero fun k _ => h2 k
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
    rw [Matrix.mul_apply]
    exact sub_eq_zero.1 h3
  have hinv : HMul.hMul (mt S g) (mt S g⁻¹) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, mul_inv_cancel, Formalism.IndefR.Eqv.mt_one]
  have hR' : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = t := by
    conv_lhs => rw [← hR]
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  unfold actO
  rw [hL, hR']

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `mi` using `fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h`. Take `⟨hs, k, hk, hi, hl⟩` from `hΨ`. Establish `hK : 0 < k * k` using `Nat.mul_pos hk hk`. Establish `hfinY : ∀ j, 0 < j → Finite (Four.Qt j (Λ ⊓ halfSub S T (cA D e₁)))` using `fun j hj => by`. Take `⟨R, hR⟩` from `hfY₁ j hj`.

Conclude with `finite_qt_of S T R fun u hu => by`. Take `⟨r, hr, v, hv, hve, huv⟩` from `hR u (mi hu).1 (mi hu).2`. Conclude with `⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩`. Establish `htf : ∀ j : ℕ, 0 < j → ∀ t : WO S T, j • t = 0 → t = 0` using `fun j hj t h => nsmul_eq_zero_WO S T hj h`. Use `haveI := Four.Gk_finite hfinY htf hK`.

Use `letI := Fintype.ofFinite (Four.Gk Λ (halfSub S T (cA D e₁)) (k * k))`. Set `G` to `Four.Gk Λ (halfSub S T (cA D e₁)) (k * k)`. Establish `hgY : ∀ g : G, IsHalf (cA D e₁) (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))` using `fun g i j => by`. Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, (Four.Gk_out g).1 i j]`. Establish `he₁e₁ : ∀ a : AE D, e₁ * (e₁ * a) = e₁ * a` using `fun a => by rw [← mul_assoc, he₁.1]`.

Establish `hA : ∀ t, ∑ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t = 0`. Introduce `t`. Distinguish the cases in `hΨt : Ψ t = 0`. Simplify using `[hΨt]`. Establish `ht` using `hs t hΨt`.

Establish `hkt` using `hl t hΨt`. Use `set s : WO S T := (k • t).map (fun a => e₁ * a) with hsdef`. Establish `hsΛ : s ∈ Λ` using `hΛe₁ _ hkt`. Establish `hsh : IsHalf e₁ s` using `fun i j => by simp only [hsdef, Matrix.map_apply]; exact he₁e₁ _`. Establish `hterm : ∀ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) = ψ (symplO S T s ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))`.

Introduce `g`. Rewrite using `[symplO_left_e₁ S T (hgY g), symplO_nsmul_right]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `only [hsdef, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Finset.sum_mul, Finset.sum_congr rfl fun g _ => hterm g]`. Establish `hcs` using `Four.chi_sum (χ := fun t y => ψ (symplO S T t y)) (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁)) (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul]) (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul]) (fun t y => psi_ne_zero ψ _ …`. Rewrite `hcs` using `[finsum_eq_sum_of_fintype]`. Rewrite using `[hcs]`.

Use `split_ifs with hin`. It suffices to derive a contradiction. Take `⟨u, hu, hus⟩` from `Four.mem_smulSub.1 hin`. Establish `hu'` using `mi hu`. Establish `he1t : t.map (fun a => e₁ * a) = k • u`.

Use `sub_eq_zero.1 (htf k hk _ ?_)` and prove the remaining obligations. Rewrite using `[smul_sub, smul_smul, hus, sub_eq_zero, hsdef]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdec : t = (t - t.map (fun a => e₁ * a)) + k • u` using `by rw [he1t, sub_add_cancel]`. Apply `hΨt` to reduce the goal to its premises. Rewrite using `[hdec, hi u hu'.1 (half_sub_of S T h1 hu'.2)]`. Use `hΨ0 _ (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, Matrix.map_apply, mul_sub, ht i j, ← mul_assoc, mul_comm e e₁, h1]`.

Rewrite using `[Matrix.sub_apply, Matrix.map_apply, mul_sub, he₁e₁, sub_self]`. Conclude with `zero_mul _`. Establish `hM : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hfun : Ψ = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (Ψ - fun t => ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t)`. Use function extensionality and compare the values at `t`.

Rewrite using `[Pi.smul_apply, Finset.sum_apply]`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[Finset.sum_sub_distrib, hA t, sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hM]`. Use `conv_lhs => rw [hfun]`. Rewrite using `[map_smul, map_sum, map_smul, map_sum]`.

Use `(smul_eq_zero.2 (Or.inr (Finset.sum_eq_zero fun g _ => ?_)))` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, hmo Ψ ⟨hs, k, hk, hi, hl⟩ _ (chalf_sub_of S T h1 (hgY g)), hℓ _ (hgY g) _ (hth Ψ ⟨hs, k, hk, hi, hl⟩), sub_self]`.
-/
theorem evalYZero_zero (ψ : AddChar (AF D.host.F) ℂ) {e e₁ : AE D} (he₁ : IsSplitIdem D e₁) (h1 : e₁ * e = e₁)
    (Λ : AddSubgroup (WO S T))
    (hΛe₁ : ∀ u ∈ Λ, u.map (fun a => e₁ * a) ∈ Λ)
    (hLL₁ : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdX₁ : ∀ x, IsHalf e₁ x → (∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
    (hfY₁ : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hmo : ∀ Φ, IsSBHalf e Λ Φ → ∀ y, IsHalf (cA D e) y →
      Tm (fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (Tm Φ))
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ u : WO S T, (∀ i j, cA D e₁ * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f)
    {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) (hΨ0 : ∀ t, IsHalf e t → (∀ i j, e₁ * t i j = 0) → Ψ t = 0) :
    ℓ (Tm Ψ) = 0 := by
  classical
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨hs, k, hk, hi, hl⟩ := hΨ
  have hK : 0 < k * k := Nat.mul_pos hk hk
  have hfinY : ∀ j, 0 < j → Finite (Four.Qt j (Λ ⊓ halfSub S T (cA D e₁))) := fun j hj => by
    obtain ⟨R, hR⟩ := hfY₁ j hj
    exact finite_qt_of S T R fun u hu => by
      obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
      exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩
  have htf : ∀ j : ℕ, 0 < j → ∀ t : WO S T, j • t = 0 → t = 0 := fun j hj t h => nsmul_eq_zero_WO S T hj h
  haveI := Four.Gk_finite hfinY htf hK
  letI := Fintype.ofFinite (Four.Gk Λ (halfSub S T (cA D e₁)) (k * k))
  let G := Four.Gk Λ (halfSub S T (cA D e₁)) (k * k)
  have hgY : ∀ g : G, IsHalf (cA D e₁) (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out)) := fun g i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, (Four.Gk_out g).1 i j]
  have he₁e₁ : ∀ a : AE D, e₁ * (e₁ * a) = e₁ * a := fun a => by rw [← mul_assoc, he₁.1]

  have hA : ∀ t, ∑ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t = 0 := by
    intro t
    by_cases hΨt : Ψ t = 0
    · simp [hΨt]
    have ht := hs t hΨt
    have hkt := hl t hΨt
    set s : WO S T := (k • t).map (fun a => e₁ * a) with hsdef
    have hsΛ : s ∈ Λ := hΛe₁ _ hkt
    have hsh : IsHalf e₁ s := fun i j => by simp only [hsdef, Matrix.map_apply]; exact he₁e₁ _
    have hterm : ∀ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) =
        ψ (symplO S T s ((g : Four.QY Λ (halfSub S T (cA D e₁))).out)) := by
      intro g
      rw [symplO_left_e₁ S T (hgY g), symplO_nsmul_right]
      congr 2
      ext i j
      simp only [hsdef, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]
      ring
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun g _ => hterm g]
    have hcs := Four.chi_sum (χ := fun t y => ψ (symplO S T t y)) (L := Λ) (X := halfSub S T e₁)
      (Y := halfSub S T (cA D e₁))
      (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
      (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
      (fun t y => psi_ne_zero ψ _)
      (fun x hx y hy => hLL₁ x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
      (fun x hx h => hdX₁ x hx fun y hy hye => h y (AddSubgroup.mem_inf.2 ⟨hy, hye⟩))
      (fun j hj s' hs' => by obtain ⟨t', ht', h'⟩ := half_div S T hj hs'; exact ⟨t', ht', h'⟩)
      (fun j hj s' hs' => by obtain ⟨t', ht', h'⟩ := half_div S T hj hs'; exact ⟨t', ht', h'⟩)
      hfinY htf hK (AddSubgroup.mem_inf.2 ⟨hsΛ, hsh⟩)
    rw [finsum_eq_sum_of_fintype] at hcs
    rw [hcs]
    split_ifs with hin
    · exfalso
      obtain ⟨u, hu, hus⟩ := Four.mem_smulSub.1 hin
      have hu' := mi hu
      have he1t : t.map (fun a => e₁ * a) = k • u := by
        refine sub_eq_zero.1 (htf k hk _ ?_)
        rw [smul_sub, smul_smul, hus, sub_eq_zero, hsdef]
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]
        ring
      have hdec : t = (t - t.map (fun a => e₁ * a)) + k • u := by rw [he1t, sub_add_cancel]
      apply hΨt
      rw [hdec, hi u hu'.1 (half_sub_of S T h1 hu'.2)]
      refine hΨ0 _ (fun i j => ?_) (fun i j => ?_)
      · rw [Matrix.sub_apply, Matrix.map_apply, mul_sub, ht i j, ← mul_assoc, mul_comm e e₁, h1]
      · rw [Matrix.sub_apply, Matrix.map_apply, mul_sub, he₁e₁, sub_self]
    · exact zero_mul _

  have hM : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfun : Ψ = (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
      (Ψ - fun t => ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t) := by
    funext t
    rw [Pi.smul_apply, Finset.sum_apply]
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hA t, sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul,
      inv_mul_cancel_left₀ hM]
  conv_lhs => rw [hfun]
  rw [map_smul, map_sum, map_smul, map_sum]
  refine (smul_eq_zero.2 (Or.inr (Finset.sum_eq_zero fun g _ => ?_)))
  rw [map_sub, map_sub, hmo Ψ ⟨hs, k, hk, hi, hl⟩ _ (chalf_sub_of S T h1 (hgY g)),
    hℓ _ (hgY g) _ (hth Ψ ⟨hs, k, hk, hi, hl⟩), sub_self]

end Formalism.IndefR.Fin

end
