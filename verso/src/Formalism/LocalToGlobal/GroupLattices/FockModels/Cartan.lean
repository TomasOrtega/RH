import Formalism.SharpRestriction.GrowthBounds.ProjectionLemmaBaseLevel
import Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[rowAct, Matrix.one_apply]`.
-/
theorem rowAct_one' (R : Type) [CommRing R] (k n : ℕ) : rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct, Matrix.one_apply]

/- English proof (translation)
Establish `h` using `rowActMul K k n g g⁻¹`. Rewrite `h` using `[Matrix.nonsing_inv_mul g hg, rowAct_one']`. Conclude with `AlgHom.congr_fun h P`.
-/
theorem rowAct_inv_right (K : Type) [Field K] (k n : ℕ) (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (P : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ P) = P := by
  have h := rowActMul K k n g g⁻¹
  rw [Matrix.nonsing_inv_mul g hg, rowAct_one'] at h
  exact AlgHom.congr_fun h P

/- English proof (translation)
Establish `h` using `rowActMul K k n g⁻¹ g`. Rewrite `h` using `[Matrix.mul_nonsing_inv g hg, rowAct_one']`. Conclude with `AlgHom.congr_fun h P`.
-/
theorem rowAct_inv_left (K : Type) [Field K] (k n : ℕ) (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (P : MvPolynomial (Fin k × Fin n) K) : rowAct K g⁻¹ (rowAct K g P) = P := by
  have h := rowActMul K k n g⁻¹ g
  rw [Matrix.mul_nonsing_inv g hg, rowAct_one'] at h
  exact AlgHom.congr_fun h P

/- English proof (translation)
Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`.
-/
theorem map_smul' {O Kf σ : Type} [CommRing O] [Field Kf] [Algebra O Kf] (w : O) (f : MvPolynomial σ O) :
    map (algebraMap O Kf) (w • f) = algebraMap O Kf w • map (algebraMap O Kf) f := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

/- English proof (translation)
Introduce `O Kf _ _ _ _ _ _ w hw m lam mu Λ hΛ hl hm F hF G hG hX`. Take `⟨g, hg, rfl⟩` from `hΛ`. Take `⟨X, hX, hFG⟩` from `hX`. Establish `hinj : Function.Injective (algebraMap O Kf)` using `IsFractionRing.injective O Kf`. Establish `hI` using `LatticeSystems.la_indep hinj`.

Establish `hlm : Antitone (lam + mu)` using `hl.add hm`. Establish `eL` using `LatticeSystems.H0_eq_twisted_nabla hI m lam hl g hg`. Establish `eM` using `LatticeSystems.H0_eq_twisted_nabla hI m mu hm g hg`. Establish `eLM` using `LatticeSystems.H0_eq_twisted_nabla hI m (lam + mu) hlm g hg`. Rewrite `hF` using `[eL]`.

Rewrite `hG` using `[eM]`. Rewrite `hX` using `[eLM]`. Rewrite using `[eL, eM]`. Establish `hc : algebraMap O Kf w ≠ 0`. Introduce `h0`.

Conclude with `hw.ne_zero (hinj (by rw [h0, map_zero]))`. Establish `hmap : ∀ f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O, (mapAlgHom (Algebra.ofId O Kf)).toLinearMap f = map (algebraMap O Kf) f` using `fun f => rfl`. Establish `hF'` using `(nablaLTwMem O Kf m lam g hg F).1 hF`. Establish `hG'` using `(nablaLTwMem O Kf m mu g hg G).1 hG`. Establish `hX'` using `(nablaLTwMem O Kf m (lam + mu) g hg X).1 hX`.

Take `⟨f, hf, hfe⟩` from `hF'`. Take `⟨f', hf', hfe'⟩` from `hG'`. Take `⟨x, hx, hxe⟩` from `hX'`. Rewrite `hfe`, `hfe'`, `hxe` using `[hmap]`. Establish `hprod : f * f' = C w * x`.

Apply `map_injective _ hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hfe, hfe', ← smul_eq_C_mul, map_smul', hxe, smul_mul_smul_comm, ← map_mul, hFG, ← algebraMap_smul Kf w X, map_smul, smul_smul, smul_smul, Pi.add_apply, zpow_add₀ hg.ne_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hprime : Prime (C w : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O)` using `(prime_C_iff _).2 hw.prime`.

Establish `key : ∀ (la : Fin (m + 1) → ℤ) (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O), q ∈ dualWeyl O (m + 1) (m + 1) (fun t => (la t - la (Fin.last m)).toNat) → map (algebraMap O Kf) q = g.det ^ (la (Fin.last m)) • rowAct Kf g P → C w …`. Introduce `la P q hq hqe hdvd`. Take `⟨q1, rfl⟩` from `hdvd`. Rewrite `hq`, `hqe` using `[← smul_eq_C_mul]`. Establish `hq1` using `dualWeylSat O _ _ _ w q1 hw.ne_zero hq`.

Use `⟨(algebraMap O Kf w)⁻¹ • P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nablaLTwMem O Kf m la g hg]`. Use `⟨q1, hq1, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap, map_smul, smul_comm, ← hqe, map_smul', smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[← algebraMap_smul Kf w, smul_smul, mul_inv_cancel₀ hc, one_smul]`.

Break down `hprime.dvd_or_dvd ⟨x, hprod⟩ with h | h` into its components or cases. Conclude with `Or.inl (key lam F f hf hfe h)`. Conclude with `Or.inr (key mu G f' hf' hfe' h)`.
-/
theorem cartanDomain_proved : Formalism.MainNotions.flipOneThree.CartanDomain := by
  intro O Kf _ _ _ _ _ _ w hw m lam mu Λ hΛ hl hm F hF G hG hX
  obtain ⟨g, hg, rfl⟩ := hΛ
  obtain ⟨X, hX, hFG⟩ := hX
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hI := LatticeSystems.la_indep hinj
  have hlm : Antitone (lam + mu) := hl.add hm
  have eL := LatticeSystems.H0_eq_twisted_nabla hI m lam hl g hg
  have eM := LatticeSystems.H0_eq_twisted_nabla hI m mu hm g hg
  have eLM := LatticeSystems.H0_eq_twisted_nabla hI m (lam + mu) hlm g hg
  rw [eL] at hF
  rw [eM] at hG
  rw [eLM] at hX
  rw [eL, eM]
  have hc : algebraMap O Kf w ≠ 0 := by
    intro h0
    exact hw.ne_zero (hinj (by rw [h0, map_zero]))
  have hmap : ∀ f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O,
      (mapAlgHom (Algebra.ofId O Kf)).toLinearMap f = map (algebraMap O Kf) f := fun f => rfl
  have hF' := (nablaLTwMem O Kf m lam g hg F).1 hF
  have hG' := (nablaLTwMem O Kf m mu g hg G).1 hG
  have hX' := (nablaLTwMem O Kf m (lam + mu) g hg X).1 hX
  obtain ⟨f, hf, hfe⟩ := hF'
  obtain ⟨f', hf', hfe'⟩ := hG'
  obtain ⟨x, hx, hxe⟩ := hX'
  rw [hmap] at hfe hfe' hxe
  have hprod : f * f' = C w * x := by
    apply map_injective _ hinj
    rw [map_mul, hfe, hfe', ← smul_eq_C_mul, map_smul', hxe, smul_mul_smul_comm, ← map_mul, hFG,
      ← algebraMap_smul Kf w X, map_smul, smul_smul, smul_smul, Pi.add_apply, zpow_add₀ hg.ne_zero]
    congr 1
    ring
  have hprime : Prime (C w : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O) := (prime_C_iff _).2 hw.prime
  have key : ∀ (la : Fin (m + 1) → ℤ) (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
      (q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O),
      q ∈ dualWeyl O (m + 1) (m + 1) (fun t => (la t - la (Fin.last m)).toNat) →
      map (algebraMap O Kf) q = g.det ^ (la (Fin.last m)) • rowAct Kf g P → C w ∣ q →
      ∃ P' ∈ nablaLTw O Kf m la g, P = w • P' := by
    intro la P q hq hqe hdvd
    obtain ⟨q1, rfl⟩ := hdvd
    rw [← smul_eq_C_mul] at hq hqe
    have hq1 := dualWeylSat O _ _ _ w q1 hw.ne_zero hq
    refine ⟨(algebraMap O Kf w)⁻¹ • P, ?_, ?_⟩
    · rw [nablaLTwMem O Kf m la g hg]
      refine ⟨q1, hq1, ?_⟩
      rw [hmap, map_smul, smul_comm, ← hqe, map_smul', smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rw [← algebraMap_smul Kf w, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rcases hprime.dvd_or_dvd ⟨x, hprod⟩ with h | h
  · exact Or.inl (key lam F f hf hfe h)
  · exact Or.inr (key mu G f' hf' hfe' h)

def om (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [shapeDeg, om, Pi.add_apply, Finset.card_filter]`. Rewrite using `[Fin.sum_univ_castSucc]`.
-/
theorem shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) :
    (shapeDeg sz : Fin n → ℕ) = shapeDeg (fun k : Fin K => sz k.castSucc) + om n (sz (Fin.last K)) := by
  funext t
  simp only [shapeDeg, om, Pi.add_apply, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]

/- English proof (translation)
Introduce `a b hab`. Unfold `shapeDeg`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk`, the goal using `[Finset.mem_filter]`.

Establish `: a.val ≤ b.val` using `hab`. Conclude with `⟨hk.1, by omega⟩`.
-/
theorem shapeDeg_antitone {n K : ℕ} (sz : Fin K → ℕ) : Antitone (shapeDeg sz : Fin n → ℕ) := by
  intro a b hab
  unfold shapeDeg
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  have : a.val ≤ b.val := hab
  exact ⟨hk.1, by omega⟩

/- English proof (translation)
Establish `h` using `bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)`. Establish `h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs`. Simplify using `[bideterminant]`. Establish `h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = om n s`. Use function extensionality and compare the values at `t`.

Simplify using `only [shapeDeg, om, Finset.card_filter]`. Simplify using the standard rewrite rules. Rewrite `h` using `[h1, h2]`. Conclude with `h`.
-/
theorem initMinor_mem (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (om n s) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = om n s := by
    funext t
    simp only [shapeDeg, om, Finset.card_filter]
    simp
  rw [h1, h2] at h
  exact h

def ProdSpan (R : Type) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ) : Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R {X | ∃ f ∈ dualWeyl R r n ν, ∃ f' ∈ dualWeyl R r n ν', X = f * f'}

/- English proof (translation)
Establish `key : ProdSpan R r n ν ν' ≤ (ProdSpan R r n (ν + ω) ν').comap (LinearMap.mulRight R h)`. Unfold `ProdSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, f', hf', rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨f * h, dualWeyl_mul R r n ν ω hf hh, f', hf', ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulRight_apply]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `fun X hX => key hX`.
-/
theorem prodSpan_mul_left (R : Type) [CommRing R] (r n : ℕ) (ν ν' ω : Fin n → ℕ)
    (h : MvPolynomial (Fin r × Fin n) R) (hh : h ∈ dualWeyl R r n ω) :
    ∀ X ∈ ProdSpan R r n ν ν', X * h ∈ ProdSpan R r n (ν + ω) ν' := by
  have key : ProdSpan R r n ν ν' ≤ (ProdSpan R r n (ν + ω) ν').comap (LinearMap.mulRight R h) := by
    unfold ProdSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, f', hf', rfl⟩
    apply Submodule.subset_span
    refine ⟨f * h, dualWeyl_mul R r n ν ω hf hh, f', hf', ?_⟩
    simp only [LinearMap.mulRight_apply]
    ring
  exact fun X hX => key hX

/- English proof (translation)
Establish `key : ProdSpan R r n ν ν' ≤ (ProdSpan R r n ν (ν' + ω)).comap (LinearMap.mulRight R h)`. Unfold `ProdSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, f', hf', rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨f, hf, f' * h, dualWeyl_mul R r n ν' ω hf' hh, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulRight_apply]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `fun X hX => key hX`.
-/
theorem prodSpan_mul_right (R : Type) [CommRing R] (r n : ℕ) (ν ν' ω : Fin n → ℕ)
    (h : MvPolynomial (Fin r × Fin n) R) (hh : h ∈ dualWeyl R r n ω) :
    ∀ X ∈ ProdSpan R r n ν ν', X * h ∈ ProdSpan R r n ν (ν' + ω) := by
  have key : ProdSpan R r n ν ν' ≤ (ProdSpan R r n ν (ν' + ω)).comap (LinearMap.mulRight R h) := by
    unfold ProdSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, f', hf', rfl⟩
    apply Submodule.subset_span
    refine ⟨f, hf, f' * h, dualWeyl_mul R r n ν' ω hf' hh, ?_⟩
    simp only [LinearMap.mulRight_apply]
    ring
  exact fun X hX => key hX

/- English proof (translation)
Establish `h3 : ∀ a : Fin n, a.val < s → ν ⟨s - 1, by omega⟩ ≤ ν a` using `fun a ha => hν (show a ≤ ⟨s - 1, by omega⟩ from by rw [Fin.le_def]; simp only; omega)`. Use `⟨fun t => ν t - om n s t, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `hab' : a.val ≤ b.val` using `hab`. Establish `h4` using `hν hab`.

Simplify using `only [om]`. Apply the tactic sequence `by_cases ha : a.val < s <;> by_cases hb : b.val < s`. Simplify using `only [ha, hb, if_true]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [ha, hb, if_true, if_false]`.

Use `h2 b (by omega)` as an intermediate fact. Use `h3 a ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Simplify using `only [ha, hb, if_false]`.

Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.add_apply, om]`. Distinguish the cases in `ht : t.val < s`. Simplify using `only [ht, if_true]`.

Use `h3 t ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [ht, if_false]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sub_om {n s : ℕ} (hs0 : 0 < s) (hs : s ≤ n) (ν : Fin n → ℕ) (hν : Antitone ν)
    (h1 : 1 ≤ ν ⟨s - 1, by omega⟩) (h2 : ∀ b : Fin n, s ≤ b.val → ν b + 1 ≤ ν ⟨s - 1, by omega⟩) :
    ∃ ν₁ : Fin n → ℕ, Antitone ν₁ ∧ ν = ν₁ + om n s := by
  have h3 : ∀ a : Fin n, a.val < s → ν ⟨s - 1, by omega⟩ ≤ ν a := fun a ha =>
    hν (show a ≤ ⟨s - 1, by omega⟩ from by rw [Fin.le_def]; simp only; omega)
  refine ⟨fun t => ν t - om n s t, ?_, ?_⟩
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    have h4 := hν hab
    simp only [om]
    by_cases ha : a.val < s <;> by_cases hb : b.val < s
    · simp only [ha, hb, if_true]; omega
    · simp only [ha, hb, if_true, if_false]
      have := h2 b (by omega)
      have := h3 a ha
      omega
    · omega
    · simp only [ha, hb, if_false]; omega
  · funext t
    simp only [Pi.add_apply, om]
    by_cases ht : t.val < s
    · simp only [ht, if_true]
      have := h3 t ht
      omega
    · simp only [ht, if_false]; omega

/- English proof (translation)
Distinguish the cases in `hs0 : s = 0`. Use `left`. Use `⟨ν, hν, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Simplify using `[om, hs0]`.

Establish `hs1 : 0 < s` using `Nat.pos_of_ne_zero hs0`. Establish `e0` using `congrFun h ⟨s - 1, by omega⟩`. Simplify using `only [Pi.add_apply, om] at e0`. Rewrite `e0` using `[if_pos (by omega)]`. Distinguish the cases in `hsn : s < n`.

Establish `e1` using `congrFun h ⟨s, hsn⟩`. Simplify using `only [Pi.add_apply, om] at e1`. Rewrite `e1` using `[if_neg (by omega)]`. Establish `e2 : σ ⟨s, hsn⟩ ≤ σ ⟨s - 1, by omega⟩` using `hσ (by rw [Fin.le_def]; simp only; omega)`. Establish `e3 : ν ⟨s, hsn⟩ + 1 ≤ ν ⟨s - 1, by omega⟩ ∨ ν' ⟨s, hsn⟩ + 1 ≤ ν' ⟨s - 1, by omega⟩` using `by omega`.

Break down `e3 with e3 | e3` into its components or cases. Use `left`. Use `sub_om hs1 hs ν hν (by omega) fun b hb => ?_` and prove the remaining obligations. Establish `: ν b ≤ ν ⟨s, hsn⟩` using `hν (by rw [Fin.le_def]; exact hb)`. Use linear arithmetic over natural numbers and integers.

Use `right`. Use `sub_om hs1 hs ν' hν' (by omega) fun b hb => ?_` and prove the remaining obligations. Establish `: ν' b ≤ ν' ⟨s, hsn⟩` using `hν' (by rw [Fin.le_def]; exact hb)`. Use linear arithmetic over natural numbers and integers. Establish `e3 : 1 ≤ ν ⟨s - 1, by omega⟩ ∨ 1 ≤ ν' ⟨s - 1, by omega⟩` using `by omega`.

Break down `e3 with e3 | e3` into its components or cases. Use `left`. Conclude with `sub_om hs1 hs ν hν e3 fun b hb => by have := b.isLt; omega`. Use `right`. Conclude with `sub_om hs1 hs ν' hν' e3 fun b hb => by have := b.isLt; omega`.
-/
theorem split_om {n s : ℕ} (hs : s ≤ n) (ν ν' σ : Fin n → ℕ) (hν : Antitone ν) (hν' : Antitone ν')
    (hσ : Antitone σ) (h : ν + ν' = σ + om n s) :
    (∃ ν₁ : Fin n → ℕ, Antitone ν₁ ∧ ν = ν₁ + om n s) ∨ ∃ ν₁ : Fin n → ℕ, Antitone ν₁ ∧ ν' = ν₁ + om n s := by
  by_cases hs0 : s = 0
  · left
    refine ⟨ν, hν, ?_⟩
    funext t
    simp [om, hs0]
  have hs1 : 0 < s := Nat.pos_of_ne_zero hs0
  have e0 := congrFun h ⟨s - 1, by omega⟩
  simp only [Pi.add_apply, om] at e0
  rw [if_pos (by omega)] at e0
  by_cases hsn : s < n
  · have e1 := congrFun h ⟨s, hsn⟩
    simp only [Pi.add_apply, om] at e1
    rw [if_neg (by omega)] at e1
    have e2 : σ ⟨s, hsn⟩ ≤ σ ⟨s - 1, by omega⟩ := hσ (by rw [Fin.le_def]; simp only; omega)
    have e3 : ν ⟨s, hsn⟩ + 1 ≤ ν ⟨s - 1, by omega⟩ ∨ ν' ⟨s, hsn⟩ + 1 ≤ ν' ⟨s - 1, by omega⟩ := by omega
    rcases e3 with e3 | e3
    · left
      refine sub_om hs1 hs ν hν (by omega) fun b hb => ?_
      have : ν b ≤ ν ⟨s, hsn⟩ := hν (by rw [Fin.le_def]; exact hb)
      omega
    · right
      refine sub_om hs1 hs ν' hν' (by omega) fun b hb => ?_
      have : ν' b ≤ ν' ⟨s, hsn⟩ := hν' (by rw [Fin.le_def]; exact hb)
      omega
  · have e3 : 1 ≤ ν ⟨s - 1, by omega⟩ ∨ 1 ≤ ν' ⟨s - 1, by omega⟩ := by omega
    rcases e3 with e3 | e3
    · left
      exact sub_om hs1 hs ν hν e3 fun b hb => by have := b.isLt; omega
    · right
      exact sub_om hs1 hs ν' hν' e3 fun b hb => by have := b.isLt; omega

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Introduce `sz hsz I ν ν' _ _ h`. Establish `h0 : ∀ t, ν t + ν' t = 0`.

Introduce `t`. Use `congrFun h t` as an intermediate fact. Simplify using `only [shapeDeg, Pi.add_apply] at this`. Rewrite using `[← this]`. Simplify using the standard rewrite rules.

Establish `e1 : ν = 0` using `funext fun t => by have := h0 t; simp only [Pi.zero_apply]; omega`. Establish `e2 : ν' = 0` using `funext fun t => by have := h0 t; simp only [Pi.zero_apply]; omega`. Substitute `e1 e2` using the available equality. Apply `Submodule.subset_span` to reduce the goal to its premises. Establish `h1` using `(dualWeylMul R r n 0 0 1 1).2`.

Conclude with `⟨1, h1, 1, h1, by simp [bideterminant]⟩`. Consider the case `succ K ih`. Introduce `sz hsz I ν ν' hν hν' h`. Establish `hb : bideterminant R sz hsz I = bideterminant R (fun k : Fin K => sz k.castSucc) (fun k => hsz k.castSucc) (fun k => I k.castSucc) * initMinor R (I (Fin.last K)) (hsz (Fin.last K))`. Unfold `bideterminant`.

Rewrite using `[Fin.prod_univ_castSucc]`. Rewrite `h` using `[shapeDeg_succ]`. Establish `hm` using `initMinor_mem R (I (Fin.last K)) (hsz (Fin.last K))`. Rewrite using `[hb]`. Break down `split_om (hsz (Fin.last K)) ν ν' _ hν hν' (shapeDeg_antitone _) h.symm with ⟨ν₁, h1, h2⟩ | ⟨ν₁, h1, h2⟩` into its components or cases.

Rewrite using `[h2]`. Use `prodSpan_mul_left R r n ν₁ ν' _ _ hm _ (ih _ _ _ ν₁ ν' h1 hν' ?_)` and prove the remaining obligations. Rewrite `h` using `[h2]`. Use function extensionality and compare the values at `t`. Use `congrFun h t` as an intermediate fact.

Simplify using `only [Pi.add_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2]`. Use `prodSpan_mul_right R r n ν ν₁ _ _ hm _ (ih _ _ _ ν ν₁ hν h1 ?_)` and prove the remaining obligations. Rewrite `h` using `[h2]`.

Use function extensionality and compare the values at `t`. Use `congrFun h t` as an intermediate fact. Simplify using `only [Pi.add_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem bidet_mem_prod (R : Type) [CommRing R] (r n : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (ν ν' : Fin n → ℕ), Antitone ν → Antitone ν' → shapeDeg sz = ν + ν' →
    bideterminant R sz hsz I ∈ ProdSpan R r n ν ν' := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I ν ν' _ _ h
    have h0 : ∀ t, ν t + ν' t = 0 := by
      intro t
      have := congrFun h t
      simp only [shapeDeg, Pi.add_apply] at this
      rw [← this]
      simp
    have e1 : ν = 0 := funext fun t => by have := h0 t; simp only [Pi.zero_apply]; omega
    have e2 : ν' = 0 := funext fun t => by have := h0 t; simp only [Pi.zero_apply]; omega
    subst e1 e2
    apply Submodule.subset_span
    have h1 := (dualWeylMul R r n 0 0 1 1).2
    exact ⟨1, h1, 1, h1, by simp [bideterminant]⟩
  | succ K ih =>
    intro sz hsz I ν ν' hν hν' h
    have hb : bideterminant R sz hsz I = bideterminant R (fun k : Fin K => sz k.castSucc) (fun k => hsz k.castSucc)
        (fun k => I k.castSucc) * initMinor R (I (Fin.last K)) (hsz (Fin.last K)) := by
      unfold bideterminant
      rw [Fin.prod_univ_castSucc]
    rw [shapeDeg_succ] at h
    have hm := initMinor_mem R (I (Fin.last K)) (hsz (Fin.last K))
    rw [hb]
    rcases split_om (hsz (Fin.last K)) ν ν' _ hν hν' (shapeDeg_antitone _) h.symm with ⟨ν₁, h1, h2⟩ | ⟨ν₁, h1, h2⟩
    · rw [h2]
      refine prodSpan_mul_left R r n ν₁ ν' _ _ hm _ (ih _ _ _ ν₁ ν' h1 hν' ?_)
      rw [h2] at h
      funext t
      have := congrFun h t
      simp only [Pi.add_apply] at this ⊢
      omega
    · rw [h2]
      refine prodSpan_mul_right R r n ν ν₁ _ _ hm _ (ih _ _ _ ν ν₁ hν h1 ?_)
      rw [h2] at h
      funext t
      have := congrFun h t
      simp only [Pi.add_apply] at this ⊢
      omega

/- English proof (translation)
Take `⟨b, hb, h2⟩` from `sSBasis R r n (ν + ν')`. Rewrite using `[← hb.2.1, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩` from `h2 i`. Use `show b i ∈ ProdSpan R r n ν ν'`.

Rewrite using `[hbm]`. Conclude with `bidet_mem_prod R r n K sz hsz I ν ν' hν hν' hshape`.
-/
theorem dualWeyl_le_prod (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν ν' : Fin n → ℕ) (hν : Antitone ν)
    (hν' : Antitone ν') : dualWeyl R r n (ν + ν') ≤ ProdSpan R r n ν ν' := by
  obtain ⟨b, hb, h2⟩ := sSBasis R r n (ν + ν')
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
  show b i ∈ ProdSpan R r n ν ν'
  rw [hbm]
  exact bidet_mem_prod R r n K sz hsz I ν ν' hν hν' hshape

/- English proof (translation)
Introduce `a b hab`. Use `h hab` as an intermediate fact. Use `show (lam b - lam (Fin.last m)).toNat ≤ (lam a - lam (Fin.last m)).toNat`. Use linear arithmetic over natural numbers and integers.
-/
theorem toNat_antitone {m : ℕ} (lam : Fin (m + 1) → ℤ) (h : Antitone lam) :
    Antitone fun t => (lam t - lam (Fin.last m)).toNat := by
  intro a b hab
  have := h hab
  show (lam b - lam (Fin.last m)).toNat ≤ (lam a - lam (Fin.last m)).toNat
  omega

/- English proof (translation)
Introduce `O Kf _ _ _ _ _ _ m lam mu Λ hΛ hl hm`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨g, hg, rfl⟩` from `hΛ`. Establish `hinj : Function.Injective (algebraMap O Kf)` using `IsFractionRing.injective O Kf`. Establish `hI` using `LatticeSystems.la_indep hinj`.

Establish `hlm : Antitone (lam + mu)` using `hl.add hm`. Rewrite using `[LatticeSystems.H0_eq_twisted_nabla hI m lam hl g hg, LatticeSystems.H0_eq_twisted_nabla hI m mu hm g hg, LatticeSystems.H0_eq_twisted_nabla hI m (lam + mu) hlm g hg]`. Use `set e : ℤ := lam (Fin.last m) with he`. Use `set e' : ℤ := mu (Fin.last m) with he'`. Set `T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf` to `((LinearMap.lsmul Kf _ (g.det ^ (-(e + e')))).restrictScalars O) ∘ₗ ((rowAct Kf (n := m + 1) g⁻¹).toLinearMap.restrictScalars O) ∘ₗ (mapAlgHom (Algebra.ofId O Kf)).toLinearMap`.

Establish `hT : ∀ x, T x = g.det ^ (-(e + e')) • rowAct Kf g⁻¹ (map (algebraMap O Kf) x)` using `fun x => rfl`. Introduce `X hX`. Take `⟨X0, hX0, rfl⟩` from `hX`. Rewrite `hX0` using `[toNat_add_last lam mu hl hm]`. Take `⟨x, hx, hxe⟩` from `hX0`.

Establish `hxe' : map (algebraMap O Kf) x = rowAct Kf g X0` using `hxe`. Establish `hXT : (LinearMap.restrictScalars O ((LinearMap.lsmul Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)) (g.det ^ (-(lam + mu) (Fin.last m))))) X0 = T x`. Rewrite using `[hT, hxe', rowAct_inv_left Kf _ _ g hg]`. Both sides reduce to the same expression. Rewrite using `[hXT]`.

Establish `hx2` using `dualWeyl_le_prod O (m + 1) (m + 1) _ _ (toNat_antitone lam hl) (toNat_antitone mu hm) hx`. Establish `key : ProdSpan O (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat) (fun t => (mu t - mu (Fin.last m)).toNat) ≤ (Submodule.span O {X | ∃ F ∈ nablaLTw O Kf m lam g, ∃ G ∈ nablaLTw O Kf m mu g, X = F * G}).comap T`. Unfold `ProdSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, f', hf', rfl⟩`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨g.det ^ (-e) • rowAct Kf g⁻¹ (map (algebraMap O Kf) f), ?_, g.det ^ (-e') • rowAct Kf g⁻¹ (map (algebraMap O Kf) f'), ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨rowAct Kf g⁻¹ (map (algebraMap O Kf) f), ⟨f, hf, (rowAct_inv_right Kf _ _ g hg _).symm⟩, rfl⟩`. Conclude with `⟨rowAct Kf g⁻¹ (map (algebraMap O Kf) f'), ⟨f', hf', (rowAct_inv_right Kf _ _ g hg _).symm⟩, rfl⟩`. Rewrite using `[hT, map_mul, map_mul, smul_mul_smul_comm, neg_add, zpow_add₀ hg.ne_zero]`.

Conclude with `key hx2`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, G, hG, rfl⟩`. Conclude with `mul_mem_riemannRochSpace_add O Kf m lam mu hl hm Λ hF hG`.
-/
theorem cartanOnto_proved : Formalism.MainNotions.flipOneThree.CartanOnto := by
  intro O Kf _ _ _ _ _ _ m lam mu Λ hΛ hl hm
  apply le_antisymm
  · obtain ⟨g, hg, rfl⟩ := hΛ
    have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
    have hI := LatticeSystems.la_indep hinj
    have hlm : Antitone (lam + mu) := hl.add hm
    rw [LatticeSystems.H0_eq_twisted_nabla hI m lam hl g hg, LatticeSystems.H0_eq_twisted_nabla hI m mu hm g hg,
      LatticeSystems.H0_eq_twisted_nabla hI m (lam + mu) hlm g hg]
    set e : ℤ := lam (Fin.last m) with he
    set e' : ℤ := mu (Fin.last m) with he'
    let T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
      ((LinearMap.lsmul Kf _ (g.det ^ (-(e + e')))).restrictScalars O) ∘ₗ
        ((rowAct Kf (n := m + 1) g⁻¹).toLinearMap.restrictScalars O) ∘ₗ
          (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
    have hT : ∀ x, T x = g.det ^ (-(e + e')) • rowAct Kf g⁻¹ (map (algebraMap O Kf) x) := fun x => rfl
    intro X hX
    obtain ⟨X0, hX0, rfl⟩ := hX
    rw [toNat_add_last lam mu hl hm] at hX0
    obtain ⟨x, hx, hxe⟩ := hX0
    have hxe' : map (algebraMap O Kf) x = rowAct Kf g X0 := hxe
    have hXT : (LinearMap.restrictScalars O ((LinearMap.lsmul Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
        (g.det ^ (-(lam + mu) (Fin.last m))))) X0 = T x := by
      rw [hT, hxe', rowAct_inv_left Kf _ _ g hg]
      rfl
    rw [hXT]
    have hx2 := dualWeyl_le_prod O (m + 1) (m + 1) _ _ (toNat_antitone lam hl) (toNat_antitone mu hm) hx
    have key : ProdSpan O (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat)
        (fun t => (mu t - mu (Fin.last m)).toNat) ≤
        (Submodule.span O {X | ∃ F ∈ nablaLTw O Kf m lam g, ∃ G ∈ nablaLTw O Kf m mu g, X = F * G}).comap T := by
      unfold ProdSpan
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, f', hf', rfl⟩
      apply Submodule.subset_span
      refine ⟨g.det ^ (-e) • rowAct Kf g⁻¹ (map (algebraMap O Kf) f), ?_,
        g.det ^ (-e') • rowAct Kf g⁻¹ (map (algebraMap O Kf) f'), ?_, ?_⟩
      · exact ⟨rowAct Kf g⁻¹ (map (algebraMap O Kf) f), ⟨f, hf, (rowAct_inv_right Kf _ _ g hg _).symm⟩, rfl⟩
      · exact ⟨rowAct Kf g⁻¹ (map (algebraMap O Kf) f'), ⟨f', hf', (rowAct_inv_right Kf _ _ g hg _).symm⟩, rfl⟩
      · rw [hT, map_mul, map_mul, smul_mul_smul_comm, neg_add, zpow_add₀ hg.ne_zero]
    exact key hx2
  · rw [Submodule.span_le]
    rintro _ ⟨F, hF, G, hG, rfl⟩
    exact mul_mem_riemannRochSpace_add O Kf m lam mu hl hm Λ hF hG

end Formalism.L2.G.Model
