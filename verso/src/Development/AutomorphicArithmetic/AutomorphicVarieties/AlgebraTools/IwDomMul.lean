import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFundNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨p, hp, h⟩` from `hx`. Rewrite using `[← h]`. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit`.
-/
private theorem unif_lt {x : kˣ} (hx : IsUnif x) : valuation k (x : k) < 1 := by
  obtain ⟨p, hp, h⟩ := hx
  rw [← h]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit

/- English proof (translation)
Take `⟨p, hp, h⟩` from `hx`. Take `⟨a, u, hu⟩` from `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := k) hp y.ne_zero`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h1 : valuation k (algebraMap 𝒪[k] k (u : 𝒪[k])) = 1` using `(Valuation.integer.integers (valuation k)).valuation_unit u`. Rewrite using `[hu, h, Units.smul_def, Algebra.smul_def, map_mul, h1, one_mul, map_zpow₀]`.
-/
private theorem unif_dec {x : kˣ} (hx : IsUnif x) (y : kˣ) :
    ∃ a : ℤ, valuation k (y : k) = valuation k (x : k) ^ a := by
  obtain ⟨p, hp, h⟩ := hx
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := k) hp y.ne_zero
  refine ⟨a, ?_⟩
  have h1 : valuation k (algebraMap 𝒪[k] k (u : 𝒪[k])) = 1 :=
    (Valuation.integer.integers (valuation k)).valuation_unit u
  rw [hu, h, Units.smul_def, Algebra.smul_def, map_mul, h1, one_mul, map_zpow₀]

/- English proof (translation)
Introduce `i j hij`. Establish `h0 : 0 < valuation k (x : k)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)`. Simplify using `only [Units.val_zpow_eq_zpow_val, map_zpow₀]`. Conclude with `(zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).2 (ha hij)`.
-/
private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).2 (ha hij)

/- English proof (translation)
Establish `hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c` using `⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩`. Use `⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩` and prove the remaining obligations. Use `Nat.find_min hex hi push Not at this` as an intermediate fact. Take `⟨j, hj, hc⟩` from `this`. Conclude with `hc.trans_le (ha (Fin.le_def.2 hj))`.

Assume the negation of the conclusion as `h`. Conclude with `absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)`.
-/
private theorem exists_cut (a : Fin n → ℤ) (ha : Antitone a) (c : ℤ) :
    ∃ m ≤ n, ∀ i : Fin n, (i : ℕ) < m ↔ c < a i := by
  classical
  have hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c := ⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj, hc⟩ := this
    exact hc.trans_le (ha (Fin.le_def.2 hj))
  · by_contra h
    exact absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)

/- English proof (translation)
Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`. Use extensionality with `i j`. Simplify using `only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]`.
-/
private theorem const_central (y : kˣ) : diagT k (Fin n) (fun _ => y) ∈ Subgroup.center (GL (Fin n) k) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]

/- English proof (translation)
Take `⟨-, -, hn, hv⟩` from `memIwC k n C`. Establish `h : diagT k (Fin n) u ∈ iwahori k (Fin n)`. Rewrite using `[← (memIwC k n C).2.1]`. Conclude with `Subgroup.mem_sup_right ⟨u, fun i _ => (hv _).2 (hu i), rfl⟩`. Rewrite using `[Subgroup.mem_set_normalizer_iff]`.

Introduce `b`. Use `⟨fun hb => hn _ h b hb, fun hb => ?_⟩` and prove the remaining obligations. Use `hn _ (inv_mem h) _ hb` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
private theorem unit_norm (C : Subgroup 𝓀[k]ˣ) (u : Fin n → kˣ) (hu : ∀ i, valuation k (u i : k) = 1) :
    diagT k (Fin n) u ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  obtain ⟨-, -, hn, hv⟩ := memIwC k n C
  have h : diagT k (Fin n) u ∈ iwahori k (Fin n) := by
    rw [← (memIwC k n C).2.1]
    exact Subgroup.mem_sup_right ⟨u, fun i _ => (hv _).2 (hu i), rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  refine ⟨fun hb => hn _ h b hb, fun hb => ?_⟩
  have := hn _ (inv_mem h) _ hb
  simpa [mul_assoc] using this

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `k _ _ _ _ n C A M _ _ _ ρ`. Establish `hH` using `(heckePairIwC k n C).1`. Take `⟨F, hU, hM, hL, hUI, hLI, hF⟩` from `factTorus k n C`. Establish `hmul : ∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t'))`. Introduce `t t' ht ht'`.

Rewrite using `[map_mul]`. Conclude with `(leviMul A _ M ρ _ F _ _ hH ((hF t).2 ht) ((hF t').2 ht') (Or.inl (hF t).1)).2`. Use `⟨hmul, fun hq t ht => ?_, fun C' h t ht => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_isUnif (k := k)`. Establish `hfund : ∀ m ≤ n, IsUnit (hk ρ (iwC k n C) (pw x (fund n m)))`.

Introduce `m hm`. Take `⟨w, hw⟩` from `fundNorm k n C x hx m hm`. Take `⟨-, -, hu, hx⟩` from `hkNorm A _ M ρ _ _ hH hw`. Establish `e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m))`. Rewrite using `[map_inv, inv_mul_cancel_left]`.

Rewrite using `[e, (hx _).2]`. Conclude with `(permUnit k n C A M ρ _ hq).mul hu`. Establish `key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) → IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) fun i => x ^ a i))`. Introduce `c N`. Proceed by induction on `N with`.

Consider the case `zero`. Introduce `a _ hb`. Establish `e : (fun i => x ^ a i) = fun _ : Fin n => x ^ c`. Use function extensionality and compare the values at `i`. Use `hb i` as an intermediate fact.

Rewrite using `[show a i = c by omega]`. Rewrite using `[e]`. Conclude with `(hkNorm A _ M ρ _ _ hH (Subgroup.center_le_normalizer _ (const_central _))).2.2.1`. Consider the case `succ N ih`. Introduce `a ha hb`.

Take `⟨m, hm, hc⟩` from `exists_cut a ha c`. Establish `hfa : Antitone (fund n m)`. Introduce `i j hij`. Use `Fin.le_def.1 hij` as an intermediate fact. Simplify using `only [fund]`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `ha' : Antitone (a - fund n m)`. Introduce `i j hij`. Establish `h1` using `ha hij`. Establish `h2` using `hc i`.

Establish `h3` using `hc j`. Establish `h4` using `hb i`. Establish `h5` using `hb j`. Simplify using `only [fund, Pi.sub_apply]`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N`. Introduce `i`. Establish `h2` using `hc i`. Establish `h4` using `hb i`. Simplify using `only [fund, Pi.sub_apply]`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]`. Rewrite using `[e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa)]`.

Conclude with `(ih _ ha' hb').mul (hfund m hm)`. Use `choose a hav using fun i => unif_dec hx (t i)`. Establish `h0 : 0 < valuation k (x : k)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)`. Establish `ha : Antitone a`. Introduce `i j hij`.

Use `ht i j hij` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Conclude with `(zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).1 this`. Take `⟨c, hc⟩` from `(Set.finite_range a).bddBelow`. Take `⟨d, hd⟩` from `(Set.finite_range a).bddAbove`.

Establish `hk1` using `key c (d - c).toNat a ha fun i => by`. Establish `h1 : c ≤ a i` using `hc ⟨i, rfl⟩`. Establish `h2 : a i ≤ d` using `hd ⟨i, rfl⟩`. Use linear arithmetic over natural numbers and integers. Establish `hn` using `unit_norm C (fun i => t i * (x ^ a i)⁻¹) fun i => by`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hav]`. Conclude with `mul_inv_cancel₀ (zpow_ne_zero _ h0.ne')`. Take `⟨-, -, hu, hx⟩` from `hkNorm A _ M ρ _ _ hH hn`. Establish `e : t = (fun i => t i * (x ^ a i)⁻¹) * fun i => x ^ a i`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[e, map_mul, (hx _).1]`. Conclude with `hu.mul hk1`. Take `⟨F', hU', hM', hL', hUI', hLI', hF'⟩` from `factTorus k n C'`. Use `leviLevel A _ M ρ _ _ h F' F _ (heckePairIwC k n C').1 hH ((heckePairIwC k n C).2.2 C').1 (hU.trans hU'.symm) (hM.trans hM'.symm) (hL.trans hL'.symm) ?_ ?_ ?_ ((hF' t).2 ht) ?_` and prove the remaining obligations.

Rewrite using `[hUI', ← hUI]`. Conclude with `inf_le_right`. Rewrite using `[hLI', ← hLI]`. Conclude with `inf_le_right`. Introduce `a ha b hb`.

Conclude with `(memIwC k n C).2.2.1 a (((memIwC k n C').1 a).1 ha).1 b hb`. Introduce and unpack `j ⟨hj, -⟩`. Rewrite `hj` using `[hM']`. Take `⟨s, rfl⟩` from `hj`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem UpperTheory.V.AlgebraTools.domMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t'))) ∧ (IsUnit (resCard k : A) → ∀ t : Fin n → kˣ, Dom t → IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) t))) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ) (h : iwC k n C ≤ iwC k n C') (t : Fin n → kˣ), Dom t → hk ρ (iwC k n C) (diagT k (Fin n) t) ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ (iwC k n C') (diagT k (Fin n) t) ∧ trc ρ (iwC k n C') (iwC k n C) ∘ₗ hk ρ (iwC k n C) (diagT k (Fin n) t) = hk ρ (iwC k n C') (diagT k (Fin n) t) ∘ₗ trc ρ (iwC k n C') (iwC k n C) := by
  intro k _ _ _ _ n C A M _ _ _ ρ
  have hH := (heckePairIwC k n C).1
  obtain ⟨F, hU, hM, hL, hUI, hLI, hF⟩ := factTorus k n C
  have hmul : ∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t')) := by
    intro t t' ht ht'
    rw [map_mul]
    exact (leviMul A _ M ρ _ F _ _ hH ((hF t).2 ht) ((hF t').2 ht') (Or.inl (hF t).1)).2
  refine ⟨hmul, fun hq t ht => ?_, fun C' h t ht => ?_⟩
  · obtain ⟨x, hx⟩ := exists_isUnif (k := k)
    have hfund : ∀ m ≤ n, IsUnit (hk ρ (iwC k n C) (pw x (fund n m))) := by
      intro m hm
      obtain ⟨w, hw⟩ := fundNorm k n C x hx m hm
      obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hw
      have e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m)) := by
        rw [map_inv, inv_mul_cancel_left]
      rw [e, (hx _).2]
      exact (permUnit k n C A M ρ _ hq).mul hu
    have key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) →
        IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) fun i => x ^ a i)) := by
      intro c N
      induction N with
      | zero =>
        intro a _ hb
        have e : (fun i => x ^ a i) = fun _ : Fin n => x ^ c := by
          funext i
          have := hb i
          rw [show a i = c by omega]
        rw [e]
        exact (hkNorm A _ M ρ _ _ hH (Subgroup.center_le_normalizer _ (const_central _))).2.2.1
      | succ N ih =>
        intro a ha hb
        obtain ⟨m, hm, hc⟩ := exists_cut a ha c
        have hfa : Antitone (fund n m) := by
          intro i j hij
          have := Fin.le_def.1 hij
          simp only [fund]
          split_ifs <;> omega
        have ha' : Antitone (a - fund n m) := by
          intro i j hij
          have h1 := ha hij
          have h2 := hc i
          have h3 := hc j
          have h4 := hb i
          have h5 := hb j
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N := by
          intro i
          have h2 := hc i
          have h4 := hb i
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i := by
          funext i
          simp only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]
        rw [e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa)]
        exact (ih _ ha' hb').mul (hfund m hm)
    choose a hav using fun i => unif_dec hx (t i)
    have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
    have ha : Antitone a := by
      intro i j hij
      have := ht i j hij
      rw [hav, hav] at this
      exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).1 this
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range a).bddAbove
    have hk1 := key c (d - c).toNat a ha fun i => by
      have h1 : c ≤ a i := hc ⟨i, rfl⟩
      have h2 : a i ≤ d := hd ⟨i, rfl⟩
      omega
    have hn := unit_norm C (fun i => t i * (x ^ a i)⁻¹) fun i => by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hav]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h0.ne')
    obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hn
    have e : t = (fun i => t i * (x ^ a i)⁻¹) * fun i => x ^ a i := by
      funext i
      simp
    rw [e, map_mul, (hx _).1]
    exact hu.mul hk1
  · obtain ⟨F', hU', hM', hL', hUI', hLI', hF'⟩ := factTorus k n C'
    refine leviLevel A _ M ρ _ _ h F' F _ (heckePairIwC k n C').1 hH ((heckePairIwC k n C).2.2 C').1
      (hU.trans hU'.symm) (hM.trans hM'.symm) (hL.trans hL'.symm) ?_ ?_ ?_ ((hF' t).2 ht) ?_
    · rw [hUI', ← hUI]
      exact inf_le_right
    · rw [hLI', ← hLI]
      exact inf_le_right
    · intro a ha b hb
      exact (memIwC k n C).2.2.1 a (((memIwC k n C').1 a).1 ha).1 b hb
    · rintro j ⟨hj, -⟩
      rw [hM'] at hj
      obtain ⟨s, rfl⟩ := hj
      rw [← map_mul, ← map_mul, mul_comm]
