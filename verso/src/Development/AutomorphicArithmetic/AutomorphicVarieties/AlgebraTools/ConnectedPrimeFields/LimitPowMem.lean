import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Imports

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Take `⟨n, hn⟩` from `hx`. Use `⟨n * (M + M), fun K hK => ?_⟩` and prove the remaining obligations. Establish `h1 : x ^ (n * (M + M)) ∈ b ^ M ⊔ c ^ M`. Rewrite using `[pow_mul]`. Conclude with `Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_mem_pow hn _)`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hK`. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_right _ _ h1`.
-/
private theorem UpperTheory.V.AlgebraTools.Conn.limit_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K₀, ∀ K, K₀ ≤ K → x ^ K ∈ b ^ M ⊔ c ^ M := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n * (M + M), fun K hK => ?_⟩
  have h1 : x ^ (n * (M + M)) ∈ b ^ M ⊔ c ^ M := by
    rw [pow_mul]
    exact Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_mem_pow hn _)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [pow_add]
  exact Ideal.mul_mem_right _ _ h1

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.
-/
private theorem smodEq_ideal_pow_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Introduce `A R _ _ _ I _ J u v b c hJ hJI hreg hIJ hbc hb hc hu hv`. Set `P : ℕ → ℕ → Module.Dual A R → A → Prop` to `fun m N l a => ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N → algebraMap A R y = β + γ → l β - y * a ∈ J m`. Establish `weak : ∀ m m' N N' l a, m ≤ m' → N ≤ N' → P m' N l a → P m N' l a`. Introduce `m m' N N' l a hm hN h y β γ hβ hγ hy`. Conclude with `hJ hm (h y β γ (Ideal.pow_le_pow_right hN hβ) (Ideal.pow_le_pow_right hN hγ) hy)`.

Establish `uniq : ∀ m N l a a', P m N l a → P m N l a' → a - a' ∈ J m`. Introduce `m N l a a' h h'`. Take `⟨K, hK⟩` from `limit_pow_mem b c (algebraMap A R u) hu N`. Establish `hmem` using `hK K le_rfl`. Rewrite `hmem` using `[← map_pow]`.

Take `⟨β, hβ, γ, hγ, hsum⟩` from `Submodule.mem_sup.mp hmem`. Establish `e1` using `h (u ^ K) β γ hβ hγ hsum.symm`. Establish `e2` using `h' (u ^ K) β γ hβ hγ hsum.symm`. Apply `(hreg m K).1` to reduce the goal to its premises. Establish `e3` using `Ideal.sub_mem _ e2 e1`.

Use `e3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `exist : ∀ m, ∃ N, m ≤ N ∧ ∀ l, ∃ a, P m N l a`. Introduce `m`. Take `⟨N₁, hN₁⟩` from `hIJ m`.

Take `⟨P₀, hP₀⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hbc (Submodule.FG.mul hb hc)`. Use `⟨max m (P₀ * N₁), le_max_left _ _, fun l => ?_⟩` and prove the remaining obligations. Take `⟨Ku, hKu⟩` from `limit_pow_mem b c (algebraMap A R u) hu (max m (P₀ * N₁))`. Take `⟨Kv, hKv⟩` from `limit_pow_mem b c (algebraMap A R v) hv (max m (P₀ * N₁))`. Establish `hprod : b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) ≤ Ideal.map (algebraMap A R) (J m)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu' : algebraMap A R (u ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁))`. Rewrite using `[map_pow]`. Conclude with `hKu _ (le_max_left _ _)`. Establish `hv' : algebraMap A R (v ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁))`.

Rewrite using `[map_pow]`. Conclude with `hKv _ (le_max_right _ _)`. Take `⟨a, ha⟩` from `level (J m) (u ^ (max Ku Kv)) (v ^ (max Ku Kv)) _ _ (hreg m _) hprod hu' hv' l`. Conclude with `⟨a, ha⟩`. Use `choose N hNm hN using exist`.

Use `choose a ha using hN`. Establish `hcauchy : ∀ l m n, m ≤ n → a m l - a n l ∈ J m`. Introduce `l m n hmn`. Apply `uniq m (max (N m) (N n)) l` to reduce the goal to its premises. Conclude with `weak m m (N m) _ l _ le_rfl (le_max_left _ _) (ha m l)`.

Conclude with `weak m n (N n) _ l _ hmn (le_max_right _ _) (ha n l)`. Establish `hlim : ∀ l, ∃ L : A, ∀ n, a n l - L ∈ I ^ n`. Introduce `l`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := I) (M := A) inferInstance (f := fun n => a n l) (fun {m n} hmn => by`. Rewrite using `[smodEq_ideal_pow_iff_sub_mem]`.

Conclude with `hJI m (hcauchy l m n hmn))`. Conclude with `⟨L, fun n => (smodEq_ideal_pow_iff_sub_mem I n _ _).mp (hL n)⟩`. Use `choose L hL using hlim`. Establish `haus : ∀ x : A, (∀ n, x ∈ I ^ n) → x = 0`. Introduce `x hx`.

Apply `IsHausdorff.haus (I := I) inferInstance x` to reduce the goal to its premises. Introduce `n`. Rewrite using `[smodEq_ideal_pow_iff_sub_mem, sub_zero]`. Conclude with `hx n`. Establish `hadd : ∀ m l l', a m (l + l') - a m l - a m l' ∈ J m`.

Introduce `m l l'`. Establish `h3 : P m (N m) (l + l') (a m l + a m l')`. Introduce `y β γ hβ hγ hy`. Establish `e` using `Ideal.add_mem _ (ha m l y β γ hβ hγ hy) (ha m l' y β γ hβ hγ hy)`. Use `e using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [LinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `uniq m (N m) (l + l') _ _ (ha m (l + l')) h3`. Use `e using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hsmul : ∀ m (r : A) l, a m (r • l) - r * a m l ∈ J m`. Introduce `m r l`. Establish `h3 : P m (N m) (r • l) (r * a m l)`. Introduce `y β γ hβ hγ hy`. Establish `e` using `Ideal.mul_mem_left _ r (ha m l y β γ hβ hγ hy)`.

Use `e using 1` and compare the differences between its conclusion and the goal. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `uniq m (N m) (r • l) _ _ (ha m (r • l)) h3`. Set `Φ : Module.Dual A (Module.Dual A R)` to `{ toFun := L map_add' := by`.

Introduce `l l'`. Establish `h0` using `haus (L (l + l') - (L l + L l')) (fun n => by`. Establish `e` using `Ideal.sub_mem _ (Ideal.sub_mem _ (hL (l + l') n) (hL l n)) (hL l' n)`. Establish `e2` using `hJI n (hadd n l l')`. Establish `e3` using `Ideal.sub_mem _ e2 e`.

Use `e3 using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Conclude with `sub_eq_zero.mp h0`. Use the proof step `map_smul' := by`. Introduce `r l`.

Establish `h0` using `haus (L (r • l) - r * L l) (fun n => by`. Establish `e` using `Ideal.sub_mem _ (hL (r • l) n) (Ideal.mul_mem_left _ r (hL l n))`. Establish `e2` using `hJI n (hsmul n r l)`. Establish `e3` using `Ideal.sub_mem _ e2 e`. Use `e3 using 1` and compare the differences between its conclusion and the goal.

Use the proof step `ring)`. Rewrite `h0` using `[sub_eq_zero]`. Simplify using `using h0 }`. Use `⟨Φ, fun m => ⟨N m, hNm m, fun y β γ hβ hγ hy l => ?_⟩⟩` and prove the remaining obligations. Establish `e1` using `hJI m (ha m l y β γ hβ hγ hy)`.

Establish `e2` using `Ideal.mul_mem_left _ y (hL l m)`. Establish `e3` using `Ideal.add_mem _ e1 e2`. Use `show l β - y * L l ∈ I ^ m`. Use `e3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.AlgebraTools.Conn.limit :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c : Ideal R),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) →
      (∀ m, ∃ N, I ^ N ≤ J m) → b * c ≤ (I.map (algebraMap A R)).radical → b.FG → c.FG →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      ∃ a : Module.Dual A (Module.Dual A R), ∀ m, ∃ N, m ≤ N ∧ ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N →
        algebraMap A R y = β + γ → ∀ l : Module.Dual A R, l β - y * a l ∈ I ^ m := by
  intro A R _ _ _ I _ J u v b c hJ hJI hreg hIJ hbc hb hc hu hv
  let P : ℕ → ℕ → Module.Dual A R → A → Prop := fun m N l a =>
    ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N → algebraMap A R y = β + γ → l β - y * a ∈ J m
  have weak : ∀ m m' N N' l a, m ≤ m' → N ≤ N' → P m' N l a → P m N' l a := by
    intro m m' N N' l a hm hN h y β γ hβ hγ hy
    exact hJ hm (h y β γ (Ideal.pow_le_pow_right hN hβ) (Ideal.pow_le_pow_right hN hγ) hy)
  have uniq : ∀ m N l a a', P m N l a → P m N l a' → a - a' ∈ J m := by
    intro m N l a a' h h'
    obtain ⟨K, hK⟩ := limit_pow_mem b c (algebraMap A R u) hu N
    have hmem := hK K le_rfl
    rw [← map_pow] at hmem
    obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp hmem
    have e1 := h (u ^ K) β γ hβ hγ hsum.symm
    have e2 := h' (u ^ K) β γ hβ hγ hsum.symm
    apply (hreg m K).1
    have e3 := Ideal.sub_mem _ e2 e1
    convert e3 using 1
    ring
  have exist : ∀ m, ∃ N, m ≤ N ∧ ∀ l, ∃ a, P m N l a := by
    intro m
    obtain ⟨N₁, hN₁⟩ := hIJ m
    obtain ⟨P₀, hP₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hbc (Submodule.FG.mul hb hc)
    refine ⟨max m (P₀ * N₁), le_max_left _ _, fun l => ?_⟩
    obtain ⟨Ku, hKu⟩ := limit_pow_mem b c (algebraMap A R u) hu (max m (P₀ * N₁))
    obtain ⟨Kv, hKv⟩ := limit_pow_mem b c (algebraMap A R v) hv (max m (P₀ * N₁))
    have hprod : b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) ≤ Ideal.map (algebraMap A R) (J m) := by
      calc b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) = (b * c) ^ (max m (P₀ * N₁)) := (mul_pow b c _).symm
        _ ≤ (b * c) ^ (P₀ * N₁) := Ideal.pow_le_pow_right (le_max_right _ _)
        _ = ((b * c) ^ P₀) ^ N₁ := pow_mul _ _ _
        _ ≤ (I.map (algebraMap A R)) ^ N₁ := Ideal.pow_right_mono hP₀ N₁
        _ = (I ^ N₁).map (algebraMap A R) := (Ideal.map_pow _ _ _).symm
        _ ≤ (J m).map (algebraMap A R) := Ideal.map_mono hN₁
    have hu' : algebraMap A R (u ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKu _ (le_max_left _ _)
    have hv' : algebraMap A R (v ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKv _ (le_max_right _ _)
    obtain ⟨a, ha⟩ := level (J m) (u ^ (max Ku Kv)) (v ^ (max Ku Kv)) _ _ (hreg m _) hprod hu' hv' l
    exact ⟨a, ha⟩
  choose N hNm hN using exist
  choose a ha using hN
  have hcauchy : ∀ l m n, m ≤ n → a m l - a n l ∈ J m := by
    intro l m n hmn
    apply uniq m (max (N m) (N n)) l
    · exact weak m m (N m) _ l _ le_rfl (le_max_left _ _) (ha m l)
    · exact weak m n (N n) _ l _ hmn (le_max_right _ _) (ha n l)
  have hlim : ∀ l, ∃ L : A, ∀ n, a n l - L ∈ I ^ n := by
    intro l
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := fun n => a n l)
      (fun {m n} hmn => by
        rw [smodEq_ideal_pow_iff_sub_mem]
        exact hJI m (hcauchy l m n hmn))
    exact ⟨L, fun n => (smodEq_ideal_pow_iff_sub_mem I n _ _).mp (hL n)⟩
  choose L hL using hlim
  have haus : ∀ x : A, (∀ n, x ∈ I ^ n) → x = 0 := by
    intro x hx
    apply IsHausdorff.haus (I := I) inferInstance x
    intro n
    rw [smodEq_ideal_pow_iff_sub_mem, sub_zero]
    exact hx n
  have hadd : ∀ m l l', a m (l + l') - a m l - a m l' ∈ J m := by
    intro m l l'
    have h3 : P m (N m) (l + l') (a m l + a m l') := by
      intro y β γ hβ hγ hy
      have e := Ideal.add_mem _ (ha m l y β γ hβ hγ hy) (ha m l' y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.add_apply]
      ring
    have e := uniq m (N m) (l + l') _ _ (ha m (l + l')) h3
    convert e using 1
    ring
  have hsmul : ∀ m (r : A) l, a m (r • l) - r * a m l ∈ J m := by
    intro m r l
    have h3 : P m (N m) (r • l) (r * a m l) := by
      intro y β γ hβ hγ hy
      have e := Ideal.mul_mem_left _ r (ha m l y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.smul_apply, smul_eq_mul]
      ring
    exact uniq m (N m) (r • l) _ _ (ha m (r • l)) h3
  let Φ : Module.Dual A (Module.Dual A R) :=
    { toFun := L
      map_add' := by
        intro l l'
        have h0 := haus (L (l + l') - (L l + L l')) (fun n => by
          have e := Ideal.sub_mem _ (Ideal.sub_mem _ (hL (l + l') n) (hL l n)) (hL l' n)
          have e2 := hJI n (hadd n l l')
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        exact sub_eq_zero.mp h0
      map_smul' := by
        intro r l
        have h0 := haus (L (r • l) - r * L l) (fun n => by
          have e := Ideal.sub_mem _ (hL (r • l) n) (Ideal.mul_mem_left _ r (hL l n))
          have e2 := hJI n (hsmul n r l)
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        rw [sub_eq_zero] at h0
        simpa using h0 }
  refine ⟨Φ, fun m => ⟨N m, hNm m, fun y β γ hβ hγ hy l => ?_⟩⟩
  have e1 := hJI m (ha m l y β γ hβ hγ hy)
  have e2 := Ideal.mul_mem_left _ y (hL l m)
  have e3 := Ideal.add_mem _ e1 e2
  show l β - y * L l ∈ I ^ m
  convert e3 using 1
  ring
