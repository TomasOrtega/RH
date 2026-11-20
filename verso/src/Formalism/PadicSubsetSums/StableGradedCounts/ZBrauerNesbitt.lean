import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Lemmata.ScalarExtension.Scal

noncomputable section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z.BN

def simpleCps (k A : Type) [Field k] [Ring A] [Algebra k A] : Set (A → k[X]) :=
  {F | ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S)
    (_ : IsScalarTower k A S) (_ : FiniteDimensional k S) (_ : IsSimpleModule A S), F = cp k S}

open Module.Basis in
/- English proof (translation)
Set `m` to `Module.Free.ChooseBasisIndex R W`. Set `bW : Module.Basis m R W` to `Module.Free.chooseBasis R W`. Set `n` to `Module.Free.ChooseBasisIndex R (V ⧸ W)`. Set `bQ : Module.Basis n R (V ⧸ W)` to `Module.Free.chooseBasis R (V ⧸ W)`. Set `b` to `sumQuot bW bQ`.

Set `A : Matrix m m R` to `LinearMap.toMatrix bW bW (e.restrict he)`. Set `B : Matrix m n R` to `Matrix.of fun i l ↦ ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)`. Set `D : Matrix n n R` to `LinearMap.toMatrix bQ bQ (W.mapQ W e he)`. It suffices to establish `LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by`. Rewrite using `[← LinearMap.charpoly_toMatrix e b, this, ← LinearMap.charpoly_toMatrix _ bW, ← LinearMap.charpoly_toMatrix _ bQ, Matrix.charpoly_fromBlocks_zero₂₁]`.

Use extensionality with `u v`. Consider the cases of `u with`. Consider the case `inl i`. Consider the cases of `v with`. Consider the case `inl k`.

Simplify using `only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]`. Apply `sumQuot_repr_inl_of_mem` to reduce the goal to its premises. Consider the case `inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]`. Consider the case `inr j`. Consider the cases of `v with`.

Consider the case `inl k`. It suffices to establish `W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]`. Rewrite using `[← LinearMap.mem_ker, Submodule.ker_mkQ]`. Conclude with `he (Submodule.coe_mem (bW k))`. Consider the case `inr l`.

Simplify using `only [LinearMap.toMatrix_apply, sumQuot_repr_inr, Matrix.fromBlocks_apply₂₂, b, D]`. Rewrite using `[← sumQuot_inr bW bQ l, W.mapQ_apply]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_eq_restrict_mul_mapQ {R V : Type*} [Field R] [AddCommGroup V]
    [Module R V] [Module.Finite R V] (W : Submodule R V) (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Module.Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Module.Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this, ← LinearMap.charpoly_toMatrix _ bW,
      ← LinearMap.charpoly_toMatrix _ bQ, Matrix.charpoly_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

/- English proof (translation)
Establish `he : N.restrictScalars k ≤ (N.restrictScalars k).comap (Algebra.lsmul k k V a)` using `fun x hx => N.smul_mem a hx`. Unfold `cp`. Rewrite using `[charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) _ he]`. Both sides reduce to the same expression.
-/
theorem cp_quot {k A : Type} [Field k] [Ring A] [Algebra k A] {V : Type} [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    (N : Submodule A V) (a : A) :
    cp k V a = cp k N a * cp k (V ⧸ N) a := by
  have he : N.restrictScalars k ≤ (N.restrictScalars k).comap (Algebra.lsmul k k V a) :=
    fun x hx => N.smul_mem a hx
  unfold cp
  rw [charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) _ he]
  rfl

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ _ _ hn`. Distinguish the cases in `h0 : Module.finrank k V = 0`.

Establish `: (cp k V : A → k[X]) = 1`. Use function extensionality and compare the values at `a`. Establish `hm : (cp k V a).Monic` using `LinearMap.charpoly_monic _`. Establish `hd : (cp k V a).natDegree = 0`. Unfold `cp`.

Rewrite using `[LinearMap.charpoly_natDegree, h0]`. Conclude with `(Polynomial.Monic.natDegree_eq_zero hm).mp hd`. Rewrite using `[this]`. Conclude with `one_mem _`. Establish `hnt : Nontrivial V` using `Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero h0)`.

Establish `hart : IsArtinian A V` using `isArtinian_of_tower k inferInstance`. Take `⟨S, hS⟩` from `IsAtomic.exists_atom (Submodule A V)`. Establish `hsimp : IsSimpleModule A S` using `isSimpleModule_iff_isAtom.mpr hS`. Establish `h1 : (cp k V : A → k[X]) = cp k S * cp k (V ⧸ S)` using `funext (cp_quot S)`. Establish `hlt : Module.finrank k (V ⧸ S) < n`.

Establish `h2` using `congrArg Polynomial.natDegree (congrFun h1 0)`. Establish `hnS : Nontrivial S` using `IsSimpleModule.nontrivial A S`. Establish `hpos : 0 < Module.finrank k S` using `Module.finrank_pos`. Rewrite `h2` using `[Pi.mul_apply]`. Unfold `cp at h2`.

Rewrite `h2` using `[Polynomial.Monic.natDegree_mul (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _), LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1]`. Conclude with `mul_mem (Submonoid.subset_closure ⟨S, _, _, _, _, _, hsimp, rfl⟩) (ih _ hlt (V ⧸ S) rfl)`.
-/
theorem charpoly_mem_closure_simple {k A : Type} [Field k] [Ring A] [Algebra k A] :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
      [FiniteDimensional k V], Module.finrank k V = n →
      (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ _ hn
  by_cases h0 : Module.finrank k V = 0
  · have : (cp k V : A → k[X]) = 1 := by
      funext a
      have hm : (cp k V a).Monic := LinearMap.charpoly_monic _
      have hd : (cp k V a).natDegree = 0 := by
        unfold cp; rw [LinearMap.charpoly_natDegree, h0]
      exact (Polynomial.Monic.natDegree_eq_zero hm).mp hd
    rw [this]; exact one_mem _
  · have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero h0)
    have hart : IsArtinian A V := isArtinian_of_tower k inferInstance
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A V)
    have hsimp : IsSimpleModule A S := isSimpleModule_iff_isAtom.mpr hS
    have h1 : (cp k V : A → k[X]) = cp k S * cp k (V ⧸ S) := funext (cp_quot S)
    have hlt : Module.finrank k (V ⧸ S) < n := by
      have h2 := congrArg Polynomial.natDegree (congrFun h1 0)
      have hnS : Nontrivial S := IsSimpleModule.nontrivial A S
      have hpos : 0 < Module.finrank k S := Module.finrank_pos
      rw [Pi.mul_apply] at h2
      unfold cp at h2
      rw [Polynomial.Monic.natDegree_mul (LinearMap.charpoly_monic _)
        (LinearMap.charpoly_monic _), LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree,
        LinearMap.charpoly_natDegree] at h2
      omega
    rw [h1]
    exact mul_mem (Submonoid.subset_closure ⟨S, _, _, _, _, _, hsimp, rfl⟩) (ih _ hlt (V ⧸ S) rfl)

/- English proof (translation)
The claim follows from `charpoly_mem_closure_simple _ V rfl`.
-/
theorem cp_mem_closure {k A : Type} [Field k] [Ring A] [Algebra k A] (V : Type) [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] :
    (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) :=
  charpoly_mem_closure_simple _ V rfl

/- English proof (translation)
Establish `key : ∀ g, ∑ i ∈ t, ((a i : K) - (b i : K)) * (f i g).nextCoeff = 0`. Introduce `g`. Establish `h1` using `congrArg Polynomial.nextCoeff (h g)`. Rewrite `h1` using `[Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _), Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _)]`. Establish `e1 : ∀ (c : ι → ℕ), ∑ i ∈ t, (f i g ^ c i).nextCoeff = ∑ i ∈ t, (c i : K) * (f i g).nextCoeff`.

Introduce `c`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(hm i hi g).nextCoeff_pow, nsmul_eq_mul]`. Rewrite `h1` using `[e1, e1]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, h1, sub_self]`.

Introduce `i hi`. Conclude with `sub_eq_zero.mp (hli _ key i hi)`.
-/
theorem cast_eq_of_prod_eq {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0)
    (a b : ι → ℕ) (h : ∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) :
    ∀ i ∈ t, (a i : K) = (b i : K) := by
  have key : ∀ g, ∑ i ∈ t, ((a i : K) - (b i : K)) * (f i g).nextCoeff = 0 := by
    intro g
    have h1 := congrArg Polynomial.nextCoeff (h g)
    rw [Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _),
      Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _)] at h1
    have e1 : ∀ (c : ι → ℕ), ∑ i ∈ t, (f i g ^ c i).nextCoeff
        = ∑ i ∈ t, (c i : K) * (f i g).nextCoeff := by
      intro c
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hm i hi g).nextCoeff_pow, nsmul_eq_mul]
    rw [e1, e1] at h1
    simp only [sub_mul, Finset.sum_sub_distrib, h1, sub_self]
  intro i hi
  exact sub_eq_zero.mp (hli _ key i hi)

/- English proof (translation)
Take `⟨p, hp⟩` from `ExpChar.exists K`. Consider the cases of `hp with`. Consider the case `zero`. Introduce `N a b _ h i hi`. Conclude with `Nat.cast_injective (R := K) (cast_eq_of_prod_eq t f hm hli a b h i hi)`.

Consider the case `prime hprime`. Establish `: Fact p.Prime` using `⟨hprime⟩`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`.

Introduce `a b hN h`. Establish `hc` using `cast_eq_of_prod_eq t f hm hli a b h`. Establish `hmod : ∀ i ∈ t, a i ≡ b i [MOD p]` using `fun i hi => (CharP.natCast_eq_natCast K p).mp (hc i hi)`. Take `⟨c, hcdef⟩ : ∃ c : ι → ℕ, c = fun i => min (a i) (b i)` from `⟨_, rfl⟩`. Take `⟨a', ha'def⟩ : ∃ a' : ι → ℕ, a' = fun i => (a i - c i) / p` from `⟨_, rfl⟩`.

Take `⟨b', hb'def⟩ : ∃ b' : ι → ℕ, b' = fun i => (b i - c i) / p` from `⟨_, rfl⟩`. Establish `ha : ∀ i ∈ t, a i = c i + p * a' i`. Introduce `i hi`. Establish `hd : p ∣ a i - c i`. Break down `le_total (a i) (b i) with hle | hle` into its components or cases.

Simplify using `[hcdef, hle]`. Establish `: c i = b i` using `by simp [hcdef, hle]`. Rewrite using `[this]`. Conclude with `(Nat.modEq_iff_dvd' hle).mp (hmod i hi).symm`. Establish `hle : c i ≤ a i` using `by simp [hcdef]`.

Rewrite using `[ha'def]`. Simplify using `only`. Rewrite using `[Nat.mul_div_cancel' hd]`. Use linear arithmetic over natural numbers and integers. Establish `hb : ∀ i ∈ t, b i = c i + p * b' i`.

Introduce `i hi`. Establish `hd : p ∣ b i - c i`. Break down `le_total (b i) (a i) with hle | hle` into its components or cases. Simplify using `[hcdef, hle]`. Establish `: c i = a i` using `by simp [hcdef, hle]`.

Rewrite using `[this]`. Conclude with `(Nat.modEq_iff_dvd' hle).mp (hmod i hi)`. Establish `hle : c i ≤ b i` using `by simp [hcdef]`. Rewrite using `[hb'def]`. Simplify using `only`.

Rewrite using `[Nat.mul_div_cancel' hd]`. Use linear arithmetic over natural numbers and integers. Establish `hsplit : ∀ (e e' : ι → ℕ), (∀ i ∈ t, e i = c i + p * e' i) → ∀ g, ∏ i ∈ t, f i g ^ e i = (∏ i ∈ t, f i g ^ c i) * (∏ i ∈ t, f i g ^ e' i) ^ p`. Introduce `e e' he g`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[he i hi, pow_add, ← pow_mul, mul_comm p]`. Establish `h' : ∀ g, ∏ i ∈ t, f i g ^ a' i = ∏ i ∈ t, f i g ^ b' i`. Introduce `g`. Establish `h2` using `h g`.

Rewrite `h2` using `[hsplit a a' ha g, hsplit b b' hb g]`. Establish `hne : (∏ i ∈ t, f i g ^ c i) ≠ 0` using `(monic_prod_of_monic _ _ fun i hi => (hm i hi g).pow _).ne_zero`. Establish `h3` using `mul_left_cancel₀ hne h2`. Conclude with `frobenius_inj K[X] p h3`. Establish `h2p : 2 ≤ p` using `hprime.two_le`.

Establish `hsum : 2 * ∑ i ∈ t, (a' i + b' i) ≤ ∑ i ∈ t, (a i + b i)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Rewrite using `[ha i hi, hb i hi]`. Establish `h1 : 2 * a' i ≤ p * a' i` using `Nat.mul_le_mul_right _ h2p`.

Establish `h2 : 2 * b' i ≤ p * b' i` using `Nat.mul_le_mul_right _ h2p`. Use linear arithmetic over natural numbers and integers. Break down `Nat.eq_zero_or_pos N with hN0 | hNpos` into its components or cases. Introduce `i hi`. Establish `hz : ∑ i ∈ t, (a i + b i) = 0` using `by omega`.

Use `(Finset.sum_eq_zero_iff.mp hz) i hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlt : ∑ i ∈ t, (a' i + b' i) < N` using `by omega`. Establish `hab` using `ih _ hlt a' b' le_rfl h'`. Introduce `i hi`.

Rewrite using `[ha i hi, hb i hi, hab i hi]`.
-/
theorem exponents_eq_of_monic_products {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0) :
    ∀ (N : ℕ) (a b : ι → ℕ), ∑ i ∈ t, (a i + b i) ≤ N →
      (∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) → ∀ i ∈ t, a i = b i := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  cases hp with
  | zero =>
    intro N a b _ h i hi
    exact Nat.cast_injective (R := K) (cast_eq_of_prod_eq t f hm hli a b h i hi)
  | prime hprime =>
    have : Fact p.Prime := ⟨hprime⟩
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro a b hN h
    have hc := cast_eq_of_prod_eq t f hm hli a b h
    have hmod : ∀ i ∈ t, a i ≡ b i [MOD p] := fun i hi =>
      (CharP.natCast_eq_natCast K p).mp (hc i hi)
    obtain ⟨c, hcdef⟩ : ∃ c : ι → ℕ, c = fun i => min (a i) (b i) := ⟨_, rfl⟩
    obtain ⟨a', ha'def⟩ : ∃ a' : ι → ℕ, a' = fun i => (a i - c i) / p := ⟨_, rfl⟩
    obtain ⟨b', hb'def⟩ : ∃ b' : ι → ℕ, b' = fun i => (b i - c i) / p := ⟨_, rfl⟩
    have ha : ∀ i ∈ t, a i = c i + p * a' i := by
      intro i hi
      have hd : p ∣ a i - c i := by
        rcases le_total (a i) (b i) with hle | hle
        · simp [hcdef, hle]
        · have : c i = b i := by simp [hcdef, hle]
          rw [this]
          exact (Nat.modEq_iff_dvd' hle).mp (hmod i hi).symm
      have hle : c i ≤ a i := by simp [hcdef]
      rw [ha'def]
      simp only
      rw [Nat.mul_div_cancel' hd]
      omega
    have hb : ∀ i ∈ t, b i = c i + p * b' i := by
      intro i hi
      have hd : p ∣ b i - c i := by
        rcases le_total (b i) (a i) with hle | hle
        · simp [hcdef, hle]
        · have : c i = a i := by simp [hcdef, hle]
          rw [this]
          exact (Nat.modEq_iff_dvd' hle).mp (hmod i hi)
      have hle : c i ≤ b i := by simp [hcdef]
      rw [hb'def]
      simp only
      rw [Nat.mul_div_cancel' hd]
      omega
    have hsplit : ∀ (e e' : ι → ℕ), (∀ i ∈ t, e i = c i + p * e' i) → ∀ g,
        ∏ i ∈ t, f i g ^ e i = (∏ i ∈ t, f i g ^ c i) * (∏ i ∈ t, f i g ^ e' i) ^ p := by
      intro e e' he g
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [he i hi, pow_add, ← pow_mul, mul_comm p]
    have h' : ∀ g, ∏ i ∈ t, f i g ^ a' i = ∏ i ∈ t, f i g ^ b' i := by
      intro g
      have h2 := h g
      rw [hsplit a a' ha g, hsplit b b' hb g] at h2
      have hne : (∏ i ∈ t, f i g ^ c i) ≠ 0 :=
        (monic_prod_of_monic _ _ fun i hi => (hm i hi g).pow _).ne_zero
      have h3 := mul_left_cancel₀ hne h2
      exact frobenius_inj K[X] p h3
    have h2p : 2 ≤ p := hprime.two_le
    have hsum : 2 * ∑ i ∈ t, (a' i + b' i) ≤ ∑ i ∈ t, (a i + b i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [ha i hi, hb i hi]
      have h1 : 2 * a' i ≤ p * a' i := Nat.mul_le_mul_right _ h2p
      have h2 : 2 * b' i ≤ p * b' i := Nat.mul_le_mul_right _ h2p
      omega
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · intro i hi
      have hz : ∑ i ∈ t, (a i + b i) = 0 := by omega
      have := (Finset.sum_eq_zero_iff.mp hz) i hi
      omega
    · have hlt : ∑ i ∈ t, (a' i + b' i) < N := by omega
      have hab := ih _ hlt a' b' le_rfl h'
      intro i hi
      rw [ha i hi, hb i hi, hab i hi]

/- English proof (translation)
The claim follows from `exponents_eq_of_monic_products t f hm hli _ a b le_rfl h`.
-/
theorem exponents_eq {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0)
    (a b : ι → ℕ) (h : ∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) :
    ∀ i ∈ t, a i = b i :=
  exponents_eq_of_monic_products t f hm hli _ a b le_rfl h

/- English proof (translation)
Unfold `cp`. Rewrite using `[← LinearMap.charpoly_toMatrix _ (Module.Free.chooseBasis k V), LinearMap.trace_eq_matrix_trace k (Module.Free.chooseBasis k V), Matrix.trace_eq_neg_charpoly_nextCoeff, neg_neg]`.
-/
theorem nextCoeff_cp {k A : Type} [Field k] [Ring A] [Algebra k A] (V : Type) [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] (a : A) :
    (cp k V a).nextCoeff = - LinearMap.trace k V (Algebra.lsmul k k V a) := by
  unfold cp
  rw [← LinearMap.charpoly_toMatrix _ (Module.Free.chooseBasis k V),
    LinearMap.trace_eq_matrix_trace k (Module.Free.chooseBasis k V),
    Matrix.trace_eq_neg_charpoly_nextCoeff, neg_neg]

def Kills {K A : Type} [Field K] [Ring A] [Algebra K A] (t : Finset (A → K[X])) (a : A) : Prop :=
  ∀ F ∈ t, ∃ (S : Type) (_ : AddCommGroup S) (_ : Module K S) (_ : Module A S)
    (_ : IsScalarTower K A S) (_ : FiniteDimensional K S), F = cp K S ∧ ∀ s : S, a • s = 0

/- English proof (translation)
Take `⟨S, _, _, _, _, _, rfl, hS⟩` from `h F hF`. Rewrite using `[nextCoeff_cp]`. Establish `: Algebra.lsmul K K S a = 0`. Use extensionality with `s`. Simplify using `using hS s`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem Kills.nextCoeff {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) {F : A → K[X]} (hF : F ∈ t) : (F a).nextCoeff = 0 := by
  obtain ⟨S, _, _, _, _, _, rfl, hS⟩ := h F hF
  rw [nextCoeff_cp]
  have : Algebra.lsmul K K S a = 0 := by
    ext s
    simpa using hS s
  rw [this]; simp

/- English proof (translation)
Introduce `F hF`. Take `⟨S, i1, i2, i3, i4, i5, hFS, hS⟩` from `h F hF`. Conclude with `⟨S, i1, i2, i3, i4, i5, hFS, fun s => by rw [mul_smul, hS, smul_zero]⟩`.
-/
theorem Kills.mul_left {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) (b : A) : Kills t (b * a) := by
  intro F hF
  obtain ⟨S, i1, i2, i3, i4, i5, hFS, hS⟩ := h F hF
  exact ⟨S, i1, i2, i3, i4, i5, hFS, fun s => by rw [mul_smul, hS, smul_zero]⟩

/- English proof (translation)
Introduce `F hF`. Take `⟨S, i1, i2, i3, i4, i5, hFS, hS⟩` from `h F hF`. Conclude with `⟨S, i1, i2, i3, i4, i5, hFS, fun s => by rw [mul_smul, hS]⟩`.
-/
theorem Kills.mul_right {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) (b : A) : Kills t (a * b) := by
  intro F hF
  obtain ⟨S, i1, i2, i3, i4, i5, hFS, hS⟩ := h F hF
  exact ⟨S, i1, i2, i3, i4, i5, hFS, fun s => by rw [mul_smul, hS]⟩

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Use `IsSimpleModule.nontrivial A S0` as an intermediate fact. Take `⟨s, hs⟩` from `exists_ne (0 : S0)`. Conclude with `⟨1, fun F hF => absurd hF (Finset.notMem_empty F), s, by simpa using hs⟩`.

Consider the case `insert F t hFt ih`. Establish `ht' : ↑t ⊆ simpleCps K A` using `fun G hG => ht (by simp [Finset.mem_coe.mp hG])`. Establish `h0' : (cp K S0 : A → K[X]) ∉ t` using `fun h => h0 (Finset.mem_insert_of_mem h)`. Establish `hne : (cp K S0 : A → K[X]) ≠ F` using `fun h => h0 (by simp [h])`. Take `⟨a, ha, s', hs'⟩` from `ih ht' h0'`.

Take `⟨S1, i1, i2, i3, i4, i5, i6, hF⟩` from `ht (show F ∈ ↑(insert F t) by simp)`. Establish `hx : ∃ x : A, (∀ w : S1, x • w = 0) ∧ ∃ s : S0, x • s ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨f, hf⟩` from `exists_ne_zero_hom (k := K) (A := A) (W := S1) (S := S0) hcon`.

Establish `e : S1 ≃ₗ[A] S0` using `LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)`. Conclude with `hne (by rw [hF]; funext b; exact (cp_congr e b).symm)`. Take `⟨x, hx1, s, hs⟩` from `hx`. Take `⟨u, hu⟩` from `IsSimpleModule.toSpanSingleton_surjective A hs s'`. Use `⟨a * (u * x), ?_, s, ?_⟩` and prove the remaining obligations.

Introduce `G hG`. Break down `Finset.mem_insert.mp hG with rfl | hG` into its components or cases. Conclude with `⟨S1, i1, i2, i3, i4, i5, hF, fun w => by rw [mul_smul, mul_smul, hx1, smul_zero, smul_zero]⟩`. Conclude with `ha.mul_right _ G hG`. Establish `: u • x • s = s'` using `by simpa using hu`.

Rewrite using `[mul_smul, mul_smul, this]`. Conclude with `hs'`.
-/
theorem exists_kills {K A : Type} [Field K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (h0 : (cp K S0 : A → K[X]) ∉ t) :
    ∃ a : A, Kills t a ∧ ∃ s : S0, a • s ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := IsSimpleModule.nontrivial A S0
    obtain ⟨s, hs⟩ := exists_ne (0 : S0)
    exact ⟨1, fun F hF => absurd hF (Finset.notMem_empty F), s, by simpa using hs⟩
  | insert F t hFt ih =>
    have ht' : ↑t ⊆ simpleCps K A := fun G hG => ht (by simp [Finset.mem_coe.mp hG])
    have h0' : (cp K S0 : A → K[X]) ∉ t := fun h => h0 (Finset.mem_insert_of_mem h)
    have hne : (cp K S0 : A → K[X]) ≠ F := fun h => h0 (by simp [h])
    obtain ⟨a, ha, s', hs'⟩ := ih ht' h0'
    obtain ⟨S1, i1, i2, i3, i4, i5, i6, hF⟩ := ht (show F ∈ ↑(insert F t) by simp)
    have hx : ∃ x : A, (∀ w : S1, x • w = 0) ∧ ∃ s : S0, x • s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨f, hf⟩ := exists_ne_zero_hom (k := K) (A := A) (W := S1) (S := S0) hcon
      have e : S1 ≃ₗ[A] S0 := LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)
      exact hne (by rw [hF]; funext b; exact (cp_congr e b).symm)
    obtain ⟨x, hx1, s, hs⟩ := hx
    obtain ⟨u, hu⟩ := IsSimpleModule.toSpanSingleton_surjective A hs s'
    refine ⟨a * (u * x), ?_, s, ?_⟩
    · intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact ⟨S1, i1, i2, i3, i4, i5, hF, fun w => by rw [mul_smul, mul_smul, hx1, smul_zero, smul_zero]⟩
      · exact ha.mul_right _ G hG
    · have : u • x • s = s' := by simpa using hu
      rw [mul_smul, mul_smul, this]
      exact hs'

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.ScalarIdentities.goal1 .. | (apply Bl.ScalarIdentities.goal1 <;> assumption) | (intros; apply Bl.ScalarIdentities.goal1 <;> assumption)`.
-/
theorem exists_lsmul_eq {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (φ : S0 →ₗ[K] S0) :
    ∃ u : A, ∀ v : S0, u • v = φ v := by
  first | exact Bl.ScalarIdentities.goal1 .. | (apply Bl.ScalarIdentities.goal1 <;> assumption) | (intros; apply Bl.ScalarIdentities.goal1 <;> assumption)

/- English proof (translation)
Introduce `F0 hF0`. Take `⟨S0, i1, i2, i3, i4, i5, i6, hF⟩` from `ht (Finset.mem_coe.mpr hF0)`. Take `⟨a, ha, s, hs⟩` from `exists_kills S0 (t.erase F0) (fun G hG => ht (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hG)))) (by rw [← hF]; simp)`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Module.Dual K S0, l (a • s) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Conclude with `hs ((Module.forall_dual_apply_eq_zero_iff K _).mp hcon)`. Take `⟨u, hu⟩` from `exists_lsmul_eq (A := A) S0 (l.smulRight s)`. Establish `hlin : Algebra.lsmul K K S0 (u * a) = (l ∘ₗ Algebra.lsmul K K S0 a).smulRight s`. Use extensionality with `v`.

Simplify using `[hu]`. Establish `h1 : (F0 (u * a)).nextCoeff = - l (a • s)`. Rewrite using `[hF, nextCoeff_cp, hlin, LinearMap.trace_smulRight]`. Simplify using the standard rewrite rules. Establish `h2` using `h (u * a)`.

Rewrite using `[← Finset.add_sum_erase t _ hF0, Finset.sum_eq_zero (fun G hG => by`. Rewrite `h2` using `[(ha.mul_left u).nextCoeff hG, mul_zero]), add_zero, h1]`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `h3`. Conclude with `absurd (neg_eq_zero.mp h3) hl`.
-/
theorem lin_indep {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (c : (A → K[X]) → K)
    (h : ∀ a : A, ∑ F ∈ t, c F * (F a).nextCoeff = 0) : ∀ F ∈ t, c F = 0 := by
  classical
  intro F0 hF0
  obtain ⟨S0, i1, i2, i3, i4, i5, i6, hF⟩ := ht (Finset.mem_coe.mpr hF0)
  obtain ⟨a, ha, s, hs⟩ := exists_kills S0 (t.erase F0)
    (fun G hG => ht (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hG))))
    (by rw [← hF]; simp)
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual K S0, l (a • s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs ((Module.forall_dual_apply_eq_zero_iff K _).mp hcon)
  obtain ⟨u, hu⟩ := exists_lsmul_eq (A := A) S0 (l.smulRight s)
  have hlin : Algebra.lsmul K K S0 (u * a) = (l ∘ₗ Algebra.lsmul K K S0 a).smulRight s := by
    ext v
    simp [hu]
  have h1 : (F0 (u * a)).nextCoeff = - l (a • s) := by
    rw [hF, nextCoeff_cp, hlin, LinearMap.trace_smulRight]
    simp
  have h2 := h (u * a)
  rw [← Finset.add_sum_erase t _ hF0, Finset.sum_eq_zero (fun G hG => by
    rw [(ha.mul_left u).nextCoeff hG, mul_zero]), add_zero, h1] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (neg_eq_zero.mp h3) hl

/- English proof (translation)
Establish `hV` using `cp_mem_closure (k := K) (A := A) V`. Establish `hW` using `cp_mem_closure (k := K) (A := A) W`. Rewrite `hV`, `hW` using `[Submonoid.mem_closure_iff_exists_finset_subset]`. Take `⟨a, t1, ht1, ha, hVa⟩` from `hV`. Take `⟨b, t2, ht2, hb, hWb⟩` from `hW`.

Establish `ht : (↑(t1 ∪ t2) : Set (A → K[X])) ⊆ simpleCps K A`. Introduce `F hF`. Break down `Finset.mem_union.1 (Finset.mem_coe.1 hF) with h | h` into its components or cases. Conclude with `ht1 h`. Conclude with `ht2 h`.

Establish `hVa' : ∏ F ∈ t1 ∪ t2, F ^ a F = cp K V`. Rewrite using `[← hVa]`. Use `symm`. Use `Finset.prod_subset Finset.subset_union_left ?_` and prove the remaining obligations. Introduce `F _ hF`.

Establish `: a F = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hF (ha h0)`. Simplify using `[this]`. Establish `hWb' : ∏ F ∈ t1 ∪ t2, F ^ b F = cp K W`.

Rewrite using `[← hWb]`. Use `symm`. Use `Finset.prod_subset Finset.subset_union_right ?_` and prove the remaining obligations. Introduce `F _ hF`. Establish `: b F = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hF (hb h0)`. Simplify using `[this]`. Establish `hlin : ∀ F ∈ t1 ∪ t2, ∃ T : A →ₗ[K] K, ∀ x, (F x).nextCoeff = T x`. Introduce `F hF`.

Take `⟨S, _, _, _, _, _, _, rfl⟩` from `ht (Finset.mem_coe.2 hF)`. Conclude with `⟨-(LinearMap.trace K S ∘ₗ (Algebra.lsmul K K S).toLinearMap), fun x => by`. Rewrite using `[nextCoeff_cp]`. Use the proof step `rfl⟩`. Establish `key : ∀ F ∈ t1 ∪ t2, a F = b F`.

Apply `exponents_eq (Γ := Γ) (t1 ∪ t2) (fun F g => F g.1)` to reduce the goal to its premises. Introduce `F hF g`. Take `⟨S, _, _, _, _, _, _, rfl⟩` from `ht (Finset.mem_coe.2 hF)`. Conclude with `LinearMap.charpoly_monic _`. Introduce `c hc`.

Apply `lin_indep (t1 ∪ t2) ht c` to reduce the goal to its premises. Introduce `x`. Establish `hx : x ∈ Submodule.span K Γ` using `hΓ ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hc ⟨x, hx⟩`.

Consider the case `zero`. Use `Finset.sum_eq_zero fun F hF => ?_` and prove the remaining obligations. Take `⟨T, hT⟩` from `hlin F hF`. Rewrite using `[hT, map_zero, mul_zero]`. Consider the case `add x y _ _ hx hy`.

Establish `hxy : ∑ F ∈ t1 ∪ t2, c F * (F (x + y)).nextCoeff = ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff + ∑ F ∈ t1 ∪ t2, c F * (F y).nextCoeff`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun F hF => ?_` and prove the remaining obligations. Take `⟨T, hT⟩` from `hlin F hF`. Rewrite using `[hT, hT, hT, map_add, mul_add]`.

Rewrite using `[hxy, hx, hy, add_zero]`. Consider the case `smul r x _ hx`. Establish `hrx : ∑ F ∈ t1 ∪ t2, c F * (F (r • x)).nextCoeff = r * ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun F hF => ?_` and prove the remaining obligations.

Take `⟨T, hT⟩` from `hlin F hF`. Rewrite using `[hT, hT, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrx, hx, mul_zero]`. Introduce `g`.

Use `h g.1 g.2` as an intermediate fact. Rewrite `this` using `[← hVa', ← hWb']`. Simplify `this` using `[Finset.prod_apply, Pi.pow_apply]`. Rewrite using `[← hVa', ← hWb']`. Conclude with `Finset.prod_congr rfl (fun F hF => by rw [key F hF])`.
-/
theorem cp_eq_of_span {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (Γ : Set A) (hΓ : Submodule.span K Γ = ⊤) (V W : Type) [AddCommGroup V]
    [Module K V] [Module A V] [IsScalarTower K A V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [Module A W] [IsScalarTower K A W] [FiniteDimensional K W]
    (h : ∀ g ∈ Γ, cp K V g = cp K W g) : (cp K V : A → K[X]) = cp K W := by
  classical
  have hV := cp_mem_closure (k := K) (A := A) V
  have hW := cp_mem_closure (k := K) (A := A) W
  rw [Submonoid.mem_closure_iff_exists_finset_subset] at hV hW
  obtain ⟨a, t1, ht1, ha, hVa⟩ := hV
  obtain ⟨b, t2, ht2, hb, hWb⟩ := hW
  have ht : (↑(t1 ∪ t2) : Set (A → K[X])) ⊆ simpleCps K A := by
    intro F hF
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hF) with h | h
    · exact ht1 h
    · exact ht2 h
  have hVa' : ∏ F ∈ t1 ∪ t2, F ^ a F = cp K V := by
    rw [← hVa]; symm
    refine Finset.prod_subset Finset.subset_union_left ?_
    intro F _ hF
    have : a F = 0 := by
      by_contra h0
      exact hF (ha h0)
    simp [this]
  have hWb' : ∏ F ∈ t1 ∪ t2, F ^ b F = cp K W := by
    rw [← hWb]; symm
    refine Finset.prod_subset Finset.subset_union_right ?_
    intro F _ hF
    have : b F = 0 := by
      by_contra h0
      exact hF (hb h0)
    simp [this]
  have hlin : ∀ F ∈ t1 ∪ t2, ∃ T : A →ₗ[K] K, ∀ x, (F x).nextCoeff = T x := by
    intro F hF
    obtain ⟨S, _, _, _, _, _, _, rfl⟩ := ht (Finset.mem_coe.2 hF)
    exact ⟨-(LinearMap.trace K S ∘ₗ (Algebra.lsmul K K S).toLinearMap), fun x => by
      rw [nextCoeff_cp]; rfl⟩
  have key : ∀ F ∈ t1 ∪ t2, a F = b F := by
    apply exponents_eq (Γ := Γ) (t1 ∪ t2) (fun F g => F g.1)
    · intro F hF g
      obtain ⟨S, _, _, _, _, _, _, rfl⟩ := ht (Finset.mem_coe.2 hF)
      exact LinearMap.charpoly_monic _
    · intro c hc
      apply lin_indep (t1 ∪ t2) ht c
      intro x
      have hx : x ∈ Submodule.span K Γ := hΓ ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact hc ⟨x, hx⟩
      | zero =>
        refine Finset.sum_eq_zero fun F hF => ?_
        obtain ⟨T, hT⟩ := hlin F hF
        rw [hT, map_zero, mul_zero]
      | add x y _ _ hx hy =>
        have hxy : ∑ F ∈ t1 ∪ t2, c F * (F (x + y)).nextCoeff =
            ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff + ∑ F ∈ t1 ∪ t2, c F * (F y).nextCoeff := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun F hF => ?_
          obtain ⟨T, hT⟩ := hlin F hF
          rw [hT, hT, hT, map_add, mul_add]
        rw [hxy, hx, hy, add_zero]
      | smul r x _ hx =>
        have hrx : ∑ F ∈ t1 ∪ t2, c F * (F (r • x)).nextCoeff =
            r * ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          obtain ⟨T, hT⟩ := hlin F hF
          rw [hT, hT, map_smul, smul_eq_mul]; ring
        rw [hrx, hx, mul_zero]
    · intro g
      have := h g.1 g.2
      rw [← hVa', ← hWb'] at this
      simpa [Finset.prod_apply, Pi.pow_apply] using this
  rw [← hVa', ← hWb']
  exact Finset.prod_congr rfl (fun F hF => by rw [key F hF])

section group
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def bc (K : Type) [Field K] [Algebra k K] (ρ : Representation k G V) :
    Representation K G (K ⊗[k] V) where
  toFun g := (ρ g).baseChange K
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_on with`. Consider the case `of g => exact ⟨MonoidAlgebra.of K G g, by simp [bc], by simp [bc]⟩`. Consider the case `add x y hx hy`. Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`.

Conclude with `⟨x' + y', by simp [h1, h3, LinearMap.baseChange_add], by simp [h2, h4, LinearMap.baseChange_add]⟩`. Consider the case `smul r x hx`. Take `⟨x', h1, h2⟩` from `hx`. Conclude with `⟨algebraMap k K r • x', by rw [map_smul (bc K ρ).asAlgebraHom, h1, map_smul ρ.asAlgebraHom, LinearMap.baseChange_smul, algebraMap_smul], by rw [map_smul (bc K τ).asAlgebraHom, h2, map_smul τ.asAlgebraHom, LinearMap.baseChange_smul, algebraMap_smul]⟩`.
-/
theorem exists_lift (K : Type) [Field K] [Algebra k K] (ρ : Representation k G V)
    (τ : Representation k G W) (x : MonoidAlgebra k G) :
    ∃ y : MonoidAlgebra K G, (bc K ρ).asAlgebraHom y = (ρ.asAlgebraHom x).baseChange K ∧
      (bc K τ).asAlgebraHom y = (τ.asAlgebraHom x).baseChange K := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact ⟨MonoidAlgebra.of K G g, by simp [bc], by simp [bc]⟩
  | add x y hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', by simp [h1, h3, LinearMap.baseChange_add],
      by simp [h2, h4, LinearMap.baseChange_add]⟩
  | smul r x hx =>
    obtain ⟨x', h1, h2⟩ := hx
    exact ⟨algebraMap k K r • x', by rw [map_smul (bc K ρ).asAlgebraHom, h1, map_smul ρ.asAlgebraHom, LinearMap.baseChange_smul,
        algebraMap_smul],
      by rw [map_smul (bc K τ).asAlgebraHom, h2, map_smul τ.asAlgebraHom, LinearMap.baseChange_smul,
        algebraMap_smul]⟩

/- English proof (translation)
Rewrite using `[cp, ← LinearEquiv.charpoly_conj ρ.asModuleEquiv]`. Use `congr 1`.
-/
theorem cp_asModule [FiniteDimensional k V] (ρ : Representation k G V) (x : MonoidAlgebra k G) :
    cp k ρ.asModule x = (ρ.asAlgebraHom x).charpoly := by
  rw [cp, ← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
  congr 1

/- English proof (translation)
Rewrite using `[cp_asModule, Representation.asAlgebraHom_of, ← LinearMap.charpoly_baseChange]`. Both sides reduce to the same expression.
-/
theorem cp_bc_of [FiniteDimensional k V] (K : Type) [Field K] [Algebra k K]
    (ρ : Representation k G V) (g : G) :
    cp K (bc K ρ).asModule (MonoidAlgebra.of K G g) = (ρ g).charpoly.map (algebraMap k K) := by
  rw [cp_asModule, Representation.asAlgebraHom_of, ← LinearMap.charpoly_baseChange]
  rfl

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `f _`. Conclude with `Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff f)`.
-/
theorem span_of (K : Type) [Field K] :
    Submodule.span K (Set.range (MonoidAlgebra.of K G)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff f)

/- English proof (translation)
Take `⟨y, hy1, hy2⟩` from `exists_lift K ρ τ x`. Establish `key` using `cp_eq_of_span (K := K) (A := MonoidAlgebra K G) _ (span_of K) (bc K ρ).asModule (bc K τ).asModule (by`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[cp_bc_of, cp_bc_of, h g])`. Establish `h2` using `congrFun key y`.

Rewrite `h2` using `[cp_asModule, cp_asModule, hy1, hy2, LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange]`. Conclude with `Polynomial.map_injective _ (algebraMap k K).injective h2`.
-/
theorem charpoly_asAlgebraHom_eq_alt [FiniteDimensional k V] [FiniteDimensional k W]
    (K : Type) [Field K] [Algebra k K] [IsAlgClosed K]
    (ρ : Representation k G V) (τ : Representation k G W)
    (h : ∀ g, (ρ g).charpoly = (τ g).charpoly) (x : MonoidAlgebra k G) :
    (ρ.asAlgebraHom x).charpoly = (τ.asAlgebraHom x).charpoly := by
  obtain ⟨y, hy1, hy2⟩ := exists_lift K ρ τ x
  have key := cp_eq_of_span (K := K) (A := MonoidAlgebra K G)
    _ (span_of K) (bc K ρ).asModule (bc K τ).asModule (by
      rintro _ ⟨g, rfl⟩
      rw [cp_bc_of, cp_bc_of, h g])
  have h2 := congrFun key y
  rw [cp_asModule, cp_asModule, hy1, hy2, LinearMap.charpoly_baseChange,
    LinearMap.charpoly_baseChange] at h2
  exact Polynomial.map_injective _ (algebraMap k K).injective h2

/- English proof (translation)
The claim follows from `charpoly_asAlgebraHom_eq_alt (AlgebraicClosure k) ρ τ h x`.
-/
theorem charpoly_asAlgebraHom_eq [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    (h : ∀ g, (ρ g).charpoly = (τ g).charpoly) (x : MonoidAlgebra k G) :
    (ρ.asAlgebraHom x).charpoly = (τ.asAlgebraHom x).charpoly :=
  charpoly_asAlgebraHom_eq_alt (AlgebraicClosure k) ρ τ h x

end group

end Formalism.IrreducibleCountingLemmas.Z.BN

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `k _ G _ V W _ _ _ _ _ _ ρ τ hρ hτ h`. Take `⟨e⟩` from `brauer_nesbitt_algebra k (MonoidAlgebra k G) ρ.asModule τ.asModule hρ hτ (fun a => by`. Use `BN.charpoly_asAlgebraHom_eq ρ τ h a` as an intermediate fact. Rewrite `this` using `[← BN.cp_asModule, ← BN.cp_asModule]`. Conclude with `this)`.

Use `⟨ρ.asModuleEquiv.symm ≪≫ₗ e.restrictScalars k ≪≫ₗ τ.asModuleEquiv, fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]`. Rewrite using `[Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]`.
-/
theorem brauer_nesbitt : BrauerNesbitt := by
  intro k _ G _ V W _ _ _ _ _ _ ρ τ hρ hτ h
  obtain ⟨e⟩ := brauer_nesbitt_algebra k (MonoidAlgebra k G) ρ.asModule τ.asModule hρ hτ
    (fun a => by
      have := BN.charpoly_asAlgebraHom_eq ρ τ h a
      rw [← BN.cp_asModule, ← BN.cp_asModule] at this
      exact this)
  refine ⟨ρ.asModuleEquiv.symm ≪≫ₗ e.restrictScalars k ≪≫ₗ τ.asModuleEquiv, fun g => ?_⟩
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]

end Formalism.IrreducibleCountingLemmas.Z
