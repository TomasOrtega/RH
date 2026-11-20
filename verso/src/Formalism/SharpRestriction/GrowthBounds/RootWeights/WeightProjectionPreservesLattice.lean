import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsClearDenominators

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section pw
variable {n : ℕ} {K : Type} [Field K] {L W : Type} [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]

/- English proof (translation)
Proceed by induction on `m generalizing f with`. Consider the case `zero`. Use extensionality with `x`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]`. Both sides reduce to the same expression.
-/
theorem llcomp_pow_apply (X : Module.End K W) (m : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.llcomp K L W W X) ^ m) f = (X ^ m) ∘ₗ f := by
  induction m generalizing f with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    rfl

/- English proof (translation)
Proceed by induction on `j generalizing f with`. Consider the case `zero`. Use extensionality with `x`. Simplify using the standard rewrite rules. Consider the case `succ j ih`.

Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc]`. Both sides reduce to the same expression.
-/
theorem lcomp_pow_apply (Y : Module.End K L) (j : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.lcomp K W Y) ^ j) f = f ∘ₗ (Y ^ j) := by
  induction j generalizing f with
  | zero =>
    ext x
    simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    rfl

/- English proof (translation)
Establish `hc : Commute (LinearMap.llcomp K L W W (E a b)) ((-1 : K) • LinearMap.lcomp K W (EL a b))`. Use `Commute.smul_right ?_ (-1 : K)` and prove the remaining obligations. Use extensionality with `g y`. Both sides reduce to the same expression. Establish `ht : homRepresentation EL E a b = LinearMap.llcomp K L W W (E a b) + (-1 : K) • LinearMap.lcomp K W (EL a b)`.

Rewrite using `[neg_one_smul, ← sub_eq_add_neg]`. Both sides reduce to the same expression. Rewrite using `[ht, hc.add_pow, LinearMap.sum_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, Module.End.natCast_apply, smul_pow, LinearMap.smul_apply, map_nsmul, map_smul, llcomp_pow_apply, lcomp_pow_apply, LinearMap.comp_apply]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul K, smul_smul]`.
-/
theorem homRepresentation_pow_apply (EL : GLOps n K L) (E : GLOps n K W) (a b : Fin n) (k : ℕ) (f : L →ₗ[K] W) (x : L) :
    ((homRepresentation EL E a b) ^ k) f x =
      ∑ m ∈ range (k + 1), ((k.choose m : K) * (-1) ^ (k - m)) • (E a b ^ m) (f ((EL a b ^ (k - m)) x)) := by
  have hc : Commute (LinearMap.llcomp K L W W (E a b)) ((-1 : K) • LinearMap.lcomp K W (EL a b)) := by
    refine Commute.smul_right ?_ (-1 : K)
    ext g y
    rfl
  have ht : homRepresentation EL E a b =
      LinearMap.llcomp K L W W (E a b) + (-1 : K) • LinearMap.lcomp K W (EL a b) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  rw [ht, hc.add_pow, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Module.End.mul_apply, Module.End.natCast_apply, smul_pow, LinearMap.smul_apply,
    map_nsmul, map_smul, llcomp_pow_apply, lcomp_pow_apply, LinearMap.comp_apply]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul]

end pw

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

/- English proof (translation)
Proceed by induction on `j generalizing x with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
theorem restrictRepresentation_pow_coe (E : GLOps n (KK O) W) (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (j : ℕ)
    (x : L) : (((restrictRepresentation E L hL a b) ^ j) x : W) = (E a b ^ j) (x : W) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

/- English proof (translation)
Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem hx z`.
-/
theorem int_smul_mem_lattice (M : Submodule O W) (z : ℤ) {x : W} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨sh, shwt, shM⟩ : ∃ sh : Fin n → ℤ → ℕ → Module.End (KK O) W, (∀ a c d ρ x, x ∈ weightSp E ρ → sh a c d x = ((Ring.choose (ρ a + c) d : ℤ) : KK O) • x) ∧ (∀ a c d x, x ∈ M → sh a c d x ∈ M) := by`. Use `⟨fun a c d => ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : KK O) • binomE E a ij.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c d ρ x hx`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, binomial_diagonal_apply_weight E a ρ x hx, smul_smul]`.

Rewrite using `[← Finset.sum_smul, Ring.add_choose_eq d (Commute.all _ _)]`. Use `push_cast`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun ij _ => by ring`. Introduce `a c d x hx`.

Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun ij _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`. Conclude with `int_smul_mem_lattice M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)`. Establish `hT : ∀ nu : Fin n → ℤ, ∃ (T : Module.End (KK O) W) (h : (Fin n → ℤ) → ℤ), h mu = 1 ∧ (nu ≠ mu → h nu = 0) ∧ (∀ ρ, ∀ x ∈ weightSp E ρ, T x = ((h ρ : ℤ) : KK O) • x) ∧ ∀ x ∈ M, T x ∈ M`.

Introduce `nu`. Distinguish the cases in `hne : nu = mu`. Use `⟨1, fun _ => 1, rfl, fun h => absurd hne h, fun ρ x _ => by simp, fun x hx => by simpa using hx⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Function.ne_iff.1 hne`. Break down `lt_or_gt_of_ne ha with hlt | hgt` into its components or cases.

Take `⟨d, hd⟩ : ∃ d : ℕ, mu a - nu a = (d : ℤ)` from `⟨(mu a - nu a).toNat, by omega⟩`. Establish `hd0 : 0 < d` using `by omega`. Use `⟨sh a (-(nu a)) d, fun ρ => Ring.choose (ρ a + -(nu a)) d, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Ring.choose (mu a + -(nu a)) d = 1`. Rewrite using `[show mu a + -(nu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]`.

Both sides reduce to the same expression. Introduce `_ show Ring.choose (nu a + -(nu a)) d = 0`. Rewrite using `[show nu a + -(nu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hd0]`. Both sides reduce to the same expression. Introduce `ρ x hx`.

Conclude with `shwt a _ _ ρ x hx`. Introduce `x hx`. Conclude with `shM a _ _ x hx`. Take `⟨d, hd⟩ : ∃ d : ℕ, nu a - mu a = (d : ℤ)` from `⟨(nu a - mu a).toNat, by omega⟩`. Use `⟨sh a (-(mu a)) 0 - sh a (-(mu a)) d, fun ρ => Ring.choose (ρ a + -(mu a)) 0 - Ring.choose (ρ a + -(mu a)) d, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show Ring.choose (mu a + -(mu a)) 0 - Ring.choose (mu a + -(mu a)) d = 1`. Establish `hd0 : 0 < d` using `by omega`. Rewrite using `[Ring.choose_zero_right, show mu a + -(mu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hd0]`. Both sides reduce to the same expression. Introduce `_ show Ring.choose (nu a + -(mu a)) 0 - Ring.choose (nu a + -(mu a)) d = 0`.

Rewrite using `[Ring.choose_zero_right, show nu a + -(mu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]`. Both sides reduce to the same expression. Introduce `ρ x hx`. Rewrite using `[LinearMap.sub_apply, shwt a _ _ ρ x hx, shwt a _ _ ρ x hx, ← sub_smul]`. Use `push_cast`.

Both sides reduce to the same expression. Introduce `x hx`. Rewrite using `[LinearMap.sub_apply]`. Conclude with `M.sub_mem (shM a _ _ x hx) (shM a _ _ x hx)`. Establish `hproj : ∀ F : Finset (Fin n → ℤ), ∃ (P : Module.End (KK O) W) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧ (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧ (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧ ∀ x ∈ M, P x ∈ M`.

Introduce `F`. Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty`. Conclude with `⟨1, fun _ => 1, rfl, by simp, fun nu x _ => by simp, fun x hx => by simpa using hx⟩`. Consider the case `insert nu F hnu ih`.

Take `⟨P, g, hg1, hg0, hgw, hgM⟩` from `ih`. Take `⟨T, h, hh1, hh0, hhw, hhM⟩` from `hT nu`. Use `⟨T * P, fun ρ => h ρ * g ρ, by simp [hh1, hg1], ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ν hν hne`. Break down `Finset.mem_insert.1 hν with rfl | hν'` into its components or cases.

Simplify using `[hh0 hne]`. Simplify using `[hg0 ν hν' hne]`. Introduce `ρ x hx`. Rewrite using `[Module.End.mul_apply, hgw ρ x hx, map_smul, hhw ρ x hx, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Conclude with `hhM _ (hgM x hx)`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) W) ≤ ⨆ nu ∈ F, weightSp E nu := by`.

Set `bs` to `Module.finBasis (KK O) W`. Establish `hb : ∀ i, ∃ s : Finset (Fin n → ℤ), bs i ∈ ⨆ nu ∈ s, weightSp E nu`. Introduce `i`. Apply `Submodule.mem_iSup_iff_exists_finset.1` to reduce the goal to its premises. Rewrite using `[hE.2.2]`.

Conclude with `Submodule.mem_top`. Use `choose s hs using hb`. Use `⟨Finset.univ.biUnion s, ?_⟩` and prove the remaining obligations. Rewrite using `[← bs.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Establish `hmono : (⨆ nu ∈ s i, weightSp E nu) ≤ ⨆ nu ∈ Finset.univ.biUnion s, weightSp E nu` using `biSup_mono fun nu hnu => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hnu⟩`. Conclude with `hmono (hs i)`. Take `⟨P, g, hg1, hg0, hgw, hgM⟩` from `hproj F`. Establish `hπP : π = P`. Establish `hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (π - P)`.

Use `iSup₂_le fun nu hnu => ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hgw nu x hx]`. Distinguish the cases in `h : nu = mu`. Substitute `h` using the available equality.

Rewrite using `[hπ.1 x hx, hg1]`. Simplify using the standard rewrite rules. Rewrite using `[hπ.2 nu h x hx, hg0 nu hnu h]`. Simplify using the standard rewrite rules. Use extensionality with `x`.

Establish `hx` using `hle (hF (Submodule.mem_top (x := x)))`. Rewrite `hx` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `hx`. Introduce `x hx`. Rewrite using `[hπP]`.

Conclude with `hgM x hx`.
-/
theorem weightProjection_preserves_lattice [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M) (mu : Fin n → ℤ) (π : Module.End (KK O) W)
    (hπ : IsWtProj E mu π) : ∀ x ∈ M, π x ∈ M := by
  classical
  obtain ⟨sh, shwt, shM⟩ : ∃ sh : Fin n → ℤ → ℕ → Module.End (KK O) W,
      (∀ a c d ρ x, x ∈ weightSp E ρ → sh a c d x = ((Ring.choose (ρ a + c) d : ℤ) : KK O) • x) ∧
      (∀ a c d x, x ∈ M → sh a c d x ∈ M) := by
    refine ⟨fun a c d => ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : KK O) • binomE E a ij.1,
      ?_, ?_⟩
    · intro a c d ρ x hx
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, binomial_diagonal_apply_weight E a ρ x hx, smul_smul]
      rw [← Finset.sum_smul, Ring.add_choose_eq d (Commute.all _ _)]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun ij _ => by ring
    · intro a c d x hx
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun ij _ => ?_
      rw [LinearMap.smul_apply]
      exact int_smul_mem_lattice M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)
  have hT : ∀ nu : Fin n → ℤ, ∃ (T : Module.End (KK O) W) (h : (Fin n → ℤ) → ℤ), h mu = 1 ∧
      (nu ≠ mu → h nu = 0) ∧ (∀ ρ, ∀ x ∈ weightSp E ρ, T x = ((h ρ : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, T x ∈ M := by
    intro nu
    by_cases hne : nu = mu
    · refine ⟨1, fun _ => 1, rfl, fun h => absurd hne h, fun ρ x _ => by simp, fun x hx => by simpa using hx⟩
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, mu a - nu a = (d : ℤ) := ⟨(mu a - nu a).toNat, by omega⟩
        have hd0 : 0 < d := by omega
        refine ⟨sh a (-(nu a)) d, fun ρ => Ring.choose (ρ a + -(nu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(nu a)) d = 1
          rw [show mu a + -(nu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]
          rfl
        · intro _
          show Ring.choose (nu a + -(nu a)) d = 0
          rw [show nu a + -(nu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro ρ x hx
          exact shwt a _ _ ρ x hx
        · intro x hx
          exact shM a _ _ x hx
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, nu a - mu a = (d : ℤ) := ⟨(nu a - mu a).toNat, by omega⟩
        refine ⟨sh a (-(mu a)) 0 - sh a (-(mu a)) d,
          fun ρ => Ring.choose (ρ a + -(mu a)) 0 - Ring.choose (ρ a + -(mu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(mu a)) 0 - Ring.choose (mu a + -(mu a)) d = 1
          have hd0 : 0 < d := by omega
          rw [Ring.choose_zero_right, show mu a + -(mu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro _
          show Ring.choose (nu a + -(mu a)) 0 - Ring.choose (nu a + -(mu a)) d = 0
          rw [Ring.choose_zero_right, show nu a + -(mu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_self]
          rfl
        · intro ρ x hx
          rw [LinearMap.sub_apply, shwt a _ _ ρ x hx, shwt a _ _ ρ x hx, ← sub_smul]
          push_cast
          rfl
        · intro x hx
          rw [LinearMap.sub_apply]
          exact M.sub_mem (shM a _ _ x hx) (shM a _ _ x hx)
  have hproj : ∀ F : Finset (Fin n → ℤ), ∃ (P : Module.End (KK O) W) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧
      (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧ (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, P x ∈ M := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨1, fun _ => 1, rfl, by simp, fun nu x _ => by simp, fun x hx => by simpa using hx⟩
    | insert nu F hnu ih =>
      obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := ih
      obtain ⟨T, h, hh1, hh0, hhw, hhM⟩ := hT nu
      refine ⟨T * P, fun ρ => h ρ * g ρ, by simp [hh1, hg1], ?_, ?_, ?_⟩
      · intro ν hν hne
        rcases Finset.mem_insert.1 hν with rfl | hν'
        · simp [hh0 hne]
        · simp [hg0 ν hν' hne]
      · intro ρ x hx
        rw [Module.End.mul_apply, hgw ρ x hx, map_smul, hhw ρ x hx, smul_smul]
        congr 1
        push_cast
        ring
      · intro x hx
        exact hhM _ (hgM x hx)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) W) ≤ ⨆ nu ∈ F, weightSp E nu := by
    let bs := Module.finBasis (KK O) W
    have hb : ∀ i, ∃ s : Finset (Fin n → ℤ), bs i ∈ ⨆ nu ∈ s, weightSp E nu := by
      intro i
      apply Submodule.mem_iSup_iff_exists_finset.1
      rw [hE.2.2]
      exact Submodule.mem_top
    choose s hs using hb
    refine ⟨Finset.univ.biUnion s, ?_⟩
    rw [← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmono : (⨆ nu ∈ s i, weightSp E nu) ≤ ⨆ nu ∈ Finset.univ.biUnion s, weightSp E nu :=
      biSup_mono fun nu hnu => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hnu⟩
    exact hmono (hs i)
  obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := hproj F
  have hπP : π = P := by
    have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (π - P) := by
      refine iSup₂_le fun nu hnu => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hgw nu x hx]
      by_cases h : nu = mu
      · subst h
        rw [hπ.1 x hx, hg1]
        simp
      · rw [hπ.2 nu h x hx, hg0 nu hnu h]
        simp
    ext x
    have hx := hle (hF (Submodule.mem_top (x := x)))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
  intro x hx
  rw [hπP]
  exact hgM x hx

/- English proof (translation)
Establish `hf' : ∀ y : L, (y : W) ∈ M → f y ∈ M` using `hf`. Use `show ∀ x : L, (x : W) ∈ M → divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x ∈ M`. Introduce `x hx`. Establish `hexp : divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x = ∑ m ∈ range (k + 1), (((-1 : ℤ) ^ (k - m) : ℤ) : KK O) • divPowE E a b m (f ((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x))`. Rewrite using `[divPowE, LinearMap.smul_apply, LinearMap.smul_apply, homRepresentation_pow_apply, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hmk : m ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)`. Simplify using `only [divPowE, LinearMap.smul_apply, map_smul, smul_smul]`. Use `congr 1`. Establish `hc : ((k.choose m : ℕ) : KK O) * (m.factorial : KK O) * ((k - m).factorial : KK O) = (k.factorial : KK O)`.

Conclude with `Nat.choose_mul_factorial_mul_factorial hmk` after adjusting the coercions. Establish `h1 : (m.factorial : KK O) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)`. Establish `h2 : ((k - m).factorial : KK O) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - m))`. Rewrite using `[← hc]`. Establish `h3 : ((k.choose m : ℕ) : KK O) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.choose_pos hmk).ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hexp]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Apply `int_smul_mem_lattice` to reduce the goal to its premises.

Establish `hy : (((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x : L) : W) = divPowE E a b (k - m) (x : W)`. Rewrite using `[Submodule.coe_smul, restrictRepresentation_pow_coe, divPowE, LinearMap.smul_apply]`. Establish `hyM : divPowE E a b (k - m) (x : W) ∈ M` using `hM _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) _ hx`. Establish `hfy` using `hf' _ (by rw [hy]; exact hyM)`. Conclude with `hM _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ hfy`.
-/
theorem homLattice_dividedPower_stable [CharZero (KK O)] (E : GLOps n (KK O) W) (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (hab : a ≠ b) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f ∈ homLattice M L := by
  have hf' : ∀ y : L, (y : W) ∈ M → f y ∈ M := hf
  show ∀ x : L, (x : W) ∈ M → divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x ∈ M
  intro x hx
  have hexp : divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x =
      ∑ m ∈ range (k + 1), (((-1 : ℤ) ^ (k - m) : ℤ) : KK O) •
        divPowE E a b m (f ((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x)) := by
    rw [divPowE, LinearMap.smul_apply, LinearMap.smul_apply, homRepresentation_pow_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    simp only [divPowE, LinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    have hc : ((k.choose m : ℕ) : KK O) * (m.factorial : KK O) * ((k - m).factorial : KK O) =
        (k.factorial : KK O) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmk
    have h1 : (m.factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have h2 : ((k - m).factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - m))
    rw [← hc]
    have h3 : ((k.choose m : ℕ) : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hmk).ne'
    push_cast
    field_simp
  rw [hexp]
  refine Submodule.sum_mem _ fun m _ => ?_
  apply int_smul_mem_lattice
  have hy : (((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x : L) : W) =
      divPowE E a b (k - m) (x : W) := by
    rw [Submodule.coe_smul, restrictRepresentation_pow_coe, divPowE, LinearMap.smul_apply]
  have hyM : divPowE E a b (k - m) (x : W) ∈ M := hM _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) _ hx
  have hfy := hf' _ (by rw [hy]; exact hyM)
  exact hM _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ hfy

end lat

end Formalism.MainNotions.G.GLWeightTheory
