import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountExtP
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Rewrite using `[← Ideal.mem_comap, MeanB.comap_extP_pow]`. Conclude with `hs`.
-/
theorem map_mem_extP {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs

/- English proof (translation)
Take `⟨u, hu⟩` from `MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k`. Establish `e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) - algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z`. Rewrite using `[map_sub, map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))`.
-/
theorem mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
    rw [map_sub, map_mul, map_one]
    ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))

/- English proof (translation)
Take `⟨z', hz', e⟩` from `MeanB.star_mem_extP hF 𝔭 k hz`. Establish `: conjO K z = z'` using `RingOfIntegers.ext e.symm`. Rewrite using `[this]`. Conclude with `hz'`.
-/
theorem conjO_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K}
    (hz : z ∈ extP K 𝔭 ^ k) : conjO K z ∈ extP K 𝔭 ^ k := by
  obtain ⟨z', hz', e⟩ := MeanB.star_mem_extP hF 𝔭 k hz
  have : conjO K z = z' := RingOfIntegers.ext e.symm
  rw [this]
  exact hz'

/- English proof (translation)
The claim follows from `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)`.
-/
theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

/- English proof (translation)
Establish `hne` using `ne_bot_of_isMaximal h𝔭`. Establish `hpr : Prime 𝔭` using `Ideal.prime_of_isPrime hne h𝔭.isPrime`. Distinguish the cases in `hkv : k ≤ v`. Rewrite using `[Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.

Choose the witnesses or unpack the hypotheses as in `⟨J, hJ⟩ : 𝔭 ^ v ∣ Ideal.span {n} := by`. Rewrite using `[Ideal.dvd_span_singleton]`. Conclude with `hn`. Establish `hJ' : ¬ 𝔭 ∣ J`. Introduce and unpack `⟨C, rfl⟩`.

Apply `hn'` to reduce the goal to its premises. Rewrite using `[← Ideal.dvd_span_singleton, hJ, pow_succ, ← mul_assoc]`. Conclude with `Dvd.intro _ rfl`. Establish `h2 : 𝔭 ^ k ∣ Ideal.span {s} * Ideal.span {n}`. Rewrite using `[Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]`.

Conclude with `h`. Establish `ek : k = v + (k - v)` using `by omega`. Rewrite `h2` using `[hJ, ek, pow_add, mul_left_comm]`. Establish `h3` using `(mul_dvd_mul_iff_left (pow_ne_zero v hne)).1 h2`. Rewrite using `[← Ideal.dvd_span_singleton]`.

Conclude with `hpr.pow_dvd_of_dvd_mul_right _ hJ' h3`.
-/
theorem mem_pow_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s n : 𝓞 F} {k v : ℕ}
    (hn : n ∈ 𝔭 ^ v) (hn' : n ∉ 𝔭 ^ (v + 1)) (h : s * n ∈ 𝔭 ^ k) : s ∈ 𝔭 ^ (k - v) := by
  have hne := ne_bot_of_isMaximal h𝔭
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  by_cases hkv : k ≤ v
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨J, hJ⟩ : 𝔭 ^ v ∣ Ideal.span {n} := by
    rw [Ideal.dvd_span_singleton]
    exact hn
  have hJ' : ¬ 𝔭 ∣ J := by
    rintro ⟨C, rfl⟩
    apply hn'
    rw [← Ideal.dvd_span_singleton, hJ, pow_succ, ← mul_assoc]
    exact Dvd.intro _ rfl
  have h2 : 𝔭 ^ k ∣ Ideal.span {s} * Ideal.span {n} := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]
    exact h
  have ek : k = v + (k - v) := by omega
  rw [hJ, ek, pow_add, mul_left_comm] at h2
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero v hne)).1 h2
  rw [← Ideal.dvd_span_singleton]
  exact hpr.pow_dvd_of_dvd_mul_right _ hJ' h3

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e

/- English proof (translation)
Take `⟨b, hb, hloc⟩` from `LocalSpans.exists_basis_locF hL h𝔭`. Establish `hsub : Subsingleton (Fin (finrank K V))`. Rewrite using `[h1]`. Use `infer_instance`. Set `i0 : Fin (finrank K V)` to `⟨0, by omega⟩`.

Use `⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))`. Rewrite using `[hloc]`. Conclude with `LocF.le_locF 𝔭 L hx`. Take `⟨t, ht, hm⟩` from `(LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'`.

Establish `hr : Set.range b = {b i0}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Rewrite using `[Subsingleton.elim i i0]`.

Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨i0, rfl⟩`. Rewrite `hm` using `[hr, Submodule.mem_span_singleton]`. Take `⟨a, ha⟩` from `hm`.

Conclude with `⟨t, ht, a, ha.symm⟩`.
-/
theorem exists_isGen {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ e, IsGen L 𝔭 e := by
  obtain ⟨b, hb, hloc⟩ := LocalSpans.exists_basis_locF hL h𝔭
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  refine ⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hloc]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, hm⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'
  have hr : Set.range b = {b i0} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i0]
      rfl
    · rintro rfl
      exact ⟨i0, rfl⟩
  rw [hr, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨t, ht, a, ha.symm⟩

/- English proof (translation)
Establish `hsub : Subsingleton (Fin (finrank K V))`. Rewrite using `[h1]`. Use `infer_instance`. Set `i0 : Fin (finrank K V)` to `⟨0, by omega⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hle`. Rewrite using `[← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]`. Apply `hle` to reduce the goal to its premises. Use `Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]`.

Both sides reduce to the same expression. Introduce `hnj`. Unfold `discrIdeal`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨x, hx, hz⟩`.

Rewrite `hz` using `[Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply]`. Take `⟨t, ht, a, ha⟩` from `he.2.2 (x i0) (hx i0)`. Apply `mem_extP_of_mul h𝔭 ht` to reduce the goal to its premises. Apply `mem_extP_of_mul h𝔭 ht` to reduce the goal to its premises. Establish `: algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) = conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n`.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) = h (a • e) (a • e)` using `by rw [ha]`. Rewrite `e1` using `[Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz, MeanB.algebraMap_comp, MeanB.star_algebraMap hF …`. Simplify using `only [map_mul]`. Rewrite using `[MeanB.algebraMap_comp, MeanB.algebraMap_comp]`.

Express the relevant statement in the definitionally equal form `_ = star (algebraMap (𝓞 K) K a) * _ * _`. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (map_mem_extP hnj)`.
-/
theorem discrIdeal_le_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V} (he : IsGen L 𝔭 e)
    {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) (j : ℕ) :
    discrIdeal h L ≤ extP K 𝔭 ^ j ↔ n ∈ 𝔭 ^ j := by
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  constructor
  · intro hle
    rw [← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]
    apply hle
    refine Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]
    rfl
  · intro hnj
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply] at hz
    obtain ⟨t, ht, a, ha⟩ := he.2.2 (x i0) (hx i0)
    apply mem_extP_of_mul h𝔭 ht
    apply mem_extP_of_mul h𝔭 ht
    have : algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) =
        conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n := by
      apply RingOfIntegers.coe_injective
      have e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) =
          h (a • e) (a • e) := by rw [ha]
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right,
        Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz,
        MeanB.algebraMap_comp, MeanB.star_algebraMap hF] at e1
      simp only [map_mul]
      rw [MeanB.algebraMap_comp, MeanB.algebraMap_comp]
      change _ = star (algebraMap (𝓞 K) K a) * _ * _
      rw [e1]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (map_mem_extP hnj)

/- English proof (translation)
Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Apply `he.2.1` to reduce the goal to its premises. Apply `LocF.aniso_of_totPosDef hd` to reduce the goal to its premises. Rewrite using `[hn]`.

Simplify using the standard rewrite rules. Establish `hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j}`. Use extensionality with `j`. Conclude with `discrIdeal_le_iff hF h1 h𝔭 he hn j`. Establish `hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥` using `Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top`.

Choose the witnesses or unpack the hypotheses as in `⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Apply `hn0` to reduce the goal to its premises. Establish `: n ∈ (⨅ j : ℕ, 𝔭 ^ j)` using `(Submodule.mem_iInf _).2 hcon`.

Rewrite `this` using `[hinf]`. Then use the resulting hypothesis. Establish `hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j}`. Use `⟨j0, fun j hj => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Conclude with `hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)`.

Establish `hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty` using `⟨0, by simp⟩`. Unfold `vd`. Rewrite using `[hset]`. Use `⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩` and prove the remaining obligations. Use `le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem vd_spec (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V}
    (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) :
    n ∈ 𝔭 ^ vd h L 𝔭 ∧ n ∉ 𝔭 ^ (vd h L 𝔭 + 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply he.2.1
    apply LocF.aniso_of_totPosDef hd
    rw [hn]
    simp
  have hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j} := by
    ext j
    exact discrIdeal_le_iff hF h1 h𝔭 he hn j
  have hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top
  obtain ⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hn0
    have : n ∈ (⨅ j : ℕ, 𝔭 ^ j) := (Submodule.mem_iInf _).2 hcon
    rwa [hinf] at this
  have hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j} := by
    refine ⟨j0, fun j hj => ?_⟩
    by_contra hlt
    exact hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)
  have hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty := ⟨0, by simp⟩
  unfold vd
  rw [hset]
  refine ⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩
  have := le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)
  omega

end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
