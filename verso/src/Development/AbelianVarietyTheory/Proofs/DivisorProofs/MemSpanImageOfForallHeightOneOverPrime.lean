import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory.Desc

namespace GlobalTheory.Desc.LocalDescent

/- English proof (translation)
Introduce `R F _ _ _ _ _ c₀ hc p hp hp1 T hT`. Set `B` to `Localization.AtPrime p`. Use `haveI := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 B`. Establish `hu : ∀ y : p.primeCompl, IsUnit (c₀ y)` using `fun y => IsUnit.mk0 _ fun h => y.2 (((injective_iff_map_eq_zero c₀).mp hc _ h) ▸ p.zero_mem)`. Set `l : B →+* F` to `IsLocalization.lift hu`.

Establish `hl : ∀ r, l (algebraMap R B r) = c₀ r` using `fun r => IsLocalization.lift_eq hu r`. Establish `hinj` using `IsLocalization.injective B p.primeCompl_le_nonZeroDivisors`. Establish `hli : Function.Injective l`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Take `⟨⟨r, s⟩, e⟩` from `IsLocalization.surj p.primeCompl z`. Establish `h0 : c₀ r = 0` using `by rw [← hl, ← e, map_mul, hz, zero_mul]`. Rewrite `e` using `[(injective_iff_map_eq_zero c₀).mp hc _ h0, map_zero]`. Conclude with `(IsLocalization.map_units B s).mul_left_eq_zero.mp e`. Use `letI : Algebra B F := l.toAlgebra`.

Establish `hsm : ∀ (z : B) (v : F), z • v = l z * v` using `fun _ _ => rfl`. Use `haveI : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hli`. Set `E` to `Submodule.span B T`. Use `haveI : Module.Finite B E := Module.Finite.span_of_finite B hT`. Use `haveI : Module.Free B E := inferInstance`.

Set `e` to `Module.finBasis B E`. Establish `clear : ∀ {ι : Type} [Finite ι] (z : ι → B), ∃ t, t ∉ p ∧ ∃ g : ι → R, ∀ i, c₀ (g i) = c₀ t * l (z i)` using `fun z => by`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite p.primeCompl z`. Use `choose h hh using hd`. Conclude with `⟨d, d.2, h, fun i => by rw [← hl, hh, Algebra.smul_def, map_mul, hl]⟩`.

Use `⟨_, fun j => (e j : F), fun j => ?_, fun r hr => ?_, ?_⟩` and prove the remaining obligations. Take `⟨n, z, v, hv⟩` from `Submodule.mem_span_set'.mp (e j).2`. Take `⟨t, ht, g, hg⟩` from `clear z`. Use `⟨n, g, fun i => v i, t, ht, fun i => (v i).2, ?_⟩` and prove the remaining obligations. Simplify using `only [← hv, hg, hsm, Finset.mul_sum, mul_assoc]`.

Use `Fintype.linearIndependent_iff.mp e.linearIndependent (fun j => algebraMap R B (r j)) (Subtype.ext (by simpa [hsm, hl] using hr))` as an intermediate fact. Use function extensionality and compare the values at `j`. Conclude with `(injective_iff_map_eq_zero _).mp hinj _ (this j)`. Use `haveI : Finite T := hT`. Take `⟨t, ht, g, hg⟩` from `clear fun z : T × Fin (Module.finrank B E) => e.repr ⟨z.1, Submodule.subset_span z.1.2⟩ z.2`.

Use `⟨t, ht, fun v hv => ⟨fun j => g (⟨v, hv⟩, j), ?_⟩⟩` and prove the remaining obligations. Use `congrArg Subtype.val (e.sum_repr ⟨v, Submodule.subset_span hv⟩)` as an intermediate fact. Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hsm] at this`. Simplify using `only [hg, mul_assoc, ← Finset.mul_sum, this]`.
-/
theorem exists_basis_of_finite : ∀ (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] (c₀ : R →+* F), Function.Injective c₀ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → ∀ (T : Set F), T.Finite → ∃ (k : ℕ) (b : Fin k → F), (∀ j, ∃ (n : ℕ) (g : Fin n → R) (v : Fin n → F) (t : R), t ∉ p ∧ (∀ i, v i ∈ T) ∧ c₀ t * b j = ∑ i, c₀ (g i) * v i) ∧ (∀ r : Fin k → R, ∑ j, c₀ (r j) * b j = 0 → r = 0) ∧ ∃ t : R, t ∉ p ∧ ∀ v ∈ T, ∃ g : Fin k → R, c₀ t * v = ∑ j, c₀ (g j) * b j := by
  intro R F _ _ _ _ _ c₀ hc p hp hp1 T hT
  classical
  let B := Localization.AtPrime p
  haveI := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 B
  have hu : ∀ y : p.primeCompl, IsUnit (c₀ y) := fun y => IsUnit.mk0 _ fun h =>
    y.2 (((injective_iff_map_eq_zero c₀).mp hc _ h) ▸ p.zero_mem)
  let l : B →+* F := IsLocalization.lift hu
  have hl : ∀ r, l (algebraMap R B r) = c₀ r := fun r => IsLocalization.lift_eq hu r
  have hinj := IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have hli : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj p.primeCompl z
    have h0 : c₀ r = 0 := by rw [← hl, ← e, map_mul, hz, zero_mul]
    rw [(injective_iff_map_eq_zero c₀).mp hc _ h0, map_zero] at e
    exact (IsLocalization.map_units B s).mul_left_eq_zero.mp e
  letI : Algebra B F := l.toAlgebra
  have hsm : ∀ (z : B) (v : F), z • v = l z * v := fun _ _ => rfl
  haveI : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hli
  let E := Submodule.span B T
  haveI : Module.Finite B E := Module.Finite.span_of_finite B hT
  haveI : Module.Free B E := inferInstance
  let e := Module.finBasis B E
  have clear : ∀ {ι : Type} [Finite ι] (z : ι → B), ∃ t, t ∉ p ∧ ∃ g : ι → R,
      ∀ i, c₀ (g i) = c₀ t * l (z i) := fun z => by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl z
    choose h hh using hd
    exact ⟨d, d.2, h, fun i => by rw [← hl, hh, Algebra.smul_def, map_mul, hl]⟩
  refine ⟨_, fun j => (e j : F), fun j => ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.mp (e j).2
    obtain ⟨t, ht, g, hg⟩ := clear z
    refine ⟨n, g, fun i => v i, t, ht, fun i => (v i).2, ?_⟩
    simp only [← hv, hg, hsm, Finset.mul_sum, mul_assoc]
  · have := Fintype.linearIndependent_iff.mp e.linearIndependent (fun j => algebraMap R B (r j))
      (Subtype.ext (by simpa [hsm, hl] using hr))
    funext j
    exact (injective_iff_map_eq_zero _).mp hinj _ (this j)
  · haveI : Finite T := hT
    obtain ⟨t, ht, g, hg⟩ := clear
      fun z : T × Fin (Module.finrank B E) => e.repr ⟨z.1, Submodule.subset_span z.1.2⟩ z.2
    refine ⟨t, ht, fun v hv => ⟨fun j => g (⟨v, hv⟩, j), ?_⟩⟩
    have := congrArg Subtype.val (e.sum_repr ⟨v, Submodule.subset_span hv⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hsm] at this
    simp only [hg, mul_assoc, ← Finset.mul_sum, this]

/- English proof (translation)
Introduce `R₁ F₁ _ _ _ _ _ c₁ hc S hS k b hind x a ha ⟨t, g, ht, e⟩ hloc`. Establish `hle : S ≤ nonZeroDivisors R₁` using `fun y hy => mem_nonZeroDivisors_of_ne_zero fun h => hS (h ▸ hy)`. Set `A` to `Localization S`. Use `haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hle`. Use `haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance`.

Use `haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A S hle`. Establish `hinj` using `IsLocalization.injective A hle`. Establish `hdvd : ∀ j, algebraMap R₁ A a ∣ algebraMap R₁ A (g j)` using `fun j => by`. Use `GlobalTheory.dvd_of_forall_height_eq_one ((map_ne_zero_iff _ hinj).mpr ha) fun Q hQ h1 haQ => ?_` and prove the remaining obligations. Take `⟨hq, hd⟩` from `(IsLocalization.isPrime_iff_isPrime_disjoint S A Q).mp hQ`.

Take `⟨s, hs, t', g', ht', e'⟩` from `hloc (Q.comap (algebraMap R₁ A)) hq (by rw [IsLocalization.height_comap S Q, h1]) haQ hd`. Establish `h0` using `hind (fun j => t' * s * g j - t * a * g' j) (by`. Simplify using `only [map_sub, map_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, ← e, ← e']`. Use the proof step `ring)`. Establish `h1 : t' * s * g j = t * a * g' j` using `sub_eq_zero.mp (congrFun h0 j)`.

Use `⟨algebraMap R₁ A s, hs, (IsLocalization.map_units A ⟨t', ht'⟩).dvd_mul_left.mp ?_⟩` and prove the remaining obligations. Use `⟨algebraMap R₁ A (t * g' j), ?_⟩` and prove the remaining obligations. Simplify using `only [← map_mul]`. Use `congr 1`. Take the linear combination `h1`.

Use `choose y hy using hdvd`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite S y`. Use `choose h hh using hd`. Use `⟨d * t, h, S.mul_mem d.2 ht, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ j, (d : R₁) * g j = a * h j` using `fun j => hinj (by`.

Rewrite using `[map_mul, map_mul, hh, hy, Algebra.smul_def]`. Use the proof step `ring)`. Apply `mul_left_cancel₀ ((map_ne_zero_iff c₁ hc).mpr ha)` to reduce the goal to its premises. Establish `: c₁ a * (c₁ (d * t) * x) = c₁ d * (c₁ (t * a) * x)` using `by simp only [map_mul]; ring`. Rewrite using `[this, e, Finset.mul_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h1]`.
-/
theorem span_test : ∀ (R₁ F₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F₁] (c₁ : R₁ →+* F₁), Function.Injective c₁ → ∀ (S : Submonoid R₁), (0 : R₁) ∉ S → ∀ (k : ℕ) (b : Fin k → F₁), (∀ r : Fin k → R₁, ∑ j, c₁ (r j) * b j = 0 → r = 0) → ∀ (x : F₁) (a : R₁), a ≠ 0 → (∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * a) * x = ∑ j, c₁ (g j) * b j) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → a ∈ q → Disjoint (S : Set R₁) (q : Set R₁) → ∃ s, s ∉ q ∧ ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * s) * x = ∑ j, c₁ (g j) * b j) → ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ t * x = ∑ j, c₁ (g j) * b j := by
  intro R₁ F₁ _ _ _ _ _ c₁ hc S hS k b hind x a ha ⟨t, g, ht, e⟩ hloc
  classical
  have hle : S ≤ nonZeroDivisors R₁ := fun y hy =>
    mem_nonZeroDivisors_of_ne_zero fun h => hS (h ▸ hy)
  let A := Localization S
  haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hle
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A S hle
  have hinj := IsLocalization.injective A hle
  have hdvd : ∀ j, algebraMap R₁ A a ∣ algebraMap R₁ A (g j) := fun j => by
    refine GlobalTheory.dvd_of_forall_height_eq_one ((map_ne_zero_iff _ hinj).mpr ha) fun Q hQ h1 haQ => ?_
    obtain ⟨hq, hd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S A Q).mp hQ
    obtain ⟨s, hs, t', g', ht', e'⟩ := hloc (Q.comap (algebraMap R₁ A)) hq
      (by rw [IsLocalization.height_comap S Q, h1]) haQ hd
    have h0 := hind (fun j => t' * s * g j - t * a * g' j) (by
      simp only [map_sub, map_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, ← e, ← e']
      ring)
    have h1 : t' * s * g j = t * a * g' j := sub_eq_zero.mp (congrFun h0 j)
    refine ⟨algebraMap R₁ A s, hs, (IsLocalization.map_units A ⟨t', ht'⟩).dvd_mul_left.mp ?_⟩
    refine ⟨algebraMap R₁ A (t * g' j), ?_⟩
    simp only [← map_mul]
    congr 1
    linear_combination h1
  choose y hy using hdvd
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S y
  choose h hh using hd
  refine ⟨d * t, h, S.mul_mem d.2 ht, ?_⟩
  have h1 : ∀ j, (d : R₁) * g j = a * h j := fun j => hinj (by
    rw [map_mul, map_mul, hh, hy, Algebra.smul_def]; ring)
  apply mul_left_cancel₀ ((map_ne_zero_iff c₁ hc).mpr ha)
  have : c₁ a * (c₁ (d * t) * x) = c₁ d * (c₁ (t * a) * x) := by simp only [map_mul]; ring
  rw [this, e, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h1]

/- English proof (translation)
Introduce `R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf _ hρ hc₀ hcomp hlin p hp hp1 _ W hWt hWadd hWsmul hWdiv x hx hloc`. Establish `hθ : ∀ r, θ (c₀ r) = c₁ (ρ r)` using `fun r => RingHom.congr_fun hcomp r`. Establish `hc₁ : Function.Injective c₁`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`.

Use `hlin 1 (fun _ => 1) (fun g hg => by` as an intermediate fact. Use function extensionality and compare the values at `i`. Establish `h0 : c₀ (g 0) = 0` using `by simpa using hg`. Rewrite using `[Subsingleton.elim i 0]`. Conclude with `(injective_iff_map_eq_zero c₀).mp hc₀ _ h0) (fun _ => r) (by simpa using hr)`.

Conclude with `congrFun this 0`. Establish `hW0 : (0 : F) ∈ W` using `by simpa using hWt 0`. Establish `hWsum : ∀ (n : ℕ) (g : Fin n → R) (v : Fin n → F), (∀ i, v i ∈ W) → ∑ i, c₀ (g i) * v i ∈ W` using `fun n g v hv => Finset.sum_induction _ (· ∈ W) (fun a b ha hb => hWadd a ha b hb) hW0 fun i _ => hWsmul _ _ (hv i)`. Establish `hne : ∀ t, t ∉ p → c₀ t ≠ 0` using `fun t ht h => ht (((injective_iff_map_eq_zero c₀).mp hc₀ _ h) ▸ p.zero_mem)`. Establish `hρf : ρ f ≠ 0` using `fun h => hf ((injective_iff_map_eq_zero ρ).mp hρ _ h)`.

Take `⟨n, r, u', hu', rfl⟩` from `hx`. Use `choose u hu using hu'`. Take `rfl : u' = fun i => θ (u i)` from `funext fun i => (hu i).symm`. Use `set x := ∑ i, c₁ (r i) * θ (u i) with hxdef`. Use `choose m hm using hWt`.

Set `M` to `Finset.univ.sup fun i => m (u i)`. Establish `hM : ∀ i, c₀ f ^ M * u i ∈ W` using `fun i => by`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := fun i => m (u i)) (Finset.mem_univ i) : m (u i) ≤ M)`. Use `hWsmul (f ^ d) _ (hm (u i))` as an intermediate fact. Rewrite `this` using `[map_pow, ← mul_assoc, ← pow_add, add_comm, ← hd]`. Then use the resulting hypothesis.

Set `S : Submonoid R₁` to `p.primeCompl.map ρ`. Set `G : Set (PrimeSpectrum R₁)` to `{q | q.asIdeal.height = 1 ∧ ρ f ∈ q.asIdeal ∧ Disjoint (S : Set R₁) (q.asIdeal : Set R₁)}`. Establish `hG : G.Finite` using `(GlobalTheory.finite_height_eq_one_mem hρf).subset fun q hq => ⟨hq.1, hq.2.1⟩`. Establish `H : ∀ q : G, ∃ (s : R₁) (N : ℕ) (g : Fin N → R₁) (w : Fin N → F), s ∉ q.1.asIdeal ∧ (∀ l, w l ∈ W) ∧ c₁ s * x = ∑ l, c₁ (g l) * θ (w l)`. Introduce and unpack `⟨q, h1, h2, h3⟩`.

Establish `hle : q.asIdeal.comap ρ ≤ p` using `fun t ht => by_contra fun htp => Set.disjoint_left.mp h3 ⟨t, htp, rfl⟩ ht`. Establish `heq : q.asIdeal.comap ρ = p` using `le_antisymm hle ((GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one hp1 hf (hle h2)).2 ⟨Ideal.comap_isPrime ρ _, (Ideal.span_singleton_le_iff_mem _).mpr h2⟩ hle)`. Take `⟨s, hs, N, g, w', hw', e⟩` from `hloc q.asIdeal q.isPrime h1 h2 heq`. Use `choose w hw hw' using hw'`. Conclude with `⟨s, N, g, w, hs, hw, by simp only [hw', e]⟩`.

Use `choose s N g w hs hw he using H`. Use `haveI : Finite G := hG`. Set `T : Set F` to `Set.range (fun i => c₀ f ^ M * u i) ∪ ⋃ q : G, Set.range (w q)`. Establish `hT : T.Finite` using `(Set.finite_range _).union (Set.finite_iUnion fun q => Set.finite_range _)`. Establish `hTW : T ⊆ W`.

Introduce and unpack `_ (⟨i, rfl⟩ | ⟨_, ⟨q, rfl⟩, l, rfl⟩)`. Conclude with `hM i`. Conclude with `hw q l`. Take `⟨k, b, hb, hind, t, ht, hexp⟩` from `exists_basis_of_finite R F c₀ hc₀ p hp hp1 T hT`. Establish `hbW : ∀ j, b j ∈ W` using `fun j => by`.

Take `⟨n', g', v, t', ht', hv, e⟩` from `hb j`. Use `hWdiv t' ht' _ (hWsum n' g' v fun i => hTW (hv i))` as an intermediate fact. Rewrite `this` using `[← e, inv_mul_cancel_left₀ (hne t' ht')]`. Then use the resulting hypothesis. Establish `key : ∀ (n' : ℕ) (g' : Fin n' → R₁) (v : Fin n' → F), (∀ i, v i ∈ T) → ∃ h : Fin k → R₁, c₁ (ρ t) * ∑ i, c₁ (g' i) * θ (v i) = ∑ j, c₁ (h j) * θ (b j)`. Introduce `n' g' v hv`.

Use `choose h hh using fun i => hexp (v i) (hv i)`. Use `⟨fun j => ∑ i, g' i * ρ (h i j), ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm, ← hθ, ← map_mul, hh, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hθ, mul_assoc]`. Establish `htS : ρ t ∈ S` using `⟨t, ht, rfl⟩`. Take `⟨_, h, ⟨t₀, ht₀, rfl⟩, e⟩` from `span_test R₁ F₁ c₁ hc₁ S (by`.

Introduce and unpack `⟨t₀, ht₀, e⟩`. Conclude with `ht₀ (((injective_iff_map_eq_zero ρ).mp hρ _ e) ▸ p.zero_mem))`. Use `k (fun j => θ (b j)) (hlin k b hind) x (ρ f ^ M) (pow_ne_zero _ hρf)`. Use the proof step `(by`. Take `⟨h, e⟩` from `key n r (fun i => c₀ f ^ M * u i) fun i => Or.inl ⟨i, rfl⟩`.

Use `⟨_, h, htS, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, map_mul, mul_assoc, hxdef, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, hθ, mul_left_comm])`.

Use the proof step `(by`. Introduce `q hq h1 h2 h3`. Set `q' : G` to `⟨⟨q, hq⟩, h1, hq.mem_of_pow_mem _ h2, h3⟩`. Take `⟨h, e⟩` from `key _ (g q') (w q') fun l => Or.inr (Set.mem_iUnion.mpr ⟨q', l, rfl⟩)`. Conclude with `⟨s q', hs q', _, h, htS, by rw [← e, ← he, map_mul, mul_assoc]⟩)`.

Use `⟨k, h, fun j => θ ((c₀ t₀)⁻¹ * b j), fun j => ⟨_, hWdiv t₀ ht₀ _ (hbW j), rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h0 : c₁ (ρ t₀) ≠ 0` using `by rw [← hθ]; exact (map_ne_zero θ).mpr (hne t₀ ht₀)`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[e, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[map_mul, map_inv₀, hθ, mul_left_comm, mul_inv_cancel_left₀ h0]`.
-/
theorem mem_spanBy_of_forall_height_one : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → f ∈ p → ∀ (W : Set F), (∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W) → (∀ a ∈ W, ∀ b ∈ W, a + b ∈ W) → (∀ r, ∀ a ∈ W, c₀ r * a ∈ W) → (∀ s, s ∉ p → ∀ a ∈ W, (c₀ s)⁻¹ * a ∈ W) → ∀ x ∈ spanBy c₁ (Set.range θ), (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → q.comap ρ = p → ∃ s, s ∉ q ∧ c₁ s * x ∈ spanBy c₁ (θ '' W)) → x ∈ spanBy c₁ (θ '' W) := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf _ hρ hc₀ hcomp hlin p hp hp1 _ W hWt hWadd hWsmul hWdiv x hx hloc
  classical
  have hθ : ∀ r, θ (c₀ r) = c₁ (ρ r) := fun r => RingHom.congr_fun hcomp r
  have hc₁ : Function.Injective c₁ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have := hlin 1 (fun _ => 1) (fun g hg => by
      funext i
      have h0 : c₀ (g 0) = 0 := by simpa using hg
      rw [Subsingleton.elim i 0]
      exact (injective_iff_map_eq_zero c₀).mp hc₀ _ h0) (fun _ => r) (by simpa using hr)
    exact congrFun this 0
  have hW0 : (0 : F) ∈ W := by simpa using hWt 0
  have hWsum : ∀ (n : ℕ) (g : Fin n → R) (v : Fin n → F), (∀ i, v i ∈ W) → ∑ i, c₀ (g i) * v i ∈ W :=
    fun n g v hv => Finset.sum_induction _ (· ∈ W) (fun a b ha hb => hWadd a ha b hb) hW0
      fun i _ => hWsmul _ _ (hv i)
  have hne : ∀ t, t ∉ p → c₀ t ≠ 0 := fun t ht h =>
    ht (((injective_iff_map_eq_zero c₀).mp hc₀ _ h) ▸ p.zero_mem)
  have hρf : ρ f ≠ 0 := fun h => hf ((injective_iff_map_eq_zero ρ).mp hρ _ h)
  obtain ⟨n, r, u', hu', rfl⟩ := hx
  choose u hu using hu'
  obtain rfl : u' = fun i => θ (u i) := funext fun i => (hu i).symm
  set x := ∑ i, c₁ (r i) * θ (u i) with hxdef
  choose m hm using hWt
  let M := Finset.univ.sup fun i => m (u i)
  have hM : ∀ i, c₀ f ^ M * u i ∈ W := fun i => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.le_sup (f := fun i => m (u i)) (Finset.mem_univ i) : m (u i) ≤ M)
    have := hWsmul (f ^ d) _ (hm (u i))
    rwa [map_pow, ← mul_assoc, ← pow_add, add_comm, ← hd] at this
  let S : Submonoid R₁ := p.primeCompl.map ρ
  let G : Set (PrimeSpectrum R₁) :=
    {q | q.asIdeal.height = 1 ∧ ρ f ∈ q.asIdeal ∧ Disjoint (S : Set R₁) (q.asIdeal : Set R₁)}
  have hG : G.Finite := (GlobalTheory.finite_height_eq_one_mem hρf).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have H : ∀ q : G, ∃ (s : R₁) (N : ℕ) (g : Fin N → R₁) (w : Fin N → F),
      s ∉ q.1.asIdeal ∧ (∀ l, w l ∈ W) ∧ c₁ s * x = ∑ l, c₁ (g l) * θ (w l) := by
    rintro ⟨q, h1, h2, h3⟩
    have hle : q.asIdeal.comap ρ ≤ p := fun t ht => by_contra fun htp =>
      Set.disjoint_left.mp h3 ⟨t, htp, rfl⟩ ht
    have heq : q.asIdeal.comap ρ = p :=
      le_antisymm hle ((GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one hp1 hf (hle h2)).2
        ⟨Ideal.comap_isPrime ρ _, (Ideal.span_singleton_le_iff_mem _).mpr h2⟩ hle)
    obtain ⟨s, hs, N, g, w', hw', e⟩ := hloc q.asIdeal q.isPrime h1 h2 heq
    choose w hw hw' using hw'
    exact ⟨s, N, g, w, hs, hw, by simp only [hw', e]⟩
  choose s N g w hs hw he using H
  haveI : Finite G := hG
  let T : Set F := Set.range (fun i => c₀ f ^ M * u i) ∪ ⋃ q : G, Set.range (w q)
  have hT : T.Finite := (Set.finite_range _).union (Set.finite_iUnion fun q => Set.finite_range _)
  have hTW : T ⊆ W := by
    rintro _ (⟨i, rfl⟩ | ⟨_, ⟨q, rfl⟩, l, rfl⟩)
    · exact hM i
    · exact hw q l
  obtain ⟨k, b, hb, hind, t, ht, hexp⟩ := exists_basis_of_finite R F c₀ hc₀ p hp hp1 T hT
  have hbW : ∀ j, b j ∈ W := fun j => by
    obtain ⟨n', g', v, t', ht', hv, e⟩ := hb j
    have := hWdiv t' ht' _ (hWsum n' g' v fun i => hTW (hv i))
    rwa [← e, inv_mul_cancel_left₀ (hne t' ht')] at this
  have key : ∀ (n' : ℕ) (g' : Fin n' → R₁) (v : Fin n' → F), (∀ i, v i ∈ T) →
      ∃ h : Fin k → R₁, c₁ (ρ t) * ∑ i, c₁ (g' i) * θ (v i) = ∑ j, c₁ (h j) * θ (b j) := by
    intro n' g' v hv
    choose h hh using fun i => hexp (v i) (hv i)
    refine ⟨fun j => ∑ i, g' i * ρ (h i j), ?_⟩
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← hθ, ← map_mul, hh, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hθ, mul_assoc]
  have htS : ρ t ∈ S := ⟨t, ht, rfl⟩
  obtain ⟨_, h, ⟨t₀, ht₀, rfl⟩, e⟩ := span_test R₁ F₁ c₁ hc₁ S
    (by
      rintro ⟨t₀, ht₀, e⟩
      exact ht₀ (((injective_iff_map_eq_zero ρ).mp hρ _ e) ▸ p.zero_mem))
    k (fun j => θ (b j)) (hlin k b hind) x (ρ f ^ M) (pow_ne_zero _ hρf)
    (by
      obtain ⟨h, e⟩ := key n r (fun i => c₀ f ^ M * u i) fun i => Or.inl ⟨i, rfl⟩
      refine ⟨_, h, htS, ?_⟩
      rw [← e, map_mul, mul_assoc, hxdef, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_pow, hθ, mul_left_comm])
    (by
      intro q hq h1 h2 h3
      let q' : G := ⟨⟨q, hq⟩, h1, hq.mem_of_pow_mem _ h2, h3⟩
      obtain ⟨h, e⟩ := key _ (g q') (w q') fun l => Or.inr (Set.mem_iUnion.mpr ⟨q', l, rfl⟩)
      exact ⟨s q', hs q', _, h, htS, by rw [← e, ← he, map_mul, mul_assoc]⟩)
  refine ⟨k, h, fun j => θ ((c₀ t₀)⁻¹ * b j), fun j => ⟨_, hWdiv t₀ ht₀ _ (hbW j), rfl⟩, ?_⟩
  have h0 : c₁ (ρ t₀) ≠ 0 := by rw [← hθ]; exact (map_ne_zero θ).mpr (hne t₀ ht₀)
  apply mul_left_cancel₀ h0
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [map_mul, map_inv₀, hθ, mul_left_comm, mul_inv_cancel_left₀ h0]

end GlobalTheory.Desc.LocalDescent
