import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris.SmallDescent

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}}
  {s : X ⟶ Sp R}

def IsLoc {T L : Thick κ s} (ι : T ⟶ L) (x : T.B) : Prop :=
  IsUnit (ι.φ x) ∧ (∀ c : L.B, ∃ (n : T.B) (N : ℕ), c * ι.φ x ^ N = ι.φ n) ∧
    (∀ n : T.B, ι.φ n = 0 → ∃ M : ℕ, x ^ M * n = 0) ∧
    ∀ (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ x) → ∃ ψ : L ⟶ S, ι ≫ ψ = a

/- English proof (translation)
Take `⟨δ', hn, hd, hu⟩` from `GlobalTheory.DPLoc.exists_away T.B T.J T.δ x T.nil`. Set `A` to `Localization.Away x`. Set `j : T.B →+* A` to `algebraMap T.B A`. Set `J' : Ideal A` to `T.J.map j`. Establish `hk : RingHom.ker T.π ≤ RingHom.ker ((Ideal.Quotient.mk J').comp j)` using `fun b hb ↦ Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker b).1 hb))`.

Set `j₀ : T.B₀ →+* A ⧸ J'` to `RingHom.liftOfSurjective T.π T.surj ⟨_, hk⟩`. Establish `hj₀ : ∀ b, j₀ (T.π b) = Ideal.Quotient.mk J' (j b)` using `fun b ↦ RingHom.liftOfSurjective_comp_apply T.π T.surj ⟨_, hk⟩ b`. Set `L : Thick κ s` to `{ B := A J := J' δ := δ' nil := hn dp := by rw [IsScalarTower.algebraMap_eq R T.B A]; exact IsDPMorphism.comp _ hd T.dp B₀ := A ⧸ J' π := Ideal.Quotient.mk J' surj := Ideal.Quotient.mk_surjective ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem x := spMap j₀ ≫ T.x w := by`. Rewrite using `[Category.assoc, T.w, ← Cris.spMap_comp]`. Use `congr 1`.

Conclude with `RingHom.ext fun r ↦ (hj₀ _).trans (congrArg (Ideal.Quotient.mk J') (IsScalarTower.algebraMap_apply R T.B A r).symm) }`. Set `ι : T ⟶ L` to `{ φ := IsScalarTower.toAlgHom R T.B A φ₀ := j₀ comm := hj₀ dp := hd pt := rfl }`. Use `⟨L, ι, IsLocalization.Away.algebraMap_isUnit (S := A) x, fun c ↦ ?_, fun n hn ↦ ?_, fun S a ha ↦ ?_⟩` and prove the remaining obligations. Take `⟨N, n, h⟩` from `IsLocalization.Away.surj (S := A) x c`. Conclude with `⟨n, N, h⟩`.

Take `⟨⟨_, M, rfl⟩, h⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers x) A n).1 hn`. Conclude with `⟨M, h⟩`. Set `g : A →+* S.B` to `IsLocalization.Away.lift (g := (a.φ : T.B →+* S.B)) x ha`. Establish `hg : ∀ b, g (j b) = a.φ b` using `fun b ↦ IsLocalization.Away.lift_eq x ha b`. Establish `hg' : g.comp j = (a.φ : T.B →+* S.B)` using `RingHom.ext hg`.

Establish `hdp : IsDPMorphism δ' S.δ g` using `hu _ _ _ g (by rw [hg']; exact a.dp)`. Establish `hz : ∀ c ∈ J', (S.π.comp g) c = 0` using `fun c hc ↦ (S.ker _).2 (hdp.1 (Ideal.mem_map_of_mem _ hc))`. Set `ψ : L ⟶ S` to `{ φ := { g with commutes' := fun r ↦ (congrArg g (IsScalarTower.algebraMap_apply R T.B A r)).trans ((hg _).trans (a.φ.commutes r)) } φ₀ := Ideal.Quotient.lift J' (S.π.comp g) hz comm := fun _ ↦ rfl dp := hdp pt := by`. Express the relevant statement in the definitionally equal form `spMap _ ≫ spMap j₀ ≫ T.x = S.x`. Rewrite using `[← Category.assoc, ← Cris.spMap_comp, ← a.pt]`.

Use `congr 2`. Use `RingHom.ext fun b ↦ ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `T.surj b`. Rewrite using `[RingHom.comp_apply, hj₀, a.comm, ← hg]`. Use `rfl }`.

Conclude with `⟨ψ, Thick.hom_ext hg⟩`.
-/
theorem exists_isLoc (T : Thick κ s) (x : T.B) : ∃ (L : Thick κ s) (ι : T ⟶ L), IsLoc ι x := by
  obtain ⟨δ', hn, hd, hu⟩ := GlobalTheory.DPLoc.exists_away T.B T.J T.δ x T.nil
  let A := Localization.Away x
  let j : T.B →+* A := algebraMap T.B A
  let J' : Ideal A := T.J.map j
  have hk : RingHom.ker T.π ≤ RingHom.ker ((Ideal.Quotient.mk J').comp j) := fun b hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker b).1 hb))
  let j₀ : T.B₀ →+* A ⧸ J' := RingHom.liftOfSurjective T.π T.surj ⟨_, hk⟩
  have hj₀ : ∀ b, j₀ (T.π b) = Ideal.Quotient.mk J' (j b) := fun b ↦
    RingHom.liftOfSurjective_comp_apply T.π T.surj ⟨_, hk⟩ b
  let L : Thick κ s :=
    { B := A
      J := J'
      δ := δ'
      nil := hn
      dp := by rw [IsScalarTower.algebraMap_eq R T.B A]; exact IsDPMorphism.comp _ hd T.dp
      B₀ := A ⧸ J'
      π := Ideal.Quotient.mk J'
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := spMap j₀ ≫ T.x
      w := by
        rw [Category.assoc, T.w, ← Cris.spMap_comp]
        congr 1
        exact RingHom.ext fun r ↦ (hj₀ _).trans
          (congrArg (Ideal.Quotient.mk J') (IsScalarTower.algebraMap_apply R T.B A r).symm) }
  let ι : T ⟶ L :=
    { φ := IsScalarTower.toAlgHom R T.B A
      φ₀ := j₀
      comm := hj₀
      dp := hd
      pt := rfl }
  refine ⟨L, ι, IsLocalization.Away.algebraMap_isUnit (S := A) x, fun c ↦ ?_, fun n hn ↦ ?_,
    fun S a ha ↦ ?_⟩
  · obtain ⟨N, n, h⟩ := IsLocalization.Away.surj (S := A) x c
    exact ⟨n, N, h⟩
  · obtain ⟨⟨_, M, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x) A n).1 hn
    exact ⟨M, h⟩
  · let g : A →+* S.B := IsLocalization.Away.lift (g := (a.φ : T.B →+* S.B)) x ha
    have hg : ∀ b, g (j b) = a.φ b := fun b ↦ IsLocalization.Away.lift_eq x ha b
    have hg' : g.comp j = (a.φ : T.B →+* S.B) := RingHom.ext hg
    have hdp : IsDPMorphism δ' S.δ g := hu _ _ _ g (by rw [hg']; exact a.dp)
    have hz : ∀ c ∈ J', (S.π.comp g) c = 0 := fun c hc ↦
      (S.ker _).2 (hdp.1 (Ideal.mem_map_of_mem _ hc))
    let ψ : L ⟶ S :=
      { φ := { g with
          commutes' := fun r ↦ (congrArg g (IsScalarTower.algebraMap_apply R T.B A r)).trans
            ((hg _).trans (a.φ.commutes r)) }
        φ₀ := Ideal.Quotient.lift J' (S.π.comp g) hz
        comm := fun _ ↦ rfl
        dp := hdp
        pt := by
          change spMap _ ≫ spMap j₀ ≫ T.x = S.x
          rw [← Category.assoc, ← Cris.spMap_comp, ← a.pt]
          congr 2
          refine RingHom.ext fun b ↦ ?_
          obtain ⟨b, rfl⟩ := T.surj b
          rw [RingHom.comp_apply, hj₀, a.comm, ← hg]
          rfl }
    exact ⟨ψ, Thick.hom_ext hg⟩

/- English proof (translation)
Establish `e' : ∀ b, ψ.φ (ι.φ b) = ψ'.φ (ι.φ b)` using `fun b ↦ congrArg (fun u : T ⟶ S ↦ u.φ b) e`. Use `Thick.hom_ext fun c ↦ ?_` and prove the remaining obligations. Take `⟨n, N, hc⟩` from `h.2.1 c`. Use `((h.1.map ψ.φ).pow N).mul_right_cancel ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul, hc, ← map_pow, e', e', ← map_mul, map_pow, hc]`.
-/
theorem IsLoc.hom_ext {T L S : Thick κ s} {ι : T ⟶ L} {x : T.B} (h : IsLoc ι x) {ψ ψ' : L ⟶ S}
    (e : ι ≫ ψ = ι ≫ ψ') : ψ = ψ' := by
  have e' : ∀ b, ψ.φ (ι.φ b) = ψ'.φ (ι.φ b) := fun b ↦ congrArg (fun u : T ⟶ S ↦ u.φ b) e
  refine Thick.hom_ext fun c ↦ ?_
  obtain ⟨n, N, hc⟩ := h.2.1 c
  refine ((h.1.map ψ.φ).pow N).mul_right_cancel ?_
  rw [← map_pow, ← map_mul, hc, ← map_pow, e', e', ← map_mul, map_pow, hc]

/- English proof (translation)
Set `G : Set T.B` to `{x | ∀ (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ x) → IsSmall κ s U S}`. It suffices to establish `h : Ideal.span G = ⊤ by`. Take `⟨σ, h1, h2⟩` from `(Ideal.span_eq_top_iff_finite G).1 h`. Conclude with `⟨σ, h2, fun x hx ↦ h1 hx⟩`. Establish `h0 : (Ideal.span G).map T.π = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `p : PrimeSpectrum T.B₀` to `⟨m, hm.isPrime⟩`. Establish `hp : T.x p ∈ ⨆ i, U i` using `by rw [hU]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hp`.

Take `⟨_, ⟨y, rfl⟩, hy, hyU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) (u := (T.x ⁻¹ᵁ U i).1) hi (T.x ⁻¹ᵁ U i).isOpen`. Take `⟨y, rfl⟩` from `T.surj y`. Use `hy (hle (Ideal.mem_map_of_mem _ (Ideal.subset_span fun S a ha ↦ ⟨i, fun q _ ↦ ?_⟩)))` and prove the remaining obligations. Rewrite using `[← a.pt]`. Use `hyU (a := spMap a.φ₀ q) fun hq ↦ ?_` and prove the remaining obligations.

Establish `hq' : a.φ₀ (T.π y) ∈ PrimeSpectrum.asIdeal q` using `hq`. Rewrite `hq'` using `[a.comm]`. Conclude with `(PrimeSpectrum.isPrime q).ne_top (Ideal.eq_top_of_isUnit_mem _ hq' (ha.map S.π))`. Take `⟨z, hz, hz1⟩` from `(Ideal.mem_map_iff_of_surjective T.π T.surj).1 (h0 ▸ Submodule.mem_top : (1 : T.B₀) ∈ (Ideal.span G).map T.π)`. Establish `hJ : z - 1 ∈ T.J` using `(T.ker _).1 (by rw [map_sub, hz1, map_one, sub_self])`.

Establish `hnil : IsNilpotent (z - 1)`. Take `⟨N, hN⟩` from `T.nil`. Use `⟨N, ?_⟩` and prove the remaining obligations. Use `hN (List.replicate N (1, z - 1)) (fun p hp ↦ by rw [List.eq_of_mem_replicate hp]; exact hJ) (by simp)` as an intermediate fact. Simplify `this` using `[T.δ.dpow_one hJ]`.

Use `Ideal.eq_top_of_isUnit_mem _ hz ?_` and prove the remaining obligations. Simplify using `using hnil.isUnit_add_one`.
-/
theorem exists_cover {K : Type} {U : K → X.Opens} (hU : ⨆ i, U i = ⊤) (T : Thick κ s) :
    ∃ (σ : Finset T.B), Ideal.span (σ : Set T.B) = ⊤ ∧
      ∀ x ∈ σ, ∀ (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ x) → IsSmall κ s U S := by
  let G : Set T.B := {x | ∀ (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ x) → IsSmall κ s U S}
  suffices h : Ideal.span G = ⊤ by
    obtain ⟨σ, h1, h2⟩ := (Ideal.span_eq_top_iff_finite G).1 h
    exact ⟨σ, h2, fun x hx ↦ h1 hx⟩
  have h0 : (Ideal.span G).map T.π = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x p ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    obtain ⟨_, ⟨y, rfl⟩, hy, hyU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (T.x ⁻¹ᵁ U i).1) hi (T.x ⁻¹ᵁ U i).isOpen
    obtain ⟨y, rfl⟩ := T.surj y
    refine hy (hle (Ideal.mem_map_of_mem _ (Ideal.subset_span fun S a ha ↦ ⟨i, fun q _ ↦ ?_⟩)))
    rw [← a.pt]
    refine hyU (a := spMap a.φ₀ q) fun hq ↦ ?_
    have hq' : a.φ₀ (T.π y) ∈ PrimeSpectrum.asIdeal q := hq
    rw [a.comm] at hq'
    exact (PrimeSpectrum.isPrime q).ne_top (Ideal.eq_top_of_isUnit_mem _ hq' (ha.map S.π))
  obtain ⟨z, hz, hz1⟩ := (Ideal.mem_map_iff_of_surjective T.π T.surj).1
    (h0 ▸ Submodule.mem_top : (1 : T.B₀) ∈ (Ideal.span G).map T.π)
  have hJ : z - 1 ∈ T.J := (T.ker _).1 (by rw [map_sub, hz1, map_one, sub_self])
  have hnil : IsNilpotent (z - 1) := by
    obtain ⟨N, hN⟩ := T.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, z - 1)) (fun p hp ↦ by rw [List.eq_of_mem_replicate hp]; exact hJ)
      (by simp)
    simpa [T.δ.dpow_one hJ] using this
  refine Ideal.eq_top_of_isUnit_mem _ hz ?_
  simpa using hnil.isUnit_add_one

/- English proof (translation)
Use `choose n hn using h`. Take `⟨N, hN⟩` from `(Set.finite_range n).bddAbove`. Use `⟨N, fun i ↦ ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le (hN (Set.mem_range_self i))`. Conclude with `mono _ _ _ (hn i)`.
-/
theorem exists_uniform {ι : Type} [Finite ι] (P : ι → ℕ → Prop)
    (mono : ∀ i n k, P i n → P i (n + k)) (h : ∀ i, ∃ n, P i n) : ∃ N, ∀ i, P i N := by
  choose n hn using h
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  refine ⟨N, fun i ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hN (Set.mem_range_self i))
  exact mono _ _ _ (hn i)

/- English proof (translation)
Take `⟨L, ι, hι⟩` from `exists_isLoc T x`. Conclude with `hι.2.2.1 n (h L ι hι.1)`.
-/
theorem exists_pow_mul_eq_zero {T : Thick κ s} (x n : T.B)
    (h : ∀ (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ x) → a.φ n = 0) : ∃ M : ℕ, x ^ M * n = 0 := by
  obtain ⟨L, ι, hι⟩ := exists_isLoc T x
  exact hι.2.2.1 n (h L ι hι.1)

/- English proof (translation)
The claim follows from `exists_uniform (fun i M ↦ x i ^ M * n i = 0) (fun i M k e ↦ by rw [add_comm, pow_add, mul_assoc, e, mul_zero]) fun i ↦ exists_pow_mul_eq_zero _ _ (h i)`.
-/
theorem exists_pow_mul_eq_zero' {T : Thick κ s} {ι : Type} [Finite ι] (x n : ι → T.B)
    (h : ∀ i (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ (x i)) → a.φ (n i) = 0) :
    ∃ M : ℕ, ∀ i, x i ^ M * n i = 0 :=
  exists_uniform (fun i M ↦ x i ^ M * n i = 0)
    (fun i M k e ↦ by rw [add_comm, pow_add, mul_assoc, e, mul_zero])
    fun i ↦ exists_pow_mul_eq_zero _ _ (h i)

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_uniform (fun i N ↦ ∃ n : T.B, ∀ S a h, g i S a h * a.φ (x i) ^ N = a.φ n) (fun i N k ⟨n, e⟩ ↦ ⟨n * x i ^ k, fun S a h ↦ by`. Rewrite using `[pow_add, ← mul_assoc, e, map_mul, map_pow]⟩)`. Use `fun i ↦ by`. Take `⟨L, ι, hι⟩` from `exists_isLoc T (x i)`. Take `⟨n, N, e⟩` from `hι.2.1 (g i L ι hι.1)`.

Use `⟨N, n, fun S a h ↦ ?_⟩` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `hι.2.2.2 S a h`. Rewrite using `[← hg i L S ι ψ hι.1 h, Thick.comp_φ, Thick.comp_φ, ← e, map_mul, map_pow]`. Use `choose n hn using hN`. Conclude with `⟨N, n, hn⟩`.
-/
theorem exists_numerator {T : Thick κ s} {ι : Type} [Finite ι] (x : ι → T.B)
    (g : ∀ i (S : Thick κ s) (a : T ⟶ S), IsUnit (a.φ (x i)) → S.B)
    (hg : ∀ i (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h',
      u.φ (g i S a h) = g i S' (a ≫ u) h') :
    ∃ (N : ℕ) (n : ι → T.B), ∀ i S a h, g i S a h * a.φ (x i) ^ N = a.φ (n i) := by
  obtain ⟨N, hN⟩ := exists_uniform
    (fun i N ↦ ∃ n : T.B, ∀ S a h, g i S a h * a.φ (x i) ^ N = a.φ n)
    (fun i N k ⟨n, e⟩ ↦ ⟨n * x i ^ k, fun S a h ↦ by
      rw [pow_add, ← mul_assoc, e, map_mul, map_pow]⟩)
    fun i ↦ by
      obtain ⟨L, ι, hι⟩ := exists_isLoc T (x i)
      obtain ⟨n, N, e⟩ := hι.2.1 (g i L ι hι.1)
      refine ⟨N, n, fun S a h ↦ ?_⟩
      obtain ⟨ψ, rfl⟩ := hι.2.2.2 S a h
      rw [← hg i L S ι ψ hι.1 h, Thick.comp_φ, Thick.comp_φ, ← e, map_mul, map_pow]
  choose n hn using hN
  exact ⟨N, n, hn⟩

def Gen {B : Type} [CommRing B] {ι : Type} [Fintype ι] (b : ι → B) : Prop :=
  ∀ N : ℕ, ∃ r : ι → B, ∑ i, r i * b i ^ N = 1

/- English proof (translation)
The claim follows from `fun N ↦ by obtain ⟨r, hr⟩ := h N exact ⟨fun i ↦ a.φ (r i), by simpa using congrArg a.φ hr⟩`.
-/
theorem Gen.map {T S : Thick κ s} {ι : Type} [Fintype ι] {b : ι → T.B} (h : Gen b) (a : T ⟶ S) :
    Gen fun i ↦ a.φ (b i) := fun N ↦ by
  obtain ⟨r, hr⟩ := h N
  exact ⟨fun i ↦ a.φ (r i), by simpa using congrArg a.φ hr⟩

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_pow_mul_eq_zero' b (fun _ ↦ t - t') fun i S a ha ↦ by`. Rewrite using `[map_sub, h S a ⟨i, ha⟩, sub_self]`. Take `⟨r, hr⟩` from `hb M`. Rewrite using `[← sub_eq_zero, ← one_mul (t - t'), ← hr, Finset.sum_mul]`. Conclude with `Finset.sum_eq_zero fun i _ ↦ by rw [mul_assoc, hM, mul_zero]`.
-/
theorem Gen.sep {T : Thick κ s} {ι : Type} [Fintype ι] {b : ι → T.B} (hb : Gen b) {t t' : T.B}
    (h : ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) → a.φ t = a.φ t') : t = t' := by
  obtain ⟨M, hM⟩ := exists_pow_mul_eq_zero' b (fun _ ↦ t - t') fun i S a ha ↦ by
    rw [map_sub, h S a ⟨i, ha⟩, sub_self]
  obtain ⟨r, hr⟩ := hb M
  rw [← sub_eq_zero, ← one_mul (t - t'), ← hr, Finset.sum_mul]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [mul_assoc, hM, mul_zero]

/- English proof (translation)
Take `⟨N, n, hn⟩` from `exists_numerator b (fun i S a h ↦ g S a ⟨i, h⟩) fun i S S' a u h h' ↦ hg S S' a u _ _`. Take `⟨M, hM⟩` from `exists_pow_mul_eq_zero' (fun p : ι × ι ↦ b p.1 * b p.2) (fun p ↦ b p.1 ^ N * n p.2 - b p.2 ^ N * n p.1) fun p S a ha ↦ by`. Rewrite `ha` using `[map_mul, IsUnit.mul_iff]`. Simplify using `only [map_sub, map_mul, map_pow, ← hn _ S a ha.1, ← hn _ S a ha.2]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr⟩` from `hb (N + M)`. Use `⟨∑ j, r j * b j ^ M * n j, fun S a ⟨i, hi⟩ ↦ (hi.pow (N + M)).mul_right_cancel ?_⟩` and prove the remaining obligations. Establish `e : (∑ j, r j * b j ^ M * n j) * b i ^ (N + M) = n i * b i ^ M`. Rewrite using `[← one_mul (n i * b i ^ M), ← hr, Finset.sum_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ by linear_combination (exp := 1) r j * hM (i, j)`.

Rewrite using `[← map_pow, ← map_mul, e, map_mul, map_pow, ← hn i S a hi, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Gen.glue {T : Thick κ s} {ι : Type} [Fintype ι] {b : ι → T.B} (hb : Gen b)
    (g : ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) → S.B)
    (hg : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h', u.φ (g S a h) = g S' (a ≫ u) h') :
    ∃ t : T.B, ∀ S a h, a.φ t = g S a h := by
  obtain ⟨N, n, hn⟩ := exists_numerator b (fun i S a h ↦ g S a ⟨i, h⟩)
    fun i S S' a u h h' ↦ hg S S' a u _ _
  obtain ⟨M, hM⟩ := exists_pow_mul_eq_zero' (fun p : ι × ι ↦ b p.1 * b p.2)
    (fun p ↦ b p.1 ^ N * n p.2 - b p.2 ^ N * n p.1) fun p S a ha ↦ by
      rw [map_mul, IsUnit.mul_iff] at ha
      simp only [map_sub, map_mul, map_pow, ← hn _ S a ha.1, ← hn _ S a ha.2]
      ring
  obtain ⟨r, hr⟩ := hb (N + M)
  refine ⟨∑ j, r j * b j ^ M * n j, fun S a ⟨i, hi⟩ ↦ (hi.pow (N + M)).mul_right_cancel ?_⟩
  have e : (∑ j, r j * b j ^ M * n j) * b i ^ (N + M) = n i * b i ^ M := by
    rw [← one_mul (n i * b i ^ M), ← hr, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by linear_combination (exp := 1) r j * hM (i, j)
  rw [← map_pow, ← map_mul, e, map_mul, map_pow, ← hn i S a hi, map_pow]
  ring

/- English proof (translation)
Establish `l : ∀ {S : Thick κ s} {a : T ⟶ S} {x y : T.B}, IsUnit (a.φ (x * y)) → IsUnit (a.φ x)` using `fun h ↦ by rw [map_mul, IsUnit.mul_iff] at h; exact h.1`. Establish `l' : ∀ {S : Thick κ s} {a : T ⟶ S} {x y : T.B}, IsUnit (a.φ (x * y)) → IsUnit (a.φ y)` using `fun h ↦ by rw [map_mul, IsUnit.mul_iff] at h; exact h.2`. Take `⟨N, n, hn⟩` from `exists_numerator (fun p : ι × ι ↦ b p.1 * b p.2) (fun p S a h ↦ c S a p.1 (l h) - c S a p.2 (l' h)) fun p S S' a u h h' ↦ hc S S' a u _ _ _ _ _ _`. Establish `hn' : ∀ (S : Thick κ s) (a : T ⟶ S) i j hi hj, a.φ (n (i, j)) = (c S a i hi - c S a j hj) * (a.φ (b i) * a.φ (b j)) ^ N` using `fun S a i j hi hj ↦ by`. Establish `h : IsUnit (a.φ (b i * b j))` using `by rw [map_mul]; exact hi.mul hj`.

Rewrite using `[← map_mul]`. Conclude with `(hn (i, j) S a h).symm`. Take `⟨M, hM⟩` from `exists_pow_mul_eq_zero' (fun p : ι × ι × ι ↦ b p.1 * b p.2.1 * b p.2.2) (fun p ↦ b p.2.2 ^ N * n (p.1, p.2.1) + b p.1 ^ N * n (p.2.1, p.2.2) - b p.2.1 ^ N * n (p.1, p.2.2)) fun p S a ha ↦ by`. Simplify using `only [map_sub, map_add, map_mul, map_pow, hn' S a _ _ (l (l ha)) (l' (l ha)), hn' S a _ _ (l' (l ha)) (l' ha), hn' S a _ _ (l (l ha)) (l' ha)]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr⟩` from `hb (N + M)`. Set `m : ι → T.B` to `fun i ↦ ∑ k, r k * (b i * b k) ^ M * n (i, k)`. Establish `hm : ∀ i j, b j ^ (N + M) * m i - b i ^ (N + M) * m j = (b i * b j) ^ M * n (i, j)`. Introduce `i j`. Rewrite using `[← one_mul ((b i * b j) ^ M * n (i, j)), ← hr, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ ↦ by linear_combination (exp := 1) (-r k) * hM (i, j, k)`. Establish `ex : ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) → ∃ y : S.B, ∀ j hj, (c S a j hj - y) * a.φ (b j) ^ (N + M) = a.φ (m j)`. Introduce and unpack `S a ⟨i, hi⟩`. Take `⟨v, hv⟩` from `(hi.pow (N + M)).exists_right_inv`. Use `⟨c S a i hi - a.φ (m i) * v, fun j hj ↦ (hi.pow (N + M)).mul_right_cancel ?_⟩` and prove the remaining obligations.

Use `congrArg a.φ (hm i j)` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, hn' S a i j hi hj] at this`. Take the linear combination `(exp := 1) this + a.φ (m i) * a.φ (b j) ^ (N + M) * hv`. Use `choose e he using ex`. Use `⟨e, fun S S' a u i hi hi' ↦ (hi'.pow (N + M)).mul_right_cancel ?_⟩` and prove the remaining obligations.

Rewrite using `[he, Thick.comp_φ, Thick.comp_φ, ← he S a ⟨i, hi⟩ i hi, map_mul, map_pow]`.
-/
theorem Gen.cech {T : Thick κ s} {ι : Type} [Fintype ι] {b : ι → T.B} (hb : Gen b)
    (c : ∀ (S : Thick κ s) (a : T ⟶ S) i, IsUnit (a.φ (b i)) → S.B)
    (hc : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') i j hi hj hi' hj',
      u.φ (c S a i hi - c S a j hj) = c S' (a ≫ u) i hi' - c S' (a ≫ u) j hj') :
    ∃ e : ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) → S.B,
      ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') i hi hi',
        u.φ (c S a i hi - e S a ⟨i, hi⟩) = c S' (a ≫ u) i hi' - e S' (a ≫ u) ⟨i, hi'⟩ := by
  have l : ∀ {S : Thick κ s} {a : T ⟶ S} {x y : T.B}, IsUnit (a.φ (x * y)) → IsUnit (a.φ x) :=
    fun h ↦ by rw [map_mul, IsUnit.mul_iff] at h; exact h.1
  have l' : ∀ {S : Thick κ s} {a : T ⟶ S} {x y : T.B}, IsUnit (a.φ (x * y)) → IsUnit (a.φ y) :=
    fun h ↦ by rw [map_mul, IsUnit.mul_iff] at h; exact h.2
  obtain ⟨N, n, hn⟩ := exists_numerator (fun p : ι × ι ↦ b p.1 * b p.2)
    (fun p S a h ↦ c S a p.1 (l h) - c S a p.2 (l' h)) fun p S S' a u h h' ↦ hc S S' a u _ _ _ _ _ _
  have hn' : ∀ (S : Thick κ s) (a : T ⟶ S) i j hi hj, a.φ (n (i, j)) =
      (c S a i hi - c S a j hj) * (a.φ (b i) * a.φ (b j)) ^ N := fun S a i j hi hj ↦ by
    have h : IsUnit (a.φ (b i * b j)) := by rw [map_mul]; exact hi.mul hj
    rw [← map_mul]
    exact (hn (i, j) S a h).symm
  obtain ⟨M, hM⟩ := exists_pow_mul_eq_zero' (fun p : ι × ι × ι ↦ b p.1 * b p.2.1 * b p.2.2)
    (fun p ↦ b p.2.2 ^ N * n (p.1, p.2.1) + b p.1 ^ N * n (p.2.1, p.2.2) -
      b p.2.1 ^ N * n (p.1, p.2.2)) fun p S a ha ↦ by
      simp only [map_sub, map_add, map_mul, map_pow, hn' S a _ _ (l (l ha)) (l' (l ha)),
        hn' S a _ _ (l' (l ha)) (l' ha), hn' S a _ _ (l (l ha)) (l' ha)]
      ring
  obtain ⟨r, hr⟩ := hb (N + M)
  let m : ι → T.B := fun i ↦ ∑ k, r k * (b i * b k) ^ M * n (i, k)
  have hm : ∀ i j, b j ^ (N + M) * m i - b i ^ (N + M) * m j = (b i * b j) ^ M * n (i, j) := by
    intro i j
    rw [← one_mul ((b i * b j) ^ M * n (i, j)), ← hr, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by linear_combination (exp := 1) (-r k) * hM (i, j, k)
  have ex : ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) →
      ∃ y : S.B, ∀ j hj, (c S a j hj - y) * a.φ (b j) ^ (N + M) = a.φ (m j) := by
    rintro S a ⟨i, hi⟩
    obtain ⟨v, hv⟩ := (hi.pow (N + M)).exists_right_inv
    refine ⟨c S a i hi - a.φ (m i) * v, fun j hj ↦ (hi.pow (N + M)).mul_right_cancel ?_⟩
    have := congrArg a.φ (hm i j)
    simp only [map_sub, map_mul, map_pow, hn' S a i j hi hj] at this
    linear_combination (exp := 1) this + a.φ (m i) * a.φ (b j) ^ (N + M) * hv
  choose e he using ex
  refine ⟨e, fun S S' a u i hi hi' ↦ (hi'.pow (N + M)).mul_right_cancel ?_⟩
  rw [he, Thick.comp_φ, Thick.comp_φ, ← he S a ⟨i, hi⟩ i hi, map_mul, map_pow]

section Cover

variable {K : Type} {U : K → X.Opens}

/- English proof (translation)
The claim follows from `h.imp fun _ ↦ u.le_preimage`.
-/
theorem isSmall_of_hom {S S' : Thick κ s} (u : S ⟶ S') (h : IsSmall κ s U S) : IsSmall κ s U S' :=
  h.imp fun _ ↦ u.le_preimage

/- English proof (translation)
Take `⟨σ, h1, h2⟩` from `exists_cover hU T`. Use `⟨(σ : Set T.B), inferInstance, Subtype.val, fun N ↦ ?_, fun S a ⟨i, hi⟩ ↦ h2 _ i.2 S a hi⟩` and prove the remaining obligations. Use `Ideal.span_range_pow_eq_top _ h1 fun _ ↦ N` as an intermediate fact. Conclude with `Ideal.mem_span_range_iff_exists_fun.1 (this ▸ Submodule.mem_top)`.
-/
theorem exists_gen (hU : ⨆ i, U i = ⊤) (T : Thick κ s) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → T.B), Gen b ∧
      ∀ (S : Thick κ s) (a : T ⟶ S), (∃ i, IsUnit (a.φ (b i))) → IsSmall κ s U S := by
  obtain ⟨σ, h1, h2⟩ := exists_cover hU T
  refine ⟨(σ : Set T.B), inferInstance, Subtype.val, fun N ↦ ?_, fun S a ⟨i, hi⟩ ↦ h2 _ i.2 S a hi⟩
  have := Ideal.span_range_pow_eq_top _ h1 fun _ ↦ N
  exact Ideal.mem_span_range_iff_exists_fun.1 (this ▸ Submodule.mem_top)

/- English proof (translation)
Take `⟨ι, _, b, hb, hs⟩` from `exists_gen hU T`. Conclude with `hb.sep fun S a ha ↦ h S a (hs S a ha)`.
-/
theorem sep (hU : ⨆ i, U i = ⊤) {T : Thick κ s} {t t' : T.B}
    (h : ∀ (S : Thick κ s) (a : T ⟶ S), IsSmall κ s U S → a.φ t = a.φ t') : t = t' := by
  obtain ⟨ι, _, b, hb, hs⟩ := exists_gen hU T
  exact hb.sep fun S a ha ↦ h S a (hs S a ha)

/- English proof (translation)
Take `⟨ι, _, b, hb, hs⟩` from `exists_gen hU T`. Take `⟨t, ht⟩` from `hb.glue (fun S a h ↦ g S a (hs S a h)) fun S S' a u _ _ ↦ hg S S' a u _ _`. Use `⟨t, fun S a h ↦ (hb.map a).sep fun S' u hu ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hg S S' a u h (isSmall_of_hom u h), ← ht S' (a ≫ u) hu, Thick.comp_φ]`.
-/
theorem glue (hU : ⨆ i, U i = ⊤) {T : Thick κ s}
    (g : ∀ (S : Thick κ s) (_ : T ⟶ S), IsSmall κ s U S → S.B)
    (hg : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h', u.φ (g S a h) = g S' (a ≫ u) h') :
    ∃ t : T.B, ∀ S a h, a.φ t = g S a h := by
  obtain ⟨ι, _, b, hb, hs⟩ := exists_gen hU T
  obtain ⟨t, ht⟩ := hb.glue (fun S a h ↦ g S a (hs S a h)) fun S S' a u _ _ ↦ hg S S' a u _ _
  refine ⟨t, fun S a h ↦ (hb.map a).sep fun S' u hu ↦ ?_⟩
  rw [hg S S' a u h (isSmall_of_hom u h), ← ht S' (a ≫ u) hu, Thick.comp_φ]

/- English proof (translation)
Take `⟨ι, _, b, hb, hs⟩` from `exists_gen hU T`. Use `choose L j hj using fun i ↦ exists_isLoc T (b i)`. Use `choose ψ hψ using fun i ↦ (hj i).2.2.2`. Establish `hL : ∀ i, IsSmall κ s U (L i)` using `fun i ↦ hs _ (j i) ⟨i, (hj i).1⟩`. Establish `key : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') i hi hi', f (ψ i S' (a ≫ u) hi') (hL i) = u.φ (f (ψ i S a hi) (hL i)) + f u (hs S a ⟨i, hi⟩)` using `fun S S' a u i hi hi' ↦ by`.

Rewrite using `[← hf, (hj i).hom_ext (ψ := ψ i S' (a ≫ u) hi') (ψ' := ψ i S a hi ≫ u) (by rw [hψ, ← Category.assoc, hψ])]`. Take `⟨e, he⟩` from `hb.cech (fun S a i hi ↦ f (ψ i S a hi) (hL i)) fun S S' a u i j hi hj hi' hj' ↦ by`. Rewrite using `[key S S' a u i hi, key S S' a u j hj, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `he' : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h' k, f u k = e S' (a ≫ u) h' - u.φ (e S a h)`.

Introduce and unpack `S S' a u ⟨i, hi⟩ h' k`. Establish `hi' : IsUnit ((a ≫ u).φ (b i))` using `hi.map u.φ`. Use `he S S' a u i hi hi'` as an intermediate fact. Rewrite `this` using `[key S S' a u i hi hi', map_sub]`. Take the linear combination `(exp := 1) -this`.

Establish `ex : ∀ (S : Thick κ s) (a : T ⟶ S) (h : IsSmall κ s U S), ∃ t : S.B, ∀ (S' : Thick κ s) (v : S ⟶ S') k, v.φ t = e S' (a ≫ v) k - f v h` using `fun S a h ↦ (hb.map a).glue (fun S' v k ↦ e S' (a ≫ v) k - f v h) fun S' S'' v w k k' ↦ by`. Use `he' S' S'' (a ≫ v) w k (by rw [Category.assoc]; exact k') (isSmall_of_hom v h)` as an intermediate fact. Simplify using `only [Category.assoc] at this`. Rewrite using `[map_sub, hf v w h (isSmall_of_hom v h), this]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose E hE using ex`. Use `⟨E, fun S S' a u h h' ↦ (hb.map (a ≫ u)).sep fun S'' v k ↦ ?_⟩` and prove the remaining obligations. Establish `h1` using `hE S' (a ≫ u) h' S'' v k`. Establish `h2` using `hE S a h S'' (u ≫ v) k`. Simplify using `only [Category.assoc] at h1`.

Rewrite `h2` using `[Thick.comp_φ, hf u v h h']`. Rewrite using `[map_sub, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem triv (hU : ⨆ i, U i = ⊤)
    (f : ∀ {S S' : Thick κ s} (_ : S ⟶ S'), IsSmall κ s U S → S'.B)
    (hf : ∀ {S S' S'' : Thick κ s} (u : S ⟶ S') (v : S' ⟶ S'') h h',
      f (u ≫ v) h = v.φ (f u h) + f v h') (T : Thick κ s) :
    ∃ e : ∀ (S : Thick κ s) (_ : T ⟶ S), IsSmall κ s U S → S.B,
      ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h',
        f u h = e S' (a ≫ u) h' - u.φ (e S a h) := by
  obtain ⟨ι, _, b, hb, hs⟩ := exists_gen hU T
  choose L j hj using fun i ↦ exists_isLoc T (b i)
  choose ψ hψ using fun i ↦ (hj i).2.2.2
  have hL : ∀ i, IsSmall κ s U (L i) := fun i ↦ hs _ (j i) ⟨i, (hj i).1⟩
  have key : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') i hi hi',
      f (ψ i S' (a ≫ u) hi') (hL i) = u.φ (f (ψ i S a hi) (hL i)) + f u (hs S a ⟨i, hi⟩) :=
    fun S S' a u i hi hi' ↦ by
      rw [← hf, (hj i).hom_ext (ψ := ψ i S' (a ≫ u) hi') (ψ' := ψ i S a hi ≫ u)
        (by rw [hψ, ← Category.assoc, hψ])]
  obtain ⟨e, he⟩ := hb.cech (fun S a i hi ↦ f (ψ i S a hi) (hL i))
    fun S S' a u i j hi hj hi' hj' ↦ by
      rw [key S S' a u i hi, key S S' a u j hj, map_sub]; ring
  have he' : ∀ (S S' : Thick κ s) (a : T ⟶ S) (u : S ⟶ S') h h' k,
      f u k = e S' (a ≫ u) h' - u.φ (e S a h) := by
    rintro S S' a u ⟨i, hi⟩ h' k
    have hi' : IsUnit ((a ≫ u).φ (b i)) := hi.map u.φ
    have := he S S' a u i hi hi'
    rw [key S S' a u i hi hi', map_sub] at this
    linear_combination (exp := 1) -this
  have ex : ∀ (S : Thick κ s) (a : T ⟶ S) (h : IsSmall κ s U S), ∃ t : S.B,
      ∀ (S' : Thick κ s) (v : S ⟶ S') k, v.φ t = e S' (a ≫ v) k - f v h := fun S a h ↦
    (hb.map a).glue (fun S' v k ↦ e S' (a ≫ v) k - f v h) fun S' S'' v w k k' ↦ by
      have := he' S' S'' (a ≫ v) w k (by rw [Category.assoc]; exact k') (isSmall_of_hom v h)
      simp only [Category.assoc] at this
      rw [map_sub, hf v w h (isSmall_of_hom v h), this]
      ring
  choose E hE using ex
  refine ⟨E, fun S S' a u h h' ↦ (hb.map (a ≫ u)).sep fun S'' v k ↦ ?_⟩
  have h1 := hE S' (a ≫ u) h' S'' v k
  have h2 := hE S a h S'' (u ≫ v) k
  simp only [Category.assoc] at h1
  rw [Thick.comp_φ, hf u v h h'] at h2
  rw [map_sub, h1, h2]
  ring

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_` and prove the remaining obligations. Take `⟨f, rfl⟩` from `H1.mk_surjective _ c`. Take `⟨g, hg⟩` from `H1.mk_eq_zero.1 hc`. Set `g' : ∀ S : Thick κ s, IsSmall κ s U S → S.B` to `fun S h ↦ g ⟨S, h⟩`. Establish `hg' : ∀ (S S' : Thick κ s) (u : S ⟶ S') h h', g' S' h' - u.φ (g' S h) = ev f u` using `fun S S' u h h' ↦ congrFun (congrFun (congrFun hg ⟨S, h⟩) ⟨S', h'⟩) ⟨u⟩`.

Use `choose t ht using fun T : Thick κ s ↦ glue hU (T := T) (fun S a h ↦ g' S h - ev f a) fun S S' a u h h' ↦ by rw [map_sub, ev_comp, ← hg' S S' u h h']; ring`. Use `H1.mk_eq_zero.2 ⟨t, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Express the relevant statement in the definitionally equal form `t T' - φ.φ (t T) = ev f φ`. Use `sep hU fun S a h ↦ ?_` and prove the remaining obligations.

Rewrite using `[map_sub, ← Thick.comp_φ, ht _ _ _ h, ht _ _ _ h, ev_comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem small_descent_H1_injective (hU : ⨆ i, U i = ⊤) :
    Function.Injective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull1 := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
  let g' : ∀ S : Thick κ s, IsSmall κ s U S → S.B := fun S h ↦ g ⟨S, h⟩
  have hg' : ∀ (S S' : Thick κ s) (u : S ⟶ S') h h', g' S' h' - u.φ (g' S h) = ev f u :=
    fun S S' u h h' ↦ congrFun (congrFun (congrFun hg ⟨S, h⟩) ⟨S', h'⟩) ⟨u⟩
  choose t ht using fun T : Thick κ s ↦ glue hU (T := T) (fun S a h ↦ g' S h - ev f a)
    fun S S' a u h h' ↦ by rw [map_sub, ev_comp, ← hg' S S' u h h']; ring
  refine H1.mk_eq_zero.2 ⟨t, ?_⟩
  funext T T' φ
  change t T' - φ.φ (t T) = ev f φ
  refine sep hU fun S a h ↦ ?_
  rw [map_sub, ← Thick.comp_φ, ht _ _ _ h, ht _ _ _ h, ev_comp]
  ring

/- English proof (translation)
Introduce `c`. Take `⟨f, rfl⟩` from `H1.mk_surjective _ c`. Set `f' : ∀ {S S' : Thick κ s} (_ : S ⟶ S'), IsSmall κ s U S → S'.B` to `fun {S S'} u h ↦ f.1 ⟨S, h⟩ ⟨S', isSmall_of_hom u h⟩ ⟨u⟩`. Use `choose e he using triv hU f' fun {S S' S''} u v h h' ↦ Z1.comp f (T := ⟨S, h⟩) (T' := ⟨S', h'⟩) (T'' := ⟨S'', isSmall_of_hom v h'⟩) ⟨u⟩ ⟨v⟩`. Use `choose F hF using fun (T T' : Thick κ s) (φ : T ⟶ T') ↦ glue hU (T := T') (fun S a h ↦ e T S (φ ≫ a) h - e T' S a h) fun S S' a u h h' ↦ by`.

Establish `h1` using `he T S S' (φ ≫ a) u h h'`. Establish `h2` using `he T' S S' a u h h'`. Rewrite `h1` using `[Category.assoc]`. Rewrite using `[map_sub]`. Take the linear combination `(exp := 1) h1 - h2`.

Use `⟨H1.mk _ ⟨F, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F T T'' (φ ≫ ψ) = ψ.φ (F T T' φ) + F T' T'' ψ`. Use `sep hU fun S a h ↦ ?_` and prove the remaining obligations. Rewrite using `[map_add, ← Thick.comp_φ, hF _ _ _ _ _ h, hF _ _ _ _ _ h, hF _ _ _ _ _ h, Category.assoc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]`. Use `⟨fun T ↦ -e T.obj T.obj (𝟙 _) T.property, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Express the relevant statement in the definitionally equal form `-e T'.obj T'.obj (𝟙 _) T'.property - φ.hom.φ (-e T.obj T.obj (𝟙 _) T.property) = F T.obj T'.obj φ.hom - f' φ.hom T.property`. Establish `h1` using `hF _ _ φ.hom _ (𝟙 _) T'.property`.

Establish `h2` using `he _ _ _ (𝟙 _) φ.hom T.property T'.property`. Rewrite `h1` using `[Thick.id_φ, Category.comp_id]`. Rewrite `h2` using `[Category.id_comp]`. Rewrite using `[h1, h2, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem small_descent_H1_surjective (hU : ⨆ i, U i = ⊤) :
    Function.Surjective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull1 := by
  intro c
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  let f' : ∀ {S S' : Thick κ s} (_ : S ⟶ S'), IsSmall κ s U S → S'.B := fun {S S'} u h ↦
    f.1 ⟨S, h⟩ ⟨S', isSmall_of_hom u h⟩ ⟨u⟩
  choose e he using triv hU f' fun {S S' S''} u v h h' ↦
    Z1.comp f (T := ⟨S, h⟩) (T' := ⟨S', h'⟩) (T'' := ⟨S'', isSmall_of_hom v h'⟩) ⟨u⟩ ⟨v⟩
  choose F hF using fun (T T' : Thick κ s) (φ : T ⟶ T') ↦ glue hU (T := T')
    (fun S a h ↦ e T S (φ ≫ a) h - e T' S a h) fun S S' a u h h' ↦ by
      have h1 := he T S S' (φ ≫ a) u h h'
      have h2 := he T' S S' a u h h'
      rw [Category.assoc] at h1
      rw [map_sub]
      linear_combination (exp := 1) h1 - h2
  refine ⟨H1.mk _ ⟨F, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩
  · change F T T'' (φ ≫ ψ) = ψ.φ (F T T' φ) + F T' T'' ψ
    refine sep hU fun S a h ↦ ?_
    rw [map_add, ← Thick.comp_φ, hF _ _ _ _ _ h, hF _ _ _ _ _ h, hF _ _ _ _ _ h, Category.assoc]
    ring
  · rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
    refine ⟨fun T ↦ -e T.obj T.obj (𝟙 _) T.property, ?_⟩
    funext T T' φ
    change -e T'.obj T'.obj (𝟙 _) T'.property - φ.hom.φ (-e T.obj T.obj (𝟙 _) T.property) =
      F T.obj T'.obj φ.hom - f' φ.hom T.property
    have h1 := hF _ _ φ.hom _ (𝟙 _) T'.property
    have h2 := he _ _ _ (𝟙 _) φ.hom T.property T'.property
    rw [Thick.id_φ, Category.comp_id] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, map_neg]
    ring

end Cover

/- English proof (translation)
Assemble the required witnesses or components as `⟨small_descent_H1_injective hU, small_descent_H1_surjective hU⟩`.
-/
theorem pull1_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull1 :=
  ⟨small_descent_H1_injective hU, small_descent_H1_surjective hU⟩

end GlobalTheory.Cris.SmallDescent
