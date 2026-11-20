import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorsionChars

/- English proof (translation)
Use `set m := Nat.card (rootsOfUnity n Ω) with hm`. Use `haveI : NeZero m := ⟨Nat.card_pos.ne'⟩`. Establish `hinj : Function.Injective (Units.map (i : Ω →* Ω'))` using `Units.map_injective i.injective`. Set `f : rootsOfUnity n Ω → rootsOfUnity m Ω'` to `fun u => ⟨Units.map (i : Ω →* Ω') u.1, by`. Establish `h1 : (u : Ωˣ) ^ m = 1`.

Use `congrArg Subtype.val (pow_card_eq_one' (x := u))` as an intermediate fact. Rewrite `this` using `[Subgroup.coe_pow, Subgroup.coe_one]`. Conclude with `this`. Rewrite using `[mem_rootsOfUnity, ← map_pow, h1, map_one]⟩`. Establish `hf : Function.Injective f`.

Introduce `a b hab`. Conclude with `Subtype.ext (hinj (congrArg Subtype.val hab))`. Establish `hbij` using `hf.bijective_of_nat_card_le (card_rootsOfUnity Ω' m)`. Take `⟨u, hu⟩` from `hbij.2 ⟨v, by rw [mem_rootsOfUnity]; exact hv⟩`. Conclude with `⟨u.1, congrArg Subtype.val hu⟩`.
-/
theorem exists_units_map_eq {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') (n : ℕ) [NeZero n]
    (v : Ω'ˣ) (hv : v ^ Nat.card (rootsOfUnity n Ω) = 1) :
    ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = v := by
  classical
  set m := Nat.card (rootsOfUnity n Ω) with hm
  haveI : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  let f : rootsOfUnity n Ω → rootsOfUnity m Ω' := fun u =>
    ⟨Units.map (i : Ω →* Ω') u.1, by
      have h1 : (u : Ωˣ) ^ m = 1 := by
        have := congrArg Subtype.val (pow_card_eq_one' (x := u))
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        exact this
      rw [mem_rootsOfUnity, ← map_pow, h1, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hbij := hf.bijective_of_nat_card_le (card_rootsOfUnity Ω' m)
  obtain ⟨u, hu⟩ := hbij.2 ⟨v, by rw [mem_rootsOfUnity]; exact hv⟩
  exact ⟨u.1, congrArg Subtype.val hu⟩

/- English proof (translation)
Establish `h1 : χ 1 = 1`. Use `hχ 1 1 (one_pow n) (one_pow n)` as an intermediate fact. Simplify using `using this`. Proceed by induction on `k with`. Consider the case `zero => simpa using h1`.

Consider the case `succ k ih`. Establish `hk : (g ^ k) ^ n = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]`. Rewrite using `[pow_succ, hχ _ _ hk hg, ih, pow_succ]`.
-/
theorem pow_right_of_mul {G M : Type} [CommGroup G] [CommGroup M] (n : ℕ) (χ : G → M)
    (hχ : ∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g')
    (g : G) (hg : g ^ n = 1) (k : ℕ) : χ (g ^ k) = χ g ^ k := by
  have h1 : χ 1 = 1 := by
    have := hχ 1 1 (one_pow n) (one_pow n)
    simpa using this
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : (g ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]
    rw [pow_succ, hχ _ _ hk hg, ih, pow_succ]

/- English proof (translation)
Introduce `Ω Ω' _ _ i C A _ _ rel n hn hCA hAC hmul hinjA hinjC e e' emul eperf enondeg e'mul e'perf`. Use `haveI : NeZero n := ⟨by omega⟩`. Establish `hinj : Function.Injective (Units.map (i : Ω →* Ω'))` using `Units.map_injective i.injective`. Establish `hrel11 : rel 1 1`. Take `⟨a₀, -, h₀⟩` from `hCA 1 (one_pow n)`.

Establish `h` using `hmul _ _ _ _ h₀ h₀`. Rewrite `h` using `[_root_.mul_one]`. Establish `: a₀ * a₀ = a₀` using `hinjA _ _ _ h h₀`. Establish `h1 : a₀ = 1` using `by simpa using this`. Rewrite `h₀` using `[h1]`. Then use the resulting hypothesis.

Establish `hrelpow : ∀ a c, rel a c → ∀ k : ℕ, rel (a ^ k) (c ^ k)`. Introduce `a c h k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hrel11`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`.

Conclude with `hmul _ _ _ _ ih h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y' hy' set m := Nat.card (rootsOfUnity n Ω) with hm`. Establish `hCm : ∀ g : C, g ^ n = 1 → g ^ m = 1`. Introduce `g hg`.

Use `enondeg _ (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg m]`. Establish `hmem : e x g ∈ rootsOfUnity n Ω`. Rewrite using `[mem_rootsOfUnity, ← pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg n, hg]`.

Use `emul x 1 1 hx (one_pow n) (one_pow n)` as an intermediate fact. Simplify using `using this`. Use `congrArg Subtype.val (pow_card_eq_one' (x := (⟨e x g, hmem⟩ : rootsOfUnity n Ω)))` as an intermediate fact. Rewrite `this` using `[Subgroup.coe_pow, Subgroup.coe_one]`. Conclude with `this`.

Establish `hAm : ∀ a : A, a ^ n = 1 → a ^ m = 1`. Introduce `a ha`. Take `⟨c, hc, hac⟩` from `hAC a ha`. Establish `h` using `hrelpow a c hac m`. Rewrite `h` using `[hCm c hc]`.

Conclude with `hinjA _ _ _ h hrel11`. Establish `hval : ∀ a : A, a ^ n = 1 → ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = e' y' a`. Introduce `a ha`. Apply `exists_units_map_eq i n` to reduce the goal to its premises. Rewrite using `[← pow_right_of_mul n (e' y') (fun g g' => e'mul y' g g' hy') a ha m, hAm a ha]`.

Use `e'mul y' 1 1 hy' (one_pow n) (one_pow n)` as an intermediate fact. Simplify using `using this`. Establish `hpart : ∀ c : C, c ^ n = 1 → ∃ u : Ωˣ, ∃ a : A, a ^ n = 1 ∧ rel a c ∧ Units.map (i : Ω →* Ω') u = e' y' a`. Introduce `c hc`. Take `⟨a, ha, hac⟩` from `hCA c hc`.

Take `⟨u, hu⟩` from `hval a ha`. Conclude with `⟨u, a, ha, hac, hu⟩`. Set `χ : C → Ωˣ` to `fun c => if h : c ^ n = 1 then (hpart c h).choose else 1`. Establish `hχ : ∀ c : C, c ^ n = 1 → ∀ a : A, a ^ n = 1 → rel a c → Units.map (i : Ω →* Ω') (χ c) = e' y' a`. Introduce `c hc a ha hac`.

Take `⟨a₁, -, hrel, hu⟩` from `(hpart c hc).choose_spec`. Establish `: χ c = (hpart c hc).choose` using `dif_pos hc`. Rewrite using `[this, hu, hinjA _ _ _ hrel hac]`. Take `⟨y, hy, hye⟩` from `eperf χ (by`. Introduce `g g' hg hg'`.

Take `⟨a, ha, hag⟩` from `hCA g hg`. Take `⟨a', ha', hag'⟩` from `hCA g' hg'`. Establish `hgg : (g * g') ^ n = 1` using `by rw [mul_pow, hg, hg', _root_.one_mul]`. Establish `haa : (a * a') ^ n = 1` using `by rw [mul_pow, ha, ha', _root_.one_mul]`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, hχ _ hgg _ haa (hmul _ _ _ _ hag hag'), hχ _ hg _ ha hag, hχ _ hg' _ ha' hag', e'mul y' _ _ hy' ha ha'])`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Introduce `g g' hg hg' hrel`. Rewrite using `[← hχ g hg g' hg' hrel, hye g hg]`. Both sides reduce to the same expression.

Introduce `y hy`. Establish `hpart : ∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c` using `hAC`. Set `χ : A → Ω'ˣ` to `fun a => if h : a ^ n = 1 then Units.map (i : Ω →* Ω') (e y (hpart a h).choose) else 1`. Establish `hχ : ∀ a : A, a ^ n = 1 → ∀ c : C, rel a c → χ a = Units.map (i : Ω →* Ω') (e y c)`. Introduce `a ha c hac`.

Establish `: χ a = Units.map (i : Ω →* Ω') (e y (hpart a ha).choose)` using `dif_pos ha`. Rewrite using `[this, hinjC _ _ _ (hpart a ha).choose_spec.2 hac]`. Take `⟨y', hy', hye⟩` from `e'perf χ (by`. Introduce `g g' hg hg'`. Take `⟨c, hc, hgc⟩` from `hAC g hg`.

Take `⟨c', hc', hgc'⟩` from `hAC g' hg'`. Establish `hgg : (g * g') ^ n = 1` using `by rw [mul_pow, hg, hg', _root_.one_mul]`. Rewrite using `[hχ _ hgg _ (hmul _ _ _ _ hgc hgc'), hχ _ hg _ hgc, hχ _ hg' _ hgc', emul y _ _ hy hc hc', map_mul])`. Use `⟨y', hy', ?_⟩` and prove the remaining obligations. Introduce `g g' hg hg' hrel`.

Rewrite using `[← hye g' hg', hχ g' hg' g hrel]`. Both sides reduce to the same expression.
-/
theorem chars_descend : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (C A : Type) [CommGroup C] [CommGroup A] (rel : A → C → Prop) (n : ℕ), 1 ≤ n →
  (∀ c : C, c ^ n = 1 → ∃ a : A, a ^ n = 1 ∧ rel a c) →
  (∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c) →
  (∀ a a' c c', rel a c → rel a' c' → rel (a * a') (c * c')) →
  (∀ a a' c, rel a c → rel a' c → a = a') →
  (∀ a c c', rel a c → rel a c' → c = c') →
  ∀ (e : C → C → Ωˣ) (e' : A → A → Ω'ˣ),
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g') →
  (∀ χ : C → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g) →
  (∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1) →
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e' x (g * g') = e' x g * e' x g') →
  (∀ χ : A → Ω'ˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e' x g) →
  (∀ y' : A, y' ^ n = 1 → ∃ y : C, y ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) ∧
  (∀ y : C, y ^ n = 1 → ∃ y' : A, y' ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) := by
  classical
  intro Ω Ω' _ _ i C A _ _ rel n hn hCA hAC hmul hinjA hinjC e e' emul eperf enondeg e'mul e'perf
  haveI : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  have hrel11 : rel 1 1 := by
    obtain ⟨a₀, -, h₀⟩ := hCA 1 (one_pow n)
    have h := hmul _ _ _ _ h₀ h₀
    rw [_root_.mul_one] at h
    have : a₀ * a₀ = a₀ := hinjA _ _ _ h h₀
    have h1 : a₀ = 1 := by simpa using this
    rwa [h1] at h₀
  have hrelpow : ∀ a c, rel a c → ∀ k : ℕ, rel (a ^ k) (c ^ k) := by
    intro a c h k
    induction k with
    | zero => simpa using hrel11
    | succ k ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  refine ⟨?_, ?_⟩
  · intro y' hy'
    set m := Nat.card (rootsOfUnity n Ω) with hm
    have hCm : ∀ g : C, g ^ n = 1 → g ^ m = 1 := by
      intro g hg
      refine enondeg _ (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) ?_
      intro x hx
      rw [pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg m]
      have hmem : e x g ∈ rootsOfUnity n Ω := by
        rw [mem_rootsOfUnity, ← pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg n, hg]
        have := emul x 1 1 hx (one_pow n) (one_pow n)
        simpa using this
      have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨e x g, hmem⟩ : rootsOfUnity n Ω)))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hAm : ∀ a : A, a ^ n = 1 → a ^ m = 1 := by
      intro a ha
      obtain ⟨c, hc, hac⟩ := hAC a ha
      have h := hrelpow a c hac m
      rw [hCm c hc] at h
      exact hinjA _ _ _ h hrel11
    have hval : ∀ a : A, a ^ n = 1 → ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = e' y' a := by
      intro a ha
      apply exists_units_map_eq i n
      rw [← pow_right_of_mul n (e' y') (fun g g' => e'mul y' g g' hy') a ha m, hAm a ha]
      have := e'mul y' 1 1 hy' (one_pow n) (one_pow n)
      simpa using this
    have hpart : ∀ c : C, c ^ n = 1 → ∃ u : Ωˣ, ∃ a : A, a ^ n = 1 ∧ rel a c ∧
        Units.map (i : Ω →* Ω') u = e' y' a := by
      intro c hc
      obtain ⟨a, ha, hac⟩ := hCA c hc
      obtain ⟨u, hu⟩ := hval a ha
      exact ⟨u, a, ha, hac, hu⟩
    let χ : C → Ωˣ := fun c => if h : c ^ n = 1 then (hpart c h).choose else 1
    have hχ : ∀ c : C, c ^ n = 1 → ∀ a : A, a ^ n = 1 → rel a c →
        Units.map (i : Ω →* Ω') (χ c) = e' y' a := by
      intro c hc a ha hac
      obtain ⟨a₁, -, hrel, hu⟩ := (hpart c hc).choose_spec
      have : χ c = (hpart c hc).choose := dif_pos hc
      rw [this, hu, hinjA _ _ _ hrel hac]
    obtain ⟨y, hy, hye⟩ := eperf χ (by
      intro g g' hg hg'
      obtain ⟨a, ha, hag⟩ := hCA g hg
      obtain ⟨a', ha', hag'⟩ := hCA g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      have haa : (a * a') ^ n = 1 := by rw [mul_pow, ha, ha', _root_.one_mul]
      apply hinj
      rw [map_mul, hχ _ hgg _ haa (hmul _ _ _ _ hag hag'), hχ _ hg _ ha hag, hχ _ hg' _ ha' hag',
        e'mul y' _ _ hy' ha ha'])
    refine ⟨y, hy, ?_⟩
    intro g g' hg hg' hrel
    rw [← hχ g hg g' hg' hrel, hye g hg]
    rfl
  · intro y hy
    have hpart : ∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c := hAC
    let χ : A → Ω'ˣ := fun a =>
      if h : a ^ n = 1 then Units.map (i : Ω →* Ω') (e y (hpart a h).choose) else 1
    have hχ : ∀ a : A, a ^ n = 1 → ∀ c : C, rel a c →
        χ a = Units.map (i : Ω →* Ω') (e y c) := by
      intro a ha c hac
      have : χ a = Units.map (i : Ω →* Ω') (e y (hpart a ha).choose) := dif_pos ha
      rw [this, hinjC _ _ _ (hpart a ha).choose_spec.2 hac]
    obtain ⟨y', hy', hye⟩ := e'perf χ (by
      intro g g' hg hg'
      obtain ⟨c, hc, hgc⟩ := hAC g hg
      obtain ⟨c', hc', hgc'⟩ := hAC g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      rw [hχ _ hgg _ (hmul _ _ _ _ hgc hgc'), hχ _ hg _ hgc, hχ _ hg' _ hgc',
        emul y _ _ hy hc hc', map_mul])
    refine ⟨y', hy', ?_⟩
    intro g g' hg hg' hrel
    rw [← hye g' hg', hχ g' hg' g hrel]
    rfl

end GlobalTheory.CompanionTheory.Ar.TorsionChars
