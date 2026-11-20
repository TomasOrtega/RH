import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel

open GlobalTheory.PRep Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.CIndGlue

open GlobalTheory.CompanionTheory.PRep.CIndKer

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Set `ev : cIndSpace H ρ →ₗ[ℂ] W` to `(LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype`. Conclude with `map_sum ev _ _`.
-/
theorem sum_apply (H : Subgroup G) (ρ : Representation ℂ H W) {ι : Type} (s : Finset ι)
    (F : ι → cIndSpace H ρ) (g : G) :
    (∑ i ∈ s, F i).1.1.1 g = ∑ i ∈ s, (F i).1.1.1 g := by
  let ev : cIndSpace H ρ →ₗ[ℂ] W :=
    (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ
      (cIndSpace H ρ).subtype
  exact map_sum ev _ _

/- English proof (translation)
Establish `hO : (fun x : G => c⁻¹ * x * c) ⁻¹' (K₁ : Set G) ∈ 𝓝 (1 : G)` using `(hK₁o.preimage (by fun_prop)).mem_nhds (by simp [one_mem])`. Take `⟨K, hKo, hKO, B₀, hB₀, hB1, hB0⟩` from `hloc (y.1.1.1 c) _ hO`. Set `K' : Subgroup G` to `K.comap (MulAut.conj c).toMonoidHom`. Establish `hmem : ∀ x, x ∈ K' ↔ c * x * c⁻¹ ∈ K` using `fun x => Iff.rfl`. Establish `hK'o : IsOpen (K' : Set G)`.

Establish `: Continuous fun x : G => c * x * c⁻¹` using `by fun_prop`. Conclude with `hKo.preimage this`. Establish `hle : K' ≤ K₁`. Introduce `x hx`. Establish `h` using `hKO ((hmem x).1 hx)`.

Establish `e : c⁻¹ * (c * x * c⁻¹) * c = x` using `by group`. Simplify `h` using `[e]`. Use `⟨K', hK'o, hle, cInd H ρ c⁻¹ B₀, hI _ _ hB₀, fun g => ?_⟩` and prove the remaining obligations. Establish `e1 : (cInd H ρ c⁻¹ B₀).1.1.1 g = B₀.1.1.1 (g * c⁻¹)` using `rfl`. Rewrite using `[e1]`.

Distinguish the cases in `hg : g ∈ dc H K' c`. Rewrite using `[Set.indicator_of_mem hg]`. Take `⟨b, k, hk, rfl⟩` from `hg`. Establish `e2 : (b : G) * c * k * c⁻¹ = (b : G) * (c * k * c⁻¹)` using `by group`. Rewrite using `[e2, hB1 b _ ((hmem k).1 hk), mul_assoc, y.1.1.2 b, hy c k (hle hk)]`.

Rewrite using `[Set.indicator_of_notMem hg]`. Apply `hB0` to reduce the goal to its premises. Introduce and unpack `⟨a, x, hx, e⟩`. Apply `hg` to reduce the goal to its premises. Use `⟨a, c⁻¹ * x * c, (hmem _).2 ?_, ?_⟩` and prove the remaining obligations.

Establish `e3 : c * (c⁻¹ * x * c) * c⁻¹ = x` using `by group`. Rewrite using `[e3]`. Conclude with `hx`. Establish `e4 : g = (g * c⁻¹) * c` using `by group`. Rewrite using `[e4, e]`.

Use `group`.
-/
theorem exists_small_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧ ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G) :
    ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ K' ≤ K₁ ∧ ∃ B ∈ I,
      ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g := by
  classical
  have hO : (fun x : G => c⁻¹ * x * c) ⁻¹' (K₁ : Set G) ∈ 𝓝 (1 : G) :=
    (hK₁o.preimage (by fun_prop)).mem_nhds (by simp [one_mem])
  obtain ⟨K, hKo, hKO, B₀, hB₀, hB1, hB0⟩ := hloc (y.1.1.1 c) _ hO
  let K' : Subgroup G := K.comap (MulAut.conj c).toMonoidHom
  have hmem : ∀ x, x ∈ K' ↔ c * x * c⁻¹ ∈ K := fun x => Iff.rfl
  have hK'o : IsOpen (K' : Set G) := by
    have : Continuous fun x : G => c * x * c⁻¹ := by fun_prop
    exact hKo.preimage this
  have hle : K' ≤ K₁ := by
    intro x hx
    have h := hKO ((hmem x).1 hx)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    simpa [e] using h
  refine ⟨K', hK'o, hle, cInd H ρ c⁻¹ B₀, hI _ _ hB₀, fun g => ?_⟩
  have e1 : (cInd H ρ c⁻¹ B₀).1.1.1 g = B₀.1.1.1 (g * c⁻¹) := rfl
  rw [e1]
  by_cases hg : g ∈ dc H K' c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    have e2 : (b : G) * c * k * c⁻¹ = (b : G) * (c * k * c⁻¹) := by group
    rw [e2, hB1 b _ ((hmem k).1 hk), mul_assoc, y.1.1.2 b, hy c k (hle hk)]
  · rw [Set.indicator_of_notMem hg]
    apply hB0
    rintro ⟨a, x, hx, e⟩
    apply hg
    refine ⟨a, c⁻¹ * x * c, (hmem _).2 ?_, ?_⟩
    · have e3 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rw [e3]
      exact hx
    · have e4 : g = (g * c⁻¹) * c := by group
      rw [e4, e]
      group

/- English proof (translation)
Use `haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c`. Set `L : Subgroup K₁` to `K'.subgroupOf K₁`. Establish `hLo : IsOpen (L : Set K₁)` using `hK'o.preimage continuous_subtype_val`. Use `haveI : Finite (K₁ ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hLo`. Use `haveI := Fintype.ofFinite (K₁ ⧸ L)`.

Set `φ : G → ℕ` to `fun g => ∑ q : K₁ ⧸ L, if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0`. Set `Sg : cIndSpace H ρ` to `∑ q : K₁ ⧸ L, cInd H ρ ((q.out : K₁) : G) B`. Establish `hSg : Sg ∈ I` using `Submodule.sum_mem _ fun q _ => hI _ _ hBI`. Establish `hval : ∀ g, Sg.1.1.1 g = (φ g : ℂ) • y.1.1.1 g`. Introduce `g`.

Establish `e0 : Sg.1.1.1 g = ∑ q : K₁ ⧸ L, (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g` using `sum_apply H ρ _ _ g`. Rewrite using `[e0]`. Simplify using `only [φ]`. Use `push_cast`. Rewrite using `[Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `e1 : (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g = B.1.1.1 (g * ((q.out : K₁) : G))` using `rfl`. Rewrite using `[e1, hB]`. Distinguish the cases in `h : g * ((q.out : K₁) : G) ∈ dc H K' c`. Rewrite using `[Set.indicator_of_mem h, hy g _ q.out.2, if_pos h, one_smul]`.

Rewrite using `[Set.indicator_of_notMem h, if_neg h, zero_smul]`. Establish `hleft : ∀ (b : H) g, φ ((b : G) * g) = φ g`. Introduce `b g`. Simplify using `only [φ, mul_assoc, dc_left H K' c (b : G) b.2]`. Establish `hright : ∀ κ ∈ K₁, ∀ g, φ (g * κ) = φ g`.

Introduce `κ hκ g`. Set `κ' : K₁` to `⟨κ, hκ⟩`. Establish `key : ∀ q : K₁ ⧸ L, g * κ * ((q.out : K₁) : G) ∈ dc H K' c ↔ g * (((κ' • q).out : K₁) : G) ∈ dc H K' c`. Introduce `q`. Establish `e : ((κ' * q.out : K₁) : K₁ ⧸ L) = κ' • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q]`.

Both sides reduce to the same expression. Establish `e2 : (κ' • q).out⁻¹ * (κ' * q.out) ∈ L`. Apply `QuotientGroup.eq.1` to reduce the goal to its premises. Rewrite using `[e, QuotientGroup.out_eq']`. Establish `e3 : ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) ∈ K'` using `e2`.

Establish `e4 : g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) * ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G)`. Use `push_cast`. Use `show g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) * ((((κ' • q).out : K₁) : G)⁻¹ * (κ * ((q.out : K₁) : G)))`. Use `group`. Rewrite using `[e4]`.

Conclude with `dc_right H K' c _ e3 _`. Simplify using `only [φ, mul_assoc] at key ⊢`. Simplify using `only [← mul_assoc] at key ⊢`. Simplify using `only [key]`. Conclude with `Equiv.sum_comp (MulAction.toPerm κ') (fun q : K₁ ⧸ L => if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0)`.

Establish `hφc : φ c ≠ 0`. Set `q₀ : K₁ ⧸ L` to `((1 : K₁) : K₁ ⧸ L)`. Establish `h1 : (q₀.out : K₁)⁻¹ * 1 ∈ L`. Apply `QuotientGroup.eq.1` to reduce the goal to its premises. Rewrite using `[QuotientGroup.out_eq']`.

Establish `h2 : (q₀.out : K₁) ∈ L`. Use `inv_mem h1` as an intermediate fact. Simplify using `using this`. Establish `h3 : ((q₀.out : K₁) : G) ∈ K'` using `h2`. Establish `h4 : c * ((q₀.out : K₁) : G) ∈ dc H K' c` using `⟨1, _, h3, by simp⟩`.

Establish `h5 : (if c * ((q₀.out : K₁) : G) ∈ dc H K' c then 1 else 0) ≤ φ c` using `Finset.single_le_sum (f := fun q : K₁ ⧸ L => if c * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q₀)`. Rewrite `h5` using `[if_pos h4]`. Use linear arithmetic over natural numbers and integers. Establish `hoff : ∀ g, g ∉ dc H K₁ c → φ g = 0`. Introduce `g hg`.

Use `Finset.sum_eq_zero fun q _ => if_neg fun h => hg ?_` and prove the remaining obligations. Take `⟨b, k, hk, e⟩` from `h`. Conclude with `(dc_right H K₁ c _ q.out.2 g).1 ⟨b, k, hle hk, e⟩`. Establish `hc0 : (φ c : ℂ) ≠ 0` using `by exact_mod_cast hφc`. Use `⟨(φ c : ℂ)⁻¹ • Sg, Submodule.smul_mem _ _ hSg, fun g => ?_⟩` and prove the remaining obligations.

Establish `e : ((φ c : ℂ)⁻¹ • Sg).1.1.1 g = (φ c : ℂ)⁻¹ • Sg.1.1.1 g` using `rfl`. Rewrite using `[e, hval]`. Distinguish the cases in `hg : g ∈ dc H K₁ c`. Rewrite using `[Set.indicator_of_mem hg]`. Take `⟨b, k, hk, rfl⟩` from `hg`.

Rewrite using `[mul_assoc, hleft, hright k hk, smul_smul, inv_mul_cancel₀ hc0, one_smul, y.1.1.2 b, hy c k hk]`. Rewrite using `[Set.indicator_of_notMem hg, hoff g hg]`. Simplify using the standard rewrite rules.
-/
theorem average_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (K₁ : Subgroup G) (hK₁c : IsCompact (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G)
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hle : K' ≤ K₁)
    (B : cIndSpace H ρ) (hBI : B ∈ I) (hB : ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g) :
    ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
  classical
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c
  let L : Subgroup K₁ := K'.subgroupOf K₁
  have hLo : IsOpen (L : Set K₁) := hK'o.preimage continuous_subtype_val
  haveI : Finite (K₁ ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hLo
  haveI := Fintype.ofFinite (K₁ ⧸ L)
  let φ : G → ℕ := fun g => ∑ q : K₁ ⧸ L, if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0
  let Sg : cIndSpace H ρ := ∑ q : K₁ ⧸ L, cInd H ρ ((q.out : K₁) : G) B
  have hSg : Sg ∈ I := Submodule.sum_mem _ fun q _ => hI _ _ hBI
  have hval : ∀ g, Sg.1.1.1 g = (φ g : ℂ) • y.1.1.1 g := by
    intro g
    have e0 : Sg.1.1.1 g = ∑ q : K₁ ⧸ L, (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g :=
      sum_apply H ρ _ _ g
    rw [e0]
    simp only [φ]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g = B.1.1.1 (g * ((q.out : K₁) : G)) := rfl
    rw [e1, hB]
    by_cases h : g * ((q.out : K₁) : G) ∈ dc H K' c
    · rw [Set.indicator_of_mem h, hy g _ q.out.2, if_pos h, one_smul]
    · rw [Set.indicator_of_notMem h, if_neg h, zero_smul]
  have hleft : ∀ (b : H) g, φ ((b : G) * g) = φ g := by
    intro b g
    simp only [φ, mul_assoc, dc_left H K' c (b : G) b.2]
  have hright : ∀ κ ∈ K₁, ∀ g, φ (g * κ) = φ g := by
    intro κ hκ g
    let κ' : K₁ := ⟨κ, hκ⟩
    have key : ∀ q : K₁ ⧸ L, g * κ * ((q.out : K₁) : G) ∈ dc H K' c ↔
        g * (((κ' • q).out : K₁) : G) ∈ dc H K' c := by
      intro q
      have e : ((κ' * q.out : K₁) : K₁ ⧸ L) = κ' • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have e2 : (κ' • q).out⁻¹ * (κ' * q.out) ∈ L := by
        apply QuotientGroup.eq.1
        rw [e, QuotientGroup.out_eq']
      have e3 : ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) ∈ K' := e2
      have e4 : g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) := by
        push_cast
        show g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out : K₁) : G)⁻¹ * (κ * ((q.out : K₁) : G)))
        group
      rw [e4]
      exact dc_right H K' c _ e3 _
    simp only [φ, mul_assoc] at key ⊢
    simp only [← mul_assoc] at key ⊢
    simp only [key]
    exact Equiv.sum_comp (MulAction.toPerm κ')
      (fun q : K₁ ⧸ L => if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0)
  have hφc : φ c ≠ 0 := by
    let q₀ : K₁ ⧸ L := ((1 : K₁) : K₁ ⧸ L)
    have h1 : (q₀.out : K₁)⁻¹ * 1 ∈ L := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    have h2 : (q₀.out : K₁) ∈ L := by
      have := inv_mem h1
      simpa using this
    have h3 : ((q₀.out : K₁) : G) ∈ K' := h2
    have h4 : c * ((q₀.out : K₁) : G) ∈ dc H K' c := ⟨1, _, h3, by simp⟩
    have h5 : (if c * ((q₀.out : K₁) : G) ∈ dc H K' c then 1 else 0) ≤ φ c :=
      Finset.single_le_sum (f := fun q : K₁ ⧸ L =>
        if c * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q₀)
    rw [if_pos h4] at h5
    omega
  have hoff : ∀ g, g ∉ dc H K₁ c → φ g = 0 := by
    intro g hg
    refine Finset.sum_eq_zero fun q _ => if_neg fun h => hg ?_
    obtain ⟨b, k, hk, e⟩ := h
    exact (dc_right H K₁ c _ q.out.2 g).1 ⟨b, k, hle hk, e⟩
  have hc0 : (φ c : ℂ) ≠ 0 := by exact_mod_cast hφc
  refine ⟨(φ c : ℂ)⁻¹ • Sg, Submodule.smul_mem _ _ hSg, fun g => ?_⟩
  have e : ((φ c : ℂ)⁻¹ • Sg).1.1.1 g = (φ c : ℂ)⁻¹ • Sg.1.1.1 g := rfl
  rw [e, hval]
  by_cases hg : g ∈ dc H K₁ c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    rw [mul_assoc, hleft, hright k hk, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      y.1.1.2 b, hy c k hk]
  · rw [Set.indicator_of_notMem hg, hoff g hg]
    simp

/- English proof (translation)
Introduce `G W _ _ _ _ _ H ρ hbasis I hI hloc y`. Establish `hyo : IsOpen {g : G | ind H ρ g y.1.1 = y.1.1}` using `y.1.2`. Take `⟨K₁, hK₁o, hK₁c, hK₁U⟩` from `hbasis _ (hyo.mem_nhds (by simp))`. Establish `hinv : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g`. Introduce `g x hx`.

Establish `h : ind H ρ x y.1.1 = y.1.1` using `hK₁U hx`. Conclude with `congrArg (fun v : indSpace H ρ => v.1 g) h`. Establish `hdc : ∀ c : G, ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g`. Introduce `c`. Take `⟨K', hK'o, hle, B, hBI, hB⟩` from `exists_small_cut H ρ I hI hloc K₁ hK₁o y hinv c`.

Conclude with `average_cut H ρ I hI K₁ hK₁c y hinv c K' hK'o hle B hBI hB`. Establish `key : ∀ t : Finset G, ∃ S : Set G, (∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S) ∧ (∀ k ∈ K₁, ∀ g, g * k ∈ S ↔ g ∈ S) ∧ (∀ c ∈ t, c ∈ S) ∧ ∃ z ∈ I, ∀ g, z.1.1.1 g = S.indicator y.1.1.1 g`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Conclude with `⟨∅, by simp, by simp, by simp, 0, Submodule.zero_mem _, fun g => by simp⟩`. Consider the case `insert c t _ ih`. Take `⟨S, hl, hr, hcov, z, hz, ez⟩` from `ih`. Distinguish the cases in `hcS : c ∈ S`. Use `⟨S, hl, hr, fun c' hc' => ?_, z, hz, ez⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hc' with rfl | hc'` into its components or cases. Conclude with `hcS`. Conclude with `hcov c' hc'`. Take `⟨z', hz', ez'⟩` from `hdc c`. Establish `hdisj : ∀ g, g ∈ dc H K₁ c → g ∉ S`.

Introduce and unpack `g ⟨b, k, hk, rfl⟩ hg`. Rewrite `hg` using `[mul_assoc, hl _ b.2, hr k hk]`. Conclude with `hcS hg`. Use `⟨S ∪ dc H K₁ c, fun h hh g => ?_, fun k hk g => ?_, fun c' hc' => ?_, z + z', Submodule.add_mem _ hz hz', fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_union, hl h hh g, dc_left H K₁ c h hh g]`.

Simplify using `only [Set.mem_union, hr k hk g, dc_right H K₁ c k hk g]`. Break down `Finset.mem_insert.1 hc' with rfl | hc'` into its components or cases. Conclude with `Or.inr ⟨1, 1, one_mem _, by simp⟩`. Conclude with `Or.inl (hcov c' hc')`. Establish `e : (z + z').1.1.1 g = z.1.1.1 g + z'.1.1.1 g` using `rfl`.

Rewrite using `[e, ez, ez']`. Distinguish the cases in `h2 : g ∈ dc H K₁ c`. Establish `h1` using `hdisj g h2`. Simplify using `[Set.indicator, h1, h2]`. Apply the tactic sequence `by_cases h1 : g ∈ S <;> simp [Set.indicator, h1, h2]`.

Take `⟨C, hC, hsupp⟩` from `y.2`. Take `⟨t, -, ht⟩` from `hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K₁ : Set G)) (fun c _ => by`. Establish `: (fun x => c⁻¹ * x) ⁻¹' (K₁ : Set G) ∈ 𝓝 c` using `(hK₁o.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])`. Use `filter_upwards [this] with x hx`. Conclude with `⟨c⁻¹ * x, hx, by group⟩)`.

Take `⟨S, hl, hr, hcov, z, hz, ez⟩` from `key t`. Establish `hyz : y = z`. Use `Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))` and prove the remaining obligations. Use `show y.1.1.1 g = z.1.1.1 g`. Rewrite using `[ez]`.

Distinguish the cases in `h0 : y.1.1.1 g = 0`. Rewrite using `[h0]`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg, h0]`. Rewrite using `[Set.indicator_of_notMem hg]`.

Take `⟨a, ha, c', hc', e⟩` from `hsupp g h0`. Take `⟨c, hc, hcc⟩` from `Set.mem_iUnion₂.1 (ht hc')`. Take `⟨x, hx, rfl⟩` from `hcc`. Establish `hg : g ∈ S`. Rewrite using `[e]`.

Conclude with `(hl a ha _).2 ((hr x hx c).2 (hcov c hc))`. Rewrite using `[Set.indicator_of_mem hg]`. Rewrite using `[hyz]`. Conclude with `hz`.
-/
theorem eq_top_of_bumps : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W)
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧
      ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (y : cIndSpace H ρ), y ∈ I := by
  intro G W _ _ _ _ _ H ρ hbasis I hI hloc y
  classical
  have hyo : IsOpen {g : G | ind H ρ g y.1.1 = y.1.1} := y.1.2
  obtain ⟨K₁, hK₁o, hK₁c, hK₁U⟩ := hbasis _ (hyo.mem_nhds (by simp))
  have hinv : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g := by
    intro g x hx
    have h : ind H ρ x y.1.1 = y.1.1 := hK₁U hx
    exact congrArg (fun v : indSpace H ρ => v.1 g) h
  have hdc : ∀ c : G, ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
    intro c
    obtain ⟨K', hK'o, hle, B, hBI, hB⟩ := exists_small_cut H ρ I hI hloc K₁ hK₁o y hinv c
    exact average_cut H ρ I hI K₁ hK₁c y hinv c K' hK'o hle B hBI hB
  have key : ∀ t : Finset G, ∃ S : Set G, (∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S) ∧
      (∀ k ∈ K₁, ∀ g, g * k ∈ S ↔ g ∈ S) ∧ (∀ c ∈ t, c ∈ S) ∧
      ∃ z ∈ I, ∀ g, z.1.1.1 g = S.indicator y.1.1.1 g := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨∅, by simp, by simp, by simp, 0, Submodule.zero_mem _, fun g => by simp⟩
    | insert c t _ ih =>
      obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := ih
      by_cases hcS : c ∈ S
      · refine ⟨S, hl, hr, fun c' hc' => ?_, z, hz, ez⟩
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hcS
        · exact hcov c' hc'
      · obtain ⟨z', hz', ez'⟩ := hdc c
        have hdisj : ∀ g, g ∈ dc H K₁ c → g ∉ S := by
          rintro g ⟨b, k, hk, rfl⟩ hg
          rw [mul_assoc, hl _ b.2, hr k hk] at hg
          exact hcS hg
        refine ⟨S ∪ dc H K₁ c, fun h hh g => ?_, fun k hk g => ?_, fun c' hc' => ?_, z + z',
          Submodule.add_mem _ hz hz', fun g => ?_⟩
        · simp only [Set.mem_union, hl h hh g, dc_left H K₁ c h hh g]
        · simp only [Set.mem_union, hr k hk g, dc_right H K₁ c k hk g]
        · rcases Finset.mem_insert.1 hc' with rfl | hc'
          · exact Or.inr ⟨1, 1, one_mem _, by simp⟩
          · exact Or.inl (hcov c' hc')
        · have e : (z + z').1.1.1 g = z.1.1.1 g + z'.1.1.1 g := rfl
          rw [e, ez, ez']
          by_cases h2 : g ∈ dc H K₁ c
          · have h1 := hdisj g h2
            simp [Set.indicator, h1, h2]
          · by_cases h1 : g ∈ S <;> simp [Set.indicator, h1, h2]
  obtain ⟨C, hC, hsupp⟩ := y.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K₁ : Set G))
    (fun c _ => by
      have : (fun x => c⁻¹ * x) ⁻¹' (K₁ : Set G) ∈ 𝓝 c :=
        (hK₁o.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
      filter_upwards [this] with x hx
      exact ⟨c⁻¹ * x, hx, by group⟩)
  obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := key t
  have hyz : y = z := by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    show y.1.1.1 g = z.1.1.1 g
    rw [ez]
    by_cases h0 : y.1.1.1 g = 0
    · rw [h0]
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, h0]
      · rw [Set.indicator_of_notMem hg]
    · obtain ⟨a, ha, c', hc', e⟩ := hsupp g h0
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      have hg : g ∈ S := by
        rw [e]
        exact (hl a ha _).2 ((hr x hx c).2 (hcov c hc))
      rw [Set.indicator_of_mem hg]
  rw [hyz]
  exact hz

end GlobalTheory.CompanionTheory.PRep.CIndGlue
