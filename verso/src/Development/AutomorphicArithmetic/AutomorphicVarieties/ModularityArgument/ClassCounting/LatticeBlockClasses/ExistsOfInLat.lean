import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J : Type}

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
-/
private theorem coe_add' (y y' : J → 𝓞 F) :
    (fun j => ((y + y') j : F)) = (fun j => (y j : F)) + fun j => (y' j : F) := by
  funext j
  simp

end

/- English proof (translation)
Introduce `L F _ _ _ _ _ J _ b`. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : Module.FinitePresentation (𝓞 L) (J → 𝓞 F) := Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`. Establish `hadd : ∀ u w : 𝓞 F, ((u + w : 𝓞 F) : F) = (u : F) + (w : F)` using `fun u w => by simp`.

Establish `hmul : ∀ u w : 𝓞 F, ((u * w : 𝓞 F) : F) = (u : F) * (w : F)` using `fun u w => by simp`. Establish `hone1 : ((1 : 𝓞 F) : F) = 1` using `by simp`. Establish `hint : ∀ y : J → F, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔ ∀ j, ∃ a : 𝓞 F, (a : F) = y j`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy j`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y j) (fun P => by simpa using hy j P)`. Conclude with `⟨a, ha⟩`. Introduce `hy j P`. Take `⟨a, ha⟩` from `hy j`.

Rewrite using `[← ha]`. Simplify using `using HeightOneSpectrum.valuation_le_one (K := F) P a`. Set `φ : GG L F J → (J → 𝓞 F) → (J → 𝓞 F)` to `fun g x j => if hx : ∃ a : 𝓞 F, (a : F) = g (fun i => (x i : F)) j then hx.choose else 0`. Establish `hφ : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x j, ((φ g x j : 𝓞 F) : F) = g (fun i => (x i : F)) j`. Introduce `g hg x j`.

Establish `hg' : ∀ y, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔ InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (g y)` using `hg`. Establish `h1 : InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (fun i => (x i : F))` using `(hint _).2 (fun i => ⟨x i, rfl⟩)`. Establish `h2` using `(hint _).1 ((hg' _).1 h1) j`. Simplify using `only [φ, dif_pos h2]`. Conclude with `h2.choose_spec`.

Establish `hφf : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x, (fun i => ((φ g x i : 𝓞 F) : F)) = g (fun i => (x i : F))` using `fun g hg x => funext (hφ g hg x)`. Establish `hcomp : ∀ g1 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ g2 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x, φ g1 (φ g2 x) = φ (g1 * g2) x`. Introduce `g1 hg1 g2 hg2 x`. Use function extensionality and compare the values at `j`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hφ g1 hg1, hφf g2 hg2, hφ _ (Subgroup.mul_mem _ hg1 hg2)]`. Both sides reduce to the same expression. Establish `hone : ∀ x, φ 1 x = x`. Introduce `x`. Use function extensionality and compare the values at `j`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hφ 1 (Subgroup.one_mem _)]`. Both sides reduce to the same expression. Establish `hsmul : ∀ (a : 𝓞 L) (z : 𝓞 F), ((a • z : 𝓞 F) : F) = (a : L) • (z : F)`. Introduce `a z`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `hlin : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x y, φ g (x + y) = φ g x + φ g y ∧ ∀ a : 𝓞 L, φ g (a • x) = a • φ g x`. Introduce `g hg x y`. Prove the components needed by the constructor for the conclusion.

Use function extensionality and compare the values at `j`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[Pi.add_apply, hadd, hφ g hg, hφ g hg, hφ g hg, coe_add', map_add, Pi.add_apply]`. Introduce `a`. Use function extensionality and compare the values at `j`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `e : (fun i => ((a • x) i : F)) = (a : L) • fun i => (x i : F)`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, hsmul]`. Rewrite using `[Pi.smul_apply, hsmul, hφ g hg, hφ g hg, e, map_smul, Pi.smul_apply]`.

Set `E : ∀ g : GG L F J, g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)) → ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F)` to `fun g hg => { toFun := φ g invFun := φ g⁻¹ map_add' := fun x y => (hlin g hg x y).1 map_smul' := fun a x => (hlin g hg x x).2 a left_inv := by`. Introduce `x`. Use `show φ g⁻¹ (φ g x) = x`. Rewrite using `[hcomp _ (Subgroup.inv_mem _ hg) _ hg, inv_mul_cancel, hone]`. Use `right_inv := by`.

Introduce `x`. Use `show φ g (φ g⁻¹ x) = x`. Rewrite using `[hcomp _ hg _ (Subgroup.inv_mem _ hg), mul_inv_cancel, hone] }`. Set `α : ↥((StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf (GLoc F J b)) →* ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F)` to `{ toFun := fun h => E _ (Subgroup.mem_subgroupOf.1 h.2) map_one' := by`. Apply `LinearEquiv.ext` to reduce the goal to its premises.

Introduce `x`. Conclude with `hone x`. Use the proof step `map_mul' := by`. Introduce `h1 h2`. Apply `LinearEquiv.ext` to reduce the goal to its premises.

Introduce `x`. Conclude with `(hcomp _ (Subgroup.mem_subgroupOf.1 h1.2) _ (Subgroup.mem_subgroupOf.1 h2.2) x).symm }`. Use `⟨α, ?_⟩` and prove the remaining obligations. Introduce `k _ r hr μ hμ`. Establish `hfix : ∀ (σ : Gal(F/L)) (a : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) a) = algebraMap (𝓞 L) (𝓞 F) a`.

Introduce `σ a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show σ ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F)`. Establish `e : ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = algebraMap L F (a : L)`. Use `hsmul a 1` as an intermediate fact.

Simplify `this` using `[Algebra.smul_def]`. Rewrite using `[e]`. Conclude with `σ.commutes _`. Set `π : (J → 𝓞 F) →+ (Gal(F/L) × J → k)` to `{ toFun := fun x p => r (actO p.1 (x p.2)) map_zero' := by`. Use function extensionality and compare the values at `p`.

Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `x y`. Use function extensionality and compare the values at `p`. Simplify using `}`.

Establish `huniq : ∀ (y : F) (u u' : k), ResF r y u → ResF r y u' → u = u'`. Introduce and unpack `y u u' ⟨a, c, hc, hyc, hu⟩ ⟨a', c', hc', hyc', hu'⟩`. Establish `e : a * c' = a' * c`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hmul, hmul, ← hyc, ← hyc']`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `congrArg r e`. Rewrite `e2` using `[map_mul, map_mul, hu, hu']`. Establish `hcc : r c * r c' ≠ 0` using `mul_ne_zero hc hc'`. Apply `mul_right_cancel₀ hcc` to reduce the goal to its premises.

Take the linear combination `e2`. Establish `hR : ∀ z : J → 𝓞 F, RedV L r (fun i => (z i : F)) (π z)`. Introduce `z σ j`. Use `⟨actO σ (z j), 1, by simp, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hone1, mul_one]`.

Both sides reduce to the same expression. Use `show r (actO σ (z j)) = r (actO σ (z j)) * r 1`. Rewrite using `[map_one, mul_one]`. Use `⟨π, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a x`.

Use function extensionality and compare the values at `p`. Use `show r (actO p.1 ((a • x) p.2)) = (r.comp (algebraMap (𝓞 L) (𝓞 F))) a • r (actO p.1 (x p.2))`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hfix, smul_eq_mul]`. Both sides reduce to the same expression. Introduce `v choose a ha using fun j => hr.1 (fun σ => v (σ, j))`.

Conclude with `⟨a, funext fun p => ha p.2 p.1⟩`. Introduce `x hx`. Establish `hj : ∀ j, x j ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F))))` using `fun j => hr.2 (x j) (fun σ => congrFun hx (σ, j))`. Rewrite using `[← Finset.univ_sum_single x]`. Apply `Submodule.sum_mem` to reduce the goal to its premises.

Introduce `j _`. Establish `h1 : x j ∈ ((RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) • ⊤ : Submodule (𝓞 L) (𝓞 F))`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hj j`. Establish `h2` using `Submodule.mem_map_of_mem (f := LinearMap.single (𝓞 L) (fun _ : J => 𝓞 F) j) h1`.

Rewrite `h2` using `[Submodule.map_smul'', LinearMap.single_apply]`. Conclude with `Submodule.smul_mono le_rfl le_top h2`. Introduce `h x`. Use function extensionality and compare the values at `p`. Establish `hloc : InLoc b (fun i => (x i : F))`.

Introduce `j P _`. Conclude with `HeightOneSpectrum.valuation_le_one (K := F) P (x j)`. Establish `hred` using `hμ (h : ↥(GLoc F J b)) (fun i => (x i : F)) (π x) hloc (hR x)`. Establish `hα` using `hR (α h x)`. Establish `hc : (fun i => ((α h x i : 𝓞 F) : F)) = ((h : ↥(GLoc F J b)) : GG L F J) (fun i => (x i : F))` using `hφf _ (Subgroup.mem_subgroupOf.1 h.2) x`.

Rewrite `hα` using `[hc]`. Conclude with `huniq _ _ _ (hα p.1 p.2) (hred p.1 p.2)`.
-/
theorem UpperTheory.V.ZK.Cl.cInt :
    UpperTheory.V.ZK.Cl.CInt := by
  intro L F _ _ _ _ _ J _ b
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · haveI : Module.FinitePresentation (𝓞 L) (J → 𝓞 F) := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hadd : ∀ u w : 𝓞 F, ((u + w : 𝓞 F) : F) = (u : F) + (w : F) := fun u w => by simp
  have hmul : ∀ u w : 𝓞 F, ((u * w : 𝓞 F) : F) = (u : F) * (w : F) := fun u w => by simp
  have hone1 : ((1 : 𝓞 F) : F) = 1 := by simp
  have hint : ∀ y : J → F, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔ ∀ j, ∃ a : 𝓞 F, (a : F) = y j := by
    intro y
    constructor
    · intro hy j
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y j)
        (fun P => by simpa using hy j P)
      exact ⟨a, ha⟩
    · intro hy j P
      obtain ⟨a, ha⟩ := hy j
      rw [← ha]
      simpa using HeightOneSpectrum.valuation_le_one (K := F) P a
  let φ : GG L F J → (J → 𝓞 F) → (J → 𝓞 F) := fun g x j =>
    if hx : ∃ a : 𝓞 F, (a : F) = g (fun i => (x i : F)) j then hx.choose else 0
  have hφ : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x j,
      ((φ g x j : 𝓞 F) : F) = g (fun i => (x i : F)) j := by
    intro g hg x j
    have hg' : ∀ y, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔
        InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (g y) := hg
    have h1 : InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (fun i => (x i : F)) :=
      (hint _).2 (fun i => ⟨x i, rfl⟩)
    have h2 := (hint _).1 ((hg' _).1 h1) j
    simp only [φ, dif_pos h2]
    exact h2.choose_spec
  have hφf : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x,
      (fun i => ((φ g x i : 𝓞 F) : F)) = g (fun i => (x i : F)) := fun g hg x => funext (hφ g hg x)
  have hcomp : ∀ g1 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)),
      ∀ g2 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x, φ g1 (φ g2 x) = φ (g1 * g2) x := by
    intro g1 hg1 g2 hg2 x
    funext j
    apply RingOfIntegers.ext
    rw [hφ g1 hg1, hφf g2 hg2, hφ _ (Subgroup.mul_mem _ hg1 hg2)]
    rfl
  have hone : ∀ x, φ 1 x = x := by
    intro x
    funext j
    apply RingOfIntegers.ext
    rw [hφ 1 (Subgroup.one_mem _)]
    rfl
  have hsmul : ∀ (a : 𝓞 L) (z : 𝓞 F), ((a • z : 𝓞 F) : F) = (a : L) • (z : F) := by
    intro a z
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hlin : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x y,
      φ g (x + y) = φ g x + φ g y ∧ ∀ a : 𝓞 L, φ g (a • x) = a • φ g x := by
    intro g hg x y
    constructor
    · funext j
      apply RingOfIntegers.ext
      rw [Pi.add_apply, hadd, hφ g hg, hφ g hg, hφ g hg, coe_add', map_add, Pi.add_apply]
    · intro a
      funext j
      apply RingOfIntegers.ext
      have e : (fun i => ((a • x) i : F)) = (a : L) • fun i => (x i : F) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, hsmul]
      rw [Pi.smul_apply, hsmul, hφ g hg, hφ g hg, e, map_smul, Pi.smul_apply]
  let E : ∀ g : GG L F J, g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)) →
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) := fun g hg =>
    { toFun := φ g
      invFun := φ g⁻¹
      map_add' := fun x y => (hlin g hg x y).1
      map_smul' := fun a x => (hlin g hg x x).2 a
      left_inv := by
        intro x
        show φ g⁻¹ (φ g x) = x
        rw [hcomp _ (Subgroup.inv_mem _ hg) _ hg, inv_mul_cancel, hone]
      right_inv := by
        intro x
        show φ g (φ g⁻¹ x) = x
        rw [hcomp _ hg _ (Subgroup.inv_mem _ hg), mul_inv_cancel, hone] }
  let α : ↥((StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf (GLoc F J b)) →*
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) :=
    { toFun := fun h => E _ (Subgroup.mem_subgroupOf.1 h.2)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        exact hone x
      map_mul' := by
        intro h1 h2
        apply LinearEquiv.ext
        intro x
        exact (hcomp _ (Subgroup.mem_subgroupOf.1 h1.2) _ (Subgroup.mem_subgroupOf.1 h2.2) x).symm }
  refine ⟨α, ?_⟩
  intro k _ r hr μ hμ
  have hfix : ∀ (σ : Gal(F/L)) (a : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) a) = algebraMap (𝓞 L) (𝓞 F) a := by
    intro σ a
    apply RingOfIntegers.ext
    show σ ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F)
    have e : ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = algebraMap L F (a : L) := by
      have := hsmul a 1
      simpa [Algebra.smul_def] using this
    rw [e]
    exact σ.commutes _
  let π : (J → 𝓞 F) →+ (Gal(F/L) × J → k) :=
    { toFun := fun x p => r (actO p.1 (x p.2))
      map_zero' := by
        funext p
        simp
      map_add' := by
        intro x y
        funext p
        simp }
  have huniq : ∀ (y : F) (u u' : k), ResF r y u → ResF r y u' → u = u' := by
    rintro y u u' ⟨a, c, hc, hyc, hu⟩ ⟨a', c', hc', hyc', hu'⟩
    have e : a * c' = a' * c := by
      apply RingOfIntegers.ext
      rw [hmul, hmul, ← hyc, ← hyc']
      ring
    have e2 := congrArg r e
    rw [map_mul, map_mul, hu, hu'] at e2
    have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
    apply mul_right_cancel₀ hcc
    linear_combination e2
  have hR : ∀ z : J → 𝓞 F, RedV L r (fun i => (z i : F)) (π z) := by
    intro z σ j
    refine ⟨actO σ (z j), 1, by simp, ?_, ?_⟩
    · rw [hone1, mul_one]
      rfl
    · show r (actO σ (z j)) = r (actO σ (z j)) * r 1
      rw [map_one, mul_one]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · intro a x
    funext p
    show r (actO p.1 ((a • x) p.2)) = (r.comp (algebraMap (𝓞 L) (𝓞 F))) a • r (actO p.1 (x p.2))
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hfix, smul_eq_mul]
    rfl
  · intro v
    choose a ha using fun j => hr.1 (fun σ => v (σ, j))
    exact ⟨a, funext fun p => ha p.2 p.1⟩
  · intro x hx
    have hj : ∀ j, x j ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) :=
      fun j => hr.2 (x j) (fun σ => congrFun hx (σ, j))
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro j _
    have h1 : x j ∈ ((RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) • ⊤ : Submodule (𝓞 L) (𝓞 F)) := by
      rw [Ideal.smul_top_eq_map]
      exact hj j
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single (𝓞 L) (fun _ : J => 𝓞 F) j) h1
    rw [Submodule.map_smul'', LinearMap.single_apply] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  · intro h x
    funext p
    have hloc : InLoc b (fun i => (x i : F)) := by
      intro j P _
      exact HeightOneSpectrum.valuation_le_one (K := F) P (x j)
    have hred := hμ (h : ↥(GLoc F J b)) (fun i => (x i : F)) (π x) hloc (hR x)
    have hα := hR (α h x)
    have hc : (fun i => ((α h x i : 𝓞 F) : F)) = ((h : ↥(GLoc F J b)) : GG L F J) (fun i => (x i : F)) :=
      hφf _ (Subgroup.mem_subgroupOf.1 h.2) x
    rw [hc] at hα
    exact huniq _ _ _ (hα p.1 p.2) (hred p.1 p.2)
