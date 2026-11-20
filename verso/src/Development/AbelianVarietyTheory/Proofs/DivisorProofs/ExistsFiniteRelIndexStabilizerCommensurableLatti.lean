import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

def sqMul (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.map ((((n : E) ^ 2) • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E))

/- English proof (translation)
Simplify using `[sqMul]`.
-/
theorem mem_sqMul {Λ : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} {x : Fin r → E} :
    x ∈ sqMul Λ n ↔ ∃ y ∈ Λ, ((n : E) ^ 2) • y = x := by
  simp [sqMul]

def sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) Λ :=
  Submodule.comap Λ.subtype (sqMul Λ n)

def act (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) : Λ →ₗ[𝓞 E] Λ :=
  ((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)).restrict
    fun x hx => (h x).1 hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem act_apply (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) (x : Λ) :
    ((act Λ γ h x : Λ) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E).mulVec x := rfl

/- English proof (translation)
Introduce `x hx`. Simplify using `only [sqSub, Submodule.mem_comap, Submodule.subtype_apply, act_apply] at hx ⊢`. Take `⟨y, hy, hxy⟩` from `mem_sqMul.1 hx`. Conclude with `mem_sqMul.2 ⟨_, (h y).1 hy, by rw [← hxy, Matrix.mulVec_smul]⟩`.
-/
theorem act_sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    sqSub Λ n ≤ (sqSub Λ n).comap (act Λ γ h) := by
  intro x hx
  simp only [sqSub, Submodule.mem_comap, Submodule.subtype_apply, act_apply] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := mem_sqMul.1 hx
  exact mem_sqMul.2 ⟨_, (h y).1 hy, by rw [← hxy, Matrix.mulVec_smul]⟩

def rep (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (G : Subgroup (GL (Fin r) E))
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    G →* Module.End (𝓞 E) (Λ ⧸ sqSub Λ n) where
  toFun g := (sqSub Λ n).mapQ (sqSub Λ n) (act Λ g (hG g g.2)) (act_sqSub Λ n _ _)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp]
    congr 1
    ext
    simp
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Module.End.mul_apply]
    congr 1
    ext
    simp [Matrix.mulVec_mulVec]

end GlobalTheory.LatticeCongr

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

/- English proof (translation)
Establish `hu : (Submodule.Quotient.mk (act Λ g (hG g g.2) ⟨(n : E) • x, h1 x hx⟩) : Λ ⧸ sqSub Λ n) = Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩` using `LinearMap.congr_fun hg (Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩)`. Rewrite `hu` using `[Submodule.Quotient.eq]`. Take `⟨y, hy, hyx⟩` from `mem_sqMul.1 hu`. Express the relevant statement in the definitionally equal form `((n : E) ^ 2) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec ((n : E) • x) - (n : E) • x at hyx`. Rewrite `hyx` using `[Matrix.mulVec_smul]`.

Establish `hn' : (n : E) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hy' : (n : E) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x - x`. Apply `smul_right_injective _ hn'` to reduce the goal to its premises. Simplify using `only [smul_smul, smul_sub, ← pow_two]`. Conclude with `hyx`.

Establish `: ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x = x + (n : E) • y`. Rewrite using `[hy']`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Λ'.add_mem hx (h2 y hy)`.
-/
theorem mulVec_mem_of_rep_eq_one {Λ Λ' : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} (hn : 0 < n)
    (h1 : ∀ v ∈ Λ', (n : E) • v ∈ Λ) (h2 : ∀ v ∈ Λ, (n : E) • v ∈ Λ')
    {G : Subgroup (GL (Fin r) E)}
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ)
    (g : G) (hg : rep Λ n G hG g = 1) (x : Fin r → E) (hx : x ∈ Λ') :
    ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  have hu : (Submodule.Quotient.mk (act Λ g (hG g g.2) ⟨(n : E) • x, h1 x hx⟩) : Λ ⧸ sqSub Λ n) =
      Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩ :=
    LinearMap.congr_fun hg (Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩)
  rw [Submodule.Quotient.eq] at hu
  obtain ⟨y, hy, hyx⟩ := mem_sqMul.1 hu
  change ((n : E) ^ 2) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec ((n : E) • x) -
    (n : E) • x at hyx
  rw [Matrix.mulVec_smul] at hyx
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hy' : (n : E) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x - x := by
    apply smul_right_injective _ hn'
    simp only [smul_smul, smul_sub, ← pow_two]
    exact hyx
  have : ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x = x + (n : E) • y := by
    rw [hy']; abel
  rw [this]
  exact Λ'.add_mem hx (h2 y hy)

/- English proof (translation)
Introduce `E _ _ r Λ Λ' n hn hfg h1 h2 G hG`. Use `haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg`. Use `haveI : Module.Finite ℤ (Λ ⧸ sqSub Λ n) := Module.Finite.trans (𝓞 E) _`. Use `haveI : Finite (Λ ⧸ sqSub Λ n) := Module.finite_of_fg_torsion _ fun z => by`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Use `⟨⟨((n : ℤ) ^ 2), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((n : ℤ) ^ 2) • (Submodule.mkQ (sqSub Λ n) y) = 0`. Rewrite using `[← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `show (((((n : ℤ) ^ 2) • y : Λ)) : Fin r → E) ∈ sqMul Λ n`. Use `mem_sqMul.2 ⟨y, y.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul E]`. Use `push_cast`. Both sides reduce to the same expression. Use `haveI : Finite (Module.End (𝓞 E) (Λ ⧸ sqSub Λ n)) := Finite.of_injective _ DFunLike.coe_injective`. Use `set φ := (rep Λ n G hG).toHomUnits with hφ`.

Establish `key : ∀ γ ∈ φ.ker.map G.subtype, ∀ x ∈ Λ', (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ'`. Introduce and unpack `γ ⟨g, hg, rfl⟩ x hx`. Use `mulVec_mem_of_rep_eq_one hn h1 h2 hG g ?_ x hx` and prove the remaining obligations. Use `congrArg Units.val (MonoidHom.mem_ker.1 hg)` as an intermediate fact. Simplify `this` using `[hφ]`.

Use `⟨φ.ker.map G.subtype, ?_, ?_⟩` and prove the remaining obligations. Use `show (Subgroup.comap G.subtype (φ.ker.map G.subtype)).index ≠ 0`. Rewrite using `[Subgroup.comap_map_eq_self_of_injective G.subtype_injective]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`. Introduce `γ hγ x`.

Use `⟨key γ hγ x, fun h => ?_⟩` and prove the remaining obligations. Use `key γ⁻¹ (inv_mem hγ) _ h` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem exists_relIndex_ne_zero_stab : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ), 0 < n → Λ.FG → (∀ v ∈ Λ', (n : E) • v ∈ Λ) → (∀ v ∈ Λ, (n : E) • v ∈ Λ') → ∀ G : Subgroup (GL (Fin r) E), (∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) → ∃ K : Subgroup (GL (Fin r) E), K.relIndex G ≠ 0 ∧ ∀ γ ∈ K, ∀ x, x ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  intro E _ _ r Λ Λ' n hn hfg h1 h2 G hG
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (Λ ⧸ sqSub Λ n) := Module.Finite.trans (𝓞 E) _
  haveI : Finite (Λ ⧸ sqSub Λ n) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨⟨((n : ℤ) ^ 2), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((n : ℤ) ^ 2) • (Submodule.mkQ (sqSub Λ n) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (((((n : ℤ) ^ 2) • y : Λ)) : Fin r → E) ∈ sqMul Λ n
    refine mem_sqMul.2 ⟨y, y.2, ?_⟩
    rw [AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul E]
    push_cast
    rfl
  haveI : Finite (Module.End (𝓞 E) (Λ ⧸ sqSub Λ n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  set φ := (rep Λ n G hG).toHomUnits with hφ
  have key : ∀ γ ∈ φ.ker.map G.subtype, ∀ x ∈ Λ',
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
    rintro γ ⟨g, hg, rfl⟩ x hx
    refine mulVec_mem_of_rep_eq_one hn h1 h2 hG g ?_ x hx
    have := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    simpa [hφ] using this
  refine ⟨φ.ker.map G.subtype, ?_, ?_⟩
  · show (Subgroup.comap G.subtype (φ.ker.map G.subtype)).index ≠ 0
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
    exact Subgroup.FiniteIndex.index_ne_zero
  · intro γ hγ x
    refine ⟨key γ hγ x, fun h => ?_⟩
    have := key γ⁻¹ (inv_mem hγ) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this

end GlobalTheory.LatticeCongr
