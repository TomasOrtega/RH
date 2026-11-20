import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Take `⟨b, hbM, -, hsp, hli⟩` from `exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)`. Set `bb` to `Basis.extend hli`. Set `f : V → W` to `fun x => if h : x ∈ M then g ⟨x, h⟩ else 0`. Set `G : V →ₗ[K] W` to `bb.constr K fun i => f i.1`. Establish `hGb : ∀ x ∈ b, G x = f x` using `fun x hx => by`.

Establish `hx' : x ∈ hli.extend (Set.subset_univ b)` using `hli.subset_extend _ hx`. Use `bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩` as an intermediate fact. Simplify `this` using `[bb, G, Basis.extend_apply_self]`. Establish `hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `h`. Rewrite using `[hGb x hx]`. Simplify using `[f, h]`.

Consider the case `zero`. Introduce `h`. Establish `: (⟨0, h⟩ : M) = 0` using `rfl`. Rewrite using `[this, map_zero, map_zero]`. Consider the case `add x y hx hy ihx ihy`.

Introduce `h`. Establish `h1 : x ∈ M` using `Submodule.span_le.2 hbM hx`. Establish `h2 : y ∈ M` using `Submodule.span_le.2 hbM hy`. Establish `: (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩` using `rfl`. Rewrite using `[map_add, ihx h1, ihy h2, this, map_add]`.

Consider the case `smul a x hx ih`. Introduce `h`. Establish `h1 : x ∈ M` using `Submodule.span_le.2 hbM hx`. Establish `: (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩` using `rfl`. Rewrite using `[this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]`.

Establish `hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b`. Introduce `v hv`. Establish `hinj` using `IsFractionRing.injective A K`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩`.

Consider the case `zero => exact ⟨1, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨a', ha', hy⟩` from `hy`. Use `⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem _ _ hy`. Consider the case `smul r x _ hx`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨u, v, hv, rfl⟩` from `IsFractionRing.div_surjective (A := A) r`. Establish `hv0 : algebraMap A K v ≠ 0` using `(map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)`.

Use `⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩` and prove the remaining obligations. Establish `: (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x`. Rewrite using `[← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `⟨G, fun z => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, haz⟩` from `hden z (hsp z.2)`. Establish `h1` using `hG _ haz (M.smul_mem a z.2)`.

Establish `h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z` using `rfl`. Rewrite `h1` using `[h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)]`. Conclude with `smul_right_injective W ha h1`.
-/
theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add, ihx h1, ihy h2, this, map_add]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

/- English proof (translation)
Use extensionality with `v`. Simplify using `[eigProj, LinearMap.sum_apply, hact]`.
-/
theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

/- English proof (translation)
Rewrite using `[eigProj_dual D ρ hact, LinearMap.comp_apply]`. Use `congr 1`. Establish `h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e` using `fun a => by`. Rewrite using `[LatBasic.mem_eigSp.1 he]`. Simplify using `[hc]`.

Establish `h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e`. Apply `LatBasic.eigProj_of_mem` to reduce the goal to its premises. Rewrite using `[LatBasic.mem_eigSp]`. Conclude with `fun a => h1 a`. Conclude with `h2`.
-/
theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

/- English proof (translation)
Use `haveI : Module.Finite K (Module.Dual K Li) := by`. Take `⟨S, hS⟩` from `D.om_lat.fg`. Use `⟨⟨S, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← D.om_lat.span_eq_top, ← hS, Submodule.span_span_of_tower]`. Use `haveI : Module.Finite K Li := (Module.finite_dual_iff K).1 inferInstance`.

Take `⟨G, hG⟩` from `exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)`. Set `v : Li` to `(Module.evalEquiv K Li).symm G`. Establish `hv : ∀ w : Module.Dual K Li, w v = G w` using `fun w => by`. Simplify `Module.apply_evalEquiv_symm_apply w G` using `[v]`. Use `⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v`. Rewrite `h`, the goal using `[LatBasic.mem_eigSp]`. Introduce `a`. Establish `hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using `[hc]`. Use `h (RingOfIntegers.mapRingEquiv c a)` as an intermediate fact. Simplify `this` using `[hinv]`. Introduce `z`. Take `⟨w, hw, hz⟩` from `z.2`.

Establish `hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li)` using `hz`. Establish `he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)`. Establish `h` using `LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v`. Rewrite `h`, the goal using `[LatBasic.mem_eigSp]`. Introduce `a`.

Establish `hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[hc]`. Use `h (RingOfIntegers.mapRingEquiv c a)` as an intermediate fact. Simplify `this` using `[hinv]`.

Rewrite using `[← hz', eigProj_apply D ρ hc hact σ he w]`. Establish `h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v`. Rewrite using `[eigProj_dual D ρ hact, LinearMap.comp_apply]`. Rewrite using `[h2, hz', hv, hG z]`. Both sides reduce to the same expression.
-/
theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  haveI : Module.Finite K (Module.Dual K Li) := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    refine ⟨⟨S, ?_⟩⟩
    rw [← D.om_lat.span_eq_top, ← hS, Submodule.span_span_of_tower]
  haveI : Module.Finite K Li := (Module.finite_dual_iff K).1 inferInstance
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let v : Li := (Module.evalEquiv K Li).symm G
  have hv : ∀ w : Module.Dual K Li, w v = G w := fun w => by
    simpa [v] using Module.apply_evalEquiv_symm_apply w G
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    rw [h2, hz', hv, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
