import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

/- English proof (translation)
Introduce `r M W hskew hdet hW`. Use `set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef`. Establish `hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w` using `fun v w => by`. Simplify using `[hBdef, Matrix.toBilin'_apply']`. Establish `hskewB : ∀ v w, B v w = - B w v`.

Introduce `v w`. Rewrite using `[hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]`. Establish `hBalt : ∀ v, B v v = 0` using `fun v => by have := hskewB v v; linarith`. Establish `hrefl : B.IsRefl` using `fun x y h => by rw [hskewB, h, neg_zero]`. Establish `hnd : B.Nondegenerate` using `LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet`.

Set `P : ℕ → Prop` to `fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧ (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n`. Establish `P0 : P 0` using `⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩`. Take `⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r)` from `Nat.findGreatest_spec (Nat.zero_le _) P0`. Establish `hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L`. Introduce `v hvW hvL`.

Assume the negation of the conclusion as `hv`. Establish `hlt : L < L ⊔ Submodule.span ℝ {v}` using `lt_of_le_of_ne le_sup_left (fun h => hv (by`. Rewrite using `[h]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))`. Establish `hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0`.

Introduce `x hx y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨a', ha', b', hb', rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hb`. Take `⟨c', rfl⟩` from `Submodule.mem_span_singleton.mp hb'`.

Establish `h1` using `hLiso a ha a' ha'`. Establish `h2` using `hvL a' ha'`. Establish `h3 : B a v = 0` using `by rw [hskewB, hvL a ha, neg_zero]`. Establish `h4` using `hBalt v`. Simplify using `[map_add, map_smul, h1, h2, h3, h4]`.

Establish `hle : L ⊔ Submodule.span ℝ {v} ≤ W` using `sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)`. Establish `hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v}))` using `⟨_, hle, hiso, rfl⟩`. Establish `h5` using `Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP`. Establish `h6` using `Submodule.finrank_lt_finrank_of_lt hlt`. Use linear arithmetic over natural numbers and integers.

Establish `hWo : B.orthogonal W ≤ L`. Introduce `x hx`. Establish `hxW : x ∈ W` using `hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])`. Conclude with `hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])`. Set `b` to `Module.finBasis ℝ L`.

Set `e : Fin (finrank ℝ L) → Fin r → ℝ` to `fun i => ((b i : L) : Fin r → ℝ)`. Establish `heL : ∀ i, e i ∈ L` using `fun i => (b i).2`. Establish `hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0`. Introduce `φ hφ l hl`. Establish `: φ ∘ₗ L.subtype = 0` using `b.ext (fun j => by simpa using hφ j)`.

Simplify using `using LinearMap.congr_fun this ⟨l, hl⟩`. Set `φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ)` to `LinearMap.pi (fun j => B.flip (e j))`. Establish `hφ : ∀ v j, φ v j = B v (e j)` using `fun v j => rfl`. Establish `hker : LinearMap.ker φ = B.orthogonal L`. Use extensionality with `v`.

Simplify using `only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h l hl`. Establish `h'` using `hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl`. Rewrite using `[hskewB, h', neg_zero]`.

Introduce `h`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]`. Establish `hrange : LinearMap.range φ = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Rewrite `h1` using `[hker, LinearMap.BilinForm.finrank_orthogonal hnd]`. Establish `h2 : finrank ℝ L ≤ r` using `by simpa using Submodule.finrank_le L`. Simplify using `only [Module.finrank_fin_fun] at h1 ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hsurj : ∀ y, ∃ x, φ x = y` using `fun y => by`. Establish `: y ∈ LinearMap.range φ` using `by rw [hrange]; trivial`. Conclude with `this`. Use `choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)`. Establish `hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0`.

Introduce `i j`. Rewrite using `[← hφ, hf i, Pi.single_apply]`. Break down `eq_or_ne i j with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Use `⟨finrank ℝ L, e, f, fun i => hLW (heL i), fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j), fun i j => by rw [← hB]; exact hfe i j, ?_⟩` and prove the remaining obligations. Use `set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU`. Establish `hUo : B.orthogonal U = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `v hv`. Establish `hve : ∀ j, B (e j) v = 0` using `fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)`. Establish `hvf : ∀ i, B (f i) v = 0` using `fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)`. Establish `hvL : ∀ l ∈ L, B v l = 0` using `hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])`. Establish `hvW : v ∈ W`.

Rewrite using `[← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]`. Introduce `x hx`. Rewrite using `[hskewB, hvL x (hWo hx), neg_zero]`. Establish `hvL' : v ∈ L` using `hmax v hvW hvL`. Establish `hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j`.

Use `congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Establish `hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0`.

Introduce `i`. Establish `h` using `hvf i`. Rewrite `h` using `[hv', map_sum]`. Simplify `h` using `[map_smul, hfe]`. Establish `h0 : (⟨v, hvL'⟩ : L) = 0` using `b.repr.injective (by ext i; simp [hc])`.

Simplify using `using congrArg Subtype.val h0`. Establish `hdimU` using `LinearMap.BilinForm.finrank_orthogonal hnd U`. Rewrite `hdimU` using `[hUo, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use `Submodule.finrank_le U` as an intermediate fact.

Simplify using `only [Module.finrank_fin_fun] at hdimU this ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
