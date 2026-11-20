import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx.PrincipalLevelLattice

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def principalHermitianLattice : Formalism.BasicNotions.HLat K := toHLat (X.XE cr b) (X.data cr b).RR

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermitian_lattice_space_eq : (principalHermitianLattice X cr b).V = (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermitian_lattice_frame_eq : (principalHermitianLattice X cr b).X = (X.XE cr b) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermitian_lattice_eq_data : (principalHermitianLattice X cr b).L = (X.data cr b).RR := rfl

def jEEx (σ : K →+* ℂ) : (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) →ₛₗ[σ] X.EE :=
  (X.iC cr b Bs.μ0).comp (cptL σ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jEEx_apply (σ : K →+* ℂ) (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    jEEx X cr b σ x = X.iC cr b Bs.μ0 (cpt σ x) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[cpt]`. Simplify using `[cpt, Pi.single_apply, h]`.
-/
theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (i : Fin n) : cpt σ (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]

/- English proof (translation)
Introduce `x y hxy`. Rewrite `hxy` using `[jEEx_apply, jEEx_apply]`. Establish `h` using `h2.1 hxy`. Use function extensionality and compare the values at `i`. Conclude with `σ.injective (by simpa [cpt] using congrFun h i)`.
-/
theorem jEEx_injective (h2 : X.H2 cr b) (σ : K →+* ℂ) : Function.Injective (jEEx X cr b σ) := by
  intro x y hxy
  rw [jEEx_apply, jEEx_apply] at hxy
  have h := h2.1 hxy
  funext i
  exact σ.injective (by simpa [cpt] using congrFun h i)

/- English proof (translation)
Rewrite using `[← h2.2.2]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[jEEx_apply]`.

Conclude with `LinearMap.mem_range_self _ _`. Rewrite using `[LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((lv (fc X.zs) b).dQ Bs.μ0))).span_eq, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨Pi.single k 1, ?_⟩` and prove the remaining obligations. Rewrite using `[jEEx_apply, cpt_single, Pi.basisFun_apply]`.
-/
theorem span_jEEx (h2 : X.H2 cr b) (σ : K →+* ℂ) :
    Submodule.span ℂ (Set.range (jEEx X cr b σ)) = X.EEl b := by
  rw [← h2.2.2]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [jEEx_apply]
    exact LinearMap.mem_range_self _ _
  · rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((lv (fc X.zs) b).dQ Bs.μ0))).span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Pi.single k 1, ?_⟩
    rw [jEEx_apply, cpt_single, Pi.basisFun_apply]

structure RowsId (c : ℂ →+* ℂ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  c_cases : c = RingHom.id ℂ ∨ c = starRingEnd ℂ
  e : E →ₛₗ[c] X.EE
  range_e : Set.range e = (X.EEl b : Set X.EE)
  inner_e : ∀ x y : E, ⟪e x, e y⟫_ℂ = ((X.nP b : ℝ) : ℂ) * c ⟪x, y⟫_ℂ

variable {X b} {c : ℂ →+* ℂ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/- English proof (translation)
Apply the tactic sequence `rcases I.c_cases with rfl | rfl <;> simp`.
-/
theorem RowsId.c_c (I : RowsId X b c E) (z : ℂ) : c (c z) = z := by
  rcases I.c_cases with rfl | rfl <;> simp

/- English proof (translation)
Break down `I.c_cases with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Conclude with `hz`.
-/
theorem RowsId.c_real (I : RowsId X b c E) {z : ℂ} (hz : starRingEnd ℂ z = z) : c z = z := by
  rcases I.c_cases with rfl | rfl
  · rfl
  · exact hz

/- English proof (translation)
Introduce `x y hxy`. Establish `h0 : I.e (x - y) = 0` using `by rw [map_sub, hxy, sub_self]`. Establish `h1` using `I.inner_e (x - y) (x - y)`. Rewrite `h1` using `[h0, inner_zero_left]`. Establish `hne : ((X.nP b : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Establish `h2 : c ⟪x - y, x - y⟫_ℂ = 0`. Break down `mul_eq_zero.mp h1.symm with h | h` into its components or cases. Conclude with `absurd h hne`. Conclude with `h`. Establish `h3 : ⟪x - y, x - y⟫_ℂ = 0` using `by rw [← I.c_c ⟪x - y, x - y⟫_ℂ, h2, map_zero]`.

Rewrite `h3` using `[inner_self_eq_zero, sub_eq_zero]`. Conclude with `h3`.
-/
theorem RowsId.e_injective (I : RowsId X b c E) (hn : 0 < X.nP b) : Function.Injective I.e := by
  intro x y hxy
  have h0 : I.e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 := I.inner_e (x - y) (x - y)
  rw [h0, inner_zero_left] at h1
  have hne : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : c ⟪x - y, x - y⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hne
    · exact h
  have h3 : ⟪x - y, x - y⟫_ℂ = 0 := by rw [← I.c_c ⟪x - y, x - y⟫_ℂ, h2, map_zero]
  rw [inner_self_eq_zero, sub_eq_zero] at h3
  exact h3

variable (X b)

/- English proof (translation)
Establish `hy : X.iC cr b Bs.μ0 y ∈ (X.EEl b : Set X.EE)`. Rewrite using `[← h2.2.2]`. Conclude with `LinearMap.mem_range_self _ y`. Rewrite `hy` using `[← I.range_e]`. Take `⟨w, hw⟩` from `hy`.

Conclude with `⟨w, hw⟩`.
-/
theorem iC_mem_range (h2 : X.H2 cr b) (I : RowsId X b c E) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) :
    ∃ w, I.e w = X.iC cr b Bs.μ0 y := by
  have hy : X.iC cr b Bs.μ0 y ∈ (X.EEl b : Set X.EE) := by
    rw [← h2.2.2]
    exact LinearMap.mem_range_self _ y
  rw [← I.range_e] at hy
  obtain ⟨w, hw⟩ := hy
  exact ⟨w, hw⟩

def rowsMap (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) : (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) →ₛₗ[c] E where
  toFun y := Classical.choose (iC_mem_range X cr b h2 I y)
  map_add' y z := I.e_injective hn (by
    have h1 := Classical.choose_spec (iC_mem_range X cr b h2 I (y + z))
    have h3 := Classical.choose_spec (iC_mem_range X cr b h2 I y)
    have h4 := Classical.choose_spec (iC_mem_range X cr b h2 I z)
    rw [h1, map_add I.e, h3, h4, map_add])
  map_smul' a y := I.e_injective hn (by
    have h1 := Classical.choose_spec (iC_mem_range X cr b h2 I (a • y))
    have h3 := Classical.choose_spec (iC_mem_range X cr b h2 I y)
    rw [h1, map_smulₛₗ I.e, h3, I.c_c, map_smul])

/- English proof (translation)
The claim follows from `Classical.choose_spec (iC_mem_range X cr b h2 I y)`.
-/
theorem e_rowsMap (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) :
    I.e (rowsMap X cr b h2 I hn y) = X.iC cr b Bs.μ0 y :=
  Classical.choose_spec (iC_mem_range X cr b h2 I y)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y z hyz`. Apply `h2.1` to reduce the goal to its premises. Rewrite using `[← e_rowsMap X cr b h2 I hn y, ← e_rowsMap X cr b h2 I hn z, hyz]`. Introduce `w`.

Establish `hw : I.e w ∈ (X.EEl b : Set X.EE)`. Rewrite using `[← I.range_e]`. Conclude with `⟨w, rfl⟩`. Rewrite `hw` using `[← h2.2.2, SetLike.mem_coe, LinearMap.mem_range]`. Take `⟨y, hy⟩` from `hw`.

Conclude with `⟨y, I.e_injective hn (by rw [e_rowsMap, hy])⟩`.
-/
theorem rowsMap_bijective (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) :
    Function.Bijective (rowsMap X cr b h2 I hn) := by
  constructor
  · intro y z hyz
    apply h2.1
    rw [← e_rowsMap X cr b h2 I hn y, ← e_rowsMap X cr b h2 I hn z, hyz]
  · intro w
    have hw : I.e w ∈ (X.EEl b : Set X.EE) := by
      rw [← I.range_e]
      exact ⟨w, rfl⟩
    rw [← h2.2.2, SetLike.mem_coe, LinearMap.mem_range] at hw
    obtain ⟨y, hy⟩ := hw
    exact ⟨y, I.e_injective hn (by rw [e_rowsMap, hy])⟩

/- English proof (translation)
Establish `h : InfinitePlace.mk Bs.v0.embedding = InfinitePlace.mk σ`. Rewrite using `[InfinitePlace.mk_embedding, hv]`. Break down `InfinitePlace.mk_eq_iff.mp h with h | h` into its components or cases. Conclude with `⟨RingHom.id ℂ, Or.inl rfl, fun a => by simp [h]⟩`. Use `⟨starRingEnd ℂ, Or.inr rfl, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[← h]`. Simplify using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem exists_twist (σ : K →+* ℂ) (hv : InfinitePlace.mk σ = Bs.v0) :
    ∃ c : ℂ →+* ℂ, (c = RingHom.id ℂ ∨ c = starRingEnd ℂ) ∧ ∀ a, Bs.v0.embedding a = c (σ a) := by
  have h : InfinitePlace.mk Bs.v0.embedding = InfinitePlace.mk σ := by
    rw [InfinitePlace.mk_embedding, hv]
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun a => by simp [h]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun a => ?_⟩
    rw [← h]
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Break down `hcc with rfl | rfl` into its components or cases. Establish `h : Bs.v0.embedding = σ` using `RingHom.ext fun a => by simpa using hc a`. Rewrite using `[← h, InfinitePlace.mk_embedding]`. Establish `h : Bs.v0.embedding = NumberField.ComplexEmbedding.conjugate σ` using `RingHom.ext fun a => by rw [hc a, NumberField.ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]`.
-/
theorem mk_eq_of_twist (σ : K →+* ℂ) (hcc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    InfinitePlace.mk σ = Bs.v0 := by
  rcases hcc with rfl | rfl
  · have h : Bs.v0.embedding = σ := RingHom.ext fun a => by simpa using hc a
    rw [← h, InfinitePlace.mk_embedding]
  · have h : Bs.v0.embedding = NumberField.ComplexEmbedding.conjugate σ :=
      RingHom.ext fun a => by rw [hc a, NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]

def jEE (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) →ₛₗ[σ] E where
  toFun x := rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    show rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ (a • x)) = σ a • rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ x)
    rw [map_smulₛₗ, map_smulₛₗ, hc a, I.c_c]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jEE_apply (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) : jEE X cr b h2 I hn σ hc x = rowsMap X cr b h2 I hn (cpt Bs.v0.embedding x) := rfl

/- English proof (translation)
Rewrite using `[jEE_apply, e_rowsMap, jEEx_apply]`.
-/
theorem e_jEE (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) : I.e (jEE X cr b h2 I hn σ hc x) = jEEx X cr b Bs.v0.embedding x := by
  rw [jEE_apply, e_rowsMap, jEEx_apply]

/- English proof (translation)
Introduce `x y hxy`. Apply `jEEx_injective X cr b h2 Bs.v0.embedding` to reduce the goal to its premises. Rewrite using `[← e_jEE X cr b h2 I hn σ hc x, ← e_jEE X cr b h2 I hn σ hc y, hxy]`.
-/
theorem jEE_injective (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ)
    (hc : ∀ a, Bs.v0.embedding a = c (σ a)) : Function.Injective (jEE X cr b h2 I hn σ hc) := by
  intro x y hxy
  apply jEEx_injective X cr b h2 Bs.v0.embedding
  rw [← e_jEE X cr b h2 I hn σ hc x, ← e_jEE X cr b h2 I hn σ hc y, hxy]

/- English proof (translation)
Establish `hf : (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i)) = fun i => rowsMap X cr b h2 I hn (Pi.single i 1)`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.basisFun_apply, jEE_apply, cpt_single]`. Establish `hsm : ∀ (z : ℂ) (w : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ), z • rowsMap X cr b h2 I hn w = rowsMap X cr b h2 I hn (c z • w)`. Introduce `z w`.

Rewrite using `[map_smulₛₗ, I.c_c]`. Rewrite using `[hf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`.

Rewrite `hg` using `[hsm, ← map_sum]`. Establish `h0 : ∑ j, c (g j) • (Pi.single j 1 : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) = 0` using `(rowsMap_bijective X cr b h2 I hn).1 (hg.trans (map_zero _).symm)`. Establish `h1` using `congrFun h0 i`. Simplify `h1` using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[eq_top_iff]`.

Introduce `w _`. Take `⟨y, rfl⟩` from `(rowsMap_bijective X cr b h2 I hn).2 w`. Use `(Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => c (y i), ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hsm, I.c_c, ← map_sum]`. Use `congr 1`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem jEE_basis (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    LinearIndependent ℂ (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i)) ∧
      Submodule.span ℂ (Set.range (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i))) = ⊤ := by
  have hf : (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i)) =
      fun i => rowsMap X cr b h2 I hn (Pi.single i 1) := by
    funext i
    rw [Pi.basisFun_apply, jEE_apply, cpt_single]
  have hsm : ∀ (z : ℂ) (w : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ), z • rowsMap X cr b h2 I hn w = rowsMap X cr b h2 I hn (c z • w) := by
    intro z w; rw [map_smulₛₗ, I.c_c]
  rw [hf]
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp_rw [hsm, ← map_sum] at hg
    have h0 : ∑ j, c (g j) • (Pi.single j 1 : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) = 0 :=
      (rowsMap_bijective X cr b h2 I hn).1 (hg.trans (map_zero _).symm)
    have h1 := congrFun h0 i
    simpa [Finset.sum_apply, Pi.single_apply] using h1
  · rw [eq_top_iff]
    intro w _
    obtain ⟨y, rfl⟩ := (rowsMap_bijective X cr b h2 I hn).2 w
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => c (y i), ?_⟩
    simp_rw [hsm, I.c_c, ← map_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Use `show rowXE _ _ _ _ Bs.v0 = _`. Simplify using `[rowXE, rowFrame, spliceFrame]`.
-/
theorem frame_at_base_place_eq_gram : (X.XE cr b) Bs.v0 = frameOf (X.gramE cr b) := by
  show rowXE _ _ _ _ Bs.v0 = _
  simp [rowXE, rowFrame, spliceFrame]

/- English proof (translation)
The claim follows from `(rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1 (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).1`.
-/
theorem frames (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (hp : X.H4pos) :
    ∀ v, IsUnit ((principalHermitianLattice X cr b).X v).det :=
  (rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).1

/- English proof (translation)
Establish `hli : LinearIndependent ℂ (fun i => X.iC cr b Bs.μ0 (Pi.single i 1))` using `li_of_lin_injective (by rw [lin_basis]; exact h2.1)`. Rewrite using `[majAt_gram_smul (X.XE cr b) Bs.v0 _ hli _ (inv_pos.mpr hn) (frame_at_base_place_eq_gram X cr b), lin_basis]`. Both sides reduce to the same expression.
-/
theorem majorant_at_base_place_eq_inner (h2 : X.H2 cr b) (hn : 0 < X.nP b) (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y =
      (((X.nP b)⁻¹ : ℝ) : ℂ) * ⟪jEEx X cr b Bs.v0.embedding x, jEEx X cr b Bs.v0.embedding y⟫_ℂ := by
  have hli : LinearIndependent ℂ (fun i => X.iC cr b Bs.μ0 (Pi.single i 1)) :=
    li_of_lin_injective (by rw [lin_basis]; exact h2.1)
  rw [majAt_gram_smul (X.XE cr b) Bs.v0 _ hli _ (inv_pos.mpr hn) (frame_at_base_place_eq_gram X cr b), lin_basis]
  rfl

/- English proof (translation)
Rewrite using `[majorant_at_base_place_eq_inner X cr b h2 hn, ← e_jEE X cr b h2 I hn σ hc, ← e_jEE X cr b h2 I hn σ hc, I.inner_e, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hn.ne', Complex.ofReal_one, one_mul]`.
-/
theorem jEE_inner (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y = c ⟪jEE X cr b h2 I hn σ hc x, jEE X cr b h2 I hn σ hc y⟫_ℂ := by
  rw [majorant_at_base_place_eq_inner X cr b h2 hn, ← e_jEE X cr b h2 I hn σ hc, ← e_jEE X cr b h2 I hn σ hc, I.inner_e, ← mul_assoc,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hn.ne', Complex.ofReal_one, one_mul]

/- English proof (translation)
Establish `h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x x = ⟪jEE X cr b h2 I hn σ hc x, jEE X cr b h2 I hn σ hc x⟫_ℂ`. Rewrite using `[jEE_inner X cr b h2 I hn σ hc x x, I.c_real (inner_conj_symm _ _)]`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (jEE X cr b h2 I hn σ hc x)), ← inner_self_eq_norm_sq (𝕜 := ℂ), ← h]`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt`. Use `congr 1`.

Establish `hz : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hz]`.

Rewrite using `[← Complex.ofReal_sum]`. Conclude with `(Complex.ofReal_re _).symm`.
-/
theorem jEE_norm (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x = ‖jEE X cr b h2 I hn σ hc x‖ := by
  have h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x x =
      ⟪jEE X cr b h2 I hn σ hc x, jEE X cr b h2 I hn σ hc x⟫_ℂ := by
    rw [jEE_inner X cr b h2 I hn σ hc x x, I.c_real (inner_conj_symm _ _)]
  rw [← Real.sqrt_sq (norm_nonneg (jEE X cr b h2 I hn σ hc x)), ← inner_self_eq_norm_sq (𝕜 := ℂ), ← h]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  have hz : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  simp_rw [hz]
  rw [← Complex.ofReal_sum]
  exact (Complex.ofReal_re _).symm

/- English proof (translation)
Rewrite using `[mk_eq_of_twist σ I.c_cases hc]`. Conclude with `jEE_norm X cr b h2 I hn σ hc x`.
-/
theorem jEE_norm_mk (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K _) (X.XE cr b) (InfinitePlace.mk σ) x = ‖jEE X cr b h2 I hn σ hc x‖ := by
  rw [mk_eq_of_twist σ I.c_cases hc]
  exact jEE_norm X cr b h2 I hn σ hc x

/- English proof (translation)
The claim follows from `jEE_norm_mk X cr b h2 I hn σ hc x`.
-/
theorem embedding_norm_eq_lattice_norm (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : (principalHermitianLattice X cr b).V) :
    Formalism.HermitianLatticesTheory.normAt (principalHermitianLattice X cr b).b (principalHermitianLattice X cr b).X (InfinitePlace.mk σ) x = ‖jEE X cr b h2 I hn σ hc x‖ :=
  jEE_norm_mk X cr b h2 I hn σ hc x

/- English proof (translation)
The claim follows from `jEE_basis X cr b h2 I hn σ hc`.
-/
theorem embedding_of_lattice_basis_is_basis (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ)
    (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    LinearIndependent ℂ (fun i => jEE X cr b h2 I hn σ hc ((principalHermitianLattice X cr b).b i)) ∧
      Submodule.span ℂ (Set.range (fun i => jEE X cr b h2 I hn σ hc ((principalHermitianLattice X cr b).b i))) = ⊤ :=
  jEE_basis X cr b h2 I hn σ hc

/- English proof (translation)
The claim follows from `(rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1 (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).2.2 v hv x y`.
-/
theorem majAt_off (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (hp : X.H4pos) (v : InfinitePlace K) (hv : v ≠ Bs.v0)
    (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) v x y =
      ∑ p, ((X.κ v * ∏ j, X.lam j Bs.μ0 p v : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XQ Bs.μ0) v
          ((partPr (lv (fc X.zs) b) Bs.μ0 p).mulVec x) ((partPr (lv (fc X.zs) b) Bs.μ0 p).mulVec y) :=
  (rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).2.2 v hv x y

/- English proof (translation)
The claim follows from `rowXE_part (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1 (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v) v hv (ho v hv) p x hx y`.
-/
theorem majAt_off_part (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (hp : X.H4pos) (ho : X.PartsOrth b (fc := fc)) (v : InfinitePlace K)
    (hv : v ≠ Bs.v0) (p : Bs.Ix) (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) (hx : x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p)
    (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) v x y =
      ((X.κ v * ∏ j, X.lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XQ Bs.μ0) v x y :=
  rowXE_part (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1 (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v) v hv (ho v hv) p x hx y

/- English proof (translation)
The claim follows from `RR_spec hW (X.data cr b) h0 (fun t => (X.rowMat_bij cr b h2 hr t).2)`.
-/
theorem RR_lattice (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b) :
    Submodule.IsLattice K (principalHermitianLattice X cr b).L ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (principalHermitianLattice X cr b).L =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w))) :=
  RR_spec hW (X.data cr b) h0 (fun t => (X.rowMat_bij cr b h2 hr t).2)

/- English proof (translation)
Take `⟨hL, -⟩` from `RR_lattice X cr b hW h0 h2 hr`. Conclude with `⟨frames X cr b hW h2 hp, hL.fg, hL.span_eq_top⟩`.
-/
theorem principal_hermitian_lattice_good (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b) (hp : X.H4pos) :
    (principalHermitianLattice X cr b).Good := by
  obtain ⟨hL, -⟩ := RR_lattice X cr b hW h0 h2 hr
  exact ⟨frames X cr b hW h2 hp, hL.fg, hL.span_eq_top⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, (X.key_row cr b h2 hr t z).symm⟩`. Introduce and unpack `⟨z, hz, hzy⟩`. Use `⟨z, hz, jEEx_injective X cr b h2 Bs.v0.embedding ?_⟩` and prove the remaining obligations.

Use `show X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec z)) = jEEx X cr b Bs.v0.embedding y`. Rewrite using `[X.key_row cr b h2 hr t z]`. Conclude with `hzy`.
-/
theorem mem_matLat_iff (h2 : X.H2 cr b) (hr : X.RATmu cr b) (t : Bs.Tup) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    y ∈ matLat (X.rowMat cr b t) ((lv (fc X.zs) b).abelian₂ t) ↔
      jEEx X cr b Bs.v0.embedding y ∈ (fun z => X.iC cr b t (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ t) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (X.key_row cr b h2 hr t z).symm⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, jEEx_injective X cr b h2 Bs.v0.embedding ?_⟩
    show X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec z)) = jEEx X cr b Bs.v0.embedding y
    rw [X.key_row cr b h2 hr t z]
    exact hzy

/- English proof (translation)
Establish `hloc` using `(RR_lattice X cr b hW h0 h2 hr).2`. Establish `key : ∀ (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K)) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K), y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ L` using `fun _ _ _ => Iff.rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hx w`. Establish `h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (principalHermitianLattice X cr b).L` using `(key w _ x).2 ⟨1, w.asIdeal.primeCompl.one_mem, (principalHermitianLattice X cr b).L.smul_mem 1 hx⟩`.

Rewrite `h1` using `[hloc w]`. Take `⟨d, hd, hdx⟩` from `(key w _ x).1 h1`. Conclude with `⟨d, hd, hdx⟩`. Introduce `hx`. Assume the negation of the conclusion as `hxL`.

Set `I : Ideal (𝓞 K)` to `Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) _ x) (principalHermitianLattice X cr b).L`. Establish `hmem : ∀ r : 𝓞 K, r ∈ I ↔ r • x ∈ (principalHermitianLattice X cr b).L` using `fun r => Iff.rfl`. Establish `hI : I ≠ ⊤`. Introduce `h`. Apply `hxL` to reduce the goal to its premises.

Establish `h1 : (1 : 𝓞 K) ∈ I` using `h ▸ Submodule.mem_top`. Simplify using `using (hmem 1).mp h1`. Take `⟨p, hp, hIp⟩` from `Ideal.exists_le_maximal I hI`. Establish `hpb : p ≠ ⊥`. Introduce `hb`.

Substitute `hb` using the available equality. Conclude with `NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.2 hp)`. Set `w : HeightOneSpectrum (𝓞 K)` to `⟨p, hp.isPrime, hpb⟩`. Take `⟨d, hd, hdx⟩` from `hx w`. Establish `h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w)))` using `(key w _ x).2 ⟨d, hd, hdx⟩`.

Rewrite `h1` using `[← hloc w]`. Take `⟨s, hs, hsx⟩` from `(key w _ x).1 h1`. Conclude with `hs (hIp ((hmem s).2 hsx))`.
-/
theorem RR_mem (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b)
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    x ∈ (principalHermitianLattice X cr b).L ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ d : 𝓞 K, d ∉ w.asIdeal ∧
      d • x ∈ matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w)) := by
  have hloc := (RR_lattice X cr b hW h0 h2 hr).2
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K))
      (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K),
      y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ L := fun _ _ _ => Iff.rfl
  constructor
  · intro hx w
    have h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (principalHermitianLattice X cr b).L :=
      (key w _ x).2 ⟨1, w.asIdeal.primeCompl.one_mem, (principalHermitianLattice X cr b).L.smul_mem 1 hx⟩
    rw [hloc w] at h1
    obtain ⟨d, hd, hdx⟩ := (key w _ x).1 h1
    exact ⟨d, hd, hdx⟩
  · intro hx
    by_contra hxL
    let I : Ideal (𝓞 K) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) _ x) (principalHermitianLattice X cr b).L
    have hmem : ∀ r : 𝓞 K, r ∈ I ↔ r • x ∈ (principalHermitianLattice X cr b).L := fun r => Iff.rfl
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 K) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have hpb : p ≠ ⊥ := by
      intro hb
      subst hb
      exact NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.2 hp)
    let w : HeightOneSpectrum (𝓞 K) := ⟨p, hp.isPrime, hpb⟩
    obtain ⟨d, hd, hdx⟩ := hx w
    have h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w))) :=
      (key w _ x).2 ⟨d, hd, hdx⟩
    rw [← hloc w] at h1
    obtain ⟨s, hs, hsx⟩ := (key w _ x).1 h1
    exact hs (hIp ((hmem s).2 hsx))

/- English proof (translation)
Establish `hs : ∀ t, Submodule.span (𝓞 K) {y | jEEx X cr b Bs.v0.embedding y ∈ (fun z => X.iC cr b t (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ t)} = matLat (X.rowMat cr b t) ((lv (fc X.zs) b).abelian₂ t)` using `fun t => by`. Establish `: {y | jEEx X cr b Bs.v0.embedding y ∈ (fun z => X.iC cr b t (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ t)} = (matLat (X.rowMat cr b t) ((lv (fc X.zs) b).abelian₂ t) : Set _)`. Use extensionality with `y`. Conclude with `(mem_matLat_iff X cr b h2 hr t y).symm`. Rewrite using `[this, Submodule.span_eq]`.

Simplify using `only [hs]`. Conclude with `RR_mem X cr b hW h0 h2 hr x`.
-/
theorem RR_mem_span (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b)
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    x ∈ (principalHermitianLattice X cr b).L ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ d : 𝓞 K, d ∉ w.asIdeal ∧
      d • x ∈ Submodule.span (𝓞 K) {y | jEEx X cr b Bs.v0.embedding y ∈
        (fun z => X.iC cr b (X.μ w) (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ (X.μ w))} := by
  have hs : ∀ t, Submodule.span (𝓞 K) {y | jEEx X cr b Bs.v0.embedding y ∈
      (fun z => X.iC cr b t (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ t)} =
      matLat (X.rowMat cr b t) ((lv (fc X.zs) b).abelian₂ t) := fun t => by
    have : {y | jEEx X cr b Bs.v0.embedding y ∈
        (fun z => X.iC cr b t (cpt Bs.v0.embedding z)) '' ((lv (fc X.zs) b).abelian₂ t)} =
        (matLat (X.rowMat cr b t) ((lv (fc X.zs) b).abelian₂ t) : Set _) := by
      ext y; exact (mem_matLat_iff X cr b h2 hr t y).symm
    rw [this, Submodule.span_eq]
  simp only [hs]
  exact RR_mem X cr b hW h0 h2 hr x

end Formalism.IndefR.Cx.PrincipalLevelLattice

end
