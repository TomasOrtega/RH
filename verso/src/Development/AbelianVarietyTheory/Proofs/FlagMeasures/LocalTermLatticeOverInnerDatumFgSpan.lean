import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TermLat

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun v := H.h v y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem hl_apply (H : HermSp M V) (y v : V) : hl H y v = H.h v y := rfl

/- English proof (translation)
The claim follows from `(hl H y).map_sub x x'`.
-/
theorem h_sub (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y :=
  (hl H y).map_sub x x'

/- English proof (translation)
The claim follows from `map_sum (hl H y) g s`.
-/
theorem h_sum (H : HermSp M V) {ι : Type} (s : Finset ι) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, g i) y = ∑ i ∈ s, H.h (g i) y :=
  map_sum (hl H y) g s

/- English proof (translation)
The claim follows from `H.h_smul_left a x y`.
-/
theorem h_smul (H : HermSp M V) (a : E) (x y : V) : H.h (a • x) y = a * H.h x y :=
  H.h_smul_left a x y

/- English proof (translation)
Rewrite using `[H.h_herm, h, map_zero]`.
-/
theorem h_eq_zero_comm (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h, map_zero]

/- English proof (translation)
Rewrite `hx`, the goal using `[L.O_def]`. Conclude with `hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])`.
-/
theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

/- English proof (translation)
The claim follows from `(L.O_def _).2 isIntegral_algebraMap`.
-/
theorem alg_mem (L : LocE F E) (a : 𝒪[F]) : algebraMap 𝒪[F] E a ∈ L.O :=
  (L.O_def _).2 isIntegral_algebraMap

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `: IsFractionRing 𝒪[F] F` using `(Valuation.integer.integers (valuation F)).isFractionRing`. Establish `h1 : IsAlgebraic F x` using `(Algebra.IsIntegral.isIntegral (R := F) x).isAlgebraic`. Establish `h2 : IsAlgebraic 𝒪[F] x` using `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1`.

Take `⟨d, hd, hi⟩` from `h2.exists_integral_multiple`. Conclude with `⟨d, hd, (L.O_def _).2 (by rwa [Algebra.smul_def] at hi)⟩`.
-/
theorem exists_one (L : LocE F E) (x : E) :
    ∃ b : 𝒪[F], b ≠ 0 ∧ algebraMap 𝒪[F] E b * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsFractionRing 𝒪[F] F := (Valuation.integer.integers (valuation F)).isFractionRing
  have h1 : IsAlgebraic F x := (Algebra.IsIntegral.isIntegral (R := F) x).isAlgebraic
  have h2 : IsAlgebraic 𝒪[F] x := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨d, hd, hi⟩ := h2.exists_integral_multiple
  exact ⟨d, hd, (L.O_def _).2 (by rwa [Algebra.smul_def] at hi)⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert x s _ ih`. Take `⟨a, ha, hs⟩` from `ih`. Take `⟨b, hb, hbx⟩` from `exists_one L x`.

Use `⟨a * b, mul_ne_zero ha hb, fun y hy => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Rewrite using `[map_mul, mul_assoc]`. Conclude with `L.O.mul_mem (alg_mem L a) hbx`. Rewrite using `[map_mul, mul_right_comm]`.

Conclude with `L.O.mul_mem (hs y hy) (alg_mem L b)`.
-/
theorem exists_fin (L : LocE F E) (s : Finset E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ x ∈ s, algebraMap 𝒪[F] E a * x ∈ L.O := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x s _ ih =>
    obtain ⟨a, ha, hs⟩ := ih
    obtain ⟨b, hb, hbx⟩ := exists_one L x
    refine ⟨a * b, mul_ne_zero ha hb, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [map_mul, mul_assoc]
      exact L.O.mul_mem (alg_mem L a) hbx
    · rw [map_mul, mul_right_comm]
      exact L.O.mul_mem (hs y hy) (alg_mem L b)

/- English proof (translation)
The claim follows from `h.map _`.
-/
theorem img_fg (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} (h : Λ.FG) : (img g Λ).FG := h.map _

/- English proof (translation)
Establish `e : (img g Λ : Set V) = (g : V →ₗ[E] V) '' Λ`. Unfold `img`. Rewrite using `[Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[e, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `g.surjective`.
-/
theorem img_span (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} (h : Submodule.span E (Λ : Set V) = ⊤) :
    Submodule.span E (img g Λ : Set V) = ⊤ := by
  have e : (img g Λ : Set V) = (g : V →ₗ[E] V) '' Λ := by
    unfold img; rw [Submodule.map_coe]; rfl
  rw [e, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end GlobalTheory.TermLat

namespace GlobalTheory.TermLat

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

/- English proof (translation)
The claim follows from `Fr.h_es a b`.
-/
theorem h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

/- English proof (translation)
Apply the tactic sequence `rw [H.h_herm, h_e_es]; split_ifs <;> simp`.
-/
theorem h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := by
  rw [H.h_herm, h_e_es]; split_ifs <;> simp

/- English proof (translation)
The claim follows from `Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)`.
-/
theorem h_e_e (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)

/- English proof (translation)
The claim follows from `Fr.h_ss a b`.
-/
theorem h_es_es (a b : Fin r) : H.h (Fr.es a) (Fr.es b) = 0 := Fr.h_ss a b

def prL : V →ₗ[E] V :=
  LinearMap.id - ∑ a, (hl H (Fr.es a)).smulRight (Fr.e a) - ∑ a, (hl H (Fr.e a)).smulRight (Fr.es a)

/- English proof (translation)
Simplify using `[prL, FrameD.prF, LinearMap.sub_apply, LinearMap.sum_apply]`.
-/
theorem prL_apply (v : V) : prL Fr v = Fr.prF v := by
  simp [prL, FrameD.prF, LinearMap.sub_apply, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[FrameD.prF, h_sub, h_sum, h_smul, h_e_es, h_es_es]`.
-/
theorem prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  simp [FrameD.prF, h_sub, h_sum, h_smul, h_e_es, h_es_es]

/- English proof (translation)
Simplify using `[FrameD.prF, h_sub, h_sum, h_smul, h_e_e, h_es_e]`.
-/
theorem prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  simp [FrameD.prF, h_sub, h_sum, h_smul, h_e_e, h_es_e]

/- English proof (translation)
Simplify using `[FrameD.prF, h1, h2]`.
-/
theorem prF_of {u : V} (h1 : ∀ a, H.h u (Fr.es a) = 0) (h2 : ∀ a, H.h u (Fr.e a) = 0) :
    Fr.prF u = u := by
  simp [FrameD.prF, h1, h2]

/- English proof (translation)
The claim follows from `prF_of Fr (prF_es Fr v) (prF_e Fr v)`.
-/
theorem prF_prF (v : V) : Fr.prF (Fr.prF v) = Fr.prF v :=
  prF_of Fr (prF_es Fr v) (prF_e Fr v)

/- English proof (translation)
Rewrite using `[← prL_apply, map_smul, prL_apply]`.
-/
theorem prF_smul (c : E) (u : V) : Fr.prF (c • u) = c • Fr.prF u := by
  rw [← prL_apply, map_smul, prL_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu a`. Conclude with `hu (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `hu x hx`. Establish `hle : H.X Fr.f ≤ LinearMap.ker (hl H u)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, hl_apply]`. Conclude with `h_eq_zero_comm H (hu a)`. Conclude with `h_eq_zero_comm H (hle hx)`.
-/
theorem mem_perpX {u : V} : u ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h u (Fr.e a) = 0 := by
  constructor
  · intro hu a
    exact hu (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩)
  · intro hu x hx
    have hle : H.X Fr.f ≤ LinearMap.ker (hl H u) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hl_apply]
      exact h_eq_zero_comm H (hu a)
    exact h_eq_zero_comm H (hle hx)

/- English proof (translation)
The claim follows from `(mem_perpX Fr).2 (prF_e Fr v)`.
-/
theorem prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perpX Fr).2 (prF_e Fr v)

/- English proof (translation)
Establish `hle : H.X Fr.f ≤ LinearMap.ker (prL Fr)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker]`. Use `show (prL Fr) (Fr.e a) = 0`.

Rewrite using `[prL_apply]`. Simplify using `[FrameD.prF, h_e_es, h_e_e, ite_smul, Finset.sum_ite_eq]`. Rewrite using `[← prL_apply]`. Conclude with `hle hξ`.
-/
theorem prF_X {ξ : V} (hξ : ξ ∈ H.X Fr.f) : Fr.prF ξ = 0 := by
  have hle : H.X Fr.f ≤ LinearMap.ker (prL Fr) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    show (prL Fr) (Fr.e a) = 0
    rw [prL_apply]
    simp [FrameD.prF, h_e_es, h_e_e, ite_smul, Finset.sum_ite_eq]
  rw [← prL_apply]; exact hle hξ

/- English proof (translation)
The claim follows from `prF_X Fr (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem prF_e_self (a : Fin r) : Fr.prF (Fr.e a) = 0 := prF_X Fr (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Simplify using `[FrameD.prF, h_es_es, h_es_e, ite_smul, Finset.sum_ite_eq']`.
-/
theorem prF_es_self (a : Fin r) : Fr.prF (Fr.es a) = 0 := by
  simp [FrameD.prF, h_es_es, h_es_e, ite_smul, Finset.sum_ite_eq']

/- English proof (translation)
Establish `h0 : ∀ a, H.h y (Fr.e a) = 0` using `(mem_perpX Fr).1 hy`. Establish `e : Fr.prF y - y = -∑ a, H.h y (Fr.es a) • Fr.e a`. Simplify using `only [FrameD.prF, h0, zero_smul, Finset.sum_const_zero, sub_zero]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `neg_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))`.
-/
theorem prF_sub_mem {y : V} (hy : y ∈ H.perp (H.X Fr.f)) : Fr.prF y - y ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h y (Fr.e a) = 0 := (mem_perpX Fr).1 hy
  have e : Fr.prF y - y = -∑ a, H.h y (Fr.es a) • Fr.e a := by
    simp only [FrameD.prF, h0, zero_smul, Finset.sum_const_zero, sub_zero]; abel
  rw [e]
  exact neg_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

def rho : H.Wb Fr.f →ₗ[E] V :=
  Submodule.liftQ _ (prL Fr ∘ₗ (H.perp (H.X Fr.f)).subtype) (by
    intro w hw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hw
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, prL_apply]
    exact prF_X Fr hw)

/- English proof (translation)
Simplify using `[rho, HermSp.mkW, prL_apply]`.
-/
theorem rho_mkW (y : ↥(H.perp (H.X Fr.f))) : rho Fr (H.mkW Fr.f y) = Fr.prF y := by
  simp [rho, HermSp.mkW, prL_apply]

/- English proof (translation)
Simplify using `only [HermSp.mkW, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Simplify `prF_sub_mem Fr y.2` using `[Submodule.mem_comap]`.
-/
theorem mkW_prF (y : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f ⟨Fr.prF y, prF_perp Fr y⟩ = H.mkW Fr.f y := by
  simp only [HermSp.mkW, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  simpa [Submodule.mem_comap] using prF_sub_mem Fr y.2

end GlobalTheory.TermLat

namespace GlobalTheory.TermLat

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨h1, h2, w, hw, hL⟩`.
-/
theorem mem_LamStd {L : Submodule M.L.O (H.Wb Fr.f)} {u : V} (h1 : ∀ a, H.h u (Fr.es a) ∈ M.L.O)
    (h2 : ∀ a, H.h u (Fr.e a) ∈ M.L.O) (w : ↥(H.perp (H.X Fr.f))) (hw : (w : V) = Fr.prF u)
    (hL : H.mkW Fr.f w ∈ L) : u ∈ Fr.LamStd L :=
  Submodule.subset_span ⟨h1, h2, w, hw, hL⟩

/- English proof (translation)
The claim follows from `mem_LamStd Fr (fun b => by rw [h_e_es]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]) (fun b => by rw [h_e_e]; exact M.L.O.zero_mem) 0 (by rw [prF_e_self]; rfl) (by rw [map_zero]; exact L.zero_mem)`.
-/
theorem e_mem (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) : Fr.e a ∈ Fr.LamStd L :=
  mem_LamStd Fr (fun b => by rw [h_e_es]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem])
    (fun b => by rw [h_e_e]; exact M.L.O.zero_mem) 0 (by rw [prF_e_self]; rfl)
    (by rw [map_zero]; exact L.zero_mem)

/- English proof (translation)
The claim follows from `mem_LamStd Fr (fun b => by rw [h_es_es]; exact M.L.O.zero_mem) (fun b => by rw [h_es_e]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]) 0 (by rw [prF_es_self]; rfl) (by rw [map_zero]; exact L.zero_mem)`.
-/
theorem es_mem (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) : Fr.es a ∈ Fr.LamStd L :=
  mem_LamStd Fr (fun b => by rw [h_es_es]; exact M.L.O.zero_mem)
    (fun b => by rw [h_es_e]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]) 0
    (by rw [prF_es_self]; rfl) (by rw [map_zero]; exact L.zero_mem)

/- English proof (translation)
Rewrite using `[rho_mkW]`. Conclude with `mem_LamStd Fr (fun b => by rw [prF_es]; exact M.L.O.zero_mem) (fun b => by rw [prF_e]; exact M.L.O.zero_mem) ⟨Fr.prF y, prF_perp Fr y⟩ (prF_prF Fr y).symm (by rw [mkW_prF]; exact hy)`.
-/
theorem hyperbolicQuotientLift_mem_of_perp_mem {L : Submodule M.L.O (H.Wb Fr.f)} (y : ↥(H.perp (H.X Fr.f)))
    (hy : H.mkW Fr.f y ∈ L) : rho Fr (H.mkW Fr.f y) ∈ Fr.LamStd L := by
  rw [rho_mkW]
  exact mem_LamStd Fr (fun b => by rw [prF_es]; exact M.L.O.zero_mem)
    (fun b => by rw [prF_e]; exact M.L.O.zero_mem)
    ⟨Fr.prF y, prF_perp Fr y⟩ (prF_prF Fr y).symm (by rw [mkW_prF]; exact hy)

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ x`. Conclude with `hyperbolicQuotientLift_mem_of_perp_mem Fr y hx`.
-/
theorem rho_mem {L : Submodule M.L.O (H.Wb Fr.f)} {x : H.Wb Fr.f} (hx : x ∈ L) :
    rho Fr x ∈ Fr.LamStd L := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  exact hyperbolicQuotientLift_mem_of_perp_mem Fr y hx

/- English proof (translation)
Take `⟨G, hG⟩` from `hL.1`. Use `⟨(Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪ G.image (rho Fr), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Simplify using `only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union, Set.mem_range, Set.mem_image, Finset.mem_coe] at hv`.

Break down `hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨g, hg, rfl⟩` into its components or cases. Conclude with `e_mem Fr L a`. Conclude with `es_mem Fr L a`. Conclude with `rho_mem Fr (hG ▸ Submodule.subset_span hg)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨h1, h2, w, hw, hwL⟩`. Establish `hv : v = (∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a) + rho Fr (H.mkW Fr.f w)`. Rewrite using `[rho_mkW, hw, prF_prF]`. Simplify using `only [FrameD.prF]`. Normalize the expressions using the abelian group laws.

Rewrite using `[SetLike.mem_coe, hv]`. Use `Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) (Submodule.sum_mem _ fun a _ => ?_)) ?_` and prove the remaining obligations. Use `Submodule.smul_mem _ (⟨_, h1 a⟩ : M.L.O) (Submodule.subset_span (R := M.L.O) (s := (((Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪ G.image (rho Fr) : Finset V) : Set V)) (by simp : Fr.e a ∈ _))` as an intermediate fact. Conclude with `this`. Use `Submodule.smul_mem _ (⟨_, h2 a⟩ : M.L.O) (Submodule.subset_span (R := M.L.O) (s := (((Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪ G.image (rho Fr) : Finset V) : Set V)) (by simp : Fr.es a ∈ _))` as an intermediate fact.

Conclude with `this`. Establish `hm : H.mkW Fr.f w ∈ Submodule.span M.L.O (G : Set (H.Wb Fr.f))` using `hG.symm ▸ hwL`. Establish `h3` using `Submodule.mem_map_of_mem (f := (rho Fr).restrictScalars M.L.O) hm`. Rewrite `h3` using `[← Submodule.span_image]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg))`.
-/
theorem LamStd_fg {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) : (Fr.LamStd L).FG := by
  obtain ⟨G, hG⟩ := hL.1
  refine ⟨(Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪ G.image (rho Fr), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro v hv
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range, Set.mem_image, Finset.mem_coe] at hv
    rcases hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨g, hg, rfl⟩
    · exact e_mem Fr L a
    · exact es_mem Fr L a
    · exact rho_mem Fr (hG ▸ Submodule.subset_span hg)
  · refine Submodule.span_le.2 ?_
    rintro v ⟨h1, h2, w, hw, hwL⟩
    have hv : v = (∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a) +
        rho Fr (H.mkW Fr.f w) := by
      rw [rho_mkW, hw, prF_prF]; simp only [FrameD.prF]; abel
    rw [SetLike.mem_coe, hv]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_)
      (Submodule.sum_mem _ fun a _ => ?_)) ?_
    · have := Submodule.smul_mem _ (⟨_, h1 a⟩ : M.L.O)
        (Submodule.subset_span (R := M.L.O) (s := (((Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪
          G.image (rho Fr) : Finset V) : Set V)) (by simp : Fr.e a ∈ _))
      exact this
    · have := Submodule.smul_mem _ (⟨_, h2 a⟩ : M.L.O)
        (Submodule.subset_span (R := M.L.O) (s := (((Finset.univ.image Fr.e ∪ Finset.univ.image Fr.es) ∪
          G.image (rho Fr) : Finset V) : Set V)) (by simp : Fr.es a ∈ _))
      exact this
    · have hm : H.mkW Fr.f w ∈ Submodule.span M.L.O (G : Set (H.Wb Fr.f)) := hG.symm ▸ hwL
      have h3 := Submodule.mem_map_of_mem (f := (rho Fr).restrictScalars M.L.O) hm
      rw [← Submodule.span_image] at h3
      refine Submodule.span_mono ?_ h3
      rintro _ ⟨g, hg, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg))

/- English proof (translation)
Take `⟨G, hG⟩` from `hL.1`. Set `ψ : H.Wb Fr.f →ₗ[E] E` to `Submodule.liftQ _ (hl H (x : V) ∘ₗ (H.perp (H.X Fr.f)).subtype) (by`. Introduce `w hw`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply] at hw`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hl_apply]`.

Conclude with `h_eq_zero_comm H (x.2 _ hw))`. Establish `hψ : ∀ y : ↥(H.perp (H.X Fr.f)), ψ (H.mkW Fr.f y) = H.h y x` using `fun y => rfl`. Take `⟨a, ha, hint⟩` from `exists_fin M.L (G.image ψ)`. Establish `hcF : algebraMap 𝒪[F] E a = algebraMap F E (a : F)` using `IsScalarTower.algebraMap_apply 𝒪[F] F E a`. Establish `ha' : (a : F) ≠ 0` using `fun h => ha (Subtype.ext h)`.

Establish `hc : IsUnit (algebraMap 𝒪[F] E a)` using `by rw [hcF]; exact (Ne.isUnit ha').map _`. Establish `hcj : M.L.cj (algebraMap 𝒪[F] E a) = algebraMap 𝒪[F] E a` using `by rw [hcF]; exact M.L.cj.commutes _`. Establish `key : ∀ z ∈ L, algebraMap 𝒪[F] E a * ψ z ∈ M.L.O`. Introduce `z hz`. Rewrite `hz` using `[← hG]`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact hint _ (Finset.mem_image_of_mem _ hz)`. Consider the case `zero => simp`. Consider the case `add z z' _ _ h h' => rw [map_add, mul_add]`. Conclude with `M.L.O.add_mem h h'`.

Consider the case `smul o z _ h`. Rewrite using `[LinearMap.map_smul_of_tower]`. Use `show algebraMap 𝒪[F] E a * ((o : E) * ψ z) ∈ M.L.O`. Rewrite using `[mul_left_comm]`. Conclude with `M.L.O.mul_mem o.2 h`.

Use `⟨algebraMap 𝒪[F] E a, hc, (hL.2.1 _).2 fun y hy => ?_⟩` and prove the remaining obligations. Use `show H.h (algebraMap 𝒪[F] E a • (x : V)) y ∈ M.L.O`. Rewrite using `[H.h_smul_left, H.h_herm y (x : V), ← hcj, ← map_mul]`. Use `key _ hy` as an intermediate fact. Rewrite `this` using `[hψ]`.

Conclude with `cj_mem M.L this`.
-/
theorem exists_unit_smul {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L)
    (x : ↥(H.perp (H.X Fr.f))) : ∃ c : E, IsUnit c ∧ H.mkW Fr.f (c • x) ∈ L := by
  obtain ⟨G, hG⟩ := hL.1
  let ψ : H.Wb Fr.f →ₗ[E] E := Submodule.liftQ _ (hl H (x : V) ∘ₗ (H.perp (H.X Fr.f)).subtype) (by
    intro w hw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hw
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hl_apply]
    exact h_eq_zero_comm H (x.2 _ hw))
  have hψ : ∀ y : ↥(H.perp (H.X Fr.f)), ψ (H.mkW Fr.f y) = H.h y x := fun y => rfl
  obtain ⟨a, ha, hint⟩ := exists_fin M.L (G.image ψ)
  have hcF : algebraMap 𝒪[F] E a = algebraMap F E (a : F) := IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have ha' : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  have hc : IsUnit (algebraMap 𝒪[F] E a) := by rw [hcF]; exact (Ne.isUnit ha').map _
  have hcj : M.L.cj (algebraMap 𝒪[F] E a) = algebraMap 𝒪[F] E a := by rw [hcF]; exact M.L.cj.commutes _
  have key : ∀ z ∈ L, algebraMap 𝒪[F] E a * ψ z ∈ M.L.O := by
    intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hint _ (Finset.mem_image_of_mem _ hz)
    | zero => simp
    | add z z' _ _ h h' => rw [map_add, mul_add]; exact M.L.O.add_mem h h'
    | smul o z _ h =>
      rw [LinearMap.map_smul_of_tower]
      show algebraMap 𝒪[F] E a * ((o : E) * ψ z) ∈ M.L.O
      rw [mul_left_comm]
      exact M.L.O.mul_mem o.2 h
  refine ⟨algebraMap 𝒪[F] E a, hc, (hL.2.1 _).2 fun y hy => ?_⟩
  show H.h (algebraMap 𝒪[F] E a • (x : V)) y ∈ M.L.O
  rw [H.h_smul_left, H.h_herm y (x : V), ← hcj, ← map_mul]
  have := key _ hy
  rw [hψ] at this
  exact cj_mem M.L this

/- English proof (translation)
Use `Submodule.eq_top_iff'.2 fun v => ?_` and prove the remaining obligations. Establish `hmem : ∀ u ∈ Fr.LamStd L, u ∈ Submodule.span E (Fr.LamStd L : Set V)` using `fun u hu => Submodule.subset_span hu`. Establish `hp : Fr.prF v ∈ Submodule.span E (Fr.LamStd L : Set V)`. Take `⟨c, hc, hcL⟩` from `exists_unit_smul Fr hL ⟨Fr.prF v, prF_perp Fr v⟩`. Establish `h1` using `hmem _ (rho_mem Fr hcL)`.

Rewrite `h1` using `[rho_mkW, Submodule.coe_smul, prF_smul, prF_prF]`. Establish `h2` using `Submodule.smul_mem _ (↑hc.unit⁻¹ : E) h1`. Rewrite `h2` using `[smul_smul, hc.val_inv_mul, one_smul]`. Then use the resulting hypothesis. Establish `hv : v = (∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a) + Fr.prF v`. Simplify using `only [FrameD.prF]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hv]`. Conclude with `Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hmem _ (e_mem Fr L a))) (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hmem _ (es_mem Fr L a)))) hp`.
-/
theorem LamStd_span {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) :
    Submodule.span E (Fr.LamStd L : Set V) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun v => ?_
  have hmem : ∀ u ∈ Fr.LamStd L, u ∈ Submodule.span E (Fr.LamStd L : Set V) :=
    fun u hu => Submodule.subset_span hu
  have hp : Fr.prF v ∈ Submodule.span E (Fr.LamStd L : Set V) := by
    obtain ⟨c, hc, hcL⟩ := exists_unit_smul Fr hL ⟨Fr.prF v, prF_perp Fr v⟩
    have h1 := hmem _ (rho_mem Fr hcL)
    rw [rho_mkW, Submodule.coe_smul, prF_smul, prF_prF] at h1
    have h2 := Submodule.smul_mem _ (↑hc.unit⁻¹ : E) h1
    rwa [smul_smul, hc.val_inv_mul, one_smul] at h2
  have hv : v = (∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a) + Fr.prF v := by
    simp only [FrameD.prF]; abel
  rw [hv]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hmem _ (e_mem Fr L a)))
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hmem _ (es_mem Fr L a)))) hp

/- English proof (translation)
Take `⟨-, -, ⟨n, -, -, hn⟩, -⟩` from `ht`. Rewrite using `[hn]`. Conclude with `⟨img_fg n (LamStd_fg P.A d.hL), img_span n (LamStd_span P.A d.hL)⟩`.
-/
theorem term_lat {P : FPair H r} {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    t.abelian₂.FG ∧ Submodule.span E (t.abelian₂ : Set V) = ⊤ := by
  obtain ⟨-, -, ⟨n, -, -, hn⟩, -⟩ := ht
  rw [hn]
  exact ⟨img_fg n (LamStd_fg P.A d.hL), img_span n (LamStd_span P.A d.hL)⟩

end GlobalTheory.TermLat

namespace GlobalTheory.GenMass.Fibre

/- English proof (translation)
Introduce `_ _ _ _ _ _ ht` and use `GlobalTheory.TermLat.term_lat ht`.
-/
theorem termLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ :=
  fun _ _ _ _ _ _ ht => GlobalTheory.TermLat.term_lat ht

end GlobalTheory.GenMass.Fibre
