import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SelfDualPI
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def latB (B : GL (Fin n) E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | ∀ a, (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range}
  add_mem' := by
    intro x y hx hy a
    rw [Matrix.mulVec_add]
    exact add_mem (hx a) (hy a)
  zero_mem' := by
    intro a
    rw [Matrix.mulVec_zero]
    exact zero_mem _
  smul_mem' := by
    intro c x hx a
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨c, rfl⟩ (hx a)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latB (B : GL (Fin n) E) (x : Fin n → E) :
    x ∈ latB B ↔ ∀ a, (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

/- English proof (translation)
Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `zero_mem _`.
-/
theorem single_int (j a : Fin n) : (Pi.single j 1 : Fin n → E) a ∈ (algebraMap (𝓞 E) E).range := by
  by_cases h : a = j
  · subst h; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

/- English proof (translation)
Introduce `a`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `single_int j a`.
-/
theorem latB_col (B : GL (Fin n) E) (j : Fin n) : ((B : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single j 1) ∈ latB B := by
  intro a
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact single_int j a

/- English proof (translation)
Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem entry_eq {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    M a b = (M *ᵥ Pi.single b 1) a := by
  rw [Matrix.mulVec_single_one]; rfl

variable (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ * ((c : E ⊗[F] v.adicCompletion F) * y j) = (c : E ⊗[F] v.adicCompletion F) * (_ * y j)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulVec_smul_int (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (c : intV E v)
    (y : Fin n → E ⊗[F] v.adicCompletion F) : M *ᵥ (c • y) = c • (M *ᵥ y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * ((c : E ⊗[F] v.adicCompletion F) * y j) = (c : E ⊗[F] v.adicCompletion F) * (_ * y j)
  ring

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)`.
-/
theorem incl_int (b : 𝓞 E) : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b) ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec _ _ _ _).symm`.
-/
theorem incl_mulVec (M : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    M.map (inclE (F := F) (v.adicCompletion F)) *ᵥ (fun i => inclE (F := F) (v.adicCompletion F) (y i)) =
      fun i => inclE (F := F) (v.adicCompletion F) ((M *ᵥ y) i) := by
  funext i
  exact (RingHom.map_mulVec _ _ _ _).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨y, hy, rfl⟩` from `hy`.

Introduce `a`. Rewrite using `[← map_inv]`. Establish `e` using `incl_mulVec v ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) y`. Establish `e' : ((bc (inclE (F` using `F) (v.adicCompletion F)) B⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => inclE (F := F) (v.adicCompletion F) (y i)) = fun i => inclE (F := F) (v.adicCompletion F) ((((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) …`. Rewrite using `[e']`.

Take `⟨b, hb⟩` from `hy a`. Use `show inclE (F := F) (v.adicCompletion F) ((((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) a) ∈ intV E v`. Rewrite using `[← hb]`. Conclude with `incl_int v b`. Consider the case `zero => intro a`.

Rewrite using `[Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => intro a`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem (hy a) (hz a)`.

Consider the case `smul c y _ hy`. Introduce `a`. Rewrite using `[mulVec_smul_int]`. Conclude with `mul_mem c.2 (hy a)`. Introduce `h set t := (((bc (inclE (F := F) (v.adicCompletion F)) B)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x with ht`.

Establish `hx : x = ((bc (inclE (F` using `F) (v.adicCompletion F)) B : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ t := by`. Rewrite using `[ht, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hs : ((bc (inclE (F` using `F) (v.adicCompletion F)) B : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ t = ∑ a, (⟨t a, h a⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) (((B : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single a 1) i)) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show inclE (F := F) (v.adicCompletion F) ((B : Matrix (Fin n) (Fin n) E) i a) * t a = t a * inclE (F := F) (v.adicCompletion F) (((B : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single a 1) i)`. Rewrite using `[← entry_eq, mul_comm]`. Rewrite using `[hx, hs]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, latB_col B a, rfl⟩)`.
-/
theorem mem_latS_latB (B : GL (Fin n) E) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latB B) ↔
      ∀ a, ((((bc (inclE (F := F) (v.adicCompletion F)) B)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x) a ∈ intV E v := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      intro a
      rw [← map_inv]
      have e := incl_mulVec v ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) y
      have e' : ((bc (inclE (F := F) (v.adicCompletion F)) B⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => inclE (F := F) (v.adicCompletion F) (y i)) =
          fun i => inclE (F := F) (v.adicCompletion F) ((((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) i) := e
      rw [e']
      obtain ⟨b, hb⟩ := hy a
      show inclE (F := F) (v.adicCompletion F) ((((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) a) ∈ intV E v
      rw [← hb]
      exact incl_int v b
    | zero => intro a; rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => intro a; rw [Matrix.mulVec_add]; exact add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [mulVec_smul_int]
      exact mul_mem c.2 (hy a)
  · intro h
    set t := (((bc (inclE (F := F) (v.adicCompletion F)) B)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x with ht
    have hx : x = ((bc (inclE (F := F) (v.adicCompletion F)) B : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ t := by
      rw [ht, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hs : ((bc (inclE (F := F) (v.adicCompletion F)) B : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ t =
        ∑ a, (⟨t a, h a⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F)
          (((B : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single a 1) i)) := by
      funext i
      rw [Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      show inclE (F := F) (v.adicCompletion F) ((B : Matrix (Fin n) (Fin n) E) i a) * t a =
        t a * inclE (F := F) (v.adicCompletion F) (((B : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single a 1) i)
      rw [← entry_eq, mul_comm]
    rw [hx, hs]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, latB_col B a, rfl⟩)

/- English proof (translation)
Rewrite using `[map_natCast]`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_natCast, smul_eq_mul]`.
-/
theorem natCast_smul' (s : ℕ) (x : Fin n → E) : (algebraMap (𝓞 F) (𝓞 E) (s : 𝓞 F)) • x = (s : E) • x := by
  rw [map_natCast]
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_natCast, smul_eq_mul]

/- English proof (translation)
Establish `h1 : ¬ p ∣ 1` using `fun h => hp.ne_one (Nat.dvd_one.1 h)`. Use `le_antisymm (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_latS_mono v fun x hx => ?_) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_latS_mono v fun x hx => ?_)` and prove the remaining obligations. Take `⟨s, hs, h⟩` from `(hB x).1 ⟨1, h1, by rw [Nat.cast_one, one_smul]; exact hx⟩`. Use `⟨(s : 𝓞 F), natCast_notMem v hp hv hs, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[natCast_smul', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`.

Conclude with `h a`. Take `⟨s, hs, h⟩` from `(hB x).2 ⟨1, h1, fun a => by rw [Nat.cast_one, one_mul]; exact hx a⟩`. Conclude with `⟨(s : 𝓞 F), natCast_notMem v hp hv hs, by rw [natCast_smul']; exact h⟩`.
-/
theorem latS_of_locBasis {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 F) ∈ v.asIdeal) (Ld : Submodule (𝓞 E) (Fin n → E))
    (B : GL (Fin n) E) (hB : IsLocBasis p (Ld : Set (Fin n → E)) B) :
    latS (F := F) (v.adicCompletion F) (intV E v) Ld = latS (F := F) (v.adicCompletion F) (intV E v) (latB B) := by
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  refine le_antisymm (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_latS_mono v fun x hx => ?_) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_latS_mono v fun x hx => ?_)
  · obtain ⟨s, hs, h⟩ := (hB x).1 ⟨1, h1, by rw [Nat.cast_one, one_smul]; exact hx⟩
    refine ⟨(s : 𝓞 F), natCast_notMem v hp hv hs, fun a => ?_⟩
    rw [natCast_smul', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact h a
  · obtain ⟨s, hs, h⟩ := (hB x).2 ⟨1, h1, fun a => by rw [Nat.cast_one, one_mul]; exact hx a⟩
    exact ⟨(s : 𝓞 F), natCast_notMem v hp hv hs, by rw [natCast_smul']; exact h⟩

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `[sigR, inclE]`.
-/
theorem sigR_incl (a : E) : sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) a) =
    inclE (F := F) (v.adicCompletion F) (σ a) := by
  simp [sigR, inclE]

/- English proof (translation)
Establish `h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b))` using `(RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)`. Conclude with `⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩`.
-/
theorem sig_int (b : 𝓞 E) : σ (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 E) E).range := by
  have h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) :=
    (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩

/- English proof (translation)
Establish `key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F))`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Use `show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v`. Rewrite using `[sigR_incl]`.

Take `⟨c, hc⟩` from `sig_int σ b`. Rewrite using `[← hc]`. Conclude with `incl_int v c`. Use `show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v`. Simplify using `only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]`.

Conclude with `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`. Conclude with `key hs`.
-/
theorem sigR_mem {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ intV E v) : sigR σ (v.adicCompletion F) s ∈ intV E v := by
  have key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v
      rw [sigR_incl]
      obtain ⟨c, hc⟩ := sig_int σ b
      rw [← hc]
      exact incl_int v c
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v
      simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

/- English proof (translation)
Simplify using `only [hform, map_sum, map_mul, sigR_incl, Matrix.map_apply]`. Both sides reduce to the same expression.
-/
theorem hform_incl (y x : Fin n → E) :
    hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      (fun i => inclE (F := F) (v.adicCompletion F) (y i)) (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      inclE (F := F) (v.adicCompletion F) (hform (σ : E →+* E) J y x) := by
  simp only [hform, map_sum, map_mul, sigR_incl, Matrix.map_apply]
  rfl

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨y, hy, rfl⟩` from `hu`. Rewrite using `[hform_incl]`. Take `⟨b, hb⟩` from `hx y hy`.

Rewrite using `[← hb]`. Conclude with `incl_int v b`. Consider the case `zero => rw [Formalism.UG.P.csDual_hform_zero_left]`. Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw => rw [Formalism.UG.P.csDual_hform_add_left]`.

Conclude with `add_mem hu hw`. Consider the case `smul s u _ hu`. Rewrite using `[Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]`. Conclude with `mul_mem (sigR_mem v σ s.2) hu`.
-/
theorem pair_int (M : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (hx : x ∈ dualSet (σ : E →+* E) J M)
    (u : Fin n → E ⊗[F] v.adicCompletion F) (hu : u ∈ latS (F := F) (v.adicCompletion F) (intV E v) M) :
    hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) u
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ intV E v := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    rw [hform_incl]
    obtain ⟨b, hb⟩ := hx y hy
    rw [← hb]
    exact incl_int v b
  | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
  | add u w _ _ hu hw => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem hu hw
  | smul s u _ hu =>
    rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
    exact mul_mem (sigR_mem v σ s.2) hu

variable {σ J}

/- English proof (translation)
Establish `hyU : cT (sigR σ (v.adicCompletion F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) * J.map (inclE (F` using `F) (v.adicCompletion F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = J.map (inclE (F := F) (v.adicCompletion F)) := hy`. Establish `key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F, hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F` using `F) (v.adicCompletion F))) z (((y⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x) = hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) * …`. Introduce `z x`. Establish `e` using `Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) z (((y⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x)`. Rewrite `e` using `[hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `e.symm`. Introduce `x`. Establish `h0` using `(hyl x).trans (h _)`. Use `h0.trans ⟨fun H z hz => ?_, fun H z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `H _ ((hyl z).1 hz)`.

Rewrite `h1` using `[key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `h1`. Rewrite using `[key]`. Use `H _ ((hyl _).2 ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `hz`.
-/
theorem selfDual_move {Lb Lc : Submodule (𝓞 E) (Fin n → E)} (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lc ↔
      ((y⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈
        latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (h : SelfDualAt σ J v Lb) : SelfDualAt σ J v Lc := by
  have hyU : cT (sigR σ (v.adicCompletion F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy
  have key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z
        (((y⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x) =
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
        ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z) x := by
    intro z x
    have e := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) z
      (((y⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e
    exact e.symm
  intro x
  have h0 := (hyl x).trans (h _)
  refine h0.trans ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · have h1 := H _ ((hyl z).1 hz)
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1
  · rw [key]
    refine H _ ((hyl _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hz

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `(hsd _).2 fun z hz => pair_int v σ J Lc y (hLd ▸ hy) z hz`. Conclude with `Submodule.span_mono (Set.image_mono hle)`.
-/
theorem latS_dual_eq {Lc Ld : Submodule (𝓞 E) (Fin n → E)} (hLd : (Ld : Set (Fin n → E)) = dualSet (σ : E →+* E) J Lc)
    (hle : Lc ≤ Ld) (hsd : SelfDualAt σ J v Lc) :
    latS (F := F) (v.adicCompletion F) (intV E v) Ld = latS (F := F) (v.adicCompletion F) (intV E v) Lc := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨y, hy, rfl⟩
    exact (hsd _).2 fun z hz => pair_int v σ J Lc y (hLd ▸ hy) z hz
  · exact Submodule.span_mono (Set.image_mono hle)

end Formalism.L2.G.RelativeIndexFlags
