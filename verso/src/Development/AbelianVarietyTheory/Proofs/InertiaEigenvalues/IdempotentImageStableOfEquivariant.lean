import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

/- English proof (translation)
Establish `hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B`. Introduce `i m hm`. Use `Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr (hT i n hn)`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro y x _ hx _ _`. Simplify using `[hx]`.

Consider the case `insert a s ha ih`. Introduce `y x hy hx hxB hev`. Rewrite `hx` using `[Finset.sum_insert ha]`. Break down `hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩` into its components or cases. Conclude with `ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev`.

Establish `h1 : T i x - e i • x ∈ I • B`. Use `ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB)) (fun j => ?_)` and prove the remaining obligations. Break down `hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩` into its components or cases. Use `left`. Simplify using `[h0]`.

Use `right`. Use `⟨e', fun j => ?_, hu'⟩` and prove the remaining obligations. Rewrite using `[he' i, ← sub_smul, map_smul, he' j, smul_comm]`. Rewrite using `[hx, map_add, smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.

Establish `h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) = (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x))`. Simplify using `only [map_sub, map_smul]`. Use `module`. Rewrite using `[h2]`. Conclude with `add_mem (Submodule.smul_mem _ _ (hev j)) (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))`.

Establish `h3 : (ev i - e i) • x ∈ I • B`. Establish `: (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x)` using `by module`. Rewrite using `[this]`. Conclude with `sub_mem h1 (hev i)`. Take `⟨u, hu⟩` from `hu`.

Establish `h4` using `Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3`. Rewrite `h4` using `[← hu, smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]
        · rw [hx, map_add, smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply]`. Unfold `eG`. Rewrite using `[← map_mul, Y.eAlg_idem]`.
-/
theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← Module.End.mul_apply]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

/- English proof (translation)
Unfold `eG`. Proceed by induction on `Y.eAlg i b using MonoidAlgebra.induction_on with`. Consider the case `of g`. Simplify using `only [MonoidAlgebra.lift_of]`. Conclude with `LinearMap.congr_fun (h g) x`.

Consider the case `add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]`. Consider the case `smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]`.
-/
theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Use `⟨T y, ?_, eG_comm Y i j b T h y⟩` and prove the remaining obligations. Simplify using `only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢`. Introduce `u`. Use `LinearMap.congr_fun (h u) y` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, hy u, map_smul]`.
-/
theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]

/- English proof (translation)
Introduce `D N X Y E hI hA hS hss i hi j hj b x hxB hxm ev hev`. Assume the negation of the conclusion as `hno`. Apply `hxm` to reduce the goal to its premises. Establish `hcomm` using `((hA i hi b).2 j hj).1`. Establish `hM` using `(hI i hi j hj b).2.2.2.1`.

Establish `hx : x ∈ ⨆ ev, Eigsp Y i j b ev` using `by rw [hss i j b hi]; trivial`. Take `⟨f, hf, hfx⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx`. Establish `hex : eG Y i j b x = x`. Take `⟨y, -, hy⟩` from `hxB.2`. Rewrite using `[← hy, eG_idem]`.

Use `mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _ (fun p => hkO Y i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support (fun a => eG Y i j b (f a)) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)` and prove the remaining obligations. Conclude with `⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant Y i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩`. Distinguish the cases in `h0 : eG Y i j b (f a) = 0`. Conclude with `Or.inl h0`. Use `right`.

Establish `heig : ∀ k P, HkIdx i k P → Y.hkF i j b k P (eG Y i j b (f a)) = a k P • eG Y i j b (f a)`. Introduce `k P hk`. Establish `h1` using `hf a`. Simplify using `only [Eigsp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1`. Rewrite using `[← eG_comm Y i j b _ (fun g => hcomm g _ _ hk), h1 k P hk, map_smul]`.

Take `⟨s, hs1, hs2, hs3⟩` from `hS i j b _ a h0 (eG_idem Y i j b (f a)) (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)`. Use `⟨fun p => X.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y.hkF i j b _ _ _ = _`. Rewrite using `[heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]`. Assume the negation of the conclusion as `hu`.

Use `hno ⟨s, hs1, hs2, fun k P hk => ?_⟩` and prove the remaining obligations. Conclude with `fun h => hu ⟨⟨(k, P), hk⟩, h⟩`. Rewrite using `[← hex, ← map_sum]`. Use `congr 1`. Conclude with `hfx.symm`.
-/
theorem admT3_of_semisimple : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y), Formalism.MainNotions.IntegralHeckeForms.IsotypicPartsInternalDirectSum Y E → Formalism.MainNotions.IntegralHeckeForms.GroupAlgebraIntegrality Y → Y.sig_all → (∀ i j b, X.NonzeroIndexPlace i → ⨆ ev, Formalism.MainNotions.IntegralHeckeForms.Eigsp Y i j b ev = ⊤) → Formalism.MainNotions.IntegralHeckeForms.GoodLatticePoints Y := by
  intro D N X Y E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx : x ∈ ⨆ ev, Eigsp Y i j b ev := by rw [hss i j b hi]; trivial
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  have hex : eG Y i j b x = x := by
    obtain ⟨y, -, hy⟩ := hxB.2
    rw [← hy, eG_idem]
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO Y i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => eG Y i j b (f a)) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant Y i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : eG Y i j b (f a) = 0
    · exact Or.inl h0
    right
    have heig : ∀ k P, HkIdx i k P → Y.hkF i j b k P (eG Y i j b (f a)) = a k P • eG Y i j b (f a) := by
      intro k P hk
      have h1 := hf a
      simp only [Eigsp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      rw [← eG_comm Y i j b _ (fun g => hcomm g _ _ hk), h1 k P hk, map_smul]
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 (eG_idem Y i j b (f a))
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => X.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change Y.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · rw [← hex, ← map_sum]
    congr 1
    exact hfx.symm

end GlobalTheory.EigRed
