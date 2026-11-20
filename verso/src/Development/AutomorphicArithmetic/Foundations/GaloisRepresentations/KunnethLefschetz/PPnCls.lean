import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
import Development.EtaleCohomology.EtaleTrace.LPdCut
import Development.EtaleCohomology.EtaleTrace.LEmptyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz.PnClsPf

/- English proof (translation)
Use `smoothOfRelativeDimension_comp (n := 0) (m := n) i f` as an intermediate fact. Simplify using `using this`.
-/
private theorem sm_open {A B C : Scheme.{0}} (i : A ⟶ B) [IsOpenImmersion i] (f : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) : SmoothOfRelativeDimension n (i ≫ f) := by
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) i f
  simpa using this

/- English proof (translation)
Establish `hE` using `LEmptyPf.LEmpty_of hI.a5 hI.a9`. Use `haveI h1 : ∀ k, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => hE _ X hX _ n`. Use `haveI h2 : Subsingleton (Hl l (sch.obj X) n 0) := by show Subsingleton (HlSub l (sch.obj X) n 0) infer_instance`. Use `show Subsingleton (ℚ_[l] ⊗[ℤ_[l]] Hl l (sch.obj X) n 0)`. Use `infer_instance`.
-/
private theorem empty_v (l : ℕ) [Fact l.Prime] (hI : In) (X : Scheme.{0}) (hX : IsEmpty X) (n : ℤ) :
    Subsingleton (V l X n) := by
  have hE := LEmptyPf.LEmpty_of hI.a5 hI.a9
  haveI h1 : ∀ k, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => hE _ X hX _ n
  haveI h2 : Subsingleton (Hl l (sch.obj X) n 0) := by
    show Subsingleton (HlSub l (sch.obj X) n 0)
    infer_instance
  show Subsingleton (ℚ_[l] ⊗[ℤ_[l]] Hl l (sch.obj X) n 0)
  infer_instance

/- English proof (translation)
Establish `key : ∀ z : Ht q (sch.obj A) n 0, pull (ZMod q) (sch.map e.hom) (tw q 0) n (pull (ZMod q) (sch.map e.inv) (tw q 0) n z) = z`. Introduce `z`. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]`. Prove the components needed by the constructor for the conclusion. Introduce `x y`.

Rewrite using `[← key x, ← key y, Subsingleton.elim (pull (ZMod q) (sch.map e.inv) (tw q 0) n x) (pull (ZMod q) (sch.map e.inv) (tw q 0) n y)]`.
-/
private theorem iso_sub {A B : Scheme.{0}} (e : A ≅ B) (q : ℕ) (n : ℤ)
    (h : Subsingleton (Ht q (sch.obj B) n 0)) : Subsingleton (Ht q (sch.obj A) n 0) := by
  have key : ∀ z : Ht q (sch.obj A) n 0,
      pull (ZMod q) (sch.map e.hom) (tw q 0) n (pull (ZMod q) (sch.map e.inv) (tw q 0) n z) = z := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, pull_id]
  constructor
  intro x y
  rw [← key x, ← key y,
    Subsingleton.elim (pull (ZMod q) (sch.map e.inv) (tw q 0) n x)
      (pull (ZMod q) (sch.map e.inv) (tw q 0) n y)]

end UpperTheory.Gal.KunnethLefschetz.PnClsPf

open UpperTheory.Gal.KunnethLefschetz.PnClsPf in
/- English proof (translation)
Introduce `hI hF hH hO l _ k _ _ hl hR hL hA hG`. Take `⟨gq⟩` from `hG`. Establish `one_ne : oneV l (S k) ≠ 0`. Introduce `h0`. Take `⟨r, -, hr⟩` from `Low.line hL 0`.

Establish `h1` using `hr 0 (by simp)`. Establish `h2` using `hr 1 (by simp [h0])`. Conclude with `one_ne_zero (h2.trans h1.symm)`. Establish `key : ∀ d : ℕ, ∃ t : Pt (PNto k d), IsClosedImmersion t.1 ∧ ∃ U : (PN k d).Opens, Off t.1 U ∧ ∃ z : V l (PN k d) (2 * (d : ℤ)), z ≠ 0 ∧ pb l U.ι (2 * (d : ℤ)) z = 0`. Introduce `d`.

Proceed by induction on `d with`. Consider the case `zero => haveI := (hF k 0).2.2.2`. Use `⟨⟨inv (PNto k 0), IsIso.inv_hom_id _⟩, inferInstance, ⊥, ?_, ?_⟩` and prove the remaining obligations. Use `show ((⊥ : (PN k 0).Opens) : Set (PN k 0)) = (Set.range (inv (PNto k 0)).base)ᶜ`. Rewrite using `[Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso (inv (PNto k 0)).base).2]`.

Simplify using the standard rewrite rules. Use `⟨oneV l (PN k 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `one_ne` to reduce the goal to its premises. Establish `hu` using `Ring.one_nat hR (inv (PNto k 0)) (LPdCut.unit_of (PNto k 0) (isUnit_iff_ne_zero.mpr hl))`.

Rewrite using `[← hu]`. Express the relevant statement in the definitionally equal form `pb l (inv (PNto k 0)) 0 (oneV l (PN k 0)) = 0`. Rewrite using `[h0, map_zero]`. Establish `he : IsEmpty ((⊥ : (PN k 0).Opens) : Scheme)` using `⟨fun x => by simpa using x.2⟩ haveI := empty_v l hI ((⊥ : (PN k 0).Opens) : Scheme) he (2 * ((0 : ℕ) : ℤ))`. Conclude with `Subsingleton.elim _ _`.

Consider the case `succ d ih`. Take `⟨t, htc, U, hU, z, hz, hzU⟩` from `ih`. Take `⟨ι, U0, hιc, hιp, hoff0, ⟨eU0⟩⟩` from `hH k d`. Use `haveI := htc`. Use `haveI := hιc`.

Set `t' : Pt (PNto k (d + 1))` to `Pt.map ι hιp t`. Establish `htc' : IsClosedImmersion t'.1` using `by show IsClosedImmersion (t.1 ≫ ι) infer_instance`. Take `⟨U', hU'⟩` from `hO.1 t'.1 htc'`. Establish `hP : IsPair 1 d (PNto k (d + 1)) ι` using `⟨hιc, (hF k (d + 1)).1.2, by rw [hιp]; exact (hF k d).1.2⟩`. Establish `hn : 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨t', htc', U', hU', gq.g hP hn z, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hz` to reduce the goal to its premises.

Establish `hinj` using `gq.inj hP hn U0 hoff0 (fun j => iso_sub eU0 (l ^ j) _ (hA j (d + 1) _ (by push_cast; omega)))`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Establish `hinj : Function.Injective ι.base` using `(IsClosedImmersion.base_closed ι).injective`. Establish `hVU : ι ⁻¹ᵁ U' = U`.

Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Rewrite using `[hU]`. Use `show ι.base ⁻¹' (U' : Set (PN k (d + 1))) = _`. Rewrite using `[hU']`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, t', Pt.map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨y, rfl⟩`. Conclude with `h ⟨y, rfl⟩`. Introduce and unpack `h ⟨y, hy⟩`.

Apply `h` to reduce the goal to its premises. Use `⟨y, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Both sides reduce to the same expression. Substitute `hVU` using the available equality.

Establish `hP' : IsPair 1 d (U'.ι ≫ PNto k (d + 1)) (ι ∣_ U')`. Use `⟨inferInstance, sm_open U'.ι _ _ (hF k (d + 1)).1.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc, hιp]`. Conclude with `sm_open _ _ _ (hF k d).1.2`. Rewrite using `[gq.nat hP' hP U'.ι (ι ⁻¹ᵁ U').ι rfl (isPullback_morphismRestrict ι U') hn z, hzU, map_zero]`.

Introduce `d`. Take `⟨t, -, U, hU, z, hz, hzU⟩` from `key d`. Conclude with `⟨t, U, z, hU, hz, hzU⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.pnCls_holds :
    UpperTheory.Gal.KunnethLefschetz.PnCls := by
  intro hI hF hH hO l _ k _ _ hl hR hL hA hG
  obtain ⟨gq⟩ := hG
  have one_ne : oneV l (S k) ≠ 0 := by
    intro h0
    obtain ⟨r, -, hr⟩ := Low.line hL 0
    have h1 := hr 0 (by simp)
    have h2 := hr 1 (by simp [h0])
    exact one_ne_zero (h2.trans h1.symm)
  have key : ∀ d : ℕ, ∃ t : Pt (PNto k d), IsClosedImmersion t.1 ∧
      ∃ U : (PN k d).Opens, Off t.1 U ∧
        ∃ z : V l (PN k d) (2 * (d : ℤ)), z ≠ 0 ∧ pb l U.ι (2 * (d : ℤ)) z = 0 := by
    intro d
    induction d with
    | zero =>
      haveI := (hF k 0).2.2.2
      refine ⟨⟨inv (PNto k 0), IsIso.inv_hom_id _⟩, inferInstance, ⊥, ?_, ?_⟩
      · show ((⊥ : (PN k 0).Opens) : Set (PN k 0)) = (Set.range (inv (PNto k 0)).base)ᶜ
        rw [Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso (inv (PNto k 0)).base).2]
        simp
      · refine ⟨oneV l (PN k 0), ?_, ?_⟩
        · intro h0
          apply one_ne
          have hu := Ring.one_nat hR (inv (PNto k 0))
            (LPdCut.unit_of (PNto k 0) (isUnit_iff_ne_zero.mpr hl))
          rw [← hu]
          change pb l (inv (PNto k 0)) 0 (oneV l (PN k 0)) = 0
          rw [h0, map_zero]
        · have he : IsEmpty ((⊥ : (PN k 0).Opens) : Scheme) := ⟨fun x => by simpa using x.2⟩
          haveI := empty_v l hI ((⊥ : (PN k 0).Opens) : Scheme) he (2 * ((0 : ℕ) : ℤ))
          exact Subsingleton.elim _ _
    | succ d ih =>
      obtain ⟨t, htc, U, hU, z, hz, hzU⟩ := ih
      obtain ⟨ι, U0, hιc, hιp, hoff0, ⟨eU0⟩⟩ := hH k d
      haveI := htc
      haveI := hιc
      let t' : Pt (PNto k (d + 1)) := Pt.map ι hιp t
      have htc' : IsClosedImmersion t'.1 := by
        show IsClosedImmersion (t.1 ≫ ι)
        infer_instance
      obtain ⟨U', hU'⟩ := hO.1 t'.1 htc'
      have hP : IsPair 1 d (PNto k (d + 1)) ι :=
        ⟨hιc, (hF k (d + 1)).1.2, by rw [hιp]; exact (hF k d).1.2⟩
      have hn : 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      refine ⟨t', htc', U', hU', gq.g hP hn z, ?_, ?_⟩
      · intro h0
        apply hz
        have hinj := gq.inj hP hn U0 hoff0 (fun j =>
          iso_sub eU0 (l ^ j) _ (hA j (d + 1) _ (by push_cast; omega)))
        apply hinj
        rw [h0, map_zero]
      · have hinj : Function.Injective ι.base := (IsClosedImmersion.base_closed ι).injective
        have hVU : ι ⁻¹ᵁ U' = U := by
          apply TopologicalSpace.Opens.ext
          rw [hU]
          show ι.base ⁻¹' (U' : Set (PN k (d + 1))) = _
          rw [hU']
          ext x
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, t', Pt.map]
          constructor
          · rintro h ⟨y, rfl⟩
            exact h ⟨y, rfl⟩
          · rintro h ⟨y, hy⟩
            apply h
            refine ⟨y, hinj ?_⟩
            rw [← hy]
            rfl
        subst hVU
        have hP' : IsPair 1 d (U'.ι ≫ PNto k (d + 1)) (ι ∣_ U') := by
          refine ⟨inferInstance, sm_open U'.ι _ _ (hF k (d + 1)).1.2, ?_⟩
          rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hιp]
          exact sm_open _ _ _ (hF k d).1.2
        rw [gq.nat hP' hP U'.ι (ι ⁻¹ᵁ U').ι rfl (isPullback_morphismRestrict ι U') hn z, hzU,
          map_zero]
  intro d
  obtain ⟨t, -, U, hU, z, hz, hzU⟩ := key d
  exact ⟨t, U, z, hU, hz, hzU⟩
