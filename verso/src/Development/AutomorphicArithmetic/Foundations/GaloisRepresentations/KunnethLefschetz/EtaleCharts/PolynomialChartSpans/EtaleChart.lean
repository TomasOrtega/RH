import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PresBC

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Set `P₀ : Algebra.Presentation A (MvPolynomial (Fin D) A) (Fin D) Empty` to `{ __ := Algebra.Generators.mvPolynomial A (Fin D) relation := Empty.elim span_range_relation_eq_ker := by`. Rewrite using `[Algebra.Generators.ker_mvPolynomial]`. Simplify using `}`. Set `P₁ : Algebra.PreSubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty` to `{ __ := P₀ map := Empty.elim map_inj := fun a => a.elim }`. Set `P₂ : Algebra.SubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty` to `{ __ := P₁ jacobian_isUnit := by`.

Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]`. Simplify using `}`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension D A (MvPolynomial (Fin D) A)` using `P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])`. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2 this`.
-/
private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  let P₀ : Algebra.Presentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial A (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have : Algebra.IsStandardSmoothOfRelativeDimension D A (MvPolynomial (Fin D) A) :=
    P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2 this

/- English proof (translation)
Take `⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s` from `⟨_, rfl⟩`. Take `⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* A, σ = eval₂Hom (RingHom.id A) (fun _ => 0)` from `⟨_, rfl⟩`. Rewrite `hφ` using `[← hφd]`. Establish `φC : ∀ x, φ (MvPolynomial.C x) = p x` using `fun x => by rw [hφd, eval₂Hom_C]`. Establish `φX : ∀ k, φ (X k) = s k` using `fun k => by rw [hφd, eval₂Hom_X']`.

Establish `σC : ∀ x, σ (MvPolynomial.C x) = x` using `fun x => by rw [hσd, eval₂Hom_C]; rfl`. Establish `σX : ∀ k, σ (X k) = 0` using `fun k => by rw [hσd, eval₂Hom_X']`. Establish `qs : ∀ k, q (s k) = 0` using `fun k => by`. Establish `: s k ∈ RingHom.ker q` using `by rw [ker]; exact Ideal.subset_span ⟨k, rfl⟩`. Conclude with `RingHom.mem_ker.1 this`.

Establish `hcomm : (q.comp p).comp σ = q.comp φ`. Use `MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, σC, φC]`. Simplify using `only [RingHom.comp_apply, σX, φX, qs, map_zero]`. Establish `exi : ∀ (Q : Type) [CommRing Q] (a : A →+* Q) (b : E →+* Q), a.comp σ = b.comp φ → ∃ r : R →+* Q, r.comp (q.comp p) = a ∧ r.comp q = b`.

Introduce `Q _ a b h`. Establish `hb : ∀ x, b (φ x) = a (σ x)` using `fun x => (RingHom.congr_fun h x).symm`. Establish `hle : RingHom.ker q ≤ RingHom.ker b`. Rewrite using `[ker]`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker]`. Rewrite using `[← φX, hb, σX, map_zero]`. Establish `lf : ∀ x, q.liftOfSurjective surj ⟨b, hle⟩ (q x) = b x` using `fun x => RingHom.liftOfSurjective_comp_apply q surj ⟨b, hle⟩ x`. Use `⟨q.liftOfSurjective surj ⟨b, hle⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, lf, ← φC, hb, σC]`. Conclude with `RingHom.ext fun x => by rw [RingHom.comp_apply, lf]`. Establish `uni : ∀ (Q : Type) [CommRing Q] (u v : R →+* Q), u.comp q = v.comp q → u = v`. Introduce `Q _ u v h`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `surj x`. Conclude with `RingHom.congr_fun h w`. Establish `hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (q.comp p) = CommRingCat.ofHom φ ≫ CommRingCat.ofHom q`. Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]`.

Establish `hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom (q.comp p)) (CommRingCat.ofHom q)`. Establish `ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ), ∃ r : R →+* t.pt, r.comp (q.comp p) = t.inl.hom ∧ r.comp q = t.inr.hom` using `fun t => exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)`. Use `⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _ (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `t`. Conclude with `CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1`.

Introduce `t`. Conclude with `CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2`. Introduce `t m h1 h2`. Use `CommRingCat.hom_ext (uni t.pt m.hom _ ?_)` and prove the remaining obligations. Conclude with `(congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm`.

Establish `hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange` using `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange`. Conclude with `(RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ`.
-/
private theorem etale_quot {A E R : Type} [CommRing A] [CommRing E] [CommRing R] {D : ℕ}
    (p : A →+* E) (q : E →+* R) (s : Fin D → E) (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective q) (ker : RingHom.ker q = Ideal.span (Set.range s)) :
    (q.comp p).Etale := by
  obtain ⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s := ⟨_, rfl⟩
  obtain ⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* A, σ = eval₂Hom (RingHom.id A) (fun _ => 0) := ⟨_, rfl⟩
  rw [← hφd] at hφ
  have φC : ∀ x, φ (MvPolynomial.C x) = p x := fun x => by rw [hφd, eval₂Hom_C]
  have φX : ∀ k, φ (X k) = s k := fun k => by rw [hφd, eval₂Hom_X']
  have σC : ∀ x, σ (MvPolynomial.C x) = x := fun x => by rw [hσd, eval₂Hom_C]; rfl
  have σX : ∀ k, σ (X k) = 0 := fun k => by rw [hσd, eval₂Hom_X']
  have qs : ∀ k, q (s k) = 0 := fun k => by
    have : s k ∈ RingHom.ker q := by rw [ker]; exact Ideal.subset_span ⟨k, rfl⟩
    exact RingHom.mem_ker.1 this
  have hcomm : (q.comp p).comp σ = q.comp φ := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, σC, φC]
    · simp only [RingHom.comp_apply, σX, φX, qs, map_zero]
  have exi : ∀ (Q : Type) [CommRing Q] (a : A →+* Q) (b : E →+* Q),
      a.comp σ = b.comp φ → ∃ r : R →+* Q, r.comp (q.comp p) = a ∧ r.comp q = b := by
    intro Q _ a b h
    have hb : ∀ x, b (φ x) = a (σ x) := fun x => (RingHom.congr_fun h x).symm
    have hle : RingHom.ker q ≤ RingHom.ker b := by
      rw [ker]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      rw [← φX, hb, σX, map_zero]
    have lf : ∀ x, q.liftOfSurjective surj ⟨b, hle⟩ (q x) = b x :=
      fun x => RingHom.liftOfSurjective_comp_apply q surj ⟨b, hle⟩ x
    refine ⟨q.liftOfSurjective surj ⟨b, hle⟩, ?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, lf, ← φC, hb, σC]
    · exact RingHom.ext fun x => by rw [RingHom.comp_apply, lf]
  have uni : ∀ (Q : Type) [CommRing Q] (u v : R →+* Q), u.comp q = v.comp q → u = v := by
    intro Q _ u v h
    refine RingHom.ext fun x => ?_
    obtain ⟨w, rfl⟩ := surj x
    exact RingHom.congr_fun h w
  have hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (q.comp p) = CommRingCat.ofHom φ ≫ CommRingCat.ofHom q := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  have hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom (q.comp p))
      (CommRingCat.ofHom q) := by
    have ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ),
        ∃ r : R →+* t.pt, r.comp (q.comp p) = t.inl.hom ∧ r.comp q = t.inr.hom := fun t =>
      exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)
    refine ⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _
      (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2
    · intro t m h1 h2
      refine CommRingCat.hom_ext (uni t.pt m.hom _ ?_)
      exact (congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm
  have hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ

/- English proof (translation)
Set `e : MvPolynomial (Fin D) (MvPolynomial (Fin n) K) ≃+* MvPolynomial (Fin n ⊕ Fin D) K` to `((MvPolynomial.sumAlgEquiv K (Fin D) (Fin n)).symm.trans (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin D) (Fin n)))).toRingEquiv`. Establish `key : eval₂Hom (eval₂Hom s x) t = (eval₂Hom s (Sum.elim x t)).comp e.toRingHom`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)` and prove the remaining obligations. Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C c => simp [e]`.

Consider the case `add a b ha hb => simp_all`. Consider the case `mul_X a i ha => simp_all [e]`. Simplify using `[e]`. Rewrite using `[key]`. Conclude with `RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) h`.
-/
private theorem etale_iter {K E : Type} [CommRing K] [CommRing E] (s : K →+* E) {n D : ℕ}
    (x : Fin n → E) (t : Fin D → E) (h : (eval₂Hom s (Sum.elim x t)).Etale) :
    (eval₂Hom (eval₂Hom s x) t).Etale := by
  let e : MvPolynomial (Fin D) (MvPolynomial (Fin n) K) ≃+* MvPolynomial (Fin n ⊕ Fin D) K :=
    ((MvPolynomial.sumAlgEquiv K (Fin D) (Fin n)).symm.trans
      (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin D) (Fin n)))).toRingEquiv
  have key : eval₂Hom (eval₂Hom s x) t = (eval₂Hom s (Sum.elim x t)).comp e.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · induction a using MvPolynomial.induction_on with
      | C c => simp [e]
      | add a b ha hb => simp_all
      | mul_X a i ha => simp_all [e]
    · simp [e]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) h

/- English proof (translation)
Establish `h0` using `(RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC _ D)`. Rewrite `h0` using `[MvPolynomial.eval₂Hom_comp_C, Nat.zero_add]`. Conclude with `h0.comp (stdC K n)`.
-/
private theorem std_etale {K E : Type} [CommRing K] [CommRing E] {n D : ℕ}
    (p : MvPolynomial (Fin n) K →+* E) (y : Fin D → E) (h : (eval₂Hom p y).Etale) :
    (p.comp MvPolynomial.C).IsStandardSmoothOfRelativeDimension (D + n) := by
  have h0 := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC _ D)
  rw [MvPolynomial.eval₂Hom_comp_C, Nat.zero_add] at h0
  exact h0.comp (stdC K n)

/- English proof (translation)
Establish `h0` using `(RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC K n)`. Rewrite `h0` using `[Nat.zero_add]`. Then use the resulting hypothesis.
-/
private theorem std_etale0 {K E : Type} [CommRing K] [CommRing E] {n : ℕ}
    (p : MvPolynomial (Fin n) K →+* E) (h : p.Etale) :
    (p.comp MvPolynomial.C).IsStandardSmoothOfRelativeDimension n := by
  have h0 := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC K n)
  rwa [Nat.zero_add] at h0

/- English proof (translation)
Take `⟨h, hd⟩ : ∃ h : MvPolynomial (Fin (d + 1)) R →+* MvPolynomial (Fin d) R, h = eval₂Hom MvPolynomial.C (k.insertNth 1 X)` from `⟨_, rfl⟩`. Take `⟨g, gd⟩ : ∃ g : MvPolynomial (Fin d) R →+* B, g = eval₂Hom f (fun m => u (k.succAbove m))` from `⟨_, rfl⟩`. Take `⟨ι, ιd⟩ : ∃ ι : MvPolynomial (Fin d) R →+* MvPolynomial (Fin (d + 1)) R, ι = eval₂Hom MvPolynomial.C (fun m => X (k.succAbove m))` from `⟨_, rfl⟩`. Establish `hX : h (X k) = 1` using `by rw [hd, eval₂Hom_X', Fin.insertNth_apply_same]`. Establish `hXs : ∀ m, h (X (k.succAbove m)) = X m` using `fun m => by rw [hd, eval₂Hom_X', Fin.insertNth_apply_succAbove]`.

Establish `hC : ∀ a, h (MvPolynomial.C a) = MvPolynomial.C a` using `fun a => by rw [hd, eval₂Hom_C]`. Establish `gC : ∀ a, g (MvPolynomial.C a) = f a` using `fun a => by rw [gd, eval₂Hom_C]`. Establish `gX : ∀ m, g (X m) = u (k.succAbove m)` using `fun m => by rw [gd, eval₂Hom_X']`. Establish `uk : u k = 1`. Establish `: (X k - 1 : MvPolynomial (Fin (d + 1)) R) ∈ RingHom.ker (eval₂Hom f u)`.

Rewrite using `[ker]`. Conclude with `Ideal.subset_span hk`. Use `RingHom.mem_ker.1 this` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, eval₂Hom_X']`. Conclude with `sub_eq_zero.1 this`.

Establish `gh : g.comp h = eval₂Hom f u`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hC, gC, eval₂Hom_C]`. Rewrite using `[RingHom.comp_apply, eval₂Hom_X']`. Break down `Fin.eq_self_or_eq_succAbove k m with rfl | ⟨m, rfl⟩` into its components or cases.

Rewrite using `[hX, map_one, uk]`. Rewrite using `[hXs, gX]`. Establish `hι : h.comp ι = RingHom.id _`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)` and prove the remaining obligations. Simplify using `[ιd, hC]`.

Simplify using `[ιd, hXs]`. Establish `gι : (eval₂Hom f u).comp ι = g` using `by rw [← gh, RingHom.comp_assoc, hι, RingHom.comp_id]`. Establish `hker : RingHom.ker (eval₂Hom f u) ≤ RingHom.ker h`. Rewrite using `[ker]`. Use `Ideal.span_le.2 fun s hs => ?_` and prove the remaining obligations.

Break down `hS s hs with rfl | rfl` into its components or cases. Simplify using `[RingHom.mem_ker, hX]`. Simplify using the standard rewrite rules. Establish `bij : Function.Bijective g`. Use `⟨(injective_iff_map_eq_zero g).2 fun a ha => ?_, fun b => ?_⟩` and prove the remaining obligations.

Establish `h1 : ι a ∈ RingHom.ker (eval₂Hom f u)`. Rewrite using `[RingHom.mem_ker]`. Use `RingHom.congr_fun gι a` as an intermediate fact. Rewrite `this` using `[RingHom.comp_apply]`. Rewrite using `[this, ha]`.

Establish `h2` using `RingHom.mem_ker.1 (hker h1)`. Establish `h3` using `RingHom.congr_fun hι a`. Rewrite `h3` using `[RingHom.comp_apply]`. Rewrite `h3` using `[h2]`. Conclude with `h3.symm`.

Take `⟨w, rfl⟩` from `surj b`. Conclude with `⟨h w, by rw [← RingHom.comp_apply, gh]⟩`. Establish `e : f = (RingEquiv.ofBijective g bij).toRingHom.comp MvPolynomial.C`. Use extensionality with `a`. Simplify using `[gC]`.

Rewrite using `[e]`. Conclude with `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ (stdC R d)`.
-/
private theorem std_pres {R B : Type} [CommRing R] [CommRing B] (f : R →+* B) {d : ℕ} (u : Fin (d + 1) → B) (k : Fin (d + 1))
    (S : Set (MvPolynomial (Fin (d + 1)) R)) (surj : Function.Surjective (eval₂Hom f u))
    (ker : RingHom.ker (eval₂Hom f u) = Ideal.span S) (hk : (X k - 1 : MvPolynomial (Fin (d + 1)) R) ∈ S)
    (hS : ∀ s ∈ S, s = X k - 1 ∨ s = 0) : f.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨h, hd⟩ : ∃ h : MvPolynomial (Fin (d + 1)) R →+* MvPolynomial (Fin d) R,
    h = eval₂Hom MvPolynomial.C (k.insertNth 1 X) := ⟨_, rfl⟩
  obtain ⟨g, gd⟩ : ∃ g : MvPolynomial (Fin d) R →+* B, g = eval₂Hom f (fun m => u (k.succAbove m)) := ⟨_, rfl⟩
  obtain ⟨ι, ιd⟩ : ∃ ι : MvPolynomial (Fin d) R →+* MvPolynomial (Fin (d + 1)) R,
    ι = eval₂Hom MvPolynomial.C (fun m => X (k.succAbove m)) := ⟨_, rfl⟩
  have hX : h (X k) = 1 := by rw [hd, eval₂Hom_X', Fin.insertNth_apply_same]
  have hXs : ∀ m, h (X (k.succAbove m)) = X m := fun m => by rw [hd, eval₂Hom_X', Fin.insertNth_apply_succAbove]
  have hC : ∀ a, h (MvPolynomial.C a) = MvPolynomial.C a := fun a => by rw [hd, eval₂Hom_C]
  have gC : ∀ a, g (MvPolynomial.C a) = f a := fun a => by rw [gd, eval₂Hom_C]
  have gX : ∀ m, g (X m) = u (k.succAbove m) := fun m => by rw [gd, eval₂Hom_X']
  have uk : u k = 1 := by
    have : (X k - 1 : MvPolynomial (Fin (d + 1)) R) ∈ RingHom.ker (eval₂Hom f u) := by
      rw [ker]; exact Ideal.subset_span hk
    have := RingHom.mem_ker.1 this
    rw [map_sub, map_one, eval₂Hom_X'] at this
    exact sub_eq_zero.1 this
  have gh : g.comp h = eval₂Hom f u := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · rw [RingHom.comp_apply, hC, gC, eval₂Hom_C]
    · rw [RingHom.comp_apply, eval₂Hom_X']
      rcases Fin.eq_self_or_eq_succAbove k m with rfl | ⟨m, rfl⟩
      · rw [hX, map_one, uk]
      · rw [hXs, gX]
  have hι : h.comp ι = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · simp [ιd, hC]
    · simp [ιd, hXs]
  have gι : (eval₂Hom f u).comp ι = g := by rw [← gh, RingHom.comp_assoc, hι, RingHom.comp_id]
  have hker : RingHom.ker (eval₂Hom f u) ≤ RingHom.ker h := by
    rw [ker]
    refine Ideal.span_le.2 fun s hs => ?_
    rcases hS s hs with rfl | rfl
    · simp [RingHom.mem_ker, hX]
    · simp
  have bij : Function.Bijective g := by
    refine ⟨(injective_iff_map_eq_zero g).2 fun a ha => ?_, fun b => ?_⟩
    · have h1 : ι a ∈ RingHom.ker (eval₂Hom f u) := by
        rw [RingHom.mem_ker]
        have := RingHom.congr_fun gι a
        rw [RingHom.comp_apply] at this
        rw [this, ha]
      have h2 := RingHom.mem_ker.1 (hker h1)
      have h3 := RingHom.congr_fun hι a
      rw [RingHom.comp_apply] at h3
      rw [h2] at h3
      exact h3.symm
    · obtain ⟨w, rfl⟩ := surj b
      exact ⟨h w, by rw [← RingHom.comp_apply, gh]⟩
  have e : f = (RingEquiv.ofBijective g bij).toRingHom.comp MvPolynomial.C := by
    ext a
    simp [gC]
  rw [e]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ (stdC R d)

/- English proof (translation)
Take `⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s` from `⟨_, rfl⟩`. Take `⟨f, hfd⟩ : ∃ f : MvPolynomial (Fin D) E →+* B, f = eval₂Hom ψ y` from `⟨_, rfl⟩`. Take `⟨g, hgd⟩ : ∃ g : MvPolynomial (Fin D) A →+* B, g = eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))` from `⟨_, rfl⟩`. Take `⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* MvPolynomial (Fin D) A, σ = eval₂Hom MvPolynomial.C (fun k => if k = j then X j else X k * X j)` from `⟨_, rfl⟩`. Rewrite `hφ` using `[← hφd]`.

Rewrite `surj`, `ker` using `[← hfd]`. Rewrite using `[← hgd]`. Establish `φC : ∀ x, φ (MvPolynomial.C x) = p x` using `fun x => by rw [hφd, eval₂Hom_C]`. Establish `φX : ∀ k, φ (X k) = s k` using `fun k => by rw [hφd, eval₂Hom_X']`. Establish `fC : ∀ x, f (MvPolynomial.C x) = ψ x` using `fun x => by rw [hfd, eval₂Hom_C]`.

Establish `fX : ∀ k, f (X k) = y k` using `fun k => by rw [hfd, eval₂Hom_X']`. Establish `gC : ∀ x, g (MvPolynomial.C x) = ψ (p x)` using `fun x => by rw [hgd, eval₂Hom_C]; rfl`. Establish `gX : ∀ k, k ≠ j → g (X k) = y k` using `fun k hk => by`. Rewrite using `[hgd, eval₂Hom_X', Function.update_of_ne hk]`. Establish `gXj : g (X j) = ψ (s j)` using `by rw [hgd, eval₂Hom_X', Function.update_self]`.

Establish `σC : ∀ x, σ (MvPolynomial.C x) = MvPolynomial.C x` using `fun x => by rw [hσd, eval₂Hom_C]`. Establish `σX : ∀ k, k ≠ j → σ (X k) = X k * X j` using `fun k hk => by`. Rewrite using `[hσd, eval₂Hom_X', if_neg hk]`. Establish `σXj : σ (X j) = X j` using `by rw [hσd, eval₂Hom_X', if_pos rfl]`. Establish `mem1 : (X j - 1 : MvPolynomial (Fin D) E) ∈ RingHom.ker f`.

Rewrite using `[ker]`. Conclude with `Ideal.subset_span (Set.mem_insert _ _)`. Establish `mem2 : ∀ k, (MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k : MvPolynomial (Fin D) E) ∈ RingHom.ker f` using `fun k => by`. Rewrite using `[ker]`. Conclude with `Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)`.

Establish `hyj : y j = 1`. Use `RingHom.mem_ker.1 mem1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, fX]`. Conclude with `sub_eq_zero.1 this`. Establish `hsk : ∀ k, ψ (s k) = ψ (s j) * y k` using `fun k => by`.

Use `RingHom.mem_ker.1 (mem2 k)` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, fC, fC, fX]`. Conclude with `sub_eq_zero.1 this`. Establish `hcomm : g.comp σ = ψ.comp φ`. Use `MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, σC, gC, φC]`. Simplify using `only [RingHom.comp_apply, φX]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[σXj, gXj]`.

Rewrite using `[σX k hk, map_mul, gX k hk, gXj, hsk k, mul_comm]`. Establish `exi : ∀ (Q : Type) [CommRing Q] (a : MvPolynomial (Fin D) A →+* Q) (b : E →+* Q), a.comp σ = b.comp φ → ∃ r : B →+* Q, r.comp g = a ∧ r.comp ψ = b`. Introduce `Q _ a b h`. Establish `hb : ∀ x, b (φ x) = a (σ x)` using `fun x => (RingHom.congr_fun h x).symm`. Take `⟨r', hr'⟩ : ∃ r' : MvPolynomial (Fin D) E →+* Q, r' = eval₂Hom b (Function.update (fun k => a (X k)) j 1)` from `⟨_, rfl⟩`.

Establish `r'C : ∀ x, r' (MvPolynomial.C x) = b x` using `fun x => by rw [hr', eval₂Hom_C]`. Establish `r'X : ∀ k, k ≠ j → r' (X k) = a (X k)` using `fun k hk => by`. Rewrite using `[hr', eval₂Hom_X', Function.update_of_ne hk]`. Establish `r'Xj : r' (X j) = 1` using `by rw [hr', eval₂Hom_X', Function.update_self]`. Establish `bs : ∀ k, b (s k) = a (σ (X k))` using `fun k => by rw [← hb, φX]`.

Establish `hle : RingHom.ker f ≤ RingHom.ker r'`. Rewrite using `[ker]`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨k, rfl⟩)`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, r'Xj, sub_self]`.

Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, r'C]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[r'Xj, mul_one, sub_self]`. Rewrite using `[r'X k hk, bs k, bs j, σX k hk, σXj, map_mul, mul_comm, sub_self]`.

Use `⟨f.liftOfSurjective surj ⟨r', hle⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `lf : ∀ x, f.liftOfSurjective surj ⟨r', hle⟩ (f x) = r' x` using `fun x => RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩ x`. Use `MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, gC, ← fC, lf, r'C, ← φC, hb, σC]`. Rewrite using `[RingHom.comp_apply]`.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[gXj, ← fC, lf, r'C, bs, σXj]`. Rewrite using `[gX k hk, ← fX, lf, r'X k hk]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, ← fC, RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩, r'C]`. Establish `uni : ∀ (Q : Type) [CommRing Q] (u v : B →+* Q), u.comp g = v.comp g → u.comp ψ = v.comp ψ → u = v`. Introduce `Q _ u v h1 h2`. Establish `h3 : u.comp f = v.comp f`. Use `MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)` and prove the remaining obligations.

Simplify `RingHom.congr_fun h2 x` using `only [RingHom.comp_apply, fC]`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, fX]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[hyj, map_one, map_one]`.

Simplify `RingHom.congr_fun h1 (X k)` using `only [RingHom.comp_apply, gX k hk]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `surj x`. Conclude with `RingHom.congr_fun h3 w`. Establish `hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom g = CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ`.

Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]`. Establish `hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom g) (CommRingCat.ofHom ψ)`. Establish `ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ), ∃ r : B →+* t.pt, r.comp g = t.inl.hom ∧ r.comp ψ = t.inr.hom` using `fun t => exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)`. Use `⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _ (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `t`.

Conclude with `CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1`. Introduce `t`. Conclude with `CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2`. Introduce `t m h1 h2`. Use `CommRingCat.hom_ext (uni t.pt m.hom _ ?_ ?_)` and prove the remaining obligations.

Conclude with `(congrArg CommRingCat.Hom.hom h1).trans (Classical.choose_spec (ex' t)).1.symm`. Conclude with `(congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm`. Establish `hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange` using `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange`. Conclude with `(RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ`.
-/
private theorem etale_chart {A E B : Type} [CommRing A] [CommRing E] [CommRing B] {D : ℕ}
    (p : A →+* E) (ψ : E →+* B) (s : Fin D → E) (y : Fin D → B) (j : Fin D)
    (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective (eval₂Hom ψ y))
    (ker : RingHom.ker (eval₂Hom ψ y) = Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k))) :
    (eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))).Etale := by
  classical
  obtain ⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s := ⟨_, rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : MvPolynomial (Fin D) E →+* B, f = eval₂Hom ψ y := ⟨_, rfl⟩
  obtain ⟨g, hgd⟩ : ∃ g : MvPolynomial (Fin D) A →+* B,
    g = eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j))) := ⟨_, rfl⟩
  obtain ⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* MvPolynomial (Fin D) A,
    σ = eval₂Hom MvPolynomial.C (fun k => if k = j then X j else X k * X j) := ⟨_, rfl⟩
  rw [← hφd] at hφ
  rw [← hfd] at surj ker
  rw [← hgd]
  have φC : ∀ x, φ (MvPolynomial.C x) = p x := fun x => by rw [hφd, eval₂Hom_C]
  have φX : ∀ k, φ (X k) = s k := fun k => by rw [hφd, eval₂Hom_X']
  have fC : ∀ x, f (MvPolynomial.C x) = ψ x := fun x => by rw [hfd, eval₂Hom_C]
  have fX : ∀ k, f (X k) = y k := fun k => by rw [hfd, eval₂Hom_X']
  have gC : ∀ x, g (MvPolynomial.C x) = ψ (p x) := fun x => by rw [hgd, eval₂Hom_C]; rfl
  have gX : ∀ k, k ≠ j → g (X k) = y k := fun k hk => by
    rw [hgd, eval₂Hom_X', Function.update_of_ne hk]
  have gXj : g (X j) = ψ (s j) := by rw [hgd, eval₂Hom_X', Function.update_self]
  have σC : ∀ x, σ (MvPolynomial.C x) = MvPolynomial.C x := fun x => by rw [hσd, eval₂Hom_C]
  have σX : ∀ k, k ≠ j → σ (X k) = X k * X j := fun k hk => by
    rw [hσd, eval₂Hom_X', if_neg hk]
  have σXj : σ (X j) = X j := by rw [hσd, eval₂Hom_X', if_pos rfl]
  have mem1 : (X j - 1 : MvPolynomial (Fin D) E) ∈ RingHom.ker f := by
    rw [ker]; exact Ideal.subset_span (Set.mem_insert _ _)
  have mem2 : ∀ k, (MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k : MvPolynomial (Fin D) E) ∈
      RingHom.ker f := fun k => by
    rw [ker]; exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hyj : y j = 1 := by
    have := RingHom.mem_ker.1 mem1
    rw [map_sub, map_one, fX] at this
    exact sub_eq_zero.1 this
  have hsk : ∀ k, ψ (s k) = ψ (s j) * y k := fun k => by
    have := RingHom.mem_ker.1 (mem2 k)
    rw [map_sub, map_mul, fC, fC, fX] at this
    exact sub_eq_zero.1 this
  have hcomm : g.comp σ = ψ.comp φ := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, σC, gC, φC]
    · simp only [RingHom.comp_apply, φX]
      by_cases hk : k = j
      · subst hk; rw [σXj, gXj]
      · rw [σX k hk, map_mul, gX k hk, gXj, hsk k, mul_comm]
  have exi : ∀ (Q : Type) [CommRing Q] (a : MvPolynomial (Fin D) A →+* Q) (b : E →+* Q),
      a.comp σ = b.comp φ → ∃ r : B →+* Q, r.comp g = a ∧ r.comp ψ = b := by
    intro Q _ a b h
    have hb : ∀ x, b (φ x) = a (σ x) := fun x => (RingHom.congr_fun h x).symm
    obtain ⟨r', hr'⟩ : ∃ r' : MvPolynomial (Fin D) E →+* Q,
      r' = eval₂Hom b (Function.update (fun k => a (X k)) j 1) := ⟨_, rfl⟩
    have r'C : ∀ x, r' (MvPolynomial.C x) = b x := fun x => by rw [hr', eval₂Hom_C]
    have r'X : ∀ k, k ≠ j → r' (X k) = a (X k) := fun k hk => by
      rw [hr', eval₂Hom_X', Function.update_of_ne hk]
    have r'Xj : r' (X j) = 1 := by rw [hr', eval₂Hom_X', Function.update_self]
    have bs : ∀ k, b (s k) = a (σ (X k)) := fun k => by rw [← hb, φX]
    have hle : RingHom.ker f ≤ RingHom.ker r' := by
      rw [ker]
      refine Ideal.span_le.2 ?_
      rintro _ (rfl | ⟨k, rfl⟩)
      · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, r'Xj, sub_self]
      · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, r'C]
        by_cases hk : k = j
        · subst hk; rw [r'Xj, mul_one, sub_self]
        · rw [r'X k hk, bs k, bs j, σX k hk, σXj, map_mul, mul_comm, sub_self]
    refine ⟨f.liftOfSurjective surj ⟨r', hle⟩, ?_, ?_⟩
    · have lf : ∀ x, f.liftOfSurjective surj ⟨r', hle⟩ (f x) = r' x :=
        fun x => RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩ x
      refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
      · rw [RingHom.comp_apply, gC, ← fC, lf, r'C, ← φC, hb, σC]
      · rw [RingHom.comp_apply]
        by_cases hk : k = j
        · subst hk; rw [gXj, ← fC, lf, r'C, bs, σXj]
        · rw [gX k hk, ← fX, lf, r'X k hk]
    · refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, ← fC, RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩, r'C]
  have uni : ∀ (Q : Type) [CommRing Q] (u v : B →+* Q),
      u.comp g = v.comp g → u.comp ψ = v.comp ψ → u = v := by
    intro Q _ u v h1 h2
    have h3 : u.comp f = v.comp f := by
      refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
      · simpa only [RingHom.comp_apply, fC] using RingHom.congr_fun h2 x
      · rw [RingHom.comp_apply, RingHom.comp_apply, fX]
        by_cases hk : k = j
        · subst hk; rw [hyj, map_one, map_one]
        · simpa only [RingHom.comp_apply, gX k hk] using RingHom.congr_fun h1 (X k)
    refine RingHom.ext fun x => ?_
    obtain ⟨w, rfl⟩ := surj x
    exact RingHom.congr_fun h3 w
  have hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom g = CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  have hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ψ) := by
    have ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ),
        ∃ r : B →+* t.pt, r.comp g = t.inl.hom ∧ r.comp ψ = t.inr.hom := fun t =>
      exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)
    refine ⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _
      (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2
    · intro t m h1 h2
      refine CommRingCat.hom_ext (uni t.pt m.hom _ ?_ ?_)
      · exact (congrArg CommRingCat.Hom.hom h1).trans (Classical.choose_spec (ex' t)).1.symm
      · exact (congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm
  have hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ

/- English proof (translation)
Establish `hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n)` using `HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))`. Use `choose O hx hO using H`. Use `(IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O ?_).2 hO` and prove the remaining obligations. Conclude with `top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩`.
-/
private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  choose O hx hO using H
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O ?_).2 hO
  exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩

/- English proof (translation)
Establish `: IsAffine U.toScheme` using `hU`. Establish `: IsAffine V.toScheme` using `hV`. Establish `hr` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)`. Establish `h1 : SmoothOfRelativeDimension n (f.resLE U V e)`. Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]`.

Conclude with `((RingHom.locally_respectsIso hr).arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr (RingHom.locally_of hr _ h)`. Establish `h2 : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι)` using `inferInstance`. Rewrite `h2` using `[Scheme.Hom.resLE_comp_ι]`. Conclude with `h2`.
-/
private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hr := RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)
  have h1 : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact ((RingHom.locally_respectsIso hr).arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of hr _ h)
  have h2 : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  rw [Scheme.Hom.resLE_comp_ι] at h2
  exact h2

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, h⟩` from `ha.exists_isStandardSmoothOfRelativeDimension x`. Establish `hl : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (f.appLE U V e).hom` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension b) f hb ⟨U, hU⟩ ⟨V, hV⟩ e`. Take `⟨s, hs, hl⟩` from `hl`. Use `haveI : Nonempty V := ⟨⟨x, hx⟩⟩`. Take `⟨m, hm⟩` from `Ideal.exists_maximal Γ(X, V)`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht, htm⟩ : ∃ t ∈ s, t ∉ m := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hm.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))`. Establish `h1` using `hl t ht`.

Establish `h0 : (algebraMap Γ(X, V) (Localization.Away t)).IsStandardSmoothOfRelativeDimension 0` using `RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t`. Establish `h2` using `h0.comp h`. Rewrite `h2` using `[Nat.zero_add]`. Use `haveI : Nontrivial (Localization.Away t) := by`. Use `letI := Ideal.Quotient.field m`.

Establish `hu : IsUnit (Ideal.Quotient.mk m t)` using `isUnit_iff_ne_zero.2 (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Conclude with `RingHom.domain_nontrivial (IsLocalization.Away.lift (S := Localization.Away t) t hu)`. Use `letI := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra`. Use `haveI ia : Algebra.IsStandardSmoothOfRelativeDimension a Γ(Y, U) (Localization.Away t) := h2`. Use `haveI ib : Algebra.IsStandardSmoothOfRelativeDimension b Γ(Y, U) (Localization.Away t) := h1`.

Establish `ra` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) a`. Establish `rb` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) b`. Conclude with `Nat.cast_injective (R := Cardinal) (ra.symm.trans rb)`.
-/
private theorem dim_unique {X Y : Scheme.{0}} (f : X ⟶ Y) {a b : ℕ} (x : X)
    (ha : SmoothOfRelativeDimension a f) (hb : SmoothOfRelativeDimension b f) : a = b := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := ha.exists_isStandardSmoothOfRelativeDimension x
  have hl : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension b) f hb ⟨U, hU⟩ ⟨V, hV⟩ e
  obtain ⟨s, hs, hl⟩ := hl
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htm⟩ : ∃ t ∈ s, t ∉ m := by
    by_contra hc
    push_neg at hc
    exact hm.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have h1 := hl t ht
  have h0 : (algebraMap Γ(X, V) (Localization.Away t)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have h2 := h0.comp h
  rw [Nat.zero_add] at h2
  haveI : Nontrivial (Localization.Away t) := by
    letI := Ideal.Quotient.field m
    have hu : IsUnit (Ideal.Quotient.mk m t) :=
      isUnit_iff_ne_zero.2 (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact RingHom.domain_nontrivial (IsLocalization.Away.lift (S := Localization.Away t) t hu)
  letI := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  haveI ia : Algebra.IsStandardSmoothOfRelativeDimension a Γ(Y, U) (Localization.Away t) := h2
  haveI ib : Algebra.IsStandardSmoothOfRelativeDimension b Γ(Y, U) (Localization.Away t) := h1
  have ra := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) a
  have rb := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) b
  exact Nat.cast_injective (R := Cardinal) (ra.symm.trans rb)

section Charts

variable {K : Type} [CommRing K]

/- English proof (translation)
Establish `h` using `Scheme.Hom.appLE_comp_appLE f q ⊤ V' V le_top e`. Unfold `Pb.strV`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
private theorem strV_comp {X X' : Scheme.{0}} (f : X ⟶ X') (q : X' ⟶ Spec (CommRingCat.of K)) (V' : X'.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ V') : Pb.strV (f ≫ q) V = (f.appLE V' V e).hom.comp (Pb.strV q V') := by
  have h := Scheme.Hom.appLE_comp_appLE f q ⊤ V' V le_top e
  unfold Pb.strV
  rw [← h]
  rfl

/- English proof (translation)
Use `chart q n (isAffineOpen_top _) hV le_top ?_` and prove the remaining obligations. Establish `e : (q.appLE ⊤ V le_top).hom = (Pb.strV q V).comp (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toRingHom`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv a) = a` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm_apply_apply a`. Simplify using `[Pb.strV, h2]`.

Rewrite using `[e]`. Conclude with `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ h`.
-/
private theorem sm_of_strV {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (hV : IsAffineOpen V) (n : ℕ)
    (h : (Pb.strV q V).IsStandardSmoothOfRelativeDimension n) : SmoothOfRelativeDimension n (V.ι ≫ q) := by
  refine chart q n (isAffineOpen_top _) hV le_top ?_
  have e : (q.appLE ⊤ V le_top).hom =
      (Pb.strV q V).comp (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toRingHom := by
    refine RingHom.ext fun a => ?_
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv a) = a :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm_apply_apply a
    simp [Pb.strV, h2]
  rw [e]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ h

variable {W Z Y : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) {D : ℕ} {V : Z.Opens}

/- English proof (translation)
Use `sm_of_strV p V c.affine _ ?_` and prove the remaining obligations. Establish `h` using `std_etale (eval₂Hom (Pb.strV p V) c.x) c.t (etale_iter _ _ _ c.etale)`. Rewrite `h` using `[eval₂Hom_comp_C]`. Then use the resulting hypothesis.
-/
private theorem chartZ (c : CrystallineSemistableComparison.Onto.BChart p i π D V) : SmoothOfRelativeDimension (D + c.n) (V.ι ≫ p) := by
  refine sm_of_strV p V c.affine _ ?_
  have h := std_etale (eval₂Hom (Pb.strV p V) c.x) c.t (etale_iter _ _ _ c.etale)
  rwa [eval₂Hom_comp_C] at h

/- English proof (translation)
Use `sm_of_strV _ _ (c.C_aff k) _ ?_` and prove the remaining obligations. Establish `h1` using `etale_chart (eval₂Hom (Pb.strV p V) c.x) (π.appLE V (c.C k) (c.C_le k)).hom c.t (c.u k) k (etale_iter _ _ _ c.etale) (c.surj k) (c.rel k)`. Establish `h` using `std_etale _ _ h1`. Rewrite `h` using `[RingHom.comp_assoc, eval₂Hom_comp_C, ← strV_comp π p V _ (c.C_le k)]`. Conclude with `h`.
-/
private theorem chartY (c : CrystallineSemistableComparison.Onto.BChart p i π D V) (k : Fin D) :
    SmoothOfRelativeDimension (D + c.n) ((c.C k).ι ≫ π ≫ p) := by
  refine sm_of_strV _ _ (c.C_aff k) _ ?_
  have h1 := etale_chart (eval₂Hom (Pb.strV p V) c.x) (π.appLE V (c.C k) (c.C_le k)).hom c.t (c.u k) k
    (etale_iter _ _ _ c.etale) (c.surj k) (c.rel k)
  have h := std_etale _ _ h1
  rw [RingHom.comp_assoc, eval₂Hom_comp_C, ← strV_comp π p V _ (c.C_le k)] at h
  exact h

/- English proof (translation)
Establish `hVi : IsAffineOpen (i ⁻¹ᵁ V)` using `c.affine.preimage i`. Establish `h' : j ⁻¹ᵁ c.C k ≤ r ⁻¹ᵁ (i ⁻¹ᵁ V)`. Introduce `y hy`. Establish `h1 : π (j y) ∈ V` using `c.C_le k hy`. Establish `e : π (j y) = i (r y)`.

Use `congr($(hpb.w) y)` as an intermediate fact. Simplify `this` using `only [Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `i (r y) ∈ V`. Rewrite using `[← e]` and apply the resulting hypothesis. Take `⟨hA, hs, hker⟩` from `presBC π r i j hpb V (c.C k) (c.C_le k) c.affine (c.C_aff k) hVi h' (Fin (d + 1)) (c.u k) _ (c.surj k) (c.rel k)`.

Establish `ht : ∀ m, (i.app V).hom (c.t m) = 0` using `fun m => by`. Establish `: c.t m ∈ RingHom.ker (i.app V).hom`. Rewrite using `[c.ker]`. Conclude with `Ideal.subset_span ⟨m, rfl⟩`. Conclude with `RingHom.mem_ker.1 this`.

Establish `hstd : (r.appLE (i ⁻¹ᵁ V) (j ⁻¹ᵁ c.C k) h').hom.IsStandardSmoothOfRelativeDimension d`. Use `std_pres _ _ k _ hs hker ⟨X k - 1, Set.mem_insert _ _, by simp⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, (rfl | ⟨m, rfl⟩), rfl⟩`. Use `left`. Simplify using the standard rewrite rules.

Use `right`. Simplify using `[ht]`. Establish `hq : ((i.app V).hom.comp (eval₂Hom (Pb.strV p V) c.x)).Etale` using `etale_quot _ _ c.t (etale_iter _ _ _ c.etale) (i.app_surjective V c.affine) c.ker`. Establish `hW` using `std_etale0 _ hq`. Rewrite `hW` using `[RingHom.comp_assoc, eval₂Hom_comp_C]`.

Establish `hW' : (Pb.strV (i ≫ p) (i ⁻¹ᵁ V)).IsStandardSmoothOfRelativeDimension c.n`. Rewrite using `[strV_comp i p V _ le_rfl, Scheme.Hom.appLE_eq_app]`. Conclude with `hW`. Establish `hc` using `hstd.comp hW'`. Rewrite `hc` using `[← strV_comp r (i ≫ p) (i ⁻¹ᵁ V) _ h']`.

Establish `hm` using `sm_of_strV _ _ hA _ hc`. Establish `hw : j ≫ π ≫ p = r ≫ i ≫ p` using `by rw [← Category.assoc, hpb.w, Category.assoc]`. Rewrite using `[hw]`. Conclude with `hm`.
-/
private theorem chartT {T : Scheme.{0}} [IsClosedImmersion i] {d : ℕ} (c : CrystallineSemistableComparison.Onto.BChart p i π (d + 1) V) (k : Fin (d + 1))
    (j : T ⟶ Y) (r : T ⟶ W) (hpb : IsPullback j r π i) :
    SmoothOfRelativeDimension (d + c.n) ((j ⁻¹ᵁ c.C k).ι ≫ j ≫ π ≫ p) := by
  have hVi : IsAffineOpen (i ⁻¹ᵁ V) := c.affine.preimage i
  have h' : j ⁻¹ᵁ c.C k ≤ r ⁻¹ᵁ (i ⁻¹ᵁ V) := by
    intro y hy
    have h1 : π (j y) ∈ V := c.C_le k hy
    have e : π (j y) = i (r y) := by
      have := congr($(hpb.w) y)
      simpa only [Scheme.Hom.comp_apply] using this
    change i (r y) ∈ V
    rwa [← e]
  obtain ⟨hA, hs, hker⟩ := presBC π r i j hpb V (c.C k) (c.C_le k) c.affine (c.C_aff k) hVi h' (Fin (d + 1)) (c.u k) _
    (c.surj k) (c.rel k)
  have ht : ∀ m, (i.app V).hom (c.t m) = 0 := fun m => by
    have : c.t m ∈ RingHom.ker (i.app V).hom := by
      rw [c.ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    exact RingHom.mem_ker.1 this
  have hstd : (r.appLE (i ⁻¹ᵁ V) (j ⁻¹ᵁ c.C k) h').hom.IsStandardSmoothOfRelativeDimension d := by
    refine std_pres _ _ k _ hs hker ⟨X k - 1, Set.mem_insert _ _, by simp⟩ ?_
    rintro _ ⟨s, (rfl | ⟨m, rfl⟩), rfl⟩
    · left
      simp
    · right
      simp [ht]
  have hq : ((i.app V).hom.comp (eval₂Hom (Pb.strV p V) c.x)).Etale :=
    etale_quot _ _ c.t (etale_iter _ _ _ c.etale) (i.app_surjective V c.affine) c.ker
  have hW := std_etale0 _ hq
  rw [RingHom.comp_assoc, eval₂Hom_comp_C] at hW
  have hW' : (Pb.strV (i ≫ p) (i ⁻¹ᵁ V)).IsStandardSmoothOfRelativeDimension c.n := by
    rw [strV_comp i p V _ le_rfl, Scheme.Hom.appLE_eq_app]
    exact hW
  have hc := hstd.comp hW'
  rw [← strV_comp r (i ≫ p) (i ⁻¹ᵁ V) _ h'] at hc
  have hm := sm_of_strV _ _ hA _ hc
  have hw : j ≫ π ≫ p = r ≫ i ≫ p := by rw [← Category.assoc, hpb.w, Category.assoc]
  rw [hw]
  exact hm

end Charts

/- English proof (translation)
Introduce `K _ W Z Y T p i π D d e hB hsm hpr j r hpb`. Take `⟨B⟩` from `hB`. Use `haveI := B.closed`. Establish `hcl : IsClosedImmersion j` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip B.closed`. Establish `hr : IsProper r` using `MorphismProperty.of_isPullback (P := @IsProper) hpb hpr`.

Establish `find : ∀ y : Y, π y ∈ Set.range i → ∃ (α : B.ι) (k : Fin (d + 1)), y ∈ (B.c α).C k ∧ π y ∈ B.V α`. Introduce and unpack `y ⟨w, hw⟩`. Establish `h1 : w ∈ i ⁻¹ᵁ (⨆ α, B.V α)` using `B.cover (show w ∈ (⊤ : W.Opens) from trivial)`. Take `⟨α, hα⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show i w ∈ ⨆ α, B.V α from h1)`. Establish `h2 : π y ∈ B.V α` using `hw ▸ hα`.

Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 ((B.c α).C_cover (show y ∈ π ⁻¹ᵁ B.V α from h2))`. Conclude with `⟨α, k, hk, h2⟩`. Establish `dimE : ∀ (α : B.ι) (z : Z), z ∈ B.V α → (B.c α).n = e`. Introduce `α z hz`. Establish `h1` using `chartZ p i π (B.c α)`.

Establish `h2 : SmoothOfRelativeDimension (0 + (e + (d + 1))) ((B.V α).ι ≫ p)` using `inferInstance`. Use `dim_unique ((B.V α).ι ≫ p) (⟨z, hz⟩ : (B.V α : Scheme.{0})) h1 h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨⟨hcl, ?_, ?_⟩, hr⟩` and prove the remaining obligations. Use `ofPts _ _ fun y => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : π y ∈ B.U`. Use `⟨π ⁻¹ᵁ B.U, hy, ?_⟩ haveI := B.iso` and prove the remaining obligations. Establish `h0 : SmoothOfRelativeDimension (0 + (0 + (e + (d + 1)))) ((π ∣_ B.U) ≫ B.U.ι ≫ p)` using `inferInstance`. Rewrite `h0` using `[Nat.zero_add, Nat.zero_add, ← Category.assoc, morphismRestrict_ι, Category.assoc]`. Conclude with `h0`.

Establish `hrange : π y ∈ Set.range i`. Assume the negation of the conclusion as `h`. Apply `hy` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `π y ∈ (B.U : Set Z)`. Rewrite using `[B.U_eq]`.

Conclude with `h`. Take `⟨α, k, hk, hv⟩` from `find y hrange`. Use `⟨_, hk, ?_⟩` and prove the remaining obligations. Establish `h1` using `chartY p i π (B.c α) k`. Rewrite `h1` using `[dimE α _ hv]`.

Establish `he : d + 1 + e = e + d + 1` using `by omega`. Rewrite `h1` using `[he]`. Conclude with `h1`. Use `ofPts _ _ fun t => ?_` and prove the remaining obligations. Establish `hrange : π (j t) ∈ Set.range i` using `⟨r t, by`.

Use `congr($(hpb.w) t)` as an intermediate fact. Simplify `this.symm⟩` using `only [Scheme.Hom.comp_apply]`. Take `⟨α, k, hk, hv⟩` from `find (j t) hrange`. Use `⟨j ⁻¹ᵁ (B.c α).C k, hk, ?_⟩` and prove the remaining obligations. Establish `h1` using `chartT p i π (B.c α) k j r hpb`.

Rewrite `h1` using `[dimE α _ hv, Nat.add_comm]`. Conclude with `h1`.
-/
theorem blowE : BlowE := by
  intro K _ W Z Y T p i π D d e hB hsm hpr j r hpb
  obtain ⟨B⟩ := hB
  haveI := B.closed
  have hcl : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip B.closed
  have hr : IsProper r := MorphismProperty.of_isPullback (P := @IsProper) hpb hpr
  have find : ∀ y : Y, π y ∈ Set.range i → ∃ (α : B.ι) (k : Fin (d + 1)), y ∈ (B.c α).C k ∧ π y ∈ B.V α := by
    rintro y ⟨w, hw⟩
    have h1 : w ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (show w ∈ (⊤ : W.Opens) from trivial)
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 (show i w ∈ ⨆ α, B.V α from h1)
    have h2 : π y ∈ B.V α := hw ▸ hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((B.c α).C_cover (show y ∈ π ⁻¹ᵁ B.V α from h2))
    exact ⟨α, k, hk, h2⟩
  have dimE : ∀ (α : B.ι) (z : Z), z ∈ B.V α → (B.c α).n = e := by
    intro α z hz
    have h1 := chartZ p i π (B.c α)
    have h2 : SmoothOfRelativeDimension (0 + (e + (d + 1))) ((B.V α).ι ≫ p) := inferInstance
    have := dim_unique ((B.V α).ι ≫ p) (⟨z, hz⟩ : (B.V α : Scheme.{0})) h1 h2
    omega
  refine ⟨⟨hcl, ?_, ?_⟩, hr⟩
  · refine ofPts _ _ fun y => ?_
    by_cases hy : π y ∈ B.U
    · refine ⟨π ⁻¹ᵁ B.U, hy, ?_⟩
      haveI := B.iso
      have h0 : SmoothOfRelativeDimension (0 + (0 + (e + (d + 1)))) ((π ∣_ B.U) ≫ B.U.ι ≫ p) := inferInstance
      rw [Nat.zero_add, Nat.zero_add, ← Category.assoc, morphismRestrict_ι, Category.assoc] at h0
      exact h0
    · have hrange : π y ∈ Set.range i := by
        by_contra h
        apply hy
        change π y ∈ (B.U : Set Z)
        rw [B.U_eq]
        exact h
      obtain ⟨α, k, hk, hv⟩ := find y hrange
      refine ⟨_, hk, ?_⟩
      have h1 := chartY p i π (B.c α) k
      rw [dimE α _ hv] at h1
      have he : d + 1 + e = e + d + 1 := by omega
      rw [he] at h1
      exact h1
  · refine ofPts _ _ fun t => ?_
    have hrange : π (j t) ∈ Set.range i := ⟨r t, by
      have := congr($(hpb.w) t)
      simpa only [Scheme.Hom.comp_apply] using this.symm⟩
    obtain ⟨α, k, hk, hv⟩ := find (j t) hrange
    refine ⟨j ⁻¹ᵁ (B.c α).C k, hk, ?_⟩
    have h1 := chartT p i π (B.c α) k j r hpb
    rw [dimE α _ hv, Nat.add_comm] at h1
    exact h1

end UpperTheory.Gal.KunnethLefschetz.G
