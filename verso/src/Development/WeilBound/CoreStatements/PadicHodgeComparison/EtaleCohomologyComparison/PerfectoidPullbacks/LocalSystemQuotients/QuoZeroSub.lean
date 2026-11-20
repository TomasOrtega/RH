import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.Functor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijectiveStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijCov
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTransStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsQ

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

section Gen

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem mapH_comp {K L P : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L P (RingHom.id R)) (j : ℕ)
    (x : K.H j) : (φ.comp ψ).mapH j x = ψ.mapH j (φ.mapH j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/- English proof (translation)
Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `congrArg Submodule.Quotient.mk (Subtype.ext (h j z))`.
-/
theorem mapH_eq_self {K : Cx.{1} R} (φ : Cx.Hom K K (RingHom.id R)) (h : ∀ i x, φ.f i x = x) (j : ℕ) (x : K.H j) :
    φ.mapH j x = x := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h j z))

def hinv {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) :
    Cx.Hom L K (RingHom.id R) where
  f i := (LinearEquiv.ofBijective (φ.f i) (h i)).symm.toLinearMap
  comm i y := (h (i + 1)).1 (by
    have e : ∀ i y, φ.f i ((LinearEquiv.ofBijective (φ.f i) (h i)).symm y) = y := fun i y =>
      (LinearEquiv.ofBijective (φ.f i) (h i)).apply_symm_apply y
    change φ.f (i + 1) (K.d i ((LinearEquiv.ofBijective (φ.f i) (h i)).symm y)) =
      φ.f (i + 1) ((LinearEquiv.ofBijective (φ.f (i + 1)) (h (i + 1))).symm (L.d i y))
    rw [← φ.comm, e, e])

/- English proof (translation)
The claim follows from `(LinearEquiv.ofBijective (φ.f i) (h i)).symm_apply_apply x`.
-/
theorem hinv_left {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ)
    (x : K.X i) : (hinv φ h).f i (φ.f i x) = x := (LinearEquiv.ofBijective (φ.f i) (h i)).symm_apply_apply x

/- English proof (translation)
The claim follows from `(LinearEquiv.ofBijective (φ.f i) (h i)).apply_symm_apply y`.
-/
theorem hinv_right {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ)
    (y : L.X i) : φ.f i ((hinv φ h).f i y) = y := (LinearEquiv.ofBijective (φ.f i) (h i)).apply_symm_apply y

/- English proof (translation)
The claim follows from `(LinearEquiv.ofBijective (φ.f i) (h i)).symm.bijective`.
-/
theorem hinv_bij {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ) :
    Function.Bijective ((hinv φ h).f i) := (LinearEquiv.ofBijective (φ.f i) (h i)).symm.bijective

/- English proof (translation)
Use `⟨Function.LeftInverse.injective (g := (hinv φ h).mapH j) fun x => ?_, Function.RightInverse.surjective (g := (hinv φ h).mapH j) fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← mapH_comp]`. Conclude with `mapH_eq_self _ (hinv_left φ h) j x`. Rewrite using `[← mapH_comp]`. Conclude with `mapH_eq_self _ (hinv_right φ h) j y`.
-/
theorem mapH_bij {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (j : ℕ) :
    Function.Bijective (φ.mapH j) := by
  refine ⟨Function.LeftInverse.injective (g := (hinv φ h).mapH j) fun x => ?_,
    Function.RightInverse.surjective (g := (hinv φ h).mapH j) fun y => ?_⟩
  · rw [← mapH_comp]; exact mapH_eq_self _ (hinv_left φ h) j x
  · rw [← mapH_comp]; exact mapH_eq_self _ (hinv_right φ h) j y

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem pull_comp {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {F'' : C'' ⥤ ModuleCat.{0} R}
    (m : CH.Mor F F' (RingHom.id R)) (m' : CH.Mor F' F'' (RingHom.id R)) (j : ℕ) (x : CH.H F j) :
    (m.comp m').pull j x = m'.pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

def zh (K L : Cx.{1} R) : Cx.Hom K L (RingHom.id R) := ⟨fun _ => 0, fun _ _ => by simp⟩

/- English proof (translation)
Establish `hX : Subsingleton ((quo l K 0).X j)`. Use `Submodule.Quotient.subsingleton_iff.2 ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`. Conclude with `⟨x, by simp⟩`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Rewrite using `[Subsingleton.elim a b]`.
-/
theorem quo_zero_sub (l : ℕ) (K : Cx.{1} R) (j : ℕ) : Subsingleton ((quo l K 0).H j) := by
  have hX : Subsingleton ((quo l K 0).X j) := by
    refine Submodule.Quotient.subsingleton_iff.2 ?_
    rw [eq_top_iff]
    intro x _
    exact ⟨x, by simp⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

end Gen

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {F : B.Fn O} {ρ : O →+* k}

/- English proof (translation)
Establish `hW : Subsingleton (Wc.Wm l k 0)`. Use `Ideal.Quotient.subsingleton_iff.2 ?_` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.span_singleton_one]`. Establish `hT : ∀ T : (fl l F ρ 0).FullSubcategory, Subsingleton T.obj.B` using `fun T => subsingleton_of_zero_eq_one (by rw [← map_zero T.obj.i, Subsingleton.elim (0 : Wc.Wm l k 0) 1, map_one])`. Establish `hX : Subsingleton ((Kt l F ρ 0).X j)` using `⟨fun f g => funext fun s => @Subsingleton.elim _ (hT (s.obj (Fin.last j))) (f s) (g s)⟩`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, ha⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨⟨b, hb⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Establish `: a = b` using `Subsingleton.elim a b`. Substitute `this` using the available equality.

Both sides reduce to the same expression.
-/
theorem Kt_zero_sub (j : ℕ) : Subsingleton ((Kt l F ρ 0).H j) := by
  have hW : Subsingleton (Wc.Wm l k 0) := by
    refine Ideal.Quotient.subsingleton_iff.2 ?_
    rw [pow_zero, Ideal.span_singleton_one]
  have hT : ∀ T : (fl l F ρ 0).FullSubcategory, Subsingleton T.obj.B := fun T =>
    subsingleton_of_zero_eq_one (by rw [← map_zero T.obj.i, Subsingleton.elim (0 : Wc.Wm l k 0) 1, map_one])
  have hX : Subsingleton ((Kt l F ρ 0).X j) :=
    ⟨fun f g => funext fun s => @Subsingleton.elim _ (hT (s.obj (Fin.last j))) (f s) (g s)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have : a = b := Subsingleton.elim a b
  subst this
  rfl

section Pos

variable {n : ℕ} (hn : n ≠ 0)

variable (F ρ) in

def psiP : Cx.Hom (Kt l F ρ n) (quo l (Kt l F ρ (n + 1)) n) (RingHom.id _) :=
  ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).hom.comp
    (hinv (cmpq (sW l F ρ (n + 1)).A l n) fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i)

/- English proof (translation)
Rewrite using `[psiP, mapH_comp, ← mapH_comp]`. Conclude with `mapH_eq_self _ (fun i x => hinv_right (cmpq (sW l F ρ (n + 1)).A l n) (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) i x) j _`.
-/
theorem cmpq_psiP (j : ℕ) (y : (Kt l F ρ n).H j) :
    (cmpq (sW l F ρ (n + 1)).A l n).mapH j ((psiP F ρ hn).mapH j y) =
      ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j y := by
  rw [psiP, mapH_comp, ← mapH_comp]
  exact mapH_eq_self _ (fun i x =>
    hinv_right (cmpq (sW l F ρ (n + 1)).A l n) (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) i x) j _

/- English proof (translation)
Rewrite using `[← mapH_comp]`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Both sides reduce to the same expression.
-/
theorem cmpq_prj (j : ℕ) (z : (Kt l F ρ (n + 1)).H j) :
    (cmpq (sW l F ρ (n + 1)).A l n).mapH j ((prj l (Kt l F ρ (n + 1)) n).mapH j z) =
      (qM (sW l F ρ (n + 1)).A l n).pull j z := by
  rw [← mapH_comp]
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

def qαN : ((qM (sW l F ρ (n + 1)).A l n).G ⋙ (fl l F ρ (n + 1)).ι) ⟶
    ((qG hn ⋙ (fl l F ρ n).ι) ⋙ (Wc.redM l F ρ n).functor) where
  app T := qα hn T.obj
  naturality _ _ f := (qα_nat hn f.hom).symm

/- English proof (translation)
Apply `(mapH_bij _ (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) j).1` to reduce the goal to its premises. Rewrite using `[cmpq_psiP, cmpq_prj]`. Establish `key` using `GlobalTheory.T.pull_eq_of_nat_trans _ _ _ _ _ ((CH.Mor.restrict (Wc.OM l F ρ (n + 1)) (fl l F ρ (n + 1)).ι).comp (qM (sW l F ρ (n + 1)).A l n)) ((Wc.redMor l F ρ n).comp ((CH.Mor.restrict (Wc.OM l F ρ n) (fl l F ρ n).ι).comp ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun …`. Establish `h1` using `congrArg (fun g => g x) key`. Simplify using `only [pull_comp] at h1`.

Conclude with `h1.symm`.
-/
theorem psiP_compat (j : ℕ) (x : (Wc.HS l F ρ j).M (n + 1)) :
    (psiP F ρ hn).mapH j (resF l F ρ n j ((Wc.HS l F ρ j).r n x)) =
      (prj l (Kt l F ρ (n + 1)) n).mapH j (resF l F ρ (n + 1) j x) := by
  apply (mapH_bij _ (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) j).1
  rw [cmpq_psiP, cmpq_prj]
  have key := GlobalTheory.T.pull_eq_of_nat_trans _ _ _ _ _
    ((CH.Mor.restrict (Wc.OM l F ρ (n + 1)) (fl l F ρ (n + 1)).ι).comp (qM (sW l F ρ (n + 1)).A l n))
    ((Wc.redMor l F ρ n).comp ((CH.Mor.restrict (Wc.OM l F ρ n) (fl l F ρ n).ι).comp
      ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl))))
    (qαN hn) (fun _ _ => rfl) j
  have h1 := congrArg (fun g => g x) key
  simp only [pull_comp] at h1
  exact h1.symm

end Pos

/- English proof (translation)
Introduce `l _ K r M hM`. Use `⟨fun n => if hn : n = 0 then zh _ _ else psiP (B.schFn M.p) r.ρ hn, fun n j => ?_, fun n j x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Use `Kt_zero_sub (F := B.schFn M.p) (ρ := r.ρ) j` as an intermediate fact.

Use `quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j` as an intermediate fact. Conclude with `⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩`. Simplify using `only`. Rewrite using `[dif_neg hn]`. Establish `e : ∀ y, (psiP (B.schFn M.p) r.ρ hn).mapH j y = (hinv (cmpq (sW l (B.schFn M.p) r.ρ (n + 1)).A l n) fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l (B.schFn M.p) r.ρ (n + 1)).A l n i).mapH j (((mq hn).o (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pul …` using `fun y => mapH_comp _ _ j y`.

Rewrite using `[show ⇑((psiP (B.schFn M.p) r.ρ hn).mapH j) = _ from funext e]`. Conclude with `(mapH_bij _ (hinv_bij _ _) j).comp (SubquotientResolution.bij r M hM n hn j)`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Use `quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j` as an intermediate fact.

Conclude with `Subsingleton.elim _ _`. Simplify using `only`. Rewrite using `[dif_neg hn]`. Conclude with `psiP_compat hn j x`.
-/
theorem seqflat0_pf : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K),
    M.Sm → ∃ (ψ : ∀ n, Cx.Hom (Kt l (B.schFn M.p) r.ρ n) (quo l (Kt l (B.schFn M.p) r.ρ (n + 1)) n) (RingHom.id _))
      (_ : ∀ n j, Function.Bijective ((ψ n).mapH j)), ∀ n j x,
      (ψ n).mapH j (resF l (B.schFn M.p) r.ρ n j ((Wc.HS l (B.schFn M.p) r.ρ j).r n x)) =
        (prj l (Kt l (B.schFn M.p) r.ρ (n + 1)) n).mapH j (resF l (B.schFn M.p) r.ρ (n + 1) j x) := by
  intro l _ K r M hM
  refine ⟨fun n => if hn : n = 0 then zh _ _ else psiP (B.schFn M.p) r.ρ hn, fun n j => ?_, fun n j x => ?_⟩
  · by_cases hn : n = 0
    · subst hn
      have := Kt_zero_sub (F := B.schFn M.p) (ρ := r.ρ) j
      have := quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j
      exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · dsimp only
      rw [dif_neg hn]
      have e : ∀ y, (psiP (B.schFn M.p) r.ρ hn).mapH j y =
          (hinv (cmpq (sW l (B.schFn M.p) r.ρ (n + 1)).A l n)
            fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l (B.schFn M.p) r.ρ (n + 1)).A l n i).mapH j
          (((mq hn).o (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pull j y) := fun y =>
        mapH_comp _ _ j y
      rw [show ⇑((psiP (B.schFn M.p) r.ρ hn).mapH j) = _ from funext e]
      exact (mapH_bij _ (hinv_bij _ _) j).comp (SubquotientResolution.bij r M hM n hn j)
  · by_cases hn : n = 0
    · subst hn
      have := quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j
      exact Subsingleton.elim _ _
    · dsimp only
      rw [dif_neg hn]
      exact psiP_compat hn j x

end CrystallineSemistableComparison.Pb.LsQ

end
