import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MeasurablePhiInv

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def sigI : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  X.pl.trans (Formalism.MainNotions.BlockEstimateWords.l2Pl D)

/- English proof (translation)
Establish `h : (sigI X v).1 = InfinitePlace.mk (embS D (X.pl v))` using `rfl`. Break down `InfinitePlace.embedding_mk_eq (embS D (X.pl v)) with h1 | h1` into its components or cases. Use `left`. Rewrite using `[h, h1]`. Use `right`.

Rewrite using `[h, h1]`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem embS_sig (v : InfinitePlace X.B.I.F) :
    embS D (X.pl v) = (sigI X v).1.embedding ∨
      embS D (X.pl v) = ComplexEmbedding.conjugate (sigI X v).1.embedding := by
  have h : (sigI X v).1 = InfinitePlace.mk (embS D (X.pl v)) := rfl
  rcases InfinitePlace.embedding_mk_eq (embS D (X.pl v)) with h1 | h1
  · left; rw [h, h1]
  · right; rw [h, h1]
    ext x; simp

/- English proof (translation)
The claim follows from `D.host.der.discr_sq`.
-/
theorem discrE_eq : discr D.host.E = discr D.host.F ^ 2 := D.host.der.discr_sq

/- English proof (translation)
Rewrite using `[← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]`. Conclude with `D.sp.cm.deg2`.
-/
theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]; exact D.sp.cm.deg2

/- English proof (translation)
Rewrite using `[Ideal.absNorm_algebraMap, NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), finrank_O]`.
-/
theorem absNorm_ddS_ideal :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) =
      (discr D.host.F).natAbs ^ 2 := by
  rw [Ideal.absNorm_algebraMap, NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), finrank_O]

/- English proof (translation)
Unfold `ddS`. Rewrite using `[FractionalIdeal.coeIdeal_absNorm, absNorm_ddS_ideal]`.
-/
theorem absNorm_ddS : FractionalIdeal.absNorm (ddS D) = (((discr D.host.F).natAbs ^ 2 : ℕ) : ℚ) := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_absNorm, absNorm_ddS_ideal]

def fHom : X.B.I.F →+* D.host.F where
  toFun := fun a => ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).2 ⟨a, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp
  map_zero' := by ext; simp
  map_add' := fun a b => by ext; simp

def fIso : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective (fHom X)
    ⟨fun a b h => by
        have h1 := congrArg Subtype.val h
        exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h1),
     fun y => by
        obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
        exact ⟨a, Subtype.ext ha⟩⟩

/- English proof (translation)
The claim follows from `discr_eq_discr_of_ringEquiv X.B.I.F (fIso X)`.
-/
theorem discrF_eq : discr X.B.I.F = discr D.host.F := discr_eq_discr_of_ringEquiv X.B.I.F (fIso X)

/- English proof (translation)
Rewrite using `[discrE_eq, discrF_eq]`. Use `push_cast`. Rewrite using `[abs_pow]`.
-/
theorem absDiscrE : |(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| ^ 2 := by
  rw [discrE_eq, discrF_eq]; push_cast; rw [abs_pow]

/- English proof (translation)
Rewrite using `[absDiscrE, Real.sqrt_sq (abs_nonneg _)]`.
-/
theorem sqrtDiscrE : √|(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| := by
  rw [absDiscrE, Real.sqrt_sq (abs_nonneg _)]

/- English proof (translation)
The claim follows from `abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)`.
-/
theorem dF_pos : 0 < |(discr X.B.I.F : ℝ)| :=
  abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)

def embVHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' := fun a b => by funext v; simp [embV]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embVHom_apply (t : D.host.E) : embVHom X t = fun v => embS D (X.pl v) t := rfl

/- English proof (translation)
Introduce `a b h`. Take `⟨v⟩ : Nonempty (InfinitePlace X.B.I.F)` from `inferInstance`. Conclude with `(embS D (X.pl v)).injective (congrFun h v)`.
-/
theorem embVHom_injective : Function.Injective (embVHom X) := by
  intro a b h
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  exact (embS D (X.pl v)).injective (congrFun h v)

/- English proof (translation)
Establish `e : embV X '' (I : Set D.host.E) = embVHom X '' (((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup : AddSubgroup D.host.E) : Set D.host.E)` using `rfl`. Rewrite using `[e]`. Rewrite using `[← AddMonoidHom.map_closure, AddSubgroup.closure_eq]`.
-/
theorem closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    AddSubgroup.closure (embV X '' (I : Set D.host.E)) =
      ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (embVHom X) := by
  have e : embV X '' (I : Set D.host.E) =
      embVHom X '' (((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup : AddSubgroup D.host.E) : Set D.host.E) := rfl
  rw [e]
  rw [← AddMonoidHom.map_closure, AddSubgroup.closure_eq]

/- English proof (translation)
Rewrite using `[closure_embV, AddSubgroup.mem_map]`. Both sides reduce to the same expression.
-/
theorem mem_closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (a : InfinitePlace X.B.I.F → ℂ) :
    a ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embVHom X t = a := by
  rw [closure_embV, AddSubgroup.mem_map]
  rfl

/- English proof (translation)
Use `set C := AddSubgroup.closure (embV X '' (I : Set D.host.E)) with hC`. Use `set ΛE : AddSubgroup D.host.E := (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup with hΛE`. Use `set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := Units.mk0 I hI with hIu`. Establish `hIu' : ((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) = I` using `rfl`. Use `set φ : InfinitePlace X.B.I.F → (D.host.E →+* ℂ) := fun v => embS D (X.pl v) with hφ`.

Establish `hsig : ∀ v, φ v = (sigI X v).1.embedding ∨ φ v = ComplexEmbedding.conjugate (sigI X v).1.embedding` using `fun v => embS_sig X v`. Establish `hΛ : ∀ a ∈ ΛE, a ∈ (Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)` using `fun a ha => ha`. Establish `hk : ΛE.relIndex (((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = 1`. Rewrite using `[hIu']`. Conclude with `AddSubgroup.relIndex_self ΛE`.

Establish `hmemC : ∀ a, a ∈ C ↔ ∃ t ∈ I, embVHom X t = a` using `mem_closure_embV X I`. Establish `hto : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v, (∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F) → ∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F`. Introduce `F v ⟨a, ha, hu⟩`. Use `⟨⟨embVHom X a, (hmemC _).2 ⟨a, a.2, rfl⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify `ha` using `[embVHom_apply, hφ]`.

Introduce and unpack `⟨b, hb⟩ hbF`. Take `⟨t, ht, rfl⟩` from `(hmemC b).1 hb`. Use `hu ⟨t, ht⟩ (by simpa [embVHom_apply, hφ] using hbF)` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression.

Establish `hfrom : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v, (∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F) → ∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F`. Introduce `F v ⟨⟨b, hb⟩, hbF, hu⟩`. Take `⟨t, ht, rfl⟩` from `(hmemC b).1 hb`. Use `⟨⟨t, ht⟩, by simpa [embVHom_apply, hφ] using hbF, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩ haF`.

Use `hu ⟨embVHom X a, (hmemC _).2 ⟨a, ha, rfl⟩⟩ (by simpa [embVHom_apply, hφ] using haF)` as an intermediate fact. Establish `h2 : embVHom X a = embVHom X t` using `congrArg Subtype.val this`. Conclude with `Subtype.ext (embVHom_injective X h2)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: Countable D.host.E`.

Set `b` to `Module.finBasis ℚ D.host.E`. Conclude with `Function.Injective.countable b.equivFun.injective`. Rewrite using `[hC, closure_embV]`. Conclude with `Function.Surjective.countable (f := fun a : ΛE => (⟨embVHom X a, AddSubgroup.mem_map_of_mem _ a.2⟩ : ΛE.map (embVHom X))) (fun ⟨y, hy⟩ => by obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy; exact ⟨⟨a, ha⟩, rfl⟩)`. Take `⟨F, hF, hFd⟩` from `Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ (by rw [hk]; exact one_ne_zero) 1 one_ne_zero`.

Conclude with `⟨F, hF, fun v => hto F v (hFd v)⟩`. Introduce `F hF hFd`. Establish `h` using `Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ 1 hk one_ne_zero 1 one_ne_zero F hF (fun v => hfrom F v (hFd v))`. Rewrite using `[h, hIu', sqrtDiscrE X]`. Use `congr 1`.

Simplify using the standard rewrite rules.
-/
theorem idealBlock (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) :
    Countable (AddSubgroup.closure (embV X '' (I : Set D.host.E))) ∧
    (∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) ∧
    ∀ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal ((FractionalIdeal.absNorm I : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
          |(discr X.B.I.F : ℝ)|) := by
  classical
  set C := AddSubgroup.closure (embV X '' (I : Set D.host.E)) with hC
  set ΛE : AddSubgroup D.host.E := (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup with hΛE
  set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := Units.mk0 I hI with hIu
  have hIu' : ((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) = I := rfl
  set φ : InfinitePlace X.B.I.F → (D.host.E →+* ℂ) := fun v => embS D (X.pl v) with hφ
  have hsig : ∀ v, φ v = (sigI X v).1.embedding ∨ φ v = ComplexEmbedding.conjugate (sigI X v).1.embedding :=
    fun v => embS_sig X v
  have hΛ : ∀ a ∈ ΛE, a ∈ (Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := fun a ha => ha
  have hk : ΛE.relIndex
      (((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup)
      = 1 := by
    rw [hIu']; exact AddSubgroup.relIndex_self ΛE
  have hmemC : ∀ a, a ∈ C ↔ ∃ t ∈ I, embVHom X t = a := mem_closure_embV X I

  have hto : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F) → ∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro F v ⟨a, ha, hu⟩
    refine ⟨⟨embVHom X a, (hmemC _).2 ⟨a, a.2, rfl⟩⟩, ?_, ?_⟩
    · simpa [embVHom_apply, hφ] using ha
    · rintro ⟨b, hb⟩ hbF
      obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
      have := hu ⟨t, ht⟩ (by simpa [embVHom_apply, hφ] using hbF)
      subst this
      rfl
  have hfrom : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F) → ∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F := by
    intro F v ⟨⟨b, hb⟩, hbF, hu⟩
    obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
    refine ⟨⟨t, ht⟩, by simpa [embVHom_apply, hφ] using hbF, ?_⟩
    rintro ⟨a, ha⟩ haF
    have := hu ⟨embVHom X a, (hmemC _).2 ⟨a, ha, rfl⟩⟩ (by simpa [embVHom_apply, hφ] using haF)
    have h2 : embVHom X a = embVHom X t := congrArg Subtype.val this
    exact Subtype.ext (embVHom_injective X h2)
  refine ⟨?_, ?_, ?_⟩
  · have : Countable D.host.E := by
      let b := Module.finBasis ℚ D.host.E
      exact Function.Injective.countable b.equivFun.injective
    rw [hC, closure_embV]
    exact Function.Surjective.countable
      (f := fun a : ΛE => (⟨embVHom X a, AddSubgroup.mem_map_of_mem _ a.2⟩ : ΛE.map (embVHom X)))
      (fun ⟨y, hy⟩ => by obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy; exact ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨F, hF, hFd⟩ := Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ
      (by rw [hk]; exact one_ne_zero) 1 one_ne_zero
    exact ⟨F, hF, fun v => hto F v (hFd v)⟩
  · intro F hF hFd
    have h := Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ 1 hk
      one_ne_zero 1 one_ne_zero F hF (fun v => hfrom F v (hFd v))
    rw [h, hIu', sqrtDiscrE X]
    congr 1
    simp

/- English proof (translation)
Rewrite using `[discrF_eq, Nat.cast_natAbs, Int.cast_abs]`.
-/
theorem dF_natAbs : |(discr X.B.I.F : ℝ)| = ((discr D.host.F).natAbs : ℝ) := by
  rw [discrF_eq, Nat.cast_natAbs, Int.cast_abs]

/- English proof (translation)
Unfold `aaD`. Rewrite using `[map_zpow₀, absNorm_ddS, Rat.cast_zpow, dF_natAbs X]`. Use `push_cast`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem absNorm_aaD (a : Fin D.R.rS) :
    ((FractionalIdeal.absNorm (aaD D a) : ℚ) : ℝ) = |(discr X.B.I.F : ℝ)| ^ (-(2 * ((D.R.rS : ℝ) - (a : ℕ)))) := by
  unfold aaD
  rw [map_zpow₀, absNorm_ddS, Rat.cast_zpow, dF_natAbs X]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

/- English proof (translation)
Introduce `h`. Establish `h1` using `absNorm_aaD Y a`. Rewrite `h1` using `[h, map_zero, Rat.cast_zero]`. Use `Real.rpow_pos_of_pos (dF_pos Y) (-(2 * ((D.R.rS : ℝ) - (a : ℕ))))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aaD_ne_zero (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := by
  intro h
  have h1 := absNorm_aaD Y a
  rw [h, map_zero, Rat.cast_zero] at h1
  have := Real.rpow_pos_of_pos (dF_pos Y) (-(2 * ((D.R.rS : ℝ) - (a : ℕ))))
  linarith

/- English proof (translation)
Rewrite using `[← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_one]`.
-/
theorem rpow_combine {d : ℝ} (hd : 0 < d) {x y z : ℝ} (h : x + y + 1 = z) : d ^ x * d ^ y * d = d ^ z := by
  rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_one]

/- English proof (translation)
Establish `hI : aaD D p.1.1 * (aaD D p.1.2)⁻¹ ≠ 0` using `mul_ne_zero (aaD_ne_zero X _) (inv_ne_zero (aaD_ne_zero X _))`. Take `⟨h1, h2, h3⟩` from `idealBlock X _ hI`. Use `⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩` and prove the remaining obligations. Use `congr 1`. Use `show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))`.

Rewrite using `[map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, absNorm_aaD X, absNorm_aaD X, ← Real.rpow_neg (abs_nonneg _)]`. Rewrite using `[show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockCovol_X (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inl (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inl p))) := by
  have hI : aaD D p.1.1 * (aaD D p.1.2)⁻¹ ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (inv_ne_zero (aaD_ne_zero X _))
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, absNorm_aaD X, absNorm_aaD X, ← Real.rpow_neg (abs_nonneg _)]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

/- English proof (translation)
Establish `hI : aaD D p.1.1 * aaD D p.1.2 ≠ 0` using `mul_ne_zero (aaD_ne_zero X _) (aaD_ne_zero X _)`. Take `⟨h1, h2, h3⟩` from `idealBlock X _ hI`. Use `⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩` and prove the remaining obligations. Use `congr 1`. Use `show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))`.

Rewrite using `[map_mul, Rat.cast_mul, absNorm_aaD X, absNorm_aaD X]`. Rewrite using `[show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockCovol_K (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inr (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inr (Sum.inl p))) := by
  have hI : aaD D p.1.1 * aaD D p.1.2 ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (aaD_ne_zero X _)
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  rw [map_mul, Rat.cast_mul, absNorm_aaD X, absNorm_aaD X]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB
