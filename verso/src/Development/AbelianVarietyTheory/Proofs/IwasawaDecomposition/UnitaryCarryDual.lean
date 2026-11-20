import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

/- English proof (translation)
Establish `hle : tensInt (F` using `F) 𝔸 (intOE E) (intAd F) ≤ (tensInt (F := F) 𝔸 (intOE E) (intAd F)).comap (sigR σ 𝔸) := by conv_lhs => unfold tensInt`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨y, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Subring.mem_comap]`. Take `⟨a, r, hr⟩` from `a`.

Substitute `hr` using the available equality. Establish `hi : IsIntegral ℤ (σ (r : E))` using `map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)`. Express the relevant statement in the definitionally equal form `(σ (r : E)) ⊗ₜ[F] (1 : 𝔸) ∈ _`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨σ (r : E), ⟨⟨σ (r : E), hi⟩, rfl⟩⟩, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Subring.mem_comap]`.

Express the relevant statement in the definitionally equal form `(σ (1 : E)) ⊗ₜ[F] (y : 𝔸) ∈ _`. Rewrite using `[map_one]`. Conclude with `Subring.subset_closure (Or.inr ⟨y, rfl⟩)`. Conclude with `hle hx`.
-/
theorem sigR_int (σ : E →ₐ[F] E) (x : E ⊗[F] 𝔸)
    (hx : x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) :
    sigR σ 𝔸 x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  have hle : tensInt (F := F) 𝔸 (intOE E) (intAd F) ≤
      (tensInt (F := F) 𝔸 (intOE E) (intAd F)).comap (sigR σ 𝔸) := by
    conv_lhs => unfold tensInt
    rw [Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      obtain ⟨a, r, hr⟩ := a
      subst hr
      have hi : IsIntegral ℤ (σ (r : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)
      change (σ (r : E)) ⊗ₜ[F] (1 : 𝔸) ∈ _
      exact Subring.subset_closure (Or.inl ⟨⟨σ (r : E), ⟨⟨σ (r : E), hi⟩, rfl⟩⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      change (σ (1 : E)) ⊗ₜ[F] (y : 𝔸) ∈ _
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  exact hle hx

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨l, hl, rfl⟩` from `hu`. Take `⟨r, hr⟩` from `hz l hl`. Establish `e : (fun i => sigR σ 𝔸 (inclE (F` using `F) 𝔸 (l i))) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) = inclE (F := F) 𝔸 (hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z) := by`.

Establish `h1 : hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z = ∑ i, σ (l i) * z i`. Unfold `hform`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`. Rewrite using `[h1, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Simplify using `only [] at e ⊢`. Rewrite using `[e, ← hr]`.

Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, ⟨r, rfl⟩⟩, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Establish `: (fun i => sigR σ 𝔸 ((a + b) i)) = (fun i => sigR σ 𝔸 (a i)) + (fun i => sigR σ 𝔸 (b i))`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[this, add_dotProduct]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `: (fun i => sigR σ 𝔸 ((c • a) i)) = sigR σ 𝔸 (c : E ⊗[F] 𝔸) • (fun i => sigR σ 𝔸 (a i))`.

Use function extensionality and compare the values at `i`. Simplify using `[Subring.smul_def]`. Rewrite using `[this, smul_dotProduct]`. Conclude with `mul_mem (sigR_int σ _ c.2) ha`.
-/
theorem form_latS_int (σ : E →ₐ[F] E) {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L')
    (u : Fin n → E ⊗[F] 𝔸)
    (hu : u ∈ latS (F := F) 𝔸 (tensInt (F := F) 𝔸 (intOE E) (intAd F)) L') :
    (fun i => sigR σ 𝔸 (u i)) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) ∈
      tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    obtain ⟨r, hr⟩ := hz l hl
    have e : (fun i => sigR σ 𝔸 (inclE (F := F) 𝔸 (l i))) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) =
        inclE (F := F) 𝔸 (hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z) := by
      have h1 : hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z = ∑ i, σ (l i) * z i := by
        unfold hform
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.one_apply]
      rw [h1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      rfl
    simp only [] at e ⊢
    rw [e, ← hr]
    exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨r, rfl⟩⟩, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb =>
    have : (fun i => sigR σ 𝔸 ((a + b) i)) = (fun i => sigR σ 𝔸 (a i)) + (fun i => sigR σ 𝔸 (b i)) := by
      funext i; simp
    rw [this, add_dotProduct]
    exact add_mem ha hb
  | smul c a _ ha =>
    have : (fun i => sigR σ 𝔸 ((c • a) i)) = sigR σ 𝔸 (c : E ⊗[F] 𝔸) • (fun i => sigR σ 𝔸 (a i)) := by
      funext i
      simp [Subring.smul_def]
    rw [this, smul_dotProduct]
    exact mul_mem (sigR_int σ _ c.2) ha

end GlobalTheory.Mem.LevDual

namespace GlobalTheory.Mem.LevDual

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigR_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (σ e) := rfl

/- English proof (translation)
Unfold `hform`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.
-/
theorem hform_one {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold `_root_.Formalism.UG.latS at hv ⊢`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, hx, rfl⟩` from `hv`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `(_root_.Formalism.UG.P.afsplit_prV_inclE w (x i)).symm`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb`. Use `add_mem ha hb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Consider the case `smul c a _ ha`. Establish `hc : _root_.Formalism.UG.prV w (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ _root_.Formalism.BasicNotions.intV (F` using `F) E w := by unfold _root_.Formalism.BasicNotions.intV; exact _root_.Formalism.UG.P.afsplit_prV_int w _ c.2`. Use `Submodule.smul_mem _ (⟨_, hc⟩ : _root_.Formalism.BasicNotions.intV (F := F) E w) ha using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `[Subring.smul_def]`.
-/
private lemma prV_mem_latS (w : HeightOneSpectrum (𝓞 F)) {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E))
    {v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) :
    (fun i => _root_.Formalism.UG.prV w (v i)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L := by
  unfold _root_.Formalism.UG.latS at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨x, hx, ?_⟩
    funext i
    exact (_root_.Formalism.UG.P.afsplit_prV_inclE w (x i)).symm
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    funext i
    simp
  | smul c a _ ha =>
    have hc : _root_.Formalism.UG.prV w (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w :=
      by unfold _root_.Formalism.BasicNotions.intV; exact _root_.Formalism.UG.P.afsplit_prV_int w _ c.2
    convert Submodule.smul_mem _ (⟨_, hc⟩ : _root_.Formalism.BasicNotions.intV (F := F) E w) ha using 1
    funext i
    simp [Subring.smul_def]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold `_root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)`.
-/
private lemma inclE_mem_intV_of_mem_intOE (w : HeightOneSpectrum (𝓞 F)) {a : E} (ha : a ∈ _root_.Formalism.UG.intOE E) :
    _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) a ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold `_root_.Formalism.UG.hform`. Simplify using `[Matrix.one_apply]`.
-/
private lemma hform_one_apply {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (x y : Fin m → A) :
    _root_.Formalism.UG.hform σ 1 x y = ∑ i, σ (x i) * y i := by
  unfold _root_.Formalism.UG.hform
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold `_root_.Formalism.UG.intOE`. Conclude with `⟨⟨σ r, (r.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)⟩, rfl⟩`.
-/
private lemma algHom_coe_mem_intOE (σ : E →ₐ[F] E) (r : 𝓞 E) : σ (r : E) ∈ _root_.Formalism.UG.intOE E := by
  unfold _root_.Formalism.UG.intOE
  exact ⟨⟨σ r, (r.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)⟩, rfl⟩

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold `_root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt at *`. Establish `hle : Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : w.adicCompletion F)) ∪ Set.range fun y : (w.adicCompletionIntegers F).toSubring => (1 : E) ⊗ₜ[F] (y : w.adicCompletion F)) ≤ (Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE …`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨x, rfl⟩ | ⟨y, rfl⟩)`. Take `⟨r, hr⟩ : (x : E) ∈ (algebraMap (𝓞 E) E).range` from `x.2`.

Establish `hσ : σ (x : E) ∈ _root_.Formalism.UG.intOE E` using `by rw [← hr]; exact algHom_coe_mem_intOE σ r`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Use `⟨⟨σ x, hσ⟩, ?_⟩` and prove the remaining obligations. Unfold `_root_.Formalism.UG.sigR`.

Simplify using the standard rewrite rules. Apply `Subring.subset_closure right` to reduce the goal to its premises. Use `⟨y, ?_⟩` and prove the remaining obligations. Unfold `_root_.Formalism.UG.sigR`. Simplify using the standard rewrite rules.

Conclude with `hle hc`.
-/
private lemma sigR_mem_intV' (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    {c : E ⊗[F] w.adicCompletion F} (hc : c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w) :
    _root_.Formalism.UG.sigR σ (w.adicCompletion F) c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt at *
  have hle : Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F]
        (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring => (1 : E) ⊗ₜ[F] (y : w.adicCompletion F)) ≤
      (Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring =>
        (1 : E) ⊗ₜ[F] (y : w.adicCompletion F))).comap (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) := by
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨r, hr⟩ : (x : E) ∈ (algebraMap (𝓞 E) E).range := x.2
      have hσ : σ (x : E) ∈ _root_.Formalism.UG.intOE E := by rw [← hr]; exact algHom_coe_mem_intOE σ r
      apply Subring.subset_closure
      left
      refine ⟨⟨σ x, hσ⟩, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
    · apply Subring.subset_closure
      right
      refine ⟨y, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
  exact hle hc

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Establish `hz' : ∀ y ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 y z ∈ (algebraMap (𝓞 E) E).range` using `hz`. Unfold `_root_.Formalism.UG.latS at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨y, hy, rfl⟩` from `hv`.

Establish `h` using `inclE_mem_intV_of_mem_intOE (F := F) w (hz' y hy)`. Rewrite `h` using `[hform_one_apply, map_sum]`. Use `h using 2 with j` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`. Use `congr 1`.

Apply the tactic sequence `all_goals (unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE; simp)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Use `add_mem ha hb using 1` and compare the differences between its conclusion and the goal. Simplify using `[map_add, add_mul, Finset.sum_add_distrib]`.

Consider the case `smul c a _ ha`. Use `mul_mem (sigR_mem_intV' σ w c.2) ha using 1` and compare the differences between its conclusion and the goal. Simplify using `[Subring.smul_def, map_mul, Finset.mul_sum, mul_assoc]`.
-/
private lemma pairing_mem_intV_of_mem_dualSet (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {m : ℕ}
    (L : Submodule (𝓞 E) (Fin m → E)) {z : Fin m → E} (hz : z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L)
    {x : Fin m → E ⊗[F] w.adicCompletion F}
    (hx : x ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L) :
    ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) (x j) * _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z j) ∈
      _root_.Formalism.BasicNotions.intV (F := F) E w := by
  have hz' : ∀ y ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 y z ∈ (algebraMap (𝓞 E) E).range := hz
  unfold _root_.Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    have h := inclE_mem_intV_of_mem_intOE (F := F) w (hz' y hy)
    rw [hform_one_apply, map_sum] at h
    convert h using 2 with j
    rw [map_mul]
    congr 1
    all_goals (unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE; simp)
  | zero => simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    simp [map_add, add_mul, Finset.sum_add_distrib]
  | smul c a _ ha =>
    convert mul_mem (sigR_mem_intV' σ w c.2) ha using 1
    simp [Subring.smul_def, map_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ w n J L p hJ hp hL L' Y hY hLat z hz`. Substitute `hJ` using the available equality. Consider the cases of `n with`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal.

Consider the case `succ m => set Yw := _root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y with hYw_def`. Establish `hYwU : Yw ∈ _root_.Formalism.UG.UPts σ 1 (w.adicCompletion F)` using `_root_.Formalism.UG.P.afsplit_bc_mem σ 1 w Y hY`. Establish `hunit : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) * (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) = 1`. Establish `h` using `hYwU`. Unfold `_root_.Formalism.UG.UPts _root_.Formalism.UG.UJ at h`.

Express the relevant statement in the definitionally equal form `_ * _ * _ = _ at h`. Rewrite `h` using `[Matrix.map_one _ (map_zero _) (map_one _), mul_one]`. Then use the resulting hypothesis. Establish `hinv : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) _) = _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _)`. Combine the equalities or inequalities in the displayed calculation. Use `set v : Fin (m + 1) → E ⊗[F] w.adicCompletion F := fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a) with hv`.

Establish `hu_apply : ∀ i, (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i = ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j i) * v j`. Introduce `i`. Rewrite using `[hinv]`. Unfold `_root_.Formalism.UG.cT`. Simplify using `[Matrix.mulVec, dotProduct]`.

Establish `hcol : ∀ x ∈ L, (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ (fun a => _root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) (x a)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L' := by`. Introduce `x hx`. Establish `hA : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ (fun a => _root_.Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (x a)) ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' := by`. Rewrite using `[hLat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.

Establish `h` using `prV_mem_latS w L' hA`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[hYw_def, _root_.Formalism.UG.P.afsplit_coe_bc_prV, RingHom.map_mulVec]`. Use `congr 1`.

Establish `hlast : ∀ j : Fin (m + 1), j.1 + 1 = m + 1 ↔ j = Fin.last m` using `fun j => by`. Rewrite using `[Fin.ext_iff, Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Establish `hsingle : ∀ i, i ≠ Fin.last m → (Pi.single i 1 : Fin (m + 1) → E) ∈ L`. Introduce `i hi`.

Rewrite using `[hL]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Conclude with `⟨1, by simp, fun h => absurd ((hlast j).1 h) hi⟩`.

Conclude with `⟨0, by simp [hj], fun _ => dvd_zero p⟩`. Establish `hpL : (Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) ∈ L`. Rewrite using `[hL]`. Introduce `j`. Distinguish the cases in `hj : j = Fin.last m`.

Substitute `hj` using the available equality. Conclude with `⟨p, by simp, fun _ => dvd_refl _⟩`. Conclude with `⟨0, by simp [hj], fun _ => dvd_zero p⟩`. Establish `hcoef_low : ∀ i, i ≠ Fin.last m → (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i ∈ _root_.Formalism.BasicNotions.intV (F` using `F) E w := by`. Introduce `i hi`.

Establish `h` using `pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ (hsingle i hi))`. Rewrite using `[hu_apply]`. Use `h using 2 with j` and compare the differences between its conclusion and the goal. Use `congr 2`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Establish `hcoef_last : _root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) (σ (p : E)) * (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) (Fin.last m) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by`. Establish `h` using `pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ hpL)`. Rewrite using `[hu_apply, Finset.mul_sum]`. Use `h using 2 with j` and compare the differences between its conclusion and the goal. Establish `hc : ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ (fun a => _root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a))) j = (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j (Fin.last m) * _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E) := by`.

Establish `hv' : (fun a => _root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a)) = Pi.single (Fin.last m) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) := by`. Use function extensionality and compare the values at `a`. Distinguish the cases in `ha : a = Fin.last m`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[ha]`. Rewrite using `[hv']`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hc, map_mul]`. Establish `hs : _root_.Formalism.UG.sigR σ (w.adicCompletion F) (_root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) (p : E)) = _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) := by`.

Unfold `_root_.Formalism.UG.sigR _root_.Formalism.UG.inclE`. Simplify using the standard rewrite rules. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd_single : ∀ i, (Pi.single i 1 : Fin (m + 1) → E) ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L`.

Introduce `i`. Use `show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x _ ∈ (algebraMap (𝓞 E) E).range`. Introduce `x hx`. Take `⟨r, hr, _⟩` from `(hL x).1 hx i`. Establish `hc : σ (r : E) ∈ (algebraMap (𝓞 E) E).range` using `algHom_coe_mem_intOE σ r`.

Rewrite using `[hform_one_apply]`. Simplify `hc` using `[Pi.single_apply, hr]`. Establish `hq : σ (p : E) ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises.

Establish `h' : (p : E) = 0` using `σ.injective (h.trans (map_zero σ).symm)`. Conclude with `h'` after adjusting the coercions. Use `set e0 : Fin (m + 1) → E := Pi.single (Fin.last m) (σ (p : E))⁻¹ with he0_def`. Establish `he0 : e0 ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L` using `by show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x e0 ∈ (algebraMap (𝓞 E) E).range`. Introduce `x hx`.

Take `⟨r, hxr, hdiv⟩` from `(hL x).1 hx (Fin.last m)`. Take `⟨c, rfl⟩` from `hdiv (by simp)`. Rewrite using `[hform_one_apply]`. Establish `hc : σ (c : E) ∈ (algebraMap (𝓞 E) E).range` using `algHom_coe_mem_intOE σ c`. Establish `key : σ (x (Fin.last m)) * (σ (p : E))⁻¹ = σ (c : E)`.

Rewrite using `[hxr]`. Use `push_cast`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Simplify `hc` using `[he0_def, Pi.single_apply, key]`.

Set `d : Fin (m + 1) → Fin (m + 1) → E` to `fun i => if i = Fin.last m then e0 else Pi.single i 1`. Establish `hd : ∀ i, d i ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L`. Introduce `i`. Distinguish the cases in `h : i = Fin.last m`. Simplify using `only [d, h, if_true]`.

Conclude with `he0`. Simplify using `only [d, h, if_false]`. Conclude with `hd_single i`. Set `c : Fin (m + 1) → _root_.Formalism.BasicNotions.intV (F` to `F) E w := fun i => if h : i = Fin.last m then ⟨_, hcoef_last⟩ else ⟨_, hcoef_low i h⟩`. Establish `hsum : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v = ∑ i, c i • (fun a => _root_.Formalism.UG.inclE (F` using `F) (w.adicCompletion F) (d i a)) := by`.

Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single k]`. Distinguish the cases in `hk : k = Fin.last m`. Substitute `hk` using the available equality. Simplify using `only [c, d, dif_pos, if_pos, Pi.smul_apply, Subring.smul_def, smul_eq_mul, he0_def, Pi.single_eq_same]`.

Rewrite using `[mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]`. Simplify using `[c, d, hk, Subring.smul_def]`. Introduce `b _ hb`. Distinguish the cases in `hbl : b = Fin.last m`. Substitute `hbl` using the available equality.

Simplify using `[c, d, he0_def, Pi.single_apply, Ne.symm hb, Subring.smul_def]`. Simplify using `[c, d, hbl, Pi.single_apply, Ne.symm hb, Subring.smul_def]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨d i, Submodule.subset_span (hd i), rfl⟩)`.
-/
theorem _root_.GlobalTheory.Mem.LevDual.unitary_carry_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ _root_.Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) → ∀ z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L', ((_root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L)) := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL L' Y hY hLat z hz
  subst hJ
  cases n with
  | zero =>
    convert Submodule.zero_mem _ using 1
  | succ m =>
    set Yw := _root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y with hYw_def
    have hYwU : Yw ∈ _root_.Formalism.UG.UPts σ 1 (w.adicCompletion F) := _root_.Formalism.UG.P.afsplit_bc_mem σ 1 w Y hY
    have hunit : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
        (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) = 1 := by
      have h := hYwU
      unfold _root_.Formalism.UG.UPts _root_.Formalism.UG.UJ at h
      change _ * _ * _ = _ at h
      rwa [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h
    have hinv : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) =
        _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by
      calc ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) _)
          = (_root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
              (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _)) * ((Yw⁻¹ : GL (Fin (m + 1)) _) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by rw [hunit, one_mul]
        _ = _ := by rw [mul_assoc, Units.mul_inv, mul_one]
    set v : Fin (m + 1) → E ⊗[F] w.adicCompletion F :=
      fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a) with hv
    have hu_apply : ∀ i, (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i =
        ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j i) * v j := by
      intro i
      rw [hinv]
      unfold _root_.Formalism.UG.cT
      simp [Matrix.mulVec, dotProduct]
    have hcol : ∀ x ∈ L, (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
        (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (x a)) ∈
        _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L' := by
      intro x hx
      have hA : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) ∈
          _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
            (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' := by
        rw [hLat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      have h := prV_mem_latS w L' hA
      convert h using 1
      funext i
      rw [hYw_def, _root_.Formalism.UG.P.afsplit_coe_bc_prV, RingHom.map_mulVec]
      congr 1
    have hlast : ∀ j : Fin (m + 1), j.1 + 1 = m + 1 ↔ j = Fin.last m := fun j => by
      rw [Fin.ext_iff, Fin.val_last]
      omega
    have hsingle : ∀ i, i ≠ Fin.last m → (Pi.single i 1 : Fin (m + 1) → E) ∈ L := by
      intro i hi
      rw [hL]
      intro j
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp, fun h => absurd ((hlast j).1 h) hi⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hpL : (Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) ∈ L := by
      rw [hL]
      intro j
      by_cases hj : j = Fin.last m
      · subst hj
        exact ⟨p, by simp, fun _ => dvd_refl _⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hcoef_low : ∀ i, i ≠ Fin.last m → (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      intro i hi
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ (hsingle i hi))
      rw [hu_apply]
      convert h using 2 with j
      congr 2
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcoef_last : _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) *
        (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) (Fin.last m) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ hpL)
      rw [hu_apply, Finset.mul_sum]
      convert h using 2 with j
      have hc : ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a))) j =
          (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j (Fin.last m) *
            _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E) := by
        have hv' : (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a)) =
            Pi.single (Fin.last m) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) := by
          funext a
          by_cases ha : a = Fin.last m
          · subst ha
            simp
          · simp [ha]
        rw [hv']
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hc, map_mul]
      have hs : _root_.Formalism.UG.sigR σ (w.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) =
          _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) := by
        unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE
        simp
      rw [hs]
      ring
    have hd_single : ∀ i, (Pi.single i 1 : Fin (m + 1) → E) ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x _ ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hr, _⟩ := (hL x).1 hx i
      have hc : σ (r : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ r
      rw [hform_one_apply]
      simpa [Pi.single_apply, hr] using hc
    have hq : σ (p : E) ≠ 0 := by
      intro h
      apply hp
      have h' : (p : E) = 0 := σ.injective (h.trans (map_zero σ).symm)
      exact_mod_cast h'
    set e0 : Fin (m + 1) → E := Pi.single (Fin.last m) (σ (p : E))⁻¹ with he0_def
    have he0 : e0 ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x e0 ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hxr, hdiv⟩ := (hL x).1 hx (Fin.last m)
      obtain ⟨c, rfl⟩ := hdiv (by simp)
      rw [hform_one_apply]
      have hc : σ (c : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ c
      have key : σ (x (Fin.last m)) * (σ (p : E))⁻¹ = σ (c : E) := by
        rw [hxr]
        push_cast
        rw [map_mul]
        field_simp
      simpa [he0_def, Pi.single_apply, key] using hc
    let d : Fin (m + 1) → Fin (m + 1) → E := fun i => if i = Fin.last m then e0 else Pi.single i 1
    have hd : ∀ i, d i ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      by_cases h : i = Fin.last m
      · simp only [d, h, if_true]
        exact he0
      · simp only [d, h, if_false]
        exact hd_single i
    let c : Fin (m + 1) → _root_.Formalism.BasicNotions.intV (F := F) E w := fun i =>
      if h : i = Fin.last m then ⟨_, hcoef_last⟩ else ⟨_, hcoef_low i h⟩
    have hsum : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v =
        ∑ i, c i • (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (d i a)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · by_cases hk : k = Fin.last m
        · subst hk
          simp only [c, d, dif_pos, if_pos, Pi.smul_apply, Subring.smul_def, smul_eq_mul, he0_def,
            Pi.single_eq_same]
          rw [mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
        · simp [c, d, hk, Subring.smul_def]
      · intro b _ hb
        by_cases hbl : b = Fin.last m
        · subst hbl
          simp [c, d, he0_def, Pi.single_apply, Ne.symm hb, Subring.smul_def]
        · simp [c, d, hbl, Pi.single_apply, Ne.symm hb, Subring.smul_def]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨d i, Submodule.subset_span (hd i), rfl⟩)

end GlobalTheory.Mem.LevDual
