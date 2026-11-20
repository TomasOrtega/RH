import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

noncomputable section

namespace GlobalTheory.CompanLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Conclude with `⟨s, hs, h hx⟩`.
-/
theorem locS_mono {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

/- English proof (translation)
Introduce `x hx` and use `⟨1, S.one_mem, by simpa using hx⟩`.
-/
theorem le_locS {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) (M : Submodule (𝓞 E) W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Take `⟨t, ht, hx'⟩` from `h hx`. Use `⟨t * s, S.mul_mem ht hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `hx'`.
-/
theorem locS_le_of_le {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  refine ⟨t * s, S.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

abbrev conjO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

/- English proof (translation)
Establish `hle : Formalism.HermitianLatticesTheory.hcompl (K` using `E) Q ≤ (Formalism.HermitianLatticesTheory.hcompl (K := E) Q).comap (conjO (E := E)).toMonoidHom := by`. Unfold `Formalism.HermitianLatticesTheory.hcompl`. Rewrite using `[Submonoid.closure_le]`. Introduce and unpack `s ⟨hs1, hs2⟩`. Apply `Submonoid.subset_closure` to reduce the goal to its premises.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hs2 _ rfl`. Introduce `t ht hm`. Establish `: t = s`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Establish `h1 : (t : E) = star (star (s : E))` using `ht`. Simplify using `using h1`. Conclude with `hs1 (this ▸ hm)`. Conclude with `hle hs`.
-/
theorem conjO_mem_hcompl (Q : Ideal (𝓞 E)) {s : 𝓞 E} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q) :
    conjO s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q ≤ (Formalism.HermitianLatticesTheory.hcompl (K := E) Q).comap (conjO (E := E)).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    apply Submonoid.subset_closure
    refine ⟨?_, ?_⟩
    · exact hs2 _ rfl
    · intro t ht hm
      have : t = s := by
        apply RingOfIntegers.ext
        have h1 : (t : E) = star (star (s : E)) := ht
        simpa using h1
      exact hs1 (this ▸ hm)
  exact hle hs

/- English proof (translation)
Unfold `Formalism.UG.hform`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/- English proof (translation)
Unfold `Formalism.UG.hform`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_right {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `Formalism.UG.hform`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_add_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

/- English proof (translation)
Unfold `Formalism.UG.hform`. Simplify using the standard rewrite rules.
-/
theorem hform_zero_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (y : Fin N → E) :
    Formalism.UG.hform σ J 0 y = 0 := by
  unfold Formalism.UG.hform
  simp

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
example {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.BasicNotions.dualSet σ J L ↔ ∀ x ∈ L, Formalism.UG.hform σ J x y ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

/- English proof (translation)
The claim follows from `(algebraMap_smul E c w).symm`.
-/
theorem smul_coe {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (c : 𝓞 E) (w : W) :
    c • w = (c : E) • w := (algebraMap_smul E c w).symm

/- English proof (translation)
Take `⟨s, rfl⟩` from `hfg`. Establish `hg : ∀ g ∈ s, ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `E) Q, t • g ∈ Λ := fun g hg => h (Submodule.subset_span hg)`. Use `choose t ht hts using hg`. Use `set u : 𝓞 E := ∏ g ∈ s.attach, conjO (t g.1 g.2) with hu`. Establish `hu_mem : u ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `E) Q := Submonoid.prod_mem _ fun g _ => conjO_mem_hcompl Q (ht g.1 g.2)`.

Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Use `⟨u, hu_mem, Submodule.subset_span ?_⟩` and prove the remaining obligations. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem g hgs`. Rewrite using `[smul_coe, hform_smul_right]`. Establish `e : u = (∏ g' ∈ s.attach.erase ⟨g, hgs⟩, conjO (t g'.1 g'.2)) * conjO (t g hgs)`. Rewrite using `[hu]`. Conclude with `(Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm`.

Establish `h2 : Formalism.UG.hform (starRingEnd E) J (t g hgs • g) y ∈ (algebraMap (𝓞 E) E).range` using `hy _ (hts g hgs)`. Rewrite `h2` using `[smul_coe, hform_smul_left]`. Rewrite using `[e, show ∀ A B : 𝓞 E, ((A * B : 𝓞 E) : E) = (A : E) * (B : E) from fun _ _ => rfl, mul_assoc]`. Use `Subring.mul_mem _ ⟨_, rfl⟩ ?_` and prove the remaining obligations. Conclude with `h2`.

Consider the case `zero => rw [hform_zero_left]`. Conclude with `Subring.zero_mem _`. Consider the case `add x x' _ _ hx hx' => rw [hform_add_left]`. Conclude with `Subring.add_mem _ hx hx'`. Consider the case `smul c x _ hx`.

Rewrite using `[smul_coe, hform_smul_left]`. Conclude with `Subring.mul_mem _ ⟨conjO c, rfl⟩ hx`.
-/
theorem span_dual_le {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E))
    (hfg : Λ₁.FG) (h : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ) ≤
      Formalism.HermitianLatticesTheory.loc (K := E) Q (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ₁)) := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have hg : ∀ g ∈ s, ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q, t • g ∈ Λ := fun g hg => h (Submodule.subset_span hg)
  choose t ht hts using hg
  set u : 𝓞 E := ∏ g ∈ s.attach, conjO (t g.1 g.2) with hu
  have hu_mem : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q :=
    Submonoid.prod_mem _ fun g _ => conjO_mem_hcompl Q (ht g.1 g.2)
  rw [Submodule.span_le]
  intro y hy
  refine ⟨u, hu_mem, Submodule.subset_span ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hgs =>
    rw [smul_coe, hform_smul_right]
    have e : u = (∏ g' ∈ s.attach.erase ⟨g, hgs⟩, conjO (t g'.1 g'.2)) * conjO (t g hgs) := by
      rw [hu]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm
    have h2 : Formalism.UG.hform (starRingEnd E) J (t g hgs • g) y ∈ (algebraMap (𝓞 E) E).range := hy _ (hts g hgs)
    rw [smul_coe, hform_smul_left] at h2
    rw [e, show ∀ A B : 𝓞 E, ((A * B : 𝓞 E) : E) = (A : E) * (B : E) from fun _ _ => rfl, mul_assoc]
    refine Subring.mul_mem _ ⟨_, rfl⟩ ?_
    exact h2
  | zero => rw [hform_zero_left]; exact Subring.zero_mem _
  | add x x' _ _ hx hx' => rw [hform_add_left]; exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [smul_coe, hform_smul_left]
    exact Subring.mul_mem _ ⟨conjO c, rfl⟩ hx

/- English proof (translation)
Establish `hσ : (sp.cm.sig : E →+* E) = starRingEnd E` using `RingHom.ext fun _ => rfl`. Unfold `compan`. Rewrite using `[hσ]`. Apply `sup_le` to reduce the goal to its premises. Conclude with `h.trans (locS_mono _ le_sup_left)`.

Rewrite using `[Submodule.smul_le]`. Introduce `r hr n hn`. Take `⟨s, hs, hsn⟩` from `span_dual_le J Q Λ Λ₁ hfg h₁ hn`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsn)`.
-/
theorem compan_le_loc {R : Ranks} {F : Type} [Field F] [NumberField F] [Algebra F E] (sp : Spaces R F E) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ₁.FG)
    (h : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) (h₁ : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    compan (sp := sp) J a Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  have hσ : (sp.cm.sig : E →+* E) = starRingEnd E := RingHom.ext fun _ => rfl
  unfold compan
  rw [hσ]
  apply sup_le
  · exact h.trans (locS_mono _ le_sup_left)
  · rw [Submodule.smul_le]
    intro r hr n hn
    obtain ⟨s, hs, hsn⟩ := span_dual_le J Q Λ Λ₁ hfg h₁ hn
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsn)

end GlobalTheory.CompanLoc

namespace GlobalTheory

/- English proof (translation)
Introduce `R F E _ _ _ _ _ _ sp N J a Q Λ Λ₁ hfg hfg₁ h`. Establish `h1 : Λ ≤ Formalism.HermitianLatticesTheory.loc (K` using `E) Q Λ₁ := (CompanLoc.le_locS _ Λ).trans h.le`. Establish `h2 : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K` using `E) Q Λ := (CompanLoc.le_locS _ Λ₁).trans h.ge`. Conclude with `le_antisymm (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ Λ₁ hfg₁ h1 h2)) (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ₁ Λ hfg h2 h1))`.
-/
theorem loc_compan_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)),
    Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ →
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  intro R F E _ _ _ _ _ _ sp N J a Q Λ Λ₁ hfg hfg₁ h
  have h1 : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ := (CompanLoc.le_locS _ Λ).trans h.le
  have h2 : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ := (CompanLoc.le_locS _ Λ₁).trans h.ge
  exact le_antisymm (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ Λ₁ hfg₁ h1 h2))
    (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ₁ Λ hfg h2 h1))

end GlobalTheory
