import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.FlagVectorMemLocalization
import Lemmata.GeneralBFactThirdForm.Imports

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open NumberField Module

section Quot

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

abbrev Xc (W X : Submodule E V) : Submodule E W := X.comap W.subtype

abbrev QW (W X : Submodule E V) : Type := W ⧸ Xc W X

def qForm1 (h : V →ₗ⋆[E] V →ₗ[E] E) (W X : Submodule E V)
    (hR : ∀ x ∈ W, ∀ y ∈ X, h x y = 0) : W →ₗ⋆[E] QW W X →ₗ[E] E where
  toFun w := (Xc W X).liftQ (h.domRestrict₁₂ W W w) (by
    intro y hy
    simp only [LinearMap.mem_ker, LinearMap.domRestrict₁₂_apply]
    exact hR _ w.2 _ hy)
  map_add' a b := by
    apply Submodule.linearMap_qext
    ext y
    simp
  map_smul' c a := by
    apply Submodule.linearMap_qext
    ext y
    simp

def qForm (h : V →ₗ⋆[E] V →ₗ[E] E) (W X : Submodule E V)
    (hR : ∀ x ∈ W, ∀ y ∈ X, h x y = 0) (hL : ∀ x ∈ X, ∀ y ∈ W, h x y = 0) :
    QW W X →ₗ⋆[E] QW W X →ₗ[E] E :=
  (Xc W X).liftQ (qForm1 h W X hR) (by
    intro x hx
    simp only [LinearMap.mem_ker]
    apply Submodule.linearMap_qext
    ext y
    simp only [qForm1, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.domRestrict₁₂_apply, LinearMap.zero_comp,
      LinearMap.zero_apply]
    exact hL _ hx _ y.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qForm_mk (h : V →ₗ⋆[E] V →ₗ[E] E) (W X : Submodule E V)
    (hR : ∀ x ∈ W, ∀ y ∈ X, h x y = 0) (hL : ∀ x ∈ X, ∀ y ∈ W, h x y = 0) (a b : W) :
    qForm h W X hR hL (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = h a b := rfl

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with | H a => ?_`. Proceed by induction on `y using Submodule.Quotient.induction_on with | H b => ?_`. Rewrite using `[qForm_mk, qForm_mk]`. Conclude with `hs.eq _ _`.
-/
theorem qForm_isSymm (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (W X : Submodule E V)
    (hR : ∀ x ∈ W, ∀ y ∈ X, h x y = 0) (hL : ∀ x ∈ X, ∀ y ∈ W, h x y = 0) :
    (qForm h W X hR hL).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [qForm_mk, qForm_mk]
  exact hs.eq _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Rewrite `hv` using `[← hU]`. Take `⟨y, hy, hyv⟩` from `hv`. Establish `: y = v` using `γ.injective hyv`.

Conclude with `this ▸ hy`. Introduce `hv`. Rewrite using `[← hU]`. Conclude with `Submodule.mem_map_of_mem hv`.
-/
theorem mem_of_map_eq {γ : V ≃ₗ[E] V} {U U' : Submodule E V} (hU : U.map (γ : V →ₗ[E] V) = U') (v : V) :
    γ v ∈ U' ↔ v ∈ U := by
  constructor
  · intro hv
    rw [← hU] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    have : y = v := γ.injective hyv
    exact this ▸ hy
  · intro hv
    rw [← hU]
    exact Submodule.mem_map_of_mem hv

def qEquiv (δ : V ≃ₗ[E] V) (W X : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : X.map (δ : V →ₗ[E] V) = X) : QW W X ≃ₗ[E] QW W X :=
  Submodule.Quotient.equiv (Xc W X) (Xc W X) (δ.ofSubmodules W W hW) (by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hy ⊢
      rw [LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_apply]
      exact (mem_of_map_eq hX _).2 hy
    · intro hw
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hw
      have h1 : δ (δ.symm w) ∈ W := by simpa using w.2
      have h2 : δ (δ.symm w) ∈ X := by simpa using hw
      refine ⟨⟨δ.symm w, (mem_of_map_eq hW _).1 h1⟩, (mem_of_map_eq hX _).1 h2, ?_⟩
      apply Subtype.ext
      simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qEquiv_mk (δ : V ≃ₗ[E] V) (W X : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : X.map (δ : V →ₗ[E] V) = X) (w : W) :
    qEquiv δ W X hW hX (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨δ w, (mem_of_map_eq hW _).2 w.2⟩ := rfl

def qLat (Λ : Submodule (𝓞 E) V) (W X : Submodule E V) : Submodule (𝓞 E) (QW W X) :=
  (Λ.comap ((W.subtype).restrictScalars (𝓞 E))).map ((Xc W X).mkQ.restrictScalars (𝓞 E))

/- English proof (translation)
Simplify using `[qLat]`.
-/
theorem mem_qLat {Λ : Submodule (𝓞 E) V} {W X : Submodule E V} {q : QW W X} :
    q ∈ qLat Λ W X ↔ ∃ w : W, (w : V) ∈ Λ ∧ Submodule.Quotient.mk w = q := by
  simp [qLat]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_third_form.goal1 .. | (apply Bl.general_b_fact_third_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_form.goal1 <;> assumption)`.
-/
theorem exists_smul_mem (Λ : Submodule (𝓞 E) V) [hΛ : Submodule.IsLattice E Λ] (v : V) :
    ∃ s : 𝓞 E, s ≠ 0 ∧ s • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_form.goal1 .. | (apply Bl.general_b_fact_third_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_form.goal1 <;> assumption)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.FG.map _ ?_` and prove the remaining obligations. Use `Submodule.fg_of_fg_map_injective ((W.subtype).restrictScalars (𝓞 E)) ?_ ?_` and prove the remaining obligations. Conclude with `Subtype.val_injective`. Use `Submodule.FG.of_le hΛ.fg ?_` and prove the remaining obligations.

Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `hv`. Conclude with `hw`. Rewrite using `[eq_top_iff]`. Introduce `q _`.

Proceed by induction on `q using Submodule.Quotient.induction_on with | H w => ?_`. Take `⟨s, hs, hsw⟩` from `exists_smul_mem Λ (w : V)`. Establish `hmem : Submodule.Quotient.mk (s • w) ∈ qLat Λ W X` using `mem_qLat.2 ⟨s • w, by simpa using hsw, rfl⟩`. Establish `hsE : algebraMap (𝓞 E) E s ≠ 0` using `by simpa using hs`. Establish `: (Submodule.Quotient.mk w : QW W X) = (algebraMap (𝓞 E) E s)⁻¹ • (Submodule.Quotient.mk (s • w) : QW W X)`.

Rewrite using `[Submodule.Quotient.mk_smul, ← algebraMap_smul E s, smul_smul, inv_mul_cancel₀ hsE, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem qLat_isLattice (Λ : Submodule (𝓞 E) V) [hΛ : Submodule.IsLattice E Λ] (W X : Submodule E V) :
    Submodule.IsLattice E (qLat Λ W X) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.FG.map _ ?_
    refine Submodule.fg_of_fg_map_injective ((W.subtype).restrictScalars (𝓞 E)) ?_ ?_
    · exact Subtype.val_injective
    · refine Submodule.FG.of_le hΛ.fg ?_
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact hw
  · rw [eq_top_iff]
    intro q _
    induction q using Submodule.Quotient.induction_on with | H w => ?_
    obtain ⟨s, hs, hsw⟩ := exists_smul_mem Λ (w : V)
    have hmem : Submodule.Quotient.mk (s • w) ∈ qLat Λ W X := mem_qLat.2 ⟨s • w, by simpa using hsw, rfl⟩
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs
    have : (Submodule.Quotient.mk w : QW W X) =
        (algebraMap (𝓞 E) E s)⁻¹ • (Submodule.Quotient.mk (s • w) : QW W X) := by
      rw [Submodule.Quotient.mk_smul, ← algebraMap_smul E s, smul_smul, inv_mul_cancel₀ hsE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Use `set Q := qEquiv δ W X hW hX with hQ`. Establish `hlat` using `qLat_isLattice Λ W X`. Establish `hiso : Q ∈ Formalism.HermitianLatticesTheory.isom (qForm h W X hR hL)`. Establish `: ∀ a b, qForm h W X hR hL (Q a) (Q b) = qForm h W X hR hL a b`. Introduce `a b`.

Proceed by induction on `a using Submodule.Quotient.induction_on with | H a => ?_`. Proceed by induction on `b using Submodule.Quotient.induction_on with | H b => ?_`. Rewrite using `[hQ, qEquiv_mk, qEquiv_mk, qForm_mk, qForm_mk]`. Conclude with `hδ a b`. Conclude with `this`.

Establish `hpq : ∀ q : QW W X, q ≠ 0 → 0 < Algebra.trace ℚ E (qForm h W X hR hL q q)`. Introduce `q hq`. Proceed by induction on `q using Submodule.Quotient.induction_on with | H w => ?_`. Rewrite using `[qForm_mk]`. Use `hpos w w.2 ?_` and prove the remaining obligations.

Introduce `hwX`. Apply `hq` to reduce the goal to its premises. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hwX`. Establish `haut : Q ∈ Formalism.L2.Col.autLat (qLat Λ W X)`.

Establish `: Formalism.HermitianLatticesTheory.gmap Q (qLat Λ W X) = qLat Λ W X`. Use extensionality with `n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Take `⟨w, hwΛ, rfl⟩` from `mem_qLat.1 hm`.

Use `mem_qLat.2 ⟨⟨δ w, (mem_of_map_eq hW _).2 w.2⟩, (hδΛ w).2 hwΛ, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Introduce `hn`. Take `⟨w, hwΛ, rfl⟩` from `mem_qLat.1 hn`. Establish `h1 : δ (δ.symm w) ∈ W` using `by simpa using w.2`.

Establish `h2 : δ (δ.symm w) ∈ Λ` using `by simpa using hwΛ`. Use `⟨Submodule.Quotient.mk ⟨δ.symm w, (mem_of_map_eq hW _).1 h1⟩, mem_qLat.2 ⟨_, (hδΛ _).1 h2, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show Q _ = _`. Rewrite using `[hQ, qEquiv_mk]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Conclude with `this`. Establish `hunip : ∀ PP : Ideal (𝓞 E), ((g₁ * g₂ : ℕ) : 𝓞 E) ∈ PP → Formalism.L2.Col.UnipMod PP (qLat Λ W X) Q`. Introduce `PP hPP`.

Use `⟨haut, 1, fun q hq => ?_⟩` and prove the remaining obligations. Take `⟨w, hwΛ, rfl⟩` from `mem_qLat.1 hq`. Take `⟨a, haW, haΛ, hXa⟩` from `hstep w w.2 hwΛ`. Establish `key : Q (Submodule.Quotient.mk w) - Submodule.Quotient.mk w = ((g₁ * g₂ : ℕ) : 𝓞 E) • (Submodule.Quotient.mk ⟨a, haW⟩ : QW W X)`. Rewrite using `[hQ, qEquiv_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`.

Simplify using `using hXa`. Rewrite using `[pow_one, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, key]`. Conclude with `Submodule.smul_mem_smul hPP (mem_qLat.2 ⟨⟨a, haW⟩, haΛ, rfl⟩)`. Take `⟨P₁, hP₁, hg₁P⟩` from `Formalism.L2.SG.LemmaN.exists_prime_over E hg₁`. Take `⟨P₂, hP₂, hg₂P⟩` from `Formalism.L2.SG.LemmaN.exists_prime_over E hg₂`.

Establish `hfin : IsOfFinOrder Q` using `Formalism.L2.Col.isOfFinOrder_of_isom (qForm h W X hR hL) (qForm_isSymm h hs W X hR hL) hpq hlat hiso haut`. Establish `hmul : ((g₁ * g₂ : ℕ) : 𝓞 E) = (g₁ : 𝓞 E) * (g₂ : 𝓞 E)` using `by push_cast; ring`. Establish `hone : Q = 1` using `Formalism.L2.SG.LemmaN.lemmaNcGlob_of_exists E (QW W X) (qLat Λ W X) hlat Q hfin hg₁ hg₂ hne hP₁.ne_top hP₂.ne_top hg₁P hg₂P (hunip P₁ (by rw [hmul]; exact Ideal.mul_mem_right _ _ hg₁P)) (hunip P₂ (by rw [hmul]; exact Ideal.mul_mem_left _ _ hg₂P))`. Introduce `w hw`. Establish `h1` using `congrArg (fun f : QW W X ≃ₗ[E] QW W X => f (Submodule.Quotient.mk ⟨w, hw⟩)) hone`.

Simplify using `only [hQ, qEquiv_mk, LinearEquiv.coe_one, id_eq] at h1`. Rewrite `h1` using `[Submodule.Quotient.eq]`. Simplify using `using h1`.
-/
theorem quot_fix (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (W X : Submodule E V)
    (hR : ∀ x ∈ W, ∀ y ∈ X, h x y = 0) (hL : ∀ x ∈ X, ∀ y ∈ W, h x y = 0)
    (hpos : ∀ w ∈ W, w ∉ X → 0 < Algebra.trace ℚ E (h w w))
    (Λ : Submodule (𝓞 E) V) [Submodule.IsLattice E Λ] (δ : V ≃ₗ[E] V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hδΛ : ∀ v, δ v ∈ Λ ↔ v ∈ Λ) (hW : W.map (δ : V →ₗ[E] V) = W) (hX : X.map (δ : V →ₗ[E] V) = X)
    {g₁ g₂ : ℕ} (hg₁ : g₁.Prime) (hg₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    (hstep : ∀ w ∈ W, w ∈ Λ → ∃ a ∈ W, a ∈ Λ ∧ δ w - w - ((g₁ * g₂ : ℕ) : 𝓞 E) • a ∈ X) :
    ∀ w ∈ W, δ w - w ∈ X := by
  set Q := qEquiv δ W X hW hX with hQ
  have hlat := qLat_isLattice Λ W X
  have hiso : Q ∈ Formalism.HermitianLatticesTheory.isom (qForm h W X hR hL) := by
    have : ∀ a b, qForm h W X hR hL (Q a) (Q b) = qForm h W X hR hL a b := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | H a => ?_
      induction b using Submodule.Quotient.induction_on with | H b => ?_
      rw [hQ, qEquiv_mk, qEquiv_mk, qForm_mk, qForm_mk]
      exact hδ a b
    exact this
  have hpq : ∀ q : QW W X, q ≠ 0 → 0 < Algebra.trace ℚ E (qForm h W X hR hL q q) := by
    intro q hq
    induction q using Submodule.Quotient.induction_on with | H w => ?_
    rw [qForm_mk]
    refine hpos w w.2 ?_
    intro hwX
    apply hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hwX
  have haut : Q ∈ Formalism.L2.Col.autLat (qLat Λ W X) := by
    have : Formalism.HermitianLatticesTheory.gmap Q (qLat Λ W X) = qLat Λ W X := by
      ext n
      constructor
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hm
        refine mem_qLat.2 ⟨⟨δ w, (mem_of_map_eq hW _).2 w.2⟩, (hδΛ w).2 hwΛ, ?_⟩
        rfl
      · intro hn
        obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hn
        have h1 : δ (δ.symm w) ∈ W := by simpa using w.2
        have h2 : δ (δ.symm w) ∈ Λ := by simpa using hwΛ
        refine ⟨Submodule.Quotient.mk ⟨δ.symm w, (mem_of_map_eq hW _).1 h1⟩,
          mem_qLat.2 ⟨_, (hδΛ _).1 h2, rfl⟩, ?_⟩
        show Q _ = _
        rw [hQ, qEquiv_mk]
        congr 1
        apply Subtype.ext
        simp
    exact this
  have hunip : ∀ PP : Ideal (𝓞 E), ((g₁ * g₂ : ℕ) : 𝓞 E) ∈ PP →
      Formalism.L2.Col.UnipMod PP (qLat Λ W X) Q := by
    intro PP hPP
    refine ⟨haut, 1, fun q hq => ?_⟩
    obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hq
    obtain ⟨a, haW, haΛ, hXa⟩ := hstep w w.2 hwΛ
    have key : Q (Submodule.Quotient.mk w) - Submodule.Quotient.mk w =
        ((g₁ * g₂ : ℕ) : 𝓞 E) • (Submodule.Quotient.mk ⟨a, haW⟩ : QW W X) := by
      rw [hQ, qEquiv_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      simpa using hXa
    rw [pow_one, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, key]
    exact Submodule.smul_mem_smul hPP (mem_qLat.2 ⟨⟨a, haW⟩, haΛ, rfl⟩)
  obtain ⟨P₁, hP₁, hg₁P⟩ := Formalism.L2.SG.LemmaN.exists_prime_over E hg₁
  obtain ⟨P₂, hP₂, hg₂P⟩ := Formalism.L2.SG.LemmaN.exists_prime_over E hg₂
  have hfin : IsOfFinOrder Q :=
    Formalism.L2.Col.isOfFinOrder_of_isom (qForm h W X hR hL) (qForm_isSymm h hs W X hR hL) hpq hlat hiso haut
  have hmul : ((g₁ * g₂ : ℕ) : 𝓞 E) = (g₁ : 𝓞 E) * (g₂ : 𝓞 E) := by push_cast; ring
  have hone : Q = 1 := Formalism.L2.SG.LemmaN.lemmaNcGlob_of_exists E (QW W X) (qLat Λ W X) hlat Q hfin hg₁ hg₂
    hne hP₁.ne_top hP₂.ne_top hg₁P hg₂P (hunip P₁ (by rw [hmul]; exact Ideal.mul_mem_right _ _ hg₁P))
    (hunip P₂ (by rw [hmul]; exact Ideal.mul_mem_left _ _ hg₂P))
  intro w hw
  have h1 := congrArg (fun f : QW W X ≃ₗ[E] QW W X => f (Submodule.Quotient.mk ⟨w, hw⟩)) hone
  simp only [hQ, qEquiv_mk, LinearEquiv.coe_one, id_eq] at h1
  rw [Submodule.Quotient.eq] at h1
  simpa using h1

end Quot

section Helpers

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth_iff_bl {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[mem_orth_iff_bl]`. Conclude with `fun x hx => hv x (h hx)`.
-/
theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro v hv
  rw [mem_orth_iff_bl] at hv ⊢
  exact fun x hx => hv x (h hx)

/- English proof (translation)
Introduce `x hx`. Establish `hle : Submodule.span E s ≤ LinearMap.ker (S.hT v)`. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker]`.

Conclude with `S.herm.eq_iff.1 (hs y hy)`. Conclude with `S.herm.eq_iff.1 (hle hx)`.
-/
theorem form_span_left {s : Set S.V} {v : S.V} (hs : ∀ x ∈ s, S.hT x v = 0) :
    ∀ x ∈ Submodule.span E s, S.hT x v = 0 := by
  intro x hx
  have hle : Submodule.span E s ≤ LinearMap.ker (S.hT v) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact S.herm.eq_iff.1 (hs y hy)
  exact S.herm.eq_iff.1 (hle hx)

/- English proof (translation)
Establish `hX : ∀ b ∈ F.X, ∀ i, S.hT (F.e i) b = 0` using `fun b hb i => by`. Establish `hle : F.X ≤ LinearMap.ker (S.hT (F.e i))` using `Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact F.e_iso i j)`. Conclude with `hle hb`. Establish `hzX : ∀ b ∈ F.X, S.hT F.z b = 0` using `fun b hb => by`. Establish `hle : F.X ≤ LinearMap.ker (S.hT F.z)` using `Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact S.herm.eq_iff.1 (F.z_orth j))`.

Conclude with `hle hb`. Introduce `x hx v hv`. Take `⟨x1, hx1, x2, hx2, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hx2`. Establish `h1 : S.hT x1 v = 0` using `form_span_left (s := Set.range F.e) (by rintro _ ⟨i, rfl⟩; exact hX v hv i) x1 hx1`.

Rewrite using `[map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, hzX v hv]`. Simplify using the standard rewrite rules.
-/
theorem flag_form_zero {T : E} (F : FlagG S r T) : ∀ x ∈ F.Xplus, ∀ v ∈ F.X, S.hT x v = 0 := by
  have hX : ∀ b ∈ F.X, ∀ i, S.hT (F.e i) b = 0 := fun b hb i => by
    have hle : F.X ≤ LinearMap.ker (S.hT (F.e i)) :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact F.e_iso i j)
    exact hle hb
  have hzX : ∀ b ∈ F.X, S.hT F.z b = 0 := fun b hb => by
    have hle : F.X ≤ LinearMap.ker (S.hT F.z) :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact S.herm.eq_iff.1 (F.z_orth j))
    exact hle hb
  intro x hx v hv
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx2
  have h1 : S.hT x1 v = 0 :=
    form_span_left (s := Set.range F.e) (by rintro _ ⟨i, rfl⟩; exact hX v hv i) x1 hx1
  rw [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, hzX v hv]
  simp

/- English proof (translation)
Introduce `v hv`. Rewrite using `[mem_orth_iff_bl]`. Conclude with `fun x hx => flag_form_zero F x hx v hv`.
-/
theorem flag_X_le {T : E} (F : FlagG S r T) : F.X ≤ orth S F.Xplus := by
  intro v hv
  rw [mem_orth_iff_bl]
  exact fun x hx => flag_form_zero F x hx v hv

/- English proof (translation)
The claim follows from `form_span_left (s := Set.range F.e) (by rintro _ ⟨i, rfl⟩; exact F.z_orth i)`.
-/
theorem flag_z_orth {T : E} (F : FlagG S r T) : ∀ x ∈ F.X, S.hT x F.z = 0 :=
  form_span_left (s := Set.range F.e) (by rintro _ ⟨i, rfl⟩; exact F.z_orth i)

/- English proof (translation)
Simplify using `only [FlagG.Xa, FlagG.X]`. Use `congr 1`. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem Xa_self {T : E} (F : FlagG S r T) : F.Xa r = F.X := by
  simp only [FlagG.Xa, FlagG.X]
  congr 1
  ext v
  simp

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[Submodule.mem_map_equiv, mem_orth_iff_bl, mem_orth_iff_bl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h _ ⟨u, hu, rfl⟩`. Use `h u hu` as an intermediate fact.

Rewrite `this` using `[← hγ u (γ.symm w)]`. Simplify using `using this`. Introduce `h u hu`. Use `h (γ u) (Submodule.mem_map_of_mem hu)` as an intermediate fact. Rewrite using `[← hγ u (γ.symm w)]`.

Simplify using `using this`.
-/
theorem orth_map_bl {γ : S.V ≃ₗ[E] S.V} (hγ : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) (U : Submodule E S.V) :
    (orth S U).map (γ : S.V →ₗ[E] S.V) = orth S (U.map (γ : S.V →ₗ[E] S.V)) := by
  ext w
  rw [Submodule.mem_map_equiv, mem_orth_iff_bl, mem_orth_iff_bl]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    have := h u hu
    rw [← hγ u (γ.symm w)] at this
    simpa using this
  · intro h u hu
    have := h (γ u) (Submodule.mem_map_of_mem hu)
    rw [← hγ u (γ.symm w)]
    simpa using this

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[Submodule.mem_map_equiv]`. Rewrite using `[← h (γ.symm w)]`. Simplify using the standard rewrite rules.
-/
theorem map_eq_of_iff {γ : S.V ≃ₗ[E] S.V} {U : Submodule E S.V} (h : ∀ w, γ w ∈ U ↔ w ∈ U) :
    U.map (γ : S.V →ₗ[E] S.V) = U := by
  ext w
  rw [Submodule.mem_map_equiv]
  rw [← h (γ.symm w)]
  simp

/- English proof (translation)
Use `show ∃ s ∈ P.primeCompl, s • x ∈ M`. Conclude with `⟨1, P.primeCompl.one_mem, by simpa using hx⟩`.
-/
theorem mem_localization_of_mem' {P : Ideal (𝓞 E)} [P.IsPrime] {M : Submodule (𝓞 E) S.V} {x : S.V} (hx : x ∈ M) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P M := by
  show ∃ s ∈ P.primeCompl, s • x ∈ M
  exact ⟨1, P.primeCompl.one_mem, by simpa using hx⟩

/- English proof (translation)
Take `⟨s, hs, h⟩` from `hx`. Conclude with `⟨s, hs, hMN h⟩`.
-/
theorem localization_mono {P : Ideal (𝓞 E)} [P.IsPrime] {M N : Submodule (𝓞 E) S.V} (hMN : M ≤ N) {x : S.V}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P M) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P N := by
  obtain ⟨s, hs, h⟩ := hx
  exact ⟨s, hs, hMN h⟩

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Set `I : Ideal (𝓞 E)` to `M.comap (LinearMap.toSpanSingleton (𝓞 E) S.V x)`. Establish `hI : I ≠ ⊤`. Introduce `htop`. Apply `hx` to reduce the goal to its premises.

Establish `h1 : (1 : 𝓞 E) ∈ I` using `htop ▸ Submodule.mem_top`. Simplify `h1` using `[I]`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hI`. Establish `hne : m ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)`. Take `⟨s, hs, hsx⟩` from `h ⟨m, hm.isPrime, hne⟩`.

Conclude with `hs (hIm (by simpa [I] using hsx))`.
-/
theorem mem_of_forall_locP {M : Submodule (𝓞 E) S.V} {x : S.V}
    (h : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) S.V x)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hx
    have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa [I] using h1
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hne : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hne⟩
  exact hs (hIm (by simpa [I] using hsx))

/- English proof (translation)
The claim follows from `algebraMap_smul E c v`.
-/
theorem coe_smul_eq (c : 𝓞 E) (v : S.V) : ((c : E)) • v = c • v := algebraMap_smul E c v

/- English proof (translation)
Introduce `x hx`. Use `mem_of_forall_locP (fun P => ?_)` and prove the remaining obligations. Use `haveI := P.isPrime`. Distinguish the cases in `hgP : (g : 𝓞 E) ∈ P.asIdeal`. Take `⟨ξ, hlow, hdiag, hmod⟩` from `hadm`.

Take `⟨c, -, hc1, hloc⟩` from `hF.1 P`. Take `⟨c', -, hc1', hloc'⟩` from `hF'.1 P`. Establish `hc : c = fun _ => 1` using `funext (hc1 hgP)`. Establish `hc' : c' = fun _ => 1` using `funext (hc1' hgP)`. Substitute `hc hc'` using the available equality.

Simplify using `only [one_smul] at hloc hloc'`. Establish `he' : ∀ b, F'.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')`. Introduce `b`. Establish `h1 : F'.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F')`. Rewrite using `[hloc']`.

Conclude with `mem_localization_of_mem' (Submodule.subset_span ⟨b, rfl⟩)`. Conclude with `localization_mono le_sup_right h1`. Establish `hmod' : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')` using `fun b => localization_mono le_sup_left (hmod b P hgP)`. Establish `hfr : ∀ a : Fin r, frame F (Fin.castSucc a) = F.fl.e a` using `fun a => by`. Simplify using `[frame, FlagG.fvec]`.

Establish `hfr' : ∀ a : Fin r, frame F' (Fin.castSucc a) = F'.fl.e a` using `fun a => by`. Simplify using `[frame, FlagG.fvec]`. Establish `he : ∀ n : ℕ, ∀ a : Fin r, a.val < n → F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro a ha`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `a ha`. Establish `hsum : frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')`.

Establish `heq : frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a) = ∑ i, (((ξ i (Fin.castSucc a) : 𝓞 E) : E) - if i = Fin.castSucc a then 1 else 0) • frame F i`. Simplify using `[frameAct, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[heq]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Break down `lt_trichotomy i (Fin.castSucc a) with hi | hi | hi` into its components or cases.

Rewrite using `[if_neg hi.ne, sub_zero]`. Establish `hir : i.val < r` using `lt_trans hi a.castSucc_lt_last`. Establish `hi' : Fin.castSucc (⟨i.val, hir⟩ : Fin r) = i` using `Fin.ext rfl`. Rewrite using `[← hi', hfr, coe_smul_eq]`. Use `Submodule.smul_mem _ _ (ih _ ?_)` and prove the remaining obligations.

Establish `: i.val < a.val` using `hi`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Substitute `hi` using the available equality. Rewrite using `[if_pos rfl, hdiag]`.

Simplify using the standard rewrite rules. Rewrite using `[hlow _ _ hi, if_neg hi.ne']`. Simplify using the standard rewrite rules. Establish `hb` using `hmod' (Fin.castSucc a)`. Establish `hrw : F.fl.e a = F'.fl.e a - (frame F' (Fin.castSucc a) - frameAct (frame F) ξ (Fin.castSucc a)) - (frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a))`.

Rewrite using `[hfr, hfr']`. Normalize the expressions using the abelian group laws. Rewrite using `[hrw]`. Conclude with `sub_mem (sub_mem (he' a) hb) hsum`. Establish `hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range F.fl.e))`.

Rewrite using `[← hloc]`. Conclude with `mem_localization_of_mem' hx`. Take `⟨s, hs, hsx⟩` from `hx'`. Establish `hspan : Submodule.span (𝓞 E) (Set.range F.fl.e) ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')` using `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact he (a.val + 1) a (by omega))`. Take `⟨t, ht, htx⟩` from `hspan hsx`.

Use `⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `htx`. Use `⟨(g : 𝓞 E), hgP, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx.1)`.
-/
theorem xlam_le (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')
    (hF : IsFixedConv Λ g F) (hF' : IsFixedConv Λ g F') (hadm : IsAdmissible Λ g F F') :
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  intro x hx
  refine mem_of_forall_locP (fun P => ?_)
  haveI := P.isPrime
  by_cases hgP : (g : 𝓞 E) ∈ P.asIdeal
  · obtain ⟨ξ, hlow, hdiag, hmod⟩ := hadm
    obtain ⟨c, -, hc1, hloc⟩ := hF.1 P
    obtain ⟨c', -, hc1', hloc'⟩ := hF'.1 P
    have hc : c = fun _ => 1 := funext (hc1 hgP)
    have hc' : c' = fun _ => 1 := funext (hc1' hgP)
    subst hc hc'
    simp only [one_smul] at hloc hloc'
    have he' : ∀ b, F'.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
      intro b
      have h1 : F'.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
        rw [hloc']
        exact mem_localization_of_mem' (Submodule.subset_span ⟨b, rfl⟩)
      exact localization_mono le_sup_right h1
    have hmod' : ∀ b, frame F' b - frameAct (frame F) ξ b ∈
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := fun b =>
      localization_mono le_sup_left (hmod b P hgP)
    have hfr : ∀ a : Fin r, frame F (Fin.castSucc a) = F.fl.e a := fun a => by
      simp [frame, FlagG.fvec]
    have hfr' : ∀ a : Fin r, frame F' (Fin.castSucc a) = F'.fl.e a := fun a => by
      simp [frame, FlagG.fvec]
    have he : ∀ n : ℕ, ∀ a : Fin r, a.val < n →
        F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
      intro n
      induction n with
      | zero => intro a ha; omega
      | succ n ih =>
        intro a ha
        have hsum : frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a) ∈
            Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
          have heq : frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a) =
              ∑ i, (((ξ i (Fin.castSucc a) : 𝓞 E) : E) - if i = Fin.castSucc a then 1 else 0) • frame F i := by
            simp [frameAct, sub_smul, Finset.sum_sub_distrib]
          rw [heq]
          refine Submodule.sum_mem _ (fun i _ => ?_)
          rcases lt_trichotomy i (Fin.castSucc a) with hi | hi | hi
          · rw [if_neg hi.ne, sub_zero]
            have hir : i.val < r := lt_trans hi a.castSucc_lt_last
            have hi' : Fin.castSucc (⟨i.val, hir⟩ : Fin r) = i := Fin.ext rfl
            rw [← hi', hfr, coe_smul_eq]
            refine Submodule.smul_mem _ _ (ih _ ?_)
            have : i.val < a.val := hi
            simp only
            omega
          · subst hi
            rw [if_pos rfl, hdiag]
            simp
          · rw [hlow _ _ hi, if_neg hi.ne']
            simp
        have hb := hmod' (Fin.castSucc a)
        have hrw : F.fl.e a = F'.fl.e a - (frame F' (Fin.castSucc a) - frameAct (frame F) ξ (Fin.castSucc a)) -
            (frameAct (frame F) ξ (Fin.castSucc a) - frame F (Fin.castSucc a)) := by
          rw [hfr, hfr']
          abel
        rw [hrw]
        exact sub_mem (sub_mem (he' a) hb) hsum
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range F.fl.e)) := by
      rw [← hloc]
      exact mem_localization_of_mem' hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hspan : Submodule.span (𝓞 E) (Set.range F.fl.e) ≤
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact he (a.val + 1) a (by omega))
    obtain ⟨t, ht, htx⟩ := hspan hsx
    refine ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
    rw [mul_smul]
    exact htx
  · refine ⟨(g : 𝓞 E), hgP, ?_⟩
    exact Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx.1)

end Helpers

section Sig

open Matrix

def cform {n : Type} [Fintype n] (G : Matrix n n ℂ) (x y : n → ℂ) : ℂ := star x ⬝ᵥ (G *ᵥ y)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.
-/
theorem cT_eq_conjTranspose {m n : Type} (P : Matrix m n ℂ) : Formalism.UG.cT (starRingEnd ℂ) P = Pᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hG`. Rewrite `hP` using `[cT_eq_conjTranspose]`. Set `Pm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)`. Set `Pinv : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)`. Establish `hPP : Pm * Pinv = 1`.

Simplify using `only [Pm, Pinv]`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hPP' : Pinv * Pm = 1`. Simplify using `only [Pm, Pinv]`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Set `pr : (Fin N → ℂ) →ₗ[ℂ] (Fin p ⊕ Fin q → ℂ)` to `(Matrix.mulVecLin Pinv).comp (LinearMap.funLeft ℂ ℂ e.symm)`. Establish `hpr : ∀ x, pr x = Pinv *ᵥ (x ∘ e.symm)` using `fun x => rfl`. Establish `hback : ∀ x, x ∘ e.symm = Pm *ᵥ pr x` using `fun x => by`. Rewrite using `[hpr, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]`. Establish `hpr_inj : Function.Injective pr`.

Introduce `x y hxy`. Establish `h1 : x ∘ e.symm = y ∘ e.symm` using `by rw [hback, hback, hxy]`. Use function extensionality and compare the values at `i`. Use `congrFun h1 (e i)` as an intermediate fact. Simplify using `using this`.

Establish `hkey : ∀ x, cform G x x = star (pr x) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ pr x)`. Introduce `x`. Establish `h1 : cform G x x = star (x ∘ e.symm) ⬝ᵥ ((G.reindex e e) *ᵥ (x ∘ e.symm))`. Simplify using `only [cform, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]`. Rewrite using `[show (x ∘ e.symm) ∘ e.symm.symm = x by funext i; simp]`.

Rewrite using `[show star (x ∘ e.symm) = star x ∘ e.symm from rfl, dotProduct_comp_equiv_symm]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[h1, hback, ← hP, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.

Establish `hJ : ∀ y : Fin p ⊕ Fin q → ℂ, star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) = ∑ a, star (y (Sum.inl a)) * y (Sum.inl a) - ∑ b, star (y (Sum.inr b)) * y (Sum.inr b)`. Introduce `y`. Simplify using `only [Formalism.UG.Jpq, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply, Pi.star_apply]`. Simplify using `[Finset.sum_ite_eq, sub_eq_add_neg, Finset.sum_neg_distrib]`. Set `w : ι → Fin q → ℂ` to `fun l b => pr (c l) (Sum.inr b)`.

Establish `hw : LinearIndependent ℂ w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `d hd`. Use `set x := ∑ l, d l • c l with hx`. Establish `hprx : ∀ s, pr x s = ∑ l, d l * pr (c l) s`.

Introduce `s`. Rewrite using `[hx, map_sum]`. Simplify using the standard rewrite rules. Establish `hinr : ∀ b, pr x (Sum.inr b) = 0`. Introduce `b`.

Rewrite using `[hprx]`. Use `congrFun hd b` as an intermediate fact. Simplify `this` using `[w]`. Establish `hre` using `hneg d`. Rewrite `hre` using `[← hx, hkey, hJ]`.

Simplify using `only [hinr, star_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hre`. Establish `hsq : ∀ a, star (pr x (Sum.inl a)) * pr x (Sum.inl a) = ((Complex.normSq (pr x (Sum.inl a)) : ℝ) : ℂ)`. Introduce `a`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.

Simplify using `only [hsq] at hre`. Rewrite `hre` using `[← Complex.ofReal_sum, Complex.ofReal_re]`. Establish `hnn : ∀ a ∈ Finset.univ, 0 ≤ Complex.normSq (pr x (Sum.inl a))` using `fun a _ => Complex.normSq_nonneg _`. Establish `hzero` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hre (Finset.sum_nonneg hnn))`. Establish `hinl : ∀ a, pr x (Sum.inl a) = 0` using `fun a => Complex.normSq_eq_zero.1 (hzero a (Finset.mem_univ _))`.

Establish `hx0 : pr x = 0`. Use function extensionality and compare the values at `s`. Consider the cases of `s with`. Consider the case `inl a => exact hinl a`. Consider the case `inr b => exact hinr b`.

Establish `hx00 : x = 0` using `hpr_inj (by rw [hx0, map_zero])`. Conclude with `(Fintype.linearIndependent_iff.1 hc) d hx00`. Use `hw.fintype_card_le_finrank` as an intermediate fact. Simplify using `using this`.
-/
theorem sig_bound {N p q : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : Formalism.UG.HasSignature G p q)
    {ι : Type} [Fintype ι] (c : ι → Fin N → ℂ) (hc : LinearIndependent ℂ c)
    (hneg : ∀ d : ι → ℂ, (cform G (∑ l, d l • c l) (∑ l, d l • c l)).re ≤ 0) : Fintype.card ι ≤ q := by
  obtain ⟨e, P, hP⟩ := hG
  rw [cT_eq_conjTranspose] at hP
  let Pm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
  let Pinv : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)
  have hPP : Pm * Pinv = 1 := by
    simp only [Pm, Pinv]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : Pinv * Pm = 1 := by
    simp only [Pm, Pinv]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let pr : (Fin N → ℂ) →ₗ[ℂ] (Fin p ⊕ Fin q → ℂ) :=
    (Matrix.mulVecLin Pinv).comp (LinearMap.funLeft ℂ ℂ e.symm)
  have hpr : ∀ x, pr x = Pinv *ᵥ (x ∘ e.symm) := fun x => rfl
  have hback : ∀ x, x ∘ e.symm = Pm *ᵥ pr x := fun x => by
    rw [hpr, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have hpr_inj : Function.Injective pr := by
    intro x y hxy
    have h1 : x ∘ e.symm = y ∘ e.symm := by rw [hback, hback, hxy]
    funext i
    have := congrFun h1 (e i)
    simpa using this
  have hkey : ∀ x, cform G x x = star (pr x) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ pr x) := by
    intro x
    have h1 : cform G x x = star (x ∘ e.symm) ⬝ᵥ ((G.reindex e e) *ᵥ (x ∘ e.symm)) := by
      simp only [cform, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      rw [show (x ∘ e.symm) ∘ e.symm.symm = x by funext i; simp]
      rw [show star (x ∘ e.symm) = star x ∘ e.symm from rfl, dotProduct_comp_equiv_symm]
      congr 1
      funext i
      simp
    rw [h1, hback, ← hP, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hJ : ∀ y : Fin p ⊕ Fin q → ℂ, star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) =
      ∑ a, star (y (Sum.inl a)) * y (Sum.inl a) - ∑ b, star (y (Sum.inr b)) * y (Sum.inr b) := by
    intro y
    simp only [Formalism.UG.Jpq, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
      Matrix.zero_apply, Matrix.neg_apply, Pi.star_apply]
    simp [Finset.sum_ite_eq, sub_eq_add_neg, Finset.sum_neg_distrib]
  let w : ι → Fin q → ℂ := fun l b => pr (c l) (Sum.inr b)
  have hw : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    set x := ∑ l, d l • c l with hx
    have hprx : ∀ s, pr x s = ∑ l, d l * pr (c l) s := by
      intro s
      rw [hx, map_sum]
      simp
    have hinr : ∀ b, pr x (Sum.inr b) = 0 := by
      intro b
      rw [hprx]
      have := congrFun hd b
      simpa [w] using this
    have hre := hneg d
    rw [← hx, hkey, hJ] at hre
    simp only [hinr, star_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hre
    have hsq : ∀ a, star (pr x (Sum.inl a)) * pr x (Sum.inl a) = ((Complex.normSq (pr x (Sum.inl a)) : ℝ) : ℂ) := by
      intro a
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    simp only [hsq] at hre
    rw [← Complex.ofReal_sum, Complex.ofReal_re] at hre
    have hnn : ∀ a ∈ Finset.univ, 0 ≤ Complex.normSq (pr x (Sum.inl a)) := fun a _ => Complex.normSq_nonneg _
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hre (Finset.sum_nonneg hnn))
    have hinl : ∀ a, pr x (Sum.inl a) = 0 := fun a => Complex.normSq_eq_zero.1 (hzero a (Finset.mem_univ _))
    have hx0 : pr x = 0 := by
      funext s
      cases s with
      | inl a => exact hinl a
      | inr b => exact hinr b
    have hx00 : x = 0 := hpr_inj (by rw [hx0, map_zero])
    exact (Fintype.linearIndependent_iff.1 hc) d hx00
  have := hw.fintype_card_le_finrank
  simpa using this

end Sig

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Corank

def IotaLift (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x : Carrier (PD D Λ (lf D F0) u'), ∀ x' ∈ Lrep Λ x.1,
      ∃ l ∈ Lrep Λ (lf D F0), l - x' ∈ NgX Λ (gS D) (lf D F0) x.1

def PosW (D : D7) : Prop :=
  ∀ T' : ℕ, 0 < T' → ∀ F' : FlagG (VS D) D.R.rS (T' : D.host.E), ∀ v ∈ orth (VS D) F'.Xplus, v ∉ F'.X →
    0 < Algebra.trace ℚ D.host.E ((VS D).hT v v)

/- English proof (translation)
Introduce `_ F0 Λ hΛ x y _ _ β₁ β₂ hp₁ hp₂ v hv`. Use `haveI : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1`. Take `⟨⟨hiso₁, hΛ₁⟩, hfl₁, hz₁, hι₁⟩` from `hp₁`. Take `⟨⟨hiso₂, hΛ₂⟩, hfl₂, hz₂, hι₂⟩` from `hp₂`. Establish `i₁ : ∀ a b, (VS D).hT (β₁ a) (β₁ b) = (VS D).hT a b` using `hiso₁`.

Establish `i₂ : ∀ a b, (VS D).hT (β₂ a) (β₂ b) = (VS D).hT a b` using `hiso₂`. Use `set δ : (VS D).V ≃ₗ[D.host.E] (VS D).V := β₁.trans β₂.symm with hδdef`. Establish `hβδ : ∀ w, β₂ (δ w) = β₁ w` using `fun w => by simp [hδdef]`. Establish `iδ : ∀ a b, (VS D).hT (δ a) (δ b) = (VS D).hT a b` using `fun a b => by`. Rewrite using `[← i₂ (δ a) (δ b), hβδ, hβδ, i₁]`.

Establish `hΛmem : ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → ∀ w, β w ∈ Λ ↔ w ∈ Λ`. Introduce `β hβ w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Rewrite `hw` using `[← hβ]`.

Take `⟨y', hy', hyw⟩` from `hw`. Establish `: y' = w` using `β.injective hyw`. Conclude with `this ▸ hy'`. Introduce `hw`. Rewrite using `[← hβ]`.

Conclude with `Submodule.mem_map_of_mem hw`. Establish `hδΛ : ∀ w, δ w ∈ Λ ↔ w ∈ Λ` using `fun w => by`. Rewrite using `[← hΛmem β₂ hΛ₂, hβδ, hΛmem β₁ hΛ₁]`. Use `set X' : Submodule D.host.E (VS D).V := x.1.fl.X with hX'def`. Use `set Xp : Submodule D.host.E (VS D).V := x.1.fl.Xplus with hXpdef`.

Use `set W0 : Submodule D.host.E (VS D).V := orth (VS D) Xp with hW0def`. Establish `hX₁ : X'.map (β₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = y.1.fl.X`. Use `hfl₁ D.R.rS` as an intermediate fact. Simplify `this` using `[Xflag, Xa_self]`. Establish `hX₂ : X'.map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = y.1.fl.X`.

Use `hfl₂ D.R.rS` as an intermediate fact. Simplify `this` using `[Xflag, Xa_self]`. Establish `hδX' : ∀ w, δ w ∈ X' ↔ w ∈ X'` using `fun w => by`. Rewrite using `[← mem_of_map_eq hX₂, hβδ, mem_of_map_eq hX₁]`. Establish `hδXm : X'.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = X'` using `map_eq_of_iff hδX'`.

Establish `hδz : δ x.1.fl.z = x.1.fl.z`. Apply `β₂.injective` to reduce the goal to its premises. Rewrite using `[hβδ, hz₁, hz₂]`. Establish `hδXp : Xp.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xp`. Rewrite using `[hXpdef, FlagG.Xplus, Submodule.map_sup, Submodule.map_span, Set.image_singleton]`.

Simplify using `only [LinearEquiv.coe_coe, hδz]`. Rewrite using `[← hX'def, hδXm]`. Establish `hδW : W0.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = W0`. Rewrite using `[hW0def, orth_map_bl iδ, hδXp]`. Establish `hXW : X' ≤ W0` using `flag_X_le x.1.fl`.

Establish `hXXp : X' ≤ Xp` using `le_sup_left`. Establish `hW0L : W0 ≤ orth (VS D) X'` using `orth_anti hXXp`. Establish `hR : ∀ a ∈ W0, ∀ b ∈ X', (VS D).hT a b = 0` using `fun a ha b hb => (VS D).herm.eq_iff.1 ((mem_orth_iff_bl.1 ha) b (hXXp hb))`. Establish `hL : ∀ a ∈ X', ∀ b ∈ W0, (VS D).hT a b = 0` using `fun a ha b hb => (mem_orth_iff_bl.1 hb) a (hXXp ha)`. Establish `hTpos : 0 < Tu D u'` using `(D.mem u').A.T_prime.pos`.

Establish `hpos : ∀ w ∈ W0, w ∉ X' → 0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)` using `fun w hw hwX => hP (Tu D u') hTpos x.1.fl w hw hwX`. Establish `hadm : XLam Λ (lf D F0) ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1` using `xlam_le Λ (gS D) (lf D F0) x.1 hΛ.2.1.2.2.2 x.2.2.2.1 x.2.2.1`. Establish `hstep : ∀ w ∈ W0, w ∈ Λ → ∃ a ∈ W0, a ∈ Λ ∧ δ w - w - ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) • a ∈ X'`. Introduce `w hwW hwΛ`. Establish `hwL : w ∈ Lrep Λ x.1` using `⟨hwΛ, hW0L hwW⟩`.

Take `⟨l, hl, hlw⟩` from `hI F0 Λ hΛ x w hwL`. Establish `h1 : l - β₁ w ∈ NgX Λ (gS D) (lf D F0) y.1` using `(hι₁ w hwL l hl).1 hlw`. Establish `hδwW : δ w ∈ W0` using `(mem_of_map_eq hδW w).2 hwW`. Establish `hδwL : δ w ∈ Lrep Λ x.1` using `⟨(hδΛ w).2 hwΛ, hW0L hδwW⟩`. Establish `h2 : l - δ w ∈ NgX Λ (gS D) (lf D F0) x.1` using `(hι₂ (δ w) hδwL l hl).2 (by rw [hβδ]; exact h1)`.

Establish `h3 : δ w - w ∈ NgX Λ (gS D) (lf D F0) x.1`. Use `sub_mem hlw h2` as an intermediate fact. Rewrite `this` using `[show l - w - (l - δ w) = δ w - w by abel]`. Then use the resulting hypothesis. Establish `h4 : NgX Λ (gS D) (lf D F0) x.1 ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1` using `sup_le (sup_le le_sup_left hadm) le_sup_right`. Take `⟨p, hp, c, hc, hpc⟩` from `Submodule.mem_sup.1 (h4 h3)`.

Rewrite `hp` using `[Submodule.ideal_span_singleton_smul]`. Take `⟨a, haΛ, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hp`. Establish `hcX : c ∈ X'` using `hc.2`. Establish `hga : ((gS D : ℕ) : 𝓞 D.host.E) • a ∈ W0`. Establish `: ((gS D : ℕ) : 𝓞 D.host.E) • a = δ w - w - c` using `by rw [← hpc]; abel`.

Rewrite using `[this]`. Conclude with `sub_mem (sub_mem hδwW hwW) (hXW hcX)`. Establish `hg0 : ((gS D : ℕ) : D.host.E) ≠ 0`. Establish `h0` using `(D.host.g_prime 0).ne_zero`. Establish `h1'` using `(D.host.g_prime 1).ne_zero`.

Simplify using `only [gS]`. Conclude with `Nat.mul_ne_zero h0 h1'` after adjusting the coercions. Establish `haW : a ∈ W0`. Establish `: a = ((gS D : ℕ) : D.host.E)⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • a)`. Rewrite using `[← coe_smul_eq (S := VS D), smul_smul]`.

Use `push_cast`. Rewrite using `[inv_mul_cancel₀ hg0, one_smul]`. Rewrite using `[this]`. Conclude with `W0.smul_mem _ hga`. Use `⟨a, haW, haΛ, ?_⟩` and prove the remaining obligations.

Establish `: δ w - w - ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) • a = c`. Rewrite using `[← hpc]`. Simplify using `only [gS]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `hcX`. Establish `hfix` using `quot_fix (VS D).hT (VS D).herm W0 X' hR hL hpos Λ δ iδ hδΛ hδW hδXm (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hstep`. Establish `hzz : (VS D).hT x.1.fl.z x.1.fl.z ≠ 0`. Rewrite using `[x.1.fl.z_norm]`. Conclude with `neg_ne_zero.2 (tu_ne_zero u')`.

Use `set c : D.host.E := (VS D).hT x.1.fl.z v / (VS D).hT x.1.fl.z x.1.fl.z with hc`. Establish `hv0 : v - c • x.1.fl.z ∈ W0`. Rewrite using `[hW0def, mem_orth_iff_bl]`. Introduce `q hq`. Take `⟨q1, hq1, q2, hq2, rfl⟩` from `Submodule.mem_sup.1 hq`.

Take `⟨d, rfl⟩` from `Submodule.mem_span_singleton.1 hq2`. Establish `hv'` using `mem_orth_iff_bl.1 hv`. Establish `e1 : (VS D).hT q1 (v - c • x.1.fl.z) = 0`. Rewrite using `[map_sub, map_smul, hv' q1 hq1, flag_z_orth x.1.fl q1 hq1]`. Simplify using the standard rewrite rules.

Establish `e2 : (VS D).hT x.1.fl.z (v - c • x.1.fl.z) = 0`. Rewrite using `[map_sub, map_smul, hc, smul_eq_mul, div_mul_cancel₀ _ hzz, sub_self]`. Rewrite using `[map_add, LinearMap.add_apply, e1, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e2]`. Simplify using the standard rewrite rules. Establish `hδv : δ v - v ∈ X'`.

Establish `h0` using `hfix _ hv0`. Establish `: δ (v - c • x.1.fl.z) - (v - c • x.1.fl.z) = δ v - v`. Rewrite using `[map_sub, map_smul, hδz]`. Normalize the expressions using the abelian group laws. Rewrite `h0` using `[this]`. Then use the resulting hypothesis.

Establish `hfin : β₂ (δ v - v) ∈ y.1.fl.X` using `(mem_of_map_eq hX₂ _).2 hδv`. Rewrite `hfin` using `[map_sub, hβδ]`. Conclude with `hfin`.
-/
theorem betaL_of (D : D7) (u u' : D.what₂.Word) (hI : IotaLift D u u') (hP : PosW D) : BetaL D u u' := by
  intro _ F0 Λ hΛ x y _ _ β₁ β₂ hp₁ hp₂ v hv
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  obtain ⟨⟨hiso₁, hΛ₁⟩, hfl₁, hz₁, hι₁⟩ := hp₁
  obtain ⟨⟨hiso₂, hΛ₂⟩, hfl₂, hz₂, hι₂⟩ := hp₂
  have i₁ : ∀ a b, (VS D).hT (β₁ a) (β₁ b) = (VS D).hT a b := hiso₁
  have i₂ : ∀ a b, (VS D).hT (β₂ a) (β₂ b) = (VS D).hT a b := hiso₂
  set δ : (VS D).V ≃ₗ[D.host.E] (VS D).V := β₁.trans β₂.symm with hδdef
  have hβδ : ∀ w, β₂ (δ w) = β₁ w := fun w => by simp [hδdef]
  have iδ : ∀ a b, (VS D).hT (δ a) (δ b) = (VS D).hT a b := fun a b => by
    rw [← i₂ (δ a) (δ b), hβδ, hβδ, i₁]

  have hΛmem : ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → ∀ w, β w ∈ Λ ↔ w ∈ Λ := by
    intro β hβ w
    constructor
    · intro hw
      rw [← hβ] at hw
      obtain ⟨y', hy', hyw⟩ := hw
      have : y' = w := β.injective hyw
      exact this ▸ hy'
    · intro hw
      rw [← hβ]
      exact Submodule.mem_map_of_mem hw
  have hδΛ : ∀ w, δ w ∈ Λ ↔ w ∈ Λ := fun w => by
    rw [← hΛmem β₂ hΛ₂, hβδ, hΛmem β₁ hΛ₁]

  set X' : Submodule D.host.E (VS D).V := x.1.fl.X with hX'def
  set Xp : Submodule D.host.E (VS D).V := x.1.fl.Xplus with hXpdef
  set W0 : Submodule D.host.E (VS D).V := orth (VS D) Xp with hW0def
  have hX₁ : X'.map (β₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = y.1.fl.X := by
    have := hfl₁ D.R.rS
    simpa [Xflag, Xa_self] using this
  have hX₂ : X'.map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = y.1.fl.X := by
    have := hfl₂ D.R.rS
    simpa [Xflag, Xa_self] using this
  have hδX' : ∀ w, δ w ∈ X' ↔ w ∈ X' := fun w => by
    rw [← mem_of_map_eq hX₂, hβδ, mem_of_map_eq hX₁]
  have hδXm : X'.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = X' := map_eq_of_iff hδX'
  have hδz : δ x.1.fl.z = x.1.fl.z := by
    apply β₂.injective
    rw [hβδ, hz₁, hz₂]
  have hδXp : Xp.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xp := by
    rw [hXpdef, FlagG.Xplus, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    simp only [LinearEquiv.coe_coe, hδz]
    rw [← hX'def, hδXm]
  have hδW : W0.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = W0 := by
    rw [hW0def, orth_map_bl iδ, hδXp]
  have hXW : X' ≤ W0 := flag_X_le x.1.fl
  have hXXp : X' ≤ Xp := le_sup_left
  have hW0L : W0 ≤ orth (VS D) X' := orth_anti hXXp
  have hR : ∀ a ∈ W0, ∀ b ∈ X', (VS D).hT a b = 0 := fun a ha b hb =>
    (VS D).herm.eq_iff.1 ((mem_orth_iff_bl.1 ha) b (hXXp hb))
  have hL : ∀ a ∈ X', ∀ b ∈ W0, (VS D).hT a b = 0 := fun a ha b hb =>
    (mem_orth_iff_bl.1 hb) a (hXXp ha)

  have hTpos : 0 < Tu D u' := (D.mem u').A.T_prime.pos
  have hpos : ∀ w ∈ W0, w ∉ X' → 0 < Algebra.trace ℚ D.host.E ((VS D).hT w w) :=
    fun w hw hwX => hP (Tu D u') hTpos x.1.fl w hw hwX

  have hadm : XLam Λ (lf D F0) ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1 :=
    xlam_le Λ (gS D) (lf D F0) x.1 hΛ.2.1.2.2.2 x.2.2.2.1 x.2.2.1
  have hstep : ∀ w ∈ W0, w ∈ Λ → ∃ a ∈ W0, a ∈ Λ ∧
      δ w - w - ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) • a ∈ X' := by
    intro w hwW hwΛ
    have hwL : w ∈ Lrep Λ x.1 := ⟨hwΛ, hW0L hwW⟩
    obtain ⟨l, hl, hlw⟩ := hI F0 Λ hΛ x w hwL
    have h1 : l - β₁ w ∈ NgX Λ (gS D) (lf D F0) y.1 := (hι₁ w hwL l hl).1 hlw
    have hδwW : δ w ∈ W0 := (mem_of_map_eq hδW w).2 hwW
    have hδwL : δ w ∈ Lrep Λ x.1 := ⟨(hδΛ w).2 hwΛ, hW0L hδwW⟩
    have h2 : l - δ w ∈ NgX Λ (gS D) (lf D F0) x.1 := (hι₂ (δ w) hδwL l hl).2 (by rw [hβδ]; exact h1)
    have h3 : δ w - w ∈ NgX Λ (gS D) (lf D F0) x.1 := by
      have := sub_mem hlw h2
      rwa [show l - w - (l - δ w) = δ w - w by abel] at this
    have h4 : NgX Λ (gS D) (lf D F0) x.1 ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1 :=
      sup_le (sup_le le_sup_left hadm) le_sup_right
    obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.1 (h4 h3)
    rw [Submodule.ideal_span_singleton_smul] at hp
    obtain ⟨a, haΛ, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hp
    have hcX : c ∈ X' := hc.2
    have hga : ((gS D : ℕ) : 𝓞 D.host.E) • a ∈ W0 := by
      have : ((gS D : ℕ) : 𝓞 D.host.E) • a = δ w - w - c := by rw [← hpc]; abel
      rw [this]
      exact sub_mem (sub_mem hδwW hwW) (hXW hcX)
    have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have h0 := (D.host.g_prime 0).ne_zero
      have h1' := (D.host.g_prime 1).ne_zero
      simp only [gS]
      exact_mod_cast Nat.mul_ne_zero h0 h1'
    have haW : a ∈ W0 := by
      have : a = ((gS D : ℕ) : D.host.E)⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • a) := by
        rw [← coe_smul_eq (S := VS D), smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hg0, one_smul]
      rw [this]
      exact W0.smul_mem _ hga
    refine ⟨a, haW, haΛ, ?_⟩
    have : δ w - w - ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) • a = c := by
      rw [← hpc]
      simp only [gS]
      abel
    rw [this]
    exact hcX
  have hfix := quot_fix (VS D).hT (VS D).herm W0 X' hR hL hpos Λ δ iδ hδΛ hδW hδXm
    (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hstep

  have hzz : (VS D).hT x.1.fl.z x.1.fl.z ≠ 0 := by
    rw [x.1.fl.z_norm]
    exact neg_ne_zero.2 (tu_ne_zero u')
  set c : D.host.E := (VS D).hT x.1.fl.z v / (VS D).hT x.1.fl.z x.1.fl.z with hc
  have hv0 : v - c • x.1.fl.z ∈ W0 := by
    rw [hW0def, mem_orth_iff_bl]
    intro q hq
    obtain ⟨q1, hq1, q2, hq2, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hq2
    have hv' := mem_orth_iff_bl.1 hv
    have e1 : (VS D).hT q1 (v - c • x.1.fl.z) = 0 := by
      rw [map_sub, map_smul, hv' q1 hq1, flag_z_orth x.1.fl q1 hq1]
      simp
    have e2 : (VS D).hT x.1.fl.z (v - c • x.1.fl.z) = 0 := by
      rw [map_sub, map_smul, hc, smul_eq_mul, div_mul_cancel₀ _ hzz, sub_self]
    rw [map_add, LinearMap.add_apply, e1, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e2]
    simp
  have hδv : δ v - v ∈ X' := by
    have h0 := hfix _ hv0
    have : δ (v - c • x.1.fl.z) - (v - c • x.1.fl.z) = δ v - v := by
      rw [map_sub, map_smul, hδz]
      abel
    rwa [this] at h0
  have hfin : β₂ (δ v - v) ∈ y.1.fl.X := (mem_of_map_eq hX₂ _).2 hδv
  rw [map_sub, hβδ] at hfin
  exact hfin

end D7

section PosWPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

/- English proof (translation)
Use `conv_lhs => rw [← S.frame.sum_equivFun a, ← S.frame.sum_equivFun b]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul, starRingEnd_apply, hconj]`. Simplify using `only [cform, dotProduct, Matrix.mulVec, Matrix.map_apply, Formalism.BasicNotions.HSpace.gram, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations.

Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_coord {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ)
    (hconj : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (a b : S.V) :
    τ (S.hT a b) = cform (S.gram.map τ) (fun i => τ (S.frame.equivFun a i))
      (fun j => τ (S.frame.equivFun b j)) := by
  conv_lhs => rw [← S.frame.sum_equivFun a, ← S.frame.sum_equivFun b]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, hconj]
  simp only [cform, dotProduct, Matrix.mulVec, Matrix.map_apply, Formalism.BasicNotions.HSpace.gram, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Complex.star_def]
  ring

/- English proof (translation)
Simplify using `only [cform, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))` and prove the remaining obligations. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cform_sum {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (d : ι → ℂ) (c : ι → n → ℂ) :
    cform G (∑ l, d l • c l) (∑ l, d l • c l) =
      ∑ l, ∑ l', starRingEnd ℂ (d l) * d l' * cform G (c l) (c l') := by
  simp only [cform, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
  simp only [Complex.star_def]
  ring

/- English proof (translation)
Rewrite using `[← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, zero_mul, sub_zero, mul_zero, neg_zero]`. Use polynomial arithmetic with `[Complex.normSq_nonneg a, Complex.normSq_nonneg b]`.
-/
theorem re_hermitian_combination_nonpos (a b z : ℂ) (T : ℝ) (hz : z.re ≤ 0) (hT : 0 ≤ T) :
    (starRingEnd ℂ a * a * z + starRingEnd ℂ b * b * (-(T : ℂ))).re ≤ 0 := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, zero_mul, sub_zero, mul_zero, neg_zero]
  nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]

/- English proof (translation)
Introduce `T' hT' F' v hv hvX`. Establish `hconj : ∀ (φ : D.host.E →+* ℂ) (a : D.host.E), φ (star a) = starRingEnd ℂ (φ a)` using `D.sp.cm.cmUnram.2.1`. Use `set t := (VS D).hT v v with ht`. Establish `hvorth` using `mem_orth_iff_bl.1 hv`. Establish `hzXp : F'.z ∈ F'.Xplus` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.

Establish `heXp : ∀ a, F'.e a ∈ F'.Xplus` using `fun a => Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hzv : (VS D).hT F'.z v = 0` using `hvorth _ hzXp`. Establish `hvz : (VS D).hT v F'.z = 0` using `(VS D).herm.eq_iff.1 hzv`. Establish `hev : ∀ a, (VS D).hT (F'.e a) v = 0` using `fun a => hvorth _ (heXp a)`. Establish `hve : ∀ a, (VS D).hT v (F'.e a) = 0` using `fun a => (VS D).herm.eq_iff.1 (hev a)`.

Establish `hze : ∀ a, (VS D).hT F'.z (F'.e a) = 0` using `fun a => (VS D).herm.eq_iff.1 (F'.z_orth a)`. Establish `hT0 : (T' : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hT'.ne'`. Set `m : Fin (D.R.rS + 2) → (VS D).V` to `Fin.cons v (Fin.cons F'.z F'.e)`. Establish `hm : LinearIndependent D.host.E m`. Rewrite using `[linearIndependent_finCons]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_finCons]`. Use `⟨F'.e_indep, ?_⟩` and prove the remaining obligations. Introduce `hz`. Establish `h0 : (VS D).hT F'.z F'.z = 0` using `flag_form_zero F' F'.z hzXp F'.z hz`.

Rewrite `h0` using `[F'.z_norm]`. Conclude with `hT0 (neg_eq_zero.1 h0)`. Introduce `hvs`. Rewrite `hvs` using `[Fin.range_cons, Submodule.span_insert]`. Take `⟨a1, ha1, a2, ha2, hsum⟩` from `Submodule.mem_sup.1 hvs`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 ha1`. Establish `h1 : (VS D).hT F'.z v = c * (VS D).hT F'.z F'.z`. Rewrite using `[← hsum, map_add, map_smul, flag_form_zero F' F'.z hzXp a2 ha2, smul_eq_mul, add_zero]`. Rewrite `h1` using `[hzv, F'.z_norm]`. Establish `hc : c = 0`.

Break down `mul_eq_zero.1 h1.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (neg_eq_zero.1 h) hT0`. Apply `hvX` to reduce the goal to its premises. Rewrite using `[← hsum, hc, zero_smul, zero_add]`.

Conclude with `ha2`. Establish `hτ : ∀ τ : D.host.E →+* ℂ, 0 < (τ t).re`. Introduce `τ`. Assume the negation of the conclusion as `hle'`. Establish `hle : (τ t).re ≤ 0` using `not_lt.1 hle'`.

Use `letI : Algebra D.host.E ℂ := τ.toAlgebra`. Use `haveI : FaithfulSMul D.host.E ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 τ.injective`. Set `c : Fin (D.R.rS + 2) → Fin (VS D).rank → ℂ` to `fun l => algebraMap D.host.E ℂ ∘ ((VS D).frame.equivFun (m l))`. Establish `hc : LinearIndependent ℂ c`. Use `linearIndependent_algebraMap_comp_iff.2 ?_` and prove the remaining obligations.

Conclude with `hm.map' (VS D).frame.equivFun.toLinearMap (VS D).frame.equivFun.ker`. Establish `hsig : Formalism.UG.HasSignature ((VS D).gram.map τ) (D.R.k + D.R.rS) (D.R.rS + 1)`. Establish `h1` using `D.sp.Y_sig 0 τ`. Rewrite `h1` using `[D.sp.baseSpace_signature_eq τ]`. Conclude with `h1`.

Establish `hneg : ∀ d : Fin (D.R.rS + 2) → ℂ, (cform ((VS D).gram.map τ) (∑ l, d l • c l) (∑ l, d l • c l)).re ≤ 0`. Introduce `d`. Establish `hexp : cform ((VS D).gram.map τ) (∑ l, d l • c l) (∑ l, d l • c l) = ∑ l, ∑ l', starRingEnd ℂ (d l) * d l' * τ ((VS D).hT (m l) (m l'))`. Rewrite using `[cform_sum]`. Use `Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))` and prove the remaining obligations.

Rewrite using `[form_coord (VS D) τ (hconj τ)]`. Both sides reduce to the same expression. Establish `hexp2 : ∑ l, ∑ l', starRingEnd ℂ (d l) * d l' * τ ((VS D).hT (m l) (m l')) = starRingEnd ℂ (d 0) * d 0 * τ t + starRingEnd ℂ (d 1) * d 1 * (-(T' : ℂ))`. Simplify using `[Fin.sum_univ_succ, m, hvz, hzv, hve, hev, hze, F'.z_orth, F'.e_iso, F'.z_norm, ht]`. Rewrite using `[hexp, hexp2]`.

Conclude with `re_hermitian_combination_nonpos _ _ _ _ hle (Nat.cast_nonneg _)`. Use `sig_bound _ hsig c hc hneg` as an intermediate fact. Simplify using `at this`. Establish `key : ((Algebra.trace ℚ D.host.E t : ℚ) : ℂ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ t`. Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]`.

Establish `key' : ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ t).re`. Use `congrArg Complex.re key` as an intermediate fact. Rewrite `this` using `[Complex.re_sum]`. Rewrite using `[← this]`. Simplify using the standard rewrite rules.

Establish `hpos : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ t).re`. Set `σ0 : D.host.E →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Conclude with `Finset.sum_pos (fun σ _ => hτ σ.toRingHom) ⟨σ0, Finset.mem_univ _⟩`. Conclude with `key' ▸ hpos` after adjusting the coercions.
-/
theorem posW_holds (D : D7) : PosW D := by
  intro T' hT' F' v hv hvX
  have hconj : ∀ (φ : D.host.E →+* ℂ) (a : D.host.E), φ (star a) = starRingEnd ℂ (φ a) :=
    D.sp.cm.cmUnram.2.1
  set t := (VS D).hT v v with ht
  have hvorth := mem_orth_iff_bl.1 hv
  have hzXp : F'.z ∈ F'.Xplus := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have heXp : ∀ a, F'.e a ∈ F'.Xplus := fun a => Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hzv : (VS D).hT F'.z v = 0 := hvorth _ hzXp
  have hvz : (VS D).hT v F'.z = 0 := (VS D).herm.eq_iff.1 hzv
  have hev : ∀ a, (VS D).hT (F'.e a) v = 0 := fun a => hvorth _ (heXp a)
  have hve : ∀ a, (VS D).hT v (F'.e a) = 0 := fun a => (VS D).herm.eq_iff.1 (hev a)
  have hze : ∀ a, (VS D).hT F'.z (F'.e a) = 0 := fun a => (VS D).herm.eq_iff.1 (F'.z_orth a)
  have hT0 : (T' : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT'.ne'
  let m : Fin (D.R.rS + 2) → (VS D).V := Fin.cons v (Fin.cons F'.z F'.e)
  have hm : LinearIndependent D.host.E m := by
    rw [linearIndependent_finCons]
    refine ⟨?_, ?_⟩
    · rw [linearIndependent_finCons]
      refine ⟨F'.e_indep, ?_⟩
      intro hz
      have h0 : (VS D).hT F'.z F'.z = 0 := flag_form_zero F' F'.z hzXp F'.z hz
      rw [F'.z_norm] at h0
      exact hT0 (neg_eq_zero.1 h0)
    · intro hvs
      rw [Fin.range_cons, Submodule.span_insert] at hvs
      obtain ⟨a1, ha1, a2, ha2, hsum⟩ := Submodule.mem_sup.1 hvs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha1
      have h1 : (VS D).hT F'.z v = c * (VS D).hT F'.z F'.z := by
        rw [← hsum, map_add, map_smul, flag_form_zero F' F'.z hzXp a2 ha2, smul_eq_mul, add_zero]
      rw [hzv, F'.z_norm] at h1
      have hc : c = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hT0
      apply hvX
      rw [← hsum, hc, zero_smul, zero_add]
      exact ha2
  have hτ : ∀ τ : D.host.E →+* ℂ, 0 < (τ t).re := by
    intro τ
    by_contra hle'
    have hle : (τ t).re ≤ 0 := not_lt.1 hle'
    letI : Algebra D.host.E ℂ := τ.toAlgebra
    haveI : FaithfulSMul D.host.E ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 τ.injective
    let c : Fin (D.R.rS + 2) → Fin (VS D).rank → ℂ :=
      fun l => algebraMap D.host.E ℂ ∘ ((VS D).frame.equivFun (m l))
    have hc : LinearIndependent ℂ c := by
      refine linearIndependent_algebraMap_comp_iff.2 ?_
      exact hm.map' (VS D).frame.equivFun.toLinearMap (VS D).frame.equivFun.ker
    have hsig : Formalism.UG.HasSignature ((VS D).gram.map τ) (D.R.k + D.R.rS) (D.R.rS + 1) := by
      have h1 := D.sp.Y_sig 0 τ
      rw [D.sp.baseSpace_signature_eq τ] at h1
      exact h1
    have hneg : ∀ d : Fin (D.R.rS + 2) → ℂ,
        (cform ((VS D).gram.map τ) (∑ l, d l • c l) (∑ l, d l • c l)).re ≤ 0 := by
      intro d
      have hexp : cform ((VS D).gram.map τ) (∑ l, d l • c l) (∑ l, d l • c l) =
          ∑ l, ∑ l', starRingEnd ℂ (d l) * d l' * τ ((VS D).hT (m l) (m l')) := by
        rw [cform_sum]
        refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
        rw [form_coord (VS D) τ (hconj τ)]
        rfl
      have hexp2 : ∑ l, ∑ l', starRingEnd ℂ (d l) * d l' * τ ((VS D).hT (m l) (m l')) =
          starRingEnd ℂ (d 0) * d 0 * τ t + starRingEnd ℂ (d 1) * d 1 * (-(T' : ℂ)) := by
        simp [Fin.sum_univ_succ, m, hvz, hzv, hve, hev, hze, F'.z_orth, F'.e_iso, F'.z_norm, ht]
      rw [hexp, hexp2]
      exact re_hermitian_combination_nonpos _ _ _ _ hle (Nat.cast_nonneg _)
    have := sig_bound _ hsig c hc hneg
    simp at this
  have key : ((Algebra.trace ℚ D.host.E t : ℚ) : ℂ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ t := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have key' : ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ t).re := by
    have := congrArg Complex.re key
    rw [Complex.re_sum] at this
    rw [← this]
    simp
  have hpos : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ t).re := by
    let σ0 : D.host.E →ₐ[ℚ] ℂ := IsAlgClosed.lift
    exact Finset.sum_pos (fun σ _ => hτ σ.toRingHom) ⟨σ0, Finset.mem_univ _⟩
  exact_mod_cast key' ▸ hpos

end PosWPf

section Final

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Corank

/- English proof (translation)
Introduce `F0 Λ hΛ x x' hx'`. Take `⟨ξ, hξ⟩` from `x.2.2.1`. Establish `hU` using `hΛ.2.1.2.1`. Establish `hFC` using `hΛ.2.1.2.2.2`. Establish `hmem : x' ∈ Lrep Λ (lf D F0) ⊔ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ`.

Use `mem_of_forall_locP (fun P => ?_)` and prove the remaining obligations. Use `haveI := P.isPrime`. Distinguish the cases in `hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Take `⟨t, ht, l, hl, hlt⟩` from `PI.UnitaryGroupMassFormula.BetaLUniq.EigB.iotaLift hU hFC hξ P hgP x' hx'.1 hx'.2`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Establish `e : t • x' = l - (l - t • x')` using `by abel`. Rewrite using `[e]`. Conclude with `sub_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right hlt)`. Conclude with `⟨_, hgP, Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx'.1)⟩`. Take `⟨l, hl, n, hn, hln⟩` from `Submodule.mem_sup.1 hmem`.

Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Establish `e : l - x' = -n` using `by rw [← hln]; abel`. Rewrite using `[e]`. Conclude with `neg_mem (Submodule.mem_sup_left (Submodule.mem_sup_left hn))`.
-/
theorem iotaLift_holds (D : D7) (u u' : D.what₂.Word) : IotaLift D u u' := by
  intro F0 Λ hΛ x x' hx'
  obtain ⟨ξ, hξ⟩ := x.2.2.1
  have hU := hΛ.2.1.2.1
  have hFC := hΛ.2.1.2.2.2
  have hmem : x' ∈ Lrep Λ (lf D F0) ⊔ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    refine mem_of_forall_locP (fun P => ?_)
    haveI := P.isPrime
    by_cases hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    · obtain ⟨t, ht, l, hl, hlt⟩ :=
        PI.UnitaryGroupMassFormula.BetaLUniq.EigB.iotaLift hU hFC hξ P hgP x' hx'.1 hx'.2
      refine ⟨t, ht, ?_⟩
      have e : t • x' = l - (l - t • x') := by abel
      rw [e]
      exact sub_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right hlt)
    · exact ⟨_, hgP, Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx'.1)⟩
  obtain ⟨l, hl, n, hn, hln⟩ := Submodule.mem_sup.1 hmem
  refine ⟨l, hl, ?_⟩
  have e : l - x' = -n := by rw [← hln]; abel
  rw [e]
  exact neg_mem (Submodule.mem_sup_left (Submodule.mem_sup_left hn))

/- English proof (translation)
Introduce `D u u'` and use `betaL_of D u u' (iotaLift_holds D u u') (posW_holds D)`.
-/
theorem beta_lattice_holds : ∀ (D : D7) (u u' : D.what₂.Word), BetaL D u u' :=
  fun D u u' => betaL_of D u u' (iotaLift_holds D u u') (posW_holds D)

end Final

end Formalism.L2.SG.Pf
