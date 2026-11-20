import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGOthNotDvd

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Unfold `InModP`. Rewrite using `[imA_span_Bg X p]`.
-/
theorem imA_inModP_Bg (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p X.B.g S y ↔ InModP X p (gOf p) S y := by
  unfold InModP
  rw [imA_span_Bg X p]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Subring.one_mem _, map_one _⟩`.
-/
theorem imA_OEp_one (p : TypX X) : (1 : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) ∈ OEp X p :=
  ⟨1, Subring.one_mem _, map_one _⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hs`. Take `⟨b, hb, rfl⟩` from `ht`. Conclude with `⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩`.
-/
theorem imA_OEp_sub (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s - t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩

abbrev epsP (p : TypX X) : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E := PI.FinKW.psiV X.B.I p.1 X.ew

/- English proof (translation)
Assemble the required witnesses or components as `⟨X.ew, X.ew_int, rfl⟩`.
-/
theorem imA_eps_mem (p : TypX X) : epsP X p ∈ OEp X p := ⟨X.ew, X.ew_int, rfl⟩

/- English proof (translation)
Unfold `epsP`. Rewrite using `[← map_mul, X.ew_idem]`.
-/
theorem imA_eps_idem (p : TypX X) : epsP X p * epsP X p = epsP X p := by
  unfold epsP
  rw [← map_mul, X.ew_idem]

/- English proof (translation)
Unfold `latLoc at hu ⊢`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨l, hl, rfl⟩` from `hw`. Use `Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul c a _ ha => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
private theorem latLoc_ringOfIntegers_incl (p : TypX X) (x : 𝓞 X.B.I.E) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((1 : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  unfold latLoc at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩
    funext i
    simp [ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

/- English proof (translation)
Establish `h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ c hu`.
-/
private theorem latLoc_adicIntegers_incl (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u := by
    funext i
    simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c hu

/- English proof (translation)
Establish `key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E` using `X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)), PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by`. Introduce `b hb`. Unfold `Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb`. Proceed by induction on `hb using Subring.closure_induction with`. Consider the case `mem z hz`.

Introduce `w hw`. Break down `hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩` into its components or cases. Take `⟨x, rfl⟩` from `RingHom.mem_range.mp he`. Use `latLoc_ringOfIntegers_incl X p x hw using 2` and compare the differences between its conclusion and the goal. Simplify using `[PI.FinKW.psiV]`.

Establish `hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F` using `hy`. Use `latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `simp [PI.FinKW.psiV] <;> rfl`. Consider the case `zero => intro w _`. Simplify using the standard rewrite rules.

Consider the case `one => intro w hw`. Simplify using `using hw`. Consider the case `add a b _ _ ha hb => intro w hw`. Rewrite using `[map_add, add_smul]`. Conclude with `add_mem (ha w hw) (hb w hw)`.

Consider the case `neg a _ ha => intro w hw`. Rewrite using `[map_neg, neg_smul]`. Conclude with `neg_mem (ha w hw)`. Consider the case `mul a b _ _ ha hb => intro w hw`. Rewrite using `[map_mul, mul_smul]`.

Conclude with `ha _ (hb w hw)`. Take `⟨a, ha, rfl⟩` from `ht`. Conclude with `key a ha u hu`.
-/
theorem imA_lat_OEp (p : TypX X) {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    t • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro b hb
    unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb
    induction hb using Subring.closure_induction with
    | mem z hz =>
      intro w hw
      rcases hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · obtain ⟨x, rfl⟩ := RingHom.mem_range.mp he
        convert latLoc_ringOfIntegers_incl X p x hw using 2
        simp [PI.FinKW.psiV]
      · have hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F := hy
        convert latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2
        simp [PI.FinKW.psiV] <;> rfl
    | zero => intro w _; simp
    | one => intro w hw; simpa using hw
    | add a b _ _ ha hb => intro w hw; rw [map_add, add_smul]; exact add_mem (ha w hw) (hb w hw)
    | neg a _ ha => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (ha w hw)
    | mul a b _ _ ha hb => intro w hw; rw [map_mul, mul_smul]; exact ha _ (hb w hw)
  obtain ⟨a, ha, rfl⟩ := ht
  exact key a ha u hu

/- English proof (translation)
Unfold `InModP at h ⊢`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp h`. Use `clear h`. Rewrite using `[smul_add]`. Apply `Submodule.add_mem_sup` to reduce the goal to its premises.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨t', ht', s, hs, rfl⟩` from `hw`. Conclude with `Submodule.subset_span ⟨t', ht', t • s, ⟨s, hs, rfl⟩, smul_comm t t' s⟩`. Consider the case `zero => simp`.

Consider the case `add a₁ a₂ _ _ ha₁ ha₂ => rw [smul_add]`. Conclude with `add_mem ha₁ ha₂`. Consider the case `smul c a₁ _ ha₁ => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ c ha₁`. Use `Submodule.smul_induction_on (p := fun b => t • b ∈ _) hb ?_ ?_` and prove the remaining obligations.

Introduce `r hr n hn`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem_smul hr (imA_lat_OEp X p ht hn)`. Introduce `a b ha hb`. Rewrite using `[smul_add]`.

Conclude with `add_mem ha hb`.
-/
theorem inModP_smul (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (h : InModP X p m S y) :
    InModP X p m ((fun s => t • s) '' S) (t • y) := by
  unfold InModP at h ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
  clear h
  rw [smul_add]
  apply Submodule.add_mem_sup
  · induction ha using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t', ht', s, hs, rfl⟩ := hw
      exact Submodule.subset_span ⟨t', ht', t • s, ⟨s, hs, rfl⟩, smul_comm t t' s⟩
    | zero => simp
    | add a₁ a₂ _ _ ha₁ ha₂ => rw [smul_add]; exact add_mem ha₁ ha₂
    | smul c a₁ _ ha₁ => rw [smul_comm]; exact Submodule.smul_mem _ c ha₁
  · refine Submodule.smul_induction_on (p := fun b => t • b ∈ _) hb ?_ ?_
    · intro r hr n hn
      rw [smul_comm]
      exact Submodule.smul_mem_smul hr (imA_lat_OEp X p ht hn)
    · intro a b ha hb
      rw [smul_add]
      exact add_mem ha hb

/- English proof (translation)
Unfold `InModP at h ⊢`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp h`. Use `Submodule.add_mem_sup ?_ hb` and prove the remaining obligations. Establish `hle : Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t' ∈ OEp X p, ∃ s ∈ (fun s => t • s) '' S, w = t' • s} ≤ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t' ∈ OEp X p, ∃ s ∈ S, w = t' • s}`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `w ⟨t', ht', _, ⟨s, hs, rfl⟩, rfl⟩`. Conclude with `⟨t' * t, imA_OEp_mul X p ht' ht, s, hs, (mul_smul t' t s).symm⟩`. Conclude with `hle ha`.
-/
theorem inModP_of_inModP_smul_image (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (h : InModP X p m ((fun s => t • s) '' S) y) :
    InModP X p m S y := by
  unfold InModP at h ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
  refine Submodule.add_mem_sup ?_ hb
  have hle : Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
        {w | ∃ t' ∈ OEp X p, ∃ s ∈ (fun s => t • s) '' S, w = t' • s} ≤
      Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t' ∈ OEp X p, ∃ s ∈ S, w = t' • s} := by
    apply Submodule.span_mono
    rintro w ⟨t', ht', _, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨t' * t, imA_OEp_mul X p ht' ht, s, hs, (mul_smul t' t s).symm⟩
  exact hle ha

/- English proof (translation)
Establish `h1 : (1 - epsP X p) ∈ OEp X p` using `imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨inModP_smul X p m S (imA_eps_mem X p) h, inModP_smul X p m S h1 h⟩`. Introduce and unpack `⟨h₁, h₂⟩`.

Establish `e1` using `inModP_of_inModP_smul_image X p m S (imA_eps_mem X p) h₁`. Establish `e2` using `inModP_of_inModP_smul_image X p m S h1 h₂`. Establish `hy : epsP X p • y + (1 - epsP X p) • y = y`. Rewrite using `[sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← hy]`. Unfold `InModP at e1 e2 ⊢`. Conclude with `add_mem e1 e2`.
-/
theorem inModP_iff_split (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p m S y ↔ InModP X p m ((fun s => epsP X p • s) '' S) (epsP X p • y) ∧
      InModP X p m ((fun s => (1 - epsP X p) • s) '' S) ((1 - epsP X p) • y) := by
  have h1 : (1 - epsP X p) ∈ OEp X p := imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)
  constructor
  · intro h
    exact ⟨inModP_smul X p m S (imA_eps_mem X p) h, inModP_smul X p m S h1 h⟩
  · rintro ⟨h₁, h₂⟩
    have e1 := inModP_of_inModP_smul_image X p m S (imA_eps_mem X p) h₁
    have e2 := inModP_of_inModP_smul_image X p m S h1 h₂
    have hy : epsP X p • y + (1 - epsP X p) • y = y := by
      rw [sub_smul, one_smul]
      abel
    rw [← hy]
    unfold InModP at e1 e2 ⊢
    exact add_mem e1 e2

end MassDataIdxSteps
