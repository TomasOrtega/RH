import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferencesSpanIntertwinersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherFurther

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThK.TransMaps

section Abstract

variable {P V ι : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup V] [Module ℂ V]

def gen (ρ : ι → V →ₗ[ℂ] V) : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)

/- English proof (translation)
Use `first`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `@_root_.GlobalTheory.SpectralLemmaFirst.main`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `_root_.GlobalTheory.SpectralLemmaFirst.main`.

Consider the case `exact @_root_.GlobalTheory.SpectralLemmaFirst.main`. Consider the case `exact _root_.GlobalTheory.SpectralLemmaFirst.main`. Consider the case `(apply _root_.GlobalTheory.SpectralLemmaFirst.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpectralLemmaFirst.main <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.SpectralLemmaFirst.main <;> first | assumption | infer_instance)`.

Consider the case `(intros; exact _root_.GlobalTheory.SpectralLemmaFirst.main ..)`.
-/
theorem gen_stable {ρ : ι → V →ₗ[ℂ] V} {N : Submodule ℂ V} (hN : ∀ y, ∀ x ∈ N, ρ y x ∈ N)
    {s : Module.End ℂ V} (hs : s ∈ gen ρ) : ∀ x ∈ N, s x ∈ N := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SpectralLemmaFirst.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SpectralLemmaFirst.main
  | exact @_root_.GlobalTheory.SpectralLemmaFirst.main
  | exact _root_.GlobalTheory.SpectralLemmaFirst.main
  | (apply _root_.GlobalTheory.SpectralLemmaFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpectralLemmaFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpectralLemmaFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpectralLemmaFirst.main ..)

def lift (ρ : ι → V →ₗ[ℂ] V) (N : Submodule ℂ V) (hN : ∀ y, ∀ x ∈ N, ρ y x ∈ N) : Submodule (gen ρ) V where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' s x hx := gen_stable hN s.2 x hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lift {ρ : ι → V →ₗ[ℂ] V} {N : Submodule ℂ V} {hN : ∀ y, ∀ x ∈ N, ρ y x ∈ N} {x : V} :
    x ∈ lift ρ N hN ↔ x ∈ N := Iff.rfl

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨y, rfl⟩`.
-/
theorem mem_gen (ρ : ι → V →ₗ[ℂ] V) (y : ι) : ρ y ∈ gen ρ := Algebra.subset_adjoin ⟨y, rfl⟩

/- English proof (translation)
Use `set A := gen ρ`. Establish `hstab : ∀ j y, ∀ x ∈ LinearMap.range (T j), ρ y x ∈ LinearMap.range (T j)`. Introduce and unpack `j y _ ⟨ζ, rfl⟩`. Take `⟨ζ₁, h⟩` from `tot y ζ`. Conclude with `⟨ζ₁, hT j y ζ ζ₁ h⟩`.

Set `Rj : Fin m → Submodule A V` to `fun j => lift ρ (LinearMap.range (T j)) (hstab j)`. Establish `atom : ∀ j, Rj j ≠ ⊥ → IsAtom (Rj j)`. Introduce `j hne`. Use `⟨hne, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hQ` using `irred ((b.restrictScalars ℂ).comap (T j)) (by`.

Introduce `y ζ ζ₁ h hζ`. Express the relevant statement in the definitionally equal form `T j ζ₁ ∈ b`. Rewrite using `[hT j y ζ ζ₁ h]`. Conclude with `b.smul_mem (⟨ρ y, mem_gen ρ y⟩ : A) hζ)`. Break down `hQ with hQ | hQ` into its components or cases.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨ζ, rfl⟩ : x ∈ LinearMap.range (T j)` from `hb.le hx`. Establish `: ζ ∈ (b.restrictScalars ℂ).comap (T j)` using `hx`. Rewrite `this` using `[hQ, Submodule.mem_bot]`.

Simplify using `[this]`. It suffices to derive a contradiction. Use `hb.not_ge fun x hx => ?_` and prove the remaining obligations. Take `⟨ζ, rfl⟩ : x ∈ LinearMap.range (T j)` from `hx`. Establish `: ζ ∈ (b.restrictScalars ℂ).comap (T j)` using `by rw [hQ]; trivial`.

Conclude with `this`. Set `s : Set (Fin m)` to `{j | Rj j ≠ ⊥}`. Set `M : Submodule A V` to `⨆ j ∈ s, Rj j`. Use `haveI : IsSemisimpleModule A M := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun j hj => haveI := (isSimpleModule_iff_isAtom.mpr (atom j hj)); inferInstance)`. Establish `memM : ∀ j ζ, T j ζ ∈ M`.

Introduce `j ζ`. Distinguish the cases in `hj : j ∈ s`. Conclude with `(le_biSup Rj hj : Rj j ≤ M) ⟨ζ, rfl⟩`. Establish `: Rj j = ⊥` using `by simpa [s] using hj`. Establish `h0 : T j ζ ∈ Rj j` using `⟨ζ, rfl⟩`.

Rewrite `h0` using `[this, Submodule.mem_bot]`. Rewrite using `[h0]`. Conclude with `M.zero_mem`. Set `N' : Submodule A M` to `(lift ρ N hN).comap M.subtype`. Take `⟨C, hC⟩` from `exists_isCompl N'`.

Set `Pv : M →ₗ[A] V` to `M.subtype ∘ₗ N'.subtype ∘ₗ N'.linearProjOfIsCompl C hC`. Establish `Pv_mem : ∀ z, Pv z ∈ N` using `fun z => (N'.linearProjOfIsCompl C hC z).2`. Establish `Pv_fix : ∀ z ∈ N', Pv z = z` using `fun z hz => congrArg (fun w : N' => ((w : M) : V)) (Submodule.linearProjOfIsCompl_apply_left hC ⟨z, hz⟩)`. Set `S : Fin m → P →ₗ[ℂ] V` to `fun j => (Pv.restrictScalars ℂ).comp ((T j).codRestrict (M.restrictScalars ℂ) (memM j))`. Establish `S_apply : ∀ j ζ, S j ζ = Pv ⟨T j ζ, memM j ζ⟩` using `fun _ _ => rfl`.

Establish `key : ∑ j, T j (ξ j) = ∑ j, S j (ξ j)`. Establish `hsum : (∑ j, (⟨T j (ξ j), memM j (ξ j)⟩ : M)) ∈ N'`. Rewrite using `[Submodule.mem_comap, map_sum, mem_lift]`. Simplify using `using hx`. Use `Pv_fix _ hsum` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify using `only [S_apply]`. Rewrite using `[this, Submodule.coe_sum]`. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨S j, fun ζ => Pv_mem _, ?_, ξ j, rfl⟩` and prove the remaining obligations.

Introduce `y ζ ζ₁ h`. Rewrite using `[S_apply, S_apply]`. Establish `e : (⟨T j ζ₁, memM j ζ₁⟩ : M) = (⟨ρ y, mem_gen ρ y⟩ : A) • ⟨T j ζ, memM j ζ⟩` using `by ext; exact hT j y ζ ζ₁ h`. Rewrite using `[e, map_smul]`. Both sides reduce to the same expression.
-/
theorem sum_mem_span (R : ι → P → P → Prop) (ρ : ι → V →ₗ[ℂ] V) (tot : ∀ y ξ, ∃ ξ₁, R y ξ ξ₁)
    (irred : ∀ Q : Submodule ℂ P, (∀ y ξ ξ₁, R y ξ ξ₁ → ξ ∈ Q → ξ₁ ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (N : Submodule ℂ V) (hN : ∀ y, ∀ x ∈ N, ρ y x ∈ N) {m : ℕ} (T : Fin m → P →ₗ[ℂ] V)
    (hT : ∀ j y ξ ξ₁, R y ξ ξ₁ → T j ξ₁ = ρ y (T j ξ)) (ξ : Fin m → P) (hx : ∑ j, T j (ξ j) ∈ N) :
    ∑ j, T j (ξ j) ∈ Submodule.span ℂ {x | ∃ S : P →ₗ[ℂ] V, (∀ ζ, S ζ ∈ N) ∧
      (∀ y ζ ζ₁, R y ζ ζ₁ → S ζ₁ = ρ y (S ζ)) ∧ ∃ ζ, x = S ζ} := by
  classical
  set A := gen ρ
  have hstab : ∀ j y, ∀ x ∈ LinearMap.range (T j), ρ y x ∈ LinearMap.range (T j) := by
    rintro j y _ ⟨ζ, rfl⟩
    obtain ⟨ζ₁, h⟩ := tot y ζ
    exact ⟨ζ₁, hT j y ζ ζ₁ h⟩
  let Rj : Fin m → Submodule A V := fun j => lift ρ (LinearMap.range (T j)) (hstab j)
  have atom : ∀ j, Rj j ≠ ⊥ → IsAtom (Rj j) := by
    intro j hne
    refine ⟨hne, fun b hb => ?_⟩
    have hQ := irred ((b.restrictScalars ℂ).comap (T j)) (by
      intro y ζ ζ₁ h hζ
      change T j ζ₁ ∈ b
      rw [hT j y ζ ζ₁ h]
      exact b.smul_mem (⟨ρ y, mem_gen ρ y⟩ : A) hζ)
    rcases hQ with hQ | hQ
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨ζ, rfl⟩ : x ∈ LinearMap.range (T j) := hb.le hx
      have : ζ ∈ (b.restrictScalars ℂ).comap (T j) := hx
      rw [hQ, Submodule.mem_bot] at this
      simp [this]
    · exfalso
      refine hb.not_ge fun x hx => ?_
      obtain ⟨ζ, rfl⟩ : x ∈ LinearMap.range (T j) := hx
      have : ζ ∈ (b.restrictScalars ℂ).comap (T j) := by rw [hQ]; trivial
      exact this
  let s : Set (Fin m) := {j | Rj j ≠ ⊥}
  let M : Submodule A V := ⨆ j ∈ s, Rj j
  haveI : IsSemisimpleModule A M := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
    (fun j hj => haveI := (isSimpleModule_iff_isAtom.mpr (atom j hj)); inferInstance)
  have memM : ∀ j ζ, T j ζ ∈ M := by
    intro j ζ
    by_cases hj : j ∈ s
    · exact (le_biSup Rj hj : Rj j ≤ M) ⟨ζ, rfl⟩
    · have : Rj j = ⊥ := by simpa [s] using hj
      have h0 : T j ζ ∈ Rj j := ⟨ζ, rfl⟩
      rw [this, Submodule.mem_bot] at h0
      rw [h0]; exact M.zero_mem
  let N' : Submodule A M := (lift ρ N hN).comap M.subtype
  obtain ⟨C, hC⟩ := exists_isCompl N'
  let Pv : M →ₗ[A] V := M.subtype ∘ₗ N'.subtype ∘ₗ N'.linearProjOfIsCompl C hC
  have Pv_mem : ∀ z, Pv z ∈ N := fun z => (N'.linearProjOfIsCompl C hC z).2
  have Pv_fix : ∀ z ∈ N', Pv z = z := fun z hz =>
    congrArg (fun w : N' => ((w : M) : V)) (Submodule.linearProjOfIsCompl_apply_left hC ⟨z, hz⟩)
  let S : Fin m → P →ₗ[ℂ] V := fun j => (Pv.restrictScalars ℂ).comp
    ((T j).codRestrict (M.restrictScalars ℂ) (memM j))
  have S_apply : ∀ j ζ, S j ζ = Pv ⟨T j ζ, memM j ζ⟩ := fun _ _ => rfl
  have key : ∑ j, T j (ξ j) = ∑ j, S j (ξ j) := by
    have hsum : (∑ j, (⟨T j (ξ j), memM j (ξ j)⟩ : M)) ∈ N' := by
      rw [Submodule.mem_comap, map_sum, mem_lift]
      simpa using hx
    have := Pv_fix _ hsum
    rw [map_sum] at this
    simp only [S_apply]
    rw [this, Submodule.coe_sum]
  rw [key]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨S j, fun ζ => Pv_mem _, ?_, ξ j, rfl⟩
  intro y ζ ζ₁ h
  rw [S_apply, S_apply]
  have e : (⟨T j ζ₁, memM j ζ₁⟩ : M) = (⟨ρ y, mem_gen ρ y⟩ : A) • ⟨T j ζ, memM j ζ⟩ := by
    ext; exact hT j y ζ ζ₁ h
  rw [e, map_smul]
  rfl

end Abstract

section Concrete

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c N hN f hf hfN`. Establish `hA` using `GlobalTheory.T.theta_action_exists hKP.base`. Establish `ex` using `(hA F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hM.triple) B.v₁).1`. Establish `ex'` using `(hA F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hM.triple) B.v₁).1`. Establish `one_mem : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F B.v₁)`.

Introduce `n Y u _`. Express the relevant statement in the definitionally equal form `u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0`. Rewrite using `[sub_self, smul_zero]`. Set `ι` to `UAt σ G.W (evFin F B.v₁)`. Set `Rel : ι → Rf.Pi B.v₁ → Rf.Pi B.v₁ → Prop` to `fun y ξ ξ₁ => ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (1, y.1)) φ φ₁ ∧ Rf.p B.v₁ φ = ξ ∧ Rf.p B.v₁ φ₁ = ξ₁`.

Set `ρ : ι → (UA σ G.W.J → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ)` to `fun y => LinearMap.funLeft ℂ ℂ (· * y.1)`. Establish `ρ_apply : ∀ y (F₀ : UA σ G.W.J → ℂ) h, ρ y F₀ h = F₀ (h * y.1)` using `fun _ _ _ => rfl`. Establish `onto : ∀ ξ, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Rf.p B.v₁ φ = ξ` using `fun ξ => by`. Establish `: ξ ∈ (SB _).map (Rf.p B.v₁)` using `by rw [hM.fin.onto B.v₁]; trivial`. Conclude with `Submodule.mem_map.1 this`.

Establish `onto' : ∀ ξ, ∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Rf.p' B.v₁ φ = ξ` using `fun ξ => by`. Establish `: ξ ∈ (SB _).map (Rf.p' B.v₁)` using `by rw [hM.fin.onto' B.v₁]; trivial`. Conclude with `Submodule.mem_map.1 this`. Establish `tot : ∀ y ξ, ∃ ξ₁, Rel y ξ ξ₁`. Introduce `y ξ`.

Take `⟨φ, hφ, rfl⟩` from `onto ξ`. Take `⟨φ₁, hφ₁, hact⟩` from `(ex 1 (one_mem G.V) y.1 y.2 φ hφ).exists`. Conclude with `⟨_, φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩`. Establish `irred : ∀ Q : Submodule ℂ (Rf.Pi B.v₁), (∀ y ξ ξ₁, Rel y ξ ξ₁ → ξ ∈ Q → ξ₁ ∈ Q) → Q = ⊥ ∨ Q = ⊤` using `fun Q hQ => hM.fin.irred B.v₁ Q fun h hh φ hφ φ₁ hφ₁ hact hmem => hQ ⟨h, hh⟩ _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩ hmem`. Establish `hN' : ∀ y, ∀ x ∈ N, ρ y x ∈ N` using `fun y x hx => hN y.1 y.2 x hx`.

Establish `transfer : ∀ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ), (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) → ∀ y ξ ξ …`. Introduce and unpack `T hT y _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩`. Take `⟨φ', hφ', he⟩` from `onto' (Rf.p B.v₁ φ)`. Take `⟨φ₁', hφ₁', hact'⟩` from `(ex' 1 (one_mem G.V') y.1 y.2 φ' hφ').exists`. Establish `e₁` using `hM.fin.equiv B.v₁ y.1 y.2 φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' he.symm`.

Use function extensionality and compare the values at `h`. Rewrite using `[e₁, hT y.1 y.2 φ' hφ' φ₁' hφ₁' hact' h, ρ_apply, he]`. Establish `hI` using `GlobalTheory.T.differences_span_intertwiners hKP F E σ B a a' G X om om' R Rf hM c hf`. Take `⟨m, k, g, hg⟩` from `Submodule.mem_span_set'.1 hI`. Use `choose T hTD hTe ξ hξ using fun j => (g j).2`.

Establish `hsum : f = ∑ j, T j (k j • ξ j)`. Rewrite using `[← hg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hξ j]`. Establish `key` using `TransMaps.sum_mem_span Rel ρ tot irred N hN' T (fun j => transfer (T j) (hTe j)) (fun j => k j • ξ j) (hsum ▸ hfN)`.

Rewrite using `[hsum]`. Use `Submodule.span_mono ?_ key` and prove the remaining obligations. Introduce and unpack `_ ⟨S, hSN, hSe, ζ, rfl⟩`. Take `⟨φ, hφ, rfl⟩` from `onto ζ`. Use `⟨S ∘ₗ Rf.p B.v₁, fun _ _ => hSN _, fun z hz => ?_, ?_, φ, hφ, rfl⟩` and prove the remaining obligations.

Establish `: z ∈ LinearMap.ker (Rf.p B.v₁)` using `hM.fin.inv B.v₁ hz`. Rewrite `this`, the goal using `[LinearMap.mem_ker]`. Simplify using `[this]`. Introduce `y hy φ₀ hφ₀ φ₁ hφ₁ hact h`. Use `hSe ⟨y, hy⟩ _ _ ⟨φ₀, hφ₀, φ₁, hφ₁, hact, rfl, rfl⟩` as an intermediate fact.

Conclude with `congrFun this h`.
-/
theorem diffs_mem_span_maps : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (c : ℂ) (N : Submodule ℂ (UA σ G.W.J → ℂ)), (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ F₀ ∈ N, (fun h => F₀ (h * y)) ∈ N) →
    ∀ f ∈ GlobalTheory.ThK.DescB.Diffs B G X om om' R Rf c, f ∈ N →
      f ∈ Submodule.span ℂ {F₀ | ∃ T : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ),
        (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), T φ ∈ N) ∧ augAt om B.v₁ ≤ LinearMap.ker T ∧
        (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om (1, y)) φ φ₁ → ∀ h, T φ₁ h = T φ (h * y)) ∧ ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), F₀ = T φ} := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c N hN f hf hfN
  have hA := GlobalTheory.T.theta_action_exists hKP.base
  have ex := (hA F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hM.triple) B.v₁).1
  have ex' := (hA F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hM.triple) B.v₁).1
  have one_mem : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F B.v₁) := by
    intro n Y u _
    change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  let ι := UAt σ G.W (evFin F B.v₁)
  let Rel : ι → Rf.Pi B.v₁ → Rf.Pi B.v₁ → Prop := fun y ξ ξ₁ =>
    ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om (1, y.1)) φ φ₁ ∧ Rf.p B.v₁ φ = ξ ∧ Rf.p B.v₁ φ₁ = ξ₁
  let ρ : ι → (UA σ G.W.J → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ) := fun y => LinearMap.funLeft ℂ ℂ (· * y.1)
  have ρ_apply : ∀ y (F₀ : UA σ G.W.J → ℂ) h, ρ y F₀ h = F₀ (h * y.1) := fun _ _ _ => rfl
  have onto : ∀ ξ, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Rf.p B.v₁ φ = ξ := fun ξ => by
    have : ξ ∈ (SB _).map (Rf.p B.v₁) := by rw [hM.fin.onto B.v₁]; trivial
    exact Submodule.mem_map.1 this
  have onto' : ∀ ξ, ∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Rf.p' B.v₁ φ = ξ := fun ξ => by
    have : ξ ∈ (SB _).map (Rf.p' B.v₁) := by rw [hM.fin.onto' B.v₁]; trivial
    exact Submodule.mem_map.1 this
  have tot : ∀ y ξ, ∃ ξ₁, Rel y ξ ξ₁ := by
    intro y ξ
    obtain ⟨φ, hφ, rfl⟩ := onto ξ
    obtain ⟨φ₁, hφ₁, hact⟩ := (ex 1 (one_mem G.V) y.1 y.2 φ hφ).exists
    exact ⟨_, φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩
  have irred : ∀ Q : Submodule ℂ (Rf.Pi B.v₁), (∀ y ξ ξ₁, Rel y ξ ξ₁ → ξ ∈ Q → ξ₁ ∈ Q) → Q = ⊥ ∨ Q = ⊤ :=
    fun Q hQ => hM.fin.irred B.v₁ Q fun h hh φ hφ φ₁ hφ₁ hact hmem =>
      hQ ⟨h, hh⟩ _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩ hmem
  have hN' : ∀ y, ∀ x ∈ N, ρ y x ∈ N := fun y x hx => hN y.1 y.2 x hx

  have transfer : ∀ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
      (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) →
      ∀ y ξ ξ₁, Rel y ξ ξ₁ → T ξ₁ = ρ y (T ξ) := by
    rintro T hT y _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩
    obtain ⟨φ', hφ', he⟩ := onto' (Rf.p B.v₁ φ)
    obtain ⟨φ₁', hφ₁', hact'⟩ := (ex' 1 (one_mem G.V') y.1 y.2 φ' hφ').exists
    have e₁ := hM.fin.equiv B.v₁ y.1 y.2 φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' he.symm
    funext h
    rw [e₁, hT y.1 y.2 φ' hφ' φ₁' hφ₁' hact' h, ρ_apply, he]
  have hI := GlobalTheory.T.differences_span_intertwiners hKP F E σ B a a' G X om om' R Rf hM c hf
  obtain ⟨m, k, g, hg⟩ := Submodule.mem_span_set'.1 hI
  choose T hTD hTe ξ hξ using fun j => (g j).2
  have hsum : f = ∑ j, T j (k j • ξ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hξ j]
  have key := TransMaps.sum_mem_span Rel ρ tot irred N hN' T (fun j => transfer (T j) (hTe j)) (fun j => k j • ξ j)
    (hsum ▸ hfN)
  rw [hsum]
  refine Submodule.span_mono ?_ key
  rintro _ ⟨S, hSN, hSe, ζ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := onto ζ
  refine ⟨S ∘ₗ Rf.p B.v₁, fun _ _ => hSN _, fun z hz => ?_, ?_, φ, hφ, rfl⟩
  · have : z ∈ LinearMap.ker (Rf.p B.v₁) := hM.fin.inv B.v₁ hz
    rw [LinearMap.mem_ker] at this ⊢
    simp [this]
  · intro y hy φ₀ hφ₀ φ₁ hφ₁ hact h
    have := hSe ⟨y, hy⟩ _ _ ⟨φ₀, hφ₀, φ₁, hφ₁, hact, rfl, rfl⟩
    exact congrFun this h

end Concrete

end GlobalTheory.ThK.TransMaps
