import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInducedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumpsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpTranslateMemSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetweenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowUpdateNhdsGenerationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOpenCellRetractionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCellStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureOpenNonemptyNeZeroStatement

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO
section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Take `⟨L, hLo, hL⟩` from `GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H ρ y`. Take `⟨K, hKo, hKc, hKL⟩` from `hbase _ (hLo.mem_nhds L.one_mem)`. Use `GlobalTheory.T.mem_submodule_of_bumps H ρ K hKo hKc y (fun g x hx => hL g x (hKL hx)) S fun c B hB => ?_` and prove the remaining obligations. Set `K₁ : Subgroup G` to `K.map (MulAut.conj c).toMonoidHom`. Establish `hK₁ : ∀ x, x ∈ K₁ ↔ c⁻¹ * x * c ∈ K`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `: c⁻¹ * ((MulAut.conj c).toMonoidHom z) * c = z`. Simplify using `[MulAut.conj_apply]`.

Use `group`. Rewrite using `[this]`. Conclude with `hz`. Introduce `h`. Conclude with `⟨_, h, by simp [MulAut.conj_apply]; group⟩`.

Establish `hconj : Continuous fun x : G => c⁻¹ * x * c` using `by fun_prop`. Establish `hconj' : Continuous fun x : G => c * x * c⁻¹` using `by fun_prop`. Establish `hset : (K₁ : Set G) = (fun x : G => c⁻¹ * x * c) ⁻¹' (K : Set G)` using `Set.ext hK₁`. Establish `hK₁o : IsOpen (K₁ : Set G)` using `by rw [hset]; exact hKo.preimage hconj`. Establish `hK₁c : IsCompact (K₁ : Set G)`.

Establish `: (K₁ : Set G) = (fun x : G => c * x * c⁻¹) '' (K : Set G)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, (hK₁ x).1 h, by group⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Use `(hK₁ _).2 ?_` and prove the remaining obligations. Establish `: c⁻¹ * (c * z * c⁻¹) * c = z` using `by group`. Rewrite using `[this]`. Conclude with `hz`.

Rewrite using `[this]`. Conclude with `hKc.image hconj'`. Use `set v := y.1.1.1 c with hvdef`. Establish `hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v`. Introduce `a ha`.

Establish `h1` using `(hK₁ _).1 ha`. Establish `e : (a : G) * c = c * (c⁻¹ * a * c)` using `by group`. Establish `e1 : y.1.1.1 ((a : G) * c) = ρ a (y.1.1.1 c)` using `y.1.1.2 a c`. Rewrite `e1` using `[← hvdef]`. Rewrite using `[← e1, e, hL c _ (hKL h1)]`.

Establish `hB' : IsBump H ρ K₁ 1 v (cInd H ρ c B)`. Use `⟨fun a x hx => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Use `show B.1.1.1 ((a : G) * 1 * x * c) = _`. Establish `e : (a : G) * 1 * x * c = a * c * (c⁻¹ * x * c)` using `by group`. Rewrite using `[e]`.

Conclude with `hB.1 a _ ((hK₁ x).1 hx)`. Use `show B.1.1.1 (g * c) = 0`. Apply `hB.2` to reduce the goal to its premises. Introduce and unpack `⟨a, x, hx, e⟩`. Apply `hg` to reduce the goal to its premises.

Use `⟨a, c * x * c⁻¹, (hK₁ _).2 (by` and prove the remaining obligations. Establish `: c⁻¹ * (c * x * c⁻¹) * c = x` using `by group`. Rewrite using `[this]`. Conclude with `hx), ?_⟩`. Establish `: g = (g * c) * c⁻¹` using `by group`.

Rewrite using `[this, e]`. Use `group`. Take `⟨K₂, h₂O, hK₂o, -, b, hbS, hbb⟩` from `hb v K₁ hK₁o`. Establish `hB'S` using `GlobalTheory.T.bump_translate_mem_submodule H ρ K₁ K₂ h₂O hK₁c hK₂o v hv S hS b hbb hbS _ hB'`. Use `hS c⁻¹ _ hB'S` as an intermediate fact.

Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem top_of_bumps (H : Subgroup G) (ρ : Representation ℂ H W)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ g, ∀ b ∈ S, cInd H ρ g b ∈ S)
    (hb : ∀ (v : W) (O : Subgroup G), IsOpen (O : Set G) → ∃ K₂ : Subgroup G, K₂ ≤ O ∧ IsOpen (K₂ : Set G) ∧
      IsCompact (K₂ : Set G) ∧ ∃ b ∈ S, IsBump H ρ K₂ 1 v b) (y : cIndSpace H ρ) : y ∈ S := by
  obtain ⟨L, hLo, hL⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H ρ y
  obtain ⟨K, hKo, hKc, hKL⟩ := hbase _ (hLo.mem_nhds L.one_mem)
  refine GlobalTheory.T.mem_submodule_of_bumps H ρ K hKo hKc y (fun g x hx => hL g x (hKL hx)) S fun c B hB => ?_
  let K₁ : Subgroup G := K.map (MulAut.conj c).toMonoidHom
  have hK₁ : ∀ x, x ∈ K₁ ↔ c⁻¹ * x * c ∈ K := by
    intro x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : c⁻¹ * ((MulAut.conj c).toMonoidHom z) * c = z := by
        simp [MulAut.conj_apply]; group
      rw [this]; exact hz
    · intro h
      exact ⟨_, h, by simp [MulAut.conj_apply]; group⟩
  have hconj : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hconj' : Continuous fun x : G => c * x * c⁻¹ := by fun_prop
  have hset : (K₁ : Set G) = (fun x : G => c⁻¹ * x * c) ⁻¹' (K : Set G) := Set.ext hK₁
  have hK₁o : IsOpen (K₁ : Set G) := by rw [hset]; exact hKo.preimage hconj
  have hK₁c : IsCompact (K₁ : Set G) := by
    have : (K₁ : Set G) = (fun x : G => c * x * c⁻¹) '' (K : Set G) := by
      ext x
      constructor
      · intro h
        exact ⟨_, (hK₁ x).1 h, by group⟩
      · rintro ⟨z, hz, rfl⟩
        refine (hK₁ _).2 ?_
        have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
        rw [this]; exact hz
    rw [this]; exact hKc.image hconj'
  set v := y.1.1.1 c with hvdef
  have hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v := by
    intro a ha
    have h1 := (hK₁ _).1 ha
    have e : (a : G) * c = c * (c⁻¹ * a * c) := by group
    have e1 : y.1.1.1 ((a : G) * c) = ρ a (y.1.1.1 c) := y.1.1.2 a c
    rw [← hvdef] at e1
    rw [← e1, e, hL c _ (hKL h1)]
  have hB' : IsBump H ρ K₁ 1 v (cInd H ρ c B) := by
    refine ⟨fun a x hx => ?_, fun g hg => ?_⟩
    · show B.1.1.1 ((a : G) * 1 * x * c) = _
      have e : (a : G) * 1 * x * c = a * c * (c⁻¹ * x * c) := by group
      rw [e]
      exact hB.1 a _ ((hK₁ x).1 hx)
    · show B.1.1.1 (g * c) = 0
      apply hB.2
      rintro ⟨a, x, hx, e⟩
      apply hg
      refine ⟨a, c * x * c⁻¹, (hK₁ _).2 (by
        have : c⁻¹ * (c * x * c⁻¹) * c = x := by group
        rw [this]; exact hx), ?_⟩
      have : g = (g * c) * c⁻¹ := by group
      rw [this, e]; group
  obtain ⟨K₂, h₂O, hK₂o, -, b, hbS, hbb⟩ := hb v K₁ hK₁o
  have hB'S := GlobalTheory.T.bump_translate_mem_submodule H ρ K₁ K₂ h₂O hK₁c hK₂o v hv S hS b hbb hbS _ hB'
  have := hS c⁻¹ _ hB'S
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

end Abs
end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs2
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Distinguish the cases in `hg : ∃ a : H, ∃ z ∈ K, g = (a : G) * c * z`. Take `⟨a, z, hz, rfl⟩` from `hg`. Rewrite using `[mul_assoc _ z x, hB.1 a _ (mul_mem hz hx), hB.1 a _ hz]`. Establish `hn : ¬ ∃ a : H, ∃ z ∈ K, g * x = (a : G) * c * z`. Introduce and unpack `⟨a, z, hz, e⟩`.

Use `hg ⟨a, z * x⁻¹, mul_mem hz (inv_mem hx), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e]`. Use `group`. Rewrite using `[hB.2 _ hn, hB.2 _ hg]`.
-/
theorem IsBump.right_inv {H : Subgroup G} {ρ : Representation ℂ H W} {K : Subgroup G} {c : G} {v : W} {B : cIndSpace H ρ}
    (hB : IsBump H ρ K c v B) (g : G) (x : G) (hx : x ∈ K) : B.1.1.1 (g * x) = B.1.1.1 g := by
  by_cases hg : ∃ a : H, ∃ z ∈ K, g = (a : G) * c * z
  · obtain ⟨a, z, hz, rfl⟩ := hg
    rw [mul_assoc _ z x, hB.1 a _ (mul_mem hz hx), hB.1 a _ hz]
  · have hn : ¬ ∃ a : H, ∃ z ∈ K, g * x = (a : G) * c * z := by
      rintro ⟨a, z, hz, e⟩
      refine hg ⟨a, z * x⁻¹, mul_mem hz (inv_mem hx), ?_⟩
      rw [← mul_assoc, ← e]
      group
    rw [hB.2 _ hn, hB.2 _ hg]

end Abs2

section Abs3
variable {G M Z A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M] [TopologicalSpace M]
  [IsTopologicalGroup M] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup A] [Module ℂ A]

def imgS (H : Subgroup G) (σ : Representation ℂ H Z) (H' : Subgroup M) (ρ' : Representation ℂ H' A) (C : Set G)
    (e : cIndSpace H σ → M → A) (e_add : ∀ f g, e (f + g) = e f + e g) (e_smul : ∀ (c : ℂ) f, e (c • f) = c • e f) :
    Submodule ℂ (cIndSpace H' ρ') where
  carrier := {y | ∃ f : cIndSpace H σ, (∀ x ∈ C, f.1.1.1 x = 0) ∧ e f = y.1.1.1}
  add_mem' := by
    rintro a b ⟨f, hf, ef⟩ ⟨g, hg, eg⟩
    refine ⟨f + g, fun x hx => ?_, ?_⟩
    · show f.1.1.1 x + g.1.1.1 x = 0
      rw [hf x hx, hg x hx, add_zero]
    · rw [e_add, ef, eg]
      rfl
  zero_mem' := by
    refine ⟨0, fun x _ => rfl, ?_⟩
    have := e_smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    rfl
  smul_mem' := by
    rintro c a ⟨f, hf, ef⟩
    refine ⟨c • f, fun x hx => ?_, ?_⟩
    · show c • f.1.1.1 x = 0
      rw [hf x hx, smul_zero]
    · rw [e_smul, ef]
      rfl

/- English proof (translation)
Use `top_of_bumps H' ρ' hbase (imgS H σ H' ρ' C e e_add e_smul) (fun g b hbS => ?_) (fun v O hO => ?_) y` and prove the remaining obligations. Take `⟨f, hf, ef⟩` from `hbS`. Use `⟨((χ g : ℂˣ) : ℂ) • cInd H σ (s g) f, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Use `show ((χ g : ℂˣ) : ℂ) • f.1.1.1 (x * s g) = 0`. Rewrite using `[hf _ (hC x hx g), smul_zero]`.

Rewrite using `[e_smul]`. Use function extensionality and compare the values at `m`. Use `show ((χ g : ℂˣ) : ℂ) • e _ m = b.1.1.1 (m * g)`. Rewrite using `[e_tr, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, ef]`. Distinguish the cases in `hv : v = 0`.

Substitute `hv` using the available equality. Take `⟨K₂, hK₂o, hK₂c, hK₂⟩` from `hbase _ (hO.mem_nhds O.one_mem)`. Use `⟨K₂, hK₂, hK₂o, hK₂c, 0, Submodule.zero_mem _, fun a x _ => ?_, fun g _ => rfl⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Both sides reduce to the same expression.

Take `⟨K₂, h₂, hK₂o, hK₂c, f, hf, b, hb', α, hα, hbump⟩` from `hb v hv O hO`. Use `⟨K₂, h₂, hK₂o, hK₂c, α⁻¹ • b, Submodule.smul_mem _ _ ⟨f, hf, hb'⟩, fun a x hx => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Use `show α⁻¹ • b.1.1.1 _ = _`. Rewrite using `[hbump.1 a x hx, map_smul, smul_smul, inv_mul_cancel₀ hα, one_smul]`. Use `show α⁻¹ • b.1.1.1 _ = 0`.

Rewrite using `[hbump.2 g hg, smul_zero]`.
-/
theorem onto_abs (H : Subgroup G) (σ : Representation ℂ H Z) (H' : Subgroup M) (ρ' : Representation ℂ H' A)
    (hbase : ∀ O ∈ 𝓝 (1 : M), ∃ K : Subgroup M, IsOpen (K : Set M) ∧ IsCompact (K : Set M) ∧ (K : Set M) ⊆ O)
    (C : Set G) (s : M →* G) (hC : ∀ x ∈ C, ∀ g, x * s g ∈ C)
    (e : cIndSpace H σ → M → A) (e_add : ∀ f g, e (f + g) = e f + e g) (e_smul : ∀ (c : ℂ) f, e (c • f) = c • e f)
    (χ : M →* ℂˣ) (e_tr : ∀ f g m, e (cInd H σ (s g) f) m = (((χ g)⁻¹ : ℂˣ) : ℂ) • e f (m * g))
    (hb : ∀ v : A, v ≠ 0 → ∀ O : Subgroup M, IsOpen (O : Set M) → ∃ K₂ : Subgroup M, K₂ ≤ O ∧ IsOpen (K₂ : Set M) ∧
      IsCompact (K₂ : Set M) ∧ ∃ f : cIndSpace H σ, (∀ x ∈ C, f.1.1.1 x = 0) ∧ ∃ b : cIndSpace H' ρ', e f = b.1.1.1 ∧
      ∃ α : ℂ, α ≠ 0 ∧ IsBump H' ρ' K₂ 1 (α • v) b)
    (y : cIndSpace H' ρ') : ∃ f : cIndSpace H σ, (∀ x ∈ C, f.1.1.1 x = 0) ∧ e f = y.1.1.1 := by
  refine top_of_bumps H' ρ' hbase (imgS H σ H' ρ' C e e_add e_smul) (fun g b hbS => ?_) (fun v O hO => ?_) y
  · obtain ⟨f, hf, ef⟩ := hbS
    refine ⟨((χ g : ℂˣ) : ℂ) • cInd H σ (s g) f, fun x hx => ?_, ?_⟩
    · show ((χ g : ℂˣ) : ℂ) • f.1.1.1 (x * s g) = 0
      rw [hf _ (hC x hx g), smul_zero]
    · rw [e_smul]
      funext m
      show ((χ g : ℂˣ) : ℂ) • e _ m = b.1.1.1 (m * g)
      rw [e_tr, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, ef]
  · by_cases hv : v = 0
    · subst hv
      obtain ⟨K₂, hK₂o, hK₂c, hK₂⟩ := hbase _ (hO.mem_nhds O.one_mem)
      refine ⟨K₂, hK₂, hK₂o, hK₂c, 0, Submodule.zero_mem _, fun a x _ => ?_, fun g _ => rfl⟩
      rw [map_zero]
      rfl
    · obtain ⟨K₂, h₂, hK₂o, hK₂c, f, hf, b, hb', α, hα, hbump⟩ := hb v hv O hO
      refine ⟨K₂, h₂, hK₂o, hK₂c, α⁻¹ • b, Submodule.smul_mem _ _ ⟨f, hf, hb'⟩, fun a x hx => ?_, fun g hg => ?_⟩
      · show α⁻¹ • b.1.1.1 _ = _
        rw [hbump.1 a x hx, map_smul, smul_smul, inv_mul_cancel₀ hα, one_smul]
      · show α⁻¹ • b.1.1.1 _ = 0
        rw [hbump.2 g hg, smul_zero]

end Abs3
end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs4
variable {G M Z A D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M] [TopologicalSpace M]
  [IsTopologicalGroup M] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup A] [Module ℂ A] [TopologicalSpace D]

/- English proof (translation)
Take `⟨O₁, hO₁, hfix⟩` from `hfix₀`. Take `⟨N₂, hN₂, hforce2⟩` from `force2 O₁ hO₁`. Establish `h1 : {x | w * x ∉ C} ∈ 𝓝 (1 : G)` using `(hCc.isOpen_compl.preimage (by fun_prop : Continuous fun x => w * x)).mem_nhds (by simpa using hwC)`. Establish `h2 : {x | w * x * w⁻¹ ∈ O₁} ∈ 𝓝 (1 : G)` using `(Continuous.tendsto' (by fun_prop : Continuous fun x => w * x * w⁻¹) 1 1 (by simp)) hO₁`. Take `⟨K₀, hK₀o, hK₀c, hK₀⟩` from `hbaseG _ (Filter.inter_mem (Filter.inter_mem hN₂ h1) h2)`.

Establish `h3 : (O : Set M) ∩ (s ⁻¹' (K₀ : Set G)) ∩ (χ.ker : Set M) ∈ 𝓝 (1 : M)` using `((hO.inter (hK₀o.preimage hsc)).inter hχ).mem_nhds ⟨⟨O.one_mem, by simp [K₀.one_mem]⟩, one_mem _⟩`. Take `⟨K₂, hK₂o, hK₂c, hK₂⟩` from `hbaseM _ h3`. Take `⟨N₁, hN₁, hforce⟩` from `force K₂ (hK₂o.mem_nhds K₂.one_mem)`. Take `⟨K, hKo, hKc, hCK, hKK₀, hKfac⟩` from `GlobalTheory.T.exists_small_compact_open_between hbaseG K₀ (K₂.map s) hK₀o hK₀c (by rintro _ ⟨x, hx, rfl⟩; exact (hK₂ hx).1.2) N₁ hN₁`. Take `⟨B, hB⟩` from `GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc w v₀ (fun a x hx e => hfix a (by rw [e]; exact (hK₀ (hKK₀ hx)).2))`.

Establish `hB' : IsBump H σ K w v₀ B` using `hB`. Establish `hvan : ∀ x ∈ C, B.1.1.1 x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `hex : ∃ a : H, ∃ z ∈ K, x = (a : G) * w * z` using `by_contra fun h => hne (hB.2 x h)`.

Take `⟨a, z, hz, rfl⟩` from `hex`. Establish `hmem` using `hHC _ (inv_mem a.2) _ hx`. Establish `e : (a : G)⁻¹ * ((a : G) * w * z) = w * z` using `by group`. Rewrite `hmem` using `[e]`. Conclude with `(hK₀ (hKK₀ hz)).1.2 hmem`.

Take `⟨y, hy⟩` from `mem B hvan`. Take `⟨hl, hc⟩` from `fib B (w * s 1)`. Use `set φ : D → Z := fun d => B.1.1.1 (dE d * (w * s 1)) with hφ`. Establish `hdich : ∀ d, φ d = v₀ ∨ φ d = 0`. Introduce `d`.

Establish `e0 : dE d * (w * s 1) = dE d * w` using `by rw [map_one, mul_one]`. Distinguish the cases in `hex : ∃ a : H, ∃ z ∈ K, dE d * w = (a : G) * w * z`. Take `⟨a, z, hz, e⟩` from `hex left`. Rewrite using `[hφ]`. Simplify using `only`.

Rewrite using `[e0, e, hB.1 a z hz]`. Conclude with `hfix a (hforce2 a a.2 d z (hK₀ (hKK₀ hz)).1.1 e)`. Use `right`. Rewrite using `[hφ]`. Simplify using `only`.

Rewrite using `[e0]`. Conclude with `hB.2 _ hex`. Establish `h0 : φ d₀ = v₀`. Establish `e0 : dE d₀ * (w * s 1) = ((1 : H) : G) * w * 1`. Rewrite using `[hd0, map_one]`.

Simplify using the standard rewrite rules. Rewrite using `[hφ]`. Simplify using `only`. Rewrite using `[e0, hB.1 1 1 (one_mem _), map_one, Module.End.one_apply]`. Use `set E : Set D := φ ⁻¹' {v₀} with hE`.

Establish `hφE : φ = E.indicator fun _ => v₀`. Use function extensionality and compare the values at `d`. Distinguish the cases in `hd : d ∈ E`. Rewrite using `[Set.indicator_of_mem hd]`. Conclude with `hd`.

Rewrite using `[Set.indicator_of_notMem hd]`. Conclude with `(hdich d).resolve_left hd`. Establish `hvol : (μ E).toReal ≠ 0`. Use `vol E (tsupport φ) (hl.isOpen_fiber _) ⟨d₀, h0⟩ hc fun d hd => subset_tsupport _ ?_` and prove the remaining obligations. Rewrite using `[Function.mem_support, show φ d = v₀ from hd]`.

Conclude with `hv0`. Establish `hval : e B 1 = (((μ E).toReal : ℝ) : ℂ) • v`. Rewrite using `[e_def, map_one, Units.val_one, one_smul]`. Use `show q (GlobalTheory.CompanionTheory.Rodier.smInt μ φ) = _`. Rewrite using `[hφE, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator, map_smul, hq]`.

Establish `hinv : ∀ x ∈ K₂, e B x = e B 1`. Introduce `x hx`. Establish `e2 : χ x = 1` using `(hK₂ hx).2`. Rewrite using `[e_def, e_def, e2, map_one, Units.val_one]`. Use `congr 3`.

Use function extensionality and compare the values at `d`. Establish `hs : s x ∈ K` using `hCK ⟨x, hx, rfl⟩`. Rewrite using `[map_one, mul_one, ← mul_assoc]`. Conclude with `hB'.right_inv _ _ hs`. Establish `hzero : ∀ g, (¬ ∃ a : H', ∃ x ∈ K₂, g = (a : M) * 1 * x) → e B g = 0`.

Introduce `g hg`. Establish `hz : ∀ d, B.1.1.1 (dE d * (w * s g)) = 0`. Introduce `d`. Apply `hB.2` to reduce the goal to its premises. Introduce and unpack `⟨a, z, hz, e⟩`.

Take `⟨n, hn, _, ⟨x₂, hx₂, rfl⟩, rfl⟩` from `hKfac z hz`. Establish `e2 : dE d * w * s (g * x₂⁻¹) = (a : G) * w * n`. Establish `e3 : s (g * x₂⁻¹) = s g * (s x₂)⁻¹` using `by rw [map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a', ha', x', hx', e3⟩` from `hforce a a.2 d _ n hn e2`.

Use `hg ⟨⟨a', ha'⟩, x' * x₂, mul_mem hx' hx₂, ?_⟩` and prove the remaining obligations. Establish `: g = (g * x₂⁻¹) * x₂` using `by group`. Rewrite using `[this, e3]`. Simplify using `[mul_assoc]`. Establish `e1 : (fun d => B.1.1.1 (dE d * (w * s g))) = (∅ : Set D).indicator fun _ => (0 : Z)`.

Use function extensionality and compare the values at `d`. Simplify using `using hz d`. Rewrite using `[e_def, e1, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator, smul_zero, map_zero, smul_zero]`. Use `⟨K₂, fun x hx => (hK₂ hx).1.1, hK₂o, hK₂c, B, hvan, y, hy.symm, (((μ E).toReal : ℝ) : ℂ), Complex.ofReal_ne_zero.2 hvol, fun a x hx => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e1 : y.1.1.1 ((a : M) * x) = ρ' a (y.1.1.1 x)` using `y.1.1.2 a x`.

Rewrite using `[mul_one, e1, hy, hinv x hx, hval]`. Rewrite using `[hy]`. Conclude with `hzero g hg`.
-/
theorem bump_abs [MeasurableSpace D] (μ : MeasureTheory.Measure D) (H : Subgroup G) (σ : Representation ℂ H Z) (H' : Subgroup M)
    (ρ' : Representation ℂ H' A)
    (hbaseG : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hbaseM : ∀ O ∈ 𝓝 (1 : M), ∃ K : Subgroup M, IsOpen (K : Set M) ∧ IsCompact (K : Set M) ∧ (K : Set M) ⊆ O)
    (s : M →* G) (hsc : Continuous s) (w : G) (dE : D → G) (d₀ : D) (hd0 : dE d₀ = 1)
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hwC : w ∉ C)
    (q : Z →ₗ[ℂ] A) (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (e : cIndSpace H σ → M → A)
    (e_def : ∀ f m, e f m = ((χ m : ℂˣ) : ℂ) • q (GlobalTheory.CompanionTheory.Rodier.smInt μ fun d => f.1.1.1 (dE d * (w * s m))))
    (fib : ∀ (f : cIndSpace H σ) (y : G), IsLocallyConstant (fun d => f.1.1.1 (dE d * y)) ∧
      HasCompactSupport (fun d => f.1.1.1 (dE d * y)))
    (mem : ∀ f : cIndSpace H σ, (∀ x ∈ C, f.1.1.1 x = 0) → ∃ y : cIndSpace H' ρ', y.1.1.1 = e f)
    (force2 : ∀ O ∈ 𝓝 (1 : G), ∃ N ∈ 𝓝 (1 : G), ∀ h ∈ H, ∀ (d : D) (x : G), x ∈ N → dE d * w = h * w * x → h ∈ O)
    (force : ∀ O ∈ 𝓝 (1 : M), ∃ N ∈ 𝓝 (1 : G), ∀ h ∈ H, ∀ (d : D) (m : M) (x : G), x ∈ N →
      dE d * w * s m = h * w * x → ∃ a ∈ H', ∃ x' ∈ O, m = a * x')
    (vol : ∀ E Y : Set D, IsOpen E → E.Nonempty → IsCompact Y → E ⊆ Y → (μ E).toReal ≠ 0)
    (v₀ : Z) (hv0 : v₀ ≠ 0) (hfix₀ : ∃ O ∈ 𝓝 (1 : G), ∀ a : H, (a : G) ∈ O → σ a v₀ = v₀)
    (v : A) (hq : q v₀ = v) (O : Subgroup M) (hO : IsOpen (O : Set M)) :
    ∃ K₂ : Subgroup M, K₂ ≤ O ∧ IsOpen (K₂ : Set M) ∧ IsCompact (K₂ : Set M) ∧ ∃ f : cIndSpace H σ,
      (∀ x ∈ C, f.1.1.1 x = 0) ∧ ∃ b : cIndSpace H' ρ', e f = b.1.1.1 ∧ ∃ α : ℂ, α ≠ 0 ∧ IsBump H' ρ' K₂ 1 (α • v) b := by
  obtain ⟨O₁, hO₁, hfix⟩ := hfix₀
  obtain ⟨N₂, hN₂, hforce2⟩ := force2 O₁ hO₁
  have h1 : {x | w * x ∉ C} ∈ 𝓝 (1 : G) :=
    (hCc.isOpen_compl.preimage (by fun_prop : Continuous fun x => w * x)).mem_nhds (by simpa using hwC)
  have h2 : {x | w * x * w⁻¹ ∈ O₁} ∈ 𝓝 (1 : G) :=
    (Continuous.tendsto' (by fun_prop : Continuous fun x => w * x * w⁻¹) 1 1 (by simp)) hO₁
  obtain ⟨K₀, hK₀o, hK₀c, hK₀⟩ := hbaseG _ (Filter.inter_mem (Filter.inter_mem hN₂ h1) h2)
  have h3 : (O : Set M) ∩ (s ⁻¹' (K₀ : Set G)) ∩ (χ.ker : Set M) ∈ 𝓝 (1 : M) :=
    ((hO.inter (hK₀o.preimage hsc)).inter hχ).mem_nhds ⟨⟨O.one_mem, by simp [K₀.one_mem]⟩, one_mem _⟩
  obtain ⟨K₂, hK₂o, hK₂c, hK₂⟩ := hbaseM _ h3
  obtain ⟨N₁, hN₁, hforce⟩ := force K₂ (hK₂o.mem_nhds K₂.one_mem)
  obtain ⟨K, hKo, hKc, hCK, hKK₀, hKfac⟩ := GlobalTheory.T.exists_small_compact_open_between hbaseG K₀ (K₂.map s) hK₀o hK₀c
    (by rintro _ ⟨x, hx, rfl⟩; exact (hK₂ hx).1.2) N₁ hN₁
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc w v₀
    (fun a x hx e => hfix a (by rw [e]; exact (hK₀ (hKK₀ hx)).2))
  have hB' : IsBump H σ K w v₀ B := hB
  have hvan : ∀ x ∈ C, B.1.1.1 x = 0 := by
    intro x hx
    by_contra hne
    have hex : ∃ a : H, ∃ z ∈ K, x = (a : G) * w * z := by_contra fun h => hne (hB.2 x h)
    obtain ⟨a, z, hz, rfl⟩ := hex
    have hmem := hHC _ (inv_mem a.2) _ hx
    have e : (a : G)⁻¹ * ((a : G) * w * z) = w * z := by group
    rw [e] at hmem
    exact (hK₀ (hKK₀ hz)).1.2 hmem
  obtain ⟨y, hy⟩ := mem B hvan
  obtain ⟨hl, hc⟩ := fib B (w * s 1)
  set φ : D → Z := fun d => B.1.1.1 (dE d * (w * s 1)) with hφ
  have hdich : ∀ d, φ d = v₀ ∨ φ d = 0 := by
    intro d
    have e0 : dE d * (w * s 1) = dE d * w := by rw [map_one, mul_one]
    by_cases hex : ∃ a : H, ∃ z ∈ K, dE d * w = (a : G) * w * z
    · obtain ⟨a, z, hz, e⟩ := hex
      left
      rw [hφ]
      simp only
      rw [e0, e, hB.1 a z hz]
      exact hfix a (hforce2 a a.2 d z (hK₀ (hKK₀ hz)).1.1 e)
    · right
      rw [hφ]
      simp only
      rw [e0]
      exact hB.2 _ hex
  have h0 : φ d₀ = v₀ := by
    have e0 : dE d₀ * (w * s 1) = ((1 : H) : G) * w * 1 := by
      rw [hd0, map_one]; simp
    rw [hφ]
    simp only
    rw [e0, hB.1 1 1 (one_mem _), map_one, Module.End.one_apply]
  set E : Set D := φ ⁻¹' {v₀} with hE
  have hφE : φ = E.indicator fun _ => v₀ := by
    funext d
    by_cases hd : d ∈ E
    · rw [Set.indicator_of_mem hd]; exact hd
    · rw [Set.indicator_of_notMem hd]
      exact (hdich d).resolve_left hd
  have hvol : (μ E).toReal ≠ 0 := by
    refine vol E (tsupport φ) (hl.isOpen_fiber _) ⟨d₀, h0⟩ hc fun d hd => subset_tsupport _ ?_
    rw [Function.mem_support, show φ d = v₀ from hd]
    exact hv0
  have hval : e B 1 = (((μ E).toReal : ℝ) : ℂ) • v := by
    rw [e_def, map_one, Units.val_one, one_smul]
    show q (GlobalTheory.CompanionTheory.Rodier.smInt μ φ) = _
    rw [hφE, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator, map_smul, hq]
  have hinv : ∀ x ∈ K₂, e B x = e B 1 := by
    intro x hx
    have e2 : χ x = 1 := (hK₂ hx).2
    rw [e_def, e_def, e2, map_one, Units.val_one]
    congr 3
    funext d
    have hs : s x ∈ K := hCK ⟨x, hx, rfl⟩
    rw [map_one, mul_one, ← mul_assoc]
    exact hB'.right_inv _ _ hs
  have hzero : ∀ g, (¬ ∃ a : H', ∃ x ∈ K₂, g = (a : M) * 1 * x) → e B g = 0 := by
    intro g hg
    have hz : ∀ d, B.1.1.1 (dE d * (w * s g)) = 0 := by
      intro d
      apply hB.2
      rintro ⟨a, z, hz, e⟩
      obtain ⟨n, hn, _, ⟨x₂, hx₂, rfl⟩, rfl⟩ := hKfac z hz
      have e2 : dE d * w * s (g * x₂⁻¹) = (a : G) * w * n := by
        have e3 : s (g * x₂⁻¹) = s g * (s x₂)⁻¹ := by rw [map_mul, map_inv]
        calc dE d * w * s (g * x₂⁻¹) = dE d * (w * s g) * (s x₂)⁻¹ := by rw [e3]; group
          _ = (a : G) * w * (n * s x₂) * (s x₂)⁻¹ := by rw [e]
          _ = (a : G) * w * n := by group
      obtain ⟨a', ha', x', hx', e3⟩ := hforce a a.2 d _ n hn e2
      refine hg ⟨⟨a', ha'⟩, x' * x₂, mul_mem hx' hx₂, ?_⟩
      have : g = (g * x₂⁻¹) * x₂ := by group
      rw [this, e3]
      simp [mul_assoc]
    have e1 : (fun d => B.1.1.1 (dE d * (w * s g))) = (∅ : Set D).indicator fun _ => (0 : Z) := by
      funext d
      simpa using hz d
    rw [e_def, e1, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator, smul_zero, map_zero, smul_zero]
  refine ⟨K₂, fun x hx => (hK₂ hx).1.1, hK₂o, hK₂c, B, hvan, y, hy.symm, (((μ E).toReal : ℝ) : ℂ), Complex.ofReal_ne_zero.2 hvol, fun a x hx => ?_, fun g hg => ?_⟩
  · have e1 : y.1.1.1 ((a : M) * x) = ρ' a (y.1.1.1 x) := y.1.1.2 a x
    rw [mul_one, e1, hy, hinv x hx, hval]
  · rw [hy]
    exact hzero g hg

end Abs4
end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}

variable (k) in
/- English proof (translation)
Take `⟨Θ, hΘc, hΘ1, hΘ⟩` from `GlobalTheory.T.continuous_open_cell_retraction k i t`. Take `⟨N, hN, hNf⟩` from `GlobalTheory.T.last_row_update_nhds_generation k (i + (t + 1)) (parab k (ePG i (t + 1))) (by`. Introduce `r _ g hg`. Rewrite using `[mem_parab_iff]`. Introduce `a b u v hab`.

Apply the tactic sequence `cases a <;> cases b <;> first | exact absurd hab (by decide) | skip`. Establish `hne : ePG i (t + 1) ⟨true, u⟩ ≠ Fin.last (i + (t + 1))`. Rewrite using `[← ePG_false_last]`. Introduce `e`. Simplify using `using (ePG i (t + 1)).injective e`.

Establish `hne2 : ePG i (t + 1) ⟨true, u⟩ ≠ ePG i (t + 1) ⟨false, v⟩`. Introduce `e`. Simplify using `using (ePG i (t + 1)).injective e`. Rewrite using `[hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]) O hO`. Use `⟨Θ ⁻¹' N, hΘc.continuousAt.preimage_mem_nhds (by rwa [hΘ1]), fun h hh d m x hx e => ?_⟩` and prove the remaining obligations.

Take `⟨p, hp, hm⟩` from `hΘ h hh d m x e`. Take `⟨a, ha, x', hx', e2⟩` from `hNf p hp _ hx m hm`. Conclude with `⟨a, ha, x', hx', e2⟩`.
-/
theorem forcing (i t : ℕ) (O : Set (Mir k (i + (t + 1)))) (hO : O ∈ 𝓝 (1 : Mir k (i + (t + 1)))) :
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1))) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
        ∃ a ∈ HPG k i (t + 1), ∃ x' ∈ O, m = a * x' := by
  obtain ⟨Θ, hΘc, hΘ1, hΘ⟩ := GlobalTheory.T.continuous_open_cell_retraction k i t
  obtain ⟨N, hN, hNf⟩ := GlobalTheory.T.last_row_update_nhds_generation k (i + (t + 1)) (parab k (ePG i (t + 1))) (by
    intro r _ g hg
    rw [mem_parab_iff]
    intro a b u v hab
    cases a <;> cases b <;> first | exact absurd hab (by decide) | skip
    have hne : ePG i (t + 1) ⟨true, u⟩ ≠ Fin.last (i + (t + 1)) := by
      rw [← ePG_false_last]
      intro e
      simpa using (ePG i (t + 1)).injective e
    have hne2 : ePG i (t + 1) ⟨true, u⟩ ≠ ePG i (t + 1) ⟨false, v⟩ := by
      intro e
      simpa using (ePG i (t + 1)).injective e
    rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]) O hO
  refine ⟨Θ ⁻¹' N, hΘc.continuousAt.preimage_mem_nhds (by rwa [hΘ1]), fun h hh d m x hx e => ?_⟩
  obtain ⟨p, hp, hm⟩ := hΘ h hh d m x e
  obtain ⟨a, ha, x', hx', e2⟩ := hNf p hp _ hx m hm
  exact ⟨a, ha, x', hx', e2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eO_apply (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    eO ψ f m = ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sO k i t m)) := rfl

/- English proof (translation)
Rewrite using `[smul_smul, ← Units.val_mul, mul_comm a b, inv_mul_cancel_left]`.
-/
theorem sm2 {X : Type} [AddCommGroup X] [Module ℂ X] (a b : ℂˣ) (x : X) :
   ((a : ℂˣ) : ℂ) • x = ((b⁻¹ : ℂˣ) : ℂ) • ((a * b : ℂˣ) : ℂ) • x := by
  rw [smul_smul, ← Units.val_mul, mul_comm a b, inv_mul_cancel_left]

/- English proof (translation)
Establish `e : intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sO k i t g) f) (wEl k i t * sO k i t m) = intO f (wEl k i t * sO k i t (m * g))`. Unfold `intO`. Use `congr 1`. Use function extensionality and compare the values at `d`. Use `show evX f (dEmb k i t d * (wEl k i t * sO k i t m) * sO k i t g) = evX f (dEmb k i t d * (wEl k i t * sO k i t (m * g)))`.

Rewrite using `[map_mul]`. Simplify using `only [mul_assoc]`. Establish `h1` using `eO_apply ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sO k i t g) f) m`. Establish `h2` using `eO_apply ψ f (m * g)`. Establish `hd : dpowM (k` using `k) (i + (t + 1)) (-1 / 2) (m * g) = dpowM (i + (t + 1)) (-1 / 2) m * dpowM (i + (t + 1)) (-1 / 2) g := map_mul _ _ _`.

Use `h1.trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (fun z => (((dpowM (i + (t + 1)) (-1 / 2) g)⁻¹ : ℂˣ) : ℂ) • z) h2.symm)` and prove the remaining obligations. Use `Eq.trans (congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • qO τ σ ψ z) e) ?_` and prove the remaining obligations. Use `show _ = (((dpowM (i + (t + 1)) (-1 / 2) g)⁻¹ : ℂˣ) : ℂ) • ((dpowM (i + (t + 1)) (-1 / 2) (m * g) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sO k i t (m * g)))`. Rewrite using `[hd]`.

Conclude with `sm2 _ _ _`.
-/
theorem eO_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sO k i t g) f) m =
      (((dpowM (i + (t + 1)) (-1 / 2) g)⁻¹ : ℂˣ) : ℂ) • eO ψ f (m * g) := by
  have e : intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sO k i t g) f) (wEl k i t * sO k i t m) =
      intO f (wEl k i t * sO k i t (m * g)) := by
    unfold intO
    congr 1
    funext d
    show evX f (dEmb k i t d * (wEl k i t * sO k i t m) * sO k i t g) = evX f (dEmb k i t d * (wEl k i t * sO k i t (m * g)))
    rw [map_mul]
    simp only [mul_assoc]
  have h1 := eO_apply ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sO k i t g) f) m
  have h2 := eO_apply ψ f (m * g)
  have hd : dpowM (k := k) (i + (t + 1)) (-1 / 2) (m * g) = dpowM (i + (t + 1)) (-1 / 2) m * dpowM (i + (t + 1)) (-1 / 2) g := map_mul _ _ _
  refine h1.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (((dpowM (i + (t + 1)) (-1 / 2) g)⁻¹ : ℂˣ) : ℂ) • z) h2.symm)
  refine Eq.trans (congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • qO τ σ ψ z) e) ?_
  show _ = (((dpowM (i + (t + 1)) (-1 / 2) g)⁻¹ : ℂˣ) : ℂ) • ((dpowM (i + (t + 1)) (-1 / 2) (m * g) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sO k i t (m * g)))
  rw [hd]
  exact sm2 _ _ _

/- English proof (translation)
Use `onto_abs (HPG k (i + 1) (t + 1)) (sigX τ σ) (HPG k i (t + 1)) (sigO τ σ ψ) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (Cl k i t) (sO k i t) (GlobalTheory.T.closed_cell_right_stable k i t) (eO ψ) (fun f g => (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ …` and prove the remaining obligations. Take `⟨v₀, hv₀⟩ : ∃ v₀, qO τ σ ψ v₀ = v` from `LinearMap.rTensor_surjective σ.V (Submodule.mkQ_surjective _) v`. Establish `h0 : v₀ ≠ 0` using `fun h => hv (hv₀.symm.trans ((congrArg (qO τ σ ψ) h).trans (map_zero _)))`. Establish `grp` using `GlobalTheory.T.mirabolic_cell_structure_data k ψ hψ i t`. Establish `hker : IsOpen ((dpowM (k` using `k) (i + (t + 1)) (-1 / 2)).ker : Set (Mir k (i + (t + 1)))) := (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow (k := k) (i + (t + 1) + 1) (-1 / 2)).preimage continuous_subtype_val`.

Set `_ : MeasurableSpace (Fin (t + 1) → k)` to `borel _`. Conclude with `bump_abs (muD k (t + 1)) (HPG k (i + 1) (t + 1)) (sigX τ σ) (HPG k i (t + 1)) (sigO τ σ ψ) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (sO k i t) (GlobalTheory.T.continuous_shifted_orbit_map k i t …`.
-/
theorem onto (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)) :
  ∃ f : XS τ σ, (∀ x ∈ Cl k i t, evX f x = 0) ∧ eO ψ f = (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 := by
  refine onto_abs (HPG k (i + 1) (t + 1)) (sigX τ σ) (HPG k i (t + 1)) (sigO τ σ ψ)
    (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (Cl k i t) (sO k i t) (GlobalTheory.T.closed_cell_right_stable k i t) (eO ψ)
    (fun f g => (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).2.2.1)
    (fun c f => (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.2.2)
    (dpowM (i + (t + 1)) (-1 / 2)) (eO_translate ψ) (fun v hv O hO => ?_) y
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, qO τ σ ψ v₀ = v := LinearMap.rTensor_surjective σ.V (Submodule.mkQ_surjective _) v
  have h0 : v₀ ≠ 0 := fun h => hv (hv₀.symm.trans ((congrArg (qO τ σ ψ) h).trans (map_zero _)))
  have grp := GlobalTheory.T.mirabolic_cell_structure_data k ψ hψ i t
  have hker : IsOpen ((dpowM (k := k) (i + (t + 1)) (-1 / 2)).ker : Set (Mir k (i + (t + 1)))) :=
    (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow (k := k) (i + (t + 1) + 1) (-1 / 2)).preimage continuous_subtype_val
  let _ : MeasurableSpace (Fin (t + 1) → k) := borel _
  exact bump_abs (muD k (t + 1)) (HPG k (i + 1) (t + 1)) (sigX τ σ) (HPG k i (t + 1)) (sigO τ σ ψ)
    (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) (sO k i t) (GlobalTheory.T.continuous_shifted_orbit_map k i t)
    (wEl k i t) (dEmb k i t) 0 (GlobalTheory.T.weyl_not_mem_closed_cell k i t).2 (Cl k i t) grp.2.2.1 grp.2.2.2.1 (GlobalTheory.T.weyl_not_mem_closed_cell k i t).1 (qO τ σ ψ)
    (dpowM (i + (t + 1)) (-1 / 2)) hker (eO ψ) (fun f m => rfl) (fun f y => GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y)
    (fun f hf => GlobalTheory.T.open_evaluation_induced k i t ψ hψ τ σ hτ hσ f hf) (fun O hO => GlobalTheory.T.open_cell_parabolic_near_identity k i t O hO) (fun O hO => forcing k i t O hO)
    (GlobalTheory.T.haar_measure_open_nonempty_ne_zero k (t + 1)) v₀ h0 (GlobalTheory.T.smooth_vector_fixed_parabolic_near_one k i t τ σ hτ hσ v₀) v hv₀ O hO

end Main
end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
